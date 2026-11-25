import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { getConfig } from './config';
import { DataSource } from './dataSource';
import { DEFAULT_REPO_STATE, ExtensionState } from './extensionState';
import { t } from './i18n';
import { Logger } from './logger';
import { BooleanOverride, ErrorInfo, FileViewType, GitRepoSet, GitRepoState, PinnedCommit, PullRequestConfig, PullRequestConfigBase, PullRequestProvider, RepoCommitOrdering } from './types';
import { evalPromises } from './utils/childProcess';
import {
	getPathFromStr,
	getPathFromUri,
	getRepoName,
	pathWithTrailingSlash,
	realpath,
} from './utils/paths';
import { showErrorMessage, showInformationMessage } from './utils/actions';
import { BufferedQueue } from './utils/bufferedQueue';
import { Disposable, toDisposable } from './utils/disposable';
import { EventEmitter, GgEvent } from './utils/event';

const REPO_SCAN_EXCLUDED_FOLDERS = new Set(['build', 'coverage', 'dist', 'node_modules', 'out', 'target', 'venv', '__pycache__']);

/** Can the repository scan descend into this directory? */
function isScannableFolder(entry: fs.Dirent) {
	return entry.isDirectory() && !entry.name.startsWith('.') && !REPO_SCAN_EXCLUDED_FOLDERS.has(entry.name);
}

export interface RepoChangeEvent {
	readonly repos: GitRepoSet;
	readonly numRepos: number;
	readonly loadRepo: string | null;
}

/**
 * Detects and manages repositories in Git Graph.
 */
export class RepoManager extends Disposable {
	private readonly dataSource: DataSource;
	private readonly extensionState: ExtensionState;
	private readonly logger: Logger;

	private repos: GitRepoSet;
	private ignoredRepos: string[];
	private maxDepthOfRepoSearch: number;
	private readonly pinsWriteInFlight: Set<string> = new Set(); // repos whose pinned branches/commits are currently being persisted to the External Configuration File

	private readonly folderWatchers: { [workspace: string]: vscode.FileSystemWatcher } = {};
	private readonly configWatcher: vscode.FileSystemWatcher;

	private readonly repoEventEmitter: EventEmitter<RepoChangeEvent>;

	private readonly onWatcherCreateQueue: BufferedQueue<string>;
	private readonly onWatcherChangeQueue: BufferedQueue<string>;
	private readonly checkRepoConfigQueue: BufferedQueue<string>;

	/**
	 * Creates the Git Graph Repository Manager, and runs startup tasks.
	 * @param dataSource The Git Graph DataSource instance.
	 * @param extensionState The Git Graph ExtensionState instance.
	 * @param logger The Git Graph Logger instance.
	 */
	constructor(dataSource: DataSource, extensionState: ExtensionState, onDidChangeConfiguration: GgEvent<vscode.ConfigurationChangeEvent>, logger: Logger) {
		super();
		this.dataSource = dataSource;
		this.extensionState = extensionState;
		this.logger = logger;
		// Repository paths used to be persisted in native-separator form on Windows when they came
		// from a backend (submodules in particular), which made them miss every forward-slash
		// comparison; migrate them to the normalised form
		this.repos = {};
		const savedRepos = extensionState.getRepos();
		const lastActiveRepo = extensionState.getLastActiveRepo();
		let pathsChanged = false;
		for (const repo of Object.keys(savedRepos)) {
			const normalised = getPathFromStr(repo);
			if (typeof this.repos[normalised] === 'undefined' || repo === lastActiveRepo ||
				(repo === normalised && getPathFromStr(lastActiveRepo ?? '') !== normalised)) {
				this.repos[normalised] = savedRepos[repo];
			}
			if (repo !== normalised) {
				extensionState.transferRepo(repo, normalised);
				pathsChanged = true;
			}
		}
		if (pathsChanged) extensionState.saveRepos(this.repos);
		this.ignoredRepos = extensionState.getIgnoredRepos().map((repo) => getPathFromStr(repo)).filter((repo, i, repos) => repos.indexOf(repo) === i);
		this.maxDepthOfRepoSearch = getConfig().maxDepthOfRepoSearch;

		this.configWatcher = vscode.workspace.createFileSystemWatcher('**/.vscode/git-graph-rs.json');
		this.configWatcher.onDidCreate(this.onConfigWatcherCreateOrChange.bind(this));
		this.configWatcher.onDidChange(this.onConfigWatcherCreateOrChange.bind(this));

		this.repoEventEmitter = new EventEmitter<RepoChangeEvent>();

		this.onWatcherCreateQueue = new BufferedQueue<string>(this.processOnWatcherCreateEvent.bind(this), this.sendRepos.bind(this));
		this.onWatcherChangeQueue = new BufferedQueue<string>(this.processOnWatcherChangeEvent.bind(this), this.sendRepos.bind(this));
		this.checkRepoConfigQueue = new BufferedQueue<string>(this.checkRepoForNewConfig.bind(this), this.sendRepos.bind(this));

		this.startWatchingFolders();
		void this.startupTasks().catch((error) => this.logger.logError('Repository startup tasks failed: ' + error));

		this.registerDisposables(
			// Monitor changes to the workspace folders to:
			// - search added folders for repositories
			// - remove repositories within deleted folders
			// - apply changes to the order of workspace folders
			vscode.workspace.onDidChangeWorkspaceFolders(async (e) => {
				const removed = e.removed.map((folder) => getPathFromUri(folder.uri));
				for (const folder of removed) this.stopWatchingFolder(folder);
				let changes = removed.length > 0 && this.removeReposNotInWorkspace(removed);
				for (const folder of e.added) {
					const directory = getPathFromUri(folder.uri);
					this.startWatchingFolder(directory);
					if (await this.searchDirectoryForRepos(directory, this.maxDepthOfRepoSearch, true)) changes = true;
				}
				if (this.updateReposWorkspaceFolderIndex()) {
					this.extensionState.saveRepos(this.repos);
					changes = true;
				}
				if (changes) this.sendRepos();
			}),

			// Monitor changes to the maxDepthOfRepoSearch Extension Setting, and trigger a new search if needed
			onDidChangeConfiguration((event) => {
				if (event.affectsConfiguration('git-graph-rs.maxDepthOfRepoSearch')) {
					this.maxDepthOfRepoSearchChanged();
				}
			}),

			// Dispose the Repository Event Emitter when disposed
			this.repoEventEmitter,

			// Dispose the configWatcher
			this.configWatcher,

			// Dispose the onWatcherCreateQueue
			this.onWatcherCreateQueue,

			// Dispose the onWatcherChangeQueue
			this.onWatcherChangeQueue,

			// Dispose the checkRepoConfigQueue,
			this.checkRepoConfigQueue,

			// Stop watching folders when disposed
			toDisposable(() => {
				const folders = Object.keys(this.folderWatchers);
				for (let i = 0; i < folders.length; i++) {
					this.stopWatchingFolder(folders[i]);
				}
			})
		);
	}

	/**
	 * Get the Event that can be used to subscribe to updates when the repositories available in Git Graph change.
	 */
	get onDidChangeRepos() {
		return this.repoEventEmitter.subscribe;
	}

	/**
	 * Apply the new value of `git-graph-rs.maxDepthOfRepoSearch` to the RepoManager.
	 */
	private maxDepthOfRepoSearchChanged() {
		const newDepth = getConfig().maxDepthOfRepoSearch;
		if (newDepth > this.maxDepthOfRepoSearch) {
			this.maxDepthOfRepoSearch = newDepth;
			this.searchWorkspaceForRepos();
		} else {
			this.maxDepthOfRepoSearch = newDepth;
		}
	}

	/**
	 * Run various startup tasks when Git Graph is activated.
	 */
	private async startupTasks() {
		this.removeReposNotInWorkspace();
		if (this.updateReposWorkspaceFolderIndex()) {
			this.extensionState.saveRepos(this.repos);
		}
		if (!await this.checkReposExist()) {
			// On startup, ensure that sendRepo is called (even if no changes were made)
			this.sendRepos();
		}
		this.checkReposForNewConfig();
		await this.checkReposForNewSubmodules();
		await Promise.all(Object.keys(this.repos).map(repo => {
			if (getConfig(repo).trackRemoteTags) {
				return this.dataSource.trackRemoteTags(repo);
			}
			return Promise.resolve();
		}));
		await this.searchWorkspaceForRepos();
	}

	/** Remove repositories that are no longer covered by any workspace folder. */
	private removeReposNotInWorkspace(removedFolders?: string[]) {
		const { rootsExact } = getWorkspaceFolderInfoForRepoInclusionMapping();
		let changes = false;
		for (const repo of Object.keys(this.repos)) {
			if (removedFolders && !removedFolders.some((folder) => pathsOverlap(folder, repo))) continue;
			if (!rootsExact.some((folder) => pathsOverlap(folder, repo))) {
				this.removeRepo(repo);
				changes = true;
			}
		}
		return changes;
	}

	/**
	 * Register a new repository with Git Graph.
	 * @param path The path of the repository.
	 * @param loadRepo If TRUE and the Git Graph View is visible, load the Git Graph View with the repository being registered.
	 */
	public registerRepo(path: string, loadRepo: boolean) {
		return new Promise<{ root: string | null, error: string | null }>(async resolve => {
			const detectedRoot = await this.dataSource.repoRoot(path);
			const root = detectedRoot === null ? null : getPathFromStr(detectedRoot);
			if (root === null) {
				resolve({ root: null, error: 'The folder "' + path + '" is not a Git repository.' });
			} else if (typeof this.repos[root] !== 'undefined') {
				resolve({ root: null, error: 'The folder "' + path + '" is contained within the known repository "' + root + '".' });
			} else {
				if (this.ignoredRepos.includes(root)) {
					this.ignoredRepos.splice(this.ignoredRepos.indexOf(root), 1);
					this.extensionState.setIgnoredRepos(this.ignoredRepos);
				}
				await this.addRepo(root);
				this.sendRepos(loadRepo ? root : null);
				resolve({ root: root, error: null });
			}
		});
	}

	/**
	 * Ignore a repository known to Git Graph. Unlike `removeRepo`, ignoring the repository will prevent it from being automatically detected and re-added the next time Visual Studio Code is started.
	 * @param repo The path of the repository.
	 * @returns TRUE => Repository was ignored, FALSE => Repository is not know to Git Graph.
	 */
	public ignoreRepo(repo: string) {
		if (this.isKnownRepo(repo)) {
			if (!this.ignoredRepos.includes(repo)) this.ignoredRepos.push(repo);
			this.extensionState.setIgnoredRepos(this.ignoredRepos);
			this.removeRepo(repo);
			this.sendRepos();
			return true;
		} else {
			return false;
		}
	}


	/* Repo Management */

	/**
	 * Get a set of all known repositories in the current workspace.
	 * @returns The set of repositories.
	 */
	public getRepos() {
		return Object.assign({}, this.repos);
	}

	/**
	 * Get the number of all known repositories in the current workspace.
	 * @returns The number of repositories.
	 */
	public getNumRepos() {
		return Object.keys(this.repos).length;
	}

	/**
	 * Get the repository that contains the specified file.
	 * @param path The path of the file.
	 * @returns The path of the repository containing the file, or NULL if no known repository contains the file.
	 */
	public getRepoContainingFile(path: string) {
		let repoPaths = Object.keys(this.repos), repo = null;
		for (let i = 0; i < repoPaths.length; i++) {
			if (path.startsWith(pathWithTrailingSlash(repoPaths[i])) && (repo === null || repo.length < repoPaths[i].length)) repo = repoPaths[i];
		}
		return repo;
	}

	/**
	 * Get all known repositories that are contained in the specified folder.
	 * @param path The path of the folder.
	 * @returns An array of the paths of all known repositories contained in the specified folder.
	 */
	private getReposInFolder(path: string) {
		let pathFolder = pathWithTrailingSlash(path), repoPaths = Object.keys(this.repos), reposInFolder: string[] = [];
		for (let i = 0; i < repoPaths.length; i++) {
			if (repoPaths[i] === path || repoPaths[i].startsWith(pathFolder)) reposInFolder.push(repoPaths[i]);
		}
		return reposInFolder;
	}

	/**
	 * Get the path of the known repository matching the specified repository path (checking symbolic links if necessary).
	 * @param repo The path of the repository.
	 * @returns The path of the known repository, or NULL if the specified repository is unknown.
	 */
	public async getKnownRepo(repo: string) {
		repo = getPathFromStr(repo);
		if (this.isKnownRepo(repo)) {
			// The path is already known as a repo
			return repo;
		}

		// Check to see if a known repository contains a symlink that resolves the repo
		let canonicalRepo = await realpath(repo);
		let repoPaths = Object.keys(this.repos);
		for (let i = 0; i < repoPaths.length; i++) {
			if (canonicalRepo === (await realpath(repoPaths[i]))) {
				return repoPaths[i];
			}
		}

		// Repo is unknown
		return null;
	}

	/**
	 * Check to see if a repository exactly matches a known repository.
	 * @param repo The path of the repository to check.
	 * @returns TRUE => Known repository, FALSE => Unknown repository.
	 */
	public isKnownRepo(repo: string) {
		return typeof this.repos[repo] !== 'undefined';
	}

	/**
	 * Add a new repository to Git Graph.
	 * @param repo The path of the repository.
	 * @returns TRUE if the repository was added.
	 */
	private async addRepo(repo: string) {
		repo = getPathFromStr(repo);
		if (this.isDisposed() || this.isKnownRepo(repo) || this.ignoredRepos.includes(repo)) {
			return false;
		} else {
			this.repos[repo] = Object.assign({}, DEFAULT_REPO_STATE);
			// Open a repository handle in the Git backend (fire-and-forget: a failure just means the
			// backend reads this repository through the `git` CLI instead)
			this.dataSource.openRepository(repo);
			this.updateReposWorkspaceFolderIndex(repo);
			this.extensionState.saveRepos(this.repos);
			this.logger.log('Added new repo: ' + repo);
			await this.checkRepoForNewConfig(repo, true);
			await this.searchRepoForSubmodules(repo);
			await this.searchRepoForWorktrees(repo);
			return true;
		}
	}

	/**
	 * Remove a known repository from Git Graph.
	 * @param repo The path of the repository.
	 */
	private removeRepo(repo: string) {
		delete this.repos[repo];
		// Release the engine's handle and the cached config data of the removed repository: both
		// would otherwise stay resident for the rest of the editor session
		this.dataSource.closeRepository(repo);
		this.extensionState.saveRepos(this.repos);
		this.logger.log('Removed repo: ' + repo);
	}

	/**
	 * Remove all repositories that are contained within the specified folder.
	 * @param path The path of the folder.
	 * @returns TRUE => At least one repository was removed, FALSE => No repositories were removed.
	 */
	private removeReposWithinFolder(path: string) {
		let reposInFolder = this.getReposInFolder(path);
		for (let i = 0; i < reposInFolder.length; i++) {
			this.removeRepo(reposInFolder[i]);
		}
		return reposInFolder.length > 0;
	}

	/**
	 * Send the latest set of known repositories to subscribers as they have changed.
	 * @param loadRepo The optional path of a repository to load in the Git Graph View.
	 */
	private sendRepos(loadRepo: string | null = null) {
		this.repoEventEmitter.emit({
			repos: this.getRepos(),
			numRepos: this.getNumRepos(),
			loadRepo: loadRepo
		});
	}

	/**
	 * Check that all known repositories still exist. If they don't, remove them.
	 * @returns TRUE => At least one repository was removed or transferred, FALSE => No repositories were removed.
	 */
	public checkReposExist() {
		let repoPaths = Object.keys(this.repos), changes = false;
		return evalPromises(repoPaths, 3, (path) => this.dataSource.repoRoot(path)).then((results) => {
			for (let i = 0; i < repoPaths.length; i++) {
				const repo = repoPaths[i], root = results[i] === null ? null : getPathFromStr(results[i]!);
				if (!this.isKnownRepo(repo) || root === repo) continue;
				// Deleting a nested repository's .git can leave its directory inside the parent
				// repository. Do not transfer the nested state to that parent.
				if (root === null || this.isKnownRepo(root) || this.ignoredRepos.includes(root) ||
					(path.relative(root, repo) !== '' && isWithinDirectory(root, repo))) {
					this.removeRepo(repo);
				} else {
					this.transferRepoState(repo, root);
				}
				changes = true;
			}
		}).catch(() => { }).then(() => {
			if (changes) {
				this.sendRepos();
			}
			return changes;
		});
	}

	/**
	 * Update each repositories workspaceFolderIndex based on the current workspace.
	 * @param repo If provided, only update this specific repository.
	 * @returns TRUE => At least one repository was changed, FALSE => No repositories were changed.
	 */
	private updateReposWorkspaceFolderIndex(repo: string | null = null) {
		const workspaceFolderInfo = getWorkspaceFolderInfoForRepoInclusionMapping();
		const rootsExact = workspaceFolderInfo.rootsExact, rootsFolder = workspaceFolderInfo.rootsFolder, workspaceFolders = workspaceFolderInfo.workspaceFolders;
		const repoPaths = repo !== null && this.isKnownRepo(repo) ? [repo] : Object.keys(this.repos);
		let changes = false, rootIndex: number, workspaceFolderIndex: number | null;
		for (let i = 0; i < repoPaths.length; i++) {
			rootIndex = rootsExact.indexOf(repoPaths[i]);
			if (rootIndex === -1) {
				// Find a workspace folder that contains the repository
				rootIndex = rootsFolder.findIndex((root) => repoPaths[i].startsWith(root));
			}
			if (rootIndex === -1) {
				// Find a workspace folder that is contained within the repository
				const repoPathFolder = pathWithTrailingSlash(repoPaths[i]);
				rootIndex = rootsExact.findIndex((root) => root.startsWith(repoPathFolder));
			}
			workspaceFolderIndex = rootIndex > -1 ? workspaceFolders[rootIndex].index : null;
			if (this.repos[repoPaths[i]].workspaceFolderIndex !== workspaceFolderIndex) {
				this.repos[repoPaths[i]].workspaceFolderIndex = workspaceFolderIndex;
				changes = true;
			}
		}
		return changes;
	}

	/**
	 * Set the state of a known repository.
	 * @param repo The repository the state belongs to.
	 * @param state The state.
	 */
	public setRepoState(repo: string, state: GitRepoState) {
		// The message can arrive for a repository this host no longer knows (removed from disk or
		// the workspace, or ignored, while the webview still had it loaded): assigning would
		// silently re-add it — persisted, resurrecting an ignored/deleted repo, and writing a
		// pin file into a path that may not exist. State for an unknown repo is dropped.
		if (!this.isKnownRepo(repo)) return;
		// The state (and its pinned arrays) arrive deserialized over postMessage, so compare by value
		const pinsChanged = !pinsEqual(this.repos[repo], state);
		this.repos[repo] = state;
		this.extensionState.saveRepos(this.repos);
		if (pinsChanged) {
			this.writeRepoPins(repo);
		}
	}

	/**
	 * Persist the pinned commits and branches of a repository to its External Configuration File (`.vscode/git-graph-rs.json`).
	 * @param repo The path of the repository.
	 */
	private writeRepoPins(repo: string) {
		const state = this.repos[repo];
		if (state === undefined) {
			return;
		}
		this.pinsWriteInFlight.add(repo);
		readExternalConfigFile(repo).then((file) => {
			if (!this.isKnownRepo(repo) || this.repos[repo] !== state) {
				this.pinsWriteInFlight.delete(repo);
				return;
			}
			const contents: ExternalRepoConfig.File = file !== null ? Object.assign({}, file) : {};
			contents.pinnedBranches = state.pinnedBranches;
			contents.pinnedCommits = state.pinnedCommits;
			writeExternalConfigFile(repo, contents).catch(showErrorMessage).then(() => this.pinsWriteInFlight.delete(repo));
		});
	}

	/**
	 * Transfer the repository state from one known repository to another.
	 * @param oldRepo The repository to transfer the state from.
	 * @param newRepo The repository to transfer the state to.
	 */
	private transferRepoState(oldRepo: string, newRepo: string) {
		this.repos[newRepo] = this.repos[oldRepo];
		delete this.repos[oldRepo];
		// The old path no longer names the repository, so its engine handle must not stay resident
		this.dataSource.closeRepository(oldRepo);
		this.updateReposWorkspaceFolderIndex(newRepo);
		this.extensionState.saveRepos(this.repos);
		this.extensionState.transferRepo(oldRepo, newRepo);

		this.logger.log('Transferred repo state: ' + oldRepo + ' -> ' + newRepo);
	}


	/* Repo Searching */

	/**
	 * Search all of the current workspace folders for new repositories (and add them).
	 * @returns TRUE => At least one repository was added, FALSE => No repositories were added.
	 */
	public async searchWorkspaceForRepos() {
		this.logger.log('Searching workspace for new repos ...');
		let rootFolders = vscode.workspace.workspaceFolders, changes = false;
		if (typeof rootFolders !== 'undefined') {
			for (let i = 0; i < rootFolders.length; i++) {
				if (await this.searchDirectoryForRepos(getPathFromUri(rootFolders[i].uri), this.maxDepthOfRepoSearch, true)) changes = true;
			}
		}
		this.logger.log('Completed searching workspace for new repos');
		if (changes) this.sendRepos();
		return changes;
	}

	/**
	 * Search the specified directory for new repositories (and add them).
	 * @param directory The path of the directory to search.
	 * @param maxDepth The maximum depth to recursively search.
	 * @returns TRUE => At least one repository was added, FALSE => No repositories were added.
	 */
	private async searchDirectoryForRepos(directory: string, maxDepth: number, includeEnclosingRepo = false) {
		let changes = false;
		let directories = [directory];
		for (let depth = 0; directories.length > 0 && !this.isDisposed(); depth++) {
			const descend = depth < maxDepth;
			const nextLevel = await evalPromises(directories, 8, async (candidate) => {
				const entries = descend ? await fs.promises.readdir(candidate, { withFileTypes: true }).catch(() => []) : [];
				const allowEnclosing = depth === 0 && includeEnclosingRepo;
				try {
					if (!this.isKnownRepo(candidate) && !this.ignoredRepos.includes(candidate)) {
						// Probe Git only at a workspace root or where there is a .git marker (a file
						// for worktrees and initialized submodules). Keep scanning below known roots.
						if (allowEnclosing || (descend ? entries.some((entry) => entry.name === '.git') : await doesPathExist(path.join(candidate, '.git')))) {
							const root = await this.dataSource.repoRoot(candidate);
							const folders = vscode.workspace.workspaceFolders ?? [];
							if (root !== null && (allowEnclosing || path.relative(candidate, root) === '') &&
								folders.some((folder) => pathsOverlap(getPathFromUri(folder.uri), root)) && await this.addRepo(root)) {
								changes = true;
							}
						}
					}
				} catch (_) { } // An unreadable or vanishing directory must not abort the scan
				return entries.filter(isScannableFolder)
					.map((entry) => pathWithTrailingSlash(candidate) + entry.name);
			});
			directories = [];
			for (const children of nextLevel) {
				for (const child of children) directories.push(child);
			}
		}
		return changes;
	}

	/**
	 * Check the know repositories for any new submodules (and add them).
	 */
	private async checkReposForNewSubmodules() {
		let repoPaths = Object.keys(this.repos), changes = false;
		for (let i = 0; i < repoPaths.length; i++) {
			if (await this.searchRepoForSubmodules(repoPaths[i])) changes = true;
		}
		if (changes) this.sendRepos();
	}

	/**
	 * Search a repository for any new submodules (and add them).
	 * @param repo The path of the repository to search.
	 * @returns TRUE => At least one submodule was added, FALSE => No submodules were added.
	 */
	private async searchRepoForSubmodules(repo: string) {
		let submodules = await this.dataSource.getSubmodules(repo), changes = false;
		for (let i = 0; i < submodules.length; i++) {
			if (!this.isKnownRepo(submodules[i])) {
				if (await this.addRepo(submodules[i])) changes = true;
			}
		}
		return changes;
	}

	/**
	 * Add the repository's working trees that live inside the workspace. Worktrees are often kept
	 * in a hidden directory (e.g. `.worktrees/`), which the workspace scan skips.
	 * @param repo The path of the repository to search.
	 * @returns TRUE => At least one worktree was added, FALSE => No worktrees were added.
	 */
	private async searchRepoForWorktrees(repo: string) {
		const worktrees = await this.dataSource.getWorktrees(repo);
		const folders = vscode.workspace.workspaceFolders ?? [];
		let changes = false;
		for (const worktree of worktrees) {
			const worktreePath = getPathFromStr(path.normalize(worktree.path));
			if (worktreePath === repo || worktree.prunable || this.isKnownRepo(worktreePath) || this.ignoredRepos.includes(worktreePath)) continue;
			if (!folders.some((folder) => pathsOverlap(getPathFromUri(folder.uri), worktreePath))) continue;
			if (await isDirectory(worktreePath) && await this.addRepo(worktreePath)) changes = true;
		}
		return changes;
	}


	/* Workspace Folder Watching */

	/**
	 * Start watching each of the folders in the current workspace for changes.
	 */
	private startWatchingFolders() {
		let rootFolders = vscode.workspace.workspaceFolders;
		if (typeof rootFolders !== 'undefined') {
			for (let i = 0; i < rootFolders.length; i++) {
				this.startWatchingFolder(getPathFromUri(rootFolders[i].uri));
			}
		}
	}

	/**
	 * Start watching the specified directory for file system events.
	 * @param path The path of the directory.
	 */
	private startWatchingFolder(path: string) {
		// A watcher for this folder may already exist (e.g. the folder was added while the
		// startup scan that ends in startWatchingFolders was still running): replacing the map
		// entry would orphan the previous watcher, whose handlers keep firing for the rest of
		// the session — every event in the folder processed twice.
		if (this.folderWatchers[path] !== undefined) return;
		const watcher = vscode.workspace.createFileSystemWatcher(new vscode.RelativePattern(path, '**'));
		watcher.onDidCreate(this.onWatcherCreate.bind(this));
		watcher.onDidChange(this.onWatcherChange.bind(this));
		watcher.onDidDelete(this.onWatcherDelete.bind(this));
		this.folderWatchers[path] = watcher;
	}

	/**
	 * Stop watching the specified directory for file system events.
	 * @param path The path of the directory.
	 */
	private stopWatchingFolder(path: string) {
		if (this.folderWatchers[path] !== undefined) {
			this.folderWatchers[path].dispose();
			delete this.folderWatchers[path];
		}
	}

	/**
	 * Handle a file system creation event.
	 * @param uri The URI of the creation event.
	 */
	private onWatcherCreate(uri: vscode.Uri) {
		let path = getPathFromUri(uri);
		if (path.indexOf('/.git/') > -1) return;
		if (path.endsWith('/.git')) path = path.slice(0, -5);
		this.onWatcherCreateQueue.enqueue(path);
	}

	/**
	 * Handle a file system change event.
	 * @param uri The URI of the change event.
	 */
	private onWatcherChange(uri: vscode.Uri) {
		let path = getPathFromUri(uri);
		if (path.indexOf('/.git/') > -1) return;
		if (path.endsWith('/.git')) path = path.slice(0, -5);
		this.onWatcherChangeQueue.enqueue(path);
	}

	/**
	 * Handle a file system deletion event.
	 * @param uri The URI of the deletion event.
	 */
	private onWatcherDelete(uri: vscode.Uri) {
		const deleted = getPathFromUri(uri);
		if (deleted.includes('/.git/')) return;
		if (deleted.endsWith('/.git')) {
			const repo = getPathFromStr(path.dirname(deleted));
			if (this.isKnownRepo(repo)) {
				this.removeRepo(repo);
				this.sendRepos();
			}
		} else if (this.removeReposWithinFolder(deleted)) {
			this.sendRepos();
		}
	}

	/** Discover newly initialized repositories and repositories in newly added directories. */
	private async processOnWatcherCreateEvent(directory: string) {
		let remainingDepth = -1;
		for (const folder of vscode.workspace.workspaceFolders ?? []) {
			const root = getPathFromUri(folder.uri);
			if (!isWithinDirectory(root, directory)) continue;
			const parts = getPathFromStr(path.relative(root, directory)).split('/').filter(Boolean);
			if (parts.some((part) => part.startsWith('.') || REPO_SCAN_EXCLUDED_FOLDERS.has(part))) continue;
			remainingDepth = Math.max(remainingDepth, this.maxDepthOfRepoSearch - parts.length);
		}
		if (remainingDepth < 0 || !await isDirectory(directory)) return false;
		return this.searchDirectoryForRepos(directory, remainingDepth);
	}

	/**
	 * Process a file system change event.
	 * @param path The path of the file that was changed.
	 * @returns TRUE => Change was made. FALSE => No change was made.
	 */
	private async processOnWatcherChangeEvent(path: string) {
		if (!await doesPathExist(path)) {
			if (this.removeReposWithinFolder(path)) {
				return true;
			}
		}
		return false;
	}


	/* Repository Configuration Management */

	/**
	 * Check the known repositories for new configuration files.
	 */
	private checkReposForNewConfig() {
		Object.keys(this.repos).forEach((repo) => this.checkRepoConfigQueue.enqueue(repo));
	}

	/**
	 * Check to see if the repository has a new configuration file.
	 * @param repo The repository to check.
	 * @param isRepoNew Is the repository new (was it just added)
	 */
	private async checkRepoForNewConfig(repo: string, isRepoNew: boolean = false) {
		let changes = false;
		try {
			const file = await readExternalConfigFile(repo);
			const state = this.repos[repo];
			if (state && file !== null && !this.pinsWriteInFlight.has(repo)) {
				// Skip importing pins while a write is in flight: the watcher event that triggered
				// this check may be our own write, and importing the file's (older) pins would
				// silently revert the user's pins in memory before they are written back
				const pinnedBranches = Array.isArray(file.pinnedBranches) ? file.pinnedBranches : [];
				const pinnedCommits = Array.isArray(file.pinnedCommits) ? file.pinnedCommits : [];
				if (!pinsEqual(state, { pinnedBranches, pinnedCommits })) {
					state.pinnedBranches = pinnedBranches;
					state.pinnedCommits = pinnedCommits;
					this.extensionState.saveRepos(this.repos);
					changes = true;
				}
			}
			if (state && file !== null && typeof file.exportedAt === 'number' && file.exportedAt > state.lastImportAt) {
				const validationError = validateExternalConfigFile(file);
				if (validationError === null) {
					const yes = t('yesButton');
					const action = isRepoNew ? yes : await vscode.window.showInformationMessage(t('newerRepoConfigDetected', state.name || getRepoName(repo)), yes, t('noButton'));
					if (this.isKnownRepo(repo) && action) {
						const state = this.repos[repo];
						if (action === yes) {
							applyExternalConfigFile(file, state);
						}
						state.lastImportAt = file.exportedAt;
						this.extensionState.saveRepos(this.repos);
						if (!isRepoNew && action === yes) {
							showInformationMessage(t('repoConfigImported', state.name || getRepoName(repo)));
						}
						changes = true;
					}
				} else {
					showErrorMessage(t('repoConfigInvalidValue', validationError, getPathFromStr(path.join(repo, '.vscode', 'git-graph-rs.json'))));
				}
			}
		} catch (_) { }
		return changes;
	}

	/**
	 * Handle a file system create or change event for a configuration file.
	 * @param uri The URI of the create or change event.
	 */
	private onConfigWatcherCreateOrChange(uri: vscode.Uri) {
		const path = getPathFromUri(uri);
		const repo = this.getRepoContainingFile(path);
		if (repo !== null) {
			this.checkRepoConfigQueue.enqueue(repo);
		}
	}

	/**
	 * Export a repositories configuration.
	 * @param repo The path of the repository to export.
	 * @returns The ErrorInfo produced when performing this action.
	 */
	public exportRepoConfig(repo: string): Promise<ErrorInfo> {
		const file = generateExternalConfigFile(this.repos[repo]);
		return writeExternalConfigFile(repo, file).then((message) => {
			showInformationMessage(message);
			if (this.isKnownRepo(repo)) {
				this.repos[repo].lastImportAt = file.exportedAt!;
				this.extensionState.saveRepos(this.repos);
			}
			return null;
		}, (error) => error);
	}
}

function isWithinDirectory(parent: string, directory: string) {
	const relative = path.relative(parent, directory);
	return relative !== '..' && !relative.startsWith('..' + path.sep) && !path.isAbsolute(relative);
}

function pathsOverlap(a: string, b: string) {
	return isWithinDirectory(a, b) || isWithinDirectory(b, a);
}

/**
 * Gets the current workspace folders, and generates information required to identify whether a repository is within any of the workspace folders.
 * @returns The Workspace Folder Information.
 */
function getWorkspaceFolderInfoForRepoInclusionMapping() {
	let rootsExact = [], rootsFolder = [], workspaceFolders = vscode.workspace.workspaceFolders || [], path;
	for (let i = 0; i < workspaceFolders.length; i++) {
		path = getPathFromUri(workspaceFolders[i].uri);
		rootsExact.push(path);
		rootsFolder.push(pathWithTrailingSlash(path));
	}
	return {
		workspaceFolders: workspaceFolders,
		rootsExact: rootsExact,
		rootsFolder: rootsFolder
	};
}

/**
 * Check if the specified path is a directory.
 * @param path The path to check.
 * @returns TRUE => Directory, FALSE => Not a directory.
 */
function isDirectory(path: string) {
	return new Promise<boolean>(resolve => {
		fs.lstat(path, (err, stats) => {
			resolve(err ? false : stats.isDirectory());
		});
	});
}

/**
 * Check if the specified path exists.
 * @param path The path to check.
 * @returns TRUE => Path exists, FALSE => Path doesn't exist.
 */
function doesPathExist(path: string) {
	return new Promise<boolean>(resolve => {
		fs.stat(path, err => resolve(!err));
	});
}


/** External Repo Config File */

export namespace ExternalRepoConfig {

	export const enum FileViewType {
		Tree = 'tree',
		List = 'list'
	}

	export interface IssueLinkingConfig {
		readonly issue: string;
		readonly url: string;
	}

	export const enum PullRequestProvider {
		Bitbucket = 'bitbucket',
		Custom = 'custom',
		GitHub = 'github',
		GitLab = 'gitlab'
	}

	interface PullRequestConfigBuiltIn extends PullRequestConfigBase {
		readonly provider: Exclude<PullRequestProvider, PullRequestProvider.Custom>;
		readonly custom: null;
	}

	interface PullRequestConfigCustom extends PullRequestConfigBase {
		readonly provider: PullRequestProvider.Custom;
		readonly custom: {
			readonly name: string,
			readonly templateUrl: string
		};
	}

	export type PullRequestConfig = PullRequestConfigBuiltIn | PullRequestConfigCustom;

	export interface File {
		commitOrdering?: RepoCommitOrdering;
		fileViewType?: FileViewType;
		hideRemotes?: string[];
		includeCommitsMentionedByReflogs?: boolean;
		issueLinkingConfig?: IssueLinkingConfig;
		name?: string | null;
		onlyFollowFirstParent?: boolean;
		onRepoLoadShowCheckedOutBranch?: boolean;
		onRepoLoadShowSpecificBranches?: string[];
		pinnedBranches?: string[];
		pinnedCommits?: PinnedCommit[];
		pullRequestConfig?: PullRequestConfig;
		showRemoteBranches?: boolean;
		showStashes?: boolean;
		showTags?: boolean;
		exportedAt?: number;
	}

}

/**
 * Reads the External Configuration File for a repository from the File System.
 * @param repo The path of the repository.
 * @returns A promise resolving to the parsed config file, or NULL if the file couldn't be read or parsed.
 */
function readExternalConfigFile(repo: string) {
	return new Promise<Readonly<ExternalRepoConfig.File> | null>((resolve) => {
		fs.readFile(path.join(repo, '.vscode', 'git-graph-rs.json'), (err, data) => {
			if (err) {
				resolve(null);
			} else {
				try {
					const contents = JSON.parse(data.toString());
					resolve(typeof contents === 'object' ? contents : null);
				} catch (_) {
					resolve(null);
				}
			}
		});
	});
}

/**
 * Writes the External Configuration File of a repository to the File System.
 * @param repo The path of the repository.
 * @param file The file contents.
 * @returns A promise that resolves to a success message, or rejects to an error message.
 */
function writeExternalConfigFile(repo: string, file: ExternalRepoConfig.File) {
	return new Promise<string>((resolve, reject) => {
		const vscodePath = path.join(repo, '.vscode');
		fs.mkdir(vscodePath, (err) => {
			if (!err || err.code === 'EEXIST') {
				const configPath = path.join(vscodePath, 'git-graph-rs.json');
				fs.writeFile(configPath, JSON.stringify(file, null, 4), (err) => {
					if (err) {
						reject(t('writeRepoConfigFailed', getPathFromStr(configPath)));
					} else {
						resolve(t('repoConfigExported', getPathFromStr(configPath)));
					}
				});
			} else {
				reject(t('checkVscodeDirFailed', getPathFromStr(vscodePath)));
			}
		});
	});
}

/**
 * Generate the External Config File's contents from the Git Repositories state.
 * @param state The state being exported.
 * @returns The file contents.
 */
function generateExternalConfigFile(state: GitRepoState): Readonly<ExternalRepoConfig.File> {
	const file: ExternalRepoConfig.File = {};

	if (state.commitOrdering !== RepoCommitOrdering.Default) {
		file.commitOrdering = state.commitOrdering;
	}
	if (state.fileViewType !== FileViewType.Default) {
		switch (state.fileViewType) {
			case FileViewType.Tree:
				file.fileViewType = ExternalRepoConfig.FileViewType.Tree;
				break;
			case FileViewType.List:
				file.fileViewType = ExternalRepoConfig.FileViewType.List;
				break;
		}
	}
	if (state.hideRemotes.length > 0) {
		file.hideRemotes = state.hideRemotes;
	}
	if (state.includeCommitsMentionedByReflogs !== BooleanOverride.Default) {
		file.includeCommitsMentionedByReflogs = state.includeCommitsMentionedByReflogs === BooleanOverride.Enabled;
	}
	if (state.issueLinkingConfig !== null) {
		file.issueLinkingConfig = state.issueLinkingConfig;
	}
	if (state.name !== null) {
		file.name = state.name;
	}
	if (state.onlyFollowFirstParent !== BooleanOverride.Default) {
		file.onlyFollowFirstParent = state.onlyFollowFirstParent === BooleanOverride.Enabled;
	}
	if (state.onRepoLoadShowCheckedOutBranch !== BooleanOverride.Default) {
		file.onRepoLoadShowCheckedOutBranch = state.onRepoLoadShowCheckedOutBranch === BooleanOverride.Enabled;
	}
	if (state.onRepoLoadShowSpecificBranches !== null) {
		file.onRepoLoadShowSpecificBranches = state.onRepoLoadShowSpecificBranches;
	}
	file.pinnedBranches = state.pinnedBranches;
	file.pinnedCommits = state.pinnedCommits;
	if (state.pullRequestConfig !== null) {
		let provider: ExternalRepoConfig.PullRequestProvider;
		switch (state.pullRequestConfig.provider) {
			case PullRequestProvider.Bitbucket:
				provider = ExternalRepoConfig.PullRequestProvider.Bitbucket;
				break;
			case PullRequestProvider.Custom:
				provider = ExternalRepoConfig.PullRequestProvider.Custom;
				break;
			case PullRequestProvider.GitHub:
				provider = ExternalRepoConfig.PullRequestProvider.GitHub;
				break;
			case PullRequestProvider.GitLab:
				provider = ExternalRepoConfig.PullRequestProvider.GitLab;
				break;
		}
		file.pullRequestConfig = Object.assign({}, state.pullRequestConfig, { provider: provider });
	}
	if (state.showRemoteBranchesV2 !== BooleanOverride.Default) {
		file.showRemoteBranches = state.showRemoteBranchesV2 === BooleanOverride.Enabled;
	}
	if (state.showStashes !== BooleanOverride.Default) {
		file.showStashes = state.showStashes === BooleanOverride.Enabled;
	}
	if (state.showTags !== BooleanOverride.Default) {
		file.showTags = state.showTags === BooleanOverride.Enabled;
	}
	file.exportedAt = (new Date()).getTime();
	return file;
}

/**
 * Validate an external configuration file.
 * @param file The external configuration file.
 * @returns NULL => Value, String => The first field that is invalid.
 */
function validateExternalConfigFile(file: Readonly<ExternalRepoConfig.File>) {
	if (typeof file.commitOrdering !== 'undefined' && file.commitOrdering !== RepoCommitOrdering.Date && file.commitOrdering !== RepoCommitOrdering.AuthorDate && file.commitOrdering !== RepoCommitOrdering.Topological) {
		return 'commitOrdering';
	}
	if (typeof file.fileViewType !== 'undefined' && file.fileViewType !== ExternalRepoConfig.FileViewType.Tree && file.fileViewType !== ExternalRepoConfig.FileViewType.List) {
		return 'fileViewType';
	}
	if (typeof file.hideRemotes !== 'undefined' && (!Array.isArray(file.hideRemotes) || file.hideRemotes.some((remote) => typeof remote !== 'string'))) {
		return 'hideRemotes';
	}
	if (typeof file.includeCommitsMentionedByReflogs !== 'undefined' && typeof file.includeCommitsMentionedByReflogs !== 'boolean') {
		return 'includeCommitsMentionedByReflogs';
	}
	if (typeof file.issueLinkingConfig !== 'undefined' && (typeof file.issueLinkingConfig !== 'object' || file.issueLinkingConfig === null || typeof file.issueLinkingConfig.issue !== 'string' || typeof file.issueLinkingConfig.url !== 'string')) {
		return 'issueLinkingConfig';
	}
	if (typeof file.name !== 'undefined' && typeof file.name !== 'string') {
		return 'name';
	}
	if (typeof file.onlyFollowFirstParent !== 'undefined' && typeof file.onlyFollowFirstParent !== 'boolean') {
		return 'onlyFollowFirstParent';
	}
	if (typeof file.onRepoLoadShowCheckedOutBranch !== 'undefined' && typeof file.onRepoLoadShowCheckedOutBranch !== 'boolean') {
		return 'onRepoLoadShowCheckedOutBranch';
	}
	if (typeof file.onRepoLoadShowSpecificBranches !== 'undefined' && (!Array.isArray(file.onRepoLoadShowSpecificBranches) || file.onRepoLoadShowSpecificBranches.some((branch) => typeof branch !== 'string'))) {
		return 'onRepoLoadShowSpecificBranches';
	}
	if (typeof file.pinnedBranches !== 'undefined' && (!Array.isArray(file.pinnedBranches) || file.pinnedBranches.some((branch) => typeof branch !== 'string'))) {
		return 'pinnedBranches';
	}
	if (typeof file.pinnedCommits !== 'undefined' && (!Array.isArray(file.pinnedCommits) || file.pinnedCommits.some((commit) => typeof commit !== 'object' || commit === null || typeof commit.hash !== 'string' || typeof commit.summary !== 'string'
		|| (typeof commit.author !== 'undefined' && typeof commit.author !== 'string')
		|| (typeof commit.email !== 'undefined' && typeof commit.email !== 'string')
		|| (typeof commit.date !== 'undefined' && typeof commit.date !== 'number')))) {
		return 'pinnedCommits';
	}
	if (typeof file.pullRequestConfig !== 'undefined' && (
		typeof file.pullRequestConfig !== 'object' ||
		file.pullRequestConfig === null ||
		(
			file.pullRequestConfig.provider !== ExternalRepoConfig.PullRequestProvider.Bitbucket &&
			(file.pullRequestConfig.provider !== ExternalRepoConfig.PullRequestProvider.Custom || typeof file.pullRequestConfig.custom !== 'object' || file.pullRequestConfig.custom === null || typeof file.pullRequestConfig.custom.name !== 'string' || typeof file.pullRequestConfig.custom.templateUrl !== 'string') &&
			file.pullRequestConfig.provider !== ExternalRepoConfig.PullRequestProvider.GitHub &&
			file.pullRequestConfig.provider !== ExternalRepoConfig.PullRequestProvider.GitLab
		) ||
		typeof file.pullRequestConfig.hostRootUrl !== 'string' ||
		typeof file.pullRequestConfig.sourceRemote !== 'string' ||
		typeof file.pullRequestConfig.sourceOwner !== 'string' ||
		typeof file.pullRequestConfig.sourceRepo !== 'string' ||
		(typeof file.pullRequestConfig.destRemote !== 'string' && file.pullRequestConfig.destRemote !== null) ||
		typeof file.pullRequestConfig.destOwner !== 'string' ||
		typeof file.pullRequestConfig.destRepo !== 'string' ||
		typeof file.pullRequestConfig.destProjectId !== 'string' ||
		typeof file.pullRequestConfig.destBranch !== 'string'
	)) {
		return 'pullRequestConfig';
	}
	if (typeof file.showRemoteBranches !== 'undefined' && typeof file.showRemoteBranches !== 'boolean') {
		return 'showRemoteBranches';
	}
	if (typeof file.showStashes !== 'undefined' && typeof file.showStashes !== 'boolean') {
		return 'showStashes';
	}
	if (typeof file.showTags !== 'undefined' && typeof file.showTags !== 'boolean') {
		return 'showTags';
	}
	return null;
}

/**
 * Apply the configuration provided in an external configuration file to a repository state.
 * @param file The file to apply.
 * @param state The state to be updated.
 */
function applyExternalConfigFile(file: Readonly<ExternalRepoConfig.File>, state: GitRepoState) {
	if (typeof file.commitOrdering !== 'undefined') {
		state.commitOrdering = file.commitOrdering;
	}
	if (typeof file.fileViewType !== 'undefined') {
		switch (file.fileViewType) {
			case ExternalRepoConfig.FileViewType.Tree:
				state.fileViewType = FileViewType.Tree;
				break;
			case ExternalRepoConfig.FileViewType.List:
				state.fileViewType = FileViewType.List;
				break;
		}
	}
	if (typeof file.hideRemotes !== 'undefined') {
		state.hideRemotes = file.hideRemotes;
	}
	if (typeof file.includeCommitsMentionedByReflogs !== 'undefined') {
		state.includeCommitsMentionedByReflogs = file.includeCommitsMentionedByReflogs ? BooleanOverride.Enabled : BooleanOverride.Disabled;
	}
	if (typeof file.issueLinkingConfig !== 'undefined') {
		state.issueLinkingConfig = {
			issue: file.issueLinkingConfig.issue,
			url: file.issueLinkingConfig.url
		};
	}
	if (typeof file.name !== 'undefined') {
		state.name = file.name;
	}
	if (typeof file.onlyFollowFirstParent !== 'undefined') {
		state.onlyFollowFirstParent = file.onlyFollowFirstParent ? BooleanOverride.Enabled : BooleanOverride.Disabled;
	}
	if (typeof file.onRepoLoadShowCheckedOutBranch !== 'undefined') {
		state.onRepoLoadShowCheckedOutBranch = file.onRepoLoadShowCheckedOutBranch ? BooleanOverride.Enabled : BooleanOverride.Disabled;
	}
	if (typeof file.onRepoLoadShowSpecificBranches !== 'undefined') {
		state.onRepoLoadShowSpecificBranches = file.onRepoLoadShowSpecificBranches;
	}
	if (typeof file.pullRequestConfig !== 'undefined') {
		let provider: PullRequestProvider;
		switch (file.pullRequestConfig.provider) {
			case ExternalRepoConfig.PullRequestProvider.Bitbucket:
				provider = PullRequestProvider.Bitbucket;
				break;
			case ExternalRepoConfig.PullRequestProvider.Custom:
				provider = PullRequestProvider.Custom;
				break;
			case ExternalRepoConfig.PullRequestProvider.GitHub:
				provider = PullRequestProvider.GitHub;
				break;
			case ExternalRepoConfig.PullRequestProvider.GitLab:
				provider = PullRequestProvider.GitLab;
				break;
		}
		state.pullRequestConfig = <PullRequestConfig>{
			provider: provider,
			custom: provider === PullRequestProvider.Custom
				? {
					name: file.pullRequestConfig.custom!.name,
					templateUrl: file.pullRequestConfig.custom!.templateUrl
				}
				: null,
			hostRootUrl: file.pullRequestConfig.hostRootUrl,
			sourceRemote: file.pullRequestConfig.sourceRemote,
			sourceOwner: file.pullRequestConfig.sourceOwner,
			sourceRepo: file.pullRequestConfig.sourceRepo,
			destRemote: file.pullRequestConfig.destRemote,
			destOwner: file.pullRequestConfig.destOwner,
			destRepo: file.pullRequestConfig.destRepo,
			destProjectId: file.pullRequestConfig.destProjectId,
			destBranch: file.pullRequestConfig.destBranch
		};
	}
	if (typeof file.showRemoteBranches !== 'undefined') {
		state.showRemoteBranchesV2 = file.showRemoteBranches ? BooleanOverride.Enabled : BooleanOverride.Disabled;
	}
	if (typeof file.showStashes !== 'undefined') {
		state.showStashes = file.showStashes ? BooleanOverride.Enabled : BooleanOverride.Disabled;
	}
	if (typeof file.showTags !== 'undefined') {
		state.showTags = file.showTags ? BooleanOverride.Enabled : BooleanOverride.Disabled;
	}
}

/**
 * Compare the pinned branches and commits of two repository states by value.
 * @param a The first repository state (or a partial state with the pins to compare).
 * @param b The second repository state.
 * @returns TRUE if both the pinned branches and pinned commits are equal.
 */
function pinsEqual(a: Pick<GitRepoState, 'pinnedBranches' | 'pinnedCommits'>, b: Pick<GitRepoState, 'pinnedBranches' | 'pinnedCommits'>) {
	if (a.pinnedBranches.length !== b.pinnedBranches.length || a.pinnedCommits.length !== b.pinnedCommits.length) return false;
	return a.pinnedBranches.every((branch, i) => branch === b.pinnedBranches[i])
		&& a.pinnedCommits.every((commit, i) => {
			const other = b.pinnedCommits[i];
			return other !== undefined && commit.hash === other.hash && commit.summary === other.summary
				&& commit.author === other.author && commit.email === other.email && commit.date === other.date;
		});
}
