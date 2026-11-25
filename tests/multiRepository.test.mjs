import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { it } from 'node:test';
import { bootRealView, fireRepoFileEvent, sleep } from './webviewRealPipelineHarness.mjs';

const normalized = (p) => p.replace(/\\/g, '/');
const git = (repo, ...args) => execFileSync('git', args, { cwd: repo, encoding: 'utf8' }).trim();

function init(repo, subject) {
	fs.mkdirSync(repo, { recursive: true });
	git(repo, 'init', '-q', '-b', 'main');
	git(repo, '-c', 'user.name=Test', '-c', 'user.email=test@example.com', '-c', 'commit.gpgsign=false', 'commit', '-q', '--allow-empty', '-m', subject);
}

async function waitFor(condition, description) {
	for (let i = 0; i < 300; i++) {
		const result = condition();
		if (result) return result;
		await sleep(50);
	}
	assert.fail(description);
}

it('discovers nested repositories and worktrees and keeps rapid switches scoped to the selected repository', { timeout: 60000 }, async () => {
	const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'gg-multi-'));
	const parent = path.join(tmp, 'parent');
	const nested = path.join(parent, 'libs', 'nested');
	const other = path.join(tmp, 'second-root');
	const worktree = path.join(parent, '.worktrees', 'topic');
	const deep = path.join(parent, 'a', 'b', 'c', 'outside-depth');
	const removed = path.join(parent, 'libs', 'removed-later');
	const late = path.join(parent, 'libs', 'late');
	let h;
	let releaseRead;
	try {
		init(parent, 'parent history');
		init(nested, 'nested history');
		init(other, 'second history');
		init(deep, 'outside default scan depth');
		init(removed, 'removed later');
		git(parent, 'worktree', 'add', '-q', '-b', 'topic', worktree);
		fs.mkdirSync(late); // Its .git marker appears while the view is open.
		h = await bootRealView(parent, { workspaceFolders: [parent, other] });
		const view = h.GitGraphView.currentPanel;
		const options = () => Array.from(h.document.querySelectorAll('#repoDropdown .dropdownOption'));
		const option = (repo) => options().find((elem) => normalized(elem.querySelector('.dropdownOptionInfo')?.title ?? '') === normalized(repo));
		const select = (repo) => {
			h.document.querySelector('#repoDropdown .dropdownCurrentValue').click();
			option(repo).click();
		};
		const row = (subject) => h.rows().find((elem) => elem.textContent.includes(subject));

		await waitFor(() => option(parent) && option(nested) && option(other) && option(worktree),
			'the dropdown lists both workspace roots, the nested repository, and the worktree: ' +
			JSON.stringify(options().map((elem) => elem.querySelector('.dropdownOptionInfo')?.title)));
		assert.equal(option(deep), undefined, 'repositories deeper than the default scan depth are not discovered');
		await waitFor(() => row('parent history'), 'the first workspace repository loads');

		// Hold the nested repository's info response until the second selection has loaded: a
		// late answer for the abandoned selection must not take over the active repository.
		const pendingRead = new Promise((resolve) => { releaseRead = resolve; });
		const getRepoInfo = view.dataSource.getRepoInfo.bind(view.dataSource);
		view.dataSource.getRepoInfo = async (repo, ...args) => {
			if (repo === normalized(nested)) await pendingRead;
			return getRepoInfo(repo, ...args);
		};
		let staleRequest;
		const respond = view.respondToMessage.bind(view);
		view.respondToMessage = (msg) => {
			const reply = respond(msg);
			if (msg.command === 'loadRepoInfo' && msg.repo === normalized(nested)) staleRequest = reply;
			return reply;
		};
		select(nested);
		assert.ok(staleRequest, 'the nested repository info request is pending');
		select(other);
		await waitFor(() => row('second history'), 'the second repository loads while the nested request is pending');
		releaseRead();
		await staleRequest;
		assert.equal(view.automationState().currentRepo, normalized(other));
		assert.equal(view.extensionState.getLastActiveRepo(), normalized(other));
		assert.equal(view.repoFileWatcher.getRepo(), normalized(other));
		assert.ok(row('second history'), 'the late nested response did not replace the rendered history');

		select(nested);
		const commit = await waitFor(() => row('nested history'), 'selecting a nested repository loads its own history');
		assert.equal(row('second history'), undefined);
		commit.dispatchEvent(new h.window.MouseEvent('contextmenu', { bubbles: true, cancelable: true }));
		const addTag = [...h.document.querySelectorAll('.contextMenuItem')].find((item) => item.textContent === 'Add Tag…');
		assert.ok(addTag);
		addTag.click();
		const input = h.document.getElementById('dialogInput0');
		input.value = 'nested-only';
		input.dispatchEvent(new h.window.KeyboardEvent('keyup', { bubbles: true }));
		h.document.getElementById('dialogAction').click();
		await waitFor(() => row('nested history')?.textContent.includes('nested-only'), 'a tag created from the selected graph appears on its commit');
		assert.equal(git(nested, 'tag', '--list'), 'nested-only');
		assert.equal(git(parent, 'tag', '--list'), '');
		assert.equal(git(other, 'tag', '--list'), '');

		// A repository initialized inside a discovered directory appears without a restart.
		init(late, 'initialized after opening');
		fireRepoFileEvent('create', path.join(late, '.git'));
		await waitFor(() => option(late), 'initializing a subdirectory adds it to the open dropdown');
		fs.rmSync(path.join(late, '.git'), { recursive: true, force: true });
		fireRepoFileEvent('delete', path.join(late, '.git'));
		await waitFor(() => !option(late), 'removing Git metadata removes just that repository');
		assert.ok(option(parent) && option(nested));

		// Deleting a nested repository's .git while its directory stays behind removes that
		// repository on the periodic existence check, rather than transferring its state to the
		// containing repository.
		const parentState = view.repoManager.getRepos()[parent];
		fs.rmSync(path.join(removed, '.git'), { recursive: true, force: true });
		await view.repoManager.checkReposExist();
		assert.equal(view.repoManager.getRepos()[removed], undefined);
		assert.equal(view.repoManager.getRepos()[parent], parentState);
	} finally {
		releaseRead?.();
		if (h) {
			h.dispose();
			h.window.close();
		}
		fs.rmSync(tmp, { recursive: true, force: true, maxRetries: 10, retryDelay: 100 });
	}
});

it('merges saved Windows repositories that differ only by drive-letter case', { skip: !/^[A-Za-z]:[\\/]/.test(os.tmpdir()) || process.platform !== 'win32' }, async () => {
	const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'gg-drive-'));
	const normalizedDirectory = normalized(directory);
	const repo = normalizedDirectory[0].toUpperCase() + normalizedDirectory.slice(1);
	const alias = normalizedDirectory[0].toLowerCase() + normalizedDirectory.slice(1);
	let harness;
	try {
		init(repo, 'Windows drive alias');
		harness = await bootRealView(repo, {
			workspaceFolders: [alias],
			workspaceState: {
				repoStates: { [repo]: {}, [alias]: { name: 'Saved repository' } },
				lastActiveRepo: alias
			}
		});
		const view = harness.GitGraphView.currentPanel;
		await waitFor(() => harness.rows().some((row) => row.textContent.includes('Windows drive alias')), 'the saved repository loads');
		assert.deepEqual(Object.keys(view.repoManager.getRepos()), [repo]);
		assert.deepEqual(Object.keys(view.extensionState.getRepos()), [repo]);
		assert.equal(view.extensionState.getRepos()[repo].name, 'Saved repository');
		assert.equal(view.extensionState.getLastActiveRepo(), repo);
		assert.equal(await view.repoManager.getKnownRepo(alias), repo);
		assert.ok(harness.document.querySelector('.singleRepo'));
	} finally {
		harness?.dispose();
		harness?.window.close();
		fs.rmSync(directory, { recursive: true, force: true, maxRetries: 20, retryDelay: 100 });
	}
});
