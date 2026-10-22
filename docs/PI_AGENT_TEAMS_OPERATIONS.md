# Pi Agent Teams: safe operating procedure

This procedure applies to `@codexstar/pi-agent-teams`. It is separate from
Codex's native collaboration API, the repository Hive queue, and Archon. Use
only one scheduler for a task.

## Before assigning work

1. In the active Pi session, inspect `/team list`, `/team panel`, and
   `/team task list`; use `/team task show <id>` and `/team doctor` when status
   or ownership is ambiguous. Do not infer the live roster from old reports,
   event logs, process-name searches, or a stale `config.json` alone.
2. Check the selected teammate is actually available (not `stopped`/`offline`,
   not in a shutdown handshake, and not already handling other work). A
   completed task proves only that its task completed; it does not prove the
   teammate is currently alive.
3. Give one bounded task with exact source paths, read/write limits, and an
   output location in that worker's existing sandbox. For Lean work, workers
   do not edit live owner files or run builds unless explicitly authorized.

### API-only fallback

The LLM-callable `teams` tool does not expose `/team list`, `/team panel`,
`/team doctor`, or `/team task list` actions. If those Pi commands are not
available in the current interface, read the file-backed task/member records
for diagnosis, but treat them as snapshots rather than live confirmation. Do
not directly edit team metadata or infer liveness from process-name searches.
If no panel, doctor result, or explicit worker response can confirm a live
owner, do not dispatch; use the leader fallback below or report the blocker.

## Dispatch and confirmation

1. Assign with `/team task assign <id> <agent>` or the equivalent `task_assign`
   action.
2. Treat assignment, a queued DM, a successful `message_steer` call, and
   `member_spawn`'s text response as **dispatch attempts**, not evidence that
   work started. Confirm the worker's task changed to `in_progress`, or obtain
   an explicit response from the worker. If the panel and tool disagree, stop
   dispatching and reconcile the live task/member state first.
3. Do not report work as underway until that confirmation. Do not mark a task
   complete based on an agent summary alone; inspect the specified artifact
   and distinguish source review from kernel/build verification.

## Stale, stopped, and shutdown workers

- If a worker is stopped or stale, unassign its pending task with
  `/team task unassign <id>` (or `task_unassign`) and leave the task pending
  until a live owner is confirmed. A stale heartbeat is not an invitation to
  retry RPC indefinitely.
- `/team prune` is for stale manual workers; it is not a general RPC restart
  mechanism. Use `--all` only when intentionally hiding every eligible stale
  manual worker.
- Prefer a targeted graceful shutdown after the worker is done. Do not issue a
  team-wide shutdown while any worker is needed for an assigned task. Use
  `/team kill <name>` only when intentionally force-stopping that specific RPC
  worker, after checking it has no useful active work; it may unassign tasks.
- Do not respawn a name merely because the tool says “already running” or a
  stale panel label persists. Consult `/team doctor` and the task/member views;
  do not send new work to a stopped process. A pending shutdown request can
  make an apparent restart exit again. If the state cannot be reconciled, stop
  and ask before creating another worktree/branch.
- Reusing a worker name is not, by itself, proof that its old worktree or
  shutdown state is safe. If a restart is approved, verify the resulting
  worktree/branch with `git worktree list` before claiming no new branch was
  created.

## Leader fallback and verification

If no worker is confirmed live, the leader either performs the bounded work
itself or reports the blocker; it does not leave work attached to a dead
worker. Preserve task IDs and completed reports, and do not delete task or
mailbox state as a cleanup shortcut. For Lean tasks, builds remain serial and
must use the repository's shared build lock. Agent reports are navigation or
review evidence, never Lean kernel/build evidence.
