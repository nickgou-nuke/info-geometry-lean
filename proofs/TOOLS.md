# TOOLS.md - Local Notes

Skills define _how_ tools work. This file is for _your_ specifics — the stuff that's unique to your setup.

## What Goes Here

Things like:

- Camera names and locations
- SSH hosts and aliases
- Preferred voices for TTS
- Speaker/room names
- Device nicknames
- Anything environment-specific

## Examples

```markdown
### Cameras

- living-room → Main area, 180° wide angle
- front-door → Entrance, motion-triggered

### SSH

- home-server → 192.168.1.100, user: admin

### TTS

- Preferred voice: "Nova" (warm, slightly British)
- Default speaker: Kitchen HomePod
```

## Why Separate?

Skills are shared. Your setup is yours. Keeping them apart means you can update skills without losing your notes, and share skills without leaking your infrastructure.

---

Add whatever helps you do your job. This is your cheat sheet.

## Related

- [Agent workspace](/concepts/agent-workspace)

## Local ArangoDB Brains

There are two distinct ArangoDB-backed graphs in this workspace. Do not mix
them.

### Agent / Conversation Brain

- Endpoint: `http://localhost:8531`
- Database: `agent_brain`
- Purpose: agent conversation history, planning traces, subagent steps, prior
  reasoning artifacts.
- Known collections: `steps`, `next_step`, `spawns`.
- Use when past agent work, orchestration history, or subagent traces matter.

### Codebase / Lean Theorem Graph

- Endpoint: `http://127.0.0.1:8529`
- Database: `info_geometry`
- Purpose: compiled Lean declarations, syntax/AST graph, module imports,
  theorem connectivity.
- Known collections include: `lean_decls`, `syntax_nodes`, `lean_modules`,
  `references`, `ast_child`, `has_syntax`, `decl_root`, `lean_imports`.
- Use for theorem/codebase queries and proof dependency work.
- If local scripts default to `ARANGO_DATABASE=agent_brain` on port `8529`,
  override explicitly:

```bash
ARANGO_URL=http://127.0.0.1:8529
ARANGO_DATABASE=info_geometry
```

## Browser Harness Setup & Usage

**What is Browser Harness?**
[Browser Harness](https://browser-harness.com/) is a powerful tool that allows an AI agent to connect directly to the real Chrome browser using the Chrome DevTools Protocol (CDP).

**Installation**
```bash
uv tool install --python 3.12 --force browser-harness
```

**Registering the Skill**
```bash
browser-harness skill
```

**Connecting to the Browser**
When the agent runs a `browser-harness` command, Chrome will automatically open the `chrome://inspect/#remote-debugging` page. The user needs to manually tick the **"Allow remote debugging for this browser instance"** checkbox and click **Allow** on the popup.

**Usage Example**
```bash
browser-harness <<'PY'
new_tab("https://chatgpt.com")
print(page_info())
PY
```
