# Docs Tools

This directory contains the maintained documentation refresh helpers.

## Maintained entrypoints

- `generate_auto_docs.py`
- `update_repo_docs.py`

## Purpose

Use this layer for:
- regenerating [docs/auto/index.md](../../docs/auto/index.md);
- rebuilding selected derived documentation surfaces from refreshed graph/frontier data;
- keeping generated doc outputs separate from hand-maintained operational docs.

## Rule

Do not edit generated docs by hand if a script in this directory owns them.

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../../docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md) for the current build/audit state.

