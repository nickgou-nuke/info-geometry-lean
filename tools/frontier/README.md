# Frontier Tools

This directory contains the maintained semantic-block and frontier-discovery tooling.

## Maintained entrypoints

- `semantic_block_export.py`
- `skynet_v2.py`
- `extract_module_patch.py`

## Purpose

Use this layer for:
- trusted semantic-block export of heavy Lean modules;
- frontier exploration around a chosen seed theorem or module;
- extraction of prompt-ready local context for focused agent work.

## Current rule

For heavy files, prefer the external semantic export path instead of trying to infer structure from the raw declaration graph alone.

Outputs from this lane usually land under `reports/dag/`, but individual
entrypoints may also write to explicit caller-supplied paths.
