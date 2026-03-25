# Bridge Thinness Index

This file explains the bridge-thinness audit and its purpose.

## What thinness means

A bridge is thin when its public theorem surface mostly consists of:
- definitional identities;
- one-step re-exports from lower files;
- orientation rewrites;
- packaging over already-proved lower statements.

Thin bridges are not automatically wrong, but they should not dominate the public mathematical story.

## Current tooling

Use:
- `tools/generate_bridge_thinness_index.py`
- `tools/infra/generate_theorem_surface_index.py`
- `tools/infra/generate_semantic_quotient.py`

## Policy

If a thin bridge is real lower-owner mathematics, keep it low. If it is only shell packaging, internalize it or move it behind the owner file.
