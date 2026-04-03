# Release Notes and Current Status

This repository is maintained as a rolling `main` branch, not as a polished public release train.

## Current status

The important current milestones are structural rather than marketing-oriented:
- the graph pipeline is centralized under `tools/infra/` and `artifacts/dag/`;
- the repo now tracks semantic quotient and projection coloring as maintained reports;
- several overloaded canonical files have been split by ownership;
- repo-local skills now encode both repo workflow and canonicalization policy.

## What belongs in release notes

Use this file to record:
- durable changes to the public Lean surface;
- durable changes to maintained tooling entrypoints;
- changes to repository policy or workflow;
- documentation resets and structural reorganizations.

Do not use this file for:
- transient hotspot numbers;
- generated report snapshots;
- speculative theory prose;
- TODO lists that belong in issues or targeted plans.

## Current release posture

There is no separate public alpha packaging workflow documented here at the moment.
Until one exists, the authoritative state of the project is:
- the current `main` branch;
- the current `lakefile.lean` and `lean-toolchain` pins;
- the current maintained docs listed in [README.md](README.md).
