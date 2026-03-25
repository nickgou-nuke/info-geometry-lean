# Surrogate Index

This file describes the surrogate/debt audit surface. It is no longer a frozen snapshot report.

## What this index tracks

Surrogates include:
- assumption-only interfaces pretending to be closure;
- placeholder or vacuous theorem surfaces;
- bridge scaffolds whose only content is restating a hypothesis package.

## Current checks

Use:
- `scripts/quality/audit_constructivity.py --mode stable`
- `lake script run strictCheck`
- `tools/infra/generate_theorem_surface_index.py`

## Policy

A clean audit means only that the known forbidden surrogate patterns were not found on the checked stable surface. It does not by itself prove that every public theorem is semantically well placed.
