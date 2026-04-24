# Vacuity Index

Generated: `2026-04-25 01:28:17`

This report tracks alias-driven and identity-transport surfaces, prioritized by whether they are actually graph-active in the exported declaration graph.

## Status
- vacuity gate: **PASS**
- interpretation: `FAIL` means at least one alias/identity-transport surface is active in the graph-backed theory path

## Counts
- total tracked findings: **0**
- high-priority active alias/identity findings: **0**
- medium-priority inactive or documentary findings: **0**
- low-priority findings: **0**

## Aggressive Replacement Queue
- none

## Policy
- alias/identity surfaces matter most when they are graph-active
- inactive alias surfaces remain documentary debt, but do not outrank active graph-facing debt
- truth still lives in Lean; this report only prioritizes replacement pressure
