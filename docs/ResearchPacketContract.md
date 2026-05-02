# Research Packet Contract

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This document defines the repo-native handoff contract from quarantined Hermes
discovery into Prompt A / Prompt B.

## Purpose

`deep research` is an intake subphase, not an authority surface.

It must emit a typed packet that separates:

1. facts
2. interpretations
3. metaphors
4. formalization candidates

Only Lean closure can admit Lane C results.

## Paths

- schema: `tools/schema/research_packet.json`
- default packet lane: `quarantine/hermes_memory/research_packets/`
- builder/validator: `tools/infra/research_packet.py`
- ClawCode gate: `tools/infra/check_research_handoff_gate.py`

## Build

```bash
python3 tools/infra/research_packet.py build \
  --state reports/research/deep-research-state-<timestamp>-<goal>.json \
  --out quarantine/hermes_memory/research_packets/<packet>.json
```

## Validate

```bash
python3 tools/infra/research_packet.py validate \
  --packet quarantine/hermes_memory/research_packets/<packet>.json
```

## Prompt A requirement

Prompt A must consume one packet and emit:

- `research_packet_path`
- packet id
- unresolved assumptions
- NemoClaw note path with research provenance split

## Prompt B requirement

Prompt B must block admission unless:

1. packet validates
2. NemoClaw note contains research provenance markers
3. standard build + DAG + doctor gates pass
