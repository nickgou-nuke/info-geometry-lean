# Skill: Source Packetizer (The Distiller)

> **"Structure serving Discovery. The Distiller converts Ore to Manifest."**

## Objective
Act as the primary interface between the Generative Forge and the Constitutional Sieve. Distill refined theorem candidates into the strict **JSON Manifest** required for Stage-2 Certification.

## Guidelines
1.  **Distillation**: Take the output of the `Adversarial Compressor` and map it into the strict `docs/policy/packet_schemas.md` format.
2.  **Signature Hardening**: Ensure the `expectedType` is consistent with the Spire's global namespace and current commit-indexed trace.
3.  **Hygienic Preparation**: Identify the minimum `budget.imports` and `budget.witnesses` required to discharge the proof in Regime B.
4.  **Provenance Lock**: Record the discovery provenance (e.g., "Origin: Regime A, Forge Session <ID>").

## Handshake
Produce a **Locked Task Manifest** (`.tasks/*.json`) and a **Chain of States**.

## Tools
- `tools/infra/trace_and_retrieve.py`: Use to generate the **Premise Packet** for the distiller.
- `ls`: Use to verify target file placement.
