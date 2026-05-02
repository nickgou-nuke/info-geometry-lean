# Prima Materia Generation Chain (ArXiv -> Socratic -> Hive Packets)

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Status: active implementation note
Scope: restore and operationalize the long generative lane before formalization.

## Intent

This repo must not wait only for "ready" ideas. It should actively generate novel theorem-candidate material from:
- ArXiv corpus (prima materia)
- Black Book motifs
- Socratic/daydream multi-stream LLM generation

Formalization remains downstream. Generation is first-class.

## Canonical chain

1) ArXiv/BlackBook ingestion (raw symbolic pressure)
2) Multi-stream generation bursts (Gemini sidecar + local lanes)
3) Socratic stabilization rounds (contradiction + repair)
4) Invariant extraction (objects/morphisms/symmetries/conserved readouts)
5) Hive packetization into theorem-candidate queue
6) Only then: Lean corridor routing and proof attempts

## Packet doctrine (generation-first)

The generative lane emits packetized artifacts with explicit epistemic status:
- `hive.packet.prima_materia.v1`
- `hive.packet.socratic_stabilization.v1`
- `hive.packet.invariant_candidate.v1`

Required status values:
- `speculative`
- `stabilizing`
- `corridor_ready`

No packet from this lane may claim theorem closure.

## Guarded Gemini use

Gemini is allowed only through repo guard wrapper:

```bash
tools/infra/run_gemini_guarded.sh --reason "prima materia generative burst" -- gemini <args>
```

No direct `gemini` calls.

## Operational command

Use the chain driver script:

```bash
tools/infra/prima_materia_chain.sh \
  --source-arxiv handover/injections/digests/EXT-20260418-052939.md \
  --black-book docs/black_books/188_jung_alchemy_and_the_hive_of_transmutation.md \
  --topic "operatorial KMS / Souriau / triality transport" \
  --rounds 3
```

Outputs are written under:
- `artifacts/prima_materia/<timestamp>/`

and include JSON packet stubs ready for queue import.

## Acceptance criteria

A generation run is successful when:
- at least one `prima_materia` packet is emitted,
- at least one `socratic_stabilization` packet is emitted,
- at least one `invariant_candidate` packet is emitted,
- each packet includes explicit `epistemic_status`, `falsifier`, and `anchor_candidates`.

## Non-goals in this stage

- no clustering/aggregation,
- no promotion to canonical theorem surfaces,
- no theorem-closure claims without Lean proof.
