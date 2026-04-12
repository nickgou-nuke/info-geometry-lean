# Symbol-First Protocol

Effective date: **2026-04-12**

This protocol defines the required communication contract for agentic proof exploration.

## Core Rule

Exploration is **symbol-first**.
Natural language is a coordination layer, not the primary search surface.

## Required Packet (Per Attempt)

1. `target_theorem`
   - theorem id or file-path + declaration name
2. `symbolic_state`
   - symbols (operators, projectors, generators, indices)
   - relations (equations, commutators, anticommutators, inclusions)
3. `proof_skeleton`
   - candidate lemma chain
   - tactic sketch aligned to Lean goals
4. `compile_probe`
   - command used
   - first failing goal
   - error signature
5. `delta_update`
   - minimal symbolic change proposed from compiler feedback
6. `status`
   - `open` | `narrowed` | `closed` | `quarantine`

## Prohibited

- Language-only closure claims.
- Mythic/prose inflation without symbolic map.
- Treating narrative coherence as proof evidence.

## Admission Boundary

Only compiled Lean terms are authoritative.
All non-compiled packets are exploratory artifacts.
