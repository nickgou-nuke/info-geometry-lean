---
name: topological-repair
description: Policy for purifying the repository's DAG by restoring continuous Mathlib dependency chains from L0 upward.
---

# Topological Repair & Mathlib Conductivity

This skill defines the overarching policy and methodology for purifying the repository's Directed Acyclic Graph (DAG) of dependencies. It is the core theoretical framework for transforming schematic code into verified, theorem-honest Lean mathematics.

## 1. Mathlib Conductivity
Every theorem node must maintain "Mathlib conductivity." This means there must exist a strict, unbroken Lean dependency path descending directly into Mathlib roots.
- **Do not** route sideways into opaque abstraction packets.
- **Do not** use bridge surfaces or externalized claims as substitutes for native definitions.
- **Do not** hide infinite/analytic claims behind finite `Prop` fields or uninstantiated witnesses unless explicitly labeled as an analytic boundary.

## 2. Bottom-Up Purification (L0/L1 First)
Always start from the deepest layer in the chain of derivation (`L0`).
- Identify modules whose imports bottom out purely in Mathlib.
- Clean and restore those root modules first.
- **Never start from the last leaves.** Do not attempt to repair `L5` capstone theorems if their `L1`/`L2` foundations are unrooted.
- Once a root module compiles with zero errors and zero warnings, freeze it and move upward to its immediate dependents.

## 3. Root Restoration
The repository must be physically re-rooted.
- Example: If a bounded operator module depends on an abstract vector space, but the physics requires the real doubled Hestenes/Krein carrier (`DoubledSpace E`), you must rewrite the operator module to import and act on `DoubledSpace E` directly.
- All hanging propositions must be rooted one by one.

## 4. Certification Rule for Conducting Edges
A Lean module may become a conducting edge in the superconducting graph of proofs when:

1. **It is purified**:
   - No external authority.
   - No prose/packet/bridge premise acting as proof authority.
   - No unsupported surrogate theorem.
   - No hidden root through deleted/stale configs.

2. **It is rooted in Lean/Mathlib**:
   - Imports are exclusively `Mathlib` or already-certified local Lean modules.
   - Claims reduce through theorem chains, constructors, projections, or readback lemmas.
   - `lake env lean <file>` and targeted `lake build <Module>` pass.

3. **It has explicit readback/certification lemmas**:
   - Theorem projections for structure fields.
   - Witness extraction for subtypes/existentials.
   - `@[simp]` readbacks where downstream modules need transport.
   - No opaque “package says so” authority.

4. **Once certified, it is usable as a conducting edge**:
   - Downstream modules may safely import it.
   - Graph traversal may use it as an upward ladder edge.
   - Arango/DAG can mark it as conductive navigation evidence, but Lean/build remains the ultimate authority.

## 5. Operational Checklist for Agents
When asked to formalize or repair a module:
1. **Identify the Roots**: What `L0` carriers (e.g., `DoubledSpace`, `Cl11Matrix`) does this physical concept depend on?
2. **Trace the Mathlib Path**: What native Mathlib constructs (e.g., `ContinuousLinearMap`, `InnerProductSpace`) implement this logic without intermediate aliases?
3. **Write Natively**: Project the Mathlib functions directly onto the `L0` roots.
4. **Verify Conductivity**: Ensure the module compiles cleanly with `lake env lean` with no broken links.
5. **Certify as Conducting Edge**: Verify all 4 conditions above are met before moving upward to its dependents.
