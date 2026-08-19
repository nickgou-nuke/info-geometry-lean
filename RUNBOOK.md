# Info-Geometry-Lean: Runbook and Execution Guide

This Runbook serves as the definitive execution guide for the `info-geometry-lean` repository. It outlines the current state of the pipeline, how to trigger the verification builds, and the standards for native Lean closure.

## 1. The Canonical Build Pipeline
To verify the complete mathematical unification from the bulk causal algebras to the topological superconducting horizon, run the master build command:

```bash
lake build
```
This executes the compilation of all Lean 4 modules across the repository (over 8000+ verification jobs). 

### Key Modules to Verify:
* `InfoGeometry.Projective.SplitOctonions.ZornMatrix` (Verifies the base Split Octonion algebra)
* `InfoGeometry.Projective.SplitOctonions.OctonionicProjectiveLine` (Verifies the $\mathbb{OP}^1$ associative boundary via Lemma 4.5.2)
* `InfoGeometry.Projective.KuzminCuntzPath` (Verifies the Cuntz-Toeplitz $q$-CCR algebraic path)
* `InfoGeometry.KasparovKreinDIIIBridge` (Verifies the Class DIII equivalence)

## 2. The Strict "Native Lean Closure" Policy
As defined in `GEMINI.md`:
> "Effective immediately, every mathematical claim must be discharged by a native Lean proof."

**Rules of Execution:**
1. **No Proof by Python:** External computations are not accepted as mathematical truth.
2. **Lean Kernel Authority:** Every proposition must be discharged by a native Lean 4 derivation path.
3. **Open Claims:** If a bridge lacks a native Lean proof term, it is not a theorem and must not be presented as one.

## 3. Advanced Graph Tooling
For redundancy cleanup, namespace deduplication, or legacy compatibility checks across the DAG/ArangoDB graphs, use the dedicated skill library:

```bash
tools/infra/gepa_categorical_projection.py --evolve --generations 10
```
*(See `skills/lean-dag-wire-refactor/SKILL.md` for extended DAG operation details).*
