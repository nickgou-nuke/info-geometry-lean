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

## 2. Running Symbolic Witnesses
For specific algebraic computations that bridge into physical observables (like Yang-Baxter phase checks or large matrix reductions), we use SymPy scripts as external witnesses. 

To run the Fibonacci MZM and Kuzmin path witness:
```bash
uv run python3 octonionic_cuntz_scrambling.py
```
*Note: Ensure `uv` is installed, or run `python3 -m pip install sympy` locally.*

## 3. The Strict "Native Lean Closure" Policy
As defined in `GEMINI.md`:
> "Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate."

**Rules of Execution:**
1. **No Proof by Python:** SymPy scripts, Mathematica outputs, and AI-generated certificates are **scaffolding only**. They are not accepted as mathematical truth.
2. **Lean Kernel Authority:** Every proposition must be discharged by a native Lean 4 derivation path.
3. **Open Debt:** If a bridge is structurally formulated but lacks a native Lean proof term, it must be marked with `sorry` and clearly labeled as open closure debt. Do not remove debt labels until the Lean kernel accepts the proof without warnings.

## 4. Advanced Graph Tooling
For redundancy cleanup, namespace deduplication, or legacy compatibility checks across the DAG/ArangoDB graphs, use the dedicated skill library:

```bash
tools/infra/gepa_categorical_projection.py --evolve --generations 10
```
*(See `skills/lean-dag-wire-refactor/SKILL.md` for extended DAG operation details).*
