# The Kasparov-Krein DIII Synthesis

**Status:** finite algebraic corridor verified; analytic/geometric closure debt remains
**Date:** 2026-06-18
**Canonical Module:** `lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`

## 1. Introduction: The 10-Fold Way

This document records the theorem-checked finite algebraic corridor behind the
Layer 3 DIII/Krein/Klein-bottle synthesis.  The Lean module does not prove a
physical black-hole information theorem or a full analytic KK/KO classification
statement.  It proves the algebraic sign/readback facts that make that synthesis
precise enough to become a future theorem target.

## 2. Algebraic Signatures

In the Bogoliubov-de Gennes (BdG) formalism, Class DIII is characterized by:
*   **Time-Reversal Symmetry (TRS):** $T^2 = -1$ (Fermionic/Kramers degeneracy)
*   **Particle-Hole Symmetry (PHS):** $C^2 = +1$ (Superconducting Andreev pairing)

**Compiled finite readout:**
*   the finite Andreev rotation used in the horizon witness satisfies $A^2=-I$,
    $A^4=I$, is orthogonal, and has trace zero;
*   the ordinary Andreev electron/hole channel flip satisfies $C^2=I$;
*   the canonical doubled real BdG proxy exposes the DIII sign pattern
    $T^2=-I$, $C^2=I$, and chiral product readbacks.

The physical interpretation is that this is the algebraic shape expected of a
DIII boundary model.  The repository does not currently prove that a geometric
event horizon is literally such a topological superconductor.

## 3. The Doubled Krein Space and Kasparov's KK-Theory

Because the macroscopic Minkowski metric ($-+++$) has an indefinite signature, the underlying state space is formalized as a **Doubled Krein Space**.

The Lean bridge contains readback theorems for existing split-Krein KKT
decomposition witnesses and an explicit interface for a supplied Kasparov
product datum.  This is intentionally not a construction of the interior tensor
product or a proof that cooperadic gluing realizes the analytic Kasparov
intersection product.

## 4. The Klein Bottle Anomaly Absorption

The finite topology interface uses the existing matrix-level Klein-bottle trace
transport lemma.  Under explicit premises

```text
P^T P = I
trace(M) = 0
```

it proves

```text
trace(P M P^T) = 0.
```

This is the kernel-checked trace-absorption corridor.  A full KO-theoretic
anomaly theorem for a constructed Klein-bottle quotient remains open closure
debt.

## 5. Verified Surface and Evidence Manifests

The checked surface currently consists of:

Projective bridge theorems:
* `InfoGeometry.Projective.KasparovKreinDIIIBridge.finite_andreev_diii_signature_packet`
* `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_sign_readback`
* `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_root_readback`
* `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_grade_split_from_witness`
* `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_mixed_commutator_gZero`
* `InfoGeometry.Projective.KasparovKreinDIIIBridge.kasparov_product_cycle_readback`
* `InfoGeometry.Projective.KasparovKreinDIIIBridge.klein_bottle_trace_absorption`
* `InfoGeometry.Projective.KasparovKreinDIIIBridge.concreteTopologicalSocket2_packet`

Operator-algebraic bridge theorem:
* `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.concrete_diii_andreev_bridge_packet`
* `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_left_kasparov_defect_zero`
* `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_right_kasparov_defect_zero`

Andreev horizon readout connection:
* `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_sq`
* `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_normSq`
* `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_fourth`
* `InfoGeometry.Projective.AndreevHorizonUnitarity.concreteAndreevHorizon_information_preservation`

The companion finite SymPy witness script verifies the same 2×2 sign packet:

```text
T^2 = -I
C^2 = I
T^2 C^2 = -I
```

A JSON witness payload can be produced with:

```bash
python3 formalizations/andreev_diii_kasparov_witness.py --json
```

Use `docs/KASPAROV_KREIN_DIII_RUNBOOK.md` for the full verification and status workflow.


## 6. Open Closure Debt

The following are not yet proved by the repository:

* construction of a genuine doubled Krein Kasparov product for the causal-cone
  model;
* a geometric proof identifying a physical event horizon with an Andreev
  boundary;
* a full KO-theoretic Klein-bottle anomaly theorem;
* a certified de Rham computation proving that any rank-32 Betti model counts
  protected Majorana boundary modes.

## 7. Conclusion

The capstone result is a verified finite DIII/Krein/Klein trace-readout layer:
the algebraic signs, finite Andreev involutions, split-Krein readbacks, and
Klein trace transport compile.  The larger physical synthesis is now a sharply
specified theorem roadmap rather than an implicit claim.
