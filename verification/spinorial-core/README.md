# Corrected spinorial mathematical core

Entry point: `InfoGeometry.Canonical.SpinorialCore.All`.

This package implements the corrected mathematical core of the Spinorial Prima Materia program. It uses native mathlib carriers and genuine proof terms: `CliffordAlgebra`, `Matrix`, algebraic tensor products, linear maps, quotient modules, `ZMod`, continuous linear equivalences, and derivatives. It does not encode the disputed physical identifications as axioms or as conclusion-shaped structure fields.

## Reproducible isolated build

Lean is pinned to `leanprover/lean4:v4.28.1`. Mathlib is pinned to `1f9fffd5ff0b854b8a1f1f69adc11c61f05f2515`, matching the parent repository's inspected manifest.

From the repository or extracted bundle root:

```sh
cd verification/spinorial-core
lake update
lake exe cache get
lake build InfoGeometry.Canonical.SpinorialCore.All
lake env lean ../../lean/InfoGeometry/Canonical/SpinorialCore/AxiomAudit.lean
```

`lake update` here initializes this separate package from its immutable mathlib revision. It is not an instruction to update the parent repository's dependencies. The parent `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, and existing source owners are unchanged.

## Declaration owners

All paths below are relative to `lean/InfoGeometry/Canonical/SpinorialCore/`. All declarations are under `InfoGeometry.Canonical.SpinorialCore`, with the additional `G2` or `RealAtom` namespace where shown.

| Owner | Principal declarations | Exact scope |
| --- | --- | --- |
| `Algebra.lean` | `mixed_bivector_square`, `cutGrading_square`, `innerDiff_is_odd`, `innerDiff_square_is_even` | Mixed-sign Clifford product and idempotent inner-differential identities in any associative ring. |
| `NativeClifford.lean` | `clifford_mixed_bivector_square`, `RealAtom.product_is_grading`, `RealAtom.mixed_car` | Native Clifford theorem and concrete real 2-by-2 witnesses. |
| `Bipartite.lean` | `order_one_factorization`, `order_one_even`, `polynomialTrace_conjugation` | Exact tensor commutator factorization, explicitly restricted even-observable theorem, finite polynomial trace invariance. |
| `FiniteIndex.lean` | `finiteIndex_eq_dimension_difference`, `trivalent_helicity_defect`, `network_index_eq_trace` | Actual kernel/cokernel index of a finite linear map, integer graph-counting defect, and grading trace. |
| `FiniteSupertrace.lean` | `partner_positive_power_trace`, `polynomial_supertrace`, `normalized_network_supertrace` | Trace cancellation of nonconstant powers of rectangular partner operators; normalized finite polynomial supertrace equals the dimension defect. |
| `DualFlow.lean` | `dual_coordinate_linearization`, `dual_solution_eq_exponential`, `dual_flow_closed_form` | The genuine chain rule and global exponential solution, with differentiability and invertibility explicit. |
| `BoundaryCurrent.lean` | `phase_conjugate_current`, `equal_intensity_does_not_determine_current` | Derivative-dependent current reversal and an explicit counterexample to inferring current from intensity. |
| `G2Certificate.lean` | `G2.adjacency_eq_blocks`, `G2.smith_certificate`, four integral inverse identities | The specified twelve-vertex matrix is integrally equivalent to diagonal entries 1,1,1,1,1,1,1,1,1,2,2,364. Finite certificates are checked by Lean's `decide`. |
| `G2Cokernel.lean` | `G2.graphResidue_exact`, `G2.cokernelEquiv`, `G2.relation_kernel_zero`, `G2.primaryDecomposition`, `G2.no_surjection_to_zmod16` | Explicit native quotient equivalence to ZMod 2 x ZMod 2 x ZMod 364; zero integer kernel; CRT decomposition and the obstruction to a cyclic order-16 quotient of the two-primary factor. |

`All.lean` imports the nine mathematical owners. `AxiomAudit.lean` prints the axiom dependencies of fourteen central constructions and theorems. The source bundle has 64 theorem declarations and 35 definitions/abbreviations. Standard logical axioms used by mathlib must be distinguished from newly postulated mathematical or physical assumptions; the audit exposes the dependencies rather than calling the entire development axiom-free.

## Deliberately separate realization problems

The integer quotient is not labelled a proved Cuntz-Krieger K-theory classification. The code does not supply a Pin bordism classification, identify split sl(3,R) with compact su(3), derive a generation count, reconstruct a spacetime horizon, or prove a soliton's charge, form factor, or gravitational stability. Those are separate construction theorems and are not consequences silently attached to the finite algebraic results.

The independent validation target checks only this mathlib-only source closure. A passing target is not a claim that the entire parent repository has been rebuilt.
