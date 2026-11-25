# Independent review of CI-driven Lean repairs

Date: 2026-11-24
Reviewer: `/root/incidence_grassmann_audit`
Base reviewed: working-tree diff against `819b6fe68b4522cf7a903fbcd361bd250d5f3253`
Context supplied by root: draft PR 440, CI run 45359832998; three new owners compiled and the transport owner reported five elaboration failures. This reviewer did not rerun CI or Lean.

## Assessment

The diff contains exactly the stated elaboration/lint repairs. No operator definition, mathematical equation, sign, factor order, declaration name, or proof obligation was replaced. Two unused section assumptions are safely removed from individual theorems. The changes are suitable for publication and a fresh CI run from the standpoint of this independent source review.

No owner files were edited and no builds/tests were executed by this reviewer. This review does not assert that the repaired transport owner has passed its next kernel run.

## Exact repairs

| Location | Change | Review conclusion |
| --- | --- | --- |
| `FenchelContactTransport.contactSuperDerivation`, `map_smul'` | Add `RingHom.id_apply` to `simp only` | Correctly reduces the identity scalar homomorphism appearing in the native linear-map field. It does not alter real scalar multiplication, parity conjugation, or the order of either operator product. |
| `homogeneousFrame_coordinate` | Replace `ext z` with `apply LinearMap.ext; intro z` | Selects pointwise equality of the two covectors while preserving the full homogeneous product argument. The subsequent `rfl` uses exactly that argument. |
| `contactPair_frameAction` | Same explicit linear-map extensionality in the covector branch | The already-separated primal branch is unchanged. The new `z` retains its `F × (ℝ × ℝ)` type, so the inverse-frame expression and its height/intercept coordinates remain exactly the intended ones. |
| `contactChartShear_coordinate` | Same explicit linear-map extensionality | Preserves the homogeneous input needed by `z.2.2`; the inverse shear and final-coordinate normalization are unchanged. |
| `contactPair_shear_of_equality` | Same explicit linear-map extensionality in the covector branch | Preserves the whole product input for inverse pullback. The contact-derived intercept `fStar p = p x - f x`, its sign, and the shear direction are unchanged. |
| `FenchelContactIncidence.homogeneousPoint_ne_zero` | `omit [NormedSpace ℝ E] in` | Safe generalization. The point `(x,f x,1)` and the proof by final coordinate `1 ≠ 0` do not use scalar multiplication on `E`. The ambient additive/normed-group structure still supplies the zero appearing in the proposition. |
| `LegendreGraphGeometry.graph_finrank` | `omit [FiniteDimensional ℝ V] in` | Safe generalization. Existing `graphSourceEquiv H` is available for arbitrary modules; native `LinearEquiv.finrank_eq` derives equality of `Cardinal.toNat` ranks without a finite-dimensionality premise. The separate half-dimension and Grassmannian constructions retain their finite-dimensionality assumption. |
| `CotangentOperators.hamiltonian_add_smul` | Remove the unused `add_mul` simp entry | Only the redundant simplifier list entry is removed. The exact quadratic expansion and final `ac_rfl` proof remain unchanged. |

The choice of explicit `LinearMap.ext` is appropriate at all four sites: the desired operation is to introduce one point of a product domain, not recursively apply product-domain extensionality and change the variables expected by the following `change` statements.

The generalized rank theorem does not assert that an infinite-dimensional space has a finite basis; Mathlib's `finrank` is a natural-valued dimension invariant defined from the cardinal rank. Only equality under an already constructed linear equivalence is used here.

## Inventory

The explicit public inventory remains 113 declarations:

- `FenchelContactIncidence`: 21.
- `LegendreGraphGeometry`: 24.
- `CotangentOperators`: 27.
- `FenchelContactTransport`: 41.

A read-only textual comparison of the current namespace-qualified declaration sequence against the generated audit commands produced no differences. The two `omit` directives do not change names or omit declarations from the audit.

## Reviewed current source hashes

| Owner | SHA-256 |
| --- | --- |
| `lean/InfoGeometry/Twistor/FenchelContactIncidence.lean` | `8b7c721eeef4d6ca50af5238cebc153aeaf9e7b6f63e4bf8c6baeceb02d2e33c` |
| `lean/InfoGeometry/Twistor/FenchelContactTransport.lean` | `3e254cb1bd5565de1624d64e5be98ca765ed9b8928ea2c6ab86c51eee63ceb34` |
| `lean/InfoGeometry/Geometry/LegendreGraphGeometry.lean` | `60b4f7b03a799a8e6161df17ca26dc17b1c812a81bc550d3c653591ab370f2f1` |
| `lean/InfoGeometry/Geometry/CotangentOperators.lean` | `43da1128f8ca13cf6ec9284dab04a1538ac92c1f6145b7ae9cd5486c0589c44c` |

Native API support for the assumption generalization was checked in the existing `GradedGraphChart.graphSourceEquiv` owner and pinned Mathlib `LinearAlgebra/Dimension/Finrank.lean`, where `LinearEquiv.finrank_eq` requires no finite-dimensionality instance. Final compiler acceptance remains the next CI result.
