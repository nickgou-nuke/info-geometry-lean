# PR #77: Arnold–Kohno tensor curvature review

The original PR adds a tensor-valued three-channel curvature calculation. The active owner previously only proved vanishing for pairwise commuting coefficients. That is not the same theorem, so filename presence did not justify duplicate closure.

## Mathematical reconstruction

Residues live in a native Mathlib `LieAlgebra R L`; forms live in `ExteriorAlgebra R M`; their weighted channels live in `L ⊗[R] ExteriorAlgebra R M`. Two infinitesimal braid relations imply equality of the three cyclic residue brackets. Tensor bilinearity factors the quadratic curvature through the three-term Arnold expression, which then vanishes when the Arnold relation holds.

The rewrite extends the existing owner and preserves its public interface. It uses Mathlib's bracket and tensor operations directly, without duplicating them as `comm`, `weightedForm`, or carrier aliases. The original `LogarithmicArnoldTriangle.closed12/23/31 : Prop` fields did not express differential closure and are not promoted. Their intended mathematical obligation is closure under an actual differential; the proved result is explicitly quadratic curvature cancellation. No theorem of full differential flatness is asserted. The original disjoint-channel cancellation follows directly from `TensorProduct.zero_tmul` once its bracket is zero and does not require another wrapper API.

## Repository reconciliation

The complete recursive content search covered 1,042,736 files, excluding Git metadata and the protected dependency directory, with no search errors. It found the active Arnold/KZ owners and three external snapshot versions, all inspected. The external copies express either scalar-weighted cancellation or the earlier tensor proposal. The active `KZLogarithmicConnection` proves cancellation in one common coefficient algebra with equal-bracket data; the added theorem keeps the residue and exterior carriers separate and derives equal brackets from the infinitesimal braid relations. External snapshots are historical sources, not kernel evidence.

## Verification on 2026-09-09

The revised owner, its existing downstream `ArnoldKZFlatnessBridge`, and a four-theorem axiom audit compiled sequentially under the shared build lock against the pinned environment. Both compiled source files produced no warnings. New theorem dependencies are only `propext` and, for the tensor theorems, `Quot.sound`. The semantic vacuity gate passed with one pre-existing warning on the unchanged `commutatorCurvature_eq_zero_of_commuting`; it reported no new findings. These are targeted checks, not a master-build or repository-wide zero-warning claim.
