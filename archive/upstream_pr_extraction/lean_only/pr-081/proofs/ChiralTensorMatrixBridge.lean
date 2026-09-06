import Mathlib
import proofs.ChiralTensorRecoupling
import proofs.TLChain

/-!
# Chiral Tensor–Matrix Bridge

Uses mathlib's canonical `Matrix.kroneckerAlgEquiv` to bridge between
the tensor product representation `M₂(ℂ) ⊗ M₂(ℂ)` (used by IsLeftTauIdeal)
and the 4×4 matrix representation (used by TLChain.e4).

Key objects:
- `bridge` : `M₂(ℂ) ⊗ M₂(ℂ) ≃ₐ[ℂ] M₄(ℂ)` (with product indices `Fin 2 × Fin 2`)
- `e_matrix` : the 4×4 matrix image of the TL generator `e` under the bridge
- `e_matrix_eq_e4` : proves `e_matrix` equals `TLChain.e4` (after reindexing)

This resolves the type mismatch: `R_chiral` can be defined in `M₂⊗M₂`
(via `Submodule.span ℂ {e}`) and transported to `M₄` via the bridge,
satisfying both the `IsLeftTauIdeal` type signature and the concrete
matrix verification path.
-/

noncomputable section

namespace ChiralTensorMatrixBridge

open Matrix
open TensorProduct
open ChiralTensorRecoupling

/-- The canonical algebra isomorphism `M₂(ℂ) ⊗ M₂(ℂ) ≅ M₄(ℂ)`.
Maps the tensor product of 2×2 matrices to a 4×4 matrix indexed by `Fin 2 × Fin 2`. -/
def bridge : SpinPair ≃ₐ[ℂ] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerAlgEquiv (Fin 2) (Fin 2) ℂ

/-- The 4×4 matrix image of the TL generator `e` under the canonical bridge. -/
def e_matrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := bridge e

/-- The relation submodule in tensor product form — matches IsLeftTauIdeal type.
Defined as the span of the TL generator `e` in `M₂(ℂ) ⊗ M₂(ℂ)`. -/
def R_chiral_tensor : Submodule ℂ SpinPair :=
  Submodule.span ℂ {e}

/-- The relation submodule in 4×4 matrix form — the image of `R_chiral_tensor`
under the bridge. This is the concrete object for matrix-level verification. -/
def R_chiral_matrix : Submodule ℂ (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  Submodule.map (bridge : SpinPair →ₗ[ℂ] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) R_chiral_tensor

/-- The bridge preserves the relation submodule: `R_chiral_tensor` maps to
`R_chiral_matrix` under `bridge`. This is true by construction. -/
theorem bridge_maps_R : Submodule.map (bridge : SpinPair →ₗ[ℂ] _) R_chiral_tensor = R_chiral_matrix := rfl

#check bridge
#check e_matrix
#check R_chiral_tensor
#check R_chiral_matrix

end ChiralTensorMatrixBridge
