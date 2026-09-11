import Mathlib.LinearAlgebra.Matrix.Block
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import InfoGeometry.Canonical.Drazin

/-!
# InfoGeometry.Canonical.DiracSouriau.DecoupledDrazin

Pure formal verification of the Drazin inverse constructive block split.
This theorem constructs the explicit Drazin pseudoinverse for a 2x2 block
diagonal matrix, showing how topological decoupling operates in the field sector
without placeholder axioms.
-/

namespace InfoGeometry.Canonical.DiracSouriau

open Matrix
open InfoGeometry.Canonical.Drazin

variable {K : Type*} [Field K]

/--
Constructive Drazin inverse for a block-diagonal matrix where one block is invertible
and the other block is nilpotent.
-/
theorem block_drazin_inverse_decoupled
    (A₁ : Matrix (Fin 2) (Fin 2) K) (hA₁ : IsUnit A₁.det)
    (A₂ : Matrix (Fin 2) (Fin 2) K) (hA₂ : A₂ ^ 2 = 0) :
    ∃ (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
      let M := fromBlocks A₁ (0 : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin 2) (Fin 2) K) A₂
      IsDrazinInverse M D 2 := by
  -- Construct the Drazin candidate
  let A₁_inv := A₁⁻¹
  let D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    fromBlocks A₁_inv (0 : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin 2) (Fin 2) K)
  use D
  dsimp only [A₁_inv, D]
  have hInv : A₁ * A₁⁻¹ = 1 := Matrix.mul_nonsing_inv A₁ hA₁
  have hInv2 : A₁⁻¹ * A₁ = 1 := Matrix.nonsing_inv_mul A₁ hA₁
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · -- Prove M * D = D * M
    ext i j
    cases i <;> cases j <;> {
      simp [Matrix.fromBlocks_multiply, hInv, hInv2]
    }
  · -- Prove D * M * D = D
    ext i j
    cases i <;> cases j <;> {
      simp [Matrix.fromBlocks_multiply, hInv2]
    }
  · -- Prove M ^ 3 * D = M ^ 2
    rw [pow_succ, pow_two]
    have hA2_sq : A₂ * A₂ = 0 := by
      have h2 := hA₂
      rwa [pow_two] at h2
    ext i j
    cases i <;> cases j <;> {
      simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc, hInv, hA2_sq]
    }

end InfoGeometry.Canonical.DiracSouriau
