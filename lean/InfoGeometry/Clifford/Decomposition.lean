import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Clifford.TowerMatrix
import Mathlib.Tactic

/-!
# InfoGeometry.Clifford.Decomposition

Cartan-style decomposition primitives induced by the `θ` involution built from
the tower matrix `J`.
-/

open scoped Matrix
open scoped Kronecker

namespace Decomposition

open Matrix InfoGeometry.Clifford.TowerMatrix

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ) (hJ1_sq : J1 * J1 = 1)
abbrev Matn : Type := Mat n
noncomputable def J : Matn (n := n) := Jn J1 n

noncomputable def θ (X : Matn (n := n)) : Matn (n := n) :=
  -(J (J1 := J1) (n := n) * Xᵀ * J (J1 := J1) (n := n))

noncomputable def θₗ : Matn (n := n) →ₗ[ℝ] Matn (n := n) :=
  { toFun := θ (J1 := J1) (n := n)
    map_add' := by
      intro X Y
      dsimp [θ]
      simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
    map_smul' := by
      intro r X
      dsimp [θ]
      simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg] }

noncomputable def kSub : Submodule ℝ (Matn (n := n)) :=
  LinearMap.ker (θₗ (J1 := J1) (n := n) - LinearMap.id)
noncomputable def pSub : Submodule ℝ (Matn (n := n)) :=
  LinearMap.ker (θₗ (J1 := J1) (n := n) + LinearMap.id)

lemma mem_k_iff (X : Matn (n := n)) :
    X ∈ kSub (J1 := J1) (n := n) ↔ θ (J1 := J1) (n := n) X = X := by
  simp [kSub, θₗ, sub_eq_zero, LinearMap.sub_apply]
lemma mem_p_iff (X : Matn (n := n)) :
    X ∈ pSub (J1 := J1) (n := n) ↔ θ (J1 := J1) (n := n) X = -X := by
  simp [pSub, θₗ, add_eq_zero_iff_eq_neg, LinearMap.add_apply]

/-- φ(X) = J Xᵀ J (The pure metric anti-automorphism engine). -/
noncomputable def φ (X : Matn (n := n)) : Matn (n := n) :=
  J (J1 := J1) (n := n) * Xᵀ * J (J1 := J1) (n := n)

lemma θ_eq_neg_φ (X : Matn (n := n)) :
    θ (J1 := J1) (n := n) X = - φ (J1 := J1) (n := n) X := by
  rfl

/-- φ strictly reverses multiplication: φ(XY) = φ(Y)φ(X). -/
lemma φ_mul_rev (hJ1_sq : J1 * J1 = 1) (X Y : Matn (n := n)) :
    φ (J1 := J1) (n := n) (X * Y) =
      φ (J1 := J1) (n := n) Y * φ (J1 := J1) (n := n) X := by
  have hJJ : J (J1 := J1) (n := n) * J (J1 := J1) (n := n) = (1 : Matn (n := n)) := by
    simpa using TowerMatrix.Jn_sq J1 hJ1_sq n
  calc
    φ (J1 := J1) (n := n) (X * Y)
        = J (J1 := J1) (n := n) * (X * Y)ᵀ * J (J1 := J1) (n := n) := by rfl
    _ = J (J1 := J1) (n := n) * (Yᵀ * Xᵀ) * J (J1 := J1) (n := n) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = J (J1 := J1) (n := n) * Yᵀ * 1 * Xᵀ * J (J1 := J1) (n := n) := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (J (J1 := J1) (n := n) * Yᵀ * J (J1 := J1) (n := n)) *
          (J (J1 := J1) (n := n) * Xᵀ * J (J1 := J1) (n := n)) := by
          simp only [← hJJ, Matrix.mul_assoc]
    _   = φ (J1 := J1) (n := n) Y * φ (J1 := J1) (n := n) X := by rfl

/-- θ reverses multiplication up to a minus sign: θ(XY) = -θ(Y)θ(X). -/
lemma θ_mul_rev (hJ1_sq : J1 * J1 = 1) (X Y : Matn (n := n)) :
    θ (J1 := J1) (n := n) (X * Y) = - (θ (J1 := J1) (n := n) Y * θ (J1 := J1) (n := n) X) := by
  dsimp [θ]
  have h_phi := φ_mul_rev (J1 := J1) hJ1_sq X Y
  dsimp [φ] at h_phi ⊢
  rw [h_phi, neg_mul_neg]

end Decomposition
