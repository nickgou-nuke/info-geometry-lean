import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

namespace InfoGeometry.Clifford.Decomposition

open Matrix InfoGeometry.Clifford.TowerMatrix

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ) (hJ1_sq : J1 * J1 = 1)
local notation "Matn" => InfoGeometry.Clifford.TowerMatrix.Mat n
noncomputable def J : Matn := Jn J1 n

noncomputable def θ (X : Matn) : Matn :=
  -(J J1 * Xᵀ * J J1)

noncomputable def θₗ : Matn →ₗ[ℝ] Matn :=
  { toFun := θ J1
    map_add' := by
      intro X Y
      dsimp [θ]
      simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
    map_smul' := by
      intro r X
      dsimp [θ]
      simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg] }

noncomputable def kSub : Submodule ℝ Matn :=
  LinearMap.ker (θₗ J1 - LinearMap.id)
noncomputable def pSub : Submodule ℝ Matn :=
  LinearMap.ker (θₗ J1 + LinearMap.id)

lemma mem_k_iff (X : Matn) :
    X ∈ kSub J1 ↔ θ J1 X = X := by
  simp [kSub, θₗ, sub_eq_zero, LinearMap.sub_apply]
lemma mem_p_iff (X : Matn) :
    X ∈ pSub J1 ↔ θ J1 X = -X := by
  simp [pSub, θₗ, add_eq_zero_iff_eq_neg, LinearMap.add_apply]

/-- φ(X) = J Xᵀ J (The pure metric anti-automorphism engine). -/
noncomputable def φ (X : Matn) : Matn :=
  J J1 * Xᵀ * J J1

lemma θ_eq_neg_φ (X : Matn) :
    θ J1 X = - φ J1 X := by
  rfl

/-- φ strictly reverses multiplication: φ(XY) = φ(Y)φ(X). -/
lemma φ_mul_rev (hJ1_sq : J1 * J1 = 1) (X Y : Matn) :
    φ J1 (X * Y) = φ J1 Y * φ J1 X := by
  have hJJ : J J1 * J J1 = (1 : Matn) := by
    simpa using InfoGeometry.Clifford.TowerMatrix.Jn_sq J1 hJ1_sq n
  calc
    φ J1 (X * Y)
        = J J1 * (X * Y)ᵀ * J J1 := by rfl
    _ = J J1 * (Yᵀ * Xᵀ) * J J1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = J J1 * Yᵀ * 1 * Xᵀ * J J1 := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (J J1 * Yᵀ * J J1) * (J J1 * Xᵀ * J J1) := by
          simp only [← hJJ, Matrix.mul_assoc]
    _   = φ J1 Y * φ J1 X := by rfl

/-- θ reverses multiplication up to a minus sign: θ(XY) = -θ(Y)θ(X). -/
lemma θ_mul_rev (hJ1_sq : J1 * J1 = 1) (X Y : Matn) :
    θ J1 (X * Y) = - (θ J1 Y * θ J1 X) := by
  dsimp [θ]
  have h_phi := φ_mul_rev (J1 := J1) hJ1_sq X Y
  dsimp [φ] at h_phi ⊢
  rw [h_phi, neg_mul_neg]

end InfoGeometry.Clifford.Decomposition
