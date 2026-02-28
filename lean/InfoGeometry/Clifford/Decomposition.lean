import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Clifford.TowerMatrix
import Mathlib.Tactic

open scoped Matrix
open scoped Kronecker

namespace InfoGeometry.Clifford.Decomposition

open Matrix InfoGeometry.Clifford.TowerMatrix

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ) (hJ1_sq : J1 * J1 = 1)
abbrev Matn : Type := Mat n
noncomputable def J : Matn (n := n) := Jn J1 n

noncomputable def θ (X : Matn (n := n)) : Matn (n := n) := TowerMatrix.cartan J1 n X
noncomputable def θₗ : Matn (n := n) →ₗ[ℝ] Matn (n := n) :=
{ toFun := θ (J1 := J1) (n := n), map_add' := by intro X Y; simp [θ, TowerMatrix.cartan, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc], map_smul' := by intro r X; simp [θ, TowerMatrix.cartan, Matrix.transpose_smul, Matrix.mul_assoc] }

noncomputable def kSub : Submodule ℝ (Matn (n := n)) := (θₗ (J1 := J1) (n := n) - LinearMap.id).ker
noncomputable def pSub : Submodule ℝ (Matn (n := n)) := (θₗ (J1 := J1) (n := n) + LinearMap.id).ker

lemma mem_k_iff (X : Matn (n := n)) : X ∈ kSub (J1 := J1) (n := n) ↔ θ (J1 := J1) (n := n) X = X := by simp [kSub, θₗ, θ, TowerMatrix.cartan, sub_eq_add_neg]
lemma mem_p_iff (X : Matn (n := n)) : X ∈ pSub (J1 := J1) (n := n) ↔ θ (J1 := J1) (n := n) X = -X := by simp [pSub, θₗ, θ, TowerMatrix.cartan, sub_eq_add_neg]

/-- φ(X) = J Xᵀ J (The pure metric anti-automorphism engine). -/
noncomputable def φ (X : Matn (n := n)) : Matn (n := n) :=
  J (J1 := J1) (n := n) * Xᵀ * J (J1 := J1) (n := n)

lemma θ_eq_neg_φ (X : Matn (n := n)) :
    θ (J1 := J1) (n := n) X = - φ (J1 := J1) (n := n) X := by
  simp [θ, TowerMatrix.cartan, φ]

/-- φ strictly reverses multiplication: φ(XY) = φ(Y)φ(X). -/
lemma φ_mul_rev (X Y : Matn (n := n)) :
    φ (J1 := J1) (n := n) (X * Y) = φ (J1 := J1) (n := n) Y * φ (J1 := J1) (n := n) X := by
  have hJJ : J (J1 := J1) (n := n) * J (J1 := J1) (n := n) = (1 : Matn (n := n)) :=
    TowerMatrix.Jn_sq J1 hJ1_sq n
  calc
    φ (J1 := J1) (n := n) (X * Y)
        = J * (X * Y)ᵀ * J := by rfl
    _   = J * (Yᵀ * Xᵀ) * J := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _   = (J * Yᵀ * J) * (J * Xᵀ * J) := by simp [Matrix.mul_assoc, hJJ]
    _   = φ (J1 := J1) (n := n) Y * φ (J1 := J1) (n := n) X := by rfl

/-- θ reverses multiplication up to a minus sign: θ(XY) = -θ(Y)θ(X). -/
lemma θ_mul_rev (X Y : Matn (n := n)) :
    θ (J1 := J1) (n := n) (X * Y) = - (θ (J1 := J1) (n := n) Y * θ (J1 := J1) (n := n) X) := by
  simp [θ_eq_neg_φ (J1 := J1) (n := n), φ_mul_rev (J1 := J1) (hJ1_sq := hJ1_sq) (n := n),
        TowerMatrix.cartan, θ, φ, Matrix.mul_assoc]

end InfoGeometry.Clifford.Decomposition
