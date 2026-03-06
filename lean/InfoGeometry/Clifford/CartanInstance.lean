import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Cartan.Involution
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Clifford.Decomposition

open scoped Matrix

namespace InfoGeometry.Clifford.CartanInstance

open Matrix
open InfoGeometry.Cartan
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Decomposition

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ)
variable (hJ1_sq : J1 * J1 = 1) (hJ1t : J1ᵀ = J1)

abbrev Matn : Type := Mat n

local notation "θL" => Decomposition.θₗ (J1 := J1) (n := n)
local notation "θf" => Decomposition.θ (J1 := J1) (n := n)

lemma θₗ_involutive (hJ1_sq : J1 * J1 = 1) (hJ1t : J1ᵀ = J1) :
    (θL).comp (θL) = (LinearMap.id : Matn (n := n) →ₗ[ℝ] Matn (n := n)) := by
  have hJJ : (Jn J1 n) * (Jn J1 n) = (1 : Matn (n := n)) := Jn_sq J1 hJ1_sq n
  have hJt' : (Jn J1 n)ᵀ = (Jn J1 n) := Jn_transpose J1 hJ1t n
  have hinv_fun : Function.Involutive (TowerMatrix.cartan J1 n) :=
    TowerMatrix.cartan_involutive J1 n hJJ hJt'
  ext X i j
  exact congr_fun (congr_fun (hinv_fun X) i) j

/-- Cartan involution as a linear equivalence on matrix towers. -/
noncomputable def C (hJ1_sq : J1 * J1 = 1) (hJ1t : J1ᵀ = J1) :
    Matn (n := n) ≃ₗ[ℝ] Matn (n := n) :=
  LinearEquiv.ofLinear (θL) (θL)
    (θₗ_involutive (J1 := J1) (n := n) hJ1_sq hJ1t)
    (θₗ_involutive (J1 := J1) (n := n) hJ1_sq hJ1t)

@[simp] lemma C_apply (X : Matn (n := n)) :
    C (J1 := J1) (n := n) hJ1_sq hJ1t X = θf X := rfl

lemma C_isCartanInvolution :
    Cartan.IsCartanInvolution (C (J1 := J1) (n := n) hJ1_sq hJ1t) := by
  simpa [C] using (θₗ_involutive (J1 := J1) (n := n) hJ1_sq hJ1t)

lemma mem_Ck_iff (X : Matn (n := n)) :
    X ∈ Cartan.k (θ := C (J1 := J1) (n := n) hJ1_sq hJ1t) ↔ θf X = X := by
  constructor
  · rintro ⟨Y, rfl⟩
    exact Cartan.theta_Pplus
      (θ := C (J1 := J1) (n := n) hJ1_sq hJ1t)
      (hθ := C_isCartanInvolution (J1 := J1) (n := n) hJ1_sq hJ1t) Y
  · intro hX
    refine ⟨X, ?_⟩
    change Cartan.Pplus (θ := C (J1 := J1) (n := n) hJ1_sq hJ1t) X = X
    dsimp [Cartan.Pplus]
    rw [hX, ← two_smul ℝ X, ← smul_assoc]
    simp

lemma mem_Cp_iff (X : Matn (n := n)) :
    X ∈ Cartan.p (θ := C (J1 := J1) (n := n) hJ1_sq hJ1t) ↔ θf X = -X := by
  constructor
  · rintro ⟨Y, rfl⟩
    exact Cartan.theta_Pminus
      (θ := C (J1 := J1) (n := n) hJ1_sq hJ1t)
      (hθ := C_isCartanInvolution (J1 := J1) (n := n) hJ1_sq hJ1t) Y
  · intro hX
    refine ⟨X, ?_⟩
    change Cartan.Pminus (θ := C (J1 := J1) (n := n) hJ1_sq hJ1t) X = X
    dsimp [Cartan.Pminus]
    rw [hX, sub_neg_eq_add, ← two_smul ℝ X, ← smul_assoc]
    simp

lemma kSub_eq_k :
    Decomposition.kSub (J1 := J1) (n := n)
      = Cartan.k (θ := C (J1 := J1) (n := n) hJ1_sq hJ1t) := by
  ext X
  have hk := Decomposition.mem_k_iff (J1 := J1) (n := n) X
  have hc := mem_Ck_iff (J1 := J1) (n := n) hJ1_sq hJ1t X
  exact hk.trans hc.symm

lemma pSub_eq_p :
    Decomposition.pSub (J1 := J1) (n := n)
      = Cartan.p (θ := C (J1 := J1) (n := n) hJ1_sq hJ1t) := by
  ext X
  have hk := Decomposition.mem_p_iff (J1 := J1) (n := n) X
  have hc := mem_Cp_iff (J1 := J1) (n := n) hJ1_sq hJ1t X
  exact hk.trans hc.symm

end InfoGeometry.Clifford.CartanInstance
