import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Cartan.Involution
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Clifford.Decomposition

open scoped Matrix

namespace CartanInstance

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
    Cartan.IsCartanInvolution ((C (J1 := J1) (n := n) hJ1_sq hJ1t).toLinearMap) := by
  simpa [C] using (θₗ_involutive (J1 := J1) (n := n) hJ1_sq hJ1t)

lemma mem_Ck_iff (X : Matn (n := n)) :
    X ∈ Decomposition.kSub (J1 := J1) (n := n) ↔ θf X = X := by
  simpa using (Decomposition.mem_k_iff (J1 := J1) (n := n) X)

lemma mem_Cp_iff (X : Matn (n := n)) :
    X ∈ Decomposition.pSub (J1 := J1) (n := n) ↔ θf X = -X := by
  simpa using (Decomposition.mem_p_iff (J1 := J1) (n := n) X)

noncomputable def Ck : Submodule ℝ (Matn (n := n)) :=
  Decomposition.kSub (J1 := J1) (n := n)

noncomputable def Cp : Submodule ℝ (Matn (n := n)) :=
  Decomposition.pSub (J1 := J1) (n := n)

lemma kSub_eq_k :
    Decomposition.kSub (J1 := J1) (n := n)
      = Ck (J1 := J1) (n := n) := rfl

lemma pSub_eq_p :
    Decomposition.pSub (J1 := J1) (n := n)
      = Cp (J1 := J1) (n := n) := rfl

end CartanInstance
