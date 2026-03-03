import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Cartan.Involution
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Clifford.Decomposition

open scoped Matrix
namespace InfoGeometry.Clifford.CartanInstance

open Matrix InfoGeometry.Cartan InfoGeometry.Clifford.TowerMatrix InfoGeometry.Clifford.Decomposition

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ) (hJ1_sq : J1 * J1 = 1) (hJ1t : J1ᵀ = J1)
abbrev Matn : Type := Mat n

local notation "θL" => Decomposition.θₗ (J1 := J1) (n := n)
local notation "θf" => Decomposition.θ  (J1 := J1) (n := n)

lemma θₗ_involutive (hJ1_sq : J1 * J1 = 1) (hJ1t : J1ᵀ = J1) : (θL).comp (θL) = (LinearMap.id : Matn (n := n) →ₗ[ℝ] Matn (n := n)) := by
  have hJJ : (Jn J1 n) * (Jn J1 n) = (1 : Matn (n := n)) := Jn_sq J1 hJ1_sq n
  have hJt' : (Jn J1 n)ᵀ = (Jn J1 n) := Jn_transpose J1 hJ1t n
  have hinv_fun : Function.Involutive (TowerMatrix.cartan J1 n) := TowerMatrix.cartan_involutive J1 n hJJ hJt'
  ext X i j
  exact congr_fun (congr_fun (hinv_fun X) i) j

noncomputable def instCartanInvolutionMatn (hJ1_sq : J1 * J1 = 1) (hJ1t : J1ᵀ = J1) : Cartan.CartanInvolution (Matn (n := n)) where
  θ := θL
  invol := θₗ_involutive J1 hJ1_sq hJ1t

noncomputable def C (hJ1_sq : J1 * J1 = 1) (hJ1t : J1ᵀ = J1) : Cartan.CartanInvolution (Matn (n := n)) := instCartanInvolutionMatn J1 hJ1_sq hJ1t



lemma mem_Ck_iff (X : Matn (n := n)) : X ∈ (C (n := n) J1 hJ1_sq hJ1t).k ↔ θf X = X := by
  let C0 := C (n := n) J1 hJ1_sq hJ1t
  constructor
  · rintro ⟨Y, rfl⟩
    change C0.θ (C0.Pplus Y) = C0.Pplus Y
    exact C0.theta_Pplus Y
  · intro hX
    refine ⟨X, ?_⟩
    change (C J1 hJ1_sq hJ1t).Pplus X = X
    dsimp [Cartan.CartanInvolution.Pplus, C, instCartanInvolutionMatn, Decomposition.θₗ, LinearMap.add_apply, LinearMap.id_apply]
    rw [hX, ← two_smul ℝ X, ← smul_assoc]
    norm_num

lemma mem_Cp_iff (X : Matn (n := n)) : X ∈ (C (n := n) J1 hJ1_sq hJ1t).p ↔ θf X = -X := by
  let C0 := C (n := n) J1 hJ1_sq hJ1t
  constructor
  · rintro ⟨Y, rfl⟩
    change C0.θ (C0.Pminus Y) = - C0.Pminus Y
    exact C0.theta_Pminus Y
  · intro hX
    refine ⟨X, ?_⟩
    change (C J1 hJ1_sq hJ1t).Pminus X = X
    dsimp [Cartan.CartanInvolution.Pminus, C, instCartanInvolutionMatn, Decomposition.θₗ, LinearMap.sub_apply, LinearMap.id_apply]
    rw [hX, sub_neg_eq_add, ← two_smul ℝ X, ← smul_assoc]
    norm_num

lemma kSub_eq_k : Decomposition.kSub (J1 := J1) (n := n) = (C J1 hJ1_sq hJ1t).k := by
  ext X
  have hc := mem_Ck_iff J1 hJ1_sq hJ1t X
  have hd := Decomposition.mem_k_iff J1 (n := n) X
  exact Iff.trans hd hc.symm

lemma pSub_eq_p : Decomposition.pSub (J1 := J1) (n := n) = (C J1 hJ1_sq hJ1t).p := by
  ext X
  have hc := mem_Cp_iff J1 hJ1_sq hJ1t X
  have hd := Decomposition.mem_p_iff J1 (n := n) X
  exact Iff.trans hd hc.symm

end InfoGeometry.Clifford.CartanInstance
