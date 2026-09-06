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

lemma θₗ_involutive : (θL).comp (θL) = (LinearMap.id : Matn (n := n) →ₗ[ℝ] Matn (n := n)) := by
  have hJJ : (Jn J1 n) * (Jn J1 n) = (1 : Matn (n := n)) := Jn_sq J1 hJ1_sq n
  have hJt : (Jn J1 n)ᵀ = (Jn J1 n) := Jn_transpose J1 hJ1t n
  have hinv_fun : Function.Involutive (TowerMatrix.cartan J1 n) := TowerMatrix.cartan_involutive (J1 := J1) (n := n) (hJJ := hJJ) (hJt := hJt)
  ext X; simpa [Decomposition.θₗ, Decomposition.θ, TowerMatrix.cartan] using hinv_fun X

noncomputable instance instCartanInvolutionMatn : Cartan.CartanInvolution (Matn (n := n)) where
  θ := θL
  invol := θₗ_involutive (J1 := J1) (hJ1_sq := hJ1_sq) (hJ1t := hJ1t) (n := n)

noncomputable def C : Cartan.CartanInvolution (Matn (n := n)) := inferInstance

lemma mem_Ck_iff (X : Matn (n := n)) : X ∈ (C (J1 := J1) (hJ1_sq := hJ1_sq) (hJ1t := hJ1t) (n := n)).k ↔ θf X = X := by
  let C0 := C (J1 := J1) (hJ1_sq := hJ1_sq) (hJ1t := hJ1t) (n := n)
  constructor
  · rintro ⟨Y, rfl⟩
    have hfix : C0.θ (C0.Pplus Y) = C0.Pplus Y := C0.theta_Pplus Y
    simpa [C0, C, Decomposition.θₗ, Decomposition.θ] using hfix
  · intro hX
    refine ⟨X, ?_⟩
    have : θf X = X := hX
    simp [C0, Cartan.CartanInvolution.Pplus, Decomposition.θₗ, Decomposition.θ, LinearMap.add_apply, LinearMap.id_apply, this]
    rw [← add_smul]
    norm_num
    simp

lemma mem_Cp_iff (X : Matn (n := n)) : X ∈ (C (J1 := J1) (hJ1_sq := hJ1_sq) (hJ1t := hJ1t) (n := n)).p ↔ θf X = -X := by
  let C0 := C (J1 := J1) (hJ1_sq := hJ1_sq) (hJ1t := hJ1t) (n := n)
  constructor
  · rintro ⟨Y, rfl⟩
    have hneg : C0.θ (C0.Pminus Y) = - C0.Pminus Y := C0.theta_Pminus Y
    simpa [C0, C, Decomposition.θₗ, Decomposition.θ] using hneg
  · intro hX
    refine ⟨X, ?_⟩
    have : θf X = -X := hX
    simp [C0, Cartan.CartanInvolution.Pminus, Decomposition.θₗ, Decomposition.θ, sub_eq_add_neg, LinearMap.add_apply, LinearMap.id_apply, this]
    rw [sub_neg_eq_add, ← add_smul]
    norm_num
    simp

lemma kSub_eq_k : Decomposition.kSub (J1 := J1) (n := n) = (C (J1 := J1) (hJ1_sq := hJ1_sq) (hJ1t := hJ1t) (n := n)).k := by
  ext X; simpa [mem_Ck_iff (J1 := J1) (hJ1_sq := hJ1_sq) (hJ1t := hJ1t) (n := n)] using (Decomposition.mem_k_iff (J1 := J1) (n := n) X)

lemma pSub_eq_p : Decomposition.pSub (J1 := J1) (n := n) = (C (J1 := J1) (hJ1_sq := hJ1_sq) (hJ1t := hJ1t) (n := n)).p := by
  ext X; simpa [mem_Cp_iff (J1 := J1) (hJ1_sq := hJ1_sq) (hJ1t := hJ1t) (n := n)] using (Decomposition.mem_p_iff (J1 := J1) (n := n) X)

end InfoGeometry.Clifford.CartanInstance
