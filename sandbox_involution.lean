import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Cartan involution and projectors

A lightweight, repo-local Cartan involution API:

* `CartanInvolution` = linear involution `θ : E →ₗ[ℝ] E` with `θ ∘ θ = id`.
* Projectors `Pplus = (Id + θ)/2`, `Pminus = (Id - θ)/2`.
* Eigenspace submodules `k = ker(θ - Id)`, `p = ker(θ + Id)`.
-/

namespace Cartan

section

variable {E : Type _} [AddCommGroup E] [Module ℝ E]

/-- A Cartan involution on a real module `E`. -/
structure CartanInvolution (E : Type _) [AddCommGroup E] [Module ℝ E] where
  θ : E →ₗ[ℝ] E
  invol : θ.comp θ = LinearMap.id

namespace CartanInvolution

variable (C : CartanInvolution E)

@[simp] lemma θθ (x : E) : C.θ (C.θ x) = x := by
  have h := congrArg (fun f => f x) C.invol
  simpa [LinearMap.comp_apply, LinearMap.id_apply] using h

/-- `(Id + θ)/2`. -/
noncomputable def Pplus : E →ₗ[ℝ] E :=
  ( (2 : ℝ)⁻¹ • (LinearMap.id + C.θ) )

/-- `(Id - θ)/2`. -/
noncomputable def Pminus : E →ₗ[ℝ] E :=
  ( (2 : ℝ)⁻¹ • (LinearMap.id - C.θ) )

@[simp] lemma Pplus_apply (x : E) :
    C.Pplus x = (2 : ℝ)⁻¹ • (x + C.θ x) := by
  simp [Pplus, LinearMap.add_apply, LinearMap.id_apply]

@[simp] lemma Pminus_apply (x : E) :
    C.Pminus x = (2 : ℝ)⁻¹ • (x - C.θ x) := by
  simp [Pminus, LinearMap.sub_apply, LinearMap.id_apply]

/-- `k = ker(θ - Id)` (`+1` eigenspace). -/
noncomputable def k : Submodule ℝ E :=
  (C.θ - LinearMap.id).ker

/-- `p = ker(θ + Id)` (`-1` eigenspace). -/
noncomputable def p : Submodule ℝ E :=
  (C.θ + LinearMap.id).ker

lemma mem_k_iff (x : E) : x ∈ C.k ↔ C.θ x = x := by
  simp [k, sub_eq_zero]

lemma mem_p_iff (x : E) : x ∈ C.p ↔ C.θ x = -x := by
  simp [p, add_eq_zero_iff_eq_neg]

/-- `θ(Pplus x) = Pplus x`. -/
@[simp] lemma theta_Pplus (x : E) : C.θ (C.Pplus x) = C.Pplus x := by
  rw [Pplus_apply, LinearMap.map_smul, LinearMap.map_add, C.θθ]
  have h : C.θ x + x = x + C.θ x := add_comm _ _
  rw [h]

/-- `θ(Pminus x) = -Pminus x`. -/
@[simp] lemma theta_Pminus (x : E) : C.θ (C.Pminus x) = - C.Pminus x := by
  rw [Pminus_apply, LinearMap.map_smul, LinearMap.map_sub, C.θθ]
  have h : C.θ x - x = -(x - C.θ x) := by abel
  rw [h, smul_neg]

/-- `Pplus` is idempotent. -/
lemma Pplus_idempotent : C.Pplus.comp C.Pplus = C.Pplus := by
  apply LinearMap.ext; intro x
  calc
    (C.Pplus.comp C.Pplus) x = C.Pplus (C.Pplus x) := by rw [LinearMap.comp_apply]
    _ = (2 : ℝ)⁻¹ • (C.Pplus x + C.θ (C.Pplus x)) := by rw [Pplus_apply]
    _ = (2 : ℝ)⁻¹ • (C.Pplus x + C.Pplus x) := by rw [theta_Pplus]
    _ = (2 : ℝ)⁻¹ • ((1 : ℝ) • C.Pplus x + (1 : ℝ) • C.Pplus x) := by rw [one_smul]
    _ = (2 : ℝ)⁻¹ • ((1 + 1 : ℝ) • C.Pplus x) := by rw [← add_smul]
    _ = ((2 : ℝ)⁻¹ * (1 + 1 : ℝ)) • C.Pplus x := by rw [smul_smul]
    _ = C.Pplus x := by
      have h : (2 : ℝ)⁻¹ * (1 + 1) = 1 := by norm_num
      rw [h, one_smul]

/-- `Pminus` is idempotent. -/
lemma Pminus_idempotent : C.Pminus.comp C.Pminus = C.Pminus := by
  apply LinearMap.ext; intro x
  calc
    (C.Pminus.comp C.Pminus) x = C.Pminus (C.Pminus x) := by rw [LinearMap.comp_apply]
    _ = (2 : ℝ)⁻¹ • (C.Pminus x - C.θ (C.Pminus x)) := by rw [Pminus_apply]
    _ = (2 : ℝ)⁻¹ • (C.Pminus x - (-C.Pminus x)) := by rw [theta_Pminus]
    _ = (2 : ℝ)⁻¹ • (C.Pminus x + C.Pminus x) := by rw [sub_neg_eq_add]
    _ = (2 : ℝ)⁻¹ • ((1 : ℝ) • C.Pminus x + (1 : ℝ) • C.Pminus x) := by rw [one_smul]
    _ = (2 : ℝ)⁻¹ • ((1 + 1 : ℝ) • C.Pminus x) := by rw [← add_smul]
    _ = ((2 : ℝ)⁻¹ * (1 + 1 : ℝ)) • C.Pminus x := by rw [smul_smul]
    _ = C.Pminus x := by
      have h : (2 : ℝ)⁻¹ * (1 + 1) = 1 := by norm_num
      rw [h, one_smul]

/-- Decomposition: `x = Pplus x + Pminus x`. -/
lemma decomposition (x : E) : x = C.Pplus x + C.Pminus x := by
  rw [Pplus_apply, Pminus_apply, smul_add, smul_sub]
  have h : (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • C.θ x + ((2 : ℝ)⁻¹ • x - (2 : ℝ)⁻¹ • C.θ x) = (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • x := by abel
  rw [h, ← add_smul]
  have h2 : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  rw [h2, one_smul]

/-- Alias name used in some older notes. -/
lemma decompose (x : E) : x = C.Pplus x + C.Pminus x :=
  C.decomposition x

/-- `Pplus x ∈ k`. -/
lemma Pplus_mem_k (x : E) : C.Pplus x ∈ C.k :=
  (C.mem_k_iff _).2 (C.theta_Pplus x)

/-- `Pminus x ∈ p`. -/
lemma Pminus_mem_p (x : E) : C.Pminus x ∈ C.p :=
  (C.mem_p_iff _).2 (C.theta_Pminus x)

end CartanInvolution
end

end Cartan
