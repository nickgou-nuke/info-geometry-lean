import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import InfoGeometry.GrandUnification.MachianCosmology
import InfoGeometry.GrandUnification.ModularPhaseSeparation

namespace InfoGeometry.GrandUnification.DirectSumDecomposition

open LinearMap
open InfoGeometry.GrandUnification.MachianCosmology
open InfoGeometry.GrandUnification.ModularPhaseSeparation

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

/-!
### Direct Sum Recovery of the Vacuum

To completely close the causal loop, we prove that the entire state space 
(the spinor fluid M) is perfectly recovered by the direct sum of its Weyl 
components (Ego and Anima). 

Since we already proved Ego ⊓ Anima = ⊥, proving Ego ⊔ Anima = ⊤ guarantees 
the space is a strict direct sum M = WeylLeft ⊕ WeylRight.
-/

/-- 
Theorem: Total Geometric Fractionalization.
If Γ is a Krein symmetry (Γ² = 1), then the total state space strictly 
decomposes into the supremum of the Ego (Left) and Anima (Right) submodules.
-/
theorem ego_sup_anima_eq_top (Γ : Module.End R M) (h_krein : IsKreinSymmetry Γ) :
    Ego Γ ⊔ Anima Γ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  
  -- We construct the exact Weyl projections: P_L(x) and P_R(x)
  let half := ⅟(2 : R)
  let x_ego := half • (x + Γ x)
  let x_anima := half • (x - Γ x)
  
  -- 1. Prove that the projections sum to the original state x
  have h_decomp : x = x_ego + x_anima := by
    dsimp [x_ego, x_anima]
    rw [← smul_add]
    have h_add : x + Γ x + (x - Γ x) = x + x := by abel
    rw [h_add]
    have h_two : x + x = (2 : R) • x := (two_smul R x).symm
    rw [h_two, ← mul_smul, invOf_mul_self, one_smul]
  
  -- 2. Prove that the Left projection is strictly in the Ego space
  have h_in_ego : x_ego ∈ Ego Γ := by
    dsimp [Ego]
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.one_apply]
    dsimp [x_ego]
    rw [map_smul, map_add]
    unfold IsKreinSymmetry at h_krein
    have h_gamma_sq : Γ (Γ x) = x := by
      have h1 : (Γ * Γ) x = x := by rw [h_krein, LinearMap.one_apply]
      exact h1
    rw [h_gamma_sq]
    have h_comm : Γ x + x = x + Γ x := add_comm _ _
    rw [h_comm, sub_self]
    
  -- 3. Prove that the Right projection is strictly in the Anima space
  have h_in_anima : x_anima ∈ Anima Γ := by
    dsimp [Anima]
    simp only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.one_apply]
    dsimp [x_anima]
    rw [map_smul, map_sub]
    unfold IsKreinSymmetry at h_krein
    have h_gamma_sq : Γ (Γ x) = x := by
      have h1 : (Γ * Γ) x = x := by rw [h_krein, LinearMap.one_apply]
      exact h1
    rw [h_gamma_sq]
    rw [← smul_add]
    have h_sub : Γ x - x + (x - Γ x) = 0 := by abel
    rw [h_sub, smul_zero]

  -- 4. Synthesize the decomposition
  rw [h_decomp]
  exact Submodule.add_mem_sup h_in_ego h_in_anima

end InfoGeometry.GrandUnification.DirectSumDecomposition
