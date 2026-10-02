import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

namespace InfoGeometry.GrandUnification.KleinDiracRealization

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

def Ego (Γ : Module.End R M) : Submodule R M := LinearMap.ker (Γ - 1)
def Anima (Γ : Module.End R M) : Submodule R M := LinearMap.ker (Γ + 1)

structure KleinBoringAnomaly (Γ Twist : Module.End R M) : Prop where
  is_twist : Γ * Twist = - (Twist * Γ)
  twist_inv : Twist * Twist = 1

theorem klein_bottle_chiral_overlap
    (Γ Twist : Module.End R M)
    (h_klein : KleinBoringAnomaly Γ Twist)
    (x : M) (h_left : x ∈ Ego Γ) :
    (Twist x) ∈ Anima Γ := by
  have h_ego : (Γ - 1) x = 0 := h_left
  have h_eval : Γ x = x := by
    have h_sub : Γ x - x = 0 := h_ego
    exact sub_eq_zero.mp h_sub
  
  have h_anima_cond : (Γ + 1) (Twist x) = 0 := by
    have h_linear : (Γ + 1) (Twist x) = Γ (Twist x) + Twist x := rfl
    rw [h_linear]
    have h_comp : Γ (Twist x) = (Γ * Twist) x := rfl
    rw [h_comp, h_klein.is_twist]
    have h_neg_comp : (- (Twist * Γ)) x = - (Twist (Γ x)) := rfl
    rw [h_neg_comp, h_eval]
    exact neg_add_cancel (Twist x)
    
  exact h_anima_cond

end InfoGeometry.GrandUnification.KleinDiracRealization
