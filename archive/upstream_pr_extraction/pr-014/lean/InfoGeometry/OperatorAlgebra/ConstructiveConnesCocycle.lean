/-
InfoGeometry/OperatorAlgebra/ConstructiveConnesCocycle.lean
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle

structure VerifiedModularFlow (A : Type*) [Ring A] where
  σ : ℝ → (A → A)
  map_mul : ∀ (t : ℝ) (x y : A), σ t (x * y) = σ t x * σ t y
  flow_zero : ∀ x : A, σ 0 x = x
  flow_add : ∀ (s t : ℝ) (x : A), σ (s + t) x = σ s (σ t x)

structure ConnesCocycle {A : Type*} [Ring A]
    (flow_phi flow_omega : VerifiedModularFlow A) where
  u : ℝ → A
  cocycle_law : ∀ s t : ℝ, u (s + t) = u s * flow_omega.σ s (u t)
  intertwine_law :
    ∀ (t : ℝ) (x : A), flow_phi.σ t x * u t = u t * flow_omega.σ t x

def chain_cocycles {A : Type*} [Ring A]
    {flow_phi flow_omega flow_psi : VerifiedModularFlow A}
    (u : ConnesCocycle flow_phi flow_omega)
    (v : ConnesCocycle flow_omega flow_psi) :
    ConnesCocycle flow_phi flow_psi where
  u := fun t => u.u t * v.u t

  cocycle_law := by
    intro s t
    calc
      u.u (s + t) * v.u (s + t)
          =
          (u.u s * flow_omega.σ s (u.u t)) *
            (v.u s * flow_psi.σ s (v.u t)) := by
            rw [u.cocycle_law s t, v.cocycle_law s t]
      _ =
          u.u s *
            (flow_omega.σ s (u.u t) * v.u s) *
              flow_psi.σ s (v.u t) := by
            simp only [mul_assoc]
      _ =
          u.u s *
            (v.u s * flow_psi.σ s (u.u t)) *
              flow_psi.σ s (v.u t) := by
            rw [v.intertwine_law s (u.u t)]
      _ =
          (u.u s * v.u s) *
            (flow_psi.σ s (u.u t) * flow_psi.σ s (v.u t)) := by
            simp only [mul_assoc]
      _ =
          (u.u s * v.u s) *
            flow_psi.σ s (u.u t * v.u t) := by
            rw [flow_psi.map_mul s (u.u t) (v.u t)]

  intertwine_law := by
    intro t x
    calc
      flow_phi.σ t x * (u.u t * v.u t)
          = (flow_phi.σ t x * u.u t) * v.u t := by
            rw [mul_assoc]
      _ = (u.u t * flow_omega.σ t x) * v.u t := by
            rw [u.intertwine_law t x]
      _ = u.u t * (flow_omega.σ t x * v.u t) := by
            rw [mul_assoc]
      _ = u.u t * (v.u t * flow_psi.σ t x) := by
            rw [v.intertwine_law t x]
      _ = (u.u t * v.u t) * flow_psi.σ t x := by
            rw [mul_assoc]

end InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle

