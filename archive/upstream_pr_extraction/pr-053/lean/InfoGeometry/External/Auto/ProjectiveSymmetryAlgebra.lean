import Mathlib.Tactic

/-!
# Projective symmetry algebra cocycle law

A genuine associativity theorem: if operators multiply projectively
`ρ(g)ρ(h)=ν(g,h)ρ(gh)` and scalar coefficients can be cancelled from one
nonzero/projectively faithful fibre, then associativity forces the `2`-cocycle
identity for `ν`.
-/

noncomputable section

namespace ProjectiveSymmetryAlgebra

variable {G : Type} [Group G]
variable {R : Type} [CommRing R]
variable {Operator : Type} [Ring Operator] [Algebra R Operator]

/-- Projective representation with scalar extraction on each fibre. -/
structure ProjectiveRep where
  ρ : G → Operator
  ν : G → G → R
  proj_mul : ∀ g h, ρ g * ρ h = algebraMap R Operator (ν g h) * ρ (g * h)
  rho_cancel : ∀ c d g, algebraMap R Operator c * ρ g = algebraMap R Operator d * ρ g → c = d

/-- Group `2`-cocycle identity. -/
def IsCocycle (ν : G → G → R) : Prop :=
  ∀ g1 g2 g3 : G, ν g1 g2 * ν (g1 * g2) g3 = ν g1 (g2 * g3) * ν g2 g3

/-- Associativity of the operator product forces the projective phase to be a cocycle. -/
theorem associativity_forces_cocycle (rep : ProjectiveRep (G := G) (R := R) (Operator := Operator)) :
    IsCocycle rep.ν := by
  intro g1 g2 g3
  have h_assoc : (rep.ρ g1 * rep.ρ g2) * rep.ρ g3 = rep.ρ g1 * (rep.ρ g2 * rep.ρ g3) := by
    rw [mul_assoc]
  have h_lhs : (rep.ρ g1 * rep.ρ g2) * rep.ρ g3 =
      algebraMap R Operator (rep.ν g1 g2 * rep.ν (g1 * g2) g3) * rep.ρ ((g1 * g2) * g3) := by
    calc
      (rep.ρ g1 * rep.ρ g2) * rep.ρ g3
          = (algebraMap R Operator (rep.ν g1 g2) * rep.ρ (g1 * g2)) * rep.ρ g3 := by rw [rep.proj_mul]
      _ = algebraMap R Operator (rep.ν g1 g2) * (rep.ρ (g1 * g2) * rep.ρ g3) := by rw [mul_assoc]
      _ = algebraMap R Operator (rep.ν g1 g2) *
            (algebraMap R Operator (rep.ν (g1 * g2) g3) * rep.ρ ((g1 * g2) * g3)) := by rw [rep.proj_mul]
      _ = (algebraMap R Operator (rep.ν g1 g2) * algebraMap R Operator (rep.ν (g1 * g2) g3)) *
            rep.ρ ((g1 * g2) * g3) := by rw [← mul_assoc]
      _ = algebraMap R Operator (rep.ν g1 g2 * rep.ν (g1 * g2) g3) * rep.ρ ((g1 * g2) * g3) := by rw [map_mul]
  have h_rhs : rep.ρ g1 * (rep.ρ g2 * rep.ρ g3) =
      algebraMap R Operator (rep.ν g1 (g2 * g3) * rep.ν g2 g3) * rep.ρ (g1 * (g2 * g3)) := by
    calc
      rep.ρ g1 * (rep.ρ g2 * rep.ρ g3)
          = rep.ρ g1 * (algebraMap R Operator (rep.ν g2 g3) * rep.ρ (g2 * g3)) := by rw [rep.proj_mul]
      _ = (rep.ρ g1 * algebraMap R Operator (rep.ν g2 g3)) * rep.ρ (g2 * g3) := by rw [mul_assoc]
      _ = (algebraMap R Operator (rep.ν g2 g3) * rep.ρ g1) * rep.ρ (g2 * g3) := by rw [Algebra.commutes]
      _ = algebraMap R Operator (rep.ν g2 g3) * (rep.ρ g1 * rep.ρ (g2 * g3)) := by rw [mul_assoc]
      _ = algebraMap R Operator (rep.ν g2 g3) *
            (algebraMap R Operator (rep.ν g1 (g2 * g3)) * rep.ρ (g1 * (g2 * g3))) := by rw [rep.proj_mul]
      _ = (algebraMap R Operator (rep.ν g2 g3) * algebraMap R Operator (rep.ν g1 (g2 * g3))) *
            rep.ρ (g1 * (g2 * g3)) := by rw [← mul_assoc]
      _ = algebraMap R Operator (rep.ν g2 g3 * rep.ν g1 (g2 * g3)) * rep.ρ (g1 * (g2 * g3)) := by rw [map_mul]
      _ = algebraMap R Operator (rep.ν g1 (g2 * g3) * rep.ν g2 g3) * rep.ρ (g1 * (g2 * g3)) := by rw [mul_comm]
  have h_scalar :
      algebraMap R Operator (rep.ν g1 g2 * rep.ν (g1 * g2) g3) * rep.ρ (g1 * (g2 * g3)) =
      algebraMap R Operator (rep.ν g1 (g2 * g3) * rep.ν g2 g3) * rep.ρ (g1 * (g2 * g3)) := by
    simpa [h_lhs, h_rhs, mul_assoc] using h_assoc
  exact rep.rho_cancel _ _ _ h_scalar

#check associativity_forces_cocycle

end ProjectiveSymmetryAlgebra
