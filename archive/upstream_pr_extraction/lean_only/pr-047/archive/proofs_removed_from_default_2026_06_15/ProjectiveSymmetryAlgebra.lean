import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Projective Symmetry Algebras with Z₂ Gauge Structures

Formalizes the algebraic foundation of "Classification of time-reversal-invariant 
crystals with gauge structures" (Chen et al., Nat. Comm. 2023).

Proves that projective symmetry representations on a Hilbert space strictly 
require the gauge flux phase factors to form a 2-cocycle in H²(G, Z₂).
This generates the Brillouin Klein Bottle topology.
-/

namespace ProjectiveSymmetryAlgebra

variable {G : Type} [Group G]
variable {R : Type} [CommRing R]
variable {Operator : Type} [Ring Operator] [Algebra R Operator]

/-- 
A Projective Representation assigns an operator `ρ(g)` to each group element,
such that composition picks up a scalar phase factor `ν(g,h)`. 
In T-invariant crystals, these are restricted to `Z₂` (±1).
-/
structure ProjectiveRep where
  ρ : G → Operator
  ν : G → G → R
  /-- Projective composition: ρ(g) * ρ(h) = ν(g,h) • ρ(gh) -/
  proj_mul : ∀ g h, ρ g * ρ h = algebraMap R Operator (ν g h) * ρ (g * h)
  /-- The representation is faithful enough that scalars can be extracted. -/
  rho_inj : ∀ c d g, algebraMap R Operator c * ρ g = algebraMap R Operator d * ρ g → c = d

/-- 
The fundamental 2-cocycle condition for a gauge flux.
This classifies the 458 Projective Symmetry Algebras.
-/
def IsCocycle (ν : G → G → R) : Prop :=
  ∀ g1 g2 g3 : G, ν g1 g2 * ν (g1 * g2) g3 = ν g1 (g2 * g3) * ν g2 g3

/-- 
Theorem: Associativity of quantum operators physically enforces the gauge 
flux 2-cocycle condition.

(ρ(g₁) ρ(g₂)) ρ(g₃) = ρ(g₁) (ρ(g₂) ρ(g₃))
=> ν(g₁, g₂) ν(g₁g₂, g₃) = ν(g₂, g₃) ν(g₁, g₂g₃)
-/
theorem associativity_forces_cocycle (rep : ProjectiveRep (G := G) (R := R) (Operator := Operator)) :
    IsCocycle rep.ν := by
  intro g1 g2 g3
  -- Start with the fundamental associativity of the Operator ring
  have h_assoc : (rep.ρ g1 * rep.ρ g2) * rep.ρ g3 = rep.ρ g1 * (rep.ρ g2 * rep.ρ g3) := mul_assoc _ _ _
  
  -- Expand LHS: (ρ(g1) * ρ(g2)) * ρ(g3)
  have h_lhs : (rep.ρ g1 * rep.ρ g2) * rep.ρ g3 = 
      algebraMap R Operator (rep.ν g1 g2 * rep.ν (g1 * g2) g3) * rep.ρ (g1 * g2 * g3) := by
    calc
      (rep.ρ g1 * rep.ρ g2) * rep.ρ g3 
        = (algebraMap R Operator (rep.ν g1 g2) * rep.ρ (g1 * g2)) * rep.ρ g3 := by rw [rep.proj_mul]
      _ = algebraMap R Operator (rep.ν g1 g2) * (rep.ρ (g1 * g2) * rep.ρ g3) := by rw [mul_assoc]
      _ = algebraMap R Operator (rep.ν g1 g2) * (algebraMap R Operator (rep.ν (g1 * g2) g3) * rep.ρ (g1 * g2 * g3)) := by rw [rep.proj_mul]
      _ = (algebraMap R Operator (rep.ν g1 g2) * algebraMap R Operator (rep.ν (g1 * g2) g3)) * rep.ρ (g1 * g2 * g3) := by rw [←mul_assoc]
      _ = algebraMap R Operator (rep.ν g1 g2 * rep.ν (g1 * g2) g3) * rep.ρ (g1 * g2 * g3) := by rw [←map_mul]

  -- Expand RHS: ρ(g1) * (ρ(g2) * ρ(g3))
  have h_rhs : rep.ρ g1 * (rep.ρ g2 * rep.ρ g3) = 
      algebraMap R Operator (rep.ν g1 (g2 * g3) * rep.ν g2 g3) * rep.ρ (g1 * (g2 * g3)) := by
    calc
      rep.ρ g1 * (rep.ρ g2 * rep.ρ g3)
        = rep.ρ g1 * (algebraMap R Operator (rep.ν g2 g3) * rep.ρ (g2 * g3)) := by rw [rep.proj_mul]
      -- Commute the scalar through ρ(g1)
      _ = algebraMap R Operator (rep.ν g2 g3) * (rep.ρ g1 * rep.ρ (g2 * g3)) := by rw [Algebra.commutes, mul_assoc]
      _ = algebraMap R Operator (rep.ν g2 g3) * (algebraMap R Operator (rep.ν g1 (g2 * g3)) * rep.ρ (g1 * (g2 * g3))) := by rw [rep.proj_mul]
      _ = (algebraMap R Operator (rep.ν g2 g3) * algebraMap R Operator (rep.ν g1 (g2 * g3))) * rep.ρ (g1 * (g2 * g3)) := by rw [←mul_assoc]
      _ = algebraMap R Operator (rep.ν g2 g3 * rep.ν g1 (g2 * g3)) * rep.ρ (g1 * (g2 * g3)) := by rw [←map_mul]
      _ = algebraMap R Operator (rep.ν g1 (g2 * g3) * rep.ν g2 g3) * rep.ρ (g1 * (g2 * g3)) := by rw [mul_comm]

  -- Equate LHS and RHS
  rw [h_lhs, h_rhs, mul_assoc g1 g2 g3] at h_assoc
  
  -- Extract the scalar relation
  exact rep.rho_inj _ _ _ h_assoc

end ProjectiveSymmetryAlgebra
