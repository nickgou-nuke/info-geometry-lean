import InfoGeometry.Canonical.ErlangenLanglandsQuantumBundle

/-!
# Algebraic homogeneous-space and modular Maurer--Cartan bridge

This owner formalizes only the algebraic part of the homogeneous-space
construction. The quotient is an abstract right-`H`-invariant carrier, so
`H` need not be normal. The Maurer--Cartan readout is evaluated on a supplied
velocity; no manifold or differentiability structure is assumed.
-/

namespace InfoGeometry.Canonical.HomogeneousModularFlows

open InfoGeometry.Canonical.ErlangenLanglandsQuantumBundle
open InfoGeometry.Modular.ExactSequence

universe u v

class HomogeneousSpace (G : Type u) [Group G] (H : Subgroup G) where
  quotient : Type v
  proj : G → quotient
  proj_invariant : ∀ (g : G) (h : H), proj (g * h.1) = proj g

namespace HomogeneousSpace

variable {G : Type u} [Group G] {H : Subgroup G}
  (X : HomogeneousSpace G H)

theorem proj_right_invariant (g : G) (h : H) :
    X.proj (g * h.1) = X.proj g :=
  X.proj_invariant g h

end HomogeneousSpace

/-- Algebraic left Maurer--Cartan readout at a group element and velocity. -/
def leftMaurerCartanReadout {G : Type u} [Group G] (g v : G) : G :=
  g⁻¹ * v

theorem leftMaurerCartanReadout_eq_identity_of_velocity
    {G : Type u} [Group G] (g : G) :
    leftMaurerCartanReadout g g = 1 := by
  simp [leftMaurerCartanReadout]

theorem leftMaurerCartanReadout_mul
    {G : Type u} [Group G] (g v : G) :
    leftMaurerCartanReadout g v = g⁻¹ * v :=
  rfl

theorem leftMaurerCartanReadout_path
    {G : Type u} [Group G] {ι : Type*}
    (path velocity : ι → G) (t : ι) :
    leftMaurerCartanReadout (path t) (velocity t) =
      (path t)⁻¹ * velocity t :=
  rfl

theorem dlogCocycle_eq_leftMaurerCartanReadout
    {A : Type*} [Ring A] [Group A]
    (D : Derivation A) (delta invDelta : A)
    (h_inv : invDelta = delta⁻¹) :
    dlogCocycle D invDelta delta =
      leftMaurerCartanReadout delta (D delta) := by
  rw [h_inv]
  simp only [dlogCocycle, leftMaurerCartanReadout]
  rfl

theorem dlogCocycle_eq_maurerCartan_of_unit
    {A : Type*} [Ring A] [Group A]
    (D : Derivation A) (delta : A) :
    dlogCocycle D (delta⁻¹) delta =
      leftMaurerCartanReadout delta (D delta) :=
  dlogCocycle_eq_leftMaurerCartanReadout D delta delta⁻¹ rfl

end InfoGeometry.Canonical.HomogeneousModularFlows
