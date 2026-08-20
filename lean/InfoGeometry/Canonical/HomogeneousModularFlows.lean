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

/-- Ring-valued logarithmic readout with an explicitly supplied inverse. -/
def algebraicMaurerCartanReadout {A : Type*} [Ring A] (invElement velocity : A) : A :=
  invElement * velocity

/-! A path-level wrapper keeps the base parameter explicit without claiming
that a differentiable manifold structure has been constructed. -/
def maurerCartanPath {ι A : Type*} [Ring A]
    (path inversePath velocity : ι → A) (t : ι) : A :=
  algebraicMaurerCartanReadout (inversePath t) (velocity t)

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
    {A : Type*} [Ring A]
    (D : Derivation A) (delta invDelta : A) :
    dlogCocycle D invDelta delta =
      algebraicMaurerCartanReadout invDelta (D delta) := by
  rfl

theorem dlogCocycle_eq_maurerCartan_of_suppliedInverse
    {A : Type*} [Ring A]
    (D : Derivation A) (delta invDelta : A) :
    dlogCocycle D invDelta delta =
      algebraicMaurerCartanReadout invDelta (D delta) :=
  dlogCocycle_eq_leftMaurerCartanReadout D delta invDelta

theorem maurerCartanPath_eq_dlogCocycle
    {ι A : Type*} [Ring A] (D : Derivation A)
    (path inversePath velocity : ι → A) (t : ι)
    (h_velocity : velocity t = D (path t))
    (h_inverse : inversePath t = (path t)⁻¹) :
    maurerCartanPath path inversePath velocity t =
      dlogCocycle D (inversePath t) (path t) := by
  unfold maurerCartanPath algebraicMaurerCartanReadout dlogCocycle
  rw [h_velocity]

theorem capstone_logarithmicBridge_factors_maurerCartan
    {ι A : Type*} [Ring A] (D : Derivation A)
    (path inversePath velocity : ι → A) (t : ι)
    (h_velocity : velocity t = D (path t)) :
    dlogCocycle D (inversePath t) (path t) =
      maurerCartanPath path inversePath velocity t := by
  symm
  exact maurerCartanPath_eq_dlogCocycle D path inversePath velocity t h_velocity rfl

end InfoGeometry.Canonical.HomogeneousModularFlows
