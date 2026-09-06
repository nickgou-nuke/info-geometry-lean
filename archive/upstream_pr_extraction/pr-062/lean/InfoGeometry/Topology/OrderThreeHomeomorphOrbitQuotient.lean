import Mathlib.Topology.Category.TopCat.Basic

/-!
# Coarse orbit quotients for order-three homeomorphisms

This is a generic quotient-topology owner.  It records only the orbit space of
an order-three homeomorphism; it does not assert an orbifold atlas, isotropy
data, a manifold, or any `G₂` geometry.
-/

noncomputable section

namespace InfoGeometry.Topology.OrderThreeHomeomorphOrbitQuotient

variable {X : Type*} [TopologicalSpace X]

def orbitRelation (h : X ≃ₜ X) (x y : X) : Prop :=
  y = x ∨ y = h x ∨ y = h (h x)

theorem orbitRelation_equivalence
    (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x) :
    Equivalence (orbitRelation h) := by
  constructor
  · intro x
    exact Or.inl rfl
  · intro x y hxy
    rcases hxy with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by simpa using (hcube x).symm))
    · exact Or.inr (Or.inl (by simpa using (hcube x).symm))
  · intro x y z hxy hyz
    rcases hxy with rfl | rfl | rfl
    · exact hyz
    · rcases hyz with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl (by simpa using hcube x)
    · rcases hyz with rfl | rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl (by simpa using hcube x)
      · have hfour : h (h (h (h x))) = h x := by
          rw [hcube]
        exact Or.inr (Or.inl hfour)

def orbitSetoid (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x) : Setoid X where
  r := orbitRelation h
  iseqv := orbitRelation_equivalence h hcube

abbrev OrbitSpace (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x) :=
  Quotient (orbitSetoid h hcube)

def orbitProjection (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x) :
    X → OrbitSpace h hcube :=
  Quotient.mk' (s := orbitSetoid h hcube)

theorem continuous_orbitProjection (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x) :
    Continuous (orbitProjection h hcube) :=
  continuous_quotient_mk'

theorem orbitProjection_apply (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x) (x : X) :
    orbitProjection h hcube (h x) = orbitProjection h hcube x := by
  apply Quotient.sound (s := orbitSetoid h hcube)
  exact Or.inr (Or.inr (hcube x).symm)

theorem orbitProjection_apply_sq (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x) (x : X) :
    orbitProjection h hcube (h (h x)) = orbitProjection h hcube x := by
  rw [orbitProjection_apply]
  exact orbitProjection_apply h hcube x

theorem orbitProjection_eq_of_orbitRelation (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x) {x y : X}
    (hxy : orbitRelation h x y) :
    orbitProjection h hcube y = orbitProjection h hcube x := by
  rcases hxy with rfl | rfl | rfl
  · rfl
  · exact orbitProjection_apply h hcube x
  · exact orbitProjection_apply_sq h hcube x

theorem orbitProjection_eq_iff_orbitRelation (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x) {x y : X} :
    orbitProjection h hcube x = orbitProjection h hcube y ↔ orbitRelation h x y := by
  constructor
  · intro hxy
    exact Quotient.exact hxy
  · intro hxy
    exact (orbitProjection_eq_of_orbitRelation h hcube hxy).symm

end InfoGeometry.Topology.OrderThreeHomeomorphOrbitQuotient
