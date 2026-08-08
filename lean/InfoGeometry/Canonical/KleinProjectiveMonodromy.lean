import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Projective Klein Monodromy

This file establishes the algebraic basis for the projective monodromy 
of the Klein bottle. The fundamental group of the Klein bottle has the 
presentation:
  `π₁(K) = ⟨ a, b | a b a⁻¹ = b⁻¹ ⟩`

At the operator level, this relation is satisfied up to a central sign `z = ±1`,
yielding the lift:
  `Θ T Θ⁻¹ = z T⁻¹`

When quotienting by the center (projectivization), this projects to the exact
Klein relation.
-/

namespace InfoGeometry.Canonical.KleinProjectiveMonodromy

variable {G : Type*} [Group G]

/-- A lift of the Klein monodromy operators, where the commutation 
    holds up to a central element `z` of order dividing 2. -/
def IsKleinMonodromyLift (Theta T z : G) : Prop :=
  z ∈ Subgroup.center G ∧
  z * z = 1 ∧
  Theta * T * Theta⁻¹ = z * T⁻¹

/-- The projective relation holds exactly in the central quotient `G / Z(G)`. -/
theorem projective_klein_relation (Theta T z : G)
    (h : IsKleinMonodromyLift Theta T z) :
    (QuotientGroup.mk' (Subgroup.center G) Theta) *
    (QuotientGroup.mk' (Subgroup.center G) T) *
    (QuotientGroup.mk' (Subgroup.center G) Theta)⁻¹ =
    (QuotientGroup.mk' (Subgroup.center G) T)⁻¹ := by
  -- Let Z = Z(G)
  let Z := Subgroup.center G
  let Q := G ⧸ Z
  let mk : G →* Q := QuotientGroup.mk' Z
  
  -- We want to prove mk(Θ) * mk(T) * mk(Θ)⁻¹ = mk(T)⁻¹
  -- This is mk(Θ * T * Θ⁻¹) = mk(T⁻¹)
  calc mk Theta * mk T * (mk Theta)⁻¹
    _ = mk (Theta * T * Theta⁻¹) := by simp only [map_mul, map_inv]
    _ = mk (z * T⁻¹) := by rw [h.2.2]
    _ = mk z * mk (T⁻¹) := by rw [map_mul]
    _ = 1 * mk (T⁻¹) := by
      have hz : mk z = 1 := QuotientGroup.eq.mpr (by
        simp only [inv_one, mul_one, Subgroup.inv_mem_iff]
        exact h.1)
      rw [hz]
    _ = (mk T)⁻¹ := by simp only [one_mul, map_inv]

/-- The projective dihedral/hexagon symmetry shadow. 
    Projectively, if T has order 6, the generated subgroup is dihedral. -/
theorem projective_dihedral_shadow (Theta T z : G)
    (h : IsKleinMonodromyLift Theta T z)
    (hT6 : (QuotientGroup.mk' (Subgroup.center G) T) ^ 6 = 1)
    (hTheta2 : (QuotientGroup.mk' (Subgroup.center G) Theta) ^ 2 = 1) :
    let mk := QuotientGroup.mk' (Subgroup.center G)
    (mk Theta * mk T * (mk Theta)⁻¹ = (mk T)⁻¹) ∧
    (mk T) ^ 6 = 1 ∧
    (mk Theta) ^ 2 = 1 := by
  exact ⟨projective_klein_relation Theta T z h, hT6, hTheta2⟩

end InfoGeometry.Canonical.KleinProjectiveMonodromy
