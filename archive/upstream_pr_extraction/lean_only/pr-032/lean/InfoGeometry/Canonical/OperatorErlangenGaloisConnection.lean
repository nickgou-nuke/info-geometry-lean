import InfoGeometry.Canonical.OperatorErlangenFixedPoints

/-!
# Operator Erlangen Galois connection

The subgroup/fixed-observable correspondence is always a Galois connection.
It is not promoted here to a Galois anti-equivalence, which would require
additional descent hypotheses.
-/

namespace InfoGeometry.Canonical.OperatorErlangenFixedPoints

variable {G A : Type*} [Group G] [Semiring A] [MulSemiringAction G A]

/-- The subgroup fixing every observable in a set. -/
def fixingSubgroup (S : Set A) : Subgroup G where
  carrier := {g | ∀ a ∈ S, g • a = a}
  one_mem' := by
    intro a ha
    simp
  mul_mem' := by
    intro g h hg hh a ha
    rw [mul_smul, hh a ha, hg a ha]
  inv_mem' := by
    intro g hg a ha
    calc
      g⁻¹ • a = g⁻¹ • (g • a) := by rw [hg a ha]
      _ = (g⁻¹ * g) • a := by rw [mul_smul]
      _ = a := by simp

theorem mem_fixingSubgroup_iff (S : Set A) (g : G) :
    g ∈ fixingSubgroup S ↔ ∀ a ∈ S, g • a = a :=
  Iff.rfl

/-- The operator-Erlangen Galois connection between subgroups and observables. -/
theorem subgroup_le_fixingSubgroup_iff {H : Subgroup G} {S : Set A} :
    H ≤ fixingSubgroup (G := G) (A := A) S ↔
      S ⊆ fixedPointSet (G := G) (A := A) H := by
  constructor
  · intro h a ha g
    exact h g.property a ha
  · intro h g hg a ha
    exact h ha ⟨g, hg⟩

theorem fixingSubgroup_antitone {S T : Set A} (h : S ⊆ T) :
    fixingSubgroup (G := G) (A := A) T ≤
      fixingSubgroup (G := G) (A := A) S := by
  intro g hg a ha
  exact hg a (h ha)

end InfoGeometry.Canonical.OperatorErlangenFixedPoints
