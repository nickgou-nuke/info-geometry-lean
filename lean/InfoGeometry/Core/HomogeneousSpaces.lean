import Mathlib.GroupTheory.GroupAction.Quotient
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Core.SymmetricSpaces

/-!
# Core homogeneous spaces

Owner-first quotient homogeneous-space package:
- basepoint `eH` in `G ⧸ H`;
- exact stabilizer of the basepoint;
- transitivity / homogeneous-space theorem for the canonical left action;
- Cartan fixed-subgroup specialization `G / Fix(θ)`.
-/

namespace InfoGeometry.Core

section QuotientAction

variable {G : Type*} [Group G]

/-- The canonical basepoint `eH` in the left-coset quotient `G ⧸ H`. -/
def quotientBasepoint (H : Subgroup G) : G ⧸ H :=
  QuotientGroup.mk (1 : G)

@[simp] theorem smul_mk (H : Subgroup G) (g x : G) :
    g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk (g * x) := by
  rfl

@[simp] theorem smul_basepoint (H : Subgroup G) (g : G) :
    g • quotientBasepoint H = (QuotientGroup.mk g : G ⧸ H) := by
  simp [quotientBasepoint]

/-- The stabilizer of the quotient basepoint is exactly `H`. -/
theorem stabilizer_quotientBasepoint_eq (H : Subgroup G) :
    MulAction.stabilizer G (quotientBasepoint H) = H := by
  simp [quotientBasepoint, MulAction.stabilizer_quotient]

/-- Minimal transitivity predicate for a group action. -/
def IsHomogeneousSpace (G X : Type*) [Group G] [MulAction G X] : Prop :=
  ∀ x y : X, ∃ g : G, g • x = y

/-- The canonical left action of `G` on `G ⧸ H` is transitive. -/
theorem quotient_isHomogeneousSpace (H : Subgroup G) :
    IsHomogeneousSpace G (G ⧸ H) := by
  intro x
  refine Quotient.inductionOn' x ?_
  intro a y
  refine Quotient.inductionOn' y ?_
  intro b
  refine ⟨b * a⁻¹, ?_⟩
  simp [mul_assoc]

/-- Every quotient class is reached from the basepoint by left translation. -/
theorem exists_smul_quotientBasepoint_eq (H : Subgroup G) (x : G ⧸ H) :
    ∃ g : G, g • quotientBasepoint H = x := by
  exact (quotient_isHomogeneousSpace (G := G) H) (quotientBasepoint H) x

@[simp] theorem orbit_quotientBasepoint_univ (H : Subgroup G) :
    MulAction.orbit G (quotientBasepoint H) = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rcases exists_smul_quotientBasepoint_eq (G := G) H x with ⟨g, hg⟩
    exact ⟨g, hg⟩

end QuotientAction

section CartanSpecialization

variable {G : Type*} [Group G]

/-- The quotient by the fixed subgroup of a Cartan involution is homogeneous. -/
theorem cartan_fixedQuotient_isHomogeneousSpace
    (θ : CartanInvolution G) :
    IsHomogeneousSpace G (G ⧸ θ.fixedSubgroup) :=
  quotient_isHomogeneousSpace (G := G) θ.fixedSubgroup

/-- The stabilizer of the Cartan quotient basepoint is exactly the fixed subgroup. -/
theorem stabilizer_cartan_fixedQuotientBasepoint_eq
    (θ : CartanInvolution G) :
    MulAction.stabilizer G (quotientBasepoint θ.fixedSubgroup) = θ.fixedSubgroup :=
  stabilizer_quotientBasepoint_eq (G := G) θ.fixedSubgroup

end CartanSpecialization

end InfoGeometry.Core
