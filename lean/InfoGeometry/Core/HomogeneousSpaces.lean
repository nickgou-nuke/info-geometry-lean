import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import InfoGeometry.Core.SymmetricSpaces

/-!
# Core homogeneous spaces

Owner-first quotient homogeneous-space package:
- canonical left `G`-action on `G ⧸ H` for any subgroup `H ≤ G`;
- basepoint `eH`;
- exact stabilizer of the basepoint;
- transitivity / homogeneous-space theorem;
- Cartan fixed-subgroup specialization `G / Fix(θ)`.
-/

namespace InfoGeometry.Core

section QuotientAction

variable {G : Type*} [Group G]

/-- The canonical basepoint `eH` in the left-coset quotient `G ⧸ H`. -/
def quotientBasepoint (H : Subgroup G) : G ⧸ H :=
  QuotientGroup.mk (1 : G)

/-- Left multiplication on `G ⧸ H`. -/
instance instMulActionQuotientLeftRel (H : Subgroup G) : MulAction G (G ⧸ H) where
  smul g :=
    Quotient.map (fun x : G => g * x) <| by
      intro a b hab
      apply QuotientGroup.leftRel_apply.mpr
      simpa [mul_assoc] using (show a⁻¹ * b ∈ H from
        QuotientGroup.leftRel_apply.mp hab)
  one_smul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    rfl
  mul_smul := by
    intro g h x
    refine Quotient.inductionOn x ?_
    intro a
    rfl

@[simp] theorem smul_mk (H : Subgroup G) (g x : G) :
    g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk (g * x) :=
  rfl

@[simp] theorem smul_basepoint (H : Subgroup G) (g : G) :
    g • quotientBasepoint H = (QuotientGroup.mk g : G ⧸ H) := by
  simp [quotientBasepoint, smul_mk]

/-- The stabilizer of the quotient basepoint is exactly `H`. -/
theorem stabilizer_quotientBasepoint_eq (H : Subgroup G) :
    MulAction.stabilizer G (quotientBasepoint H) = H := by
  ext g
  constructor
  · intro hg
    have hEq : (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk (1 : G) := by
      simpa [quotientBasepoint] using hg
    have hmem : g⁻¹ * (1 : G) ∈ H := QuotientGroup.eq.mp hEq
    simpa using H.inv_mem hmem
  · intro hg
    change g • quotientBasepoint H = quotientBasepoint H
    have hmem : (g * (1 : G))⁻¹ * (1 : G) ∈ H := by
      simpa using H.inv_mem hg
    simpa [quotientBasepoint, smul_mk, mul_assoc] using
      (QuotientGroup.eq.mpr hmem : (QuotientGroup.mk (g * (1 : G)) : G ⧸ H) = QuotientGroup.mk (1 : G))

/-- Minimal transitivity predicate for a group action. -/
def IsHomogeneousSpace (G X : Type*) [Group G] [MulAction G X] : Prop :=
  ∀ x y : X, ∃ g : G, g • x = y

/-- The left action of `G` on `G ⧸ H` is transitive. -/
theorem quotient_isHomogeneousSpace (H : Subgroup G) :
    IsHomogeneousSpace G (G ⧸ H) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro a y
  refine Quotient.inductionOn y ?_
  intro b
  exact ⟨b * a⁻¹, by simp [smul_mk, mul_assoc]⟩

/-- Every quotient class is reached from the basepoint by left translation. -/
theorem exists_smul_quotientBasepoint_eq (H : Subgroup G) (x : G ⧸ H) :
    ∃ g : G, g • quotientBasepoint H = x := by
  simpa [IsHomogeneousSpace] using
    (quotient_isHomogeneousSpace (G := G) H) (quotientBasepoint H) x

@[simp] theorem orbit_quotientBasepoint_univ (H : Subgroup G) :
    MulAction.orbit G (quotientBasepoint H) = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rcases exists_smul_quotientBasepoint_eq (G := G) H x with ⟨g, rfl⟩
    exact ⟨g, rfl⟩

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
