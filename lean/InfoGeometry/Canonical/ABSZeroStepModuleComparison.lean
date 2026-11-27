/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NegativeLineModuleClassification
import InfoGeometry.Canonical.GradedCliffordModuleSum
import InfoGeometry.Clifford.ABSZeroStepArithmetic

/-!
# Actual zero-step Clifford restriction and the arithmetic ABS cokernel

Starting with a represented graded module for the negative real line, this
module constructs its object under the existing categorical restriction
functor from `Cl(0,1)` to `Cl(0,0)`. The grade is the original grade. Dimensions
of its actual eigenspaces give the diagonal arithmetic restriction invariant,
compatibly with direct sums and the existing Grothendieck-group homomorphism.

The earlier standardization is a genuine Clifford-module isomorphism. The
comparison below identifies the invariant of every such actual restriction;
it does not replace a category or its isomorphism classes by numeric data.
The construction of a quotient of all finite module isomorphism classes and
its Grothendieck group is a separate statement from this objectwise comparison.
-/

noncomputable section

namespace InfoGeometry.Canonical.ABSZeroStepModuleComparison

open CliffordAlgebra
open PinOperatorFamilyBridge AtiyahBottShapiroSymbol
open NegativeLineModuleClassification GradedCliffordModuleSum
open InfoGeometry.Clifford.FreedCliffordSuspension
open InfoGeometry.Clifford.KahlerHestenesJWABSPrimary.AtiyahBottShapiroPrimary

abbrev ZeroVectorSpace := Fin 0 → ℝ

abbrev zeroQuadratic : QuadraticForm ℝ ZeroVectorSpace := 0

/-- The extension of the genuine zero-dimensional vector space is isometric
to the single negative real direction. -/
def zeroExtensionLineEquiv :
    (positiveForm zeroQuadratic).IsometryEquiv negativeQuadratic where
  toLinearEquiv :=
    { toFun := Prod.snd
      invFun := fun r => (0, r)
      left_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_app' p := by
    simp [positiveForm_apply, zeroQuadratic, negativeQuadratic_apply]

def zeroExtensionToLine : (positiveForm zeroQuadratic).Isometry negativeQuadratic :=
  zeroExtensionLineEquiv.toIsometry

variable {W : Type} [AddCommGroup W] [Module ℝ W]
variable (ρ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := ℝ) (W := W) (Q := negativeQuadratic))

/-- The same actual negative-line action, expressed on the domain of the
existing zero-step categorical restriction functor. -/
def zeroStepRepresentation : GradedCliffordOperatorRepresentation
    (R := ℝ) (M := ZeroVectorSpace × ℝ) (W := W)
    (Q := positiveForm zeroQuadratic) where
  representation := ρ.representation.comp (CliffordAlgebra.map zeroExtensionToLine)
  grading := ρ.grading
  grading_sq := ρ.grading_sq
  generator_odd p := by
    change ρ.grading * ρ.representation
        (CliffordAlgebra.map zeroExtensionToLine (ι (positiveForm zeroQuadratic) p)) +
      ρ.representation
        (CliffordAlgebra.map zeroExtensionToLine (ι (positiveForm zeroQuadratic) p)) *
        ρ.grading = 0
    rw [CliffordAlgebra.map_apply_ι]
    exact ρ.generator_odd (zeroExtensionToLine p)

/-- An actual object under the repository's Clifford restriction functor. -/
def zeroRestriction : absModuleCat zeroQuadratic :=
  (absRestrictionFunctor zeroQuadratic).obj (zeroStepRepresentation ρ).toGradedModule

/-- Restriction preserves the actual grading operator on the carrier. -/
@[simp] theorem zeroRestriction_grade (w : W) :
    (zeroRestriction ρ).grade w = ρ.grading w := rfl

/-- The old scalar action on the same carrier is recovered by categorical restriction. -/
theorem zeroRestriction_scalar_action (r : ℝ) (w : W) :
    letI : Module (CliffordAlgebra zeroQuadratic) W := (zeroRestriction ρ).V.isModule
    (algebraMap ℝ (CliffordAlgebra zeroQuadratic) r) • w = r • w := by
  letI : Module (CliffordAlgebra zeroQuadratic) W := (zeroRestriction ρ).V.isModule
  change (zeroStepRepresentation ρ).representation
    (absInclusion zeroQuadratic (algebraMap ℝ (CliffordAlgebra zeroQuadratic) r)) w = _
  rw [AlgHom.commutes, AlgHom.commutes]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The grade of the actual restricted object is real-linear. -/
def restrictedGrading : Module.End ℝ W where
  toFun := (zeroRestriction ρ).grade
  map_add' := (zeroRestriction ρ).grade.map_add
  map_smul' := ρ.grading.map_smul

@[simp] theorem restrictedGrading_eq : restrictedGrading ρ = ρ.grading := rfl

/-- Dimensions are taken from the actual eigenspaces of the restricted grade. -/
def restrictionSuperDimension [FiniteDimensional ℝ W] : ℕ × ℕ :=
  (Module.finrank ℝ ((restrictedGrading ρ).eigenspace (1 : ℝ)),
    Module.finrank ℝ ((restrictedGrading ρ).eigenspace (-1 : ℝ)))

/-- Actual module restriction induces precisely the existing diagonal monoid map. -/
theorem restrictionSuperDimension_eq_diagonal [FiniteDimensional ℝ W] :
    restrictionSuperDimension ρ =
      absZeroStepRestrictMonoid (Module.finrank ℝ (evenSpace ρ)) := by
  change (Module.finrank ℝ (evenSpace ρ), Module.finrank ℝ (oddSpace ρ)) =
    (Module.finrank ℝ (evenSpace ρ), Module.finrank ℝ (evenSpace ρ))
  rw [finrank_oddSpace_eq_evenSpace ρ (1 : ℝ) (by norm_num)]

/-- The comparison is additive on actual direct sums of Clifford representations. -/
theorem restrictionSuperDimension_directSum
    {V : Type} [AddCommGroup V] [Module ℝ V]
    (σ : GradedCliffordOperatorRepresentation
      (R := ℝ) (M := ℝ) (W := V) (Q := negativeQuadratic))
    [FiniteDimensional ℝ W] [FiniteDimensional ℝ V] :
    restrictionSuperDimension (directSum ρ σ) =
      restrictionSuperDimension ρ + restrictionSuperDimension σ := by
  change (Module.finrank ℝ (evenSpace (directSum ρ σ)),
      Module.finrank ℝ (oddSpace (directSum ρ σ))) = _
  rw [finrank_even_directSum, finrank_odd_directSum]
  rfl

/-- The actual restriction invariant maps into the existing Grothendieck group. -/
def restrictionClass [FiniteDimensional ℝ W] : Grothendieck (ℕ × ℕ) :=
  grothendieckMap (ℕ × ℕ) (restrictionSuperDimension ρ)

/-- The comparison commutes with the existing induced Grothendieck restriction map. -/
theorem restrictionClass_eq [FiniteDimensional ℝ W] :
    restrictionClass ρ = absZeroStepRestrictK0
      (grothendieckMap ℕ (Module.finrank ℝ (evenSpace ρ))) := by
  rw [restrictionClass, restrictionSuperDimension_eq_diagonal,
    absZeroStepRestrictK0, grothendieckFunctor_map]

/-- Every actual restricted negative-line module is zero in the arithmetic cokernel. -/
theorem restrictionClass_cokernel_zero [FiniteDimensional ℝ W] :
    (QuotientAddGroup.mk (restrictionClass ρ) :
      Grothendieck (ℕ × ℕ) ⧸ absZeroStepRestrictK0.range) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨grothendieckMap ℕ (Module.finrank ℝ (evenSpace ρ)),
    (restrictionClass_eq ρ).symm⟩

/-- Under the established arithmetic cokernel equivalence the actual restriction
has integer class zero. -/
theorem restrictionClass_integer_zero [FiniteDimensional ℝ W] :
    absCokernelZeroEquivInt (QuotientAddGroup.mk (restrictionClass ρ)) = 0 := by
  rw [restrictionClass_cokernel_zero, map_zero]

end InfoGeometry.Canonical.ABSZeroStepModuleComparison
