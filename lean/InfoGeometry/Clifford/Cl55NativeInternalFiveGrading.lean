/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55WittCalibratedRepresentation
import InfoGeometry.Clifford.Cl55OperatorLieSubalgebra
import InfoGeometry.Canonical.Cl55WittInternalFiveGrading

/-!
# Native five-lane Lie decomposition through the calibrated CAR map

The source is the existing Lie span of the named native Clifford generators.
The calibrated representation identifies it with the actual matrix Lie span.
The matrix internal decomposition therefore yields existence and uniqueness
of five native homogeneous components and dimension 55. The scalar `5/2`
correction to the number operator cancels in its commutator.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace InfoGeometry.Clifford.Cl55NativeInternalFiveGrading

open scoped DirectSum BigOperators

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl55WittCalibratedRepresentation
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Canonical.Cl55WittFullLieClosure
open InfoGeometry.Canonical.Cl55WittInternalFiveGrading

theorem calibrated_image_generators :
    cl55WittRepresentation '' cl55LieGenerators = wittLieGenerators := by
  simp only [cl55LieGenerators, wittLieGenerators, Set.image_union, ← Set.range_comp,
    Function.comp_def, cl55WittRepresentation_creation55,
    cl55WittRepresentation_annihilation55]

/-- Equality of genuine Lie-generated subalgebras, derived by the universal
Lie-span map law and the proved generator calibration. -/
theorem calibrated_map_nativeLie :
    cl55LieGeneratedSubalgebra.map cl55WittRepresentation.toLieHom =
      wittGeneratorLieSpan := by
  rw [cl55LieGeneratedSubalgebra, LieSubalgebra.map_lieSpan]
  change LieSubalgebra.lieSpan ℝ (MatStage 5)
    (cl55WittRepresentation '' cl55LieGenerators) = _
  rw [calibrated_image_generators]
  rfl

def nativeWittLieEquiv : cl55LieGeneratedSubalgebra ≃ₗ⁅ℝ⁆ wittGeneratorLieSpan :=
  cl55WittAlgEquiv.toLieEquiv.ofSubalgebras _ _ calibrated_map_nativeLie

/-- Same equivalence with the established five-grade submodule as codomain. -/
def nativeWittFiveGradeEquiv : cl55LieGeneratedSubalgebra ≃ₗ[ℝ] wittFiveGrade :=
  nativeWittLieEquiv.toLinearEquiv ≪≫ₗ
    LinearEquiv.ofEq (wittGeneratorLieSpan : Submodule ℝ (MatStage 5)) wittFiveGrade
      generatorLieSpan_toSubmodule_eq_wittFiveGrade

theorem nativeLie_finrank : Module.finrank ℝ cl55LieGeneratedSubalgebra = 55 :=
  nativeWittFiveGradeEquiv.finrank_eq.trans wittFiveGrade_finrank

/-- The decomposition's inverse extracts unique homogeneous components of
an arbitrary element of the native generated Lie algebra. -/
def nativeWittFiveGradeDecomposition :
    (⨁ i : WittLane, internalLane i) ≃ₗ[ℝ] cl55LieGeneratedSubalgebra :=
  wittFiveGradeDecomposition ≪≫ₗ nativeWittFiveGradeEquiv.symm

/-- The named lanes are pulled back through a proved calibrated equivalence. -/
def nativeLane (i : WittLane) : Submodule ℝ Cl55 :=
  (laneSpace i).comap cl55WittRepresentation.toLinearMap

/-- The lanes are homogeneous for the original native number operator. -/
theorem nativeLane_le_grade (i : WittLane) :
    nativeLane i ≤ cl55GradeSubmodule i.degree := by
  intro X hX
  change numberOperator55 * X - X * numberOperator55 = (i.degree : ℝ) • X
  apply cl55WittRepresentation_injective
  rw [cl55WittRepresentation_number_commutator, map_smul]
  exact laneSpace_le_grade i hX

theorem calibrated_grade_iff (k : ℤ) (X : Cl55) :
    cl55WittRepresentation X ∈ gradeSubmodule k ↔ X ∈ cl55GradeSubmodule k := by
  change (numberOperator * cl55WittRepresentation X -
      cl55WittRepresentation X * numberOperator = (k : ℝ) • cl55WittRepresentation X) ↔
    (numberOperator55 * X - X * numberOperator55 = (k : ℝ) • X)
  rw [← cl55WittRepresentation_number_commutator, ← map_smul]
  exact cl55WittRepresentation_injective.eq_iff

@[simp] theorem nativeWittFiveGradeEquiv_apply (X : cl55LieGeneratedSubalgebra) :
    (nativeWittFiveGradeEquiv X : MatStage 5) = cl55WittRepresentation (X : Cl55) := rfl

/-- Each component extracted through the equivalence is homogeneous for the
original native commutator, not merely tagged with a matrix-side label. -/
theorem native_component_grade (i : WittLane) (X : internalLane i) :
    (nativeWittFiveGradeEquiv.symm X.1 : Cl55) ∈ cl55GradeSubmodule i.degree := by
  apply (calibrated_grade_iff _ _).mp
  have hrep : cl55WittRepresentation (nativeWittFiveGradeEquiv.symm X.1 : Cl55) =
      (X.1 : MatStage 5) := by
    rw [← nativeWittFiveGradeEquiv_apply, nativeWittFiveGradeEquiv.apply_symm_apply]
  rw [hrep]
  exact laneSpace_le_grade i X.2

end InfoGeometry.Clifford.Cl55NativeInternalFiveGrading
