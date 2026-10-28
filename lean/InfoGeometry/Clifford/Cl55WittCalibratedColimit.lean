/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55WittCalibratedRepresentation
import InfoGeometry.Canonical.Cl11TensorInductiveLimit
import InfoGeometry.Canonical.CliffordCARGeneratorTopological
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Canonical.Cl55InfinityChiralCharge
import InfoGeometry.Canonical.Cl55InfinityGradeReversal

/-!
# Calibrated native Clifford operators in the existing tensor colimit

The native five-mode algebra maps faithfully into the owner's actual
noncommutative `Cl(1,1)` tensor direct limit. The map preserves the named CAR
generators, source/sink words and their number/chiral commutators. Its finite
representatives satisfy the existing universal lift and bonding equations.
The coherent BitWord equivalence supplies the same representation in the
algebraic UHF carrier. Projective infinity is a finite distinguished operator;
it is not identified with the diagonal cylinder boundary or a completion.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55WittCalibratedColimit

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl55WittCalibratedRepresentation
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Canonical.CliffordCARGeneratorTopological
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
open InfoGeometry.Canonical.Cl55InfinityChiralCharge
open InfoGeometry.Canonical.Cl55InfinityGradeReversal
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.OperatorAlgebra

/-- Composition with the canonical algebra map of the genuine stage-five colimit. -/
def cl55WittColimit : Cl55 →ₐ[ℝ] Limit :=
  (InfoGeometry.Canonical.Cl11TensorInductiveLimit.ofStageAlgHom 5).comp
    cl55WittAlgEquiv.toAlgHom

@[simp] theorem cl55WittColimit_apply (X : Cl55) :
    cl55WittColimit X = ofStage 5 (cl55WittRepresentation X) := rfl

theorem cl55WittColimit_injective : Function.Injective cl55WittColimit := by
  have hstage : Function.Injective (ofStage 5) := by
    apply directLimitOf_injective stageBond
    intro n
    change Function.Injective (matStageEmbed n)
    exact matStageEmbed_injective n
  exact hstage.comp cl55WittRepresentation_injective

/-- Every later finite representative determines exactly the same colimit element. -/
theorem cl55WittColimit_bondMap (n : ℕ) (hn : 5 ≤ n) (X : Cl55) :
    ofStage n (bondMap stageBond 5 n hn (cl55WittRepresentation X)) =
      cl55WittColimit X :=
  directLimitOf_bondMap stageBond 5 n hn (cl55WittRepresentation X)

/-- The native image participates in the existing universal property. -/
theorem cl55WittColimit_lift {A : Type} [Semiring A]
    (φ : ∀ n : ℕ, Stage n →+* A) (hφ : CompatibleCone stageBond φ) (X : Cl55) :
    directLimitLift stageBond φ hφ (cl55WittColimit X) =
      φ 5 (cl55WittRepresentation X) :=
  directLimitLift_of stageBond φ hφ 5 (cl55WittRepresentation X)

@[simp] theorem cl55WittColimit_creation55 (i : Fin 5) :
    cl55WittColimit (creation55 i) = algebraicCreationElement 5 i := by
  simp [algebraicCreationElement, InfoGeometry.Canonical.Cl55WittCAR.creation]

@[simp] theorem cl55WittColimit_annihilation55 (i : Fin 5) :
    cl55WittColimit (annihilation55 i) = algebraicAnnihilationElement 5 i := by
  simp [algebraicAnnihilationElement, InfoGeometry.Canonical.Cl55WittCAR.annihilation]

@[simp] theorem cl55WittColimit_infinity :
    cl55WittColimit infinityClifford55 = algebraicCreationElement 5 4 := by
  rw [infinityClifford55_eq_creation55, cl55WittColimit_creation55]

@[simp] theorem cl55WittColimit_origin :
    cl55WittColimit originClifford55 = algebraicAnnihilationElement 5 4 := by
  rw [originClifford55_eq_annihilation55, cl55WittColimit_annihilation55]

@[simp] theorem cl55WittColimit_sourcePair (i : Fin 5) :
    cl55WittColimit (sourcePair55 i) =
      algebraicCreationElement 5 4 * algebraicCreationElement 5 i := by
  simp only [sourcePair55, map_mul, cl55WittColimit_infinity,
    cl55WittColimit_creation55]

@[simp] theorem cl55WittColimit_sinkPair (i : Fin 5) :
    cl55WittColimit (sinkPair55 i) =
      algebraicAnnihilationElement 5 4 * algebraicAnnihilationElement 5 i := by
  simp only [sinkPair55, map_mul, cl55WittColimit_origin,
    cl55WittColimit_annihilation55]

theorem cl55WittColimit_chiralCharge :
    cl55WittColimit chiralCharge55 = ofStage 5 (E 0 0 - E 1 1) := by
  rw [cl55WittColimit_apply]
  simp [chiralCharge55, chiralPlusNumber55, chiralMinusNumber55]

theorem cl55WittColimit_grade_iff (N X : Cl55) (k : ℤ) :
    HasOperatorGrade (cl55WittColimit N) (cl55WittColimit X) k ↔
      HasOperatorGrade N X k := by
  unfold HasOperatorGrade
  constructor
  · intro h
    apply cl55WittColimit_injective
    simpa only [map_sub, map_mul, map_smul] using h
  · intro h
    simpa only [map_sub, map_mul, map_smul] using congrArg cl55WittColimit h

/-- Native number commutators use the fixed, centered matrix grader in the limit. -/
theorem cl55WittColimit_number_commutator (X : Cl55) :
    cl55WittColimit (numberOperator55 * X - X * numberOperator55) =
      ofStage 5 numberOperator * cl55WittColimit X -
        cl55WittColimit X * ofStage 5 numberOperator := by
  rw [cl55WittColimit_apply, cl55WittRepresentation_number_commutator]
  simp only [map_sub, map_mul, cl55WittColimit_apply]

theorem cl55WittColimit_number_grade_iff (X : Cl55) (k : ℤ) :
    HasOperatorGrade (ofStage 5 numberOperator) (cl55WittColimit X) k ↔
      X ∈ cl55GradeSubmodule k := by
  change HasOperatorGrade _ _ _ ↔ HasOperatorGrade numberOperator55 X k
  unfold HasOperatorGrade
  constructor
  · intro h
    apply cl55WittColimit_injective
    simpa only [cl55WittColimit_number_commutator, map_smul] using h
  · intro h
    simpa only [cl55WittColimit_number_commutator, map_smul] using
      congrArg cl55WittColimit h

theorem cl55WittColimit_source_grade (i : Fin 5) :
    HasOperatorGrade (ofStage 5 numberOperator) (cl55WittColimit (sourcePair55 i)) 2 :=
  (cl55WittColimit_number_grade_iff _ _).2 (sourcePair55_mem_grade_two i)

theorem cl55WittColimit_sink_grade (i : Fin 5) :
    HasOperatorGrade (ofStage 5 numberOperator) (cl55WittColimit (sinkPair55 i)) (-2) :=
  (cl55WittColimit_number_grade_iff _ _).2 (sinkPair55_mem_grade_neg_two i)

theorem cl55WittColimit_source_charge (i : Fin 5) :
    HasOperatorGrade (cl55WittColimit chiralCharge55)
      (cl55WittColimit (sourcePair55 i)) (chiralModeWeight55 i) :=
  (cl55WittColimit_grade_iff _ _ _).2 (sourcePair55_has_chiralCharge_grade i)

theorem cl55WittColimit_sink_charge (i : Fin 5) :
    HasOperatorGrade (cl55WittColimit chiralCharge55)
      (cl55WittColimit (sinkPair55 i)) (-chiralModeWeight55 i) :=
  (cl55WittColimit_grade_iff _ _ _).2 (sinkPair55_has_chiralCharge_grade i)

theorem cl55WittColimit_source_ne_zero (i : Fin 5) (hi : i ≠ 4) :
    cl55WittColimit (sourcePair55 i) ≠ 0 := by
  intro h
  apply sourcePair55_ne_zero i hi
  apply cl55WittColimit_injective
  simpa only [map_zero] using h

theorem cl55WittColimit_sink_ne_zero (i : Fin 5) (hi : i ≠ 4) :
    cl55WittColimit (sinkPair55 i) ≠ 0 := by
  intro h
  apply sinkPair55_ne_zero i hi
  apply cl55WittColimit_injective
  simpa only [map_zero] using h

theorem cl55WittColimit_reflection_source (i : Fin 5) :
    cl55WittColimit (globalSheetReflectionAlg (sourcePair55 i)) =
      cl55WittColimit (sinkPair55 i) := by
  exact congrArg cl55WittColimit (globalSheetReflectionAlg_infinity_source_pair i)

theorem cl55WittColimit_reflection_charge :
    cl55WittColimit (globalSheetReflectionAlg chiralCharge55) =
      -cl55WittColimit chiralCharge55 := by
  rw [globalSheetReflectionAlg_chiralCharge55, map_neg]

/-- The same faithful image in the existing coherent BitWord UHF colimit. -/
def cl55WittUHF : Cl55 →+* UHFCarrier :=
  cliffordBitWordColimitEquiv.toRingHom.comp cl55WittColimit.toRingHom

theorem cl55WittUHF_injective : Function.Injective cl55WittUHF :=
  cliffordBitWordColimitEquiv.injective.comp cl55WittColimit_injective

@[simp] theorem cl55WittUHF_stage (X : Cl55) :
    cl55WittUHF X = InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit 5
      (clStageEquiv 5 (cl55WittRepresentation X)) :=
  cliffordBitWordColimitEquiv_ofStage 5 (cl55WittRepresentation X)

@[simp] theorem cl55WittUHF_creation55 (i : Fin 5) :
    cl55WittUHF (creation55 i) = InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit 5
      (clStageEquiv 5 (InfoGeometry.Canonical.Cl55WittCAR.creation i)) := by simp

@[simp] theorem cl55WittUHF_annihilation55 (i : Fin 5) :
    cl55WittUHF (annihilation55 i) = InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit 5
      (clStageEquiv 5 (InfoGeometry.Canonical.Cl55WittCAR.annihilation i)) := by simp

end InfoGeometry.Clifford.Cl55WittCalibratedColimit
