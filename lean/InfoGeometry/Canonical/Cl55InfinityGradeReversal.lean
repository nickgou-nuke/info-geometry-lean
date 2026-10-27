/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55WittOrthogonalReflections
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.Clifford.Cl55ChiralGrandCanonical
import InfoGeometry.Canonical.Cl55InfinityWittBoundary

/-!
# Native infinity/source/sink exchange reverses the fixed number grading

The existing quadratic-space reflection `(p,q) ↦ (p,-q)` lifts to the
existing Clifford algebra equivalence. It exchanges all five native CAR
pairs and sends the actual number operator to `5 - N`. The central constant
therefore cancels in the commutator, reversing the eigenspaces of the same
fixed `N`. This is a concrete source/sink exchange on native Clifford words.

The two normal ordered chiral occupations change sign, hence so does their
charge difference. No Pin membership or analytic modular-flow claim is used.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55InfinityGradeReversal

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open InfoGeometry.OperatorAlgebra

@[simp] theorem globalSheetReflection_nbar_pair (i : Fin 5) :
    globalSheetReflection (nbar_pair i) = n_pair i := by
  simp [globalSheetReflection, nbar_pair, n_pair, e_pos, f_neg]

@[simp] theorem globalSheetReflection_n_pair (i : Fin 5) :
    globalSheetReflection (n_pair i) = nbar_pair i := by
  simp [globalSheetReflection, nbar_pair, n_pair, e_pos, f_neg]

@[simp] theorem globalSheetReflectionAlg_involutive (X : Cl55) :
    globalSheetReflectionAlg (globalSheetReflectionAlg X) = X := by
  have h : globalSheetReflectionAlg.toAlgHom.comp globalSheetReflectionAlg.toAlgHom =
      AlgHom.id ℝ Cl55 := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change globalSheetReflectionAlg (globalSheetReflectionAlg (ι55 v)) = ι55 v
    rw [globalSheetReflectionAlg_apply_ι, globalSheetReflectionAlg_apply_ι,
      globalSheetReflection_involutive]
  exact DFunLike.congr_fun h X

@[simp] theorem globalSheetReflectionAlg_creation55 (i : Fin 5) :
    globalSheetReflectionAlg (creation55 i) = annihilation55 i := by
  simp only [creation55, map_smul, globalSheetReflectionAlg_apply_ι,
    globalSheetReflection_nbar_pair, annihilation55]

@[simp] theorem globalSheetReflectionAlg_annihilation55 (i : Fin 5) :
    globalSheetReflectionAlg (annihilation55 i) = creation55 i := by
  simp only [annihilation55, map_smul, globalSheetReflectionAlg_apply_ι,
    globalSheetReflection_n_pair, creation55]

theorem globalSheetReflectionAlg_occupation55 (i : Fin 5) :
    globalSheetReflectionAlg (creation55 i * annihilation55 i) =
      1 - creation55 i * annihilation55 i := by
  rw [map_mul, globalSheetReflectionAlg_creation55,
    globalSheetReflectionAlg_annihilation55]
  exact eq_sub_of_add_eq (annihilation55_creation55_anticommutator i)

theorem globalSheetReflectionAlg_numberOperator55 :
    globalSheetReflectionAlg numberOperator55 = 5 - numberOperator55 := by
  simp only [numberOperator55, map_sum, globalSheetReflectionAlg_occupation55,
    Finset.sum_sub_distrib]
  norm_num

/-- The same fixed grading element occurs on both sides. -/
theorem globalSheetReflectionAlg_number_commutator (X : Cl55) :
    globalSheetReflectionAlg (numberOperator55 * X - X * numberOperator55) =
      -(numberOperator55 * globalSheetReflectionAlg X -
        globalSheetReflectionAlg X * numberOperator55) := by
  rw [map_sub, map_mul, map_mul, globalSheetReflectionAlg_numberOperator55]
  noncomm_ring

theorem globalSheetReflectionAlg_grade_mem (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    globalSheetReflectionAlg X ∈ cl55GradeSubmodule (-k) := by
  change numberOperator55 * X - X * numberOperator55 = (k : ℝ) • X at hX
  change numberOperator55 * globalSheetReflectionAlg X -
      globalSheetReflectionAlg X * numberOperator55 =
    ((-k : ℤ) : ℝ) • globalSheetReflectionAlg X
  have hF := congrArg globalSheetReflectionAlg hX
  rw [globalSheetReflectionAlg_number_commutator, map_smul] at hF
  have hneg := congrArg Neg.neg hF
  simpa only [neg_neg, Int.cast_neg, neg_smul] using hneg

theorem globalSheetReflectionAlg_grade_mem_iff (k : ℤ) (X : Cl55) :
    globalSheetReflectionAlg X ∈ cl55GradeSubmodule (-k) ↔
      X ∈ cl55GradeSubmodule k := by
  constructor
  · intro hX
    simpa only [globalSheetReflectionAlg_involutive, neg_neg] using
      globalSheetReflectionAlg_grade_mem (-k) hX
  · exact globalSheetReflectionAlg_grade_mem k

theorem globalSheetReflectionAlg_gradeSubmodule_map (k : ℤ) :
    Submodule.map globalSheetReflectionAlg.toLinearMap (cl55GradeSubmodule k) =
      cl55GradeSubmodule (-k) := by
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact globalSheetReflectionAlg_grade_mem k hX
  · intro Y hY
    refine ⟨globalSheetReflectionAlg Y, ?_, ?_⟩
    · change globalSheetReflectionAlg Y ∈ cl55GradeSubmodule k
      simpa only [neg_neg] using globalSheetReflectionAlg_grade_mem (-k) hY
    · exact globalSheetReflectionAlg_involutive Y

@[simp] theorem globalSheetReflectionAlg_creation_pair (i : Fin 5) :
    globalSheetReflectionAlg (creation55 4 * creation55 i) =
      annihilation55 4 * annihilation55 i := by
  simp only [map_mul, globalSheetReflectionAlg_creation55]

@[simp] theorem globalSheetReflectionAlg_annihilation_pair (i : Fin 5) :
    globalSheetReflectionAlg (annihilation55 4 * annihilation55 i) =
      creation55 4 * creation55 i := by
  simp only [map_mul, globalSheetReflectionAlg_annihilation55]

@[simp] theorem globalSheetReflectionAlg_infinityClifford55 :
    globalSheetReflectionAlg infinityClifford55 = originClifford55 := by
  simpa only [creation55, annihilation55, infinityClifford55, originClifford55,
    infinityVector55, originVector55, n_bar_vec, n_vec, map_smul] using
    globalSheetReflectionAlg_creation55 4

@[simp] theorem globalSheetReflectionAlg_originClifford55 :
    globalSheetReflectionAlg originClifford55 = infinityClifford55 := by
  simpa only [creation55, annihilation55, infinityClifford55, originClifford55,
    infinityVector55, originVector55, n_bar_vec, n_vec, map_smul] using
    globalSheetReflectionAlg_annihilation55 4

@[simp] theorem globalSheetReflectionAlg_infinity_source_pair (i : Fin 5) :
    globalSheetReflectionAlg (infinityClifford55 * creation55 i) =
      originClifford55 * annihilation55 i := by
  simp only [map_mul, globalSheetReflectionAlg_infinityClifford55,
    globalSheetReflectionAlg_creation55]

@[simp] theorem globalSheetReflectionAlg_origin_sink_pair (i : Fin 5) :
    globalSheetReflectionAlg (originClifford55 * annihilation55 i) =
      infinityClifford55 * creation55 i := by
  simp only [map_mul, globalSheetReflectionAlg_originClifford55,
    globalSheetReflectionAlg_annihilation55]

@[simp] theorem globalSheetReflectionAlg_infinityProjector55 :
    globalSheetReflectionAlg infinityProjector55 = originProjector55 := by
  simp only [infinityProjector55, originProjector55, map_mul,
    globalSheetReflectionAlg_infinityClifford55, globalSheetReflectionAlg_originClifford55]

@[simp] theorem globalSheetReflectionAlg_originProjector55 :
    globalSheetReflectionAlg originProjector55 = infinityProjector55 := by
  simp only [infinityProjector55, originProjector55, map_mul,
    globalSheetReflectionAlg_infinityClifford55, globalSheetReflectionAlg_originClifford55]

@[simp] theorem globalSheetReflectionAlg_infinityGrading55 :
    globalSheetReflectionAlg infinityGrading55 = -infinityGrading55 := by
  simp only [infinityGrading55, map_sub, globalSheetReflectionAlg_infinityProjector55,
    globalSheetReflectionAlg_originProjector55]
  abel

@[simp] theorem globalSheetReflectionAlg_mixed_diagonal (i : Fin 5) :
    globalSheetReflectionAlg (mixedGenerator55 i i) = -mixedGenerator55 i i := by
  simp only [mixedGenerator55, ite_true, map_sub, map_smul, map_one,
    globalSheetReflectionAlg_occupation55]
  module

@[simp] theorem globalSheetReflectionAlg_chiralCharge55 :
    globalSheetReflectionAlg chiralCharge55 = -chiralCharge55 := by
  simp only [chiralCharge55, chiralPlusNumber55, chiralMinusNumber55,
    map_sub, globalSheetReflectionAlg_mixed_diagonal]
  abel

end InfoGeometry.Canonical.Cl55InfinityGradeReversal
