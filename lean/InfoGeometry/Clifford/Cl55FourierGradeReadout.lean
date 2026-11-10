/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.FiveGradeActionPreservation

/-!
# Cl(5,5) CAR and Number-Grade Readouts

BUCKET 1 — Native carrier: the existing Clifford algebra `Cl55` and its
number-operator grade submodules.
BUCKET 2 — Compatibility readouts: explicit creation, annihilation, and
bracket grade statements exported from the five-grade owner.
BUCKET 3 — CAR/current bridge: the centered mixed creation-annihilation
generator has grade zero and its adjoint commutator preserves every grade.

`Cl55` is the fixed finite-rank head-stage Clifford algebra. These CAR and
grade statements are head-stage results; the direct-limit action law is proved
separately on `SplitCliffordInfinity` and `FockInfinity`.
-/
namespace InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra

/-- The creation and annihilation modes occupy grades `+1` and `-1`; their
same-type quadratic words occupy grades `+2` and `-2`. -/
theorem fourierClifford_grade_readout (i j : Fin 5) :
    creation55 i ∈ cl55GradeSubmodule 1 ∧
    annihilation55 i ∈ cl55GradeSubmodule (-1) ∧
    creation55 i * creation55 j ∈ cl55GradeSubmodule 2 ∧
    annihilation55 i * annihilation55 j ∈ cl55GradeSubmodule (-2) ∧
    creation55 i * creation55 j + creation55 j * creation55 i = 0 ∧
    annihilation55 i * annihilation55 j + annihilation55 j * annihilation55 i = 0 := by
  have hci : creation55 i ∈ cl55GradeSubmodule 1 := by
    change HasOperatorGrade numberOperator55 (creation55 i) 1
    simpa [HasOperatorGrade] using numberOperator55_commutator_creation i
  have hcj : creation55 j ∈ cl55GradeSubmodule 1 := by
    change HasOperatorGrade numberOperator55 (creation55 j) 1
    simpa [HasOperatorGrade] using numberOperator55_commutator_creation j
  have hai : annihilation55 i ∈ cl55GradeSubmodule (-1) := by
    change HasOperatorGrade numberOperator55 (annihilation55 i) (-1)
    simpa [HasOperatorGrade] using numberOperator55_commutator_annihilation i
  have haj : annihilation55 j ∈ cl55GradeSubmodule (-1) := by
    change HasOperatorGrade numberOperator55 (annihilation55 j) (-1)
    simpa [HasOperatorGrade] using numberOperator55_commutator_annihilation j
  refine ⟨hci, hai, ?_, ?_, ?_, ?_⟩
  · exact grade_mul hci hcj
  · have h := grade_mul hai haj
    change HasOperatorGrade numberOperator55
      (annihilation55 i * annihilation55 j) (-2)
    simpa using h
  · exact creation55_anticommutator i j
  · exact annihilation55_anticommutator i j

/-- Mixed creation-annihilation words lie in the number-grade-zero subspace. -/
theorem fourierClifford_grade_zero_readout (i j : Fin 5) :
    creation55 i * annihilation55 j ∈ cl55GradeSubmodule 0 ∧
    annihilation55 i * creation55 j ∈ cl55GradeSubmodule 0 ∧
    annihilation55 i * creation55 j + creation55 j * annihilation55 i =
      if i = j then 1 else 0 := by
  have hci : creation55 i ∈ cl55GradeSubmodule 1 :=
    creation55_mem_grade_one i
  have hci' : creation55 j ∈ cl55GradeSubmodule 1 :=
    creation55_mem_grade_one j
  have hai : annihilation55 i ∈ cl55GradeSubmodule (-1) :=
    annihilation55_mem_grade_neg_one i
  have haj : annihilation55 j ∈ cl55GradeSubmodule (-1) :=
    annihilation55_mem_grade_neg_one j
  refine ⟨?_, ?_, ?_⟩
  · have h := grade_mul hci haj
    change HasOperatorGrade numberOperator55
      (creation55 i * annihilation55 j) 0
    simpa using h
  · have h := grade_mul hai hci'
    change HasOperatorGrade numberOperator55
      (annihilation55 i * creation55 j) 0
    simpa using h
  · exact annihilation55_creation55_anticommutator_eq i j

/-- The Lie bracket adds number grades. -/
theorem fourierClifford_commutator_grade_add (k l : ℤ)
    {X Y : Cl55} (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    X * Y - Y * X ∈ cl55GradeSubmodule (k + l) := by
  change HasOperatorGrade numberOperator55 X k at hX
  change HasOperatorGrade numberOperator55 Y l at hY
  have hXY := grade_mul hX hY
  have hYX := grade_mul hY hX
  have hYX' : HasOperatorGrade numberOperator55 (Y * X) (k + l) := by
    simpa [add_comm] using hYX
  exact grade_sub hXY hYX'

/-- The Jordan bracket adds number grades. -/
theorem fourierClifford_anticommutator_grade_add (k l : ℤ)
    {X Y : Cl55} (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    X * Y + Y * X ∈ cl55GradeSubmodule (k + l) := by
  change HasOperatorGrade numberOperator55 X k at hX
  change HasOperatorGrade numberOperator55 Y l at hY
  have hXY := grade_mul hX hY
  have hYX := grade_mul hY hX
  have hYX' : HasOperatorGrade numberOperator55 (Y * X) (k + l) := by
    simpa [add_comm] using hYX
  exact grade_add hXY hYX'

/-- The CAR matrix-unit current has number-adjoint grade zero. Its two factors
have opposite grades, and the diagonal CAR correction is a scalar multiple
of the identity, which also has grade zero. -/
theorem mixedGenerator55_mem_grade_zero (i j : Fin 5) :
    mixedGenerator55 i j ∈ cl55GradeSubmodule 0 := by
  change HasOperatorGrade numberOperator55 (mixedGenerator55 i j) 0
  unfold mixedGenerator55
  have hcreation : HasOperatorGrade numberOperator55 (creation55 i) 1 :=
    creation55_mem_grade_one i
  have hannihilation : HasOperatorGrade numberOperator55 (annihilation55 j) (-1) :=
    annihilation55_mem_grade_neg_one j
  have hproduct := grade_mul hcreation hannihilation
  have hcorrection : HasOperatorGrade numberOperator55
      ((if i = j then (1 / 2 : ℝ) • (1 : Cl55) else 0)) 0 := by
    by_cases hij : i = j
    · simpa [hij] using grade_smul (1 / 2 : ℝ) (by
        unfold HasOperatorGrade
        simp)
    · simp [hij, HasOperatorGrade]
  have hcurrent := grade_sub hproduct hcorrection
  simpa using hcurrent

/-- Commutation by a mixed CAR current preserves every number-adjoint grade.
This specializes the general degree-zero commutator law to the actual
noncommutative `Cl(5,5)` creation-annihilation operators. -/
theorem mixedGenerator55_commutator_preserves_grade
    (i j : Fin 5) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    mixedGenerator55 i j * X - X * mixedGenerator55 i j ∈
      cl55GradeSubmodule k := by
  change HasOperatorGrade numberOperator55 X k at hX
  have hcurrent := mixedGenerator55_mem_grade_zero i j
  change HasOperatorGrade numberOperator55 (mixedGenerator55 i j) 0 at hcurrent
  have hleft := grade_mul hcurrent hX
  have hright := grade_mul hX hcurrent
  have hleft' : HasOperatorGrade numberOperator55 (mixedGenerator55 i j * X) k := by
    simpa using hleft
  have hright' : HasOperatorGrade numberOperator55 (X * mixedGenerator55 i j) k := by
    simpa using hright
  exact grade_sub hleft' hright'

end InfoGeometry.Clifford.Clifford55
