import InfoGeometry.Clifford.Cl55CARSpinAutomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure
import InfoGeometry.OperatorAlgebra.FiveGradeActionPreservation
import InfoGeometry.OperatorAlgebra.GradeActionInterface

/-!
# Operatorial five-grade routing on the native `Cl(5,5)` carrier

The carrier is the existing Clifford algebra `Cl55`.  The grading element is
the already-proved CAR number operator.  No second carrier and no realization
record are introduced here.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra

def cl55GradeSubmodule (k : ℤ) : Submodule ℝ Cl55 :=
  gradeSubmodule numberOperator55 k

def spinTransportedCl55GradeSubmodule (g : Spin55) (k : ℤ) :
    Submodule ℝ Cl55 :=
    gradeSubmodule (spinTransportedNumberOperator55 g) k

theorem spinTransported_grade_mem_of_mem
    (g : Spin55) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    spinCliffordRingEquiv g X ∈ spinTransportedCl55GradeSubmodule g k := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g X) k
  unfold HasOperatorGrade spinTransportedNumberOperator55 at *
  rw [← (spinCliffordRingEquiv g).map_mul,
    ← (spinCliffordRingEquiv g).map_mul,
    ← (spinCliffordRingEquiv g).map_sub, hX]
  simp

theorem spinTransported_maps_grade_family (g : Spin55) :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun k : ℤ => {X : Cl55 | X ∈ cl55GradeSubmodule k})
      (fun k : ℤ => {X : Cl55 | X ∈ spinTransportedCl55GradeSubmodule g k})
      (fun _ : Unit => fun X => spinCliffordRingEquiv g X)
      (fun _ : Unit => fun k => k) := by
  let hsmul : ∀ r : ℝ, ∀ X : Cl55,
      spinCliffordRingEquiv g (r • X) = r • spinCliffordRingEquiv g X := by
    intro r X
    change InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
        (spinGroup.toUnits g) (r • X) =
      r • InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
        (spinGroup.toUnits g) X
    exact InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul
      (spinGroup.toUnits g) r X
  simpa [spinTransportedNumberOperator55, spinTransportedCl55GradeSubmodule] using
    (InfoGeometry.OperatorAlgebra.ringEquiv_mapsToGradeSubmoduleBetween
      (spinCliffordRingEquiv g) numberOperator55 hsmul)

theorem spinTransported_grade_mem_iff
    (g : Spin55) (k : ℤ) (X : Cl55) :
    spinCliffordRingEquiv g X ∈ spinTransportedCl55GradeSubmodule g k ↔
      X ∈ cl55GradeSubmodule k := by
  let hsmul : ∀ r : ℝ, ∀ Y : Cl55,
      spinCliffordRingEquiv g (r • Y) = r • spinCliffordRingEquiv g Y := by
    intro r Y
    change InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
        (spinGroup.toUnits g) (r • Y) =
      r • InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
        (spinGroup.toUnits g) Y
    exact InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul
      (spinGroup.toUnits g) r Y
  simpa [spinTransportedNumberOperator55, spinTransportedCl55GradeSubmodule,
    cl55GradeSubmodule] using
    InfoGeometry.OperatorAlgebra.ringEquiv_map_gradeSubmodule_transport
      (spinCliffordRingEquiv g) numberOperator55 k hsmul X

theorem spinTransported_gradeSubmodule_map
    (g : Spin55) (k : ℤ) :
    Submodule.map
        (InfoGeometry.OperatorAlgebra.ringEquivLinearEquiv
          (spinCliffordRingEquiv g) (by
            intro r X
            change InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
                (spinGroup.toUnits g) (r • X) =
              r • InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
                (spinGroup.toUnits g) X
            exact InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul
              (spinGroup.toUnits g) r X)).toLinearMap
        (cl55GradeSubmodule k) = spinTransportedCl55GradeSubmodule g k := by
  apply InfoGeometry.OperatorAlgebra.ringEquivLinearEquiv_map_gradeSubmodule

/- The submodule equality above is the native Mathlib image statement in
   set form.  Keeping this readout explicit lets the generic grade-action
   interface consume the same Spin transport without introducing a second
   grade carrier. -/
theorem spinTransported_grade_image
    (g : Spin55) (k : ℤ) :
    (InfoGeometry.OperatorAlgebra.ringEquivLinearEquiv
      (spinCliffordRingEquiv g) (by
        intro r X
        change InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
            (spinGroup.toUnits g) (r • X) =
          r • InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
            (spinGroup.toUnits g) X
        exact InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul
          (spinGroup.toUnits g) r X)).toLinearMap ''
      (cl55GradeSubmodule k : Set Cl55) =
      (spinTransportedCl55GradeSubmodule g k : Set Cl55) := by
  rw [← Submodule.map_coe]
  exact congrArg (fun P : Submodule ℝ Cl55 => (P : Set Cl55))
    (spinTransported_gradeSubmodule_map g k)

theorem spinTransported_grade_mul_mem_of_mem
    (g : Spin55) (k l : ℤ) {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    spinCliffordRingEquiv g (X * Y) ∈
      spinTransportedCl55GradeSubmodule g (k + l) := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g (X * Y)) (k + l)
  rw [(spinCliffordRingEquiv g).map_mul]
  exact grade_mul
    (spinTransported_grade_mem_of_mem g k hX)
    (spinTransported_grade_mem_of_mem g l hY)

theorem spinTransported_grade_commutator_mem_of_mem
    (g : Spin55) (k l : ℤ) {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    spinCliffordRingEquiv g (X * Y - Y * X) ∈
      spinTransportedCl55GradeSubmodule g (k + l) := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g (X * Y - Y * X)) (k + l)
  rw [(spinCliffordRingEquiv g).map_sub,
    (spinCliffordRingEquiv g).map_mul,
    (spinCliffordRingEquiv g).map_mul]
  exact grade_commutator
    (spinTransported_grade_mem_of_mem g k hX)
    (spinTransported_grade_mem_of_mem g l hY)

theorem spinTransported_bracket_left_mapsToGradeBetween
    (g : Spin55) {k : ℤ} {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun l : ℤ => (cl55GradeSubmodule l : Set Cl55))
      (fun l : ℤ =>
        (spinTransportedCl55GradeSubmodule g l : Set Cl55))
      (fun _ : Unit => fun Y =>
        spinCliffordRingEquiv g (X * Y - Y * X))
      (fun _ l => k + l) := by
  intro _ l Y hY
  simpa using spinTransported_grade_commutator_mem_of_mem g k l hX hY

theorem spinTransported_grade_anticommutator_mem_of_mem
    (g : Spin55) (k l : ℤ) {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    spinCliffordRingEquiv g (X * Y + Y * X) ∈
      spinTransportedCl55GradeSubmodule g (k + l) := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g (X * Y + Y * X)) (k + l)
  rw [(spinCliffordRingEquiv g).map_add,
    (spinCliffordRingEquiv g).map_mul,
    (spinCliffordRingEquiv g).map_mul]
  exact grade_anticommutator
    (spinTransported_grade_mem_of_mem g k hX)
    (spinTransported_grade_mem_of_mem g l hY)

theorem creation55_mem_grade_one (i : Fin 5) :
    creation55 i ∈ cl55GradeSubmodule 1 := by
  change HasOperatorGrade numberOperator55 (creation55 i) 1
  simpa [HasOperatorGrade] using numberOperator55_commutator_creation i

theorem annihilation55_mem_grade_neg_one (i : Fin 5) :
    annihilation55 i ∈ cl55GradeSubmodule (-1) := by
  change HasOperatorGrade numberOperator55 (annihilation55 i) (-1)
  simpa [HasOperatorGrade] using numberOperator55_commutator_annihilation i

theorem spinTransported_creation55_mem_grade_one (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (creation55 i) ∈
      spinTransportedCl55GradeSubmodule g 1 := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g (creation55 i)) 1
  simpa [HasOperatorGrade] using
    spinTransportedNumberOperator55_commutator_creation g i

theorem spinTransported_annihilation55_mem_grade_neg_one
    (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (annihilation55 i) ∈
      spinTransportedCl55GradeSubmodule g (-1) := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g (annihilation55 i)) (-1)
  simpa [HasOperatorGrade] using
    spinTransportedNumberOperator55_commutator_annihilation g i

theorem spinTransported_creation55_mul_creation55_mem_grade_two
    (g : Spin55) (i j : Fin 5) :
    spinCliffordRingEquiv g (creation55 i * creation55 j) ∈
      spinTransportedCl55GradeSubmodule g 2 := by
  have hi : creation55 i ∈ cl55GradeSubmodule 1 := creation55_mem_grade_one i
  have hj : creation55 j ∈ cl55GradeSubmodule 1 := creation55_mem_grade_one j
  exact spinTransported_grade_mul_mem_of_mem g 1 1 hi hj

theorem spinTransported_annihilation55_mul_annihilation55_mem_grade_neg_two
    (g : Spin55) (i j : Fin 5) :
    spinCliffordRingEquiv g (annihilation55 i * annihilation55 j) ∈
      spinTransportedCl55GradeSubmodule g (-2) := by
  have hi : annihilation55 i ∈ cl55GradeSubmodule (-1) :=
    annihilation55_mem_grade_neg_one i
  have hj : annihilation55 j ∈ cl55GradeSubmodule (-1) :=
    annihilation55_mem_grade_neg_one j
  have h := spinTransported_grade_mul_mem_of_mem
    g (-1 : ℤ) (-1 : ℤ) hi hj
  convert h using 1 <;> norm_num

theorem spinTransported_creation55_mul_annihilation55_mem_grade_zero
    (g : Spin55) (i j : Fin 5) :
    spinCliffordRingEquiv g (creation55 i * annihilation55 j) ∈
      spinTransportedCl55GradeSubmodule g 0 := by
  have hi : creation55 i ∈ cl55GradeSubmodule 1 := creation55_mem_grade_one i
  have hj : annihilation55 j ∈ cl55GradeSubmodule (-1) :=
    annihilation55_mem_grade_neg_one j
  have h := spinTransported_grade_mul_mem_of_mem
    g (1 : ℤ) (-1 : ℤ) hi hj
  convert h using 1 <;> norm_num

theorem creation55_mul_creation55_mem_grade_two (i j : Fin 5) :
    creation55 i * creation55 j ∈ cl55GradeSubmodule 2 := by
  exact grade_mul (creation55_mem_grade_one i)
    (creation55_mem_grade_one j)

theorem annihilation55_mul_annihilation55_mem_grade_neg_two (i j : Fin 5) :
    annihilation55 i * annihilation55 j ∈ cl55GradeSubmodule (-2) := by
  exact grade_mul (annihilation55_mem_grade_neg_one i)
    (annihilation55_mem_grade_neg_one j)

theorem creation55_mul_annihilation55_mem_grade_zero (i j : Fin 5) :
    creation55 i * annihilation55 j ∈ cl55GradeSubmodule 0 := by
  exact grade_mul (creation55_mem_grade_one i)
    (annihilation55_mem_grade_neg_one j)

theorem annihilation55_mul_creation55_mem_grade_zero (i j : Fin 5) :
    annihilation55 i * creation55 j ∈ cl55GradeSubmodule 0 := by
  exact grade_mul (annihilation55_mem_grade_neg_one i)
    (creation55_mem_grade_one j)

theorem cl55_pos_one_pos_one_commutator_mem_grade_two
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule 1)
    (hY : Y ∈ cl55GradeSubmodule 1) :
    X * Y - Y * X ∈ cl55GradeSubmodule 2 := by
  exact grade_commutator hX hY

theorem cl55_neg_one_neg_one_commutator_mem_grade_neg_two
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule (-1))
    (hY : Y ∈ cl55GradeSubmodule (-1)) :
    X * Y - Y * X ∈ cl55GradeSubmodule (-2) := by
  exact grade_commutator hX hY

theorem cl55_mixed_commutator_mem_grade_zero
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule 1)
    (hY : Y ∈ cl55GradeSubmodule (-1)) :
    X * Y - Y * X ∈ cl55GradeSubmodule 0 := by
  exact grade_commutator hX hY

theorem cl55_same_grade_anticommutator_mem_grade_two
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule 1)
    (hY : Y ∈ cl55GradeSubmodule 1) :
    X * Y + Y * X ∈ cl55GradeSubmodule 2 := by
  exact grade_anticommutator hX hY

theorem cl55_mixed_anticommutator_mem_grade_zero
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule 1)
    (hY : Y ∈ cl55GradeSubmodule (-1)) :
    X * Y + Y * X ∈ cl55GradeSubmodule 0 := by
  exact grade_anticommutator hX hY

def cl55Associator (X Y Z : Cl55) : Cl55 :=
  (X * Y) * Z - X * (Y * Z)

theorem cl55_associator_zero (X Y Z : Cl55) :
    cl55Associator X Y Z = 0 := by
  simp [cl55Associator, mul_assoc]

end InfoGeometry.Clifford.Clifford55
