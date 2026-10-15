import InfoGeometry.Orthogonal.O55WittNullFrame
import InfoGeometry.Orthogonal.O55ContactGrading
import InfoGeometry.Clifford.Cl55FockSupergradedRepresentation
import InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
import InfoGeometry.Clifford.Cl55ExteriorBivectorLieAction
import InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge

/-!
# Contact TKK action on the Cl(5,5) vacuum ideal

The contact Euler element of `O55Contact` is lifted to the native Clifford
bivector Lie algebra. Its action on the Witt frame is proved to intertwine
with `contactEulerEnd`; the induced adjoint eigenspaces therefore use the
contact/TKK grading, not the separate operator-number grading. The same
Cl(5,5) bivectors act by left multiplication on the actual vacuum ideal, and
that representation preserves commutators and the Euler grade equation. The
existing vacuum-ideal/spinor equivalence transports this action to the native
exterior spinor.

This module proves the Euler intertwining and grade-bracket law. It does not
claim a new Jordan-pair construction or identify the grading with the doubled
real Krein operators.
-/

noncomputable section
namespace InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Orthogonal.O55Contact
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
open InfoGeometry.Clifford.Cl55FockSupergradedRepresentation
open InfoGeometry.Clifford.Cl55ExteriorBivectorLieAction
open InfoGeometry.Clifford.BivectorVectorRepresentation
open CliffordAlgebra

abbrev CV := Vector55
abbrev SV := V55

def contactToSpinorVector (z : CV) : SV :=
  (fun i => wittPlusCoefficient z i + (1 / 2 : ℝ) * wittMinusCoefficient z i,
   fun i => wittPlusCoefficient z i - (1 / 2 : ℝ) * wittMinusCoefficient z i)

def spinorToContactVector (v : SV) : CV :=
  ![((v.1 0 + v.2 0) / 2 : ℝ), (v.1 1 + v.2 1) / 2,
    v.1 2, v.1 3, v.1 4, v.2 2, v.2 3, v.2 4,
    v.1 0 - v.2 0, v.1 1 - v.2 1]

def contactToSpinorLinear : CV →ₗ[ℝ] SV where
  toFun := contactToSpinorVector
  map_add' x y := by
    unfold contactToSpinorVector
    ext i <;> fin_cases i <;>
      simp [wittPlusCoefficient, wittMinusCoefficient] <;> ring
  map_smul' c x := by
    unfold contactToSpinorVector
    ext i <;> fin_cases i <;>
      simp [wittPlusCoefficient, wittMinusCoefficient] <;> ring

def spinorToContactLinear : SV →ₗ[ℝ] CV where
  toFun := spinorToContactVector
  map_add' x y := by
    ext j
    fin_cases j <;> simp [spinorToContactVector] <;> ring
  map_smul' c x := by
    ext j
    fin_cases j <;> simp [spinorToContactVector] <;> ring

theorem spinorToContact_contactToSpinor (z : CV) :
    spinorToContactVector (contactToSpinorVector z) = z := by
  funext j
  fin_cases j <;>
    simp [spinorToContactVector, contactToSpinorVector,
      wittPlusCoefficient, wittMinusCoefficient] <;> ring

theorem contactToSpinor_spinorToContact (v : SV) :
    contactToSpinorVector (spinorToContactVector v) = v := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [contactToSpinorVector, spinorToContactVector,
        wittPlusCoefficient, wittMinusCoefficient] <;> ring
  · funext i
    fin_cases i <;>
      simp [contactToSpinorVector, spinorToContactVector,
        wittPlusCoefficient, wittMinusCoefficient] <;> ring

@[simp] theorem contactToSpinor_wittPlus (i : Fin 5) :
    contactToSpinorVector (wittPlus i) = e_pos i + f_neg i := by
  fin_cases i <;> apply Prod.ext <;> funext j <;> fin_cases j <;>
    simp [contactToSpinorVector, wittPlus, wittPlusCoefficient,
      wittMinusCoefficient, e_pos, f_neg, coordinateVector] <;> ring

@[simp] theorem contactToSpinor_wittMinus (i : Fin 5) :
    contactToSpinorVector (wittMinus i) =
      (1 / 2 : ℝ) • (e_pos i - f_neg i) := by
  fin_cases i <;> apply Prod.ext <;> funext j <;> fin_cases j <;>
    simp [contactToSpinorVector, wittMinus, wittPlusCoefficient,
      wittMinusCoefficient, e_pos, f_neg, coordinateVector] <;> ring

def contactNullPlus (i : Fin 5) : V55 := e_pos i + f_neg i
def contactNullMinus (i : Fin 5) : V55 :=
  (1 / 2 : ℝ) • (e_pos i - f_neg i)

@[simp] theorem contactToSpinor_contactNullPlus (i : Fin 5) :
    contactToSpinorVector (wittPlus i) = contactNullPlus i := by
  simpa [contactNullPlus] using contactToSpinor_wittPlus i

@[simp] theorem contactToSpinor_contactNullMinus (i : Fin 5) :
    contactToSpinorVector (wittMinus i) = contactNullMinus i := by
  simpa [contactNullMinus] using contactToSpinor_wittMinus i

@[simp] theorem contactToSpinorLinear_wittPlus (i : Fin 5) :
    contactToSpinorLinear (wittPlus i) = contactNullPlus i := by
  simpa [contactToSpinorLinear] using contactToSpinor_contactNullPlus i

@[simp] theorem contactToSpinorLinear_wittMinus (i : Fin 5) :
    contactToSpinorLinear (wittMinus i) = contactNullMinus i := by
  simpa [contactToSpinorLinear] using contactToSpinor_contactNullMinus i

@[simp] theorem Q55_contactNullPlus (i : Fin 5) :
    Q55 (contactNullPlus i) = 0 := by
  fin_cases i <;> simp [contactNullPlus, e_pos, f_neg, Q55_apply] <;> ring

@[simp] theorem Q55_contactNullMinus (i : Fin 5) :
    Q55 (contactNullMinus i) = 0 := by
  fin_cases i <;> simp [contactNullMinus, e_pos, f_neg, Q55_apply] <;> ring

theorem Q55_polar_contactNullPlusMinus (i : Fin 5) :
    QuadraticMap.polar (⇑Q55) (contactNullPlus i) (contactNullMinus i) = 2 := by
  fin_cases i <;>
    simp [QuadraticMap.polar, contactNullPlus, contactNullMinus,
      e_pos, f_neg, Q55_apply, Fin.sum_univ_succ] <;> ring

@[simp] theorem contactToSpinorVector_equality (z : CV) :
    Q55 (contactToSpinorVector z) = splitPairing z z := by
  simp [contactToSpinorVector, Q55_apply, wittPlusCoefficient,
    wittMinusCoefficient, splitPairing, Fin.sum_univ_succ] <;> ring

theorem contactToSpinor_polar (x y : CV) :
    QuadraticMap.polar (⇑Q55)
        (contactToSpinorVector x) (contactToSpinorVector y) =
      splitPairing x y + splitPairing y x := by
  unfold QuadraticMap.polar
  change Q55 (contactToSpinorLinear x + contactToSpinorLinear y) -
      Q55 (contactToSpinorLinear x) - Q55 (contactToSpinorLinear y) = _
  rw [← contactToSpinorLinear.map_add]
  change Q55 (contactToSpinorVector (x + y)) -
      Q55 (contactToSpinorVector x) - Q55 (contactToSpinorVector y) = _
  rw [contactToSpinorVector_equality, contactToSpinorVector_equality,
    contactToSpinorVector_equality]
  simp [splitPairing_add_left, splitPairing_add_right]
  abel

@[simp] theorem polar_contactNullPlusPlus (i j : Fin 5) :
    QuadraticMap.polar (⇑Q55) (contactNullPlus i) (contactNullPlus j) = 0 := by
  rw [← contactToSpinor_contactNullPlus i, ← contactToSpinor_contactNullPlus j,
    contactToSpinor_polar]
  simp [wittPlus_pairing]

@[simp] theorem polar_contactNullMinusMinus (i j : Fin 5) :
    QuadraticMap.polar (⇑Q55) (contactNullMinus i) (contactNullMinus j) = 0 := by
  rw [← contactToSpinor_contactNullMinus i, ← contactToSpinor_contactNullMinus j,
    contactToSpinor_polar]
  simp [wittMinus_pairing]

@[simp] theorem polar_contactNullMinusPlus (i j : Fin 5) :
    QuadraticMap.polar (⇑Q55) (contactNullMinus i) (contactNullPlus j) =
      if i = j then 2 else 0 := by
  rw [← contactToSpinor_contactNullMinus i, ← contactToSpinor_contactNullPlus j,
    contactToSpinor_polar]
  rw [splitPairing_comm (wittMinus i) (wittPlus j)]
  rw [wittPlus_wittMinus]
  by_cases h : i = j <;> simp [h, eq_comm] <;> norm_num

@[simp] theorem polar_contactNullPlusMinus (i j : Fin 5) :
    QuadraticMap.polar (⇑Q55) (contactNullPlus i) (contactNullMinus j) =
      if i = j then 2 else 0 := by
  rw [← contactToSpinor_contactNullPlus i, ← contactToSpinor_contactNullMinus j,
    contactToSpinor_polar]
  rw [splitPairing_comm (wittMinus j) (wittPlus i)]
  rw [wittPlus_wittMinus]
  by_cases h : i = j <;> simp [h, eq_comm] <;> norm_num

noncomputable def contactV55Equiv : CV ≃ₗ[ℝ] SV where
  toFun := contactToSpinorVector
  invFun := spinorToContactVector
  left_inv := spinorToContact_contactToSpinor
  right_inv := contactToSpinor_spinorToContact
  map_add' := contactToSpinorLinear.map_add
  map_smul' := contactToSpinorLinear.map_smul

theorem spinBivectorVectorAction_commutatorBivector
    (u v w : V55) :
    spinBivectorVectorAction (commutatorBivector u v) w =
      (2 : ℝ) • bivectorVectorTransform u v w := by
  apply ι55_injective
  rw [ι55_spinBivectorVectorAction]
  change ⁅(commutatorBivector u v : Cl55), ι55 w⁆ =
    ι55 ((2 : ℝ) • bivectorVectorTransform u v w)
  have hswap : ι55 v * ι55 u =
      algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) u v) -
        ι55 u * ι55 v := by
    have h := CliffordAlgebra.ι_mul_ι_comm (Q := Q55) v u
    simpa [QuadraticMap.polar_comm] using h
  have hsource : ⁅ι55 u, ι55 v⁆ =
      (2 : ℝ) • (ι55 u * ι55 v) -
        (QuadraticMap.polar (⇑Q55) u v) • (1 : Cl55) := by
    rw [Ring.lie_def]
    calc
      ι55 u * ι55 v - ι55 v * ι55 u =
          ι55 u * ι55 v -
            ((algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) u v)) -
              ι55 u * ι55 v) := by rw [hswap]
      _ = ι55 u * ι55 v + ι55 u * ι55 v -
          algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) u v) := by abel
      _ = (2 : ℝ) • (ι55 u * ι55 v) -
          (QuadraticMap.polar (⇑Q55) u v) • (1 : Cl55) := by
            rw [two_smul]
            simp [Algebra.smul_def]
  change ⁅⁅ι55 u, ι55 v⁆, ι55 w⁆ =
    ι55 ((2 : ℝ) • bivectorVectorTransform u v w)
  rw [hsource]
  change ((2 : ℝ) • (ι55 u * ι55 v) -
        (QuadraticMap.polar (⇑Q55) u v) • (1 : Cl55)) * ι55 w -
      ι55 w * ((2 : ℝ) • (ι55 u * ι55 v) -
        (QuadraticMap.polar (⇑Q55) u v) • (1 : Cl55)) = _
  have hT : ι55 u * ι55 v * ι55 w -
      ι55 w * (ι55 u * ι55 v) =
      ι55 (bivectorVectorTransform u v w) := by
    simpa [Ring.lie_def] using bivector_vector_action_eq u v w
  calc
    _ = (2 : ℝ) •
        (ι55 u * ι55 v * ι55 w - ι55 w * (ι55 u * ι55 v)) := by
          simp only [sub_mul, mul_sub, smul_mul_assoc,
            mul_smul_comm, one_mul, mul_one]
          module
    _ = ι55 ((2 : ℝ) • bivectorVectorTransform u v w) := by
          rw [hT]
          exact (ι55.map_smul (2 : ℝ)
            (bivectorVectorTransform u v w)).symm

theorem spinBivectorVectorAction_add (X Y : SpinBivector55) (w : V55) :
    spinBivectorVectorAction (X + Y) w =
      spinBivectorVectorAction X w + spinBivectorVectorAction Y w := by
  apply ι55_injective
  calc
    ι55 (spinBivectorVectorAction (X + Y) w) =
        ⁅((X + Y : SpinBivector55) : Cl55), ι55 w⁆ :=
      ι55_spinBivectorVectorAction (X + Y) w
    _ = ⁅(X : Cl55), ι55 w⁆ + ⁅(Y : Cl55), ι55 w⁆ := by
      change ⁅(X : Cl55) + (Y : Cl55), ι55 w⁆ = _
      simp only [Ring.lie_def]
      noncomm_ring
    _ = ι55 (spinBivectorVectorAction X w) +
        ι55 (spinBivectorVectorAction Y w) := by
      rw [← ι55_spinBivectorVectorAction X w,
        ← ι55_spinBivectorVectorAction Y w]
    _ = ι55 (spinBivectorVectorAction X w +
        spinBivectorVectorAction Y w) := by rw [map_add]

theorem spinBivectorVectorAction_smul (c : ℝ) (X : SpinBivector55)
    (w : V55) :
    spinBivectorVectorAction (c • X) w = c • spinBivectorVectorAction X w := by
  apply ι55_injective
  calc
    ι55 (spinBivectorVectorAction (c • X) w) =
        ⁅((c • X : SpinBivector55) : Cl55), ι55 w⁆ :=
      ι55_spinBivectorVectorAction (c • X) w
    _ = c • ⁅(X : Cl55), ι55 w⁆ := by
      change ⁅c • (X : Cl55), ι55 w⁆ = _
      simp only [Ring.lie_def]
      simp only [smul_mul_assoc, mul_smul_comm, sub_eq_add_neg]
      module
    _ = ι55 (c • spinBivectorVectorAction X w) := by
      rw [← ι55_spinBivectorVectorAction X w, map_smul]

noncomputable def contactCartanTerm (i : Fin 5) : SpinBivector55 :=
  (-1 / 4 : ℝ) •
    commutatorBivector (contactNullPlus i) (contactNullMinus i)

noncomputable def contactEulerBivector : SpinBivector55 :=
  contactCartanTerm 0 + contactCartanTerm 1

@[simp] theorem contactCartanTerm_vectorAction (i : Fin 5) (w : V55) :
    spinBivectorVectorAction (contactCartanTerm i) w =
      (-1 / 2 : ℝ) •
        bivectorVectorTransform (contactNullPlus i) (contactNullMinus i) w := by
  rw [contactCartanTerm, spinBivectorVectorAction_smul,
    spinBivectorVectorAction_commutatorBivector]
  simp only [smul_smul]
  congr 1
  norm_num

@[simp] theorem contactEulerBivector_vectorAction (w : V55) :
    spinBivectorVectorAction contactEulerBivector w =
      spinBivectorVectorAction (contactCartanTerm 0) w +
        spinBivectorVectorAction (contactCartanTerm 1) w := by
  exact spinBivectorVectorAction_add _ _ _

theorem contactEulerBivector_on_plus (i : Fin 5) :
    spinBivectorVectorAction contactEulerBivector (contactNullPlus i) =
      (if i.val < 2 then (-1 : ℝ) else 0) • contactNullPlus i := by
  fin_cases i <;>
    simp only [contactEulerBivector_vectorAction, contactCartanTerm_vectorAction,
      bivectorVectorTransform, polar_contactNullPlusPlus,
      polar_contactNullMinusMinus, polar_contactNullMinusPlus,
      polar_contactNullPlusMinus] <;> simp [smul_smul] <;> norm_num

theorem contactEulerBivector_on_minus (i : Fin 5) :
    spinBivectorVectorAction contactEulerBivector (contactNullMinus i) =
      (if i.val < 2 then (1 : ℝ) else 0) • contactNullMinus i := by
  fin_cases i <;>
    simp only [contactEulerBivector_vectorAction, contactCartanTerm_vectorAction,
      bivectorVectorTransform, polar_contactNullPlusPlus,
      polar_contactNullMinusMinus, polar_contactNullMinusPlus,
      polar_contactNullPlusMinus] <;> simp [smul_smul] <;> norm_num

theorem contactEulerEnd_wittPlus (i : Fin 5) :
    contactEulerEnd (wittPlus i) =
      (if i.val < 2 then (-1 : ℝ) else 0) • wittPlus i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [contactEulerEnd, contactWeightR, contactWeight,
      wittPlus, coordinateVector] <;> norm_num

theorem contactEulerEnd_wittMinus (i : Fin 5) :
    contactEulerEnd (wittMinus i) =
      (if i.val < 2 then (1 : ℝ) else 0) • wittMinus i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [contactEulerEnd, contactWeightR, contactWeight,
      wittMinus, coordinateVector] <;> norm_num

theorem contactEulerBivector_matches_wittPlus (i : Fin 5) :
    spinBivectorVectorAction contactEulerBivector
        (contactToSpinorLinear (wittPlus i)) =
      contactToSpinorLinear (contactEulerEnd (wittPlus i)) := by
  rw [contactToSpinorLinear_wittPlus, contactEulerBivector_on_plus,
    contactEulerEnd_wittPlus]
  by_cases h : i.val < 2
  · simp only [if_pos h]
    rw [← contactToSpinorLinear_wittPlus i]
    change (-1 : ℝ) • contactToSpinorLinear (wittPlus i) =
      contactToSpinorLinear ((-1 : ℝ) • wittPlus i)
    rw [map_smul]
  · simp only [if_neg h, zero_smul]
    change (0 : SV) = contactToSpinorLinear 0
    simp

theorem contactEulerBivector_matches_wittMinus (i : Fin 5) :
    spinBivectorVectorAction contactEulerBivector
        (contactToSpinorLinear (wittMinus i)) =
      contactToSpinorLinear (contactEulerEnd (wittMinus i)) := by
  rw [contactToSpinorLinear_wittMinus, contactEulerBivector_on_minus,
    contactEulerEnd_wittMinus]
  by_cases h : i.val < 2
  · simp only [if_pos h]
    rw [← contactToSpinorLinear_wittMinus i]
    change (1 : ℝ) • contactToSpinorLinear (wittMinus i) =
      contactToSpinorLinear ((1 : ℝ) • wittMinus i)
    rw [map_smul]
  · simp only [if_neg h, zero_smul]
    change (0 : SV) = contactToSpinorLinear 0
    simp

theorem contactEuler_vector_intertwining (z : CV) :
    contactToSpinorLinear (contactEulerEnd z) =
      spinBivectorVectorAction contactEulerBivector
        (contactToSpinorLinear z) := by
  rw [← witt_reconstruction z]
  unfold wittSynthesis
  simp only [map_sum, map_add, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← contactEulerBivector_matches_wittPlus i,
    ← contactEulerBivector_matches_wittMinus i]

def IsContactTKKGrade (k : ℤ) (X : SpinBivector55) : Prop :=
  ⁅contactEulerBivector, X⁆ = (k : ℝ) • X

theorem contactTKKGrade_bracket {k l : ℤ} {X Y : SpinBivector55}
    (hX : IsContactTKKGrade k X) (hY : IsContactTKKGrade l Y) :
    IsContactTKKGrade (k + l) ⁅X, Y⁆ := by
  unfold IsContactTKKGrade at *
  calc
    ⁅contactEulerBivector, ⁅X, Y⁆⁆ =
        ⁅⁅contactEulerBivector, X⁆, Y⁆ +
          ⁅X, ⁅contactEulerBivector, Y⁆⁆ := by
        have h := lie_lie contactEulerBivector X Y
        rw [h]
        abel
    _ = ((k + l : ℤ) : ℝ) • ⁅X, Y⁆ := by
        rw [hX, hY, smul_lie, lie_smul]
        module

/-- The contact-graded spin Lie algebra acts on the same real 32-coordinate
exterior spinor through the existing Clifford algebra equivalence. -/
noncomputable def tkkSpinorAction (X : SpinBivector55) :
    Module.End ℝ SCoord := cl55FockAlgEquiv X

theorem tkkSpinorAction_bracket (X Y : SpinBivector55) :
    tkkSpinorAction ⁅X, Y⁆ =
      ⁅tkkSpinorAction X, tkkSpinorAction Y⁆ := by
  change cl55FockAlgEquiv
      ((X : Cl55) * (Y : Cl55) - (Y : Cl55) * (X : Cl55)) =
    cl55FockAlgEquiv (X : Cl55) * cl55FockAlgEquiv (Y : Cl55) -
      cl55FockAlgEquiv (Y : Cl55) * cl55FockAlgEquiv (X : Cl55)
  simp [map_mul]

theorem tkkSpinorAction_grade_bracket {k : ℤ} {X : SpinBivector55}
    (hX : IsContactTKKGrade k X) :
    ⁅tkkSpinorAction contactEulerBivector, tkkSpinorAction X⁆ =
      (k : ℝ) • tkkSpinorAction X := by
  rw [← tkkSpinorAction_bracket]
  change ⁅contactEulerBivector, X⁆ = (k : ℝ) • X at hX
  rw [hX]
  simp [tkkSpinorAction, map_smul]

/-- Pointwise bracket law on the 32-dimensional spinor. -/
theorem tkkSpinorAction_bracket_apply (X Y : SpinBivector55)
    (ψ : SCoord) :
    tkkSpinorAction ⁅X, Y⁆ ψ =
      tkkSpinorAction X (tkkSpinorAction Y ψ) -
        tkkSpinorAction Y (tkkSpinorAction X ψ) := by
  rw [tkkSpinorAction_bracket]
  rfl

noncomputable def tkkVacuumIdealAction (X : SpinBivector55) :
    Module.End ℝ cl55VacuumIdeal :=
  cl55VacuumIdealLeftAction (X : Cl55)

theorem tkkVacuumIdealAction_bracket (X Y : SpinBivector55) :
    tkkVacuumIdealAction ⁅X, Y⁆ =
      ⁅tkkVacuumIdealAction X, tkkVacuumIdealAction Y⁆ := by
  ext x
  change ((X : Cl55) * (Y : Cl55) - (Y : Cl55) * (X : Cl55)) *
      (x : Cl55) =
    (X : Cl55) * ((Y : Cl55) * (x : Cl55)) -
      (Y : Cl55) * ((X : Cl55) * (x : Cl55))
  noncomm_ring

theorem tkkVacuumIdealAction_bracket_apply
    (X Y : SpinBivector55) (x : cl55VacuumIdeal) :
    tkkVacuumIdealAction ⁅X, Y⁆ x =
      tkkVacuumIdealAction X (tkkVacuumIdealAction Y x) -
        tkkVacuumIdealAction Y (tkkVacuumIdealAction X x) := by
  rw [tkkVacuumIdealAction_bracket]
  rfl

theorem tkkVacuumIdealAction_smul (c : ℝ) (X : SpinBivector55) :
    tkkVacuumIdealAction (c • X) = c • tkkVacuumIdealAction X := by
  ext x
  change (c • (X : Cl55)) * (x : Cl55) =
    c • ((X : Cl55) * (x : Cl55))
  simp [Algebra.smul_mul_assoc]

theorem tkkVacuumIdealAction_grade_bracket {k : ℤ}
    {X : SpinBivector55} (hX : IsContactTKKGrade k X) :
    ⁅tkkVacuumIdealAction contactEulerBivector, tkkVacuumIdealAction X⁆ =
      (k : ℝ) • tkkVacuumIdealAction X := by
  rw [← tkkVacuumIdealAction_bracket]
  change ⁅contactEulerBivector, X⁆ = (k : ℝ) • X at hX
  rw [hX]
  exact tkkVacuumIdealAction_smul (k : ℝ) X

theorem tkkVacuumIdealAction_intertwines_spinor
    (X : SpinBivector55) (x : cl55VacuumIdeal) :
    cl55VacuumIdealSpinorEquiv (tkkVacuumIdealAction X x) =
      neutralCliffordRep
        (InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm
          (X : Cl55))
        (cl55VacuumIdealSpinorEquiv x) := by
  exact cl55VacuumIdealLeftAction_intertwines (X : Cl55) x

end InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal
end noncomputable section
