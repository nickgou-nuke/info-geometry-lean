import InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow

/-!
# The circular `ZMod 3` grading and the axial obstruction

The normalized commutator with `lUnit` is a grading operator on the circular
frame, not a derivation of the alternative split-octonion product.  Same
polarization products change the circular weight by two, hence by `-1` modulo
three.  This file records that distinction explicitly.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Lie.SplitOctonionCircularZ3Grading

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CZ := InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.CanonicalZorn

def circularGrade : Fin 8 → ZMod 3
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | _ => 0

theorem circularGrade_frame (i : Fin 8) :
    circularGrade i =
      match i with
      | 0 => 0
      | 1 | 2 | 3 => 1
      | 4 => 0
      | 5 | 6 | 7 => 2
      | _ => 0 := by
  fin_cases i <;> rfl

theorem circularGrade_uPlus : circularGrade 0 = 0 := rfl

theorem circularGrade_uMinus : circularGrade 4 = 0 := rfl

theorem circularGrade_plus_plus : (1 : ZMod 3) + 1 = 2 := by decide

theorem circularGrade_minus_minus : (2 : ZMod 3) + 2 = 1 := by decide

theorem circularGrade_plus_minus : (1 : ZMod 3) + 2 = 0 := by decide

def circularGradeSubmodule (r : ZMod 3) : Submodule ℝ CZ :=
  if r = 0 then zeroWeightSubmodule else
    if r = 1 then positiveWeightSubmodule else negativeWeightSubmodule

theorem uPlus_mem_circularGradeSubmodule_zero :
    uPlus ∈ circularGradeSubmodule 0 := by
  rw [circularGradeSubmodule]
  simp only [if_pos]
  exact Submodule.subset_span (by simp)

theorem uMinus_mem_circularGradeSubmodule_zero :
    uMinus ∈ circularGradeSubmodule 0 := by
  rw [circularGradeSubmodule]
  simp only [if_pos]
  exact Submodule.subset_span (by simp)

theorem circularGradeSubmodules_sup_eq_top :
    circularGradeSubmodule 0 ⊔ circularGradeSubmodule 1 ⊔
        circularGradeSubmodule 2 = (⊤ : Submodule ℝ CZ) := by
  simpa [circularGradeSubmodule] using weightSubmodules_sup_eq_top

theorem circularPeirceBasis_mem_circularGradeSubmodule (i : Fin 8) :
    circularPeirceBasis i ∈ circularGradeSubmodule (circularGrade i) := by
  fin_cases i
  · simp only [circularPeirceBasis_apply, frame, circularGrade]
    rw [circularGradeSubmodule]
    simp only [if_pos]
    exact Submodule.subset_span (by simp)
  · simp only [circularPeirceBasis_apply, frame, circularGrade]
    rw [circularGradeSubmodule]
    simp only [if_neg (show (1 : ZMod 3) ≠ 0 by decide), if_pos]
    exact Submodule.subset_span ⟨0, rfl⟩
  · simp only [circularPeirceBasis_apply, frame, circularGrade]
    rw [circularGradeSubmodule]
    simp only [if_neg (show (1 : ZMod 3) ≠ 0 by decide), if_pos]
    exact Submodule.subset_span ⟨1, rfl⟩
  · simp only [circularPeirceBasis_apply, frame, circularGrade]
    rw [circularGradeSubmodule]
    simp only [if_neg (show (1 : ZMod 3) ≠ 0 by decide), if_pos]
    exact Submodule.subset_span ⟨2, rfl⟩
  · simp only [circularPeirceBasis_apply, frame, circularGrade]
    rw [circularGradeSubmodule]
    simp only [if_pos]
    exact Submodule.subset_span (by simp)
  · simp only [circularPeirceBasis_apply, frame, circularGrade]
    rw [circularGradeSubmodule]
    simp only [if_neg (show (2 : ZMod 3) ≠ 0 by decide),
      if_neg (show (2 : ZMod 3) ≠ 1 by decide)]
    exact Submodule.subset_span ⟨0, rfl⟩
  · simp only [circularPeirceBasis_apply, frame, circularGrade]
    rw [circularGradeSubmodule]
    simp only [if_neg (show (2 : ZMod 3) ≠ 0 by decide),
      if_neg (show (2 : ZMod 3) ≠ 1 by decide)]
    exact Submodule.subset_span ⟨1, rfl⟩
  · simp only [circularPeirceBasis_apply, frame, circularGrade]
    rw [circularGradeSubmodule]
    simp only [if_neg (show (2 : ZMod 3) ≠ 0 by decide),
      if_neg (show (2 : ZMod 3) ≠ 1 by decide)]
    exact Submodule.subset_span ⟨2, rfl⟩

theorem rootPlus_mul_rootMinus_mem_circularGradeSubmodule_add
    (a b : Fin 3) :
    rootPlus a * rootMinus b ∈
      circularGradeSubmodule (circularGrade 1 + circularGrade 5) := by
  have hgrade : circularGrade 1 + circularGrade 5 = (0 : ZMod 3) := by
    decide
  rw [hgrade]
  by_cases h : a = b
  · subst b
    rw [rootPlus_mul_rootMinus]
    exact uPlus_mem_circularGradeSubmodule_zero
  · have hzero : rootPlus a * rootMinus b = 0 := by
      fin_cases a <;> fin_cases b <;>
        ext i <;>
        simp_all [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
          iUnit, jUnit, kQuaternionUnit, lUnit,
          InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
          InfoGeometry.Canonical.ZornMatrix.mul,
          Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross] <;>
        (try fin_cases i) <;> norm_num
    rw [hzero]
    exact (circularGradeSubmodule 0).zero_mem

theorem rootMinus_mul_rootPlus_mem_circularGradeSubmodule_add
    (a b : Fin 3) :
    rootMinus a * rootPlus b ∈
      circularGradeSubmodule (circularGrade 5 + circularGrade 1) := by
  have hgrade : circularGrade 5 + circularGrade 1 = (0 : ZMod 3) := by
    decide
  rw [hgrade]
  by_cases h : a = b
  · subst b
    rw [rootMinus_mul_rootPlus]
    exact uMinus_mem_circularGradeSubmodule_zero
  · have hzero : rootMinus a * rootPlus b = 0 := by
      fin_cases a <;> fin_cases b <;>
        ext i <;>
        simp_all [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
          iUnit, jUnit, kQuaternionUnit, lUnit,
          InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
          InfoGeometry.Canonical.ZornMatrix.mul,
          Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross] <;>
        (try fin_cases i) <;> norm_num
    rw [hzero]
    exact (circularGradeSubmodule 0).zero_mem

theorem rootPlus_mul_rootMinus_eq_ite (a b : Fin 3) :
    rootPlus a * rootMinus b = if a = b then uPlus else 0 := by
  by_cases h : a = b
  · subst b
    simp only [if_pos rfl]
    exact rootPlus_mul_rootMinus a
  · have hzero : rootPlus a * rootMinus b = 0 := by
      fin_cases a <;> fin_cases b <;>
        simp_all [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
          iUnit, jUnit, kQuaternionUnit, lUnit,
          InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
          InfoGeometry.Canonical.ZornMatrix.mul,
          Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross] <;>
        (try fin_cases ‹Fin 3›) <;> norm_num
    simp [h, hzero]

theorem rootMinus_mul_rootPlus_eq_ite (a b : Fin 3) :
    rootMinus a * rootPlus b = if a = b then uMinus else 0 := by
  by_cases h : a = b
  · subst b
    simp only [if_pos rfl]
    exact rootMinus_mul_rootPlus a
  · have hzero : rootMinus a * rootPlus b = 0 := by
      fin_cases a <;> fin_cases b <;>
        simp_all [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
          iUnit, jUnit, kQuaternionUnit, lUnit,
          InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
          InfoGeometry.Canonical.ZornMatrix.mul,
          Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross] <;>
        (try fin_cases ‹Fin 3›) <;> norm_num
    simp [h, hzero]

theorem root_mixed_commutator_eq_ite (a b : Fin 3) :
    rootPlus a * rootMinus b - rootMinus b * rootPlus a =
      if a = b then lUnit else 0 := by
  rw [rootPlus_mul_rootMinus_eq_ite, rootMinus_mul_rootPlus_eq_ite]
  by_cases h : a = b
  · subst b
    simp only [if_pos rfl]
    exact uPlus_sub_uMinus
  · simp only [if_neg h, if_neg (Ne.symm h), sub_zero]

theorem root_mixed_anticommutator_eq_ite (a b : Fin 3) :
    rootPlus a * rootMinus b + rootMinus b * rootPlus a =
      if a = b then 1 else 0 := by
  rw [rootPlus_mul_rootMinus_eq_ite, rootMinus_mul_rootPlus_eq_ite]
  by_cases h : a = b
  · subst b
    simp only [if_pos rfl]
    exact uPlus_add_uMinus
  · simp only [if_neg h, if_neg (Ne.symm h), add_zero]

theorem rootPlus_mul_self_mem_circularGradeSubmodule_add (a : Fin 3) :
    rootPlus a * rootPlus a ∈
      circularGradeSubmodule (circularGrade 1 + circularGrade 1) := by
  rw [rootPlus_sq]
  exact (circularGradeSubmodule (circularGrade 1 + circularGrade 1)).zero_mem

theorem rootMinus_mul_self_mem_circularGradeSubmodule_add (a : Fin 3) :
    rootMinus a * rootMinus a ∈
      circularGradeSubmodule (circularGrade 5 + circularGrade 5) := by
  rw [rootMinus_sq]
  exact (circularGradeSubmodule (circularGrade 5 + circularGrade 5)).zero_mem

theorem hyperbolicFlowZorn_circularPeirceBasis
    (t : ℝ) (i : Fin 8) :
    InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow.hyperbolicFlowZorn t
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i) =
      Real.exp (t *
        InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) •
        InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i := by
  rw [InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow.hyperbolicFlowZorn_apply]
  have hcoord :
      InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun
          (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i) =
        (Pi.single i 1 : Fin 8 → ℝ) := by
    ext j
    rw [Module.Basis.equivFun_self]
    by_cases h : i = j
    · subst j
      simp
    · simp [h, Ne.symm h]
  have hsingle :
      InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun.symm
          (Pi.single i 1 : Fin 8 → ℝ) =
        InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i := by
    apply InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun.injective
    simp
  have hflow := congrArg
    (InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow.hyperbolicFlowCoordinate t)
    hcoord
  have hflow' := congrArg
    InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun.symm hflow
  rw [hflow']
  rw [
    InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow.hyperbolicFlowCoordinate_basis_action]
  rw [map_smul, hsingle]

theorem circularPeirceBasis_one_mul_two :
    InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis (1 : Fin 8) *
        InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis (2 : Fin 8) =
      InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 7 := by
  rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply,
    InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply,
    InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
  simp only [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularFrame]
  rw [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.cartesianZorn_rootPlus_mul_rootPlus_cross]
  rw [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.cartesianZorn_rootMinus]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus]
  · simp [InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus]
  · funext k
    fin_cases k <;>
      norm_num [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.axis,
        InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
        InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus,
        InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.quaternionAxis,
        InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.ellAxis,
        InfoGeometry.Canonical.ZornMatrix.cross,
        Pi.single_apply, Function.update] <;> simp [Fin.ext_iff]
  · funext k
    fin_cases k <;>
      norm_num [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.axis,
        InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
        InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus,
        InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.quaternionAxis,
        InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.ellAxis,
        InfoGeometry.Canonical.ZornMatrix.cross,
        Pi.single_apply, Function.update] <;> simp [Fin.ext_iff]

/-! A concrete same-chirality product.  This is the multiplication fact used
by the obstruction below; it is proved once from the native Zorn product. -/
theorem rootPlus_zero_mul_rootPlus_one :
    rootPlus 0 * rootPlus 1 = rootMinus 2 := by
  ext <;>
    simp [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv]
  all_goals (try fin_cases ‹Fin 3›) <;> norm_num

theorem rootPlus_one_mul_rootPlus_two :
    rootPlus 1 * rootPlus 2 = rootMinus 0 := by
  ext <;>
    simp [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv]
  all_goals (try fin_cases ‹Fin 3›) <;> norm_num

theorem rootPlus_two_mul_rootPlus_zero :
    rootPlus 2 * rootPlus 0 = rootMinus 1 := by
  ext <;>
    simp [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv]
  all_goals (try fin_cases ‹Fin 3›) <;> norm_num

theorem rootPlus_one_mul_rootPlus_zero :
    rootPlus 1 * rootPlus 0 = -rootMinus 2 := by
  ext <;>
    simp [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv]
  all_goals (try fin_cases ‹Fin 3›) <;> norm_num

theorem rootPlus_two_mul_rootPlus_one :
    rootPlus 2 * rootPlus 1 = -rootMinus 0 := by
  ext <;>
    simp [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv]
  all_goals (try fin_cases ‹Fin 3›) <;> norm_num

theorem rootPlus_zero_mul_rootPlus_two :
    rootPlus 0 * rootPlus 2 = -rootMinus 1 := by
  ext <;>
    simp [rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv]
  all_goals (try fin_cases ‹Fin 3›) <;> norm_num

theorem rootPlus_zero_mul_rootPlus_one_mem_grade_add :
    rootPlus 0 * rootPlus 1 ∈
      circularGradeSubmodule (circularGrade 1 + circularGrade 2) := by
  rw [rootPlus_zero_mul_rootPlus_one]
  have h := circularPeirceBasis_mem_circularGradeSubmodule (7 : Fin 8)
  simpa [circularPeirceBasis_seven, circularGrade,
    circularGradeSubmodule] using h

theorem rootMinus_two_ne_zero : rootMinus 2 ≠ 0 := by
  intro h
  have hx := congrArg (fun Z : CZ => Z.x 1) h
  simp [rootMinus, chiralNull, ellBasis, quaternionBasis,
      jUnit, kQuaternionUnit, lUnit, Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross] at hx

theorem hyperbolicFlowZorn_not_mul_of_ne_zero (t : ℝ) (ht : t ≠ 0) :
    ¬ ∀ X Y : CZ,
      InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow.hyperbolicFlowZorn t
          (X * Y) =
        InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow.hyperbolicFlowZorn t X *
          InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow.hyperbolicFlowZorn t Y := by
  intro hmul
  have hh := hmul
    (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis (1 : Fin 8))
    (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis (2 : Fin 8))
  rw [circularPeirceBasis_one_mul_two,
    hyperbolicFlowZorn_circularPeirceBasis t (7 : Fin 8),
    hyperbolicFlowZorn_circularPeirceBasis t (1 : Fin 8),
    hyperbolicFlowZorn_circularPeirceBasis t (2 : Fin 8)] at hh
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul,
    circularPeirceBasis_one_mul_two] at hh
  rw [smul_smul] at hh
  have hscalar := smul_left_injective ℝ
    (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.ne_zero
      (7 : Fin 8)) hh
  have hexp : Real.exp (-t) = Real.exp t * Real.exp t := by
    simpa [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] using hscalar
  rw [← Real.exp_add] at hexp
  have := Real.exp_injective hexp
  have ht0 : t = 0 := by linarith
  exact ht ht0

theorem ellCommutator_not_derivation :
    ¬ IsDerivation ellCommutator := by
  intro h
  have hh := h (rootPlus 0) (rootPlus 1)
  rw [rootPlus_zero_mul_rootPlus_one, ellCommutator_rootMinus,
    ellCommutator_rootPlus, ellCommutator_rootPlus] at hh
  have hh' : (-2 : ℝ) • rootMinus 2 =
      ((2 : ℝ) • rootPlus 0) * rootPlus 1 +
        rootPlus 0 * ((2 : ℝ) • rootPlus 1) := hh
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul,
    rootPlus_zero_mul_rootPlus_one] at hh'
  have hx := congrArg (fun Z : CZ => Z.x 1) hh'
  change (-2 : ℝ) * (rootMinus 2).x 1 =
    2 * (rootMinus 2).x 1 + 2 * (rootMinus 2).x 1 at hx
  have hcoord : (rootMinus 2).x 1 = (-1 / 2 : ℝ) := by
    simp [rootMinus, chiralNull, ellBasis, quaternionBasis,
      kQuaternionUnit, lUnit, Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
    norm_num
  rw [hcoord] at hx
  norm_num at hx

theorem circularAxialGrading_not_derivation :
    ¬ IsDerivation axialGrading := by
  intro h
  apply ellCommutator_not_derivation
  intro X Y
  have hXY := h X Y
  have hscale (Z : CZ) : ellCommutator Z = (2 : ℝ) • axialGrading Z := by
    simp [axialGrading]
  rw [hscale, hXY, hscale, hscale]
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul,
    smul_add]

theorem rootPlus_associator_zero_one_two :
    (rootPlus 0 * rootPlus 1) * rootPlus 2 -
        rootPlus 0 * (rootPlus 1 * rootPlus 2) =
      uMinus - uPlus := by
  rw [rootPlus_zero_mul_rootPlus_one,
    rootPlus_one_mul_rootPlus_two,
    rootMinus_mul_rootPlus,
    rootPlus_mul_rootMinus]

end InfoGeometry.Lie.SplitOctonionCircularZ3Grading
