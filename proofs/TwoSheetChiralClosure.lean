import Mathlib
import InfoGeometry.Canonical.ChiralCausalCone
import proofs.GrandUnifiedTKK

noncomputable section

namespace TwoSheetChiralClosure

open Matrix

abbrev M4C := Matrix (Fin 4) (Fin 4) ℂ

/-- Outer particle/hole matrix units, tensored with the inner identity. -/
def uPlus : M4C := !![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0]
def uMinus : M4C := !![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0]

/-- Inner chiral matrix units, repeated on both sheets. -/
def sPlus : M4C := !![0,1,0,0; 0,0,0,0; 0,0,0,1; 0,0,0,0]
def sMinus : M4C := !![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,1,0]

def comm (A B : M4C) : M4C := A * B - B * A
def anti (A B : M4C) : M4C := A * B + B * A

def U3 : M4C := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]
def S3 : M4C := !![1,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,-1]

def qPP : M4C := uPlus * sPlus
def qPM : M4C := uPlus * sMinus
def qMP : M4C := uMinus * sPlus
def qMM : M4C := uMinus * sMinus

@[simp] theorem uPlus_sq : uPlus * uPlus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uPlus, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

@[simp] theorem uMinus_sq : uMinus * uMinus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uMinus, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

@[simp] theorem sPlus_sq : sPlus * sPlus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sPlus, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

@[simp] theorem sMinus_sq : sMinus * sMinus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sMinus, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

theorem u_CAR : anti uPlus uMinus = (1 : M4C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [anti, uPlus, uMinus, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_four]

theorem s_CAR : anti sPlus sMinus = (1 : M4C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [anti, sPlus, sMinus, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_four]

theorem u_lie_axis : comm uPlus uMinus = U3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm, U3, uPlus, uMinus, Matrix.mul_apply, Matrix.sub_apply,
      Fin.sum_univ_four]

theorem s_lie_axis : comm sPlus sMinus = S3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm, S3, sPlus, sMinus, Matrix.mul_apply, Matrix.sub_apply,
      Fin.sum_univ_four]

theorem cross_comm :
    comm uPlus sPlus = 0 ∧ comm uPlus sMinus = 0 ∧
    comm uMinus sPlus = 0 ∧ comm uMinus sMinus = 0 := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [comm, uPlus, sPlus, Matrix.mul_apply, Matrix.sub_apply,
        Fin.sum_univ_four]
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [comm, uPlus, sMinus, Matrix.mul_apply, Matrix.sub_apply,
        Fin.sum_univ_four]
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [comm, uMinus, sPlus, Matrix.mul_apply, Matrix.sub_apply,
        Fin.sum_univ_four]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [comm, uMinus, sMinus, Matrix.mul_apply, Matrix.sub_apply,
        Fin.sum_univ_four]

/-- The four mixed channels are the tensor products of sheet and chiral lanes. -/
theorem mixed_channels_nonzero :
    qPP ≠ 0 ∧ qPM ≠ 0 ∧ qMP ≠ 0 ∧ qMM ≠ 0 := by
  repeat' constructor
  · intro h
    have hq : qPP 0 3 = 1 := by
      norm_num [qPP, uPlus, sPlus, Matrix.mul_apply, Fin.sum_univ_four,
        Fin.sum_univ_succ] <;> rfl
    have h' := congrArg (fun A => A 0 3) h
    change qPP 0 3 = (0 : M4C) 0 3 at h'
    rw [hq] at h'
    simpa using h'
  · intro h
    have hq : qPM 1 2 = 1 := by
      norm_num [qPM, uPlus, sMinus, Matrix.mul_apply, Fin.sum_univ_four,
        Fin.sum_univ_succ] <;> rfl
    have h' := congrArg (fun A => A 1 2) h
    change qPM 1 2 = (0 : M4C) 1 2 at h'
    rw [hq] at h'
    simpa using h'
  · intro h
    have hq : qMP 2 1 = 1 := by
      norm_num [qMP, uMinus, sPlus, Matrix.mul_apply, Fin.sum_univ_four,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three] <;> rfl
    have h' := congrArg (fun A => A 2 1) h
    change qMP 2 1 = (0 : M4C) 2 1 at h'
    rw [hq] at h'
    simpa using h'
  · intro h
    have hq : qMM 3 0 = 1 := by
      norm_num [qMM, uMinus, sMinus, Matrix.mul_apply, Fin.sum_univ_four,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three] <;> rfl
    have h' := congrArg (fun A => A 3 0) h
    change qMM 3 0 = (0 : M4C) 3 0 at h'
    rw [hq] at h'
    simpa using h'

/-- The two-sheet parity is the outer grading axis; the inner axis is chirality. -/
theorem grading_axes_square :
    U3 * U3 = (1 : M4C) ∧ S3 * S3 = (1 : M4C) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [U3, S3, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

/-- Möbius parity and particle-hole inversion are involutions on the punctured scalar line. -/
def mobiusParity (z : ℂ) : ℂ := -z
def mobiusParticleHole (z : ℂ) : ℂ := z⁻¹
def mobiusChiralParity (z : ℂ) : ℂ := -(z⁻¹)

theorem mobius_involutions (z : ℂ) (hz : z ≠ 0) :
    mobiusParity (mobiusParity z) = z ∧
    mobiusParticleHole (mobiusParticleHole z) = z ∧
    mobiusChiralParity (mobiusChiralParity z) = z := by
  simp [mobiusParity, mobiusParticleHole, mobiusChiralParity, hz]

inductive Lane where
 | uPlus | sPlus | uMinus | sMinus
 | U3 | S3 | qPP | qPM | qMP | qMM
 deriving DecidableEq, Repr

def laneGrade : Lane → GrandUnifiedTKK.TKK_Grade
 | .uPlus => .g_1
 | .sPlus => .g_1
 | .uMinus => .g_neg1
 | .sMinus => .g_neg1
 | .U3 => .g_0
 | .S3 => .g_0
 | .qPP => .g_2
 | .qPM => .g_0
 | .qMP => .g_0
 | .qMM => .g_neg2

theorem tkk_grade_routing :
   GrandUnifiedTKK.add_grade (laneGrade .uPlus) (laneGrade .sPlus) = some .g_2 ∧
   GrandUnifiedTKK.add_grade (laneGrade .uMinus) (laneGrade .sMinus) = some .g_neg2 ∧
   GrandUnifiedTKK.add_grade (laneGrade .uPlus) (laneGrade .sMinus) = some .g_0 ∧
   GrandUnifiedTKK.add_grade (laneGrade .uMinus) (laneGrade .sPlus) = some .g_0 := by
 decide

/-- Explicit finite closure packet: two CAR copies, commuting cross sectors,
    two grading axes, and four nonzero mixed channels. -/
theorem closure_packet :
    uPlus * uPlus = 0 ∧ uMinus * uMinus = 0 ∧
    sPlus * sPlus = 0 ∧ sMinus * sMinus = 0 ∧
    anti uPlus uMinus = (1 : M4C) ∧ anti sPlus sMinus = (1 : M4C) ∧
    comm uPlus uMinus = U3 ∧ comm sPlus sMinus = S3 ∧
    comm uPlus sPlus = 0 ∧ comm uPlus sMinus = 0 ∧
    comm uMinus sPlus = 0 ∧ comm uMinus sMinus = 0 ∧
    qPP ≠ 0 ∧ qPM ≠ 0 ∧ qMP ≠ 0 ∧ qMM ≠ 0 := by
  rcases cross_comm with ⟨h₁, h₂, h₃, h₄⟩
  rcases mixed_channels_nonzero with ⟨h₅, h₆, h₇, h₈⟩
  exact ⟨uPlus_sq, uMinus_sq, sPlus_sq, sMinus_sq, u_CAR, s_CAR,
    u_lie_axis, s_lie_axis, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩

end TwoSheetChiralClosure
