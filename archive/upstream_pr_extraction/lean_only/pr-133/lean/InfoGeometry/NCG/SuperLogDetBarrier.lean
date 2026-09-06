import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.Jordan.LogDet

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix

namespace InfoGeometry.NCG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "SubMat" => Matrix ι ι ℝ

/--
The Schur-Berezinian logarithmic potential on the ordinary finite block carrier.

This is a scalar readout of the existing algebraic `berezinianSchur`.  Its
intended barrier domain is the locus where that scalar is strictly positive.
-/
def superLogDetBarrierSchur
    (A B C D invD : SubMat) (invDetD : ℝ) : ℝ :=
  -Real.log (berezinianSchur A B C D invD invDetD)

/-- The positive real domain on which the Schur-Berezinian has barrier meaning. -/
def SuperBerezinianPositive
    (A B C D invD : SubMat) (invDetD : ℝ) : Prop :=
  0 < berezinianSchur A B C D invD invDetD

/-- A unit Berezinian has zero logarithmic potential. -/
theorem superLogDetBarrierSchur_eq_zero_of_berezinian_eq_one
    (A B C D invD : SubMat) (invDetD : ℝ)
    (hBer : berezinianSchur A B C D invD invDetD = 1) :
    superLogDetBarrierSchur A B C D invD invDetD = 0 := by
  simp [superLogDetBarrierSchur, hBer]

/--
Canonical decoupled boson/fermion logarithmic ratio.

For positive determinants this is exactly `-log(det A) + log(det D)`.
-/
def superLogDetBarrierDiag (A D : SubMat) : ℝ :=
  -Real.log (Matrix.det A / Matrix.det D)

/-- Exact bosonic-minus-fermionic logarithmic splitting on positive blocks. -/
theorem superLogDetBarrierDiag_eq
    (A D : SubMat)
    (hA : 0 < Matrix.det A) (hD : 0 < Matrix.det D) :
    superLogDetBarrierDiag A D =
      -Real.log (Matrix.det A) + Real.log (Matrix.det D) := by
  unfold superLogDetBarrierDiag
  rw [Real.log_div hA.ne' hD.ne']
  ring

/-- Equal positive determinants give unit volume ratio and zero super barrier. -/
theorem superLogDetBarrierDiag_eq_zero_of_det_eq
    (A D : SubMat)
    (hD : Matrix.det D ≠ 0)
    (hdet : Matrix.det A = Matrix.det D) :
    superLogDetBarrierDiag A D = 0 := by
  subst hdet
  simp [superLogDetBarrierDiag, hD]

section SPD

open InfoGeometry.Jordan

variable {m n : ℕ}

/--
The theorem-safe SPD super barrier: the bosonic log-det barrier minus the
fermionic log-det barrier.
-/
def superLogDetBarrierSPD (X : SPD m) (Y : SPD n) : ℝ :=
  logDetBarrier X - logDetBarrier Y

/-- The SPD super barrier is the logarithm of the determinant ratio. -/
theorem superLogDetBarrierSPD_eq_log_ratio
    (X : SPD m) (Y : SPD n) :
    superLogDetBarrierSPD X Y =
      -Real.log (Matrix.det X.mat / Matrix.det Y.mat) := by
  unfold superLogDetBarrierSPD logDetBarrier
  rw [Real.log_div X.det_ne_zero Y.det_ne_zero]
  ring

/-- Exact bosonic/fermionic sign inversion. -/
theorem superLogDetBarrierSPD_eq_bosonic_sub_fermionic
    (X : SPD m) (Y : SPD n) :
    superLogDetBarrierSPD X Y =
      logDetBarrier X - logDetBarrier Y := by
  rfl

/-- Identical graded sectors cancel algebraically. -/
@[simp]
theorem superLogDetBarrierSPD_self (X : SPD m) :
    superLogDetBarrierSPD X X = 0 := by
  simp [superLogDetBarrierSPD]

/-- Equal determinant readout is sufficient for exact scalar cancellation. -/
theorem superLogDetBarrierSPD_eq_zero_of_det_eq
    (X : SPD m) (Y : SPD n)
    (hdet : Matrix.det X.mat = Matrix.det Y.mat) :
    superLogDetBarrierSPD X Y = 0 := by
  rw [superLogDetBarrierSPD_eq_log_ratio, hdet]
  simp [Y.det_ne_zero]

end SPD

end InfoGeometry.NCG
