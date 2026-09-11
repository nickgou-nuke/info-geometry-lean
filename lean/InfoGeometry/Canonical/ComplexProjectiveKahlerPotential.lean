import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Finite scalar Kähler-potential readouts

This owner records the scalar potentials appearing in the compact, disk, and
split logarithmic charts.  It proves only finite real identities and domain
positivity.  Differential-form and manifold-level Kähler claims belong to the
existing geometric owners and are not inferred from these scalar formulas.
-/

noncomputable section

namespace InfoGeometry.Canonical.ComplexProjectiveKahlerPotential

def fubiniStudyPotential (z : ℂ) : ℝ :=
  Real.log (1 + Complex.normSq z)

def diskPotential (w : ℂ) : ℝ :=
  -Real.log (1 - Complex.normSq w)

def splitLogPotential (p q : ℝ) : ℝ :=
  -Real.log (p * q)

theorem fubiniStudy_argument_pos (z : ℂ) :
    0 < 1 + Complex.normSq z := by
  have h : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  linarith

theorem disk_argument_pos {w : ℂ} (h : Complex.normSq w < 1) :
    0 < 1 - Complex.normSq w := by
  linarith

theorem splitLog_argument_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    0 < p * q := mul_pos hp hq

@[simp] theorem fubiniStudyPotential_zero :
    fubiniStudyPotential 0 = 0 := by
  simp [fubiniStudyPotential]

theorem fubiniStudyPotential_conj (z : ℂ) :
    fubiniStudyPotential (starRingEnd ℂ z) =
      fubiniStudyPotential z := by
  simp [fubiniStudyPotential, Complex.normSq]

@[simp] theorem diskPotential_zero :
    diskPotential 0 = 0 := by
  simp [diskPotential]

theorem splitLogPotential_swap (p q : ℝ) :
    splitLogPotential p q = splitLogPotential q p := by
  simp [splitLogPotential, mul_comm]

theorem splitLogPotential_eq_neg_add_log
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    splitLogPotential p q = -(Real.log p + Real.log q) := by
  unfold splitLogPotential
  rw [Real.log_mul hp.ne' hq.ne']


end InfoGeometry.Canonical.ComplexProjectiveKahlerPotential
