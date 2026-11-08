import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Canonical.ZetaFunctionalSymmetryNativeBridge

/-!
# Centered coordinates for the actual entire completed xi

This owner transports the actual pole-removed entire representative into the
centered coordinate `z = s - 1 / 2`.  Its evenness is only the affine transport
of the already-proved reflection law for `entireRiemannXi`; no new functional
equation or zero-location statement is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireCenteredXiBridge

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ZetaFunctionalSymmetryNativeBridge

/-- The actual entire completed xi read in centered coordinates. -/
def actualEntireCenteredXi (z : ℂ) : ℂ :=
  entireRiemannXi ((1 / 2 : ℂ) + z)

/-- The `CompletedXiData` carrier for the actual entire representative. -/
def actualEntireCenteredXiData : CompletedXiData where
  lambda := entireRiemannXi
  xi := actualEntireCenteredXi
  xi_def := by
    intro z
    rfl

@[simp] theorem actualEntireCenteredXiData_lambda (s : ℂ) :
    actualEntireCenteredXiData.lambda s = entireRiemannXi s := rfl

@[simp] theorem actualEntireCenteredXiData_xi (z : ℂ) :
    actualEntireCenteredXiData.xi z = actualEntireCenteredXi z := rfl

@[simp] theorem actualEntireCenteredXi_apply (z : ℂ) :
    actualEntireCenteredXi z = entireRiemannXi ((1 / 2 : ℂ) + z) := rfl

/-- The centered actual entire xi is even. -/
theorem actualEntireCenteredXi_even (z : ℂ) :
    actualEntireCenteredXi (-z) = actualEntireCenteredXi z := by
  unfold actualEntireCenteredXi
  have hcoord :
      (1 / 2 : ℂ) + (-z) = 1 - ((1 / 2 : ℂ) + z) := by
    ring
  rw [hcoord, entireRiemannXi_one_sub]

theorem actualEntireCenteredXiData_even (z : ℂ) :
    actualEntireCenteredXiData.xi z = actualEntireCenteredXiData.xi (-z) := by
  exact (actualEntireCenteredXi_even z).symm

/-- The centered entire readout is real on the imaginary axis. -/
theorem actualEntireCenteredXi_criticalLine_conj (t : ℝ) :
    star (actualEntireCenteredXi (Complex.I * (t : ℂ))) =
      actualEntireCenteredXi (Complex.I * (t : ℂ)) := by
  simpa [actualEntireCenteredXi, add_comm, add_left_comm, add_assoc] using
    entireRiemannXi_criticalLine_conj t

end InfoGeometry.Canonical.ActualEntireCenteredXiBridge
