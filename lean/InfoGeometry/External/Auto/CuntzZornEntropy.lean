import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.FreedAnomalyCancellation
import InfoGeometry.External.Auto.ProjectiveCuntzToeplitzCARCCR

open Real
open ProjectiveCuntzToeplitzCARCCR
open Freed

noncomputable section

instance : Freed.CommMonoid ℝ where
  mul := (· * ·)
  one := 1
  mul_comm := mul_comm
  mul_assoc := mul_assoc

structure BogoliubovTransform where
  squeeze : ℝ
  tilt : ℝ

-- "squeeze" and "tilt" map to phase 1 (attachment) and phase 0 (detachment)
def bogoliubov_phase (b : BogoliubovTransform) : ℕ :=
  if b.squeeze = 0 ∧ b.tilt = 0 then 0 else 1

def frame_entropy (Z : ZornMatrix ℝ) : ℝ :=
  Real.log |ZornMatrix.det Z|

def mobius_parity_flip (Z : ZornMatrix ℝ) : ZornMatrix ℝ :=
  ⟨-Z.val⟩

theorem cuntz_entropy_balance (Z : ZornMatrix ℝ) :
    ZornMatrix.det (mobius_parity_flip Z) = - ZornMatrix.det Z ∧
    frame_entropy (mobius_parity_flip Z) = frame_entropy Z := by
  constructor
  · rfl
  · unfold frame_entropy
    unfold mobius_parity_flip
    unfold ZornMatrix.det
    rw [abs_neg]
