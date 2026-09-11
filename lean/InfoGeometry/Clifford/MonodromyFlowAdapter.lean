import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitQuaternionFlowCoordinates
import Mathlib.Tactic

noncomputable section

/-!
# MonodromyFlowAdapter

Bridge from logarithmic-CFT monodromy to the existing split-quaternion
parabolic-flow lane.

The bridge is intentionally conservative.  The LCFT monodromy is a complex
`2 × 2` matrix with an independent scalar phase.  The split-quaternion flow is
the real parabolic coordinate curve `1 + T (i - j)`.  They are connected here
by the common nilpotent law: additive flow parameters compose linearly because
the nilpotent generator squares to zero.
-/

namespace InfoGeometry.Clifford.MonodromyFlowAdapter

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

/-- The complex nilpotent generator used by the LCFT monodromy matrix. -/
abbrev infinitesimalNullGenerator : Matrix (Fin 2) (Fin 2) ℂ :=
  epsilon

/-- Complex parabolic flow step `1 + t epsilon`. -/
def lcftParabolicFlowStep (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + t • infinitesimalNullGenerator

/-- The nilpotent generator used by the complex parabolic flow is square-zero. -/
theorem infinitesimalNullGenerator_sq_zero :
    infinitesimalNullGenerator * infinitesimalNullGenerator = 0 := by
  simpa [infinitesimalNullGenerator] using (epsilon_sq)

/--
The complex parabolic flow has additive composition law.  This is the matrix
analogue of moving along a horocycle/null shear.
-/
theorem lcftParabolicFlow_composition (t₁ t₂ : ℂ) :
    lcftParabolicFlowStep t₁ * lcftParabolicFlowStep t₂ =
      lcftParabolicFlowStep (t₁ + t₂) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [lcftParabolicFlowStep, infinitesimalNullGenerator, epsilon,
      jordanNilpotent, Matrix.mul_apply]
  all_goals ring

/-- Alias for the additive parabolic-flow law. -/
theorem parabolicTimeFlow_add (t₁ t₂ : ℂ) :
    lcftParabolicFlowStep t₁ * lcftParabolicFlowStep t₂ =
      lcftParabolicFlowStep (t₁ + t₂) :=
  lcftParabolicFlow_composition t₁ t₂

/-- Repeated complex parabolic flow is just flow at the accumulated parameter. -/
theorem lcftParabolicFlow_pow (t : ℂ) (n : ℕ) :
    lcftParabolicFlowStep t ^ n =
      lcftParabolicFlowStep ((n : ℂ) * t) := by
  simpa [lcftParabolicFlowStep, infinitesimalNullGenerator] using
    (one_plus_c_epsilon_pow t n)

/-- Alias for the discrete power law of the parabolic flow. -/
theorem parabolicTimeFlow_pow (t : ℂ) (n : ℕ) :
    lcftParabolicFlowStep t ^ n = lcftParabolicFlowStep ((n : ℂ) * t) :=
  lcftParabolicFlow_pow t n

/--
One Hadjiivanov monodromy wrap is a scalar conformal phase times the complex
parabolic nilpotent flow at `logShearBase = -2πi`.
-/
theorem monodromy_is_parabolic_flow (h : ℂ) :
    hadjiivanovMonodromy h =
      lcftPhase h • lcftParabolicFlowStep logShearBase := by
  simpa [lcftParabolicFlowStep, infinitesimalNullGenerator] using
    hadjiivanovMonodromy_decomp h

/--
After `n` wraps, the scalar phase multiplies as `phase^n`, while the nilpotent
flow parameter accumulates additively as `n * logShearBase`.
-/
theorem monodromy_pow_is_compounded_flow (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n • lcftParabolicFlowStep ((n : ℂ) * logShearBase) := by
  simpa [lcftParabolicFlowStep, infinitesimalNullGenerator] using
    hadjiivanovMonodromy_pow_binomial h n

/-- Lower/scattering-convention complex parabolic flow step. -/
def lowerLcftParabolicFlowStep (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + t • lowerJordanNilpotent

/--
In the lower-triangular scattering convention, repeated logarithmic monodromy
wraps still compound as a scalar phase times additive parabolic flow.
-/
theorem lower_monodromy_pow_is_compounded_flow (h : ℂ) (n : ℕ) :
    lowerHadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n • lowerLcftParabolicFlowStep ((n : ℂ) * logShearBase) := by
  simpa [lowerLcftParabolicFlowStep] using
    lowerHadjiivanovMonodromy_pow_winding h n

/-- Real split-quaternion parabolic flow readout from the existing coordinate lane. -/
def splitQuaternionParabolicFlowStep (T : ℝ) : SplitQuaternion :=
  _root_.InfoGeometry.Clifford.SplitQuaternionFlowCoordinates.parabolicFlow T

/--
The split-quaternion parabolic coordinate flow also composes by addition of
parameters.  This is the real `1 + T(i-j)` counterpart of the LCFT epsilon law.
-/
theorem splitQuaternionParabolicFlow_composition (T₁ T₂ : ℝ) :
    splitQuaternionParabolicFlowStep T₁ * splitQuaternionParabolicFlowStep T₂ =
      splitQuaternionParabolicFlowStep (T₁ + T₂) := by
  ext
  all_goals
    simp [splitQuaternionParabolicFlowStep,
      _root_.InfoGeometry.Clifford.SplitQuaternionFlowCoordinates.parabolicFlow,
      _root_.InfoGeometry.Clifford.sqMul]
  all_goals ring

/-- The split-quaternion parabolic flow is norm-one, inherited from the owner lane. -/
theorem norm_splitQuaternionParabolicFlowStep (T : ℝ) :
    norm (splitQuaternionParabolicFlowStep T) = 1 := by
  exact _root_.InfoGeometry.Clifford.SplitQuaternionFlowCoordinates.norm_parabolicFlow T

/--
Real winding readout: `n` discrete wraps in the split-quaternion parabolic lane
accumulate to the parameter `(n : ℝ) * T`.
-/
theorem splitQuaternionParabolicFlow_winding (T : ℝ) (n : ℕ) :
    _root_.InfoGeometry.Clifford.SplitQuaternionFlowCoordinates.parabolicFlow ((n : ℝ) * T) =
      splitQuaternionParabolicFlowStep ((n : ℝ) * T) := by
  rfl

end InfoGeometry.Clifford.MonodromyFlowAdapter
