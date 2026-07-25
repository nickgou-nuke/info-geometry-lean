import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.SplitQuaternionFlows

Finite split-quaternion flow identities.

This module defines a four-coordinate real split-quaternion carrier and proves
norm invariance for the elliptic, hyperbolic, and parabolic one-parameter flow
models.

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `norm_elliptic_flow`
- `norm_hyperbolic_flow`
- `norm_parabolic_flow`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
- No proof of the full classification of one-parameter subgroups of `SL(2, ℝ)` is claimed here.
- No global spacetime model is claimed here.
-/

set_option autoImplicit false

namespace InfoGeometry.Algebra.SplitQuaternionFlows

/--
The split-quaternion, or coquaternion, real carrier with coordinates in the
basis `(1, i, j, k)`.
-/
structure SplitQuaternion where
  w : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

/-- Split quadratic norm `N(q) = w² + x² - y² - z²`. -/
def splitNorm (q : SplitQuaternion) : ℝ :=
  q.w * q.w + q.x * q.x - q.y * q.y - q.z * q.z

/-- Elliptic `SO(2)` flow in the `(1,i)` plane. -/
noncomputable def ellipticFlow (θ : ℝ) : SplitQuaternion :=
  ⟨Real.cos θ, Real.sin θ, 0, 0⟩

/-- Hyperbolic `SO(1,1)` flow in the `(1,j)` plane. -/
noncomputable def hyperbolicFlow (η : ℝ) : SplitQuaternion :=
  ⟨Real.cosh η, 0, Real.sinh η, 0⟩

/-- Parabolic/null flow along the line `1 + T i - T j`. -/
def parabolicFlow (T : ℝ) : SplitQuaternion :=
  ⟨1, T, -T, 0⟩

/-- Elliptic flow has unit split norm. -/
theorem norm_elliptic_flow (θ : ℝ) :
    splitNorm (ellipticFlow θ) = 1 := by
  unfold splitNorm ellipticFlow
  have h : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    calc
      Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ
          = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by ring
      _ = 1 := Real.cos_sq_add_sin_sq θ
  linarith

/-- Hyperbolic flow has unit split norm. -/
theorem norm_hyperbolic_flow (η : ℝ) :
    splitNorm (hyperbolicFlow η) = 1 := by
  unfold splitNorm hyperbolicFlow
  have h : Real.cosh η * Real.cosh η - Real.sinh η * Real.sinh η = 1 := by
    calc
      Real.cosh η * Real.cosh η - Real.sinh η * Real.sinh η
          = Real.cosh η ^ 2 - Real.sinh η ^ 2 := by ring
      _ = 1 := Real.cosh_sq_sub_sinh_sq η
  linarith

/-- Parabolic/null flow has unit split norm. -/
theorem norm_parabolic_flow (T : ℝ) :
    splitNorm (parabolicFlow T) = 1 := by
  unfold splitNorm parabolicFlow
  ring

/-- Compatibility alias for the user's snake-case notation. -/
noncomputable abbrev elliptic_flow := ellipticFlow

/-- Compatibility alias for the user's snake-case notation. -/
noncomputable abbrev hyperbolic_flow := hyperbolicFlow

/-- Compatibility alias for the user's snake-case notation. -/
abbrev parabolic_flow := parabolicFlow

/-- Compatibility alias for the split norm. -/
abbrev norm := splitNorm

end InfoGeometry.Algebra.SplitQuaternionFlows
