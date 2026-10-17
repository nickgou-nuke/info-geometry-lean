/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Convex.RadialLogBarrier
import InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics
import InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge
import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Canonical.ParaKahlerGradedFockCAR

/-!
# Radial Quantization, Log-Generating Scale Invariance, and the 5-Graded Conformal Cylinder

This module formalizes the finite-dimensional radial-quantization dictionary connecting the
positive radial cone $(0, \infty) \times S^1$ to the translation-invariant cylinder
$\mathbb{R}_t \times S^1$ across five Causal Poset archetypes:

1. **Archetype I — Radial Quantization Bijection ($t = \ln r \leftrightarrow r = e^t$),
   Conformal Cone-to-Cylinder Metric Equivalence & Radial Normalization (`sphericalNorm2`)**:
   - Defines `radialTime r = RadialLogBarrier.radialTau r` and `coneRadius t = Real.exp t`,
     proving `radialTime_coneRadius`, the multiplicative-to-additive homomorphism
     `radialTime_mul_scale`, and the cone-to-cylinder log-barrier and Legendre-dual bridges
     `radialBarrier_coneRadius_eq_tauBarrier` and `coneRadius_mul_radialDualNorm_eq_tauDual`.
   - Defines `coneLineElement` and `cylinderLineElement`, proving the conformal equivalence
     `coneLineElement r dr dOmega = r ^ 2 * cylinderLineElement (dr / r) dOmega`, its cylinder
     pullback `Real.exp (2 * t) * cylinderLineElement dt dOmega`, and its bridge to
     `RotaryAttentionSpiralDynamics.poincareHalfPlaneMetric`.
   - Defines the 2D vector radial log-time `vecRadialTime2` and proves that unit radial
     normalization satisfies `sphericalNorm2 1 v = Real.exp (-vecRadialTime2 v) • v`.

2. **Archetype II — Log-Generating Scale-Invariant Potential ($\Phi(\lambda w) = \Phi(w) + \ln \lambda$)
   & Degree-$0$ Scale Invariance of the Simplex Projection, Chi-Squared Metric, and
   Amari–Chentsov Cubic Tensor**:
   - Defines `conePartitionSum` and `logConePotential`, proving positivity `conePartitionSum_pos`
     and the additive log-shift laws under positive cone rescaling `w ↦ lam • w` and cylinder
     time translation `w ↦ exp dt • w`.
   - Defines the simplex projection `coneNormalizedState` and proves positivity
     `coneNormalizedState_pos` together with exact degree-$0$ scale invariance under
     `w ↦ lam • w` of `coneNormalizedState`, the chi-squared inner product
     `chiSquaredInner (coneNormalizedState _)`, and the Amari–Chentsov cubic skewness tensor
     `(chiSquaredDualManifold (coneNormalizedState _) _).diff_g`, as well as simultaneous
     degree-$1$ homogeneity of `chiSquaredInner` and `chiSquaredCubicSkewness`.

3. **Archetype III — Unfolding the Logarithmic Spiral into a Constant-Pitch Cylinder Helix**:
   - Defines `cylinderHelixTime`, `cylinderHelixAngle`, and `cylinderToConeMap`, proving that
     pushing a linear cylinder helix forward by `cylinderToConeMap` recovers
     `RotaryAttentionSpiralDynamics.spiralTrajectory`, while pulling `spiralTrajectory` back
     by `vecRadialTime2` yields an exact affine line `radialTime a + b * ω * τ`.

4. **Archetype IV — 5-Graded Super-Grassmannian Conformal Weight Representation
   ($r^{-2}, r^{-1}, r^0, r^{+1}, r^{+2}$)**:
   - Assigns integer conformal weights `gradeWeight : ConformalGrade → ℤ` (`-2, -1, 0, 1, 2`)
     compatible with `ConformalGrade.swap` (`gradeWeight_swap`), defines `gradeTimeScale` and
     `gradeRadialScale`, proves the cone-cylinder weight dictionary, additive group law, and
     inversion duality, and bridges directly to `FiveGradedConformalInversion`
     (`fiveGradedInversion_gradeWeight_theta`, `fiveGradedInversion_gradeTimeScale_theta`,
     `fiveGradedInversion_gradeTimeScale_mul_theta`, and `fiveGradedInversion_centerSet_scale_one`).

5. **Archetype V — Dilated Para-Kähler Fock CAR Superbracket Invariance & 5-Sector Dilatation Action**:
   - Defines the oppositely weighted creation and annihilation endomorphisms
     `dilatedCreateEnd` (grade `+1`, weight $e^{+t}$) and `dilatedAnnihilateEnd` (grade `-1`,
     weight $e^{-t}$) on `FockExteriorEnvelope K`, proving that their odd-odd $\mathbb{Z}_2$
     superbracket is strictly invariant under radial cylinder dilatation $t$ and equals the
     grade-$0$ central pairing $g(\alpha, u) \cdot \mathrm{id}$.
   - Defines the 5-graded direct-sum dilatation action `fiveGradedDilatation` and proves its
     one-parameter group law and fixed-point property on the grade-$0$ center.

## Scope Note

1. `radialTime` (`RadialLogBarrier.radialTau`) and `coneRadius` (`Real.exp`) form a mutually
   inverse bijection between the positive ray $(0, \infty)$ and $\mathbb{R}$.
2. `coneNormalizedState`, `chiSquaredInner`, and `chiSquaredCubicSkewness` are finite-dimensional
   algebraic expressions whose radial scale invariance under $w \mapsto \lambda w$ is proved by
   homogeneous factor cancellation rather than Fréchet differentiation on a manifold.
3. The 5-graded dilatation and dilated Para-Kähler CAR superbracket invariance are
   finite-dimensional module and exterior-algebra theorems, not infinite-dimensional Virasoro
   CFT operator-product expansions.
-/

noncomputable section

namespace InfoGeometry.Canonical.RadialQuantizationFiveGradedCylinder

open BigOperators Finset
open InfoGeometry.Convex
open InfoGeometry.QuantumContext
open InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.SuperGrassmannianProjectorEnvelope
open InfoGeometry.Canonical.ParaKahlerGradedFockCAR

variable {ι : Type*}

/-! ### Private Scalar Arithmetic Helpers (Trap T16 Safe) -/

private lemma exp_sq_eq_exp_two_mul (τ : ℝ) :
    (Real.exp τ) ^ (2 : ℕ) = Real.exp (2 * τ) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

private lemma mul_two_mul_exp_eq_two_mul_exp_two (τ : ℝ) :
    Real.exp τ * (2 * Real.exp τ) = 2 * Real.exp (2 * τ) := by
  calc
    Real.exp τ * (2 * Real.exp τ) = 2 * (Real.exp τ * Real.exp τ) := by ring
    _ = 2 * (Real.exp τ) ^ (2 : ℕ) := by rw [sq]
    _ = 2 * Real.exp (2 * τ) := by rw [exp_sq_eq_exp_two_mul]

private lemma cone_eq_r_sq_mul_cylinder_scalar (r dr dOmega : ℝ) (hr : r ≠ 0) :
    dr ^ 2 + r ^ 2 * dOmega ^ 2 = r ^ 2 * ((dr / r) ^ 2 + dOmega ^ 2) := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [div_pow, mul_add, mul_div_cancel₀ _ hr2]

private lemma cone_at_exp_scalar (t dt dOmega : ℝ) :
    (Real.exp t * dt) ^ 2 + (Real.exp t) ^ 2 * dOmega ^ 2 =
      Real.exp (2 * t) * (dt ^ 2 + dOmega ^ 2) := by
  calc
    (Real.exp t * dt) ^ 2 + (Real.exp t) ^ 2 * dOmega ^ 2 =
        (Real.exp t) ^ 2 * (dt ^ 2 + dOmega ^ 2) := by ring
    _ = Real.exp (2 * t) * (dt ^ 2 + dOmega ^ 2) := by rw [exp_sq_eq_exp_two_mul]

private lemma cylinder_eq_poincare_scalar (r dr dOmega : ℝ) (hr : r ≠ 0) :
    (dr / r) ^ 2 + dOmega ^ 2 = ((dr) ^ 2 + (r * dOmega) ^ 2) / (r ^ 2) := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [div_pow, add_div]
  congr 1
  have hmul : (r * dOmega) ^ 2 = dOmega ^ 2 * r ^ 2 := by ring
  rw [hmul, mul_div_cancel_right₀ _ hr2]

private lemma scale_div_scale_cancel (lam a b : ℝ) (hlam : lam ≠ 0) :
    (lam * a) / (lam * b) = a / b :=
  mul_div_mul_left a b hlam

private lemma chi_simultaneous_scale_term (lam r u v : ℝ) (hlam : lam ≠ 0) :
    (lam * u) * (lam * v) / (lam * r) = lam * (u * v / r) := by
  have hnum : (lam * u) * (lam * v) = lam * (lam * (u * v)) := by ring
  rw [hnum, mul_div_mul_left _ _ hlam, mul_div_assoc]

private lemma cubic_simultaneous_scale_term (lam r x y z : ℝ) (hlam : lam ≠ 0) :
    (lam * x) * (lam * y) * (lam * z) / ((lam * r) * (lam * r)) =
      lam * (x * y * z / (r * r)) := by
  have hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  have hnum : (lam * x) * (lam * y) * (lam * z) = lam ^ 2 * (lam * (x * y * z)) := by ring
  have hden : (lam * r) * (lam * r) = lam ^ 2 * (r * r) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hlam2, mul_div_assoc]

private lemma helix_time_of_angle_scalar (t₀ b ω θ : ℝ) :
    t₀ + b * (θ / ω) = t₀ + (b / ω) * θ := by
  ring

private lemma int_mul_add_distrib (w : ℤ) (t s : ℝ) :
    (w : ℝ) * (t + s) = (w : ℝ) * t + (w : ℝ) * s := by
  ring

private lemma neg_int_mul_eq (w : ℤ) (t : ℝ) :
    ((-w : ℤ) : ℝ) * t = -((w : ℝ) * t) := by
  push_cast
  ring

private lemma exp_grade_negTwo_eq_zpow (t : ℝ) :
    Real.exp (((-2 : ℤ) : ℝ) * t) = (Real.exp t) ^ (-2 : ℤ) := by
  have h : ((-2 : ℤ) : ℝ) * t = -(2 * t) := by
    push_cast
    ring
  rw [h, Real.exp_neg, ← exp_sq_eq_exp_two_mul, zpow_neg, zpow_two, sq]

private lemma exp_grade_negOne_eq_zpow (t : ℝ) :
    Real.exp (((-1 : ℤ) : ℝ) * t) = (Real.exp t) ^ (-1 : ℤ) := by
  have h : ((-1 : ℤ) : ℝ) * t = -t := by
    push_cast
    ring
  rw [h, Real.exp_neg, zpow_neg, zpow_one]

private lemma exp_grade_zero_eq_zpow (t : ℝ) :
    Real.exp (((0 : ℤ) : ℝ) * t) = (Real.exp t) ^ (0 : ℤ) := by
  rw [Int.cast_zero, zero_mul, Real.exp_zero, zpow_zero]

private lemma exp_grade_posOne_eq_zpow (t : ℝ) :
    Real.exp (((1 : ℤ) : ℝ) * t) = (Real.exp t) ^ (1 : ℤ) := by
  rw [Int.cast_one, one_mul, zpow_one]

private lemma exp_grade_posTwo_eq_zpow (t : ℝ) :
    Real.exp (((2 : ℤ) : ℝ) * t) = (Real.exp t) ^ (2 : ℤ) := by
  have h : ((2 : ℤ) : ℝ) * t = 2 * t := by
    push_cast
    ring
  rw [h, ← exp_sq_eq_exp_two_mul, zpow_two, sq]

/-!
### Archetype I — Radial Quantization Bijection ($t = \ln r \leftrightarrow r = e^t$), Conformal Cone-to-Cylinder Metric Equivalence & Radial Normalization (`sphericalNorm2`)
-/

/-- Radial quantization cylinder time $t = \ln r$ (wrapping `RadialLogBarrier.radialTau`). -/
def radialTime (r : ℝ) : ℝ :=
  RadialLogBarrier.radialTau r

/-- Punctured-cone radius $r = e^t$ recovered from the cylinder time coordinate $t$. -/
def coneRadius (t : ℝ) : ℝ :=
  Real.exp t

/-- Taking `radialTime` of `coneRadius t` recovers the cylinder time $t$ for all $t \in \mathbb{R}$. -/
theorem radialTime_coneRadius (t : ℝ) :
    radialTime (coneRadius t) = t := by
  dsimp [radialTime, coneRadius, RadialLogBarrier.radialTau]
  exact Real.log_exp t

/-- Multiplicative radial dilatations $r \mapsto \lambda r$ ($0 < \lambda, 0 < r$) become
additive time translations $t \mapsto t + \ln \lambda$ on the cylinder. -/
theorem radialTime_mul_scale {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) :
    radialTime (lam * r) = radialTime r + radialTime lam := by
  dsimp [radialTime, RadialLogBarrier.radialTau]
  rw [Real.log_mul (ne_of_gt hlam) (ne_of_gt hr), add_comm]

/-- Additive time translations $t \mapsto t + \Delta t$ on the cylinder become multiplicative
radial rescalings $e^{t + \Delta t} = e^{\Delta t} e^t$ on the cone. -/
theorem coneRadius_add (t dt : ℝ) :
    coneRadius (t + dt) = coneRadius dt * coneRadius t := by
  dsimp [coneRadius]
  rw [Real.exp_add, mul_comm]

/-- **Cone-to-Cylinder Log-Barrier Bridge**:
Evaluating `RadialLogBarrier.radialBarrier` at `coneRadius τ = exp τ` recovers the
$\tau$-coordinate barrier `RadialLogBarrier.tauBarrier τ = -log(1 - exp(2τ))`. -/
theorem radialBarrier_coneRadius_eq_tauBarrier (τ : ℝ) :
    RadialLogBarrier.radialBarrier (coneRadius τ) =
      RadialLogBarrier.tauBarrier τ := by
  dsimp [RadialLogBarrier.radialBarrier, RadialLogBarrier.tauBarrier, coneRadius]
  rw [exp_sq_eq_exp_two_mul]

/-- **Cone-to-Cylinder Legendre Dual Coordinate Bridge**:
Scaling the radial Legendre dual coordinate `RadialLogBarrier.radialDualNorm (coneRadius τ)`
by the radial factor `coneRadius τ` yields the cylinder dual variable
`RadialLogBarrier.tauDual τ = 2 exp(2τ) / (1 - exp(2τ))`. -/
theorem coneRadius_mul_radialDualNorm_eq_tauDual (τ : ℝ) :
    coneRadius τ * RadialLogBarrier.radialDualNorm (coneRadius τ) =
      RadialLogBarrier.tauDual τ := by
  dsimp [RadialLogBarrier.radialDualNorm, RadialLogBarrier.tauDual, coneRadius]
  rw [← mul_div_assoc, mul_two_mul_exp_eq_two_mul_exp_two, exp_sq_eq_exp_two_mul]

/-- Flat polar line element on the punctured cone: $ds_{\mathrm{cone}}^2 = dr^2 + r^2 d\Omega^2$. -/
def coneLineElement (r dr dOmega : ℝ) : ℝ :=
  dr ^ 2 + r ^ 2 * dOmega ^ 2

/-- Translation-invariant product line element on the cylinder $\mathbb{R}_t \times S^1$:
$ds_{\mathrm{cyl}}^2 = dt^2 + d\Omega^2$. -/
def cylinderLineElement (dt dOmega : ℝ) : ℝ :=
  dt ^ 2 + dOmega ^ 2

/-- **Conformal Cone-to-Cylinder Metric Identity**:
For $r \ne 0$ and $dt = dr / r$, the flat cone metric factors as the conformal scale factor
$r^2$ times the cylinder metric:
$dr^2 + r^2 d\Omega^2 = r^2 ((dr / r)^2 + d\Omega^2)$. -/
theorem coneLineElement_eq_r_sq_mul_cylinder (r dr dOmega : ℝ) (hr : r ≠ 0) :
    coneLineElement r dr dOmega = r ^ 2 * cylinderLineElement (dr / r) dOmega :=
  cone_eq_r_sq_mul_cylinder_scalar r dr dOmega hr

/-- In cylinder coordinates $r = e^t$ and $dr = e^t dt$, the cone line element equals
$e^{2t} (dt^2 + d\Omega^2)$. -/
theorem coneLineElement_at_coneRadius (t dt dOmega : ℝ) :
    coneLineElement (coneRadius t) (coneRadius t * dt) dOmega =
      Real.exp (2 * t) * cylinderLineElement dt dOmega :=
  cone_at_exp_scalar t dt dOmega

/-- The cylinder line element with $dt = dr / r$ coincides with
`RotaryAttentionSpiralDynamics.poincareHalfPlaneMetric r dr (r * dOmega)`. -/
theorem cylinderLineElement_eq_poincareHalfPlaneMetric (r dr dOmega : ℝ) (hr : r ≠ 0) :
    cylinderLineElement (dr / r) dOmega =
      RotaryAttentionSpiralDynamics.poincareHalfPlaneMetric r dr (r * dOmega) :=
  cylinder_eq_poincare_scalar r dr dOmega hr

/-- For any non-zero vector $v \in \mathbb{R}^2$, its squared Euclidean norm `vecNormSq2 v` is
strictly positive. -/
theorem vecNormSq2_pos_of_ne_zero (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    0 < RotaryAttentionSpiralDynamics.vecNormSq2 v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  rw [RotaryAttentionSpiralDynamics.vecNormSq2_eq_add]
  fin_cases i
  · exact add_pos_of_pos_of_nonneg (mul_self_pos.mpr hi) (mul_self_nonneg (v 1))
  · exact add_pos_of_nonneg_of_pos (mul_self_nonneg (v 0)) (mul_self_pos.mpr hi)

/-- Logarithmic radial time $t(v) = \ln \sqrt{\|v\|^2}$ of a 2D latent vector $v \in \mathbb{R}^2$. -/
def vecRadialTime2 (v : Fin 2 → ℝ) : ℝ :=
  radialTime (Real.sqrt (RotaryAttentionSpiralDynamics.vecNormSq2 v))

/-- Exponentiating `vecRadialTime2 v` for $v \ne 0$ recovers the Euclidean norm
$\sqrt{\|v\|^2}$. -/
theorem coneRadius_vecRadialTime2 (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    coneRadius (vecRadialTime2 v) =
      Real.sqrt (RotaryAttentionSpiralDynamics.vecNormSq2 v) :=
  RadialLogBarrier.exp_radialTau (Real.sqrt_pos.mpr (vecNormSq2_pos_of_ne_zero v hv))

/-- **Radial Normalization as Cylinder Time-Zero Projection**:
For any non-zero vector $v \in \mathbb{R}^2$, unit spherical normalization
`sphericalNorm2 1 v` is multiplication by $e^{-t(v)}$:
$\mathrm{sphericalNorm2}(1, v) = e^{-\mathrm{vecRadialTime2}(v)} v$. -/
theorem sphericalNorm2_unit_eq_exp_neg_vecRadialTime2_smul
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    RotaryAttentionSpiralDynamics.sphericalNorm2 1 v =
      Real.exp (-vecRadialTime2 v) • v := by
  dsimp [RotaryAttentionSpiralDynamics.sphericalNorm2]
  rw [Real.exp_neg, ← coneRadius, coneRadius_vecRadialTime2 v hv, one_div]

/-!
### Archetype II — Log-Generating Scale-Invariant Potential ($\Phi(\lambda w) = \Phi(w) + \ln \lambda$) & Degree-$0$ Scale Invariance of the Simplex Projection, Chi-Squared Metric, and Amari–Chentsov Cubic Tensor
-/

/-- Total unnormalized mass $Z(w) = \sum_i w_i$ on a finite cone carrier. -/
def conePartitionSum [Fintype ι] (w : ι → ℝ) : ℝ :=
  ∑ i, w i

/-- Logarithmic generating potential $\Phi(w) = \ln(\sum_i w_i)$ on the unnormalized cone. -/
def logConePotential [Fintype ι] (w : ι → ℝ) : ℝ :=
  radialTime (conePartitionSum w)

/-- Strict positivity of `conePartitionSum w` on a nonempty finite state space when every
component $w_i$ is strictly positive. -/
theorem conePartitionSum_pos [Fintype ι] [Nonempty ι] {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) :
    0 < conePartitionSum w := by
  dsimp [conePartitionSum]
  exact Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty

/-- Homogeneous degree-$1$ scaling of `conePartitionSum`: $Z(\lambda w) = \lambda Z(w)$. -/
theorem conePartitionSum_smul [Fintype ι] (lam : ℝ) (w : ι → ℝ) :
    conePartitionSum (fun i => lam * w i) = lam * conePartitionSum w := by
  dsimp [conePartitionSum]
  exact (Finset.mul_sum univ w lam).symm

/-- **Additive Log-Shift Law under Radial Rescaling**:
Rescaling $w \mapsto \lambda w$ ($0 < \lambda$) shifts the logarithmic potential by a constant
$\ln \lambda$: $\Phi(\lambda w) = \Phi(w) + \ln \lambda$. -/
theorem logConePotential_smul_shift [Fintype ι] (lam : ℝ) (w : ι → ℝ)
    (hlam : 0 < lam) (hw : 0 < conePartitionSum w) :
    logConePotential (fun i => lam * w i) = logConePotential w + radialTime lam := by
  dsimp [logConePotential]
  rw [conePartitionSum_smul, radialTime_mul_scale hlam hw]

/-- On a nonempty finite carrier, componentwise positivity `∀ i, 0 < w i` automatically
discharges `0 < conePartitionSum w` in the additive log-shift law. -/
theorem logConePotential_smul_shift_of_pos [Fintype ι] [Nonempty ι]
    (lam : ℝ) (w : ι → ℝ) (hlam : 0 < lam) (hw : ∀ i, 0 < w i) :
    logConePotential (fun i => lam * w i) = logConePotential w + radialTime lam :=
  logConePotential_smul_shift lam w hlam (conePartitionSum_pos hw)

/-- Under cylinder time translation $w \mapsto e^{\Delta t} w$, the logarithmic potential shifts
linearly by $\Delta t$: $\Phi(e^{\Delta t} w) = \Phi(w) + \Delta t$. -/
theorem logConePotential_exp_shift [Fintype ι] (dt : ℝ) (w : ι → ℝ)
    (hw : 0 < conePartitionSum w) :
    logConePotential (fun i => Real.exp dt * w i) = logConePotential w + dt := by
  rw [logConePotential_smul_shift (Real.exp dt) w (Real.exp_pos dt) hw]
  dsimp [radialTime, RadialLogBarrier.radialTau]
  rw [Real.log_exp]

/-- Simplex projection (normalized state):
$\rho_i(w) = w_i / \sum_j w_j$. -/
def coneNormalizedState [Fintype ι] (w : ι → ℝ) (i : ι) : ℝ :=
  w i / conePartitionSum w

/-- Strict positivity of `coneNormalizedState w i` on a nonempty finite carrier when every
component $w_j$ is strictly positive. -/
theorem coneNormalizedState_pos [Fintype ι] [Nonempty ι] {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (i : ι) :
    0 < coneNormalizedState w i :=
  div_pos (hw i) (conePartitionSum_pos hw)

/-- Cubic Amari–Chentsov skewness tensor $T_\rho(X, Y, Z) = \sum_i X_i Y_i Z_i / \rho_i^2$
matching `(chiSquaredDualManifold ρ hρ).diff_g`. -/
def chiSquaredCubicSkewness [Fintype ι] (ρ X Y Z : ι → ℝ) : ℝ :=
  ∑ i, X i * Y i * Z i / (ρ i * ρ i)

/-- `chiSquaredCubicSkewness` coincides definitionally with the `diff_g` field of
`UnifiedInfoGeometryPetzFockBridge.chiSquaredDualManifold`. -/
theorem chiSquaredCubicSkewness_eq_dualManifold_diff_g [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (X Y Z : ι → ℝ) :
    chiSquaredCubicSkewness ρ X Y Z =
      (chiSquaredDualManifold ρ hρ).diff_g X Y Z := rfl

/-- **Degree-$0$ Scale Invariance of the Normalized State**:
For any $\lambda \ne 0$, rescaling $w \mapsto \lambda w$ leaves `coneNormalizedState` invariant. -/
theorem coneNormalizedState_scale_invariant [Fintype ι]
    (lam : ℝ) (hlam : lam ≠ 0) (w : ι → ℝ) (i : ι) :
    coneNormalizedState (fun j => lam * w j) i = coneNormalizedState w i := by
  dsimp [coneNormalizedState]
  rw [conePartitionSum_smul]
  exact scale_div_scale_cancel lam (w i) (conePartitionSum w) hlam

/-- Function-level scale invariance of `coneNormalizedState` for $\lambda \ne 0$. -/
theorem coneNormalizedState_scale_invariant_fun [Fintype ι]
    (lam : ℝ) (hlam : lam ≠ 0) (w : ι → ℝ) :
    coneNormalizedState (fun j => lam * w j) = coneNormalizedState w := by
  funext i
  exact coneNormalizedState_scale_invariant lam hlam w i

/-- **Degree-$0$ Scale Invariance of the Chi-Squared Metric on `coneNormalizedState`**:
By homogeneous factor cancellation in `coneNormalizedState`, the induced chi-squared metric
`chiSquaredInner (coneNormalizedState w)` is invariant under $w \mapsto \lambda w$ ($\lambda \ne 0$). -/
theorem chiSquaredInner_coneNormalizedState_scale_invariant [Fintype ι]
    (lam : ℝ) (hlam : lam ≠ 0) (w u v : ι → ℝ) :
    chiSquaredInner (coneNormalizedState (fun j => lam * w j)) u v =
      chiSquaredInner (coneNormalizedState w) u v := by
  rw [coneNormalizedState_scale_invariant_fun lam hlam w]

/-- **Degree-$0$ Scale Invariance of the Amari–Chentsov Cubic Skewness Tensor on `coneNormalizedState`**:
For any $\lambda \ne 0$, the cubic skewness tensor on `coneNormalizedState` is invariant under
$w \mapsto \lambda w$. -/
theorem chiSquaredCubicSkewness_coneNormalizedState_scale_invariant [Fintype ι]
    (lam : ℝ) (hlam : lam ≠ 0) (w X Y Z : ι → ℝ) :
    chiSquaredCubicSkewness (coneNormalizedState (fun j => lam * w j)) X Y Z =
      chiSquaredCubicSkewness (coneNormalizedState w) X Y Z := by
  rw [coneNormalizedState_scale_invariant_fun lam hlam w]

/-- Scale invariance of `(chiSquaredDualManifold (coneNormalizedState _)).diff_g` under positive
cone rescaling $0 < \lambda$ for any positive weight vector `hw : ∀ i, 0 < w i`, discharging
both simplex positivity obligations internally via `coneNormalizedState_pos`. -/
theorem chiSquaredDualManifold_diff_g_coneNormalizedState_scale_invariant
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lam : ℝ) (hlam : 0 < lam) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (X Y Z : ι → ℝ) :
    (chiSquaredDualManifold (coneNormalizedState (fun j => lam * w j))
        (coneNormalizedState_pos (fun j => mul_pos hlam (hw j)))).diff_g X Y Z =
      (chiSquaredDualManifold (coneNormalizedState w)
        (coneNormalizedState_pos hw)).diff_g X Y Z := by
  rw [← chiSquaredCubicSkewness_eq_dualManifold_diff_g _
      (coneNormalizedState_pos (fun j => mul_pos hlam (hw j))),
    ← chiSquaredCubicSkewness_eq_dualManifold_diff_g _
      (coneNormalizedState_pos hw)]
  exact chiSquaredCubicSkewness_coneNormalizedState_scale_invariant
    lam (ne_of_gt hlam) w X Y Z

/-- Simultaneous cone rescaling $(\rho, u, v) \mapsto (\lambda \rho, \lambda u, \lambda v)$ scales
`chiSquaredInner` homogeneously of degree $1$. -/
theorem chiSquaredInner_simultaneous_scale [Fintype ι]
    (lam : ℝ) (hlam : lam ≠ 0) (ρ u v : ι → ℝ) :
    chiSquaredInner (fun i => lam * ρ i) (fun i => lam * u i) (fun i => lam * v i) =
      lam * chiSquaredInner ρ u v := by
  dsimp [chiSquaredInner]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => chi_simultaneous_scale_term lam (ρ i) (u i) (v i) hlam)

/-- Simultaneous cone rescaling $(\rho, X, Y, Z) \mapsto (\lambda \rho, \lambda X, \lambda Y, \lambda Z)$
scales the cubic skewness tensor `chiSquaredCubicSkewness` homogeneously of degree $1$. -/
theorem chiSquaredCubicSkewness_simultaneous_scale [Fintype ι]
    (lam : ℝ) (hlam : lam ≠ 0) (ρ X Y Z : ι → ℝ) :
    chiSquaredCubicSkewness (fun i => lam * ρ i)
        (fun i => lam * X i) (fun i => lam * Y i) (fun i => lam * Z i) =
      lam * chiSquaredCubicSkewness ρ X Y Z := by
  dsimp [chiSquaredCubicSkewness]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl
    (fun i _ => cubic_simultaneous_scale_term lam (ρ i) (X i) (Y i) (Z i) hlam)

/-- Simultaneous positive cone rescaling scales `(chiSquaredDualManifold _).diff_g`
homogeneously of degree $1$, deriving the rescaled positivity witness internally. -/
theorem chiSquaredDualManifold_diff_g_simultaneous_scale
    [Fintype ι] [DecidableEq ι]
    (lam : ℝ) (hlam : 0 < lam) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i)
    (X Y Z : ι → ℝ) :
    (chiSquaredDualManifold (fun i => lam * ρ i) (fun i => mul_pos hlam (hρ i))).diff_g
        (fun i => lam * X i) (fun i => lam * Y i) (fun i => lam * Z i) =
      lam * (chiSquaredDualManifold ρ hρ).diff_g X Y Z := by
  rw [← chiSquaredCubicSkewness_eq_dualManifold_diff_g
      (fun i => lam * ρ i) (fun i => mul_pos hlam (hρ i)),
    ← chiSquaredCubicSkewness_eq_dualManifold_diff_g ρ hρ]
  exact chiSquaredCubicSkewness_simultaneous_scale lam (ne_of_gt hlam) ρ X Y Z

/-!
### Archetype III — Unfolding the Logarithmic Spiral into a Constant-Pitch Cylinder Helix
-/

/-- Linear radial log-time trajectory on the cylinder: $t(\tau) = t_0 + b \tau$. -/
def cylinderHelixTime (t₀ b τ : ℝ) : ℝ :=
  t₀ + b * τ

/-- Linear angular trajectory on the cylinder: $\theta(\tau) = \omega \tau$. -/
def cylinderHelixAngle (ω τ : ℝ) : ℝ :=
  ω * τ

/-- Radial quantization map from cylinder coordinates $(t, \theta) \in \mathbb{R} \times S^1$
to the 2D punctured cone: $(t, \theta) \mapsto e^t R(\theta) v_0$. -/
def cylinderToConeMap (t θ : ℝ) (v₀ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  coneRadius t • RotaryAttentionSpiralDynamics.ropeAct θ v₀

/-- **Unfolding the Logarithmic Spiral into a Cylinder Helix**:
Mapping the constant-pitch cylinder helix `(cylinderHelixTime t₀ (b * ω) τ, cylinderHelixAngle ω τ)`
to the cone via `cylinderToConeMap` produces the exact logarithmic spiral
`RotaryAttentionSpiralDynamics.spiralTrajectory (Real.exp t₀) b ω τ v₀`. -/
theorem cylinderToConeMap_helix_eq_spiralTrajectory
    (t₀ b ω τ : ℝ) (v₀ : Fin 2 → ℝ) :
    cylinderToConeMap (cylinderHelixTime t₀ (b * ω) τ) (cylinderHelixAngle ω τ) v₀ =
      RotaryAttentionSpiralDynamics.spiralTrajectory (Real.exp t₀) b ω τ v₀ := by
  dsimp [cylinderToConeMap, cylinderHelixTime, cylinderHelixAngle, coneRadius,
    RotaryAttentionSpiralDynamics.spiralTrajectory, RotaryAttentionSpiralDynamics.spiralRadius]
  rw [Real.exp_add]

/-- **Pullback of `spiralTrajectory` to an Affine Line in `vecRadialTime2`**:
For any initial radius $0 < a$ and unit-norm initial vector $\|v_0\|^2 = 1$, the radial
log-time `vecRadialTime2` along `spiralTrajectory a b ω τ v₀` is the affine line
$\ln a + b \omega \tau$. -/
theorem vecRadialTime2_spiralTrajectory_eq_affine_line
    (a b ω τ : ℝ) (ha : 0 < a) (v₀ : Fin 2 → ℝ)
    (hv₀ : RotaryAttentionSpiralDynamics.vecNormSq2 v₀ = 1) :
    vecRadialTime2 (RotaryAttentionSpiralDynamics.spiralTrajectory a b ω τ v₀) =
      radialTime a + b * ω * τ := by
  dsimp [vecRadialTime2]
  rw [RotaryAttentionSpiralDynamics.spiralTrajectory_normSq_eq, hv₀, mul_one]
  have hpos : 0 < RotaryAttentionSpiralDynamics.spiralRadius a b ω τ :=
    RotaryAttentionSpiralDynamics.spiralRadius_pos a b ω τ ha
  rw [Real.sqrt_sq (le_of_lt hpos)]
  dsimp [RotaryAttentionSpiralDynamics.spiralRadius]
  rw [radialTime_mul_scale ha (Real.exp_pos (b * ω * τ)), add_comm (radialTime _)]
  congr 1
  exact radialTime_coneRadius (b * ω * τ)

/-- Eliminating parameter $\tau = \theta / \omega$ expresses the cylinder
helix time as an affine function of angle $\theta$: $t(\theta) = t_0 + (b / \omega) \theta$. -/
theorem cylinderHelixTime_of_angle (t₀ b ω θ : ℝ) :
    cylinderHelixTime t₀ b (θ / ω) = t₀ + (b / ω) * θ :=
  helix_time_of_angle_scalar t₀ b ω θ

/-- Exponentiating `cylinderHelixTime t₀ b (θ / ω)` yields the logarithmic spiral radius
$r(\theta) = e^{t_0} e^{(b / \omega) \theta}$. -/
theorem coneRadius_cylinderHelixTime_of_angle (t₀ b ω θ : ℝ) :
    coneRadius (cylinderHelixTime t₀ b (θ / ω)) =
      Real.exp t₀ * Real.exp ((b / ω) * θ) := by
  rw [cylinderHelixTime_of_angle]
  dsimp [coneRadius]
  exact Real.exp_add t₀ ((b / ω) * θ)

/-!
### Archetype IV — 5-Graded Super-Grassmannian Conformal Weight Representation ($r^{-2}, r^{-1}, r^0, r^{+1}, r^{+2}$)
-/

/-- Integer conformal weight $k \in \{-2, -1, 0, +1, +2\}$ associated with each of the five
grades of `ConformalGrade`. -/
def gradeWeight : ConformalGrade → ℤ
  | .negTwo => -2
  | .negOne => -1
  | .zero => 0
  | .posOne => 1
  | .posTwo => 2

/-- The conformal grade inversion `ConformalGrade.swap` negates the integer conformal weight:
$\mathrm{weight}(\mathrm{swap}(g)) = -\mathrm{weight}(g)$. -/
theorem gradeWeight_swap (g : ConformalGrade) :
    gradeWeight (ConformalGrade.swap g) = -gradeWeight g := by
  cases g <;> rfl

/-- Cylinder dilatation weight $e^{k t}$ of conformal grade $g$ at cylinder time $t$. -/
def gradeTimeScale (g : ConformalGrade) (t : ℝ) : ℝ :=
  Real.exp ((gradeWeight g : ℝ) * t)

/-- Radial cone power weight $r^k$ (`r ^ gradeWeight g`) of conformal grade $g$ at cone radius $r$. -/
def gradeRadialScale (g : ConformalGrade) (r : ℝ) : ℝ :=
  r ^ (gradeWeight g)

/-- **5-Grade Cone-to-Cylinder Conformal Weight Dictionary**:
For every conformal grade $g \in \{-2, -1, 0, +1, +2\}$, the cylinder exponential weight
$e^{k t}$ coincides with the radial power $(e^t)^k$:
`gradeTimeScale g t = gradeRadialScale g (coneRadius t)`. -/
theorem gradeTimeScale_eq_gradeRadialScale_coneRadius (g : ConformalGrade) (t : ℝ) :
    gradeTimeScale g t = gradeRadialScale g (coneRadius t) := by
  dsimp [gradeTimeScale, gradeRadialScale, coneRadius]
  cases g with
  | negTwo => exact exp_grade_negTwo_eq_zpow t
  | negOne => exact exp_grade_negOne_eq_zpow t
  | zero => exact exp_grade_zero_eq_zpow t
  | posOne => exact exp_grade_posOne_eq_zpow t
  | posTwo => exact exp_grade_posTwo_eq_zpow t

/-- For any positive cone radius $0 < r$, the radial power weight $r^k$ equals the cylinder
dilatation weight at `radialTime r = ln r`. -/
theorem gradeRadialScale_at_radialTime (g : ConformalGrade) {r : ℝ} (hr : 0 < r) :
    gradeRadialScale g r = gradeTimeScale g (radialTime r) := by
  rw [gradeTimeScale_eq_gradeRadialScale_coneRadius]
  dsimp [coneRadius, radialTime]
  rw [RadialLogBarrier.exp_radialTau hr]

/-- At cylinder time $t = 0$, every conformal grade has unit scale factor `gradeTimeScale g 0 = 1`. -/
theorem gradeTimeScale_zero_time (g : ConformalGrade) :
    gradeTimeScale g 0 = 1 := by
  dsimp [gradeTimeScale]
  rw [mul_zero, Real.exp_zero]

/-- One-parameter additive group law for conformal grade scaling on the cylinder:
`gradeTimeScale g (t + s) = gradeTimeScale g t * gradeTimeScale g s`. -/
theorem gradeTimeScale_add_time (g : ConformalGrade) (t s : ℝ) :
    gradeTimeScale g (t + s) = gradeTimeScale g t * gradeTimeScale g s := by
  dsimp [gradeTimeScale]
  rw [int_mul_add_distrib (gradeWeight g) t s, Real.exp_add]

/-- Conformal grade swap `ConformalGrade.swap` inverts the cylinder dilatation factor:
`gradeTimeScale (swap g) t = (gradeTimeScale g t)⁻¹`. -/
theorem gradeTimeScale_swap_eq_inv (g : ConformalGrade) (t : ℝ) :
    gradeTimeScale (ConformalGrade.swap g) t = (gradeTimeScale g t)⁻¹ := by
  dsimp [gradeTimeScale]
  rw [gradeWeight_swap, neg_int_mul_eq (gradeWeight g) t, Real.exp_neg]

/-- Opposite conformal grades $g$ and `swap g` have mutually inverse dilatation weights:
$e^{k t} \cdot e^{-k t} = 1$. -/
theorem gradeTimeScale_mul_swap_eq_one (g : ConformalGrade) (t : ℝ) :
    gradeTimeScale g t * gradeTimeScale (ConformalGrade.swap g) t = 1 := by
  rw [gradeTimeScale_swap_eq_inv]
  exact mul_inv_cancel₀ (Real.exp_ne_zero _)

/-- The central grade `.zero` ($k = 0$) is strictly scale-invariant for all cylinder times $t$:
`gradeTimeScale .zero t = 1`. -/
theorem gradeTimeScale_grade_zero (t : ℝ) :
    gradeTimeScale .zero t = 1 := by
  dsimp [gradeTimeScale, gradeWeight]
  rw [Int.cast_zero, zero_mul, Real.exp_zero]

/-- Under any `FiveGradedConformalInversion L`, applying the projective inversion `G.theta`
negates the integer conformal weight `gradeWeight (G.grade x)`. -/
theorem fiveGradedInversion_gradeWeight_theta {L : Type*}
    (G : FiveGradedConformalInversion L) (x : L) :
    gradeWeight (G.grade (G.theta x)) = -gradeWeight (G.grade x) := by
  rw [G.grade_swap, gradeWeight_swap]

/-- Under any `FiveGradedConformalInversion L`, applying `G.theta` inverts the cylinder
dilatation scale factor `gradeTimeScale (G.grade x) t`. -/
theorem fiveGradedInversion_gradeTimeScale_theta {L : Type*}
    (G : FiveGradedConformalInversion L) (x : L) (t : ℝ) :
    gradeTimeScale (G.grade (G.theta x)) t = (gradeTimeScale (G.grade x) t)⁻¹ := by
  rw [G.grade_swap, gradeTimeScale_swap_eq_inv]

/-- For any element $x \in L$ in a `FiveGradedConformalInversion L`, the cylinder dilatation
weights of $x$ and its conformal inverse `G.theta x` multiply to $1$. -/
theorem fiveGradedInversion_gradeTimeScale_mul_theta {L : Type*}
    (G : FiveGradedConformalInversion L) (x : L) (t : ℝ) :
    gradeTimeScale (G.grade x) t * gradeTimeScale (G.grade (G.theta x)) t = 1 := by
  rw [G.grade_swap, gradeTimeScale_mul_swap_eq_one]

/-- Every element $x \in G.\mathrm{centerSet}$ of a `FiveGradedConformalInversion L` has unit
cylinder dilatation scale factor for all $t \in \mathbb{R}$. -/
theorem fiveGradedInversion_centerSet_scale_one {L : Type*}
    (G : FiveGradedConformalInversion L) {x : L}
    (hx : x ∈ G.centerSet) (t : ℝ) :
    gradeTimeScale (G.grade x) t = 1 := by
  have h0 : G.grade x = ConformalGrade.zero := hx
  rw [h0, gradeTimeScale_grade_zero]

/-!
### Archetype V — Dilated Para-Kähler Fock CAR Superbracket Invariance & 5-Sector Dilatation Action
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Radially dilated Fock creation endomorphism at cylinder time $t$, carrying outgoing
conformal grade `.posOne` ($e^{+t}$):
$c^\dagger_t(u) = e^{+t} c^\dagger(u)$. -/
def dilatedCreateEnd (K : V →ₗ[ℝ] V) (t : ℝ) (u : primalSheet K) :
    Module.End ℝ (FockExteriorEnvelope K) :=
  gradeTimeScale .posOne t • paraKahlerCreateEnd K u

/-- Radially dilated Fock annihilation endomorphism at cylinder time $t$, carrying incoming
conformal grade `.negOne` ($e^{-t}$):
$c_t(\alpha) = e^{-t} c(\alpha)$. -/
def dilatedAnnihilateEnd (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (t : ℝ) (α : covectorVacuumSheet K) :
    Module.End ℝ (FockExteriorEnvelope K) :=
  gradeTimeScale .negOne t • paraKahlerAnnihilateEnd g K α

/-- **Radial Dilatation Invariance of the Para-Kähler Fock CAR Superbracket**:
Because `dilatedCreateEnd` transforms in grade `.posOne` ($e^{+t}$) and `dilatedAnnihilateEnd`
transforms in the dual grade `.negOne = swap .posOne` ($e^{-t}$), their odd-odd $\mathbb{Z}_2$
Lie superbracket is strictly independent of cylinder time $t$. -/
theorem superBracket_dilatedCreate_dilatedAnnihilate_invariant
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (t : ℝ) (u : primalSheet K) (α : covectorVacuumSheet K) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (dilatedCreateEnd K t u) (dilatedAnnihilateEnd g K t α) =
      ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (paraKahlerCreateEnd K u) (paraKahlerAnnihilateEnd g K α) := by
  ext ψ
  dsimp [dilatedCreateEnd, dilatedAnnihilateEnd]
  rw [ChakravalaGA.superBracket_fermionic, ChakravalaGA.superBracket_fermionic]
  rw [ Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
       Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
       smul_smul, smul_smul,
       mul_comm (gradeTimeScale .negOne t) (gradeTimeScale .posOne t),
       ← smul_add ]
  have h_one : gradeTimeScale .posOne t * gradeTimeScale .negOne t = 1 :=
    gradeTimeScale_mul_swap_eq_one .posOne t
  rw [h_one, one_smul]

/-- **Dilated CAR Superbracket Evaluation**:
At every cylinder time $t \in \mathbb{R}$, the odd-odd superbracket of `dilatedCreateEnd K t u`
and `dilatedAnnihilateEnd g K t α` evaluates to the grade-$0$ central pairing
$g(\alpha, u) \cdot \mathrm{id}_{\bigwedge T^+}$. -/
theorem superBracket_dilatedCreate_dilatedAnnihilate_eq_pairing
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (t : ℝ) (u : primalSheet K) (α : covectorVacuumSheet K) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (dilatedCreateEnd K t u) (dilatedAnnihilateEnd g K t α) =
      g (α : V) (u : V) • (1 : Module.End ℝ (FockExteriorEnvelope K)) := by
  rw [superBracket_dilatedCreate_dilatedAnnihilate_invariant,
    superBracket_create_annihilate]

/-- Direct-sum 5-graded carrier $\bigoplus_{k \in \mathrm{ConformalGrade}} M_k$ indexed by
`ConformalGrade`. -/
abbrev FiveGradedCarrier (M : ConformalGrade → Type*) :=
  ∀ k : ConformalGrade, M k

/-- Componentwise cylinder dilatation action $(D_t x)_k = e^{k t} x_k$ on a 5-graded module
family `FiveGradedCarrier M`. -/
def fiveGradedDilatation {M : ConformalGrade → Type*}
    [∀ k, AddCommMonoid (M k)] [∀ k, Module ℝ (M k)]
    (t : ℝ) (x : FiveGradedCarrier M) : FiveGradedCarrier M :=
  fun k => gradeTimeScale k t • x k

/-- Identity law at $t = 0$ for the 5-graded cylinder dilatation:
`fiveGradedDilatation 0 x = x`. -/
theorem fiveGradedDilatation_zero {M : ConformalGrade → Type*}
    [∀ k, AddCommMonoid (M k)] [∀ k, Module ℝ (M k)]
    (x : FiveGradedCarrier M) :
    fiveGradedDilatation 0 x = x := by
  funext k
  dsimp [fiveGradedDilatation]
  rw [gradeTimeScale_zero_time, one_smul]

/-- One-parameter additive group law for the 5-graded cylinder dilatation:
`fiveGradedDilatation (t + s) x = fiveGradedDilatation t (fiveGradedDilatation s x)`. -/
theorem fiveGradedDilatation_add {M : ConformalGrade → Type*}
    [∀ k, AddCommMonoid (M k)] [∀ k, Module ℝ (M k)]
    (t s : ℝ) (x : FiveGradedCarrier M) :
    fiveGradedDilatation (t + s) x =
      fiveGradedDilatation t (fiveGradedDilatation s x) := by
  funext k
  dsimp [fiveGradedDilatation]
  rw [gradeTimeScale_add_time, mul_smul]

/-- The modular center sector `.zero` ($k = 0$) is a point-wise fixed point of
`fiveGradedDilatation t` for all $t \in \mathbb{R}$. -/
theorem fiveGradedDilatation_center_fixed {M : ConformalGrade → Type*}
    [∀ k, AddCommMonoid (M k)] [∀ k, Module ℝ (M k)]
    (t : ℝ) (x : FiveGradedCarrier M) :
    fiveGradedDilatation t x .zero = x .zero := by
  dsimp [fiveGradedDilatation]
  rw [gradeTimeScale_grade_zero, one_smul]

end InfoGeometry.Canonical.RadialQuantizationFiveGradedCylinder

end
