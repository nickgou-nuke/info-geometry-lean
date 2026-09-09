import Mathlib
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.Thermal
import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.OperatorAlgebra.QCCRCore
import InfoGeometry.OperatorAlgebra.QCCRSupergrading

/-!
# InfoGeometry.Canonical.ThermalBogoliubov

**Capstone bridge: the q-CCR thermal dial and the Krein/modular/Bogoliubov
infrastructure.**

This module connects Kuzmin's continuous q-CCR deformation parameter `q`
to the thermal geometry of the doubled space.
- The `ThermalPolarization` structure encodes the relationship
  `q = exp(-beta) = tanh(theta)` that underlies the modular/Bogoliubov boost.
- The `ThermalBogoliubovBridge` packages a q-CCR algebra over the doubled
  space with a chosen polarization, providing the algebraic infrastructure
  for KMS thermal states at finite inverse temperature.
- The bridge theorems relate the statistical dial `q` to the geometric boost
  parameter `theta`, linking the algebraic q-superbracket to the geometric
  Bogoliubov transformation.

The parameter dictionary:

```
  q ∈ (-1, 1)      —  continuous statistical deformation dial
  beta = -log|q|   —  inverse temperature (finite for q ≠ 0)
  theta = artanh q  —  Bogoliubov boost rapidity (geometric angle)
  q = tanh(theta)   —  the thermal fixed-point relation
  q = exp(-beta)    —  the statistical-mechanical Boltzmann relation
```

### BUCKET 1: CLOSED FINITE THEOREMS

- `q_zero_is_absolute_zero`: At q=0, no finite β solves `q = exp(-β)`
  (the formal limit β → ∞, closure debt for extended reals).
- `q_to_beta_monotonic`: `beta > 0 ↔ |q| < 1 ∧ q ≠ 0`.  The inverse
  temperature is positive exactly when the dial is in the Kuzmin regime
  and the Cuntz apex is excluded.
- `bogoliubov_boost_at_q`: `tanh(artanh q) = q` for `|q| < 1`.  The geometric
  boost equation holds at every valid dial position.
- `cuntz_vacuum_is_thermal_fixed_point`: At q=0, `theta = 0`.  The Cuntz apex
  corresponds to zero boost angle — the unentangled vacuum.
- `q_superbracket_at_theta`: For `q = tanh θ`, the q-superbracket rewrites
  as `(cosh θ)^(-2) · ((cosh²θ)·XY - (sinhθ·coshθ)·YX)`.  This is the
  algebraic dial expressed in terms of the geometric boost parameter.

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.  All bridging theorems are purely algebraic or elementary
real-analytic.

### BUCKET 3: OPEN CLOSURE DEBT

- **Extended-real limit `q → 0⁺` ⇒ `β → ∞`**.  The statement
  `beta = -log|q|` with `q = 0` requires the extended real line `ℝ̅` to
  express `β = ∞`.  Standard `Real.log 0 = 0` (mathlib convention) gives
  the finite value `β = 0`, which is physically incorrect for the
  absolute-zero limit.  The theorem `q_zero_is_absolute_zero` proves the
  finite version: no finite β satisfies `0 = exp(-β)`.
- **Full KMS condition proof** for the q-CCR thermal state at fixed q
  requires analytic C*-algebra machinery (KMS weight theory,
  Tomita–Takesaki).  This module provides the algebraic bridge only; the
  analytic KMS verification is outside scope.
- **Kuzmin's 𝔅_{n,q} ≃ KO_n isomorphism** for `|q| < 1` is an analytic
  C*-result that depends on Kirchberg–Phillips classification and is not
  provable in this finite algebraic setting.
-/

noncomputable section

namespace InfoGeometry.Canonical.ThermalBogoliubov

open Real
open Set
open InfoGeometry.Krein
open InfoGeometry.Dynamics
open InfoGeometry.OperatorAlgebra.QCCRCore
open InfoGeometry.OperatorAlgebra.QCCRSupergrading

/-! ## 1. The thermal polarization structure -/

/--
**Thermal polarization data for the q-CCR algebra.**

The thermal polarization packages the three interrelated parameters that
connect the statistical dial `q` to the geometric boost and the inverse
temperature:

```
  q ∈ (-1, 1)      —  statistical dial (continuous supergrading)
  beta = -log|q|   —  inverse temperature (KMS parameter)
  theta = artanh q  —  Bogoliubov boost rapidity
```

The relationship `beta = -log|q|` is the Boltzmann factor `|q| = exp(-beta)`,
and `theta = artanh q` is the geometric boost angle satisfying
`q = tanh(theta)`.  Together they establish the equivalence of the
statistical-mechanical and geometric descriptions of the thermal state.
-/
structure ThermalPolarization where
  q : ℝ
  hq_bounds : -1 < q ∧ q < 1
  beta : ℝ
  beta_eq : beta = -Real.log (|q|)
  theta : ℝ
  theta_eq : theta = Real.artanh q

/-! ## 2. The bridge structure -/

/--
**Thermal–Bogoliubov bridge: a q-CCR algebra with a thermal polarization.**

This structure packages a Kuzmin `QCCRAlgebra` (generic over the operator
algebra `Op`, intended to be the endomorphisms of the doubled Krein space)
together with a `ThermalPolarization` that encodes the inverse temperature
and boost rapidity.

The `q_equals` field ensures the deformation parameter of the algebra
agrees with the polarization parameter, closing the algebraic–geometric
dictionary.

The type parameter `N` is the number of generators (the dimension of the
underlying Cuntz–Toeplitz algebra).  The type parameter `Op` is the operator
algebra carrying the q-CCR relations; for the doubled-space application,
this is `DoubledSpace E →L[ℝ] DoubledSpace E`.
-/
structure ThermalBogoliubovBridge (N : ℕ) (Op : Type*) [Ring Op] [StarRing Op] [Algebra ℝ Op] where
  qccr : QCCRAlgebra N Op
  polarization : ThermalPolarization
  /-- The q-CCR deformation parameter matches the polarization dial. -/
  q_equals : qccr.q = polarization.q

/-! ## 3. The bridge theorems -/

/--
**At q = 0, no finite β satisfies q = exp(-β).**

If q = 0, the Boltzmann factor `|q| = exp(-beta)` would require
`0 = exp(-beta)`, but the real exponential is strictly positive for all
real arguments.  Hence no finite inverse temperature exists, corresponding
to the physical limit `beta → ∞` (absolute zero).

This is the formal obstruction: in `ℝ`, `Real.log 0 = 0` (by mathlib
convention for extended definitions), so `beta = -log|0| = 0` rather than
`+∞`.  The extended real line `ℝ̅` would be required to express
`beta = ∞` formally.  This theorem proves the finite-content statement:
there is no finite β that satisfies the Boltzmann relation at q = 0.

**Closure debt**: the extended-real limit `lim_{q→0⁺} beta(q) = +∞` is
not expressible in ℝ and requires `ℝ̅`.  See BUCKET 3.
-/
theorem q_zero_is_absolute_zero (q : ℝ) (hq0 : q = 0) : ¬∃ (beta : ℝ), q = Real.exp (-beta) := by
  rw [hq0]
  intro h
  rcases h with ⟨beta, h⟩
  have hpos : 0 < Real.exp (-beta) := Real.exp_pos (-beta)
  rw [h] at hpos
  linarith

/--
**The inverse temperature is positive iff the dial is in the Kuzmin regime
and the Cuntz apex is excluded.**

  `beta > 0  ↔  |q| < 1 ∧ q ≠ 0`

Interpretation:
- `|q| < 1` places `q` in the Kuzmin regime (𝔅_{n,q} ≃ KO_n), where the
  Cuntz core is nuclear and the statistical deformation is continuous.
- `q ≠ 0` excludes the Cuntz apex, where `beta` would vanish (resp. the
  extended-real limit `β = ∞` at the exact apex).

When both conditions hold, `log|q| < 0` (log is negative on `(0,1)`) and
therefore `beta = -log|q| > 0`.  Conversely, if `beta > 0`, then
`log|q| < 0`, which forces `|q|` to be strictly between 0 and 1.

This theorem is purely elementary real-analytic (logarithm on `(0,1)`).
-/
theorem q_to_beta_monotonic (tp : ThermalPolarization) : tp.beta > 0 ↔ |tp.q| < 1 ∧ tp.q ≠ 0 := by
  constructor
  · intro hbeta
    have hlog_neg : Real.log (|tp.q|) < 0 := by
      rw [tp.beta_eq] at hbeta
      linarith
    have hq_ne_zero : tp.q ≠ 0 := by
      intro hzero
      have habs_zero : |tp.q| = 0 := by simp [hzero]
      have hlog_zero : Real.log (|tp.q|) = 0 := by simp [habs_zero]
      linarith
    have hq_abs_lt_one : |tp.q| < 1 := by
      by_contra! hge
      -- hge : 1 ≤ |tp.q|
      have hlog_nonneg : 0 ≤ Real.log (|tp.q|) := Real.log_nonneg hge
      linarith
    exact ⟨hq_abs_lt_one, hq_ne_zero⟩
  · intro ⟨hq_abs_lt_one, hq_ne_zero⟩
    have hq_abs_pos : 0 < |tp.q| := abs_pos.mpr hq_ne_zero
    have hlog_neg : Real.log (|tp.q|) < 0 := Real.log_neg hq_abs_pos hq_abs_lt_one
    rw [tp.beta_eq]
    linarith

/--
**The geometric boost equation `tanh(artanh q) = q` holds for |q| < 1.**

This trivial identity is the core of the thermal interpretation: the
statistical dial `q` is the hyperbolic tangent of the Bogoliubov boost
rapidity `theta`.  The equation `q = tanh(theta)` is the thermal fixed-point
relation.

The proof uses `Real.tanh_artanh` which requires `|q| < 1` (equivalently
`q ∈ Ioo (-1, 1)`), guaranteed by the polarization bounds.
-/
theorem bogoliubov_boost_at_q (tp : ThermalPolarization) : Real.tanh (Real.artanh tp.q) = tp.q := by
  rcases tp.hq_bounds with ⟨hleft, hright⟩
  have h_mem : tp.q ∈ Set.Ioo (-1 : ℝ) 1 := Set.mem_Ioo.mpr ⟨hleft, hright⟩
  exact Real.tanh_artanh h_mem

/--
**At the Cuntz apex q=0, the boost angle vanishes: `theta = 0`.**

When `q = 0`, the rapidity `theta = artanh 0 = 0` and the Bogoliubov
transformation is the identity — the modular boost angle is zero, meaning
the thermal state is the unentangled Cuntz vacuum with no geometric
squeezing.

This confirms that the Cuntz apex is the thermal fixed point at zero
temperature: no boost, no entanglement, no statistical deformation.
-/
theorem cuntz_vacuum_is_thermal_fixed_point (tp : ThermalPolarization) (hq0 : tp.q = 0) : tp.theta = 0 := by
  rw [tp.theta_eq, hq0]
  exact Real.artanh_zero

/--
**The q-superbracket rewritten with the geometric boost parameter.**

When the dial is set to `q = tanh θ`, the q-superbracket
`[X, Y]_q = XY - q·YX` takes the form

```
  [X, Y]_{tanh θ} = (cosh θ)^(-2) · (cosh²θ · XY - sinhθ·coshθ · YX)
```

This identity expresses the algebraic q-deformation entirely in terms of the
geometric boost rapidity `θ`.  The factor `(cosh θ)^(-2)` is the metric
scaling of the boosted frame, and the combination
`cosh²θ · XY - sinhθ·coshθ · YX` is the Bogoliubov-transformed product.

The proof uses `Real.tanh_eq_sinh_div_cosh` and elementary field algebra on
ℝ, then multiplies by `(cosh θ)²` to clear the denominator.

This is the cleanest bridge between the statistical q-dial and the
geometric Bogoliubov transformation: every dial position corresponds
to a boost rapidity, and the algebraic deformation scales as the
inverse-squared hyperbolic cosine of the boost angle.
-/
theorem q_superbracket_at_theta {Op : Type*} [Ring Op] [Algebra ℝ Op] (θ : ℝ) (X Y : Op) :
    qSuperbracket (Real.tanh θ) X Y = ((Real.cosh θ) ^ 2)⁻¹ • (((Real.cosh θ) ^ 2) • (X * Y) - (Real.sinh θ * Real.cosh θ) • (Y * X)) := by
  have hcosh_ne_zero : Real.cosh θ ≠ 0 := by
    exact ne_of_gt (Real.cosh_pos θ)
  have hcosh_sq_ne_zero : (Real.cosh θ) ^ 2 ≠ 0 := pow_ne_zero 2 hcosh_ne_zero
  -- Key computation: multiply both sides by (cosh θ)² to eliminate the outer inverse
  have hcalc : (Real.cosh θ) ^ 2 • qSuperbracket (Real.tanh θ) X Y =
      ((Real.cosh θ) ^ 2) • (X * Y) - (Real.sinh θ * Real.cosh θ) • (Y * X) := by
    have h_scalar : (Real.cosh θ) ^ 2 * (Real.sinh θ / Real.cosh θ) = Real.cosh θ * Real.sinh θ := by
      field_simp [hcosh_ne_zero]
    calc
      (Real.cosh θ) ^ 2 • qSuperbracket (Real.tanh θ) X Y
          = (Real.cosh θ) ^ 2 • (X * Y - (Real.tanh θ) • (Y * X)) := rfl
      _ = (Real.cosh θ) ^ 2 • (X * Y) - (Real.cosh θ) ^ 2 • ((Real.tanh θ) • (Y * X)) := by
        simp [smul_sub]
      _ = ((Real.cosh θ) ^ 2) • (X * Y) - ((Real.cosh θ) ^ 2 * Real.tanh θ) • (Y * X) := by
        simp [smul_smul]
      _ = ((Real.cosh θ) ^ 2) • (X * Y) - ((Real.cosh θ) ^ 2 * (Real.sinh θ / Real.cosh θ)) • (Y * X) := by
        rw [Real.tanh_eq_sinh_div_cosh θ]
      _ = ((Real.cosh θ) ^ 2) • (X * Y) - (Real.cosh θ * Real.sinh θ) • (Y * X) := by
        simp [h_scalar]
      _ = ((Real.cosh θ) ^ 2) • (X * Y) - (Real.sinh θ * Real.cosh θ) • (Y * X) := by
        simp [mul_comm]
  -- Re-introduce the factor (cosh θ)⁻²
  have h_factor : ((Real.cosh θ) ^ 2)⁻¹ • ((Real.cosh θ) ^ 2 • qSuperbracket (Real.tanh θ) X Y) =
      qSuperbracket (Real.tanh θ) X Y := by
    calc
      ((Real.cosh θ) ^ 2)⁻¹ • ((Real.cosh θ) ^ 2 • qSuperbracket (Real.tanh θ) X Y)
          = (((Real.cosh θ) ^ 2)⁻¹ * (Real.cosh θ) ^ 2) • qSuperbracket (Real.tanh θ) X Y := by
        simp [smul_smul]
      _ = (1 : ℝ) • qSuperbracket (Real.tanh θ) X Y := by
        have h_inv_mul : ((Real.cosh θ) ^ 2)⁻¹ * (Real.cosh θ) ^ 2 = (1 : ℝ) :=
          inv_mul_cancel₀ hcosh_sq_ne_zero
        simp [h_inv_mul]
      _ = qSuperbracket (Real.tanh θ) X Y := by simp
  calc
    qSuperbracket (Real.tanh θ) X Y
        = ((Real.cosh θ) ^ 2)⁻¹ • ((Real.cosh θ) ^ 2 • qSuperbracket (Real.tanh θ) X Y) := by
      rw [h_factor]
    _ = ((Real.cosh θ) ^ 2)⁻¹ • (((Real.cosh θ) ^ 2) • (X * Y) - (Real.sinh θ * Real.cosh θ) • (Y * X)) := by
      rw [hcalc]

end InfoGeometry.Canonical.ThermalBogoliubov

end noncomputable section
