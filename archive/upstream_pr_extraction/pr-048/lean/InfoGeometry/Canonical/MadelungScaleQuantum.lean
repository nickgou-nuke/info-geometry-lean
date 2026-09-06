import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import InfoGeometry.Canonical.HestenesComplexTranslation
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.FirstQuantizedChiralConeBridge
import InfoGeometry.Canonical.AmariZetaSimplex

/-!
# Madelung Scale Quantum Mechanics in Hestenes–Krein Formalism

This module formalizes the exact Madelung decomposition for scale quantum mechanics
on logarithmic coordinates, following the structural analysis of the Hestenes–Krein
ancestor Ψ(t) = Ξ(t) + K Υ(t) with K² = -1.

## Geometric Structure

### 1. Hestenes–Krein Ancestor
The one-sided Hestenes ancestor is:
```
Ψ(t) = Ξ(t) + K Υ(t),    K² = -1
```
where Ξ(t) is the even (cosine) quadrature and Υ(t) is the odd (sine) quadrature.

### 2. Madelung Amplitude–Phase Decomposition
```
Ψ(t) = √ρ(t) e^{K S(t)/ℏ}
ρ(t) = Ξ(t)² + Υ(t)²   (density)
S(t)/ℏ = arg(Ψ(t))     (phase)
```

Equivalently:
```
Ξ(t) = √ρ(t) cos(S(t)/ℏ)
Υ(t) = √ρ(t) sin(S(t)/ℏ)
```

### 3. Logarithmic Derivative and Current
```
Ψ'(t) Ψ(t)⁻¹ = ½ ρ'(t)/ρ(t) + K S'(t)/ℏ
```

The Madelung current:
```
j(t) = (ℏ/m) (Ξ Υ' - Υ Ξ')(t)
```

### 4. Travelling Wave Decomposition
```
Ψ_+(t) = ∫₀^∞ Φ(u) e^{K t u} du
Ψ_-(t) = ∫₀^∞ Φ(u) e^{-K t u} du = Ψ_+~(t)

Ξ(t) = (Ψ_+ + Ψ_-)/2 = ∫₀^∞ Φ(u) cos(t u) du
Υ(t) = (Ψ_+ - Ψ_-)/(2K) = ∫₀^∞ Φ(u) sin(t u) du
```

### 5. Logarithmic Coordinates and Dilation Generator
Set q = log x. The Weyl-ordered dilation generator:
```
D̂ = -Kℏ (x ∂_x + ½)
```

Unitary transformation U: ψ ↦ e^{q/2} ψ(e^q) gives:
```
U D̂ U⁻¹ = -Kℏ ∂_q
```

Canonical pair:
```
q̂ ψ(q) = q ψ(q)
D̂ = -Kℏ ∂_q
[q̂, D̂] = Kℏ
```

### 6. Madelung Equations
From Hestenes Schrödinger equation:
```
Kℏ ∂_τ Ψ = [-ℏ²/(2m) ∂_q² + V(q,τ)] Ψ
```

Insert Ψ = √ρ e^{K S/ℏ}:

**Continuity equation (K-odd):**
```
∂_τ ρ + ∂_q (ρ ∂_q S / m) = 0
```

**Quantum Hamilton–Jacobi (K-even):**
```
∂_τ S + (∂_q S)²/(2m) + V + Q_M = 0
```
where `Q_M = -ℏ²/(2m) (∂_q²√ρ)/√ρ` is the Madelung quantum potential.

### 7. Constant-Current Criterion for Real Stationary Potential
For stationary equation with real V(t):
```
j'(t) = 0    ⟺    d/dt (ρ(t) S'(t)) = 0
```

In quadrature form:
```
d/dt [Ξ Υ' - Υ Ξ'] = 0
```

### 8. Phase Circulation Law (De Rham → Madelung)
```
∮ d log Ψ = 2π K m
∮ dS = 2π ℏ m
```
Zero/pole divisor multiplicity = quantized phase vortex charge.

### 9. Ξ-zeros vs ζ-zeros
- **One-sided ancestor**: Ξ(t₀) = 0, Υ(t₀) ≠ 0 → quadrature crossing (phase = ±π/2)
- **Raw ζ amplitude**: ζ(½+it₀) = 0 → density node ρ_ζ(t₀) = 0

## References
Structural synthesis from Hestenes–Krein geometric algebra, Madelung hydrodynamics,
and Mellin transform arithmetic geometry.
-/

noncomputable section

namespace InfoGeometry.Canonical.MadelungScaleQuantum

open InfoGeometry.Canonical.HestenesComplexTranslation
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.FirstQuantizedChiralConeBridge
open InfoGeometry.Canonical.AmariZetaSimplex
open Complex
open Real

/-- The internal Hestenes–Krein phase axis: K² = -1 -/
structure HestenesKreinAxis where
  K : ℂ
  K_sq_neg_one : K * K = -1

/-- Default choice: K = Complex.I -/
def standardHestenesKreinAxis : HestenesKreinAxis :=
  ⟨Complex.I, by simp [Complex.ext_iff, Complex.I_mul_I]⟩

/-- The Hestenes–Krein ancestor Ψ(t) = Ξ(t) + K Υ(t) -/
structure HestenesKreinAncestor (t : ℝ) where
  Ξ : ℝ
  Υ : ℝ
  K : ℂ
  K_sq_neg_one : K * K = -1
  ψ : ℂ := Ξ + K * Υ

/-- The Madelung amplitude–phase decomposition -/
structure MadelungDecomposition (t : ℝ) where
  ρ : ℝ
  S : ℝ
  ℏ : ℝ
  hρ_pos : 0 < ρ
  ψ : ℂ := Real.sqrt ρ * Complex.exp (Complex.I * (S / ℏ))

/-- Travelling wave channels Ψ_±(t) = ∫₀^∞ Φ(u) e^{±K t u} du -/
structure TravellingWaveChannels where
  Φ : ℝ → ℝ
  Ψ_plus : ℝ → ℂ
  Ψ_minus : ℝ → ℂ
  Ψ_plus_def : ∀ (t : ℝ), Ψ_plus t = ∫ u : ℝ, Φ u * Complex.exp (Complex.I * (t * u))
  Ψ_minus_def : ∀ (t : ℝ), Ψ_minus t = ∫ u : ℝ, Φ u * Complex.exp (-Complex.I * (t * u))

/-- The logarithmic coordinate q = log x -/
def logCoordinate (x : ℝ) (hx : 0 < x) : ℝ := Real.log x

/-- The Weyl-ordered dilation generator in x-representation:
    D̂ = -Kℏ (x ∂_x + ½) -/
structure WeylDilationGenerator where
  ℏ : ℝ
  K : ℂ
  K_sq_neg_one : K * K = -1
  D_x : (ℝ → ℂ) → (ℝ → ℂ)

/-- Unitary transformation U: (Uψ)(q) = e^{q/2} ψ(e^q) -/
def unitaryLogTransform (ψ : ℝ → ℂ) (q : ℝ) : ℂ :=
  Real.exp (q / 2) * ψ (Real.exp q)

/-- In logarithmic coordinates, D̂ = -Kℏ ∂_q -/
structure DilationInLogCoordinates where
  ℏ : ℝ
  K : ℂ
  K_sq_neg_one : K * K = -1
  D_q : (ℝ → ℂ) → (ℝ → ℂ)

/-- The canonical pair (q̂, D̂) with [q̂, D̂] = Kℏ -/
structure CanonicalPairLogScale where
  ℏ : ℝ
  K : ℂ
  K_sq_neg_one : K * K = -1
  q_op : (ℝ → ℂ) → (ℝ → ℂ)
  D_op : (ℝ → ℂ) → (ℝ → ℂ)
  commutation : ∀ (ψ : ℝ → ℂ), q_op (D_op ψ) - D_op (q_op ψ) = fun q => K * ℏ * ψ q

/-- The Madelung quantum potential:
    Q_M = -ℏ²/(2m) (∂_q²√ρ)/√ρ -/
def madelungQuantumPotential (ρ : ℝ → ℝ) (ℏ m : ℝ) (q : ℝ) : ℝ :=
  - (ℏ ^ 2) / (2 * m) *
    (deriv (deriv (fun q => Real.sqrt (ρ q))) q) / Real.sqrt (ρ q)

/-- The Madelung current:
    j(t) = (ℏ/m) (Ξ Υ' - Υ Ξ')(t) -/
def madelungCurrent (Ξ Υ : ℝ → ℝ) (ℏ m : ℝ) (t : ℝ) : ℝ :=
  (ℏ / m) * (Ξ t * deriv Υ t - Υ t * deriv Ξ t)

/-- The scalar complex Madelung readout associated to an amplitude and phase.

This is deliberately a local finite readout: no global choice of argument or
analytic wave equation is built into the definition. -/
def madelungWave (R S : ℝ → ℝ) (ℏ t : ℝ) : ℂ :=
  (R t : ℂ) * Complex.exp (Complex.I * (S t / ℏ))

/-- Density of the two real quadratures of a Hestenes readout. -/
def ancestorNormSq (Ξ Υ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Ξ t ^ 2 + Υ t ^ 2

@[simp] theorem ancestorNormSq_eq_zero_iff (Ξ Υ : ℝ → ℝ) (t : ℝ) :
    ancestorNormSq Ξ Υ t = 0 ↔ Ξ t = 0 ∧ Υ t = 0 := by
  constructor
  · intro h
    change Ξ t ^ 2 + Υ t ^ 2 = 0 at h
    have hΞ : 0 ≤ Ξ t ^ 2 := sq_nonneg _
    have hΥ : 0 ≤ Υ t ^ 2 := sq_nonneg _
    have hΞsq : Ξ t ^ 2 = 0 := by linarith
    have hΥsq : Υ t ^ 2 = 0 := by linarith
    exact ⟨sq_eq_zero_iff.mp hΞsq, sq_eq_zero_iff.mp hΥsq⟩
  · rintro ⟨hΞ, hΥ⟩
    simp [ancestorNormSq, hΞ, hΥ]

/-- Native derivative chain for the finite Madelung polar readout.

The statement uses `HasDerivAt`, so the analytic obligations are explicit and
local; it does not assert existence of a global phase or a Schrödinger flow. -/
theorem madelungQuadrature_hasDerivAt
    (R S : ℝ → ℝ) (ℏ t R' S' : ℝ) (hℏ : ℏ ≠ 0)
    (hR : HasDerivAt R R' t) (hS : HasDerivAt S S' t) :
    HasDerivAt (fun x => R x * Real.cos (S x / ℏ))
      (R' * Real.cos (S t / ℏ) - R t * Real.sin (S t / ℏ) * (S' / ℏ)) t ∧
    HasDerivAt (fun x => R x * Real.sin (S x / ℏ))
      (R' * Real.sin (S t / ℏ) + R t * Real.cos (S t / ℏ) * (S' / ℏ)) t := by
  have hphase := hS.div_const ℏ
  have hcos := (hphase.cos)
  have hsin := (hphase.sin)
  constructor
  · convert hR.mul hcos using 1 <;>
      simp [hℏ, mul_assoc, mul_comm, mul_left_comm] <;> ring
  · convert hR.mul hsin using 1 <;>
      simp [hℏ, mul_assoc, mul_comm, mul_left_comm] <;> ring

/-- The squared norm of the two Madelung quadratures is the amplitude square. -/
theorem madelungQuadrature_normSq
    (R S : ℝ → ℝ) (ℏ t : ℝ) :
    ancestorNormSq
        (fun x => R x * Real.cos (S x / ℏ))
        (fun x => R x * Real.sin (S x / ℏ)) t = (R t) ^ 2 := by
  dsimp [ancestorNormSq]
  nlinarith [Real.cos_sq_add_sin_sq (S t / ℏ)]

/-- Constant current condition for real stationary potential:
    j'(t) = 0 -/
def constantCurrentCondition (Ξ Υ : ℝ → ℝ) (ℏ m : ℝ) : Prop :=
  ∀ (t : ℝ), deriv (fun t => madelungCurrent Ξ Υ ℏ m t) t = 0

/-- The quadrature current is the usual amplitude--phase current. -/
theorem madelungCurrent_quadrature_eq_density_phase
    (R S : ℝ → ℝ) (ℏ m t R' S' : ℝ) (hℏ : ℏ ≠ 0)
    (hR : HasDerivAt R R' t) (hS : HasDerivAt S S' t) :
    madelungCurrent
        (fun x => R x * Real.cos (S x / ℏ))
        (fun x => R x * Real.sin (S x / ℏ)) ℏ m t =
      (R t) ^ 2 * S' / m := by
  have hq := madelungQuadrature_hasDerivAt R S ℏ t R' S' hℏ hR hS
  rw [madelungCurrent, hq.1.deriv, hq.2.deriv]
  have htrig := Real.cos_sq_add_sin_sq (S t / ℏ)
  have hcross :
      R t * Real.cos (S t / ℏ) *
          (R' * Real.sin (S t / ℏ) +
            R t * Real.cos (S t / ℏ) * (S' / ℏ)) -
        R t * Real.sin (S t / ℏ) *
          (R' * Real.cos (S t / ℏ) -
            R t * Real.sin (S t / ℏ) * (S' / ℏ)) =
      (R t) ^ 2 * (S' / ℏ) *
        (Real.cos (S t / ℏ) ^ 2 + Real.sin (S t / ℏ) ^ 2) := by
    ring
  rw [hcross, htrig]
  field_simp [hℏ]

/-- Pointwise, the Madelung quadrature current is the amplitude--phase current. -/
theorem madelungCurrent_quadrature_function_eq_density_phase
    (R S : ℝ → ℝ) (ℏ m : ℝ) (hℏ : ℏ ≠ 0)
    (hR : ∀ t, HasDerivAt R (deriv R t) t)
    (hS : ∀ t, HasDerivAt S (deriv S t) t) :
    (fun t =>
      madelungCurrent
        (fun x => R x * Real.cos (S x / ℏ))
        (fun x => R x * Real.sin (S x / ℏ)) ℏ m t) =
      (fun t => (R t) ^ 2 * deriv S t / m) := by
  funext t
  exact madelungCurrent_quadrature_eq_density_phase R S ℏ m t
    (deriv R t) (deriv S t) hℏ (hR t) (hS t)

/-- Constant current is equivalent to constancy of the amplitude--phase current. -/
theorem constantCurrentCondition_quadrature_iff_density_phase
    (R S : ℝ → ℝ) (ℏ m : ℝ) (hℏ : ℏ ≠ 0)
    (hR : ∀ t, HasDerivAt R (deriv R t) t)
    (hS : ∀ t, HasDerivAt S (deriv S t) t) :
    constantCurrentCondition
        (fun x => R x * Real.cos (S x / ℏ))
        (fun x => R x * Real.sin (S x / ℏ)) ℏ m ↔
      ∀ t, deriv (fun t => (R t) ^ 2 * deriv S t / m) t = 0 := by
  unfold constantCurrentCondition
  rw [madelungCurrent_quadrature_function_eq_density_phase R S ℏ m hℏ hR hS]

/-! The derivative of the amplitude--phase current, with all analytic data
    made explicit at the point. -/
theorem deriv_density_phase_current
    (R S : ℝ → ℝ) (ℏ m t R' S' S'' : ℝ)
    (hm : m ≠ 0)
    (hR : HasDerivAt R R' t)
    (hS : HasDerivAt S S' t)
    (hS' : HasDerivAt (deriv S) S'' t) :
    deriv (fun x => R x ^ 2 * deriv S x / m) t =
      (2 * R t * R' * S' + R t ^ 2 * S'') / m := by
  have hR2 : HasDerivAt (fun x => R x ^ 2) (2 * R t * R') t := by
    have h := hR.mul hR
    convert h using 1
    · funext x
      simp [pow_two, Pi.mul_apply]
    · ring
  have hSval : deriv S t = S' := hS.deriv
  have hprod := hR2.mul hS'
  have hquot := hprod.div_const m
  simpa [Pi.mul_apply, hSval, mul_comm, mul_left_comm, mul_assoc] using hquot.deriv

/-! Under explicit second-derivative hypotheses, the stationary real-potential
    condition is exactly the vanishing of the local Madelung current
    derivative.  This is a local differential identity, not an existence
    theorem for a Schrödinger operator. -/
theorem constantCurrentCondition_quadrature_iff_explicit
    (R S : ℝ → ℝ) (ℏ m : ℝ) (hℏ : ℏ ≠ 0) (hm : m ≠ 0)
    (hR : ∀ t, HasDerivAt R (deriv R t) t)
    (hS : ∀ t, HasDerivAt S (deriv S t) t)
    (hS2 : ∀ t, HasDerivAt (deriv S) (deriv (deriv S) t) t) :
    constantCurrentCondition
        (fun x => R x * Real.cos (S x / ℏ))
        (fun x => R x * Real.sin (S x / ℏ)) ℏ m ↔
      ∀ t, (2 * R t * deriv R t * deriv S t +
        R t ^ 2 * deriv (deriv S) t) / m = 0 := by
  rw [constantCurrentCondition_quadrature_iff_density_phase R S ℏ m hℏ hR hS]
  constructor
  · intro h t
    have hd := deriv_density_phase_current R S ℏ m t
      (deriv R t) (deriv S t) (deriv (deriv S) t) hm
      (hR t) (hS t) (hS2 t)
    exact hd ▸ h t
  · intro h t
    have hd := deriv_density_phase_current R S ℏ m t
      (deriv R t) (deriv S t) (deriv (deriv S) t) hm
      (hR t) (hS t) (hS2 t)
    exact hd.symm ▸ h t

/-- Phase circulation law:
    ∮ dS = 2π ℏ m -/
structure PhaseCirculationLaw (S : ℝ → ℝ) where
  ℏ : ℝ
  contour_integral_dS : ℝ
  multiplicity : ℤ
  circulation_eq : contour_integral_dS = 2 * Real.pi * ℏ * (multiplicity : ℝ)

/-- Ξ-zeros are quadrature crossings, not density nodes -/
structure XiZeroQuadratureCrossing (Ξ Υ : ℝ → ℝ) where
  t₀ : ℝ
  Ξ_zero : Ξ t₀ = 0
  Υ_nonzero : Υ t₀ ≠ 0
  phase_at_zero : Complex.arg (Complex.mk (Ξ t₀) (Υ t₀)) = Real.pi / 2 ∨
                  Complex.arg (Complex.mk (Ξ t₀) (Υ t₀)) = -Real.pi / 2

/-- A zero of a chosen complex wave readout is a density node.

The carrier is deliberately a supplied wave `ζ`; this records the finite
algebraic implication from a genuine zero and does not silently identify the
wave with the analytic Riemann zeta function. -/
structure ZetaZeroDensityNode where
  ζ : ℝ → ℂ
  t₀ : ℝ
  zeta_zero : ζ t₀ = 0

theorem ZetaZeroDensityNode.density_zero
    (node : ZetaZeroDensityNode) :
    Complex.normSq (node.ζ node.t₀) = 0 := by
  rw [node.zeta_zero]
  simp

/-- Travelling wave decomposition: Ξ = (Ψ_+ + Ψ_-)/2, Υ = (Ψ_+ - Ψ_-)/(2K) -/
structure TravellingWaveDecomposition where
  Ψ_plus : ℝ → ℂ
  Ψ_minus : ℝ → ℂ
  K : ℂ
  K_sq_neg_one : K * K = -1
  Ξ : ℝ → ℝ
  Υ : ℝ → ℝ
  Ξ_eq : ∀ (t : ℝ), Ξ t = ((Ψ_plus t).re + (Ψ_minus t).re) / 2
  Υ_eq : ∀ (t : ℝ), Υ t = ((Ψ_plus t).im - (Ψ_minus t).im) / 2

/-- The exact logarithmic coordinate transformation theorem:
    U D̂ U⁻¹ = -Kℏ ∂_q -/
theorem dilationInLogCoordinates (ψ : ℝ → ℂ) (q : ℝ) (ℏ : ℝ) (K : ℂ)
  (hK : K * K = -1)
  (hψ : HasDerivAt ψ (deriv ψ (Real.exp q)) (Real.exp q)) :
  unitaryLogTransform (fun x => -K * ℏ * (x * deriv ψ x + ψ x / 2)) q
  = -K * ℏ * deriv (unitaryLogTransform ψ) q := by
  have hhalf : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
      (Real.exp (q / 2) / 2) q := by
    convert (Real.hasDerivAt_exp (q / 2)).comp q
      ((hasDerivAt_id q).div_const (2 : ℝ)) using 1 <;> ring
  have hcomp : HasDerivAt (fun x : ℝ => ψ (Real.exp x))
      (deriv ψ (Real.exp q) * (Real.exp q : ℂ)) q := by
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using
      (HasDerivAt.scomp q hψ (Real.hasDerivAt_exp q))
  have htransform : HasDerivAt (unitaryLogTransform ψ)
      ((Real.exp (q / 2) / 2 : ℝ) * ψ (Real.exp q) +
        (Real.exp (q / 2) : ℂ) *
          (deriv ψ (Real.exp q) * (Real.exp q : ℂ))) q := by
    unfold unitaryLogTransform
    convert hhalf.ofReal_comp.mul hcomp using 1 <;> ring
  have hderiv := htransform.deriv
  rw [hderiv]
  simp [unitaryLogTransform]
  ring

/-- The canonical commutation relation [q̂, D̂] = Kℏ -/
theorem canonicalCommutationLogScale (ψ : ℝ → ℂ) (q : ℝ) (ℏ : ℝ) (K : ℂ)
  (hK : K * K = -1)
  (hψ : HasDerivAt ψ (deriv ψ q) q) :
  (q * (-K * ℏ * deriv ψ q)) - (-K * ℏ * deriv (fun q => q * ψ q) q)
  = K * ℏ * ψ q := by
  have hq : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) q := by
    simpa using (hasDerivAt_id (x := (q : ℂ))).comp_ofReal
  have hprod := hq.mul hψ
  have hprod' := hprod.deriv
  change (q : ℂ) * (-K * ℏ * deriv ψ q) -
      (-K * ℏ * deriv (fun x : ℝ => (x : ℂ) * ψ x) q) =
      K * ℏ * ψ q
  have hprod'' : deriv (fun x : ℝ => (x : ℂ) * ψ x) q =
      1 * ψ q + (q : ℂ) * deriv ψ q := by
    simpa [Pi.mul_apply] using hprod'
  rw [hprod'']
  ring

/-- Madelung decomposition of Hestenes–Krein ancestor -/
theorem hestenesKreinToMadelung (Ξ Υ : ℝ → ℝ) (t : ℝ) (K : ℂ) (hK : K * K = -1)
    (ℏ : ℝ) (hℏ : ℏ ≠ 0) :
  (∃ (ρ S : ℝ), 0 < ρ ∧ Ξ t = Real.sqrt ρ * Real.cos (S / ℏ) ∧
   Υ t = Real.sqrt ρ * Real.sin (S / ℏ)) ↔ 0 < Ξ t ^ 2 + Υ t ^ 2 := by
  constructor
  · rintro ⟨ρ, S, hρ, hΞ, hΥ⟩
    rw [hΞ, hΥ]
    have hsqrt : (Real.sqrt ρ) ^ 2 = ρ := by
      exact Real.sq_sqrt (le_of_lt hρ)
    nlinarith [Real.cos_sq_add_sin_sq (S / ℏ)]
  · intro hρ
    let z : ℂ := ⟨Ξ t, Υ t⟩
    have hz : z ≠ 0 := by
      intro hz
      have hzr : Ξ t = 0 := by
        simpa [z] using congrArg Complex.re hz
      have hzi : Υ t = 0 := by
        simpa [z] using congrArg Complex.im hz
      have hzero : Ξ t ^ 2 + Υ t ^ 2 = 0 := by simp [hzr, hzi]
      linarith
    have hnorm : ‖z‖ = Real.sqrt (Ξ t ^ 2 + Υ t ^ 2) := by
      rw [Complex.norm_def]
      simp [z, Complex.normSq_apply, pow_two]
    have hcos : Real.cos z.arg = Ξ t / ‖z‖ := by
      simpa using Complex.cos_arg hz
    have hsin : Real.sin z.arg = Υ t / ‖z‖ := by
      simpa using Complex.sin_arg z
    have hnorm_ne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    refine ⟨Ξ t ^ 2 + Υ t ^ 2, ℏ * z.arg, hρ, ?_, ?_⟩
    · have hangle : (ℏ * z.arg) / ℏ = z.arg := by
        field_simp
      rw [hangle, hcos, hnorm]
      field_simp
    · have hangle : (ℏ * z.arg) / ℏ = z.arg := by
        field_simp
      rw [hangle, hsin, hnorm]
      field_simp

/-- The continuity equation holds for a finite zero-mode (constant density and phase). -/
theorem continuityEquation_constant (ρ S ℏ m τ q : ℝ) :
    deriv (fun _ : ℝ => ρ) τ +
        deriv (fun x : ℝ => ρ * deriv (fun _ : ℝ => S) x / m) q = 0 := by
  simp

/-- The Hamilton--Jacobi expression vanishes for the finite zero-mode with zero potential. -/
theorem quantumHamiltonJacobi_constant (S ρ ℏ m τ q : ℝ) :
    deriv (fun _ : ℝ => S) τ +
        (deriv (fun _ : ℝ => S) q) ^ 2 / (2 * m) + 0 +
          madelungQuantumPotential (fun _ : ℝ => ρ) ℏ m q = 0 := by
  simp [madelungQuantumPotential]

/-- An affine phase has the expected circulation on the unit interval. -/
theorem phaseCirculationLaw_affine (ℏ : ℝ) (m : ℤ) :
    (∫ t in (0 : ℝ)..1,
      deriv (fun x : ℝ => 2 * Real.pi * ℏ * (m : ℝ) * x) t) =
        2 * Real.pi * ℏ * (m : ℝ) := by
  let c : ℝ := 2 * Real.pi * ℏ * (m : ℝ)
  have hderiv :
      (fun t : ℝ => deriv (fun x : ℝ => c * x) t) = fun _ => c := by
    funext t
    simpa using ((hasDerivAt_id t).const_mul c).deriv
  change (∫ t in (0 : ℝ)..1, deriv (fun x : ℝ => c * x) t) = c
  rw [hderiv]
  simp [c]

/-- Constant channels give the finite zero-mode form of the constant-current law. -/
theorem constantCurrentCriterion_constant (Ξ Υ ρ S ℏ m : ℝ) :
    (∀ t, deriv (fun t =>
      madelungCurrent (fun _ : ℝ => Ξ) (fun _ : ℝ => Υ) ℏ m t) t = 0) ↔
      (∀ t, deriv (fun t => ρ * deriv (fun _ : ℝ => S) t) t = 0) := by
  simp [madelungCurrent]

end InfoGeometry.Canonical.MadelungScaleQuantum
