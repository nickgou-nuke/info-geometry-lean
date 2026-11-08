import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# Amari Information Geometry of the Riemann Zeta Simplex

This module formalizes the dually flat (Hessian) information geometry of the
complexified 1-simplex carrying the spectral parameter `s` of the Riemann zeta
function, following Shun-ichi Amari's framework [1].

## Geometric Structure

The binary statistical simplex `Δ¹ = { (p, q) ∈ ℝ>0² | p + q = 1 }` carries two
mutually dual, flat affine geometries connected by a Legendre transformation:

### 1. Mixture Geometry (m-flat, α = -1)
- **Affine coordinate**: `η = s ∈ (0, 1)`
- **Linear convex combination**: `(p, q) = (s, 1-s)`
- **Negative entropy potential**: `ϕ(η) = -S(η) = η ln η + (1-η) ln(1-η)`
- **Geometry**: Standard affine lines `s(λ) = (1-λ)s₁ + λ s₂`

### 2. Exponential Geometry (e-flat, α = +1)
- **Natural coordinate**: `θ = W = ln(s/(1-s)) ∈ (-∞, +∞)` (logit/surprisal)
- **Exponential family form**: `P_s(x) = exp(θ x - ψ(θ))`, `x ∈ {0, 1}`
- **Massieu potential**: `ψ(θ) = ln(1 + e^θ) = -ln(1-s)`
- **Geometry**: Straight lines in `θ` are multiplicative interpolations

### 3. Legendre Duality
```
         θ ↦ s = ∇ψ(θ) = e^θ/(1+e^θ)     s ↦ θ = ∇ϕ(s) = ln(s/(1-s))
    ψ(θ) = ln(1+e^θ)  ◄──────────────►  ϕ(s) = s ln s + (1-s) ln(1-s)
         ψ''(θ) = s(1-s)                 ϕ''(s) = 1/(s(1-s))
```

### 4. Self-Dual Symmetry Seam
- **Mixture coordinate**: `η = 1/2` (midpoint of simplex)
- **Exponential coordinate**: `θ = 0` (zero surprisal, τ = 1)
- **Functional reflection**: `η ↦ 1-η` (affine) ↔ `θ ↦ -θ` (parity, τ ↦ 1/τ)

### 5. Complexification: Critical Line
- **m-flat**: Critical line `Re(s) = 1/2` is vertical axis through symmetry seam
- **e-flat**: Critical line maps to `Re(θ) = 0` (Lee-Yang unit circle `|τ| = 1`)
- **Cayley transform**: `τ = (s-1/2)/(s+1/2)` maps critical line to unit circle

### 6. Bregman / Fenchel-Young Divergence
```
ℰ(s ∥ 1/2) = ψ(θ) + ϕ(1/2) - θ·(1/2)
           = -ln(1-s) - ln 2 - ½ ln(s/(1-s))
           = ln 2 + s ln s + (1-s) ln(1-s) ≥ 0
```
Equality iff `s = 1/2`.

## References
[1] Amari, S. "Information Geometry and Its Applications" (2016)
[2] Amari, S., Nagaoka, H. "Methods of Information Geometry" (2000)
-/

noncomputable section

namespace InfoGeometry.Canonical.AmariZetaSimplex

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open Complex
open Real

/-- The mixture (affine) coordinate on the 1-simplex: η = s ∈ (0, 1) -/
def mixtureCoordinate (s : ℂ) : ℂ := s

/-- The exponential (natural) coordinate: θ = W = ln(s/(1-s)) -/
def exponentialCoordinate (s : ℂ) : ℂ :=
  Complex.log (s / (1 - s))

/-- The logit / cross-ratio: τ = s/(1-s) = e^θ -/
def logit (s : ℂ) : ℂ :=
  s / (1 - s)

/-- The surprisal: W = ln τ = θ -/
def surprisal (s : ℂ) : ℂ :=
  exponentialCoordinate s

/-- The Massieu potential (primal, free energy): ψ(θ) = ln(1 + e^θ) = -ln(1-s) -/
def massieuPotential (θ : ℂ) : ℂ :=
  Complex.log (1 + Complex.exp θ)

/-- The Shannon potential (dual, negative entropy): ϕ(η) = η ln η + (1-η) ln(1-η) -/
def shannonPotential (η : ℂ) : ℂ :=
  η * Complex.log η + (1 - η) * Complex.log (1 - η)

/-- The gradient of ψ: ∇ψ(θ) = e^θ/(1+e^θ) = s = η -/
def massieuGradient (θ : ℂ) : ℂ :=
  Complex.exp θ / (1 + Complex.exp θ)

/-- The gradient of ϕ: ∇ϕ(η) = ln(η/(1-η)) = θ -/
def shannonGradient (η : ℂ) : ℂ :=
  Complex.log (η / (1 - η))

/-- Fisher-Rao metric in exponential coordinates: g(θ) = ψ''(θ) = s(1-s) -/
def fisherMetricExp (θ : ℂ) : ℂ :=
  let s := massieuGradient θ
  s * (1 - s)

/-- Fisher-Rao metric in mixture coordinates: g(η) = ϕ''(η) = 1/(s(1-s)) -/
def fisherMetricMix (η : ℂ) : ℂ :=
  1 / (η * (1 - η))

/-- The self-dual midpoint in mixture coordinates: η = 1/2 -/
def mixtureMidpoint : ℂ := 1 / 2

/-- The self-dual origin in exponential coordinates: θ = 0 -/
def exponentialOrigin : ℂ := 0

/-- Functional reflection in mixture coordinates: η ↦ 1-η -/
def mixtureReflection (η : ℂ) : ℂ := 1 - η

/-- Functional reflection in exponential coordinates: θ ↦ -θ (parity inversion) -/
def exponentialReflection (θ : ℂ) : ℂ := -θ

/-- Bregman / Fenchel-Young divergence from s to the symmetric center 1/2:
    ℰ(s ∥ 1/2) = ψ(θ) + ϕ(1/2) - θ·(1/2)
    = ln 2 + s ln s + (1-s) ln(1-s) -/
def bregmanDivergenceToMidpoint (s : ℂ) : ℂ :=
  let θ := exponentialCoordinate s
  massieuPotential θ + shannonPotential (mixtureMidpoint : ℂ) - θ * (mixtureMidpoint : ℂ)

/-- Simplified form of the Bregman divergence to midpoint:
    ℰ(s ∥ 1/2) = ln 2 + s ln s + (1-s) ln(1-s) -/
def bregmanDivergenceToMidpoint_simplified (s : ℂ) : ℂ :=
  Real.log 2 + (s * Complex.log s + (1 - s) * Complex.log (1 - s))

/-- The Cayley transform mapping critical line to unit circle:
    τ = (s - 1/2) / (s + 1/2) -/
def cayleyTransform (s : ℂ) : ℂ :=
  (s - 1/2) / (s + 1/2)

/-- The critical line condition in mixture coordinates: Re(s) = 1/2 -/
def isOnCriticalLineMix (s : ℂ) : Prop := s.re = 1/2

/-- The critical line condition in exponential coordinates: Re(θ) = 0 -/
def isOnCriticalLineExp (θ : ℂ) : Prop := θ.re = 0

/-- The Lee-Yang unit circle condition: |τ| = 1 -/
def isOnLeeYangCircle (τ : ℂ) : Prop := Complex.normSq τ = 1

/-- The binary statistical simplex as a type:
    Δ¹ = { (p, q) ∈ ℝ>0² | p + q = 1 } -/
structure BinarySimplex : Type where
  p : ℝ
  q : ℝ
  hp_pos : 0 < p
  hq_pos : 0 < q
  hpq_sum : p + q = 1

/-- The mixture coordinate of a simplex point -/
def BinarySimplex.mixtureCoordinate (x : BinarySimplex) : ℝ := x.p

/-- The exponential coordinate of a simplex point -/
def BinarySimplex.exponentialCoordinate (x : BinarySimplex) : ℝ :=
  Real.log (x.p / x.q)

/-- The logit of a simplex point -/
def BinarySimplex.logit (x : BinarySimplex) : ℝ := x.p / x.q

/-- The Shannon entropy of a simplex point -/
def BinarySimplex.shannonEntropy (x : BinarySimplex) : ℝ :=
  -(x.p * Real.log x.p + x.q * Real.log x.q)

/-- The Massieu potential of a simplex point -/
def BinarySimplex.massieuPotential (x : BinarySimplex) : ℝ :=
  Real.log (1 + Real.exp (x.exponentialCoordinate))

/-- The Fisher-Rao metric at a simplex point -/
def BinarySimplex.fisherMetric (x : BinarySimplex) : ℝ := x.p * x.q

/-- The Bregman divergence from a simplex point to the midpoint (1/2, 1/2) -/
def BinarySimplex.bregmanToMidpoint (x : BinarySimplex) : ℝ :=
  Real.log 2 + x.p * Real.log x.p + x.q * Real.log x.q

/-- The midpoint of the simplex -/
def BinarySimplex.midpoint : BinarySimplex :=
  ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num⟩

/-- Mixture geodesic (linear interpolation) between two simplex points -/
def BinarySimplex.mixtureGeodesic (x y : BinarySimplex) (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1) : BinarySimplex :=
  ⟨(1 - lam) * x.p + lam * y.p, (1 - lam) * x.q + lam * y.q,
    by
      have h₁ : 0 < (1 - lam) * x.p + lam * y.p := by
        have h₂ : 0 ≤ 1 - lam := by linarith
        have h₃ : 0 ≤ lam := by linarith
        have h₄ : 0 < x.p := x.hp_pos
        have h₅ : 0 < y.p := y.hp_pos
        have h₆ : 0 ≤ (1 - lam) * x.p := by positivity
        have h₇ : 0 ≤ lam * y.p := by positivity
        have h₈ : 0 < (1 - lam) * x.p + lam * y.p := by
          by_cases h₉ : (1 - lam) = 0
          · have h₁₀ : lam = 1 := by linarith
            rw [h₁₀]
            positivity
          · have h₁₀ : 0 < 1 - lam := by
              contrapose! h₉
              linarith
            have h₁₁ : 0 < (1 - lam) * x.p := by positivity
            linarith
        exact h₈
      exact h₁,
    by
      have h₁ : 0 < (1 - lam) * x.q + lam * y.q := by
        have h₂ : 0 ≤ 1 - lam := by linarith
        have h₃ : 0 ≤ lam := by linarith
        have h₄ : 0 < x.q := x.hq_pos
        have h₅ : 0 < y.q := y.hq_pos
        have h₆ : 0 ≤ (1 - lam) * x.q := by positivity
        have h₇ : 0 ≤ lam * y.q := by positivity
        have h₈ : 0 < (1 - lam) * x.q + lam * y.q := by
          by_cases h₉ : (1 - lam) = 0
          · have h₁₀ : lam = 1 := by linarith
            rw [h₁₀]
            positivity
          · have h₁₀ : 0 < 1 - lam := by
              contrapose! h₉
              linarith
            have h₁₁ : 0 < (1 - lam) * x.q := by positivity
            linarith
        exact h₈
      exact h₁,
    by
      have h₁ : ((1 - lam) * x.p + lam * y.p) + ((1 - lam) * x.q + lam * y.q) = 1 := by
        have h₂ : x.p + x.q = 1 := x.hpq_sum
        have h₃ : y.p + y.q = 1 := y.hpq_sum
        nlinarith
      exact h₁⟩

/-- Exponential geodesic (log-linear interpolation) between two simplex points -/
def BinarySimplex.exponentialGeodesic (x y : BinarySimplex) (lam : ℝ) : BinarySimplex :=
  let θ₁ := x.exponentialCoordinate
  let θ₂ := y.exponentialCoordinate
  let θ := (1 - lam) * θ₁ + lam * θ₂
  let p := Real.exp θ / (1 + Real.exp θ)
  let q := 1 / (1 + Real.exp θ)
  ⟨p, q,
    by
      have h₁ : 0 < p := by positivity
      exact h₁,
    by
      have h₁ : 0 < q := by positivity
      exact h₁,
    by
      have h₁ : p + q = 1 := by
        have h₂ : p = Real.exp θ / (1 + Real.exp θ) := rfl
        have h₃ : q = 1 / (1 + Real.exp θ) := rfl
        rw [h₂, h₃]
        have h₄ : 1 + Real.exp θ ≠ 0 := by positivity
        field_simp [h₄]
        <;> ring_nf
        <;> field_simp [h₄]
        <;> ring_nf
      exact h₁⟩

/-- The Amari duality structure on the zeta simplex -/
structure AmariZetaDuality where
  /-- The mixture coordinate η = s -/
  η : ℂ
  /-- The exponential coordinate θ = W -/
  θ : ℂ
  /-- The logit τ = e^θ = s/(1-s) -/
  τ : ℂ
  /-- The duality relations -/
  η_eq_mixture : η = τ / (1 + τ)
  θ_eq_exponential : θ = Complex.log τ
  τ_eq_logit : τ = η / (1 - η)
  /-- The Legendre dual potentials -/
  ψ : ℂ → ℂ
  ϕ : ℂ → ℂ
  ψ_def : ∀ θ, ψ θ = Complex.log (1 + Complex.exp θ)
  ϕ_def : ∀ η, ϕ η = η * Complex.log η + (1 - η) * Complex.log (1 - η)
  /-- Gradient duality -/
  gradient_ψ : ∀ θ, massieuGradient θ = Complex.exp θ / (1 + Complex.exp θ)
  gradient_ϕ : ∀ η, shannonGradient η = Complex.log (η / (1 - η))
  /-- Fisher metric duality -/
  fisher_duality : ∀ (θ : ℂ), fisherMetricExp θ = 1 / fisherMetricMix (massieuGradient θ)
  /-- Self-dual midpoint -/
  midpoint_mixture : η = 1/2 ↔ θ = 0
  /-- Functional reflection duality -/
  reflection_duality : mixtureReflection η = 1 - η ∧ exponentialReflection θ = -θ

/-- The canonical Amari duality instance for the zeta simplex -/
def canonicalAmariZetaDuality (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) : AmariZetaDuality :=
  ⟨s, exponentialCoordinate s, logit s,
   by
     -- Prove η = τ / (1 + τ) where η = s and τ = logit s
     have h₁ : logit s = s / (1 - s) := rfl
     have h₂ : (s : ℂ) = (logit s : ℂ) / (1 + logit s) := by
       rw [h₁]
       field_simp [sub_ne_zero.mpr (Ne.symm hs1), add_comm]
       ring_nf
     simpa [h₁] using h₂,
   by
     -- Prove θ = log τ where θ = exponentialCoordinate s and τ = logit s
     have h₁ : exponentialCoordinate s = Complex.log (s / (1 - s)) := rfl
     have h₂ : logit s = s / (1 - s) := rfl
     simp_all [exponentialCoordinate, logit]
     <;>
     (try ring_nf) <;>
     (try field_simp [Complex.log_div, Complex.log_mul, Complex.log_rpow, Complex.log_one]) <;>
     (try simp_all [Complex.ext_iff]) <;>
     (try norm_num) <;>
     (try linarith),
   by
     -- Prove τ = η / (1 - η) where η = s and τ = logit s
     have h₁ : logit s = s / (1 - s) := rfl
     have h₂ : (logit s : ℂ) = (s : ℂ) / (1 - s) := by simp [logit]
     simpa [h₁] using h₂,
   massieuPotential,
   shannonPotential,
   by intro θ; simp [massieuPotential],
   by intro η; simp [shannonPotential],
   by intro θ; simp [massieuGradient],
   by intro η; simp [shannonGradient],
   by
     intro θ
     simp [fisherMetricExp, fisherMetricMix, massieuGradient]
     <;> field_simp [Complex.exp_ne_zero, add_comm]
     <;> ring_nf
     <;> field_simp [Complex.exp_ne_zero, add_comm]
     <;> ring_nf,
   by
     constructor
     · intro h
       -- Prove η = 1/2 → θ = 0
       have h₁ : s = 1/2 := by simpa [mixtureCoordinate, mixtureMidpoint] using h
       have h₂ : exponentialCoordinate s = 0 := by
         rw [exponentialCoordinate] at *
         have h₃ : s = 1/2 := h₁
         rw [h₃]
         simp [Complex.log_one]
         <;> norm_num
         <;> field_simp [Complex.ext_iff] <;> norm_num
       simpa [exponentialOrigin] using h₂
     · intro h
       -- Prove θ = 0 → η = 1/2
       have h₁ : exponentialCoordinate s = 0 := by simpa [exponentialOrigin] using h
       have h₂ : s = 1/2 := by
         rw [exponentialCoordinate] at h₁
         have h₃ : Complex.log (s / (1 - s)) = 0 := h₁
         have h₄ : s / (1 - s) = 1 := by
           have hratio0 : s / (1 - s) ≠ 0 :=
             div_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))
           have hExp := congrArg Complex.exp h₃
           simpa [Complex.exp_log hratio0] using hExp
         have h₅ : s = 1/2 := by
           have h₆ : s / (1 - s) = 1 := h₄
           field_simp [sub_ne_zero.mpr (Ne.symm hs1)] at h₆
           linear_combination h₆ / 2
         exact h₅
       simpa [mixtureCoordinate, mixtureMidpoint] using h₂,
   by
     constructor
     · simp [mixtureReflection]
     · simp [exponentialReflection]⟩

end InfoGeometry.Canonical.AmariZetaSimplex
