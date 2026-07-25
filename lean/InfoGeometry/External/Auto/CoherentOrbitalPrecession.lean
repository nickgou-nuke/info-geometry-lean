import Mathlib.Tactic

/-!
# Coherent orbital precession

Theorem-honest digest of
`https://github.com/tuchaki81/Coherent-Orbital-Precession`.

The repository implements a phenomenological scalar-tensor extension of GR
with a coherence field `Φ`, an orbital asymmetry parameter

`Ξ = e²/(1-e²) · r_g/a`,

a fractional precession correction `δ = λ_eff² Ξ`, and a corrected precession
`Δφ = Δφ_GR(1+δ)`.  This module proves the algebraic invariants that the
Python implementation tests: unit-independence of `Ξ`, GR recovery at
`λ_eff=0`, circular-orbit vanishing, non-negativity of `δ` when `Ξ≥0`, and
zero/linear behavior of the coherence tensor skeleton.

Numerical astrophysical catalog values and the physical validity of the
proposed scalar-tensor model are outside the finite algebra checked here.
-/

noncomputable section

namespace CoherentOrbitalPrecession

open Matrix

/-! ## 1. Core scalar-tensor / orbital equations -/

/-- Orbital asymmetry parameter `Ξ = e²/(1-e²) · r_g/a`. -/
def asymmetryParameter (e rg a : ℝ) : ℝ :=
  (e ^ 2 / (1 - e ^ 2)) * (rg / a)

/-- Fractional correction `δ = λ_eff² Ξ`. -/
def fractionalCorrection (lambdaEff Xi : ℝ) : ℝ :=
  lambdaEff ^ 2 * Xi

/-- Corrected precession `Δφ = Δφ_GR(1+δ)`. -/
def correctedPrecession (precessionGR lambdaEff Xi : ℝ) : ℝ :=
  precessionGR * (1 + fractionalCorrection lambdaEff Xi)

/-- GR periapsis advance per orbit in radians:
`6πGM/(c² a(1-e²))`. -/
def grPrecessionPerOrbit (G M c a e : ℝ) : ℝ :=
  6 * Real.pi * G * M / (c ^ 2 * a * (1 - e ^ 2))

@[simp] theorem asymmetry_circular_orbit (rg a : ℝ) :
    asymmetryParameter 0 rg a = 0 := by
  simp [asymmetryParameter]

@[simp] theorem fractionalCorrection_zero_lambda (Xi : ℝ) :
    fractionalCorrection 0 Xi = 0 := by
  simp [fractionalCorrection]

@[simp] theorem correctedPrecession_zero_lambda (precessionGR Xi : ℝ) :
    correctedPrecession precessionGR 0 Xi = precessionGR := by
  simp [correctedPrecession, fractionalCorrection]

theorem fractionalCorrection_nonnegative
    (lambdaEff Xi : ℝ) (hXi : 0 ≤ Xi) :
    0 ≤ fractionalCorrection lambdaEff Xi := by
  unfold fractionalCorrection
  exact mul_nonneg (sq_nonneg lambdaEff) hXi

/-- `Ξ` is invariant under a common rescaling of both length variables. -/
theorem asymmetryParameter_unit_invariant
    (e rg a scale : ℝ) (ha : a ≠ 0) (hs : scale ≠ 0) :
    asymmetryParameter e (scale * rg) (scale * a) =
      asymmetryParameter e rg a := by
  unfold asymmetryParameter
  field_simp [ha, hs]

/-! ## 2. Coherence tensor skeleton -/

abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ

/-- Coherence tensor skeleton:
`C_μν = λ(∇_μ∇_ν Φ - g_μν □Φ)`. -/
def coherenceTensor (lambda : ℝ) (hessian metric : M4R) (boxPhi : ℝ) : M4R :=
  lambda • (hessian - boxPhi • metric)

@[simp] theorem coherenceTensor_zero_lambda
    (hessian metric : M4R) (boxPhi : ℝ) :
    coherenceTensor 0 hessian metric boxPhi = 0 := by
  simp [coherenceTensor]

@[simp] theorem coherenceTensor_zero_field
    (lambda : ℝ) (metric : M4R) :
    coherenceTensor lambda 0 metric 0 = 0 := by
  simp [coherenceTensor]

theorem coherenceTensor_linear_lambda
    (lambda₁ lambda₂ : ℝ) (hessian metric : M4R) (boxPhi : ℝ) :
    coherenceTensor (lambda₁ + lambda₂) hessian metric boxPhi =
      coherenceTensor lambda₁ hessian metric boxPhi +
      coherenceTensor lambda₂ hessian metric boxPhi := by
  ext i j
  simp [coherenceTensor, add_mul]

/-! ## 3. Exact rational table values from the repository readout -/

/-- PSR B1913+16 table value `λ_eff = 1.95` used in repository arithmetic. -/
def psrB1913LambdaValue : ℚ := 195 / 100

/-- Rounded table asymmetry for Mercury: about `2.3×10⁻⁹`. -/
def mercuryXiTable : ℚ := 23 / 10000000000

/-- Rounded implementation asymmetry for S2: about `2.63×10⁻⁴`. -/
def s2XiTable : ℚ := 263 / 1000000

/-- Rounded inner S-star asymmetry: about `7.3×10⁻³`. -/
def innerSStarXiTable : ℚ := 73 / 10000

/-- Rational analogue of `δ = λ_eff² Ξ`. -/
def fractionalCorrectionQ (lambdaEff Xi : ℚ) : ℚ :=
  lambdaEff ^ 2 * Xi

@[simp] theorem psr_value_eq :
    psrB1913LambdaValue = 195 / 100 := rfl

theorem mercury_delta_at_psr_value :
    fractionalCorrectionQ psrB1913LambdaValue mercuryXiTable =
      69966 / 8000000000000 := by
  norm_num [fractionalCorrectionQ, psrB1913LambdaValue, mercuryXiTable]

theorem s2_delta_at_psr_value :
    fractionalCorrectionQ psrB1913LambdaValue s2XiTable =
      400023 / 400000000 := by
  norm_num [fractionalCorrectionQ, psrB1913LambdaValue, s2XiTable]

theorem inner_sstar_delta_at_psr_value :
    fractionalCorrectionQ psrB1913LambdaValue innerSStarXiTable =
      111033 / 4000000 := by
  norm_num [fractionalCorrectionQ, psrB1913LambdaValue, innerSStarXiTable]

end CoherentOrbitalPrecession
