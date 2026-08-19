/-
InfoGeometry/Automorphic/SiegelWeilKudlaRallisBridge.lean

Witness-gated Siegel-Weil-Kudla-Rallis / doubling-method bridge.

This module processes the theorem payload of:

  Çetin Ürtiş,
  "Special values of L-functions by a Siegel-Weil-Kudla-Rallis formula",
  Journal of Number Theory 125 (2007), 149-181.

It does not prove the analytic Siegel-Weil formula, convergence of Eisenstein
series, theta correspondence, Euler products, rationality of Fourier
coefficients, or algebraicity of L-values from first principles.

It packages the paper-level analytic theorems as explicit witnesses and proves
the algebraic consequences that are constructively available from those
witnesses.
-/

import Mathlib.Tactic
import InfoGeometry.Automorphic.ProjectedLFunction

noncomputable section

namespace InfoGeometry.Automorphic.SiegelWeilKudlaRallisBridge

open InfoGeometry.Automorphic.SiegelResonance

/-! ## 1. Rational complex readouts -/

/-- A complex number is rational-valued if it lies in the embedded copy of `ℚ`. -/
def IsRationalComplex
    (z : ℂ) : Prop :=
  ∃ q : ℚ, z = (q : ℂ)

/-- Rational complex readouts are closed under equality transport. -/
theorem IsRationalComplex.of_eq
    {z w : ℂ}
    (hz : IsRationalComplex z)
    (hzw : z = w) :
    IsRationalComplex w := by
  rcases hz with ⟨q, hq⟩
  exact ⟨q, hzw ▸ hq⟩

/-! ## 2. Rankin-Selberg / theta doubling identity -/

/--
Rankin-Selberg theta integral representation property.

This is the algebraic interface for the paper's Theorem 1:

`⟨θ f₁ · E_s, θ f₂⟩_G =
  ⟨f₁, f₂⟩_H · L^S(s + 1/2, π ⊗ χ) · L_bad(s)`.

The concrete analytic content - theta lifts, measures, convergence,
bad-prime factors, and representation-theoretic hypotheses - is supplied by
the property fields.
-/
structure RankinSelbergThetaIntegralWitness
    (Cusp : Type*) where
  /-- Rankin-Selberg/theta pairing on the `G` side. -/
  rankinSelbergPairing :
    Cusp → Cusp → ℂ → ℂ

  /-- Inner product on the `H` side. -/
  innerProductH :
    Cusp → Cusp → ℂ

  /-- Standard Langlands L-function readout. -/
  standardL :
    ℂ → ℂ

  /-- Bad local factor product. -/
  badFactor :
    ℂ → ℂ

  /--
  Integral representation law.

  This is the paper-level theorem supplied as property data.
  -/
  rankinSelberg_identity :
    ∀ f₁ f₂ : Cusp, ∀ s : ℂ,
      rankinSelbergPairing f₁ f₂ s =
        innerProductH f₁ f₂ *
          standardL (s + (1 / 2 : ℂ)) *
            badFactor s

namespace RankinSelbergThetaIntegralWitness

variable {Cusp : Type*}
variable (R : RankinSelbergThetaIntegralWitness Cusp)

/-- Re-export of the Rankin-Selberg identity. -/
theorem pairing_eq_inner_mul_L_mul_bad
    (f₁ f₂ : Cusp)
    (s : ℂ) :
    R.rankinSelbergPairing f₁ f₂ s =
      R.innerProductH f₁ f₂ *
        R.standardL (s + (1 / 2 : ℂ)) *
          R.badFactor s :=
  R.rankinSelberg_identity f₁ f₂ s

/--
If the inner product and bad local factor are nonzero, the standard L-value is
recovered constructively as a quotient of the Rankin-Selberg pairing.

This is an actual processed consequence of Theorem 1.
-/
theorem standardL_eq_pairing_div_inner_bad
    (f₁ f₂ : Cusp)
    (s : ℂ)
    (hInner : R.innerProductH f₁ f₂ ≠ 0)
    (hBad : R.badFactor s ≠ 0) :
    R.standardL (s + (1 / 2 : ℂ)) =
      R.rankinSelbergPairing f₁ f₂ s /
        (R.innerProductH f₁ f₂ * R.badFactor s) := by
  rw [R.rankinSelberg_identity f₁ f₂ s]
  field_simp [hInner, hBad]

/-- Equivalent quotient orientation. -/
theorem pairing_div_inner_bad_eq_standardL
    (f₁ f₂ : Cusp)
    (s : ℂ)
    (hInner : R.innerProductH f₁ f₂ ≠ 0)
    (hBad : R.badFactor s ≠ 0) :
    R.rankinSelbergPairing f₁ f₂ s /
        (R.innerProductH f₁ f₂ * R.badFactor s) =
      R.standardL (s + (1 / 2 : ℂ)) :=
  (R.standardL_eq_pairing_div_inner_bad f₁ f₂ s hInner hBad).symm

end RankinSelbergThetaIntegralWitness

/-! ## 3. Siegel-Weil-Kudla-Rallis critical equality -/

/--
Siegel-Weil-Kudla-Rallis formula property.

This packages the paper's critical equality

`E(g, s₀, Φ) = Θ_{φ,1}(g)`.

The critical-range, convergence, local irreducibility, and invariant
distribution uniqueness obligations are represented by the supplied equality
law; this file does not recast them as Mathlib analytic closure.
-/
structure SiegelWeilKudlaRallisFormulaWitness
    (GState Value : Type*) where
  /-- Critical spectral point `s₀`. -/
  criticalPoint :
    ℂ

  /-- Siegel-Eisenstein value as a function of state and spectral parameter. -/
  eisenstein :
    GState → ℂ → Value

  /-- Theta lift of the trivial automorphic datum. -/
  thetaTrivial :
    GState → Value

  /-- Critical Siegel-Weil-Kudla-Rallis equality. -/
  siegel_weil_formula :
    ∀ g : GState, eisenstein g criticalPoint = thetaTrivial g

namespace SiegelWeilKudlaRallisFormulaWitness

variable {GState Value : Type*}
variable (S : SiegelWeilKudlaRallisFormulaWitness GState Value)

/-- At the critical point, Eisenstein equals the trivial theta lift. -/
theorem eisenstein_at_critical_eq_theta
    (g : GState) :
    S.eisenstein g S.criticalPoint = S.thetaTrivial g :=
  S.siegel_weil_formula g

end SiegelWeilKudlaRallisFormulaWitness

/-! ## 4. Pullback/decomposition formula -/

/--
Finite pullback/decomposition formula property.

This is the algebraic interface for the paper's decomposition formula:

`E_s(ι(g₁,g₂)) = Σ_f f(g₁) f̄(g₂) · λ(f) / ⟨f,f⟩`.

Here conjugation/bar behavior is intentionally absorbed into the supplied
second evaluation function.
-/
structure PullbackDecompositionFormulaWitness
    (Cusp GState : Type*) where
  /-- Finite orthogonal cusp-basis proxy. -/
  basis :
    Finset Cusp

  /-- Pullback Eisenstein readout. -/
  pullbackEisenstein :
    GState → GState → ℂ

  /-- First cusp evaluation. -/
  evalLeft :
    Cusp → GState → ℂ

  /-- Second/conjugate cusp evaluation. -/
  evalRight :
    Cusp → GState → ℂ

  /-- Coefficient `λ(f) / ⟨f,f⟩`. -/
  normalizedCoefficient :
    Cusp → ℂ

  /-- Decomposition formula. -/
  decomposition_law :
    ∀ g₁ g₂ : GState,
      pullbackEisenstein g₁ g₂ =
        basis.sum
          (fun f =>
            evalLeft f g₁ *
              evalRight f g₂ *
                normalizedCoefficient f)

namespace PullbackDecompositionFormulaWitness

variable {Cusp GState : Type*}
variable (D : PullbackDecompositionFormulaWitness Cusp GState)

/-- Re-export of the pullback decomposition formula. -/
theorem pullbackEisenstein_eq_sum
    (g₁ g₂ : GState) :
    D.pullbackEisenstein g₁ g₂ =
      D.basis.sum
        (fun f =>
          D.evalLeft f g₁ *
            D.evalRight f g₂ *
              D.normalizedCoefficient f) :=
  D.decomposition_law g₁ g₂

end PullbackDecompositionFormulaWitness

/-! ## 5. Rational Fourier and special-value property -/

/--
Rational finite-prime Fourier coefficient property.

This packages the paper's rationality result for finite parts of Fourier
coefficients without asserting a concrete Fourier expansion here.
-/
structure RationalFiniteFourierWitness
    (Cusp CoeffIndex : Type*) where
  /-- Finite-prime part of a Fourier coefficient. -/
  finiteFourierPart :
    Cusp → CoeffIndex → ℂ

  /-- Rationality of all supplied finite-prime Fourier parts. -/
  finiteFourierPart_rational :
    ∀ f : Cusp, ∀ a : CoeffIndex,
      IsRationalComplex (finiteFourierPart f a)

namespace RationalFiniteFourierWitness

variable {Cusp CoeffIndex : Type*}
variable (R : RationalFiniteFourierWitness Cusp CoeffIndex)

/-- Re-export of rational finite-prime Fourier coefficient readout. -/
theorem finiteFourierPart_is_rational
    (f : Cusp)
    (a : CoeffIndex) :
    IsRationalComplex (R.finiteFourierPart f a) :=
  R.finiteFourierPart_rational f a

end RationalFiniteFourierWitness

/--
Special-value rationality property.

This packages the paper's statement that the normalized coefficient
`λ(f) / ⟨f,f⟩` is rational.
-/
structure NormalizedSpecialValueRationalityWitness
    (Cusp : Type*) where
  /-- Coefficient `λ(f)`. -/
  lambda :
    Cusp → ℂ

  /-- Petersson/automorphic inner product `⟨f,f⟩`. -/
  selfInner :
    Cusp → ℂ

  /-- Normalized special-value readout. -/
  normalizedSpecialValue :
    Cusp → ℂ

  /-- Definitional/calibration law for the normalized value. -/
  normalizedSpecialValue_eq :
    ∀ f : Cusp, normalizedSpecialValue f = lambda f / selfInner f

  /-- Rationality law. -/
  normalizedSpecialValue_rational :
    ∀ f : Cusp, IsRationalComplex (normalizedSpecialValue f)

namespace NormalizedSpecialValueRationalityWitness

variable {Cusp : Type*}
variable (R : NormalizedSpecialValueRationalityWitness Cusp)

/-- The normalized special value is the quotient `λ(f) / ⟨f,f⟩`. -/
theorem normalized_eq_lambda_div_inner
    (f : Cusp) :
    R.normalizedSpecialValue f = R.lambda f / R.selfInner f :=
  R.normalizedSpecialValue_eq f

/-- The normalized special value is rational. -/
theorem normalized_is_rational
    (f : Cusp) :
    IsRationalComplex (R.normalizedSpecialValue f) :=
  R.normalizedSpecialValue_rational f

/-- The explicit quotient `λ(f) / ⟨f,f⟩` is rational. -/
theorem lambda_div_inner_is_rational
    (f : Cusp) :
    IsRationalComplex (R.lambda f / R.selfInner f) :=
  IsRationalComplex.of_eq
    (R.normalized_is_rational f)
    (R.normalized_eq_lambda_div_inner f)

end NormalizedSpecialValueRationalityWitness

/-! ## 6. Bridge to existing projected L-function data -/

/--
Projected L-function data supplied by a Rankin-Selberg/theta integral model.

This connects the SWKR/doubling-method lane to the existing
`ProjectedAutomorphicLFunctionData` API by a supplied equality between the
projected L-function and the standard L-function readout.
-/
structure RankinSelbergProjectedLBridge
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (P : ProjectedAutomorphicLFunctionData W)
    (Cusp : Type*) where
  /-- Rankin-Selberg theta integral property. -/
  rankinSelberg :
    RankinSelbergThetaIntegralWitness Cusp

  /--
  Compatibility between the existing projected L-function and the standard
  L-function readout from the Rankin-Selberg model.
  -/
  projected_eq_standard :
    ∀ s : ℂ, P.L s = rankinSelberg.standardL s

namespace RankinSelbergProjectedLBridge

variable
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {P : ProjectedAutomorphicLFunctionData W}
    {Cusp : Type*}

variable (B : RankinSelbergProjectedLBridge P Cusp)

/-- Existing projected L-function equals the Rankin-Selberg standard L-readout. -/
theorem projectedL_eq_standardL
    (s : ℂ) :
    P.L s = B.rankinSelberg.standardL s :=
  B.projected_eq_standard s

/--
If inner product and bad factor are nonzero, the existing projected L-function
value at `s + 1/2` is recovered from the Rankin-Selberg pairing.
-/
theorem projectedL_shift_eq_pairing_div_inner_bad
    (f₁ f₂ : Cusp)
    (s : ℂ)
    (hInner : B.rankinSelberg.innerProductH f₁ f₂ ≠ 0)
    (hBad : B.rankinSelberg.badFactor s ≠ 0) :
    P.L (s + (1 / 2 : ℂ)) =
      B.rankinSelberg.rankinSelbergPairing f₁ f₂ s /
        (B.rankinSelberg.innerProductH f₁ f₂ *
          B.rankinSelberg.badFactor s) := by
  rw [B.projectedL_eq_standardL]
  exact
    B.rankinSelberg.standardL_eq_pairing_div_inner_bad
      f₁ f₂ s hInner hBad

end RankinSelbergProjectedLBridge

end InfoGeometry.Automorphic.SiegelWeilKudlaRallisBridge
