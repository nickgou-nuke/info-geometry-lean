import InfoGeometry.Conformal.ComplexSchwarzianJet
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.BipolarLocalConformalCoordinate
import Mathlib.Tactic

/-!
# Schwarzian projective connection of the bipolar logarithmic coordinate

The Möbius coordinate `q(s)=s/(1-s)` has zero Schwarzian.  A local branch of
`W=log q` has the branch-independent derivative tower

`W'  = 1/s + 1/(1-s)`,
`W'' = -1/s² + 1/(1-s)²`,
`W''' = 2/s³ + 2/(1-s)³`.

Its Schwarzian is therefore the globally defined meromorphic quadratic
coefficient

`S_W(s)=1/(2 s² (1-s)²)=1/2 (dlog01(s))²`.

This is a projective-connection coefficient determined by the logarithmic
coordinate.  Calling a scalar multiple of it a physical CFT stress tensor
requires additional state and convention data and is not done in this file.
-/

noncomputable section

namespace InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarLocalConformalCoordinate
open InfoGeometry.Conformal.ComplexSchwarzianJet

/-- Reciprocal affine denominator of the canonical Möbius coordinate. -/
def oneMinusInv (s : ℂ) : ℂ :=
  (1 - s)⁻¹

/-- First derivative coefficient of `q(s)=s/(1-s)`. -/
def crossRatioJet₁ (s : ℂ) : ℂ :=
  oneMinusInv s ^ 2

/-- Second derivative coefficient of `q`. -/
def crossRatioJet₂ (s : ℂ) : ℂ :=
  2 * oneMinusInv s ^ 3

/-- Third derivative coefficient of `q`. -/
def crossRatioJet₃ (s : ℂ) : ℂ :=
  6 * oneMinusInv s ^ 4

/-- First derivative coefficient of a local branch of `W=log q`. -/
def logarithmicJet₁ (s : ℂ) : ℂ :=
  dlog01 s

/-- Second derivative coefficient of a local branch of `W`. -/
def logarithmicJet₂ (s : ℂ) : ℂ :=
  -(s⁻¹) ^ 2 + crossRatioJet₁ s

/-- Third derivative coefficient of a local branch of `W`. -/
def logarithmicJet₃ (s : ℂ) : ℂ :=
  2 * (s⁻¹) ^ 3 + crossRatioJet₂ s

/-- The reciprocal affine denominator has derivative `(1-s)⁻²`. -/
theorem hasDerivAt_oneMinusInv
    {s : ℂ} (hs : 1 - s ≠ 0) :
    HasDerivAt oneMinusInv (oneMinusInv s ^ 2) s := by
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)
  convert hsub.inv hs using 1
  simp [oneMinusInv, div_eq_mul_inv]

/-- The installed first derivative of `q` agrees with the canonical jet. -/
theorem hasDerivAt_crossRatio01_jet
    {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt crossRatio01 (crossRatioJet₁ s) s := by
  convert hasDerivAt_crossRatio01 hs.2 using 1
  simp [crossRatioJet₁, oneMinusInv, div_eq_mul_inv]

/-- The first derivative coefficient of `q` differentiates to its second jet. -/
theorem hasDerivAt_crossRatioJet₁
    {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt crossRatioJet₁ (crossRatioJet₂ s) s := by
  have h := (hasDerivAt_oneMinusInv (one_sub_ne_zero_of_mem hs)).pow 2
  convert h using 1 <;>
    simp [crossRatioJet₁, crossRatioJet₂] <;> ring

/-- The second derivative coefficient of `q` differentiates to its third jet. -/
theorem hasDerivAt_crossRatioJet₂
    {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt crossRatioJet₂ (crossRatioJet₃ s) s := by
  have h :=
    ((hasDerivAt_oneMinusInv (one_sub_ne_zero_of_mem hs)).pow 3).const_mul
      (2 : ℂ)
  convert h using 1 <;>
    simp [crossRatioJet₂, crossRatioJet₃] <;> ring

/-- The global logarithmic one-form differentiates to the second logarithmic
jet away from both punctures. -/
theorem hasDerivAt_logarithmicJet₁
    {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt logarithmicJet₁ (logarithmicJet₂ s) s := by
  have h₀ := (hasDerivAt_id s).inv hs.1
  have h₁ := hasDerivAt_oneMinusInv (one_sub_ne_zero_of_mem hs)
  convert h₀.add h₁ using 1
  · funext z
    dsimp [logarithmicJet₁, dlog01, oneMinusInv]
    ring
  · dsimp [logarithmicJet₂, dlog01, oneMinusInv, crossRatioJet₁]
    ring

/-- The second logarithmic jet differentiates to the third logarithmic jet. -/
theorem hasDerivAt_logarithmicJet₂
    {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt logarithmicJet₂ (logarithmicJet₃ s) s := by
  have hInv₀ := (hasDerivAt_id s).inv hs.1
  have hOrigin := (hInv₀.pow 2).neg
  have hOne := hasDerivAt_crossRatioJet₁ hs
  convert hOrigin.add hOne using 1 <;>
    simp [logarithmicJet₂, logarithmicJet₃, crossRatioJet₁,
      crossRatioJet₂, div_eq_mul_inv] <;> ring

/-- Certified local third-order derivative tower for the principal logarithmic
branch wherever the branch derivative theorem applies. -/
theorem local_bipolarLog_thirdJet
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt bipolarLog (logarithmicJet₁ s) s ∧
      HasDerivAt logarithmicJet₁ (logarithmicJet₂ s) s ∧
      HasDerivAt logarithmicJet₂ (logarithmicJet₃ s) s := by
  exact ⟨hasDerivAt_bipolarLog hs hslit,
    hasDerivAt_logarithmicJet₁ hs,
    hasDerivAt_logarithmicJet₂ hs⟩

/-- Rational normal form of the second logarithmic jet. -/
theorem logarithmicJet₂_eq_rational
    {s : ℂ} (hs : s ∈ punctured01) :
    logarithmicJet₂ s =
      (2 * s - 1) / (s ^ 2 * (s - 1) ^ 2) := by
  have h₀ : s ≠ 0 := hs.1
  have h₁ : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  have h₂ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  unfold logarithmicJet₂ crossRatioJet₁ oneMinusInv
  field_simp [h₀, h₁, h₂]
  ring

/-- Rational normal form of the third logarithmic jet. -/
theorem logarithmicJet₃_eq_rational
    {s : ℂ} (hs : s ∈ punctured01) :
    logarithmicJet₃ s =
      (-6 * s ^ 2 + 6 * s - 2) /
        (s ^ 3 * (s - 1) ^ 3) := by
  have h₀ : s ≠ 0 := hs.1
  have h₁ : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  have h₂ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  unfold logarithmicJet₃ crossRatioJet₂ oneMinusInv
  field_simp [h₀, h₁, h₂]
  ring

/-- Schwarzian coefficient of the canonical Möbius coordinate. -/
def crossRatioSchwarzian (s : ℂ) : ℂ :=
  schwarzianJet (crossRatioJet₁ s) (crossRatioJet₂ s) (crossRatioJet₃ s)

/-- The Möbius coordinate has identically zero Schwarzian away from its pole. -/
theorem crossRatioSchwarzian_eq_zero
    {s : ℂ} (hs : s ∈ punctured01) :
    crossRatioSchwarzian s = 0 := by
  have h₁ : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  unfold crossRatioSchwarzian schwarzianJet crossRatioJet₁
    crossRatioJet₂ crossRatioJet₃ oneMinusInv
  field_simp [h₁]
  ring

/-- Branch-independent Schwarzian coefficient of the logarithmic coordinate. -/
def bipolarSchwarzian (s : ℂ) : ℂ :=
  schwarzianJet (logarithmicJet₁ s) (logarithmicJet₂ s) (logarithmicJet₃ s)

/-- Rational representative of the logarithmic Schwarzian away from the two
punctures. -/
def bipolarSchwarzianRational (s : ℂ) : ℂ :=
  1 / (2 * s ^ 2 * (s - 1) ^ 2)

/-- Derivative coefficient of the rational Schwarzian representative. -/
def bipolarSchwarzianRationalDeriv (s : ℂ) : ℂ :=
  -(2 * s - 1) / (s ^ 3 * (s - 1) ^ 3)

/-- Polynomial denominator of the rational Schwarzian representative. -/
def schwarzianPoleDenominator (s : ℂ) : ℂ :=
  2 * s ^ 2 * (s - 1) ^ 2

/-- Derivative of the polynomial Schwarzian denominator. -/
def schwarzianPoleDenominatorDeriv (s : ℂ) : ℂ :=
  4 * s * (s - 1) * (2 * s - 1)

/-- Genuine derivative of the polynomial Schwarzian denominator. -/
theorem hasDerivAt_schwarzianPoleDenominator (s : ℂ) :
    HasDerivAt schwarzianPoleDenominator
      (schwarzianPoleDenominatorDeriv s) s := by
  have h₀ := (hasDerivAt_id s).pow 2
  have h₁ := ((hasDerivAt_id s).sub_const 1).pow 2
  have h := (h₀.mul h₁).const_mul (2 : ℂ)
  convert h using 1
  · funext y
    dsimp [schwarzianPoleDenominator]
    ring
  · dsimp [schwarzianPoleDenominatorDeriv]
    ring

/-- Genuine derivative of the rational Schwarzian representative. -/
theorem hasDerivAt_bipolarSchwarzianRational
    {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt bipolarSchwarzianRational
      (bipolarSchwarzianRationalDeriv s) s := by
  have h₀ : s ≠ 0 := hs.1
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  have hden : schwarzianPoleDenominator s ≠ 0 := by
    unfold schwarzianPoleDenominator
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 h₀))
      (pow_ne_zero 2 h₁)
  have hraw :=
    (hasDerivAt_const s (1 : ℂ)).div
      (hasDerivAt_schwarzianPoleDenominator s) hden
  change HasDerivAt
    (fun z : ℂ => 1 / schwarzianPoleDenominator z)
    (bipolarSchwarzianRationalDeriv s) s
  convert hraw using 1
  unfold bipolarSchwarzianRationalDeriv schwarzianPoleDenominator
    schwarzianPoleDenominatorDeriv
  field_simp [h₀, h₁]
  ring

/-- Exact quadratic-pole normal form of the logarithmic Schwarzian. -/
theorem bipolarSchwarzian_eq_rational
    {s : ℂ} (hs : s ∈ punctured01) :
    bipolarSchwarzian s =
      1 / (2 * s ^ 2 * (s - 1) ^ 2) := by
  have h₀ : s ≠ 0 := hs.1
  have h₁ : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  have h₂ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  rw [bipolarSchwarzian, logarithmicJet₁,
    logarithmicJet₂_eq_rational hs, logarithmicJet₃_eq_rational hs,
    dlog01_eq_one_div_mul hs]
  unfold schwarzianJet
  field_simp [h₀, h₁, h₂]
  ring

/-- Function-valued form of the rational normal-form theorem. -/
theorem bipolarSchwarzian_eq_rationalFunction
    {s : ℂ} (hs : s ∈ punctured01) :
    bipolarSchwarzian s = bipolarSchwarzianRational s := by
  simpa [bipolarSchwarzianRational] using
    bipolarSchwarzian_eq_rational hs

/-- The twice-punctured domain is open. -/
theorem isOpen_punctured01 : IsOpen punctured01 := by
  have hset :
      punctured01 = ({0}ᶜ ∩ {1}ᶜ : Set ℂ) := by
    ext z
    simp [punctured01]
  rw [hset]
  exact isClosed_singleton.isOpen_compl.inter
    isClosed_singleton.isOpen_compl

/-- The Schwarzian defined from the derivative jet has the genuine derivative
of its rational representative on the punctured domain. -/
theorem hasDerivAt_bipolarSchwarzian
    {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt bipolarSchwarzian
      (bipolarSchwarzianRationalDeriv s) s := by
  apply (hasDerivAt_bipolarSchwarzianRational hs).congr_of_eventuallyEq
  filter_upwards [isOpen_punctured01.mem_nhds hs] with z hz
  exact bipolarSchwarzian_eq_rationalFunction hz

/-- Ordinary derivative readout of the logarithmic Schwarzian. -/
theorem deriv_bipolarSchwarzian
    {s : ℂ} (hs : s ∈ punctured01) :
    deriv bipolarSchwarzian s = bipolarSchwarzianRationalDeriv s := by
  exact (hasDerivAt_bipolarSchwarzian hs).deriv

/-- The logarithmic Schwarzian is one half of the square of the global
logarithmic one-form coefficient. -/
theorem bipolarSchwarzian_eq_half_dlog01_sq
    {s : ℂ} (hs : s ∈ punctured01) :
    bipolarSchwarzian s = (1 / 2 : ℂ) * dlog01 s ^ 2 := by
  rw [bipolarSchwarzian_eq_rational hs, dlog01_eq_one_div_mul hs]
  have h₀ : s ≠ 0 := hs.1
  have h₁ : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  have h₂ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  field_simp [h₀, h₁, h₂]
  ring

/-- Pre-Schwarzian of the logarithmic coordinate. -/
theorem logarithmic_preSchwarzian
    {s : ℂ} (hs : s ∈ punctured01) :
    preSchwarzianJet (logarithmicJet₁ s) (logarithmicJet₂ s) =
      -(1 / s + 1 / (s - 1)) := by
  rw [logarithmicJet₁, logarithmicJet₂_eq_rational hs,
    dlog01_eq_one_div_mul hs]
  unfold preSchwarzianJet
  have h₀ : s ≠ 0 := hs.1
  have h₁ : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  have h₂ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  field_simp [h₀, h₁, h₂]
  ring

/-- Specialized Schwarzian composition factorization for `log ∘ q`.  The
second summand is retained explicitly to exhibit the vanishing Möbius term. -/
theorem bipolarSchwarzian_composition
    {s : ℂ} (hs : s ∈ punctured01) :
    bipolarSchwarzian s =
      schwarzianJet
          (1 / crossRatio01 s)
          (-1 / crossRatio01 s ^ 2)
          (2 / crossRatio01 s ^ 3) *
        crossRatioJet₁ s ^ 2 +
      crossRatioSchwarzian s := by
  have hq : crossRatio01 s ≠ 0 := crossRatio01_ne_zero hs
  rw [bipolarSchwarzian_eq_rational hs,
    logarithmJet_schwarzian (crossRatio01 s) hq,
    crossRatioSchwarzian_eq_zero hs]
  have h₀ : s ≠ 0 := hs.1
  have h₁ : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  have h₂ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  unfold crossRatioJet₁ oneMinusInv crossRatio01
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity
  field_simp [h₀, h₁, h₂]
  ring

/-- Compact Möbius/logarithm/Schwarzian packet. -/
theorem bipolar_schwarzian_packet
    {s : ℂ} (hs : s ∈ punctured01) :
    crossRatioSchwarzian s = 0 ∧
      bipolarSchwarzian s = 1 / (2 * s ^ 2 * (s - 1) ^ 2) ∧
      deriv bipolarSchwarzian s = bipolarSchwarzianRationalDeriv s ∧
      bipolarSchwarzian s = (1 / 2 : ℂ) * dlog01 s ^ 2 := by
  exact ⟨crossRatioSchwarzian_eq_zero hs,
    bipolarSchwarzian_eq_rational hs,
    deriv_bipolarSchwarzian hs,
    bipolarSchwarzian_eq_half_dlog01_sq hs⟩

end InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
