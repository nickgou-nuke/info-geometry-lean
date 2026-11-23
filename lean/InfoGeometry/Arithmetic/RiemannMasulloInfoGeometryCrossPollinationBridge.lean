/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Algebra.CyclotomicQuadraticBooleanSignBridge
import InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge
import InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
import InfoGeometry.Arithmetic.NumberFieldDedekindZetaEulerProduct
import InfoGeometry.Arithmetic.NumberFieldHeckeLFunction
import InfoGeometry.Arithmetic.RatRingOfIntegersDedekindTrace
import InfoGeometry.Analysis.MellinGaussianHolomorphicWeighted
import InfoGeometry.Analysis.GammaVerticalStripBounds
import InfoGeometry.Analysis.VerticalStripPhragmenLindelofHadamard
import InfoGeometry.Analysis.MeromorphicPolarLiouvilleCylinder
import InfoGeometry.Analysis.RectangleVerticalCauchyIntegral
import InfoGeometry.Analysis.GammaStripRatioSchwartzGaussian
import InfoGeometry.Analysis.BarrelledAnalyticContinuationFourierPhase
import InfoGeometry.Algebra.ZLatticeEuclideanTorusQuotient
import InfoGeometry.Arithmetic.MaurerCartanVonMangoldtBridge
import InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence
import InfoGeometry.Krein.KreinJordanSpectralObstructions
import InfoGeometry.Arithmetic.TateAdelicSignAndOddCharacterCosetBridge
import InfoGeometry.Arithmetic.TwoSidedHorizonMellinCutoffObstruction

/-!
# InfoGeometry.Arithmetic.RiemannMasulloInfoGeometryCrossPollinationBridge

Bidirectional cross-pollination bridge connecting ported `sorry`-free
`mccorvie/riemann-masullo` (Apache-2.0) theorems in `InfoGeometry` with
`info-geometry-lean`'s native prime-root, Bost–Connes, Möbius, cyclotomic,
Souriau `D_∞`, and lattice-torus modules:

1. `ratIdealAbsNormEquiv` and `ratIdeal_eq_span_absNorm_bridge`: identifies the
   ideal lattice `Ideal (𝓞 ℚ)` bijectively with `ℕ` via `Ideal.absNorm`,
   matching `Prime (p : 𝓞 ℚ)` with `Nat.Prime p`.
2. `ratHeckeDedekind_primonWeyl_crossPollination`: unifies trivial Hecke L-series
   over `ℚ`, Dedekind zeta Euler products over `HeightOneSpectrum (𝓞 ℚ)`,
   Möbius L-series inversion `ζ(s) * L(μ, s) = 1`, finite-cutoff Boolean-Weyl
   alternating sums, and Bost–Connes finite primon convergence to `riemannZeta β`.
3. `archimedeanGaussianMellin_souriauCriticalLine_crossPollination`: combines
   the Gaussian Mellin identity at `a = π` (yielding the Riemann archimedean
   factor `2⁻¹ * π^(-(s/2)) * Γ(s/2)`), the Souriau `D_∞` antiunitary fixed-line
   characterization `re w = 1 / 2`, and the critical-line reciprocal Gamma bound
   `‖(Complex.Gamma w)⁻¹‖ ≤ Real.exp (Real.pi * |w.im| / 2)`.
4. `cyclotomicBooleanSign_and_fisherSouriau_positivity_bridge` and
   `discreteLatticeTorusAndStripGamma_bridge`: links cyclotomic quadratic Boolean
   signs, Fisher–Souriau susceptibility positivity, discrete `ℤ`-lattice Euclidean
   torus quotients, and vertical-strip reciprocal Gamma / Hadamard interpolation.
5. `meromorphicPolar_rectangleCauchy_crossPollination`,
   `weightedGaussianMellin_and_gammaStripRatio_crossPollination`, and
   `barrelledAnalyticContinuation_and_complexPowerCylinder_bridge`: integrates
   meromorphic polar Cauchy residues, even/odd weighted Gaussian Mellin transforms,
   vertical-strip Gamma ratios, and prime complex-power cylinders.
6. `maurerCartan_weilKrein_apollonian_gamma_bridge` and
   `criticalLine_iff_weilKrein_and_apollonian`: welds R1 Maurer–Cartan `Λ` gauge
   readout (`-ζ'/ζ`) on `1 < s.re` with a pointwise finite-mode Weil-pairing
   model and the Apollonian unit-circle characterization. This finite-mode result
   is not positivity of the global Weil explicit formula or an RH/GRH criterion.
7. `errataCounterexamples_and_twoSidedRepair_capstone` and
   `twoSidedHorizonMellin_vs_oneSidedCutoff_capstone`: packages `ERRATA` F8/F9/F11/F13,
   Ch. 10 oblique/parabolic obstructions, and symmetric two-sided horizon cancellation.
-/

noncomputable section

open NumberField IsDedekindDomain Filter MeasureTheory Set ArithmeticFunction
open scoped LSeries.notation Asymptotics Topology BigOperators

namespace InfoGeometry.Arithmetic.RiemannMasulloInfoGeometryCrossPollinationBridge

open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Algebra.CyclotomicQuadraticBooleanSignBridge
open InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge
open InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
open InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
open InfoGeometry.Arithmetic.NumberFieldDedekindZetaEulerProduct
open InfoGeometry.Arithmetic.RatRingOfIntegersDedekindTrace
open InfoGeometry.Analysis.MellinGaussianHolomorphicWeighted
open InfoGeometry.Analysis.GammaVerticalStripBounds
open InfoGeometry.Analysis.VerticalStripPhragmenLindelofHadamard
open InfoGeometry.Analysis.MeromorphicPolarLiouvilleCylinder
open InfoGeometry.Analysis.RectangleVerticalCauchyIntegral
open InfoGeometry.Analysis.GammaStripRatioSchwartzGaussian
open InfoGeometry.Analysis.BarrelledAnalyticContinuationFourierPhase
open InfoGeometry.Algebra.ZLatticeEuclideanTorusQuotient
open InfoGeometry.Arithmetic.MaurerCartanVonMangoldtBridge
open InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence
open InfoGeometry.OperatorAlgebra.MaurerCartanTower
open InfoGeometry.Krein.KreinJordanSpectralObstructions
open InfoGeometry.Arithmetic.TateAdelicSignAndOddCharacterCosetBridge
open InfoGeometry.Arithmetic.TwoSidedHorizonMellinCutoffObstruction

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

/-- Explicit equivalence `Ideal (𝓞 ℚ) ≃ ℕ` sending every ideal of `𝓞 ℚ` to its
absolute norm and every natural number `n` to the principal ideal `Ideal.span {(n : 𝓞 ℚ)}`. -/
def ratIdealAbsNormEquiv : Ideal (𝓞 ℚ) ≃ ℕ where
  toFun := Ideal.absNorm
  invFun n := Ideal.span {(n : 𝓞 ℚ)}
  left_inv I := (RatRingOfIntegers.ideal_eq_span_absNorm I).symm
  right_inv n := RatRingOfIntegers.absNorm_span_natCast n

/-- Every ideal of `𝓞 ℚ` equals the principal ideal generated by its absolute norm. -/
theorem ratIdeal_eq_span_absNorm_bridge (I : Ideal (𝓞 ℚ)) :
    I = Ideal.span {(I.absNorm : 𝓞 ℚ)} :=
  RatRingOfIntegers.ideal_eq_span_absNorm I

/-- Rational primes coincide with primality of natural casts in `𝓞 ℚ`. -/
theorem ratPrimeNatCast_iff (p : ℕ) :
    Prime (p : 𝓞 ℚ) ↔ p.Prime :=
  RatRingOfIntegers.prime_natCast_iff

/-- Cross-pollination between number-field Hecke/Dedekind Euler products over `ℚ`,
the Bost–Connes partition series `partitionSeries s = riemannZeta s`, the classical
Möbius inverse identity `ζ(s) * L(μ, s) = 1`, finite Boolean-Weyl alternating
denominators, and finite primon partition convergence. -/
theorem ratHeckeDedekind_primonWeyl_crossPollination
    {s : ℂ} (hs : 1 < s.re) {β : ℝ} (hβ : 1 < β) (R : FormalPrimeRootLattice) :
    (1 : HeckeCharacter (𝓞 ℚ) ℚ).LSeries s = dedekindZeta ℚ s ∧
    HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) ↦ (1 - (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹)
      (dedekindZeta ℚ s) ∧
    partitionSeries s = riemannZeta s ∧
    riemannZeta s * L ↗(moebius : ArithmeticFunction ℂ) s = 1 ∧
    weylAlternatingSum R (boltzmannRootVariable β) = (finitePrimonPartition R β)⁻¹ ∧
    Filter.Tendsto (fun n : ℕ ↦ ((finitePrimonPartition (primesBelowLattice n) β : ℝ) : ℂ))
      Filter.atTop (𝓝 (riemannZeta (β : ℂ))) :=
  ⟨heckeLSeries_one_eq_dedekindZeta (F := ℚ) hs,
   dedekindZeta_hasProd ℚ hs,
   partitionSeries_eq_riemannZeta hs,
   actualRiemannZeta_mul_mobius_LSeries_eq_one hs,
   weylAlternatingSum_boltzmann_eq_inv_partition R β,
   finitePrimonPartition_primesBelow_tendsto_riemannZeta hβ⟩

/-- Cross-pollination between the Gaussian Mellin archimedean Gamma factor at `a = π`,
the Souriau `D_∞` antiunitary fixed-line symmetry `re w = 1 / 2`, and the
reflection bound `‖(Γ w)⁻¹‖ ≤ exp (π * |im w| / 2)` on `re w = 1 / 2`. -/
theorem archimedeanGaussianMellin_souriauCriticalLine_crossPollination
    {s w : ℂ} (hs : 0 < s.re) (hw : CriticalLine w) :
    mellin (fun t : ℝ ↦ (Real.exp (-Real.pi * t ^ 2) : ℂ)) s =
      (2 : ℂ)⁻¹ * ((Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)) ∧
    antiunitaryCriticalReflection w = w ∧
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.exp (Real.pi * |w.im| / 2) :=
  ⟨mellin_gaussian Real.pi_pos hs,
   ((fixed_antiunitaryCriticalReflection_iff_criticalLine w).mpr hw).symm,
   norm_inv_Gamma_half w hw⟩

/-- Cross-pollination pairing cyclotomic quadratic Boolean-sign characters on
`(ZMod (squarefreeCode R.primes))ˣ` with strict positivity of the Fisher–Souriau
susceptibility on any nonempty prime cutoff. -/
theorem cyclotomicBooleanSign_and_fisherSouriau_positivity_bridge
    (R : FormalPrimeRootLattice) (u : (ZMod (squarefreeCode R.primes))ˣ)
    {β : ℝ} (hβ : 0 < β) (hR : R.primes.Nonempty) :
    (∏ p : {p // p ∈ R.primes}, ((cyclotomicToBooleanSign R u p : ℤ) : ℝ)) =
      weylSign (nonResidueWeyl R u) ∧
    0 < fisherSouriauSusceptibility R β :=
  ⟨prod_cyclotomicToBooleanSign_eq_weylSign R u,
   fisherSouriauSusceptibility_pos R hβ hR⟩

/-- Cross-pollination bundling the Euclidean–torus quotient decomposition of a
discrete `ℤ`-lattice `Λ ⊂ E`, positive-strip reciprocal Gamma bounds, and Hadamard
vertical-strip exponent interpolation. -/
theorem discreteLatticeTorusAndStripGamma_bridge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Lsub : Submodule ℤ E) [DiscreteTopology Lsub]
    (a b : ℝ) (ha : 0 < a) :
    (∃ (m n : ℕ) (q : E →+ EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ))),
      IsOpenQuotientMap q ∧ q.ker = Lsub.toAddSubgroup) ∧
    (∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * (1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2)) :=
  ⟨exists_euclidean_torus_quotient Lsub,
   exists_norm_inv_Gamma_le_half_exp_on_strip a b ha⟩

/-- Vertical-strip Phragmén–Lindelöf/Hadamard interpolation bridge exposed cleanly
alongside the positive-strip reciprocal Gamma bound. -/
theorem verticalStripInterpolation_bridge {f : ℂ → ℂ} {l u K k₀ k₁ p q : ℝ}
    (hlu : l < u) (hK : 0 ≤ K) (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' Icc l u))
    (h : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc l u)] fun z ↦ |z.im| ^ K)
    (h₀ : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {l})] fun z ↦ |z.im| ^ k₀)
    (h₁ : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {u})] fun z ↦ |z.im| ^ k₁) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {p * l + q * u})]
      fun z ↦ |z.im| ^ (p * k₀ + q * k₁) :=
  isBigO_rpow_verticalStrip_interpolate hlu hK hk₀ hk₁ hp hq hpq hf h h₀ h₁

/-- Cross-pollination uniting meromorphic Laurent polar expansion around `ρ` with
rectangle Cauchy boundary residue (`2πi` at exponent `-1`, `0` at `k ≠ -1`). -/
theorem meromorphicPolar_rectangleCauchy_crossPollination
    {f : ℂ → ℂ} {z w ρ : ℂ} {k : ℤ}
    (hf : MeromorphicAt f ρ) (hρ : ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) (hk : k ≠ -1) :
    (∃ (n : ℕ) (H : ℂ → ℂ) (c : ℕ → ℂ), AnalyticAt ℂ H ρ ∧
      f =ᶠ[𝓝[≠] ρ] (fun s ↦ H s + ∑ j ∈ Finset.range n, c j * (s - ρ) ^ (-(j : ℤ) - 1))) ∧
    rectangleIntegral (fun s ↦ (s - ρ)⁻¹) z w = 2 * (Real.pi : ℂ) * Complex.I ∧
    rectangleIntegral (fun s ↦ (s - ρ) ^ k) z w = 0 :=
  ⟨meromorphicAt_exists_polar_expansion hf,
   rectangleIntegral_sub_inv hρ,
   rectangleIntegral_sub_zpow_of_ne hρ hk⟩

/-- Cross-pollination combining the weighted Gaussian Mellin transform of monomial
Hermite/theta kernels with vertical-strip Gamma ratio polynomial bounds. -/
theorem weightedGaussianMellin_and_gammaStripRatio_crossPollination
    {b : ℝ} (hb : 0 < b) (n : ℕ) {z : ℂ} (hz : 0 < z.re)
    {M : ℝ} (hM : 1 ≤ M) :
    mellin (fun t : ℝ ↦ (t : ℂ) ^ n * (Real.exp (-b * t ^ 2) : ℂ)) z =
      (1 / 2 : ℂ) * (b : ℂ) ^ (-((z + n) / 2)) * Complex.Gamma ((z + n) / 2) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x y t : ℝ, |x| ≤ M → |y| ≤ M → 1 ≤ |t| →
      ‖Complex.Gamma ⟨x, t⟩ / Complex.Gamma ⟨y, t⟩‖ ≤ C * |t| ^ (x - y)) :=
  ⟨mellin_weightedGaussian b hb n z hz,
   norm_Gamma_div_le_rpow_on_strip hM⟩

/-- Cross-pollination combining analytic continuation of continuous linear functionals
on a barrelled space with the prime-period vertical power cylinder `(ℂ ⧸ ℤ · (2πi / log q)) ≃ₜ ℂˣ`
modeling `s ↦ c * q ^ (-s)`. -/
theorem barrelledAnalyticContinuation_and_complexPowerCylinder_bridge
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (Φ : E → ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hΦ : ∀ g, AnalyticOnNhd ℂ (Φ g) U)
    {b₀ : ℂ} (hb₀ : b₀ ∈ U) (hbase : ∀ᶠ z in 𝓝 b₀, ∃ T : E →L[ℂ] ℂ, ∀ g, T g = Φ g z)
    {z : ℂ} (hz : z ∈ U) {q : ℝ} (hq : 1 < q) (c : ℂˣ) :
    (∃ T : E →L[ℂ] ℂ, ∀ g, T g = Φ g z) ∧
    (let P := AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * Complex.I / (Real.log q : ℂ))
     ∃ e : (ℂ ⧸ P) ≃ₜ ℂˣ, ∀ s : ℂ, (e (QuotientAddGroup.mk s) : ℂ) = c * (q : ℂ) ^ (-s)) :=
  ⟨exists_continuousLinearMap_of_analytic_continuation Φ hU hconn hΦ hb₀ hbase hz,
   exists_complexPowerCylinder q hq c⟩

local instance instDirichletIsScalarTower :
    IsScalarTower ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) :=
  ⟨fun r f g => by
    ext n
    simp [ArithmeticFunction.mul_apply, Finset.mul_sum]⟩

local instance instDirichletSMulCommClass :
    SMulCommClass ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) :=
  ⟨fun r f g => by
    ext n
    simp [ArithmeticFunction.mul_apply, Finset.mul_sum]⟩

/-- Joint R1 Maurer–Cartan and finite-mode Weil-pairing / Apollonian identity:
on `1 < s.re`, the R1 left Maurer–Cartan 1-form
`actionThetaL dirichletLogLane MaurerCartanVonMangoldtBridge.zetaUnit` equals `Λ`,
is CE-flat (`actionCurvature = 0`), and reads out `-deriv riemannZeta s / riemannZeta s`;
at any centered `w` on `CriticalLine (1 / 2 + w)`, the defined pointwise pairing
`weilPairMode w Φ` is nonnegative, the Apollonian map has norm square one, and
`norm_inv_Gamma_half` gives the reciprocal Gamma bound.
`weilPairMode` is the finite two-point model defined in
`WeilLiKreinGhostEquivalence`; this does not assert the global Weil explicit formula
or imply RH/GRH. -/
theorem maurerCartan_weilKrein_apollonian_gamma_bridge
    {s w : ℂ} (hs : 1 < s.re) (hw : CriticalLine (1 / 2 + w)) (Φ : ℂ → ℂ) :
    L ↗(actionThetaL dirichletLogLane MaurerCartanVonMangoldtBridge.zetaUnit ![(1 : ℝ)]) s =
      -deriv riemannZeta s / riemannZeta s ∧
    actionCurvature dirichletLogLane
      (actionThetaL dirichletLogLane MaurerCartanVonMangoldtBridge.zetaUnit) = 0 ∧
    0 ≤ weilPairMode w Φ ∧
    Complex.normSq (apollonianDiskMap w) = 1 ∧
    (CriticalLine (1 / 2 + w) ↔ ∀ Ψ : ℂ → ℂ, 0 ≤ weilPairMode w Ψ) ∧
    (CriticalLine (1 / 2 + w) ↔ Complex.normSq (apollonianDiskMap w) = 1) ∧
    ‖(Complex.Gamma (1 / 2 + w))⁻¹‖ ≤ Real.exp (Real.pi * |(1 / 2 + w).im| / 2) := by
  have hwre : w.re = 0 := (criticalLine_centered_iff_re_eq_zero w).mp hw
  refine ⟨(maurerCartan_zetaLogDerivative_mobius_synthesis hs 1).2.1,
    actionThetaL_zetaUnit_flat,
    weilPairMode_nonneg_of_re_eq_zero hwre Φ,
    (normSq_apollonianDiskMap_eq_one_iff_re_eq_zero w).mpr hwre,
    (criticalLine_centered_iff_re_eq_zero w).trans
      (re_eq_zero_iff_forall_weilPairMode_nonneg w),
    (criticalLine_centered_iff_re_eq_zero w).trans
      (normSq_apollonianDiskMap_eq_one_iff_re_eq_zero w).symm,
    norm_inv_Gamma_half (1 / 2 + w) hw⟩

/-- Finite-mode characterization accompanying
`maurerCartan_weilKrein_apollonian_gamma_bridge`: `CriticalLine (1 / 2 + w)` is
equivalent to universal nonnegativity of the defined pointwise pairing and to
unit-circle Apollonian balance (`Complex.normSq (apollonianDiskMap w) = 1`),
while any off-line `w` (`w.re ≠ 0`) admits a test function with pairing `-2`.
These statements concern the two-point model in `WeilLiKreinGhostEquivalence`, not
the global Weil explicit formula, and do not constitute an RH/GRH criterion. -/
theorem criticalLine_iff_weilKrein_and_apollonian (w : ℂ) :
    (CriticalLine (1 / 2 + w) ↔ ∀ Φ : ℂ → ℂ, 0 ≤ weilPairMode w Φ) ∧
    (CriticalLine (1 / 2 + w) ↔ Complex.normSq (apollonianDiskMap w) = 1) ∧
    (w.re ≠ 0 → ∃ Φ : ℂ → ℂ, weilPairMode w Φ = -2 ∧ weilPairMode w Φ < 0) :=
  ⟨(criticalLine_centered_iff_re_eq_zero w).trans
      (re_eq_zero_iff_forall_weilPairMode_nonneg w),
   (criticalLine_centered_iff_re_eq_zero w).trans
      (normSq_apollonianDiskMap_eq_one_iff_re_eq_zero w).symm,
   exists_negative_weilPairMode_of_re_ne_zero⟩

/-- Closed `T16` noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` from `ERRATA F9`. -/
theorem errata_F9_realMatrix_noncomm_witness :
    peirceCutP0 * outwardNilpotentX ≠ outwardNilpotentX * peirceCutP0 :=
  errata_F9_trace_norm_asymmetry.2.2.2.2.2.2

/-- **Step 1 Unified `ERRATA` & Two-Sided Repair Capstone**:
packages the exact finite-dimensional `F8` Walsh-Krein basis cancellation (`2 → 0`),
`F9` Peirce/nilpotent trace-norm asymmetry (`P₀ X = 0` vs `X P₀ = X`), `F11`/`F13` Tate
opposite-sign cancellation and odd-character mod-3 shifted-coset non-vanishing, and
Chapter 10 unbounded oblique Markushevich duals / parabolic Jordan nilpotent defect. -/
theorem errataCounterexamples_and_twoSidedRepair_capstone (M : ℝ) :
    (|kreinPolarityMat 0 0| + |kreinPolarityMat 1 1| = 2) ∧
    (|(walshMat * kreinPolarityMat * walshMat) 0 0| +
     |(walshMat * kreinPolarityMat * walshMat) 1 1| = 0) ∧
    (Matrix.trace (peirceCutP0 * outwardNilpotentX) = 0 ∧
     Matrix.trace (outwardNilpotentX * peirceCutP0) = 0 ∧
     peirceCutP0 * outwardNilpotentX = 0 ∧
     outwardNilpotentX * peirceCutP0 = outwardNilpotentX) ∧
    (addCharPos (1 / 3 : ℝ) * addCharPos (1 / 3 : ℝ) ≠ 1 ∧
     addCharNeg (1 / 3 : ℝ) * addCharPos (1 / 3 : ℝ) = 1 ∧
     quadCharMod3 (-1) = -1 ∧
     (∑ u : (ZMod 3)ˣ, quadCharMod3 u * shiftedCosetIndicator 1 u) = 1) ∧
    (∃ θ : ℝ, Real.sin θ ≠ 0 ∧ M < frobNormSq (obliqueProj θ)) ∧
    (jordanNilpotent * jordanNilpotent = 0 ∧ jordanNilpotent ≠ 0) := by
  have hF8 := errata_F8_walsh_basis_dependence
  have hF9 := errata_F9_trace_norm_asymmetry
  have hOdd := odd_quad_char_mod3_witness
  have hJ := parabolic_jordan_coalescence_witness 0 1 zero_ne_one
  exact ⟨hF8.1, hF8.2,
    ⟨hF9.2.2.1, hF9.2.2.2.1, hF9.2.2.2.2.1, hF9.2.2.2.2.2.1⟩,
    ⟨same_sign_character_fails_at_one_third, tate_opposite_sign_at_one_third,
      hOdd.1, hOdd.2.2⟩,
    obliqueProj_frobNormSq_unbounded M,
    ⟨hJ.2.2.2.2.1, hJ.2.2.2.2.2⟩⟩

/-- **Step 2 Symmetric Two-Sided Horizon Mellin vs. One-Sided Cutoff Capstone
(`ERRATA R2` / §1.4.3–1.4.4)**: contrasts non-integrability and unboundedness of the
one-sided cutoff kernel `(t - 1)⁻¹` on `[1 + ε, 2]` (`c > 0`) against symmetric
two-sided log-horizon cancellation on `[-R, -r] ∪ [r, R]`, multiplicative UV↔IR
antisymmetry `t ↦ t⁻¹`, and the §1.4.4 negative log-derivative sign at `s = 5 / 2`. -/
theorem twoSidedHorizonMellin_vs_oneSidedCutoff_capstone
    {c r R t : ℝ} (hc : 0 < c) (hr : 0 < r) (hR : 0 < R) (ht : 0 < t) (M : ℝ) :
    (¬ IntervalIntegrable (fun u : ℝ ↦ (u - 1)⁻¹) volume 1 2) ∧
    (∃ ε ∈ Set.Ioo (0 : ℝ) 1, M < ∫ u in (1 + ε)..2, c * (u - 1)⁻¹) ∧
    ((∫ τ in (-R)..(-r), c * τ⁻¹) + (∫ τ in r..R, c * τ⁻¹) = 0) ∧
    (archimedeanHorizonKernel t⁻¹ = -archimedeanHorizonKernel t) ∧
    (L ↗(actionThetaL dirichletLogLane MaurerCartanVonMangoldtBridge.zetaUnit ![(1 : ℝ)])
      (5 / 2 : ℂ) = -deriv riemannZeta (5 / 2 : ℂ) / riemannZeta (5 / 2 : ℂ)) :=
  ⟨not_intervalIntegrable_oneSidedHorizonKernel,
    oneSidedHorizonCutoff_unbounded hc M,
    twoSidedLogHorizonPrincipalValue_eq_zero c hr hR,
    archimedeanHorizonKernel_inv ht,
    sec144_vonMangoldt_LSeries_at_five_halves⟩


/-- The centred critical line is characterised by nonnegativity of every Weil
pairing together with the Apollonian disk map lying on the unit circle. -/
theorem weilKrein_apollonian_criticalLine_characterization (w : ℂ) :
    CriticalLine (1 / 2 + w) ↔
      (∀ Φ : ℂ → ℂ, 0 ≤ weilPairMode w Φ) ∧
        Complex.normSq (apollonianDiskMap w) = 1 := by
  rw [criticalLine_centered_iff_re_eq_zero]
  constructor
  · intro hw
    exact ⟨(re_eq_zero_iff_forall_weilPairMode_nonneg w).mp hw,
      (normSq_apollonianDiskMap_eq_one_iff_re_eq_zero w).mpr hw⟩
  · intro h
    exact (re_eq_zero_iff_forall_weilPairMode_nonneg w).mpr h.1

/-- Off the centred critical line there is a negative Weil pairing and the
Apollonian disk map is off the unit circle. -/
theorem offCriticalLine_weilKrein_ghost {w : ℂ} (hw : w.re ≠ 0) :
    (∃ Φ : ℂ → ℂ, weilPairMode w Φ < 0) ∧
      Complex.normSq (apollonianDiskMap w) ≠ 1 := by
  obtain ⟨Φ, _, hneg⟩ := exists_negative_weilPairMode_of_re_ne_zero hw
  refine ⟨⟨Φ, hneg⟩, ?_⟩
  intro h
  exact hw ((normSq_apollonianDiskMap_eq_one_iff_re_eq_zero w).mp h)


end InfoGeometry.Arithmetic.RiemannMasulloInfoGeometryCrossPollinationBridge
