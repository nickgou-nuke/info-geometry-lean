import Mathlib.Tactic
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Arithmetic.ZetaChiralConeProjection

/-!
# InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

Finite theorem-safe readouts of standard zeta definitions in the centered
symmetry chart `s = 1/2 + u + iv`.

The coordinate owner is `ZetaCoordinateSymmetry`.  This module does not prove
analytic continuation, the Euler product theorem, Ramanujan formulae, or RH.

#### BUCKET 1: CLOSED FINITE THEOREMS
Finite coordinate, reflection, projector-free readout, and `ξ/Ξ` parity
identities in the centered chart.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
Equivalent-definition consequences are proved only from explicitly supplied
premises such as `eta_extends_dirichlet` and `dirichlet_eq_euler`.

#### BUCKET 3: OPEN CLOSURE DEBT
Analytic continuation, Euler product convergence, Mellin integral identities,
theta modularity, Hadamard product convergence, and Ramanujan's odd-zeta
transformation.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

open Complex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart
open InfoGeometry.Arithmetic.ZetaChiralConeProjection

/-- Local abbreviation for the owner centered zeta chart. -/
abbrev CenteredChart :=
  InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

/-- The complex spectral parameter represented by centered coordinates. -/
def centeredParameter (x : CenteredChart) : ℂ :=
  (fromCentered x).toComplex

@[simp] theorem centeredParameter_re (x : CenteredChart) :
    (centeredParameter x).re = x.u + (1 / 2 : ℝ) := by
  rfl

@[simp] theorem centeredParameter_im (x : CenteredChart) :
    (centeredParameter x).im = x.v := by
  rfl

/-- In the centered chart the standard parameter is `1/2 + u + iv`. -/
theorem centeredParameter_eq_half_plus_u_plus_iv (x : CenteredChart) :
    centeredParameter x =
      ((x.u + (1 / 2 : ℝ) : ℝ) : ℂ) + (x.v : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [centeredParameter, fromCentered, ZetaAffineChart.toComplex]
  · simp [centeredParameter, fromCentered, ZetaAffineChart.toComplex]

/-- The critical line is the centered zero-locus `u = 0`. -/
def centeredCriticalLine (x : CenteredChart) : Prop :=
  x.u = 0

/-- The critical mirror fixes exactly the centered critical line. -/
theorem criticalMirror_fixed_iff_centeredCriticalLine (x : CenteredChart) :
    criticalMirror x = x ↔ centeredCriticalLine x := by
  constructor
  · intro h
    have hu := congrArg (fun y : CenteredChart => y.u) h
    simp [criticalMirror, centeredCriticalLine] at hu ⊢
    linarith
  · intro h
    ext <;> simp [criticalMirror, centeredCriticalLine] at h ⊢
    linarith

/-- Critical-line weight `exp(-L/2)` for a base with logarithm `L`. -/
def criticalLineWeight (L : ℝ) : ℂ :=
  (Real.exp (-(1 / 2 : ℝ) * L) : ℂ)

lemma criticalLineWeight_ne_zero (L : ℝ) :
    criticalLineWeight L ≠ 0 := by
  unfold criticalLineWeight
  exact_mod_cast (Real.exp_ne_zero _)

/-- Scale-normal envelope `exp(-uL)`. -/
def scaleEnvelope (L u : ℝ) : ℂ :=
  (Real.exp (-u * L) : ℂ)

lemma scaleEnvelope_ne_zero (L u : ℝ) :
    scaleEnvelope L u ≠ 0 := by
  unfold scaleEnvelope
  exact_mod_cast (Real.exp_ne_zero _)

/-- Tangential phase wave `exp(-ivL)`. -/
def phaseWave (L v : ℝ) : ℂ :=
  Complex.exp (-(v * L : ℝ) * Complex.I)

lemma phaseWave_ne_zero (L v : ℝ) :
    phaseWave L v ≠ 0 := by
  unfold phaseWave
  exact Complex.exp_ne_zero _

/--
Factored Dirichlet mode for `L = log n`:
`exp(-L/2) * exp(-uL) * exp(-ivL)`.
-/
def centeredDirichletMode (L : ℝ) (x : CenteredChart) : ℂ :=
  criticalLineWeight L * scaleEnvelope L x.u * phaseWave L x.v

lemma centeredDirichletMode_ne_zero (L : ℝ) (x : CenteredChart) :
    centeredDirichletMode L x ≠ 0 := by
  unfold centeredDirichletMode
  exact mul_ne_zero
    (mul_ne_zero (criticalLineWeight_ne_zero L) (scaleEnvelope_ne_zero L x.u))
    (phaseWave_ne_zero L x.v)

@[simp] theorem scaleEnvelope_zero (L : ℝ) :
    scaleEnvelope L 0 = 1 := by
  simp [scaleEnvelope]

@[simp] theorem phaseWave_zero (L : ℝ) :
    phaseWave L 0 = 1 := by
  simp [phaseWave]

/-- On the critical line the scale-normal envelope is exactly `1`. -/
theorem centeredDirichletMode_of_centeredCriticalLine
    {L : ℝ} {x : CenteredChart} (hx : centeredCriticalLine x) :
    centeredDirichletMode L x =
      criticalLineWeight L * phaseWave L x.v := by
  calc
    centeredDirichletMode L x
        = criticalLineWeight L * scaleEnvelope L 0 * phaseWave L x.v := by
            rw [centeredDirichletMode, hx]
    _ = criticalLineWeight L * phaseWave L x.v := by
            simp [scaleEnvelope]

/-- Conjugation reverses only the phase coordinate in the factored mode. -/
theorem centeredDirichletMode_conjugation (L : ℝ) (x : CenteredChart) :
    centeredDirichletMode L (conjugation x) =
      criticalLineWeight L * scaleEnvelope L x.u * phaseWave L (-x.v) := by
  rfl

/-- Functional duality reverses both scale-normal and phase coordinates. -/
theorem centeredDirichletMode_functionalDual (L : ℝ) (x : CenteredChart) :
    centeredDirichletMode L (functionalDual x) =
      criticalLineWeight L * scaleEnvelope L (-x.u) * phaseWave L (-x.v) := by
  rfl

/-- The critical mirror reverses only the scale-normal envelope. -/
theorem centeredDirichletMode_criticalMirror (L : ℝ) (x : CenteredChart) :
    centeredDirichletMode L (criticalMirror x) =
      criticalLineWeight L * scaleEnvelope L (-x.u) * phaseWave L x.v := by
  rfl

/-- Finite Dirichlet readout in centered coordinates. -/
def finiteDirichletReadout {ι : Type*}
    (S : Finset ι) (logWeight : ι → ℝ) (x : CenteredChart) : ℂ :=
  S.sum fun i => centeredDirichletMode (logWeight i) x

/-- Finite Euler factor in centered coordinates. -/
def finiteEulerFactor (L : ℝ) (x : CenteredChart) : ℂ :=
  (1 - centeredDirichletMode L x)⁻¹

lemma finiteEulerFactor_ne_zero {L : ℝ} {x : CenteredChart}
    (h : 1 - centeredDirichletMode L x ≠ 0) :
    finiteEulerFactor L x ≠ 0 := by
  unfold finiteEulerFactor
  exact inv_ne_zero h

/-- Finite Euler-product readout in centered coordinates. -/
def finiteEulerProduct {ι : Type*}
    (S : Finset ι) (logWeight : ι → ℝ) (x : CenteredChart) : ℂ :=
  S.prod fun i => finiteEulerFactor (logWeight i) x

@[simp] theorem finiteDirichletReadout_empty {ι : Type*}
    (logWeight : ι → ℝ) (x : CenteredChart) :
    finiteDirichletReadout (∅ : Finset ι) logWeight x = 0 := by
  simp [finiteDirichletReadout]

@[simp] theorem finiteEulerProduct_empty {ι : Type*}
    (logWeight : ι → ℝ) (x : CenteredChart) :
    finiteEulerProduct (∅ : Finset ι) logWeight x = 1 := by
  simp [finiteEulerProduct]

theorem finiteDirichletReadout_insert {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {i : ι} (hi : i ∉ S)
    (logWeight : ι → ℝ) (x : CenteredChart) :
    finiteDirichletReadout (insert i S) logWeight x =
      centeredDirichletMode (logWeight i) x +
        finiteDirichletReadout S logWeight x := by
  simp [finiteDirichletReadout, Finset.sum_insert, hi]

theorem finiteEulerProduct_insert {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {i : ι} (hi : i ∉ S)
    (logWeight : ι → ℝ) (x : CenteredChart) :
    finiteEulerProduct (insert i S) logWeight x =
      finiteEulerFactor (logWeight i) x *
        finiteEulerProduct S logWeight x := by
  simp [finiteEulerProduct, Finset.prod_insert, hi]

/-- Standard representation kinds for zeta-related readouts. -/
inductive ZetaRepresentationKind where
  | dirichletSeries
  | eulerProduct
  | etaContinuation
  | mellinThetaCompletion
  | completedXi
  | hadamardXiProduct
  | ramanujanLambertTransform
  deriving DecidableEq, Repr

/-! ## Completed xi and equivalent-definition predicates -/

/-- The Riemann reflection in standard coordinates. -/
def riemannReflection (s : ℂ) : ℂ :=
  1 - s

/-- Offset coordinate `s = 1/2 + z`, used for the classical `Ξ(z)` notation. -/
def offsetParameter (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + z

/-- Entire xi readout from a supplied completed amplitude. -/
def xiFromLambda (Lambda : ℂ → ℂ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * Lambda s

/-- Symmetry-adapted Xi coordinate `Ξ(z) = ξ(1/2+z)`. -/
def XiFromXi (xi : ℂ → ℂ) (z : ℂ) : ℂ :=
  xi (offsetParameter z)

theorem riemannReflection_offsetParameter (z : ℂ) :
    riemannReflection (offsetParameter z) = offsetParameter (-z) := by
  simp [riemannReflection, offsetParameter]
  ring

theorem xiPrefactor_reflection (s : ℂ) :
    (1 / 2 : ℂ) * riemannReflection s * (riemannReflection s - 1) =
      (1 / 2 : ℂ) * s * (s - 1) := by
  simp [riemannReflection]
  ring

theorem xiFromLambda_reflection_eq
    (Lambda : ℂ → ℂ)
    (hLambda : ∀ s, Lambda s = Lambda (riemannReflection s))
    (s : ℂ) :
    xiFromLambda Lambda s = xiFromLambda Lambda (riemannReflection s) := by
  unfold xiFromLambda
  rw [← hLambda s, xiPrefactor_reflection s]

theorem XiFromXi_even_of_reflection
    (xi : ℂ → ℂ)
    (hxi : ∀ s, xi s = xi (riemannReflection s))
    (z : ℂ) :
    XiFromXi xi z = XiFromXi xi (-z) := by
  unfold XiFromXi
  rw [hxi (offsetParameter z), riemannReflection_offsetParameter]

/-! ## Completed xi as a centered `J`-fixed field -/

/-- Center an analytic one-variable readout on the zeta chart. -/
def centeredAnalyticField (F : ℂ → ℂ) : CenteredField :=
  fun x => F (centeredParameter x)

/-- In centered coordinates, functional duality realizes `s ↦ 1 - s`. -/
theorem centeredParameter_functionalDual (x : CenteredChart) :
    centeredParameter (functionalDual x) =
      riemannReflection (centeredParameter x) := by
  apply Complex.ext
  · simp [centeredParameter, fromCentered, riemannReflection, ZetaAffineChart.toComplex,
      functionalDual]
    ring
  · simp [centeredParameter, fromCentered, riemannReflection, ZetaAffineChart.toComplex,
      functionalDual]

/-- In centered coordinates, conjugation realizes Schwarz reflection. -/
theorem centeredParameter_conjugation (x : CenteredChart) :
    centeredParameter (conjugation x) = star (centeredParameter x) := by
  apply Complex.ext <;>
    simp [centeredParameter, fromCentered, ZetaAffineChart.toComplex, conjugation]

/--
Schwarz reflection plus the Riemann reflection make an analytic completed-xi
readout a centered chiral-cone symmetry packet.
-/
def centeredXiSymmetryPacketOfReflection
    (xi : ℂ → ℂ)
    (hSchwarz :
      ∀ x : CenteredChart,
        star (centeredAnalyticField xi x) =
          centeredAnalyticField xi (conjugation x))
    (hReflection : ∀ s, xi s = xi (riemannReflection s)) :
    CenteredXiSymmetryPacket where
  xi := centeredAnalyticField xi
  schwarz_reflection := hSchwarz
  functional_equation := by
    intro x
    unfold centeredAnalyticField
    rw [centeredParameter_functionalDual x]
    exact (hReflection (centeredParameter x)).symm

/--
The completed-xi odd projector vanishes once Schwarz reflection and the Riemann
functional reflection are supplied explicitly.
-/
theorem centeredXi_JOddProjector_eq_zero_of_schwarz_reflection
    (xi : ℂ → ℂ)
    (hSchwarz :
      ∀ x : CenteredChart,
        star (centeredAnalyticField xi x) =
          centeredAnalyticField xi (conjugation x))
    (hReflection : ∀ s, xi s = xi (riemannReflection s)) :
    JOddProjector (centeredAnalyticField xi) = 0 :=
  (centeredXiSymmetryPacketOfReflection xi hSchwarz hReflection).xi_JOddProjector_eq_zero

/-- The same hypotheses put completed xi into the symbolic `J`-fixed cone. -/
theorem centeredXi_mem_JFixedCone_of_schwarz_reflection
    (xi : ℂ → ℂ)
    (hSchwarz :
      ∀ x : CenteredChart,
        star (centeredAnalyticField xi x) =
          centeredAnalyticField xi (conjugation x))
    (hReflection : ∀ s, xi s = xi (riemannReflection s)) :
    centeredAnalyticField xi ∈ JFixedCone :=
  (centeredXiSymmetryPacketOfReflection xi hSchwarz hReflection).xi_mem_JFixedCone

/-- Dirichlet-series definition of zeta at `s`; convergence is part of `HasSum`. -/
def DirichletSeriesDefinition (zeta : ℂ → ℂ) (s : ℂ) : Prop :=
  HasSum (fun n : ℕ => ((n + 1 : ℂ) ^ (-s))) (zeta s)

/-- Euler-product definition as a supplied product readout. -/
def EulerProductDefinition
    (zeta : ℂ → ℂ) (eulerProduct : ℂ → ℂ) (s : ℂ) : Prop :=
  zeta s = eulerProduct s

/-- Alternating eta quotient definition `ζ(s)=η(s)/(1-2^(1-s))`. -/
def EtaQuotientDefinition (zeta eta : ℂ → ℂ) (s : ℂ) : Prop :=
  zeta s = eta s / (1 - (2 : ℂ) ^ (1 - s))

/-- Mellin Bose-kernel definition `Γ(s)ζ(s)=∫ x^(s-1)/(e^x-1) dx`. -/
def MellinBoseKernelDefinition
    (gamma zeta mellinBoseKernel : ℂ → ℂ) (s : ℂ) : Prop :=
  gamma s * zeta s = mellinBoseKernel s

/-- Hadamard-product definition of xi as a supplied product equality. -/
def HadamardXiDefinition (xi hadamardProduct : ℂ → ℂ) (s : ℂ) : Prop :=
  xi s = hadamardProduct s

/-- On a common convergence domain, eta and Euler readouts agree from explicit premises. -/
theorem eta_eq_euler_on_convergence
    (convergenceDomain : CenteredChart → Prop)
    (dirichletSeries eulerProduct etaContinuation : CenteredChart → ℂ)
    (dirichlet_eq_euler :
      ∀ x, convergenceDomain x → dirichletSeries x = eulerProduct x)
    (eta_extends_dirichlet :
      ∀ x, convergenceDomain x → etaContinuation x = dirichletSeries x)
    (x : CenteredChart) (hx : convergenceDomain x) :
    etaContinuation x = eulerProduct x := by
  calc
    etaContinuation x = dirichletSeries x := eta_extends_dirichlet x hx
    _ = eulerProduct x := dirichlet_eq_euler x hx

/-- Ramanujan-style odd-zeta transformation target, with supplied analytic sides. -/
def RamanujanLambertTransform
    (oddZetaReadout lambertSeriesSide bernoulliCorrectionSide : ℕ → ℂ) : Prop :=
  ∀ m, oddZetaReadout m = lambertSeriesSide m + bernoulliCorrectionSide m

/-! ## The finite `n = 1` Bernoulli defect / Apéry layer -/

/-- Finite Bernoulli polynomial side in Ramanujan's odd-zeta transformation. -/
def ramanujanBernoulliSide (B : ℕ → ℝ) (n : ℕ) (alpha beta : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 * n) *
    ((Finset.range (n + 2)).sum fun k =>
      ((-1 : ℝ) ^ (k + 1)) *
        B (2 * k) / (Nat.factorial (2 * k) : ℝ) *
        B (2 * n + 2 - 2 * k) / (Nat.factorial (2 * n + 2 - 2 * k) : ℝ) *
        alpha ^ (n + 1 - k) * beta ^ k)

/-- The only Bernoulli values needed for the `ζ(3)` / Apéry layer. -/
def aperyBernoulliReadout (m : ℕ) : ℝ :=
  if m = 0 then 1
  else if m = 2 then (1 / 6 : ℝ)
  else if m = 4 then (-1 / 30 : ℝ)
  else 0

/--
The finite Bernoulli defect for the `n = 1` Ramanujan layer reduces to a
closed quadratic polynomial.

This is the theorem-safe part of the `ζ(3)` specialization; it does not prove
the infinite Lambert-series identity.
-/
theorem ramanujanBernoulliSide_apery_n1_explicit (alpha beta : ℝ) :
    ramanujanBernoulliSide aperyBernoulliReadout 1 alpha beta =
      alpha ^ 2 / 180 + alpha * beta / 36 + beta ^ 2 / 180 := by
  norm_num [ramanujanBernoulliSide, aperyBernoulliReadout, Finset.sum_range_succ]
  ring_nf

/--
Under the modular mirror condition `αβ = π²`, the same finite `ζ(3)` defect is
the sum of the two endpoint quadratic fluxes plus the central `π²/36` term.
-/
theorem ramanujanBernoulliSide_apery_n1_of_alpha_beta_eq_pi_sq
    {alpha beta : ℝ} (hαβ : alpha * beta = Real.pi ^ 2) :
    ramanujanBernoulliSide aperyBernoulliReadout 1 alpha beta =
      alpha ^ 2 / 180 + Real.pi ^ 2 / 36 + beta ^ 2 / 180 := by
  rw [ramanujanBernoulliSide_apery_n1_explicit, hαβ]

/-- The `ζ(3)` finite defect in the S-dual parameterization `α = πτ`, `β = π/τ`. -/
def aperyBernoulliDefectTau (tau : ℝ) : ℝ :=
  ramanujanBernoulliSide aperyBernoulliReadout 1 (Real.pi * tau) (Real.pi / tau)

/-- Explicit `τ`-coordinate form of the finite `ζ(3)` Bernoulli defect. -/
theorem aperyBernoulliDefectTau_explicit {tau : ℝ} (hτ : tau ≠ 0) :
    aperyBernoulliDefectTau tau =
      Real.pi ^ 2 * (tau ^ 2 / 180 + 1 / 36 + (1 / tau ^ 2) / 180) := by
  rw [aperyBernoulliDefectTau, ramanujanBernoulliSide_apery_n1_explicit]
  field_simp [hτ]

/-- The finite `ζ(3)` Bernoulli defect is invariant under `τ ↦ τ⁻¹`. -/
theorem aperyBernoulliDefectTau_inv {tau : ℝ} (hτ : tau ≠ 0) :
    aperyBernoulliDefectTau tau = aperyBernoulliDefectTau tau⁻¹ := by
  rw [aperyBernoulliDefectTau_explicit hτ,
    aperyBernoulliDefectTau_explicit (inv_ne_zero hτ)]
  field_simp [hτ]
  ring

/-! ## The finite `n = 2` Bernoulli defect / `ζ(5)` layer -/

/-- Bernoulli values needed for the `ζ(5)` layer. -/
def zetaFiveBernoulliReadout (m : ℕ) : ℝ :=
  if m = 0 then 1
  else if m = 2 then (1 / 6 : ℝ)
  else if m = 4 then (-1 / 30 : ℝ)
  else if m = 6 then (1 / 42 : ℝ)
  else 0

/--
The finite Bernoulli defect for the `n = 2` Ramanujan layer reduces to a
closed cubic polynomial.
-/
theorem ramanujanBernoulliSide_zeta5_n2_explicit (alpha beta : ℝ) :
    ramanujanBernoulliSide zetaFiveBernoulliReadout 2 alpha beta =
      -((alpha - beta) * (2 * alpha ^ 2 + 9 * alpha * beta + 2 * beta ^ 2)) / 3780 := by
  norm_num [ramanujanBernoulliSide, zetaFiveBernoulliReadout, Finset.sum_range_succ]
  ring_nf

/-- The `ζ(5)` finite defect in the S-dual parameterization `α = πτ`, `β = π/τ`. -/
def zetaFiveBernoulliDefectTau (tau : ℝ) : ℝ :=
  ramanujanBernoulliSide zetaFiveBernoulliReadout 2 (Real.pi * tau) (Real.pi / tau)

/-- Explicit `τ`-coordinate form of the finite `ζ(5)` Bernoulli defect. -/
theorem zetaFiveBernoulliDefectTau_explicit {tau : ℝ} (hτ : tau ≠ 0) :
    zetaFiveBernoulliDefectTau tau =
      -Real.pi ^ 3 *
        ((tau - 1) * (tau + 1) * (2 * tau ^ 4 + 9 * tau ^ 2 + 2) /
          (3780 * tau ^ 3)) := by
  rw [zetaFiveBernoulliDefectTau, ramanujanBernoulliSide_zeta5_n2_explicit]
  field_simp [hτ]
  ring

/-- The finite `ζ(5)` Bernoulli defect is anti-invariant under `τ ↦ τ⁻¹`. -/
theorem zetaFiveBernoulliDefectTau_inv {tau : ℝ} (hτ : tau ≠ 0) :
    zetaFiveBernoulliDefectTau tau = -zetaFiveBernoulliDefectTau tau⁻¹ := by
  rw [zetaFiveBernoulliDefectTau_explicit hτ,
    zetaFiveBernoulliDefectTau_explicit (inv_ne_zero hτ)]
  field_simp [hτ]
  ring

/-! ## The finite `n = 3` Bernoulli defect / `ζ(7)` layer -/

/-- Bernoulli values needed for the `ζ(7)` layer. -/
def zetaSevenBernoulliReadout (m : ℕ) : ℝ :=
  if m = 0 then 1
  else if m = 2 then (1 / 6 : ℝ)
  else if m = 4 then (-1 / 30 : ℝ)
  else if m = 6 then (1 / 42 : ℝ)
  else if m = 8 then (-1 / 30 : ℝ)
  else 0

/--
The finite Bernoulli defect for the `n = 3` Ramanujan layer reduces to a
closed quartic polynomial.
-/
theorem ramanujanBernoulliSide_zeta7_n3_explicit (alpha beta : ℝ) :
    ramanujanBernoulliSide zetaSevenBernoulliReadout 3 alpha beta =
      ((alpha ^ 2 - alpha * beta + beta ^ 2) *
        (3 * alpha ^ 2 + 13 * alpha * beta + 3 * beta ^ 2)) / 56700 := by
  norm_num [ramanujanBernoulliSide, zetaSevenBernoulliReadout, Finset.sum_range_succ]
  ring_nf

/-- The `ζ(7)` finite defect in the S-dual parameterization `α = πτ`, `β = π/τ`. -/
def zetaSevenBernoulliDefectTau (tau : ℝ) : ℝ :=
  ramanujanBernoulliSide zetaSevenBernoulliReadout 3 (Real.pi * tau) (Real.pi / tau)

/-- Explicit `τ`-coordinate form of the finite `ζ(7)` Bernoulli defect. -/
theorem zetaSevenBernoulliDefectTau_explicit {tau : ℝ} (hτ : tau ≠ 0) :
    zetaSevenBernoulliDefectTau tau =
      Real.pi ^ 4 *
        ((tau ^ 4 - tau ^ 2 + 1) * (3 * tau ^ 4 + 13 * tau ^ 2 + 3) /
          (56700 * tau ^ 4)) := by
  rw [zetaSevenBernoulliDefectTau, ramanujanBernoulliSide_zeta7_n3_explicit]
  field_simp [hτ]

/-- The finite `ζ(7)` Bernoulli defect is invariant under `τ ↦ τ⁻¹`. -/
theorem zetaSevenBernoulliDefectTau_inv {tau : ℝ} (hτ : tau ≠ 0) :
    zetaSevenBernoulliDefectTau tau = zetaSevenBernoulliDefectTau tau⁻¹ := by
  rw [zetaSevenBernoulliDefectTau_explicit hτ,
    zetaSevenBernoulliDefectTau_explicit (inv_ne_zero hτ)]
  field_simp [hτ]
  ring

/-! ## The finite `n = 4` Bernoulli defect / `ζ(9)` layer -/

/-- Bernoulli values needed for the `ζ(9)` layer. -/
def zetaNineBernoulliReadout (m : ℕ) : ℝ :=
  if m = 0 then 1
  else if m = 2 then (1 / 6 : ℝ)
  else if m = 4 then (-1 / 30 : ℝ)
  else if m = 6 then (1 / 42 : ℝ)
  else if m = 8 then (-1 / 30 : ℝ)
  else if m = 10 then (5 / 66 : ℝ)
  else 0

/--
The finite Bernoulli defect for the `n = 4` Ramanujan layer reduces to a
closed quintic polynomial.
-/
theorem ramanujanBernoulliSide_zeta9_n4_explicit (alpha beta : ℝ) :
    ramanujanBernoulliSide zetaNineBernoulliReadout 4 alpha beta =
      -((alpha - beta) *
        (10 * alpha ^ 4 + 43 * alpha ^ 3 * beta + 21 * alpha ^ 2 * beta ^ 2 +
          43 * alpha * beta ^ 3 + 10 * beta ^ 4)) / 1871100 := by
  norm_num [ramanujanBernoulliSide, zetaNineBernoulliReadout, Finset.sum_range_succ]
  ring_nf

/-- The `ζ(9)` finite defect in the S-dual parameterization `α = πτ`, `β = π/τ`. -/
def zetaNineBernoulliDefectTau (tau : ℝ) : ℝ :=
  ramanujanBernoulliSide zetaNineBernoulliReadout 4 (Real.pi * tau) (Real.pi / tau)

/-- Explicit `τ`-coordinate form of the finite `ζ(9)` Bernoulli defect. -/
theorem zetaNineBernoulliDefectTau_explicit {tau : ℝ} (hτ : tau ≠ 0) :
    zetaNineBernoulliDefectTau tau =
      -Real.pi ^ 5 *
        ((tau - 1) * (tau + 1) *
          (10 * tau ^ 8 + 43 * tau ^ 6 + 21 * tau ^ 4 + 43 * tau ^ 2 + 10) /
          (1871100 * tau ^ 5)) := by
  rw [zetaNineBernoulliDefectTau, ramanujanBernoulliSide_zeta9_n4_explicit]
  field_simp [hτ]
  ring

/-- The finite `ζ(9)` Bernoulli defect is anti-invariant under `τ ↦ τ⁻¹`. -/
theorem zetaNineBernoulliDefectTau_inv {tau : ℝ} (hτ : tau ≠ 0) :
    zetaNineBernoulliDefectTau tau = -zetaNineBernoulliDefectTau tau⁻¹ := by
  rw [zetaNineBernoulliDefectTau_explicit hτ,
    zetaNineBernoulliDefectTau_explicit (inv_ne_zero hτ)]
  field_simp [hτ]
  ring

end InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions
