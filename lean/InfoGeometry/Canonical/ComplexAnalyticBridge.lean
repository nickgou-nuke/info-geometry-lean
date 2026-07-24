import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Canonical.HestenesAnalyticity
import InfoGeometry.Krein.DoubledSpace

noncomputable section

namespace InfoGeometry.Canonical.ComplexAnalyticBridge

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Krein
open Metric
open scoped _root_.Topology
open Filter
/-- Pulling `DifferentiableAt` out of `AnalyticAt` is standard Mathlib. -/
theorem differentiableAt_of_analyticAt
    {f : ℂ → ℂ} {z : ℂ} (h_an : AnalyticAt ℂ f z) :
    DifferentiableAt ℂ f z :=
  h_an.differentiableAt

local notation "H₂ℝ" => DoubledSpace ℝ

/-- The canonical phase structure on the real doubled carrier. -/
def doubledPhaseStructure : PhaseStructure H₂ℝ where
  K := clockAxis (E := ℝ)
  K_square := clockAxis_sq (E := ℝ)

/-- Compatibility name for the doubled real phase structure. -/
abbrev H2_phaseStructure : PhaseStructure H₂ℝ :=
  doubledPhaseStructure

/-- Complex number as a point of the real doubled carrier. -/
def complexToDoubled (z : ℂ) : H₂ℝ :=
  to_doubled z.re z.im

/-- Compatibility name for `complexToDoubled`. -/
abbrev to_doubled_real (z : ℂ) : H₂ℝ :=
  complexToDoubled z

/-- Recover a complex number from the real doubled carrier. -/
def doubledToComplex (v : H₂ℝ) : ℂ :=
  Complex.equivRealProdCLM.symm (WithLp.fst v, WithLp.snd v)

/-- Compatibility name for `doubledToComplex`. -/
abbrev from_doubled_real (v : H₂ℝ) : ℂ :=
  doubledToComplex v

@[simp] theorem doubledToComplex_complexToDoubled (z : ℂ) :
    doubledToComplex (complexToDoubled z) = z := by
  simpa [doubledToComplex, complexToDoubled]
    using Complex.equivRealProdCLM.symm_apply_apply z

@[simp] theorem complexToDoubled_doubledToComplex (v : H₂ℝ) :
    complexToDoubled (doubledToComplex v) = v := by
  apply DoubledSpace.ext <;>
    simp [doubledToComplex, complexToDoubled]

def realProdToDoubledCLM : (ℝ × ℝ) →L[ℝ] H₂ℝ where
  toFun := fun p => to_doubled p.1 p.2
  map_add' p q := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  map_smul' a p := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  cont := by
    simpa [to_doubled] using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := ℝ) (β := ℝ))

def doubledToRealProdCLM : H₂ℝ →L[ℝ] (ℝ × ℝ) where
  toFun := fun v => (WithLp.fst v, WithLp.snd v)
  map_add' u v := by
    simp
  map_smul' a u := by
    simp
  cont := by
    exact
      (WithLp.continuous_fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).prodMk
        (WithLp.continuous_snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ))

def complexToDoubledCLM : ℂ →L[ℝ] H₂ℝ :=
  realProdToDoubledCLM.comp Complex.equivRealProdCLM.toContinuousLinearMap

def doubledToComplexCLM : H₂ℝ →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp doubledToRealProdCLM

/-- The canonical continuous linear equivalence `ℂ ≃L[ℝ] DoubledSpace ℝ`. -/
def complexDoubledCLE : ℂ ≃L[ℝ] H₂ℝ where
  toFun := complexToDoubled
  invFun := doubledToComplex
  map_add' := by
    intro z w
    change complexToDoubled (z + w) = complexToDoubled z + complexToDoubled w
    apply DoubledSpace.ext <;> simp [complexToDoubled, to_doubled]
  map_smul' := by
    intro a z
    change complexToDoubled (a • z) = a • complexToDoubled z
    apply DoubledSpace.ext <;> simp [complexToDoubled, to_doubled]
  continuous_toFun := complexToDoubledCLM.cont
  continuous_invFun := doubledToComplexCLM.cont
  left_inv := doubledToComplex_complexToDoubled
  right_inv := complexToDoubled_doubledToComplex

/-- Compatibility name for `complexDoubledCLE`. -/
abbrev complex_equiv_H2 : ℂ ≃L[ℝ] H₂ℝ :=
  complexDoubledCLE

@[simp] theorem complexToDoubledCLM_apply (z : ℂ) :
    complexToDoubledCLM z = complexToDoubled z := rfl

@[simp] theorem doubledToComplexCLM_apply (v : H₂ℝ) :
    doubledToComplexCLM v = doubledToComplex v := rfl

/-- On the doubled real carrier, `clockAxis` corresponds to multiplication by `I`. -/
@[simp] theorem doubledToComplex_clockAxis (v : H₂ℝ) :
    doubledToComplex (clockAxis (E := ℝ) v) = Complex.I * doubledToComplex v := by
  apply Complex.ext <;> simp [doubledToComplex, clockAxis, complex_i, modular_j, spectral_epsilon]

/-- Transported to the doubled carrier, multiplication by `I` is `clockAxis`. -/
@[simp] theorem clockAxis_complexToDoubled (z : ℂ) :
    clockAxis (E := ℝ) (complexToDoubled z) = complexToDoubled (Complex.I * z) := by
  apply DoubledSpace.ext <;> simp [complexToDoubled, clockAxis, complex_i, modular_j, spectral_epsilon]

/-- Honest one-way bridge already available in the bilingual analyticity owner. -/
def analyticAtToCauchyAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (h_an : AnalyticAt ℂ f z) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  analyticAt_complex_to_cauchyAnalyticAt h_an

/-- Compatibility name for the one-way complex-to-Hestenes bridge. -/
abbrev analyticAt_implies_cauchyAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (h_an : AnalyticAt ℂ f z) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  analyticAtToCauchyAnalyticAt h_an

/-- Lift a complex map to the doubled real carrier by transport across `complexDoubledCLE`. -/
def lifted (f : ℂ → ℂ) : H₂ℝ → H₂ℝ :=
  fun v => complexToDoubled (f (doubledToComplex v))

/--
Transport the native complex phase-line bridge to the doubled/clock-axis carrier.
-/
noncomputable def analyticAt_liftedToDoubled_cauchyAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (h_an : AnalyticAt ℂ f z) :
    CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
      (lifted f) (complexToDoubled z) := by
  let dC : ℂ →L[ℂ] ℂ := fderiv ℂ f z
  let dR : ℂ →L[ℝ] ℂ := dC.restrictScalars ℝ
  let deriv : H₂ℝ →L[ℝ] H₂ℝ :=
    complexDoubledCLE.toContinuousLinearMap.comp
      (dR.comp complexDoubledCLE.symm.toContinuousLinearMap)
  refine
    { deriv := deriv
      has_fderiv_at := ?_
      phase_linear_deriv := ?_ }
  · have h_inner :
        HasFDerivAt (fun v : H₂ℝ => f (doubledToComplex v))
          (dR.comp complexDoubledCLE.symm.toContinuousLinearMap)
          (complexToDoubled z) := by
      simpa [dR, dC, doubledToComplex, doubledToComplex_complexToDoubled] using
        (((h_an.differentiableAt.hasFDerivAt).restrictScalars ℝ).comp (complexToDoubled z)
          (complexDoubledCLE.symm.toContinuousLinearMap.hasFDerivAt))
    have h_outer :
        HasFDerivAt complexToDoubled complexDoubledCLE.toContinuousLinearMap (f z) :=
      complexDoubledCLE.toContinuousLinearMap.hasFDerivAt
    simpa [lifted, deriv] using h_outer.comp (complexToDoubled z) h_inner
  · have h_to :
        complexPhaseStructure.IsPhaseLinearMap
          complexDoubledCLE.toContinuousLinearMap doubledPhaseStructure := by
      apply ContinuousLinearMap.ext
      intro w
      change complexToDoubled (complexPhaseStructure.K w) =
          doubledPhaseStructure.K (complexToDoubled w)
      simpa [complexPhaseStructure, doubledPhaseStructure]
        using (clockAxis_complexToDoubled w).symm
    have h_from :
        doubledPhaseStructure.IsPhaseLinearMap
          complexDoubledCLE.symm.toContinuousLinearMap complexPhaseStructure := by
      apply ContinuousLinearMap.ext
      intro v
      change doubledToComplex (doubledPhaseStructure.K v) =
          complexPhaseStructure.K (doubledToComplex v)
      simpa [complexPhaseStructure, doubledPhaseStructure]
        using doubledToComplex_clockAxis v
    have h_mid :
        complexPhaseStructure.IsPhaseLinearMap dR complexPhaseStructure := by
      exact complexLinearMap_phaseLinear dC
    have h_inner :
        doubledPhaseStructure.IsPhaseLinearMap
          (dR.comp complexDoubledCLE.symm.toContinuousLinearMap)
          complexPhaseStructure :=
      PhaseStructure.comp_phaseLinear doubledPhaseStructure complexPhaseStructure complexPhaseStructure
        h_from h_mid
    simpa [deriv] using
      (PhaseStructure.comp_phaseLinear
        doubledPhaseStructure complexPhaseStructure doubledPhaseStructure
        h_inner h_to)

/-! ## Analyticity atlas: theorem-safe one-way formulations -/

/-- Complex differentiability at a point gives the repo Cauchy-analytic structure at that point. -/
def differentiableAtToCauchyAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z := by
  let dC : ℂ →L[ℂ] ℂ := fderiv ℂ f z
  exact
    { deriv := dC.restrictScalars ℝ
      has_fderiv_at := hf.hasFDerivAt.restrictScalars ℝ
      phase_linear_deriv := complexLinearMap_phaseLinear dC }

/-- Differentiability in a neighborhood implies Mathlib `AnalyticAt`. -/
theorem eventuallyDifferentiableAtToAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w) :
    AnalyticAt ℂ f z :=
  (Complex.analyticAt_iff_eventually_differentiableAt).2 hf

/-- Mathlib `AnalyticAt` implies differentiability in a neighborhood. -/
theorem analyticAtToEventuallyDifferentiableAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w :=
  (Complex.analyticAt_iff_eventually_differentiableAt).1 hf

/-- Complex differentiability on a neighborhood implies Mathlib analyticity at the point. -/
theorem differentiableOnNhdToAnalyticAt
    {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableOn ℂ f s) (hz : s ∈ 𝓝 z) :
    AnalyticAt ℂ f z :=
  hf.analyticAt hz

/-- Complex differentiability on a neighborhood implies the repo Cauchy-analytic structure. -/
def differentiableOnNhdToCauchyAnalyticAt
    {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableOn ℂ f s) (hz : s ∈ 𝓝 z) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  analyticAtToCauchyAnalyticAt (differentiableOnNhdToAnalyticAt hf hz)

/-- Pointwise Cauchy-Riemann, as a real derivative condition, implies complex differentiability. -/
theorem realCauchyRiemannToDifferentiableAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z)
    (hCR : fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z 1) :
    DifferentiableAt ℂ f z :=
  (differentiableAt_complex_iff_differentiableAt_real).2 ⟨hf, hCR⟩

/-- Cauchy-Riemann on a neighborhood implies Mathlib analyticity at the point. -/
theorem eventuallyRealCauchyRiemannToAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : ∀ᶠ w in 𝓝 z,
      DifferentiableAt ℝ f w ∧
        fderiv ℝ f w Complex.I = Complex.I • fderiv ℝ f w 1) :
    AnalyticAt ℂ f z :=
  eventuallyDifferentiableAtToAnalyticAt <| by
    filter_upwards [hf] with w hw
    exact realCauchyRiemannToDifferentiableAt hw.1 hw.2

/-- Cauchy-Riemann on a neighborhood implies the repo Cauchy-analytic structure at the point. -/
def eventuallyRealCauchyRiemannToCauchyAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : ∀ᶠ w in 𝓝 z,
      DifferentiableAt ℝ f w ∧
        fderiv ℝ f w Complex.I = Complex.I • fderiv ℝ f w 1) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  analyticAtToCauchyAnalyticAt (eventuallyRealCauchyRiemannToAnalyticAt hf)

/-- Morera/primitive route on an open set: conservative plus continuous implies analyticity. -/
theorem moreraOnOpenToAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (hMorera : Complex.IsConservativeOn f U)
    (hCont : ContinuousOn f U) :
    AnalyticAt ℂ f z := by
  have hdiff : DifferentiableOn ℂ f U :=
    (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn (f := f) hU).1
      ⟨hMorera, hCont⟩
  exact hdiff.analyticAt (hU.mem_nhds hz)

/-- Morera/primitive route on an open set, landed in the repo Cauchy-analytic structure. -/
def moreraOnOpenToCauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (hMorera : Complex.IsConservativeOn f U)
    (hCont : ContinuousOn f U) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  analyticAtToCauchyAnalyticAt (moreraOnOpenToAnalyticAt hU hz hMorera hCont)

/-- Cauchy integral formula surface, re-exported at the bridge layer. -/
theorem cauchyIntegralFormulaOnClosedDisc
    {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * Real.pi * Complex.I : ℂ) • f w :=
  hf.circleIntegral_sub_inv_smul hw

/-- Cauchy integral formula normalized by `(2πi)⁻¹`. -/
theorem cauchyIntegralFormulaNormalized
    {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w :=
  hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

/-- Harmonic real functions give a complex-analytic partial expression. -/
theorem harmonicAtToAnalyticAtComplexPartial
    {f : ℂ → ℝ} {z : ℂ}
    (hf : InnerProductSpace.HarmonicAt f z) :
    AnalyticAt ℂ (fun w ↦ (fderiv ℝ f w 1 : ℂ) - Complex.I * (fderiv ℝ f w Complex.I : ℂ)) z :=
  HarmonicAt.analyticAt_complex_partial hf

/-- Harmonic real functions give a repo Cauchy-analytic complex partial expression. -/
def harmonicAtToCauchyAnalyticAtComplexPartial
    {f : ℂ → ℝ} {z : ℂ}
    (hf : InnerProductSpace.HarmonicAt f z) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure
      (fun w ↦ (fderiv ℝ f w 1 : ℂ) - Complex.I * (fderiv ℝ f w Complex.I : ℂ)) z :=
  analyticAtToCauchyAnalyticAt (harmonicAtToAnalyticAtComplexPartial hf)

/-- Holomorphic with nonzero derivative implies conformality. -/
theorem differentiableAtNonzeroDerivToConformalAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hderiv : deriv f z ≠ 0) :
    ConformalAt f z :=
  hf.conformalAt hderiv

/-- Holomorphic conformal data still lands in the repo Cauchy-analytic structure. -/
def conformalHolomorphicToCauchyAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (_hconf : ConformalAt f z) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  differentiableAtToCauchyAnalyticAt hf

end InfoGeometry.Canonical.ComplexAnalyticBridge
