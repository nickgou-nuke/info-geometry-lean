import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Analysis.CliffordWaveletTransform

/-!
# InfoGeometry.Analysis.CliffordWaveletDonohoStark

Clifford-wavelet Donoho--Stark support/concentration layer.

Literature owner:
  Sabrine Arfaoui,
  "Clifford wavelet transform and the associated Donoho-Stark's uncertainty Principle",
  arXiv:2209.12037.

This file owns a theorem-safe Donoho--Stark scaffold for the continuous
Clifford wavelet transform:

* support and concentration readouts;
* a positive uncertainty constant;
* an explicit Donoho--Stark lower-bound certificate;
* a noncollapse consequence for the weighted support product.

It does not assert any prime-number, Lee--Yang, xi, Mertens, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.CliffordWaveletDonohoStark

open InfoGeometry.Analysis.CliffordWaveletTransform

/-! ## Donoho--Stark support / concentration data -/

/--
Support/concentration witness for a Clifford wavelet model.

The paper owner gives the analytic inequality; this structure records the
support and concentration readouts together with the lower-bound certificate.
-/
@[rep_depth operator]
structure CliffordDonohoStark (W : CliffordWaveletModel) where
  /-- Spatial support readout for a signal. -/
  signalSupport : W.Signal → ℝ

  /-- Wavelet-domain support readout for the transformed signal. -/
  waveletSupport : (SimilitudeParameter W.V → W.A) → ℝ

  /-- Spatial concentration readout for a signal. -/
  signalConcentration : W.Signal → ℝ

  /-- Wavelet-domain concentration readout for the transformed signal. -/
  waveletConcentration : (SimilitudeParameter W.V → W.A) → ℝ

  /-- Positive Donoho--Stark constant. -/
  uncertaintyConstant : ℝ

  uncertaintyConstant_pos :
    0 < uncertaintyConstant

  signalSupport_nonneg :
    ∀ f, 0 ≤ signalSupport f

  waveletSupport_nonneg :
    ∀ g, 0 ≤ waveletSupport g

  signalConcentration_nonneg :
    ∀ f, 0 ≤ signalConcentration f

  waveletConcentration_nonneg :
    ∀ g, 0 ≤ waveletConcentration g

  /--
  Donoho--Stark support lower bound.

  The actual analytic theorem is stored here as a witness-gated certificate.
  -/
  donoho_stark_support :
    W.admissible →
      ∀ f : W.Signal,
        ∀ εT εΩ : ℝ,
          signalConcentration f ≤ εT →
          waveletConcentration (W.waveletTransform f) ≤ εΩ →
          εT + εΩ < 1 →
          uncertaintyConstant * signalSupport f
            * waveletSupport (W.waveletTransform f) ≥
              (1 - εT - εΩ)^2

  /-- The noncollapse law is part of the owner surface. -/
  noncollapse_law : Prop

namespace CliffordDonohoStarkOps

variable {W : CliffordWaveletModel}
variable (D : CliffordDonohoStark W)

/-- Re-export of the stored Donoho--Stark lower bound. -/
@[rep_depth operator]
theorem supportLowerBound
    (hAdm : W.admissible)
    {f : W.Signal} {εT εΩ : ℝ}
    (hT : D.signalConcentration f ≤ εT)
    (hΩ : D.waveletConcentration (W.waveletTransform f) ≤ εΩ)
    (hGap : εT + εΩ < 1) :
    D.uncertaintyConstant * D.signalSupport f
      * D.waveletSupport (W.waveletTransform f) ≥
        (1 - εT - εΩ)^2 :=
  D.donoho_stark_support hAdm f εT εΩ hT hΩ hGap

/--
Positive weighted support consequence.

If the concentration gap is below `1`, the weighted support product is strictly
positive.
-/
@[rep_depth operator]
theorem weightedSupport_pos
    (hAdm : W.admissible)
    {f : W.Signal} {εT εΩ : ℝ}
    (hT : D.signalConcentration f ≤ εT)
    (hΩ : D.waveletConcentration (W.waveletTransform f) ≤ εΩ)
    (hGap : εT + εΩ < 1) :
    0 < D.uncertaintyConstant * D.signalSupport f
      * D.waveletSupport (W.waveletTransform f) := by
  have hbound :
      D.uncertaintyConstant * D.signalSupport f
        * D.waveletSupport (W.waveletTransform f) ≥
          (1 - εT - εΩ)^2 :=
    supportLowerBound D hAdm hT hΩ hGap
  have hsq : 0 < (1 - εT - εΩ)^2 := by
    have hpos : 0 < 1 - εT - εΩ := by linarith
    exact sq_pos_of_pos hpos
  exact lt_of_lt_of_le hsq hbound

end CliffordDonohoStarkOps

end InfoGeometry.Analysis.CliffordWaveletDonohoStark
