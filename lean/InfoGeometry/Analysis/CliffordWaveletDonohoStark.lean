import Mathlib.Tactic
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
* an explicit Donoho--Stark lower-bound hypothesis;
* a noncollapse consequence for the weighted support product.

It does not assert any prime-number, Lee--Yang, xi, Mertens, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.CliffordWaveletDonohoStark

open InfoGeometry.Analysis.CliffordWaveletTransform

/-! ## Donoho--Stark support / concentration data -/

/--
Support/concentration interface for a Clifford wavelet model.

The paper owner gives the analytic inequality; this structure records the
support and concentration readouts together with the lower-bound hypothesis.
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

  This is an explicit analytic hypothesis of the interface.
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

namespace CliffordDonohoStarkOps

variable {W : CliffordWaveletModel}
variable (D : CliffordDonohoStark W)

/-- Re-export of the stored wavelet-domain concentration nonnegativity. -/
@[rep_depth operator]
theorem waveletConcentration_nonneg
    (g : SimilitudeParameter W.V → W.A) :
    0 ≤ D.waveletConcentration g :=
  D.waveletConcentration_nonneg g

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

/-- Non-collapse of both support readouts under the Donoho--Stark gap. -/
@[rep_depth operator]
theorem noncollapse
    (hAdm : W.admissible)
    {f : W.Signal} {εT εΩ : ℝ}
    (hT : D.signalConcentration f ≤ εT)
    (hΩ : D.waveletConcentration (W.waveletTransform f) ≤ εΩ)
    (hGap : εT + εΩ < 1) :
    D.signalSupport f ≠ 0 ∧
      D.waveletSupport (W.waveletTransform f) ≠ 0 := by
  have hprod := weightedSupport_pos D hAdm hT hΩ hGap
  constructor
  · intro hzero
    have hprod_zero :
        D.uncertaintyConstant * D.signalSupport f *
          D.waveletSupport (W.waveletTransform f) = 0 := by
      simp [hzero]
    exact (ne_of_gt hprod) hprod_zero
  · intro hzero
    have hprod_zero :
        D.uncertaintyConstant * D.signalSupport f *
          D.waveletSupport (W.waveletTransform f) = 0 := by
      simp [hzero]
    exact (ne_of_gt hprod) hprod_zero

/-- The signal support itself is nonzero under the Donoho--Stark gap. -/
theorem signalSupport_ne_zero
    (hAdm : W.admissible)
    {f : W.Signal} {εT εΩ : ℝ}
    (hT : D.signalConcentration f ≤ εT)
    (hΩ : D.waveletConcentration (W.waveletTransform f) ≤ εΩ)
    (hGap : εT + εΩ < 1) :
    D.signalSupport f ≠ 0 := by
  exact (CliffordDonohoStarkOps.noncollapse D hAdm hT hΩ hGap).1

/-- The wavelet support itself is nonzero under the Donoho--Stark gap. -/
theorem waveletSupport_ne_zero
    (hAdm : W.admissible)
    {f : W.Signal} {εT εΩ : ℝ}
    (hT : D.signalConcentration f ≤ εT)
    (hΩ : D.waveletConcentration (W.waveletTransform f) ≤ εΩ)
    (hGap : εT + εΩ < 1) :
    D.waveletSupport (W.waveletTransform f) ≠ 0 := by
  exact (CliffordDonohoStarkOps.noncollapse D hAdm hT hΩ hGap).2

/-- The signal support is strictly positive under the Donoho--Stark gap. -/
theorem signalSupport_pos
    (hAdm : W.admissible)
    {f : W.Signal} {εT εΩ : ℝ}
    (hT : D.signalConcentration f ≤ εT)
    (hΩ : D.waveletConcentration (W.waveletTransform f) ≤ εΩ)
    (hGap : εT + εΩ < 1) :
    0 < D.signalSupport f := by
  have hnonzero := signalSupport_ne_zero D hAdm hT hΩ hGap
  exact lt_of_le_of_ne (D.signalSupport_nonneg f) hnonzero.symm

/-- The wavelet support is strictly positive under the Donoho--Stark gap. -/
theorem waveletSupport_pos
    (hAdm : W.admissible)
    {f : W.Signal} {εT εΩ : ℝ}
    (hT : D.signalConcentration f ≤ εT)
    (hΩ : D.waveletConcentration (W.waveletTransform f) ≤ εΩ)
    (hGap : εT + εΩ < 1) :
    0 < D.waveletSupport (W.waveletTransform f) := by
  have hnonzero := waveletSupport_ne_zero D hAdm hT hΩ hGap
  exact lt_of_le_of_ne (D.waveletSupport_nonneg (W.waveletTransform f)) hnonzero.symm

end CliffordDonohoStarkOps

end InfoGeometry.Analysis.CliffordWaveletDonohoStark
