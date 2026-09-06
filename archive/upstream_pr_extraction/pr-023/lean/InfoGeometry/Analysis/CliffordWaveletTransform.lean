import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.CliffordWaveletTransform

Witness-gated Clifford / geometric algebra wavelet transform.

Literature owner:
  Eckhard Hitzer, "Clifford (Geometric) Algebra Wavelet Transform",
  arXiv:1306.1620.

This file records the analytic wavelet machine:
* a real Clifford blade replacing scalar `i`;
* similitude-style dilation / translation / rotation parameters;
* admissibility;
* covariance;
* reproducing kernel;
* reconstruction.

It does not assert any prime-number or Riemann-zeta theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.CliffordWaveletTransform

/-- Abstract real Clifford target with a distinguished blade squaring to `-1`.

In a later mathlib-rooted version, `A` should be replaced by an actual
`CliffordAlgebra Q`.
-/
@[rep_depth operator]
structure CliffordBladeModel where
  A : Type
  instRing : Ring A
  blade : A
  blade_sq_neg_one : blade * blade = -1

/-- Abstract similitude parameter: scale, translation, and rotation.

The concrete owner should later identify this with `SIM(n)`.
-/
@[rep_depth operator]
structure SimilitudeParameter (V : Type) where
  scale : ℝ
  translation : V
  rotation : V → V
  scale_pos : 0 < scale

/-- Clifford wavelet model.

`Signal` is the ambient function space.
`waveletTransform` is the CWT.
`reconstruction` is the inverse/reproducing reconstruction.
-/
@[rep_depth operator]
structure CliffordWaveletModel where
  V : Type
  A : Type
  instRing : Ring A
  blade : A
  blade_sq_neg_one : blade * blade = -1

  Signal : Type
  wavelet : Signal
  admissible : Prop

  waveletTransform :
    Signal → SimilitudeParameter V → A

  reconstruction :
    (SimilitudeParameter V → A) → Signal

  /-- Hitzer-style inversion theorem, stored as owner field. -/
  reconstruction_left_inverse :
    admissible →
      ∀ f : Signal,
        reconstruction (waveletTransform f) = f

  /-- Covariance under translation / dilation / rotation. -/
  covariance : Prop

  /-- Reproducing kernel property. -/
  reproducingKernel : Prop

end InfoGeometry.Analysis.CliffordWaveletTransform
