import Mathlib.Tactic
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.CliffordWaveletTransform

Witness-gated Clifford / geometric algebra wavelet transform.

Literature owner:
  Eckhard Hitzer, "Clifford (Geometric) Algebra Wavelet Transform",
  arXiv:1306.1620.

This file records the analytic wavelet machine:
* the native `Cl(1,1)` Clifford generator replacing scalar `i`;
* similitude-style dilation / translation / rotation parameters;
* reconstruction and its native left-inverse admissibility predicate.

Covariance and reproducing-kernel theorems require an explicit similitude
action, measure, and kernel.  They are not represented by opaque proposition
markers in this finite interface.

This file does not assert any prime-number or Riemann-zeta theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.CliffordWaveletTransform

/-- Native real Clifford coefficient algebra for the wavelet transform. -/
abbrev CliffordCoefficient : Type :=
  CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11

/-- The negative `Cl(1,1)` generator used as the geometric imaginary blade. -/
noncomputable abbrev cliffordBlade : CliffordCoefficient :=
  CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1)

/-- The native Clifford blade squares to `-1`. -/
theorem cliffordBlade_sq_neg_one :
    cliffordBlade * cliffordBlade = -1 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  simp [InfoGeometry.Clifford.Cl11Matrix.q11_apply]

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

  Signal : Type
  wavelet : Signal

  waveletTransform :
    Signal → SimilitudeParameter V → CliffordCoefficient

  reconstruction :
    (SimilitudeParameter V → CliffordCoefficient) → Signal

namespace CliffordWaveletModel

/-- Clifford coefficient carrier inherited from the unique blade owner. -/
abbrev A (W : CliffordWaveletModel) : Type :=
  CliffordCoefficient

/-- Historical projection name for the native Clifford-algebra ring structure. -/
instance instRing (W : CliffordWaveletModel) : Ring W.A :=
  inferInstance

/--
Admissibility is the native left-inverse relation between reconstruction and
the wavelet transform, rather than an unrelated proposition marker.
-/
def admissible (W : CliffordWaveletModel) : Prop :=
  Function.LeftInverse W.reconstruction W.waveletTransform

/-- Admissible signals are exactly reconstructed by the wavelet transform. -/
theorem reconstruction_waveletTransform
    (W : CliffordWaveletModel) (hAdm : W.admissible) (f : W.Signal) :
    W.reconstruction (W.waveletTransform f) = f :=
  hAdm f

/--
Covariance of the Clifford wavelet transform under explicit actions on signals
and coefficient functions.

The actions are parameters because `SimilitudeParameter` currently records
geometric data but does not yet carry a proved group law.
-/
def covariance
    (W : CliffordWaveletModel)
    (signalAction :
      SimilitudeParameter W.V → W.Signal → W.Signal)
    (coefficientAction :
      SimilitudeParameter W.V →
        (SimilitudeParameter W.V → W.A) →
          (SimilitudeParameter W.V → W.A)) : Prop :=
  ∀ g f,
    W.waveletTransform (signalAction g f) =
      coefficientAction g (W.waveletTransform f)

/-- A covariance property evaluates to the corresponding transform identity. -/
theorem waveletTransform_covariant
    (W : CliffordWaveletModel)
    (signalAction :
      SimilitudeParameter W.V → W.Signal → W.Signal)
    (coefficientAction :
      SimilitudeParameter W.V →
        (SimilitudeParameter W.V → W.A) →
          (SimilitudeParameter W.V → W.A))
    (hCov : W.covariance signalAction coefficientAction)
    (g : SimilitudeParameter W.V) (f : W.Signal) :
    W.waveletTransform (signalAction g f) =
      coefficientAction g (W.waveletTransform f) :=
  hCov g f

/--
Coefficient reproducing law: analysis after reconstruction is the identity on
the coefficient space.

Together with `admissible`, this states that analysis and reconstruction are
mutual inverses, without replacing either law by an opaque proposition field.
-/
def reproducingKernel (W : CliffordWaveletModel) : Prop :=
  Function.RightInverse W.reconstruction W.waveletTransform

/-- A reproducing law reconstructs every coefficient function exactly. -/
theorem waveletTransform_reconstruction
    (W : CliffordWaveletModel) (hRep : W.reproducingKernel)
    (coeff : SimilitudeParameter W.V → W.A) :
    W.waveletTransform (W.reconstruction coeff) = coeff :=
  hRep coeff

/- The supplied left and right inverse laws imply the native bijectivity
contract for the wavelet transform.  The converse is deliberately exposed
with an existential inverse below: bijectivity alone does not identify the
model's stored `reconstruction` field. -/
theorem admissible_and_reproducingKernel_bijective
    (W : CliffordWaveletModel) :
    W.admissible ∧ W.reproducingKernel → Function.Bijective W.waveletTransform := by
  intro h
  exact Function.bijective_iff_has_inverse.mpr
    ⟨W.reconstruction, h.1, h.2⟩

/-- Any bijective wavelet transform has a (possibly non-stored) two-sided
inverse.  This is the exact converse available without identifying the
model's reconstruction field with the chosen inverse. -/
theorem bijective_waveletTransform_has_inverse
    (W : CliffordWaveletModel) (hBijective : Function.Bijective W.waveletTransform) :
    ∃ inverse,
      Function.LeftInverse inverse W.waveletTransform ∧
        Function.RightInverse inverse W.waveletTransform := by
  exact Function.bijective_iff_has_inverse.mp hBijective

end CliffordWaveletModel

end InfoGeometry.Analysis.CliffordWaveletTransform
