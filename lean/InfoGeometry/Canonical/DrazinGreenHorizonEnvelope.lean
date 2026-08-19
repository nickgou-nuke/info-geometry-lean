import Mathlib.Tactic
import InfoGeometry.Canonical.HorizonZitterModes
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.DrazinGreenHorizonEnvelope

Drazin-Green-Hodge envelope interface.

This module separates the two Drazin roles:

* `p_A = A * Aᴰ` is the signal/horizon support;
* `H_L = 1 - L * Lᴰ` is the harmonic/generalized-zero projector of a
  frequency/Laplacian-like operator.

The matter envelope is the two-stage compression

`H_L * (p_A * x * p_A) * H_L`.

If `p_A` and `H_L` commute, the envelope is a single corner

`e_{A,L} * x * e_{A,L}`, where `e_{A,L} = p_A * H_L`.

The word "harmonic" is theorem-safe here: without additional semisimplicity or
self-adjoint Laplacian hypotheses, `H_L` is the Drazin generalized zero-sector
projector.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinGreenHorizonEnvelope

open InfoGeometry.Canonical.DrazinModularPersistence
open InfoGeometry.Canonical.HorizonZitterModes
open InfoGeometry.Canonical.Drazin

/--
Drazin/Green data for a frequency or Laplacian-like operator `L`.

`LD` is the Drazin inverse.  `P_reg = L * LD` is the regular/nonzero-sector
projector.  `P_harm = 1 - P_reg` is the harmonic/generalized-null projector.
-/
@[rep_depth operator]
structure DrazinGreenData
    (Obs : Type*) [Ring Obs] [Star Obs] where
  L : Obs
  LD : Obs
  P_reg : Obs
  P_harm : Obs
  index : ℕ
  hDrazin : IsDrazinInverse L LD index
  P_reg_def : P_reg = L * LD
  P_harm_def : P_harm = 1 - P_reg
  P_reg_self_adjoint : star P_reg = P_reg
  P_harm_self_adjoint : star P_harm = P_harm

namespace DrazinGreenData

variable {Obs : Type*} [Ring Obs] [Star Obs]
variable (G : DrazinGreenData Obs)

/-- The regular/nonzero-sector projector is idempotent. -/
@[rep_depth operator]
theorem P_reg_idempotent :
    G.P_reg * G.P_reg = G.P_reg := by
  rw [G.P_reg_def]
  exact IsDrazinInverse.projection_is_idempotent G.hDrazin

/-- The harmonic/generalized-zero projector is idempotent. -/
@[rep_depth operator]
theorem P_harm_idempotent :
    G.P_harm * G.P_harm = G.P_harm := by
  rw [G.P_harm_def, G.P_reg_def]
  simpa [IsDrazinInverse.complementaryProjection, IsDrazinInverse.projection] using
    IsDrazinInverse.complementaryProjection_is_idempotent G.hDrazin

/-- The Drazin Green operator commutes with the frequency operator on the core. -/
@[rep_depth operator]
theorem L_mul_LD_eq_LD_mul_L :
    G.L * G.LD = G.LD * G.L :=
  G.hDrazin.comm

end DrazinGreenData

/-- Drazin horizon data reuses the persistence support owner. -/
abbrev DrazinHorizon
    (Obs : Type*) [Ring Obs] [Star Obs] :=
  DrazinSupportData Obs

/--
Matter envelope:
first compress to the Drazin horizon `p_A`, then project to the
harmonic/generalized-zero sector of `L`.
-/
@[rep_depth operator]
def horizonHarmonicEnvelope
    {Obs : Type*} [Ring Obs] [Star Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs)
    (x : Obs) : Obs :=
  G.P_harm * (H.p * x * H.p) * G.P_harm

/--
The combined matter support, valid as a single clean projector when the
Drazin horizon and harmonic projector commute.
-/
@[rep_depth operator]
def matterSupport
    {Obs : Type*} [Ring Obs] [Star Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs) : Obs :=
  H.p * G.P_harm

/--
If the horizon projector and harmonic projector commute, their product is an
idempotent matter support.
-/
@[rep_depth operator]
theorem matterSupport_idempotent
    {Obs : Type*} [Ring Obs] [Star Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs)
    (hComm : H.p * G.P_harm = G.P_harm * H.p) :
    matterSupport H G * matterSupport H G = matterSupport H G := by
  unfold matterSupport
  calc
    (H.p * G.P_harm) * (H.p * G.P_harm)
        = H.p * (G.P_harm * H.p) * G.P_harm := by
            simp only [mul_assoc]
    _ = H.p * (H.p * G.P_harm) * G.P_harm := by
            rw [← hComm]
    _ = (H.p * H.p) * (G.P_harm * G.P_harm) := by
            simp only [mul_assoc]
    _ = H.p * G.P_harm := by
            rw [H.p_idempotent, G.P_harm_idempotent]

/--
If the horizon and harmonic projectors commute, their product is self-adjoint.
-/
@[rep_depth operator]
theorem matterSupport_self_adjoint
    {Obs : Type*} [Ring Obs] [StarRing Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs)
    (hComm : H.p * G.P_harm = G.P_harm * H.p) :
    star (matterSupport H G) = matterSupport H G := by
  unfold matterSupport
  rw [star_mul, H.p_self_adjoint, G.P_harm_self_adjoint]
  exact hComm.symm

/--
If `p_A` and `P_harm` commute, the two-stage envelope equals compression by
the combined matter support `e = p_A * P_harm`.
-/
@[rep_depth operator]
theorem envelope_eq_combined_support_compression
    {Obs : Type*} [Ring Obs] [Star Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs)
    (x : Obs)
    (hComm : H.p * G.P_harm = G.P_harm * H.p) :
    horizonHarmonicEnvelope H G x =
      matterSupport H G * x * matterSupport H G := by
  unfold horizonHarmonicEnvelope matterSupport
  calc
    G.P_harm * (H.p * x * H.p) * G.P_harm
        = (G.P_harm * H.p) * x * (H.p * G.P_harm) := by
            simp only [mul_assoc]
    _ = (H.p * G.P_harm) * x * (H.p * G.P_harm) := by
            rw [← hComm]

theorem envelope_left_matterSupport_stable
    {Obs : Type*} [Ring Obs] [Star Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs)
    (x : Obs)
    (hComm : H.p * G.P_harm = G.P_harm * H.p) :
    matterSupport H G * horizonHarmonicEnvelope H G x =
      horizonHarmonicEnvelope H G x := by
  rw [envelope_eq_combined_support_compression H G x hComm]
  have he : matterSupport H G * matterSupport H G = matterSupport H G :=
    matterSupport_idempotent H G hComm
  calc
    matterSupport H G * (matterSupport H G * x * matterSupport H G) =
        (matterSupport H G * matterSupport H G) * x * matterSupport H G := by
          simp only [mul_assoc]
    _ = matterSupport H G * x * matterSupport H G := by rw [he]

theorem envelope_right_matterSupport_stable
    {Obs : Type*} [Ring Obs] [Star Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs)
    (x : Obs)
    (hComm : H.p * G.P_harm = G.P_harm * H.p) :
    horizonHarmonicEnvelope H G x * matterSupport H G =
      horizonHarmonicEnvelope H G x := by
  rw [envelope_eq_combined_support_compression H G x hComm]
  have he : matterSupport H G * matterSupport H G = matterSupport H G :=
    matterSupport_idempotent H G hComm
  calc
    (matterSupport H G * x * matterSupport H G) * matterSupport H G =
        matterSupport H G * x * (matterSupport H G * matterSupport H G) := by
          simp only [mul_assoc]
    _ = matterSupport H G * x * matterSupport H G := by rw [he]

theorem horizonHarmonicEnvelope_self_adjoint
    {Obs : Type*} [Ring Obs] [StarRing Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs)
    (x : Obs)
    (hx : star x = x) :
    star (horizonHarmonicEnvelope H G x) =
      horizonHarmonicEnvelope H G x := by
  unfold horizonHarmonicEnvelope
  simp [star_mul, H.p_self_adjoint, G.P_harm_self_adjoint, hx]
  noncomm_ring

/--
Convert `DrazinGreenData` into the frequency interface used by horizon zitter
modes.
-/
@[rep_depth operator]
def toDrazinFrequencyData
    {Obs : Type*} [Ring Obs] [Star Obs]
    (G : DrazinGreenData Obs) :
    DrazinFrequencyData Obs where
  L := G.L
  LD := G.LD
  harmonicProj := G.P_harm
  index := G.index
  hDrazin := G.hDrazin
  harmonicProj_def := by
    rw [G.P_harm_def, G.P_reg_def]
  harmonic_self_adjoint := G.P_harm_self_adjoint

end InfoGeometry.Canonical.DrazinGreenHorizonEnvelope
