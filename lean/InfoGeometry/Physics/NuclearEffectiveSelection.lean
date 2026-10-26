/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearEffectiveObservables
import InfoGeometry.Physics.NuclearSymmetrySectors

/-!
# Symmetry-forbidden blocks of effective transition operators

Ambient covariance passes through the actual adjoint-sandwich effective
operator, and incompatible model spectral weights force its projected block
to vanish. Initial and final state spaces remain separate. The parity
specialization applies to E2 and M1 because both have spatial-parity character
one; their physical covariance laws must still be supplied.

No angular triangle theorem, full-carrier Hilbert structure, or nonzero
amplitude for an allowed transition is inferred here.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearEffectiveSelection

open InfoGeometry.Physics.NuclearEffectiveObservables
open InfoGeometry.Physics.NuclearSymmetrySectors

variable {K Mi Mf Hi Hf : Type*} [RCLike K]
variable [NormedAddCommGroup Mi] [InnerProductSpace K Mi]
variable [NormedAddCommGroup Mf] [InnerProductSpace K Mf] [CompleteSpace Mf]
variable [NormedAddCommGroup Hi] [InnerProductSpace K Hi]
variable [NormedAddCommGroup Hf] [InnerProductSpace K Hf] [CompleteSpace Hf]

/-- Forbidden effective blocks follow from ambient symmetry covariance and
wave-map intertwining, rather than from an assumed effective selection rule. -/
theorem effective_block_zero
    (Ωi : Mi →L[K] Hi) (Ωf : Mf →L[K] Hf) (O : Hi →L[K] Hf)
    (Si : Hi →L[K] Hi) (Sf : Hf →L[K] Hf)
    (si Pi : Mi →L[K] Mi) (sf Pf : Mf →L[K] Mf) (wi wf η : K)
    (hΩi : Si.comp Ωi = Ωi.comp si) (hΩf : Sf.comp Ωf = Ωf.comp sf)
    (hSf : Sf.adjoint = Sf) (hsf : sf.adjoint = sf)
    (hO : Sf.comp O = η • O.comp Si)
    (hi : si.comp Pi = wi • Pi) (hf : Pf.comp sf = wf • Pf)
    (hne : wf ≠ η * wi) :
    Pf.comp ((effectiveOperator Ωi Ωf O).comp Pi) = 0 := by
  have he := effectiveOperator_intertwines Ωi Ωf O Si Sf si sf η
    hΩi hΩf hSf hsf hO
  have hz := spectral_block_zero si.toLinearMap Pi.toLinearMap
    sf.toLinearMap Pf.toLinearMap (effectiveOperator Ωi Ωf O).toLinearMap
    wi wf η
    (congrArg (fun T : Mi →L[K] Mi => T.toLinearMap) hi)
    (congrArg (fun T : Mf →L[K] Mf => T.toLinearMap) hf)
    (congrArg (fun T : Mi →L[K] Mf => T.toLinearMap) he) hne
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun hz x

/-- E2 and M1 have parity character one. Under that supplied ambient law,
opposite spatial-parity model sectors have an identically zero dressed block.
This statement concerns spatial parity only, independently of the CAR grading. -/
theorem effective_opposite_spatial_parity_block_zero
    (Ωi : Mi →L[K] Hi) (Ωf : Mf →L[K] Hf) (O : Hi →L[K] Hf)
    (Si : Hi →L[K] Hi) (Sf : Hf →L[K] Hf)
    (si Pi : Mi →L[K] Mi) (sf Pf : Mf →L[K] Mf)
    (pi pf : SpatialParity)
    (hΩi : Si.comp Ωi = Ωi.comp si) (hΩf : Sf.comp Ωf = Ωf.comp sf)
    (hSf : Sf.adjoint = Sf) (hsf : sf.adjoint = sf)
    (hO : Sf.comp O = O.comp Si)
    (hi : si.comp Pi = (pi.sign : K) • Pi)
    (hf : Pf.comp sf = (pf.sign : K) • Pf) (hne : pf ≠ pi) :
    Pf.comp ((effectiveOperator Ωi Ωf O).comp Pi) = 0 := by
  apply effective_block_zero Ωi Ωf O Si Sf si Pi sf Pf
    (pi.sign : K) (pf.sign : K) 1 hΩi hΩf hSf hsf
  · simpa using hO
  · exact hi
  · exact hf
  · simp only [one_mul]
    intro h
    exact hne (SpatialParity.sign_injective (RCLike.ofReal_injective h))

end InfoGeometry.Physics.NuclearEffectiveSelection
