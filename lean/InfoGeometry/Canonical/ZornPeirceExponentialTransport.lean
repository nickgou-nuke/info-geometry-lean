import InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame
import InfoGeometry.Canonical.ZornDerivationExponentialAutomorphism
import InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge

/-!
# Exponential transport of the canonical Peirce frame

The abstract Peirce owner works over an arbitrary commutative ring and accepts
a certified multiplicative linear equivalence.  This file supplies the
canonical real instance: the exponential of a canonical Zorn derivation.

No exponential is asserted over a general ring.  The real exponential and its
automorphism laws come from the continuous Zorn derivation owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornPeirceExponentialTransport

open InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
open InfoGeometry.Lie.ContinuousDerivationExponential
open InfoGeometry.Canonical.ZornDerivationExponentialAutomorphism

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

private theorem flow_is_aut
    (D : canonicalZornDerivations)
    (t : ℝ) :
    IsSplitOctonionAut
      (zornFlowLinearEquiv D.1 t) := by
  exact
    canonical_derivation_exponential_lands_in_realAut D t

theorem exp_transport_ePlus_idempotent
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t (ePlus (R := ℝ)) *
        zornFlowLinearEquiv D.1 t (ePlus (R := ℝ)) =
      zornFlowLinearEquiv D.1 t (ePlus (R := ℝ)) := by
  exact transportedEPlus_idempotent
    (R := ℝ) (zornFlowLinearEquiv D.1 t) (flow_is_aut D t)

theorem exp_transport_eMinus_idempotent
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t (eMinus (R := ℝ)) *
        zornFlowLinearEquiv D.1 t (eMinus (R := ℝ)) =
      zornFlowLinearEquiv D.1 t (eMinus (R := ℝ)) := by
  exact transportedEMinus_idempotent
    (R := ℝ) (zornFlowLinearEquiv D.1 t) (flow_is_aut D t)

theorem exp_transport_ePlus_eMinus
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t (ePlus (R := ℝ)) *
        zornFlowLinearEquiv D.1 t (eMinus (R := ℝ)) = 0 := by
  exact transportedEPlus_mul_transportedEMinus
    (R := ℝ) (zornFlowLinearEquiv D.1 t) (flow_is_aut D t)

theorem exp_transport_eMinus_ePlus
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t (eMinus (R := ℝ)) *
        zornFlowLinearEquiv D.1 t (ePlus (R := ℝ)) = 0 := by
  exact transportedEMinus_mul_transportedEPlus
    (R := ℝ) (zornFlowLinearEquiv D.1 t) (flow_is_aut D t)

theorem exp_transport_peirce_resolution
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t (ePlus (R := ℝ)) +
        zornFlowLinearEquiv D.1 t (eMinus (R := ℝ)) =
      (1 : CZ) := by
  change zornFlowLinearEquiv D.1 t (zornPlus (R := ℝ)) +
      zornFlowLinearEquiv D.1 t (zornMinus (R := ℝ)) = (1 : CZ)
  rw [← (zornFlowLinearEquiv D.1 t).map_add]
  rw [zornPlus_add_zornMinus]
  exact zornFlow_map_one D.1 D.2 t

theorem exp_transport_gPlus_square_zero
    (D : canonicalZornDerivations)
    (t : ℝ) (i : Fin 3) :
    zornFlowLinearEquiv D.1 t (gPlus (R := ℝ) i) *
        zornFlowLinearEquiv D.1 t (gPlus (R := ℝ) i) = 0 := by
  exact transportedGPlus_square_zero
    (R := ℝ) (zornFlowLinearEquiv D.1 t) (flow_is_aut D t) i

theorem exp_transport_gMinus_square_zero
    (D : canonicalZornDerivations)
    (t : ℝ) (i : Fin 3) :
    zornFlowLinearEquiv D.1 t (gMinus (R := ℝ) i) *
        zornFlowLinearEquiv D.1 t (gMinus (R := ℝ) i) = 0 := by
  exact transportedGMinus_square_zero
    (R := ℝ) (zornFlowLinearEquiv D.1 t) (flow_is_aut D t) i

theorem exp_transport_fixed_of_derivation_eq_zero
    (D : canonicalZornDerivations)
    (X : CZ)
    (hX : D.1 X = 0)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t X = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  have hcoord : coordEnd D.1 (coordLE X) = 0 := by
    rw [coordEnd_coordLE, hX]
    ext i
    fin_cases i <;> rfl
  exact flowLinearEquiv_fixed_of_derivation_eq_zero
    (coordEnd D.1) (coordLE X) hcoord t

theorem exp_transport_chiral_frame_fixed
    (D : canonicalZornDerivations)
    (hI : D.1 (chiralI (R := ℝ)) = 0)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t (ePlus (R := ℝ)) = ePlus (R := ℝ) ∧
    zornFlowLinearEquiv D.1 t (eMinus (R := ℝ)) = eMinus (R := ℝ) := by
  have hI_flow :
      zornFlowLinearEquiv D.1 t (chiralI (R := ℝ)) = chiralI (R := ℝ) :=
    exp_transport_fixed_of_derivation_eq_zero D _ hI t
  let U : SplitOctonionAutCandidate ℝ := zornFlowLinearEquiv D.1 t
  have hU : IsSplitOctonionAut U := by
    exact flow_is_aut D t
  have hPlus := transportedEPlus_eq_of_U_chiralI_eq_chiralI
    (R := ℝ) U hU hI_flow
  have hMinus := transportedEMinus_eq_of_U_chiralI_eq_chiralI
    (R := ℝ) U hU hI_flow
  exact ⟨hPlus, hMinus⟩

end InfoGeometry.Canonical.ZornPeirceExponentialTransport

end noncomputable section
