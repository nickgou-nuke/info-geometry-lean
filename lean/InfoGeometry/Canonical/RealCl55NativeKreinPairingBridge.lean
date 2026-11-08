import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealCl55NativeKreinTransportBridge

/-!
# Native Krein pairing preservation

This small consumer turns the transported Krein-adjoint identity into the
corresponding preservation law for the native indefinite pairing.  The
Krein-unitarity hypothesis remains explicit; no Hilbert-unitarity claim is
made for the integrated action.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeKreinPairingBridge

open scoped InnerProductSpace
open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge
open InfoGeometry.Canonical.RealCl55NativeKreinTransportBridge
open InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge

variable {G : Type*} [Group G]

abbrev NativeSpinorCLM :=
  RealCl55FiniteModuleEndBridge.NativeSpinorCLM

def nativeKreinPairing (x y : NativeSpinorCarrier) : ℝ :=
  ⟪nativeChirality x, y⟫_ℝ

theorem nativeKreinPairing_kreinAdjoint (T : NativeSpinorCLM)
    (x y : NativeSpinorCarrier) :
    nativeKreinPairing (T x) y =
      nativeKreinPairing x (nativeKreinAdjoint T y) := by
  unfold nativeKreinPairing nativeKreinAdjoint
  simp only [ContinuousLinearMap.comp_apply]
  have hJJ (z : NativeSpinorCarrier) :
      nativeChirality (nativeChirality z) = z := by
    have h := congrArg (fun L : NativeSpinorCLM => L z)
      nativeChirality_sq
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    ⟪nativeChirality (T x), y⟫_ℝ =
        ⟪T x, nativeChirality y⟫_ℝ := by
          simpa only [nativeChirality_hilbert_self_adjoint] using
            (ContinuousLinearMap.adjoint_inner_right nativeChirality (T x) y).symm
    _ = ⟪x, (ContinuousLinearMap.adjoint T) (nativeChirality y)⟫_ℝ := by
          exact (ContinuousLinearMap.adjoint_inner_right T x (nativeChirality y)).symm
    _ = ⟪nativeChirality x,
          nativeChirality ((ContinuousLinearMap.adjoint T)
            (nativeChirality y))⟫_ℝ := by
          have h := (ContinuousLinearMap.adjoint_inner_right nativeChirality x
            (nativeChirality ((ContinuousLinearMap.adjoint T)
              (nativeChirality y)))).symm
          rw [nativeChirality_hilbert_self_adjoint] at h
          rw [hJJ] at h
          exact h.symm

theorem nativeIntegratedAction_preserves_kreinPairing
    (act : G2IntegratedAction G)
    (hK : MatrixKreinUnitaryIntegratedAction act) (g : G)
    (x y : NativeSpinorCarrier) :
    nativeKreinPairing (nativeIntegratedAction act g x)
        (nativeIntegratedAction act g y) =
      nativeKreinPairing x y := by
  rw [nativeKreinPairing_kreinAdjoint]
  rw [nativeIntegratedAction_apply]
  rw [nativeKreinAdjoint_integratedAction_of_matrix_krein_unitary act hK g]
  have hcomp := congrArg (fun T : NativeSpinorCLM => T y)
    (nativeIntegratedAction_inverse_comp act g)
  simpa [nativeIntegratedAction_apply, ContinuousLinearMap.comp_apply] using
    congrArg (fun z : NativeSpinorCarrier => nativeKreinPairing x z) hcomp

end InfoGeometry.Canonical.RealCl55NativeKreinPairingBridge
