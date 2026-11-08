import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
import InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge
import InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge

/-!
# Native transport of the finite Krein adjoint

The matrix-level Krein adjoint is transported exactly to the native
continuous-linear-map carrier.  This is an algebraic finite-dimensional
transport theorem; it does not assert a Krein completion, regularity of an
unbounded operator, or a Kasparov class.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeKreinTransportBridge

open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge
open InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge

abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32
abbrev Mat32GL := Mat32ˣ

variable {G : Type*} [Group G]

theorem nativeKreinAdjoint_nativeContinuous (A : Mat32) :
    nativeKreinAdjoint (nativeContinuous A) =
      nativeContinuous (kreinAdjoint masterKreinFundamentalSymmetry A) := by
  unfold nativeKreinAdjoint nativeChirality kreinAdjoint
    masterKreinFundamentalSymmetry
  rw [nativeContinuous_adjoint_eq_transpose]
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  congr 1
  simp only [Matrix.mul_assoc]

theorem nativeKreinAdjoint_nativeContinuous_eq_neg_of_matrix
    (A : Mat32) (hA : IsKreinSkewAdjoint masterKreinFundamentalSymmetry A) :
    nativeKreinAdjoint (nativeContinuous A) = -nativeContinuous A := by
  rw [nativeKreinAdjoint_nativeContinuous]
  unfold IsKreinSkewAdjoint at hA
  rw [← nativeContinuous_neg]
  exact congrArg nativeContinuous hA

theorem nativeKreinAdjoint_nativeContinuous_eq_self_of_matrix
    (A : Mat32) (hA : IsKreinSelfAdjoint masterKreinFundamentalSymmetry A) :
    nativeKreinAdjoint (nativeContinuous A) = nativeContinuous A := by
  rw [nativeKreinAdjoint_nativeContinuous]
  unfold IsKreinSelfAdjoint at hA
  exact congrArg nativeContinuous hA

/-! Krein-unitarity is kept as an explicit supplied hypothesis. -/

def MatrixKreinUnitaryIntegratedAction
    (act : G2IntegratedAction G) : Prop :=
  ∀ g : G,
    kreinAdjoint masterKreinFundamentalSymmetry (act.U g : Mat32) =
      (↑((act.U g)⁻¹) : Mat32)

theorem nativeKreinAdjoint_integratedAction_of_matrix_krein_unitary
    (act : G2IntegratedAction G)
    (hK : MatrixKreinUnitaryIntegratedAction act) (g : G) :
    nativeKreinAdjoint (nativeContinuous (act.U g : Mat32)) =
      nativeContinuous (act.U g⁻¹ : Mat32) := by
  rw [nativeKreinAdjoint_nativeContinuous, hK g]
  congr 1
  exact (congrArg (fun u : Mat32GL => (u : Mat32)) (act.U.map_inv g)).symm

def MatrixHilbertUnitaryIntegratedAction
    (act : G2IntegratedAction G) : Prop :=
  ∀ g : G,
    Matrix.transpose (act.U g : Mat32) = (↑((act.U g)⁻¹) : Mat32)

theorem nativeHilbertAdjoint_integratedAction_of_matrix_unitary
    (act : G2IntegratedAction G)
    (hU : MatrixHilbertUnitaryIntegratedAction act) (g : G) :
    ContinuousLinearMap.adjoint (nativeContinuous (act.U g : Mat32)) =
      nativeContinuous (act.U g⁻¹ : Mat32) := by
  rw [nativeContinuous_adjoint_eq_transpose, hU g]
  congr 1
  exact (congrArg (fun u : Mat32GL => (u : Mat32)) (act.U.map_inv g)).symm

theorem nativeIntegratedAction_isometry_of_matrix_unitary
    (act : G2IntegratedAction G)
    (hU : MatrixHilbertUnitaryIntegratedAction act) (g : G) :
    Isometry (nativeContinuous (act.U g : Mat32)) := by
  refine AddMonoidHomClass.isometry_of_norm _ ?_
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
  rw [nativeHilbertAdjoint_integratedAction_of_matrix_unitary act hU g]
  exact nativeIntegratedAction_inverse_comp act g

noncomputable def nativeIntegratedLinearIsometry
    (act : G2IntegratedAction G)
    (hU : MatrixHilbertUnitaryIntegratedAction act) (g : G) :
    NativeSpinorCarrier →ₗᵢ[ℝ] NativeSpinorCarrier :=
  (nativeContinuous (act.U g : Mat32)).toLinearMap.toLinearIsometry
    (nativeIntegratedAction_isometry_of_matrix_unitary act hU g)

noncomputable def nativeIntegratedLinearIsometryEquiv
    (act : G2IntegratedAction G)
    (hU : MatrixHilbertUnitaryIntegratedAction act) (g : G) :
    NativeSpinorCarrier ≃ₗᵢ[ℝ] NativeSpinorCarrier :=
  LinearIsometryEquiv.ofSurjective
    (nativeIntegratedLinearIsometry act hU g)
    (nativeIntegratedAction_bijective act g).2

@[simp] theorem nativeIntegratedLinearIsometry_apply
    (act : G2IntegratedAction G)
    (hU : MatrixHilbertUnitaryIntegratedAction act) (g : G)
    (x : NativeSpinorCarrier) :
    nativeIntegratedLinearIsometry act hU g x =
      nativeContinuous (act.U g : Mat32) x := rfl

@[simp] theorem nativeIntegratedLinearIsometryEquiv_apply
    (act : G2IntegratedAction G)
    (hU : MatrixHilbertUnitaryIntegratedAction act) (g : G)
    (x : NativeSpinorCarrier) :
    nativeIntegratedLinearIsometryEquiv act hU g x =
      nativeContinuous (act.U g : Mat32) x := by
  rfl

theorem nativeIntegratedLinearIsometryEquiv_mul
    (act : G2IntegratedAction G)
    (hU : MatrixHilbertUnitaryIntegratedAction act) (g h : G) :
    (nativeIntegratedLinearIsometryEquiv act hU (g * h)).toLinearMap =
      (nativeIntegratedLinearIsometryEquiv act hU g).toLinearMap.comp
        (nativeIntegratedLinearIsometryEquiv act hU h).toLinearMap := by
  apply LinearMap.ext
  intro x
  change nativeContinuous (act.U (g * h) : Mat32) x =
    nativeContinuous (act.U g : Mat32)
      (nativeContinuous (act.U h : Mat32) x)
  rw [map_mul, Units.val_mul, nativeContinuous_mul]
  rfl

end InfoGeometry.Canonical.RealCl55NativeKreinTransportBridge
