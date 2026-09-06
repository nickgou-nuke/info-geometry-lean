import InfoGeometry.Clifford.SplitClifford55SpinRepresentationCoherence
import InfoGeometry.Clifford.Cl55SpinGroupRestrictedChiralRepresentation
import InfoGeometry.Clifford.Cl55SpinGroupChiralLinearEquivRepresentation

/-!
# Transport of the native chiral Spin representations

The native `Spin55` actions on the two chiral submodules are already bundled
as monoid homomorphisms.  This owner transports those representations along
the existing Chevalley/`Q55` Spin equivalence.  It introduces no independent
spinor carrier, kernel statement, or covering assertion.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55SpinChiralTransportBridge

open InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
open InfoGeometry.Clifford.SplitClifford55SpinRepresentationCoherence
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
open InfoGeometry.Clifford.Cl55SpinGroupRestrictedChiralRepresentation
open InfoGeometry.Clifford.Cl55SpinGroupChiralLinearEquivRepresentation

abbrev ChevalleySpin55 := SplitClifford55NeutralFormBridge.ChevalleySpin55

noncomputable def transportedChiralPlusRepresentation :
    ChevalleySpin55 →* Module.End ℝ chiralPlusSector :=
  chiralPlusRepresentation.comp spinGroupTransportEquiv.toMonoidHom

noncomputable def transportedChiralMinusRepresentation :
    ChevalleySpin55 →* Module.End ℝ chiralMinusSector :=
  chiralMinusRepresentation.comp spinGroupTransportEquiv.toMonoidHom

@[simp] theorem transportedChiralPlusRepresentation_apply
    (g : ChevalleySpin55) :
    transportedChiralPlusRepresentation g =
      chiralPlusRepresentation (spinGroupTransportEquiv g) := by
  rfl

@[simp] theorem transportedChiralMinusRepresentation_apply
    (g : ChevalleySpin55) :
    transportedChiralMinusRepresentation g =
      chiralMinusRepresentation (spinGroupTransportEquiv g) := by
  rfl

noncomputable def transportedChiralPlusLinearEquivRepresentation :
    ChevalleySpin55 →* (chiralPlusSector ≃ₗ[ℝ] chiralPlusSector) :=
  chiralPlusLinearEquivRepresentation.comp spinGroupTransportEquiv.toMonoidHom

noncomputable def transportedChiralMinusLinearEquivRepresentation :
    ChevalleySpin55 →* (chiralMinusSector ≃ₗ[ℝ] chiralMinusSector) :=
  chiralMinusLinearEquivRepresentation.comp spinGroupTransportEquiv.toMonoidHom

@[simp] theorem transportedChiralPlusLinearEquivRepresentation_apply
    (g : ChevalleySpin55) :
    transportedChiralPlusLinearEquivRepresentation g =
      chiralPlusRepresentationEquiv (spinGroupTransportEquiv g) := by
  rfl

@[simp] theorem transportedChiralMinusLinearEquivRepresentation_apply
    (g : ChevalleySpin55) :
    transportedChiralMinusLinearEquivRepresentation g =
      chiralMinusRepresentationEquiv (spinGroupTransportEquiv g) := by
  rfl

theorem transportedChiralPlusLinearEquivRepresentation_inverse
    (g : ChevalleySpin55) :
    (transportedChiralPlusLinearEquivRepresentation g).symm =
      transportedChiralPlusLinearEquivRepresentation g⁻¹ := by
  rw [transportedChiralPlusLinearEquivRepresentation_apply,
    transportedChiralPlusLinearEquivRepresentation_apply,
    spinGroupTransportEquiv.map_inv]
  exact chiralPlusRepresentationEquiv_inverse _

theorem transportedChiralMinusLinearEquivRepresentation_inverse
    (g : ChevalleySpin55) :
    (transportedChiralMinusLinearEquivRepresentation g).symm =
      transportedChiralMinusLinearEquivRepresentation g⁻¹ := by
  rw [transportedChiralMinusLinearEquivRepresentation_apply,
    transportedChiralMinusLinearEquivRepresentation_apply,
    spinGroupTransportEquiv.map_inv]
  exact chiralMinusRepresentationEquiv_inverse _

theorem transportedChiralPlusRepresentation_matrix_readback
    (g : ChevalleySpin55) (v : chiralPlusSector) :
    (transportedChiralPlusRepresentation g v).1 =
      Matrix.mulVec
        ((matrixSpinRepresentation g :
          SplitClifford55NeutralFormBridge.SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v.1 := by
  have htransport := spinGroupTransport_coe g
  have hrep :
      Clifford55.cl55SpinorRepresentation
          (spinGroupTransport g : Clifford55.Cl55) =
        Clifford55.cl55SpinorAlgEquiv
          (spinGroupTransport g : Clifford55.Cl55) := by
    have h := congrArg
      (fun F : Clifford55.Cl55 →ₐ[ℝ]
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 =>
        F (spinGroupTransport g : Clifford55.Cl55))
      Clifford55.cl55SpinorAlgEquiv_toAlgHom_eq_representation
    simpa using h
  have hmatrix :
      ((matrixSpinRepresentation g :
        SplitClifford55NeutralFormBridge.SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
        Clifford55.cl55SpinorAlgEquiv
          (spinGroupTransport g : Clifford55.Cl55) := by
    rw [matrixSpinRepresentation_val_eq_native_clifford]
    rw [← htransport, hrep]
  rw [transportedChiralPlusRepresentation_apply,
    chiralPlusRepresentation_coe]
  change Matrix.mulVec
      (Clifford55.cl55SpinorAlgEquiv
        (spinGroupTransport g : Clifford55.Cl55)) v.1 = _
  rw [← hmatrix]

theorem transportedChiralMinusRepresentation_matrix_readback
    (g : ChevalleySpin55) (v : chiralMinusSector) :
    (transportedChiralMinusRepresentation g v).1 =
      Matrix.mulVec
        ((matrixSpinRepresentation g :
          SplitClifford55NeutralFormBridge.SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v.1 := by
  have htransport := spinGroupTransport_coe g
  have hrep :
      Clifford55.cl55SpinorRepresentation
          (spinGroupTransport g : Clifford55.Cl55) =
        Clifford55.cl55SpinorAlgEquiv
          (spinGroupTransport g : Clifford55.Cl55) := by
    have h := congrArg
      (fun F : Clifford55.Cl55 →ₐ[ℝ]
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 =>
        F (spinGroupTransport g : Clifford55.Cl55))
      Clifford55.cl55SpinorAlgEquiv_toAlgHom_eq_representation
    simpa using h
  have hmatrix :
      ((matrixSpinRepresentation g :
        SplitClifford55NeutralFormBridge.SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
        Clifford55.cl55SpinorAlgEquiv
          (spinGroupTransport g : Clifford55.Cl55) := by
    rw [matrixSpinRepresentation_val_eq_native_clifford]
    rw [← htransport, hrep]
  rw [transportedChiralMinusRepresentation_apply,
    chiralMinusRepresentation_coe]
  change Matrix.mulVec
      (Clifford55.cl55SpinorAlgEquiv
        (spinGroupTransport g : Clifford55.Cl55)) v.1 = _
  rw [← hmatrix]

end InfoGeometry.Clifford.SplitClifford55SpinChiralTransportBridge
