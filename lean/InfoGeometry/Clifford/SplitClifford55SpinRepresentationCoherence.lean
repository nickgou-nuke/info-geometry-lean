import InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinGroupChiralityBridge

/-!
# Coherence of the transported Chevalley and native `Q55` spinor actions

The neutral-form bridge already identifies the two Clifford algebras.  This
owner records the stronger representation statement on the whole Clifford
algebra: the Chevalley spinor representation is the native `Q55` spinor
representation after transport.  No equality of independently chosen matrix
bases, and no physical or topological Spin identification, is asserted.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55SpinRepresentationCoherence

open InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
open InfoGeometry.Clifford.Clifford55

abbrev ChevalleyQ55 := SplitClifford55NeutralFormBridge.ChevalleyQ55
abbrev ChevalleySpin55 := SplitClifford55NeutralFormBridge.ChevalleySpin55
abbrev SpinMatrixGL55 := SplitClifford55NeutralFormBridge.SpinMatrixGL55

theorem neutralChevalleySpinorAlgEquiv_comp_coherent :
    neutralChevalleySpinorAlgEquiv.toAlgHom =
      Clifford55.cl55SpinorRepresentation.comp
        neutralCliffordAlgEquiv_for_chevalleyQ.toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change neutralChevalleySpinorAlgEquiv
      (CliffordAlgebra.ι ChevalleyQ55 v) =
    Clifford55.cl55SpinorRepresentation
      (neutralCliffordAlgEquiv_for_chevalleyQ
        (CliffordAlgebra.ι ChevalleyQ55 v))
  rw [neutralChevalleySpinorAlgEquiv_ι,
    neutralCliffordAlgEquiv_for_chevalleyQ_ι]

theorem matrixSpinRepresentation_val_eq_native_clifford
    (g : ChevalleySpin55) :
    ((matrixSpinRepresentation g : SpinMatrixGL55) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      Clifford55.cl55SpinorRepresentation
        (neutralCliffordAlgEquiv_for_chevalleyQ
          (g : CliffordAlgebra ChevalleyQ55)) := by
  rw [matrixSpinRepresentation_val]
  exact congrArg (fun f => f (g : CliffordAlgebra ChevalleyQ55))
    neutralChevalleySpinorAlgEquiv_comp_coherent

theorem matrixSpinRepresentation_val_eq_native_clifford_comp
    (g : ChevalleySpin55) :
    ((matrixSpinRepresentation g : SpinMatrixGL55) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      (Clifford55.cl55SpinorRepresentation.comp
        neutralCliffordAlgEquiv_for_chevalleyQ.toAlgHom)
        (g : CliffordAlgebra ChevalleyQ55) := by
  exact matrixSpinRepresentation_val_eq_native_clifford g

theorem matrixSpinRepresentation_eq_native_comp_transport :
    matrixSpinRepresentation =
      nativeMatrixSpinRepresentation.comp
        spinGroupTransportEquiv.toMonoidHom := by
  apply MonoidHom.ext
  intro g
  change matrixSpinRepresentation g =
    matrixSpinRepresentation
      (spinGroupTransportEquiv.symm
        (spinGroupTransportEquiv g))
  exact congrArg matrixSpinRepresentation
    (spinGroupTransportEquiv.left_inv g).symm

theorem matrixSpinRepresentation_commutes_chirality55 (g : ChevalleySpin55) :
    ((matrixSpinRepresentation g : SpinMatrixGL55) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        InfoGeometry.Clifford.Cl55SpinorChirality.chirality55 =
      InfoGeometry.Clifford.Cl55SpinorChirality.chirality55 *
        ((matrixSpinRepresentation g : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  rw [matrixSpinRepresentation_val_eq_native_clifford]
  have htransport := spinGroupTransport_coe g
  rw [← htransport]
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
  rw [hrep]
  simpa only [spinGroupTransportEquiv_apply] using
    (Cl55SpinGroupChiralityBridge.spinGroup_matrix_commutes_chirality55
      (spinGroupTransportEquiv g))

theorem matrixSpinRepresentation_commutes_chiralPlusProjector
    (g : ChevalleySpin55) :
    ((matrixSpinRepresentation g : SpinMatrixGL55) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector =
      InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector *
        ((matrixSpinRepresentation g : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  have h := matrixSpinRepresentation_commutes_chirality55 g
  dsimp [InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector]
  simp [mul_add, add_mul, h]

theorem matrixSpinRepresentation_commutes_chiralMinusProjector
    (g : ChevalleySpin55) :
    ((matrixSpinRepresentation g : SpinMatrixGL55) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector =
      InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector *
        ((matrixSpinRepresentation g : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  have h := matrixSpinRepresentation_commutes_chirality55 g
  dsimp [InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector]
  simp [mul_sub, sub_mul, h]

theorem matrixSpinRepresentation_preserves_chiralPlus_vector
    (g : ChevalleySpin55) (v : Fin (2 ^ 5) → ℝ)
    (hv : Matrix.mulVec
      InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector v = v) :
    Matrix.mulVec InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector
        (Matrix.mulVec
          ((matrixSpinRepresentation g : SpinMatrixGL55) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v) =
      Matrix.mulVec
        ((matrixSpinRepresentation g : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v := by
  calc
    Matrix.mulVec InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector
        (Matrix.mulVec
          ((matrixSpinRepresentation g : SpinMatrixGL55) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v) =
        Matrix.mulVec
          (InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector *
            ((matrixSpinRepresentation g : SpinMatrixGL55) :
              InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) v := by
      rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec
          (((matrixSpinRepresentation g : SpinMatrixGL55) :
              InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
            InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector) v := by
      rw [← matrixSpinRepresentation_commutes_chiralPlusProjector]
    _ = Matrix.mulVec
          ((matrixSpinRepresentation g : SpinMatrixGL55) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)
          (Matrix.mulVec
            InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector v) := by
      rw [← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec
          ((matrixSpinRepresentation g : SpinMatrixGL55) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v := by
      rw [hv]

theorem matrixSpinRepresentation_preserves_chiralMinus_vector
    (g : ChevalleySpin55) (v : Fin (2 ^ 5) → ℝ)
    (hv : Matrix.mulVec
      InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector v = v) :
    Matrix.mulVec InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector
        (Matrix.mulVec
          ((matrixSpinRepresentation g : SpinMatrixGL55) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v) =
      Matrix.mulVec
        ((matrixSpinRepresentation g : SpinMatrixGL55) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v := by
  calc
    Matrix.mulVec InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector
        (Matrix.mulVec
          ((matrixSpinRepresentation g : SpinMatrixGL55) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v) =
        Matrix.mulVec
          (InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector *
            ((matrixSpinRepresentation g : SpinMatrixGL55) :
              InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) v := by
      rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec
          (((matrixSpinRepresentation g : SpinMatrixGL55) :
              InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
            InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector) v := by
      rw [← matrixSpinRepresentation_commutes_chiralMinusProjector]
    _ = Matrix.mulVec
          ((matrixSpinRepresentation g : SpinMatrixGL55) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)
          (Matrix.mulVec
            InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector v) := by
      rw [← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec
          ((matrixSpinRepresentation g : SpinMatrixGL55) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v := by
      rw [hv]

end InfoGeometry.Clifford.SplitClifford55SpinRepresentationCoherence
