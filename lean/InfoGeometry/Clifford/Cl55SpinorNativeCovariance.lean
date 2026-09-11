import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinGroupChiralityBridge
import InfoGeometry.Clifford.Cl55WittPinAction

/-!
# Native `Spin(5,5)` spinor covariance

This owner packages the existing native Clifford spinor representation on
`Spin55` and records its twisted conjugation action on vector generators.
It does not assert faithfulness, identify a kernel, or identify this action
with the corrected split-Pin subgroup.
-/

namespace InfoGeometry.Clifford.Clifford55

noncomputable section

noncomputable def spin55SpinorUnitRepresentation :
    Spin55 →* (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ :=
  (Units.map cl55SpinorRepresentation.toRingHom).comp spinGroup.toUnits

noncomputable def spin55TwistedSpinorUnitRepresentation :
    Spin55 →* (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ :=
  (Units.map involuteSpinorAlgHom.toRingHom.toMonoidHom).comp
    spinGroup.toUnits

theorem spin55SpinorUnitRepresentation_coe (g : Spin55) :
    ((spin55SpinorUnitRepresentation g :
        (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      cl55SpinorRepresentation ((spinGroup.toUnits g : Cl55ˣ) : Cl55) := by
  exact Units.coe_map cl55SpinorRepresentation.toRingHom.toMonoidHom
    (spinGroup.toUnits g)

theorem spin55SpinorUnitRepresentation_commutes_chirality55 (g : Spin55) :
    ((spin55SpinorUnitRepresentation g :
        (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        InfoGeometry.Clifford.Cl55SpinorChirality.chirality55 =
      InfoGeometry.Clifford.Cl55SpinorChirality.chirality55 *
        ((spin55SpinorUnitRepresentation g :
          (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  rw [spin55SpinorUnitRepresentation_coe]
  have hrep :
      cl55SpinorRepresentation (spinGroup.toUnits g : Cl55) =
        cl55SpinorAlgEquiv (spinGroup.toUnits g : Cl55) := by
    have h := congrArg
      (fun F : Cl55 →ₐ[ℝ]
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 =>
        F (spinGroup.toUnits g : Cl55))
      cl55SpinorAlgEquiv_toAlgHom_eq_representation
    simpa using h
  rw [hrep]
  exact Cl55SpinGroupChiralityBridge.spinGroup_matrix_commutes_chirality55 g

theorem spin55SpinorUnitRepresentation_commutes_chiralPlusProjector
    (g : Spin55) :
    ((spin55SpinorUnitRepresentation g :
        (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector =
      InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector *
        ((spin55SpinorUnitRepresentation g :
          (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  have h := spin55SpinorUnitRepresentation_commutes_chirality55 g
  dsimp [InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector]
  simp [mul_add, add_mul, h]

theorem spin55SpinorUnitRepresentation_commutes_chiralMinusProjector
    (g : Spin55) :
    ((spin55SpinorUnitRepresentation g :
        (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector =
      InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector *
        ((spin55SpinorUnitRepresentation g :
          (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  have h := spin55SpinorUnitRepresentation_commutes_chirality55 g
  dsimp [InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector]
  simp [mul_sub, sub_mul, h]

theorem spin55SpinorUnitRepresentation_preserves_chiralPlus_vector
    (g : Spin55) (v : Fin (2 ^ 5) → ℝ)
    (hv : Matrix.mulVec
      InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector v = v) :
    Matrix.mulVec InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector
        (Matrix.mulVec
          ((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v) =
      Matrix.mulVec
        ((spin55SpinorUnitRepresentation g :
          (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v := by
  calc
    Matrix.mulVec InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector
        (Matrix.mulVec
          ((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v) =
        Matrix.mulVec
          (InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector *
            ((spin55SpinorUnitRepresentation g :
              (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
              InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) v := by
      rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec
          (((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
            InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector) v := by
      rw [← spin55SpinorUnitRepresentation_commutes_chiralPlusProjector]
    _ = Matrix.mulVec
          ((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)
          (Matrix.mulVec
            InfoGeometry.Clifford.Cl55SpinorChirality.chiralPlusProjector v) := by
      rw [← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec
          ((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v := by
      rw [hv]

theorem spin55SpinorUnitRepresentation_preserves_chiralMinus_vector
    (g : Spin55) (v : Fin (2 ^ 5) → ℝ)
    (hv : Matrix.mulVec
      InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector v = v) :
    Matrix.mulVec InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector
        (Matrix.mulVec
          ((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v) =
      Matrix.mulVec
        ((spin55SpinorUnitRepresentation g :
          (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v := by
  calc
    Matrix.mulVec InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector
        (Matrix.mulVec
          ((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v) =
        Matrix.mulVec
          (InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector *
            ((spin55SpinorUnitRepresentation g :
              (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
              InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) v := by
      rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec
          (((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
            InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector) v := by
      rw [← spin55SpinorUnitRepresentation_commutes_chiralMinusProjector]
    _ = Matrix.mulVec
          ((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)
          (Matrix.mulVec
            InfoGeometry.Clifford.Cl55SpinorChirality.chiralMinusProjector v) := by
      rw [← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec
          ((spin55SpinorUnitRepresentation g :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
            InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) v := by
      rw [hv]

theorem spin55TwistedSpinorUnitRepresentation_apply_ι
    (g : Spin55) (v : V55) :
    ((spin55TwistedSpinorUnitRepresentation g :
        (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        cl55SpinorRepresentation (ι55 v) *
      (↑((spin55SpinorUnitRepresentation g)⁻¹) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      cl55SpinorRepresentation (ι55 (spinAction g v)) := by
  change cl55SpinorRepresentation
      (CliffordAlgebra.involute (spinGroup.toUnits g : Cl55)) *
        cl55SpinorRepresentation (ι55 v) *
      ((spin55SpinorUnitRepresentation g)⁻¹ :
        (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) = _
  have hU :
      cl55SpinorRepresentation ((spinGroup.toUnits g : Cl55ˣ) : Cl55) =
        ((spin55SpinorUnitRepresentation g :
          (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
    exact (spin55SpinorUnitRepresentation_coe g).symm
  have hinv :
      CliffordAlgebra.involute (spinGroup.toUnits g : Cl55) =
        (spinGroup.toUnits g : Cl55) := by
    simpa using (spinGroup.involute_eq g.property)
  have hι :
      ι55 (spinAction g v) =
        (spinGroup.toUnits g : Cl55) * ι55 v *
          (↑((spinGroup.toUnits g)⁻¹) : Cl55) := by
    have h := pinTwistedAction_apply_ι (spinToPin g) v
    have hu : pinToUnits (spinToPin g) = spinGroup.toUnits g := by
      apply Units.ext
      rfl
    simpa only [pinTwistedAdj, hu, hinv] using h
  have hUinv :
      (↑((spin55SpinorUnitRepresentation g)⁻¹) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
        cl55SpinorRepresentation
          (↑((spinGroup.toUnits g)⁻¹) : Cl55) := by
    change (↑((Units.map cl55SpinorRepresentation.toRingHom.toMonoidHom
        (spinGroup.toUnits g))⁻¹) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) = _
    rw [← (Units.map cl55SpinorRepresentation.toRingHom.toMonoidHom).map_inv]
    exact Units.coe_map cl55SpinorRepresentation.toRingHom.toMonoidHom
      ((spinGroup.toUnits g)⁻¹)
  rw [hinv, hUinv]
  rw [← map_mul, ← map_mul]
  exact congrArg cl55SpinorRepresentation hι.symm

end

end InfoGeometry.Clifford.Clifford55
