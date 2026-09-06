import InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge

noncomputable section

namespace InfoGeometry.Clifford.Cl55ChiralBlockAction

open InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep

noncomputable def chiralDecompositionEquiv :
    (chiralPlusSector × chiralMinusSector) ≃ₗ[ℝ] SpinorSpace 5 :=
  chiralPlusSector.prodEquivOfIsCompl chiralMinusSector chiralSectors_isCompl

theorem chiralDecompositionEquiv_apply
    (vplus : chiralPlusSector) (vminus : chiralMinusSector) :
    (chiralDecompositionEquiv (vplus, vminus) : SpinorSpace 5) =
      (vplus : SpinorSpace 5) + (vminus : SpinorSpace 5) := by
  simp [chiralDecompositionEquiv, Submodule.coe_prodEquivOfIsCompl']

theorem commuting_matrix_preserves_chiralPlus
    (A : SpinorMatrix 5)
    (hA : A * chiralPlusProjector = chiralPlusProjector * A)
    (v : SpinorSpace 5) (hv : v ∈ chiralPlusSector) :
    Matrix.mulVec A v ∈ chiralPlusSector := by
  change Matrix.mulVec chiralPlusProjector (Matrix.mulVec A v) = Matrix.mulVec A v
  calc
    Matrix.mulVec chiralPlusProjector (Matrix.mulVec A v) =
        Matrix.mulVec (chiralPlusProjector * A) v := by
          rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (A * chiralPlusProjector) v := by rw [hA]
    _ = Matrix.mulVec A (Matrix.mulVec chiralPlusProjector v) := by
          rw [← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec A v := by rw [hv]

theorem commuting_matrix_preserves_chiralMinus
    (A : SpinorMatrix 5)
    (hA : A * chiralMinusProjector = chiralMinusProjector * A)
    (v : SpinorSpace 5) (hv : v ∈ chiralMinusSector) :
    Matrix.mulVec A v ∈ chiralMinusSector := by
  change Matrix.mulVec chiralMinusProjector (Matrix.mulVec A v) = Matrix.mulVec A v
  calc
    Matrix.mulVec chiralMinusProjector (Matrix.mulVec A v) =
        Matrix.mulVec (chiralMinusProjector * A) v := by
          rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (A * chiralMinusProjector) v := by rw [hA]
    _ = Matrix.mulVec A (Matrix.mulVec chiralMinusProjector v) := by
          rw [← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec A v := by rw [hv]

theorem commuting_matrix_action_decomposes
    (A : SpinorMatrix 5)
    (v : SpinorSpace 5) :
    Matrix.mulVec A v =
      Matrix.mulVec A (Matrix.mulVec chiralPlusProjector v) +
        Matrix.mulVec A (Matrix.mulVec chiralMinusProjector v) := by
  have h := congrArg (Matrix.mulVec A)
    (InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge.chiral_projector_decomposition v)
  simpa only [Matrix.mulVec_add] using h.symm

def restrictToChiralPlus
    (A : SpinorMatrix 5)
    (hA : A * chiralPlusProjector = chiralPlusProjector * A) :
    chiralPlusSector →ₗ[ℝ] chiralPlusSector :=
  (A.mulVecLin.comp chiralPlusSector.subtype).codRestrict
    chiralPlusSector (fun v => commuting_matrix_preserves_chiralPlus A hA v.1 v.2)

def restrictToChiralMinus
    (A : SpinorMatrix 5)
    (hA : A * chiralMinusProjector = chiralMinusProjector * A) :
    chiralMinusSector →ₗ[ℝ] chiralMinusSector :=
  (A.mulVecLin.comp chiralMinusSector.subtype).codRestrict
    chiralMinusSector (fun v => commuting_matrix_preserves_chiralMinus A hA v.1 v.2)

theorem restrictToChiralPlus_mul_apply
    (A B : SpinorMatrix 5)
    (hA : A * chiralPlusProjector = chiralPlusProjector * A)
    (hB : B * chiralPlusProjector = chiralPlusProjector * B)
    (v : chiralPlusSector) :
    restrictToChiralPlus (A * B)
        (by
          calc
            A * B * chiralPlusProjector =
                A * (B * chiralPlusProjector) := by rw [mul_assoc]
            _ = A * (chiralPlusProjector * B) := by rw [hB]
            _ = (A * chiralPlusProjector) * B := by rw [mul_assoc]
            _ = (chiralPlusProjector * A) * B := by rw [hA]
            _ = chiralPlusProjector * (A * B) := by rw [mul_assoc]) v =
      restrictToChiralPlus A hA (restrictToChiralPlus B hB v) := by
  apply Subtype.ext
  simp only [restrictToChiralPlus, LinearMap.codRestrict_apply,
    LinearMap.comp_apply, Matrix.mulVecLin_apply]
  rw [← Matrix.mulVec_mulVec]
  rfl

theorem restrictToChiralMinus_mul_apply
    (A B : SpinorMatrix 5)
    (hA : A * chiralMinusProjector = chiralMinusProjector * A)
    (hB : B * chiralMinusProjector = chiralMinusProjector * B)
    (v : chiralMinusSector) :
    restrictToChiralMinus (A * B)
        (by
          calc
            A * B * chiralMinusProjector =
                A * (B * chiralMinusProjector) := by rw [mul_assoc]
            _ = A * (chiralMinusProjector * B) := by rw [hB]
            _ = (A * chiralMinusProjector) * B := by rw [mul_assoc]
            _ = (chiralMinusProjector * A) * B := by rw [hA]
            _ = chiralMinusProjector * (A * B) := by rw [mul_assoc]) v =
      restrictToChiralMinus A hA (restrictToChiralMinus B hB v) := by
  apply Subtype.ext
  simp only [restrictToChiralMinus, LinearMap.codRestrict_apply,
    LinearMap.comp_apply, Matrix.mulVecLin_apply]
  rw [← Matrix.mulVec_mulVec]
  rfl

theorem restrictToChiralPlus_one_apply (v : chiralPlusSector) :
    restrictToChiralPlus (1 : SpinorMatrix 5)
        (by simp) v = v := by
  apply Subtype.ext
  simp [restrictToChiralPlus]

theorem restrictToChiralMinus_one_apply (v : chiralMinusSector) :
    restrictToChiralMinus (1 : SpinorMatrix 5)
        (by simp) v = v := by
  apply Subtype.ext
  simp [restrictToChiralMinus]

@[simp] theorem restrictToChiralPlus_apply
    (A : SpinorMatrix 5)
    (hA : A * chiralPlusProjector = chiralPlusProjector * A)
    (v : chiralPlusSector) :
    restrictToChiralPlus A hA v =
      ⟨Matrix.mulVec A v.1, commuting_matrix_preserves_chiralPlus A hA v.1 v.2⟩ := by
  ext i
  rfl

@[simp] theorem restrictToChiralMinus_apply
    (A : SpinorMatrix 5)
    (hA : A * chiralMinusProjector = chiralMinusProjector * A)
    (v : chiralMinusSector) :
    restrictToChiralMinus A hA v =
      ⟨Matrix.mulVec A v.1, commuting_matrix_preserves_chiralMinus A hA v.1 v.2⟩ := by
  ext i
  rfl

end InfoGeometry.Clifford.Cl55ChiralBlockAction
