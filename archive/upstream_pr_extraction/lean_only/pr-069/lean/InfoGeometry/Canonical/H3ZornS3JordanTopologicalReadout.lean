import InfoGeometry.Algebra.F4S3JordanObstruction
import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.H3ZornMcCrimmonTraceIdentities
import InfoGeometry.Canonical.H3ZornTopCatReadout

/-!
# S₃ preservation of the verified H₃(𝕆ₛ) Jordan product

This owner packages the finite Peirce-permutation action together with the
installed Jordan product.  It deliberately proves preservation on the native
`H3Zorn` carrier before introducing any topological packaging.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open CategoryTheory

theorem S3OnH3Zorn_neg (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3Zorn σ (-X) = -S3OnH3Zorn σ X := by
  rw [← neg_one_smul ℝ X, S3OnH3Zorn_smul]
  simp

theorem S3OnH3Zorn_sub (σ : S3Perm) (X Y : H3Zorn ℝ) :
    S3OnH3Zorn σ (X - Y) = S3OnH3Zorn σ X - S3OnH3Zorn σ Y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, S3OnH3Zorn_add,
    S3OnH3Zorn_neg]

theorem s12_preserve_h3zorn_crossProduct (X Y : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s12 (crossProduct X Y) =
      crossProduct (S3OnH3Zorn S3Perm.s12 X)
        (S3OnH3Zorn S3Perm.s12 Y) := by
  unfold crossProduct
  rw [S3OnH3Zorn_sub, S3OnH3Zorn_sub]
  rw [s12_preserve_h3zorn_adjointQuad (X + Y),
    S3OnH3Zorn_add,
    s12_preserve_h3zorn_adjointQuad X,
    s12_preserve_h3zorn_adjointQuad Y]

noncomputable def S3CrossProductResidual (σ : S3Perm)
    (p : H3Zorn ℝ × H3Zorn ℝ) : H3Zorn ℝ :=
  S3OnH3Zorn σ (crossProduct p.1 p.2) -
    crossProduct (S3OnH3Zorn σ p.1) (S3OnH3Zorn σ p.2)

theorem S3CrossProductResidual_s12_eq_zero (p : H3Zorn ℝ × H3Zorn ℝ) :
    S3CrossProductResidual S3Perm.s12 p = 0 := by
  unfold S3CrossProductResidual
  rw [s12_preserve_h3zorn_crossProduct]
  exact sub_self _

theorem continuous_S3CrossProductResidual (σ : S3Perm) :
    Continuous (S3CrossProductResidual σ) := by
  have hleft : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      S3OnH3Zorn σ (crossProduct p.1 p.2)) :=
    (continuous_S3OnH3Zorn σ).comp continuous_h3Zorn_crossProduct
  have hpair : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      (S3OnH3Zorn σ p.1, S3OnH3Zorn σ p.2)) := by
    exact ((continuous_S3OnH3Zorn σ).comp continuous_fst).prodMk
      ((continuous_S3OnH3Zorn σ).comp continuous_snd)
  have hright : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      crossProduct (S3OnH3Zorn σ p.1) (S3OnH3Zorn σ p.2)) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_crossProduct.comp hpair
  exact hleft.sub hright

noncomputable def S3CrossProductResidualContinuousMap (σ : S3Perm) :
    C(H3Zorn ℝ × H3Zorn ℝ, H3Zorn ℝ) :=
  ⟨S3CrossProductResidual σ, continuous_S3CrossProductResidual σ⟩

noncomputable def S3CrossProductResidualTopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ × H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom (S3CrossProductResidualContinuousMap σ)

noncomputable def S3AdjointResidual (σ : S3Perm) (X : H3Zorn ℝ) :
    H3Zorn ℝ :=
  S3OnH3Zorn σ X.adjointQuad -
    (S3OnH3Zorn σ X).adjointQuad

theorem s23_preserve_h3zorn_adjointQuad (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s23 X.adjointQuad =
      (S3OnH3Zorn S3Perm.s23 X).adjointQuad := by
  cases X
  apply H3Zorn.ext_h3 <;>
    simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.conj_mul,
      ZornVectorMatrix.norm_conj] ; ring

theorem s31_preserve_h3zorn_adjointQuad (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s31 X.adjointQuad =
      (S3OnH3Zorn S3Perm.s31 X).adjointQuad := by
  cases X
  apply H3Zorn.ext_h3 <;>
    simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.conj_mul,
      ZornVectorMatrix.norm_conj] <;> ring

theorem s12_s23_preserve_h3zorn_adjointQuad (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s12_s23 X.adjointQuad =
      (S3OnH3Zorn S3Perm.s12_s23 X).adjointQuad := by
  cases X
  apply H3Zorn.ext_h3
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce] ; ring
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce] ; ring
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce]

theorem s23_s12_preserve_h3zorn_adjointQuad (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s23_s12 X.adjointQuad =
      (S3OnH3Zorn S3Perm.s23_s12 X).adjointQuad := by
  cases X
  apply H3Zorn.ext_h3
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce] ; ring
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce] ; ring
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce]

theorem S3OnH3Zorn_preserve_crossProduct_of_adjoint
    (σ : S3Perm)
    (hadj : ∀ Z : H3Zorn ℝ,
      S3OnH3Zorn σ Z.adjointQuad =
        (S3OnH3Zorn σ Z).adjointQuad)
    (X Y : H3Zorn ℝ) :
    S3OnH3Zorn σ (crossProduct X Y) =
      crossProduct (S3OnH3Zorn σ X) (S3OnH3Zorn σ Y) := by
  unfold crossProduct
  rw [S3OnH3Zorn_sub, S3OnH3Zorn_sub,
    hadj (X + Y), S3OnH3Zorn_add, hadj X, hadj Y]

theorem s23_preserve_h3zorn_crossProduct (X Y : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s23 (crossProduct X Y) =
      crossProduct (S3OnH3Zorn S3Perm.s23 X)
        (S3OnH3Zorn S3Perm.s23 Y) :=
  S3OnH3Zorn_preserve_crossProduct_of_adjoint S3Perm.s23
    s23_preserve_h3zorn_adjointQuad X Y

theorem s31_preserve_h3zorn_crossProduct (X Y : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s31 (crossProduct X Y) =
      crossProduct (S3OnH3Zorn S3Perm.s31 X)
        (S3OnH3Zorn S3Perm.s31 Y) :=
  S3OnH3Zorn_preserve_crossProduct_of_adjoint S3Perm.s31
    s31_preserve_h3zorn_adjointQuad X Y

theorem s12_s23_preserve_h3zorn_crossProduct (X Y : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s12_s23 (crossProduct X Y) =
      crossProduct (S3OnH3Zorn S3Perm.s12_s23 X)
        (S3OnH3Zorn S3Perm.s12_s23 Y) :=
  S3OnH3Zorn_preserve_crossProduct_of_adjoint S3Perm.s12_s23
    s12_s23_preserve_h3zorn_adjointQuad X Y

theorem s23_s12_preserve_h3zorn_crossProduct (X Y : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s23_s12 (crossProduct X Y) =
      crossProduct (S3OnH3Zorn S3Perm.s23_s12 X)
        (S3OnH3Zorn S3Perm.s23_s12 Y) :=
  S3OnH3Zorn_preserve_crossProduct_of_adjoint S3Perm.s23_s12
    s23_s12_preserve_h3zorn_adjointQuad X Y

theorem S3OnH3Zorn_preserve_traceBilin (σ : S3Perm)
    (X Y : H3Zorn ℝ) :
    H3Zorn.traceBilin (S3OnH3Zorn σ X) (S3OnH3Zorn σ Y) =
      H3Zorn.traceBilin X Y := by
  rcases σ <;> cases X <;> cases Y
  all_goals
    simp [H3Zorn.traceBilin, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.trace_mul_comm,
      ZornVectorMatrix.trace_mul_conj_comm]
    try ring

theorem S3OnH3Zorn_preserve_T (σ : S3Perm)
    (X Y Z : H3Zorn ℝ) :
    S3OnH3Zorn σ (H3Zorn.T X Y Z) =
      H3Zorn.T (S3OnH3Zorn σ X) (S3OnH3Zorn σ Y)
        (S3OnH3Zorn σ Z) := by
  rcases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rw [H3Zorn.T_outer_formula, H3Zorn.T_outer_formula]
    rw [S3OnH3Zorn_sub, S3OnH3Zorn_add, S3OnH3Zorn_smul,
      S3OnH3Zorn_smul, s12_preserve_h3zorn_crossProduct,
      s12_preserve_h3zorn_crossProduct]
    rw [S3OnH3Zorn_preserve_traceBilin S3Perm.s12 X Y,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s12 Z Y]
  · rw [H3Zorn.T_outer_formula, H3Zorn.T_outer_formula]
    rw [S3OnH3Zorn_sub, S3OnH3Zorn_add, S3OnH3Zorn_smul,
      S3OnH3Zorn_smul, s23_preserve_h3zorn_crossProduct,
      s23_preserve_h3zorn_crossProduct]
    rw [S3OnH3Zorn_preserve_traceBilin S3Perm.s23 X Y,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s23 Z Y]
  · rw [H3Zorn.T_outer_formula, H3Zorn.T_outer_formula]
    rw [S3OnH3Zorn_sub, S3OnH3Zorn_add, S3OnH3Zorn_smul,
      S3OnH3Zorn_smul, s31_preserve_h3zorn_crossProduct,
      s31_preserve_h3zorn_crossProduct]
    rw [S3OnH3Zorn_preserve_traceBilin S3Perm.s31 X Y,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s31 Z Y]
  · rw [H3Zorn.T_outer_formula, H3Zorn.T_outer_formula]
    rw [S3OnH3Zorn_sub, S3OnH3Zorn_add, S3OnH3Zorn_smul,
      S3OnH3Zorn_smul, s12_s23_preserve_h3zorn_crossProduct,
      s12_s23_preserve_h3zorn_crossProduct]
    rw [S3OnH3Zorn_preserve_traceBilin S3Perm.s12_s23 X Y,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s12_s23 Z Y]
  · rw [H3Zorn.T_outer_formula, H3Zorn.T_outer_formula]
    rw [S3OnH3Zorn_sub, S3OnH3Zorn_add, S3OnH3Zorn_smul,
      S3OnH3Zorn_smul, s23_s12_preserve_h3zorn_crossProduct,
      s23_s12_preserve_h3zorn_crossProduct]
    rw [S3OnH3Zorn_preserve_traceBilin S3Perm.s23_s12 X Y,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s23_s12 Z Y]

theorem S3OnH3Zorn_preserve_candidateJordanMul (σ : S3Perm)
  (X Y : H3Zorn ℝ) :
    S3OnH3Zorn σ (X * Y) =
      S3OnH3Zorn σ X * S3OnH3Zorn σ Y := by
  simp only [← candidateJordanMul_eq_mul]
  simp only [candidateJordanMul]
  rw [S3OnH3Zorn_smul, S3OnH3Zorn_preserve_T, S3OnH3Zorn_one]

theorem S3OnH3Zorn_preserve_adjointQuad (σ : S3Perm)
    (X : H3Zorn ℝ) :
    S3OnH3Zorn σ X.adjointQuad =
      (S3OnH3Zorn σ X).adjointQuad := by
  rcases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact s12_preserve_h3zorn_adjointQuad X
  · exact s23_preserve_h3zorn_adjointQuad X
  · exact s31_preserve_h3zorn_adjointQuad X
  · exact s12_s23_preserve_h3zorn_adjointQuad X
  · exact s23_s12_preserve_h3zorn_adjointQuad X

theorem S3OnH3Zorn_preserve_normCubic (σ : S3Perm)
    (X : H3Zorn ℝ) :
    H3Zorn.normCubic (S3OnH3Zorn σ X) = H3Zorn.normCubic X := by
  have hleft := H3Zorn.mccrimmon_identity_13 (S3OnH3Zorn σ X)
  have hright := H3Zorn.mccrimmon_identity_13 X
  have htrace := S3OnH3Zorn_preserve_traceBilin σ X.adjointQuad X
  have hcalc :
      3 * H3Zorn.normCubic (S3OnH3Zorn σ X) =
        3 * H3Zorn.normCubic X := by
    calc
      3 * H3Zorn.normCubic (S3OnH3Zorn σ X) =
          H3Zorn.traceBilin ((S3OnH3Zorn σ X).adjointQuad)
            (S3OnH3Zorn σ X) := hleft.symm
      _ = H3Zorn.traceBilin (S3OnH3Zorn σ X.adjointQuad)
            (S3OnH3Zorn σ X) := by
        rw [S3OnH3Zorn_preserve_adjointQuad]
      _ = H3Zorn.traceBilin X.adjointQuad X := htrace
      _ = 3 * H3Zorn.normCubic X := hright
  nlinarith [hcalc]

theorem S3OnH3ZornTopCat_comp_adjointQuad (σ : S3Perm) :
    s3OnH3ZornReadoutTopCat σ ≫ h3ZornAdjointQuadTopCat =
      h3ZornAdjointQuadTopCat ≫ s3OnH3ZornReadoutTopCat σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app, TopCat.comp_app]
  simpa [h3ZornAdjointQuadTopCat, s3OnH3ZornReadoutTopCat] using
    (S3OnH3Zorn_preserve_adjointQuad σ X).symm

theorem normCubicAfterS3TopCat_eq_normCubicTopCat (σ : S3Perm) :
    normCubicAfterS3TopCat σ = h3ZornNormCubicTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  simpa [normCubicAfterS3TopCat, h3ZornNormCubicTopCat] using
    S3OnH3Zorn_preserve_normCubic σ X

theorem S3OnH3Zorn_preserve_crossProduct (σ : S3Perm)
    (X Y : H3Zorn ℝ) :
    S3OnH3Zorn σ (crossProduct X Y) =
      crossProduct (S3OnH3Zorn σ X) (S3OnH3Zorn σ Y) := by
  rcases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact s12_preserve_h3zorn_crossProduct X Y
  · exact s23_preserve_h3zorn_crossProduct X Y
  · exact s31_preserve_h3zorn_crossProduct X Y
  · exact s12_s23_preserve_h3zorn_crossProduct X Y
  · exact s23_s12_preserve_h3zorn_crossProduct X Y

noncomputable def S3OnH3ZornPairTopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ × H3Zorn ℝ) ⟶
      TopCat.of (H3Zorn ℝ × H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun p : H3Zorn ℝ × H3Zorn ℝ =>
        (S3OnH3Zorn σ p.1, S3OnH3Zorn σ p.2)
      continuous_toFun :=
        ((continuous_S3OnH3Zorn σ).comp continuous_fst).prodMk
          ((continuous_S3OnH3Zorn σ).comp continuous_snd) }

@[simp] theorem S3OnH3ZornPairTopCat_apply
    (σ : S3Perm) (p : H3Zorn ℝ × H3Zorn ℝ) :
    S3OnH3ZornPairTopCat σ p =
      (S3OnH3Zorn σ p.1, S3OnH3Zorn σ p.2) :=
  rfl

theorem S3OnH3ZornPairTopCat_comp_jordanMul (σ : S3Perm) :
    S3OnH3ZornPairTopCat σ ≫ h3ZornJordanMulTopCat =
      h3ZornJordanMulTopCat ≫ s3OnH3ZornReadoutTopCat σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app, TopCat.comp_app]
  simpa [S3OnH3ZornPairTopCat, h3ZornJordanMulTopCat,
    s3OnH3ZornReadoutTopCat] using
      (S3OnH3Zorn_preserve_candidateJordanMul σ p.1 p.2).symm

theorem S3OnH3ZornPairTopCat_comp_traceBilin (σ : S3Perm) :
    S3OnH3ZornPairTopCat σ ≫ h3ZornTraceBilinTopCat =
      h3ZornTraceBilinTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  simpa [S3OnH3ZornPairTopCat, h3ZornTraceBilinTopCat] using
    S3OnH3Zorn_preserve_traceBilin σ p.1 p.2

theorem S3OnH3ZornPairTopCat_comp_crossProduct (σ : S3Perm) :
    S3OnH3ZornPairTopCat σ ≫ h3ZornCrossProductTopCat =
      h3ZornCrossProductTopCat ≫ s3OnH3ZornReadoutTopCat σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app, TopCat.comp_app]
  simpa [S3OnH3ZornPairTopCat, h3ZornCrossProductTopCat,
    s3OnH3ZornReadoutTopCat] using
      (S3OnH3Zorn_preserve_crossProduct σ p.1 p.2).symm

noncomputable def S3OnH3ZornTripleTopCat (σ : S3Perm) :
    TopCat.of ((H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) ⟶
      TopCat.of ((H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
        ((S3OnH3Zorn σ p.1.1, S3OnH3Zorn σ p.1.2),
          S3OnH3Zorn σ p.2)
      continuous_toFun := by
        have h₁ : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
            S3OnH3Zorn σ p.1.1) :=
          (continuous_S3OnH3Zorn σ).comp (continuous_fst.comp continuous_fst)
        have h₂ : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
            S3OnH3Zorn σ p.1.2) :=
          (continuous_S3OnH3Zorn σ).comp (continuous_snd.comp continuous_fst)
        have h₃ : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
            S3OnH3Zorn σ p.2) :=
          (continuous_S3OnH3Zorn σ).comp continuous_snd
        exact (h₁.prodMk h₂).prodMk h₃ }

@[simp] theorem S3OnH3ZornTripleTopCat_apply
    (σ : S3Perm) (p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) :
    S3OnH3ZornTripleTopCat σ p =
      ((S3OnH3Zorn σ p.1.1, S3OnH3Zorn σ p.1.2),
        S3OnH3Zorn σ p.2) :=
  rfl

theorem S3OnH3ZornTripleTopCat_comp_T (σ : S3Perm) :
    S3OnH3ZornTripleTopCat σ ≫ h3ZornTTopCat =
      h3ZornTTopCat ≫ s3OnH3ZornReadoutTopCat σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app, TopCat.comp_app]
  simpa [S3OnH3ZornTripleTopCat, h3ZornTTopCat,
    s3OnH3ZornReadoutTopCat] using
      (S3OnH3Zorn_preserve_T σ p.1.1 p.1.2 p.2).symm

theorem S3OnH3Zorn_preserve_U (σ : S3Perm)
    (X Y : H3Zorn ℝ) :
    S3OnH3Zorn σ (H3Zorn.U X Y) =
      H3Zorn.U (S3OnH3Zorn σ X) (S3OnH3Zorn σ Y) := by
  rcases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rw [H3Zorn.U, H3Zorn.U, S3OnH3Zorn_sub, S3OnH3Zorn_smul,
      s12_preserve_h3zorn_crossProduct (X.adjointQuad) Y,
      ← s12_preserve_h3zorn_adjointQuad X,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s12 X Y]
  · rw [H3Zorn.U, H3Zorn.U, S3OnH3Zorn_sub, S3OnH3Zorn_smul,
      s23_preserve_h3zorn_crossProduct (X.adjointQuad) Y,
      ← s23_preserve_h3zorn_adjointQuad X,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s23 X Y]
  · rw [H3Zorn.U, H3Zorn.U, S3OnH3Zorn_sub, S3OnH3Zorn_smul,
      s31_preserve_h3zorn_crossProduct (X.adjointQuad) Y,
      ← s31_preserve_h3zorn_adjointQuad X,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s31 X Y]
  · rw [H3Zorn.U, H3Zorn.U, S3OnH3Zorn_sub, S3OnH3Zorn_smul,
      s12_s23_preserve_h3zorn_crossProduct (X.adjointQuad) Y,
      ← s12_s23_preserve_h3zorn_adjointQuad X,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s12_s23 X Y]
  · rw [H3Zorn.U, H3Zorn.U, S3OnH3Zorn_sub, S3OnH3Zorn_smul,
      s23_s12_preserve_h3zorn_crossProduct (X.adjointQuad) Y,
      ← s23_s12_preserve_h3zorn_adjointQuad X,
      S3OnH3Zorn_preserve_traceBilin S3Perm.s23_s12 X Y]

theorem S3OnH3ZornPairTopCat_comp_U (σ : S3Perm) :
    S3OnH3ZornPairTopCat σ ≫ h3ZornUTopCat =
      h3ZornUTopCat ≫ s3OnH3ZornReadoutTopCat σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app, TopCat.comp_app]
  simpa [S3OnH3ZornPairTopCat, h3ZornUTopCat,
    s3OnH3ZornReadoutTopCat] using
      (S3OnH3Zorn_preserve_U σ p.1 p.2).symm

noncomputable def S3ConjugateEnd (σ : S3Perm)
    (D : Module.End ℝ (H3Zorn ℝ)) : Module.End ℝ (H3Zorn ℝ) :=
  (S3OnH3ZornLinearMap σ).comp
    (D.comp (S3OnH3ZornLinearMap (S3Perm.inverse σ)))

@[simp] theorem S3ConjugateEnd_apply (σ : S3Perm)
    (D : Module.End ℝ (H3Zorn ℝ)) (X : H3Zorn ℝ) :
    S3ConjugateEnd σ D X =
      S3OnH3Zorn σ (D (S3OnH3Zorn (S3Perm.inverse σ) X)) := rfl

theorem S3ConjugateEnd_preserves_JordanDerivation
    (σ : S3Perm) (D : Module.End ℝ (H3Zorn ℝ))
    (hD : H3ZornJordanDerivation D) :
    H3ZornJordanDerivation (S3ConjugateEnd σ D) := by
  intro X Y
  rw [S3ConjugateEnd_apply, S3ConjugateEnd_apply,
    S3ConjugateEnd_apply]
  rw [S3OnH3Zorn_preserve_candidateJordanMul (S3Perm.inverse σ) X Y]
  rw [hD]
  rw [S3OnH3Zorn_add,
    S3OnH3Zorn_preserve_candidateJordanMul,
    S3OnH3Zorn_preserve_candidateJordanMul,
    S3OnH3Zorn_inverse_right, S3OnH3Zorn_inverse_right]

theorem S3ConjugateEnd_mem_H3ZornF4Derivations
    (σ : S3Perm) (D : Module.End ℝ (H3Zorn ℝ))
    (hD : D ∈ H3ZornF4Derivations) :
    S3ConjugateEnd σ D ∈ H3ZornF4Derivations := by
  change H3ZornJordanDerivation (S3ConjugateEnd σ D)
  exact S3ConjugateEnd_preserves_JordanDerivation σ D hD

theorem S3ConjugateEnd_comp_closure (σ τ : S3Perm)
    (D : Module.End ℝ (H3Zorn ℝ)) :
    ∃ ρ : S3Perm,
      S3ConjugateEnd τ (S3ConjugateEnd σ D) =
        S3ConjugateEnd ρ D := by
  rcases S3OnH3ZornLinearMap_comp_closure σ τ with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  apply LinearMap.ext
  intro X
  have hinv (Z : H3Zorn ℝ) :
      S3OnH3Zorn (S3Perm.inverse ρ) Z =
        S3OnH3Zorn (S3Perm.inverse σ)
          (S3OnH3Zorn (S3Perm.inverse τ) Z) := by
    have hZ : S3OnH3Zorn ρ
        (S3OnH3Zorn (S3Perm.inverse σ)
          (S3OnH3Zorn (S3Perm.inverse τ) Z)) = Z := by
      change S3OnH3ZornLinearMap ρ
          (S3OnH3Zorn (S3Perm.inverse σ)
            (S3OnH3Zorn (S3Perm.inverse τ) Z)) = Z
      rw [hρ]
      change S3OnH3Zorn τ
          (S3OnH3Zorn σ
            (S3OnH3Zorn (S3Perm.inverse σ)
              (S3OnH3Zorn (S3Perm.inverse τ) Z))) = Z
      rw [S3OnH3Zorn_inverse_right, S3OnH3Zorn_inverse_right]
    have hZ' := congrArg (S3OnH3Zorn (S3Perm.inverse ρ)) hZ
    simpa only [S3OnH3Zorn_inverse_left] using hZ'.symm
  rw [S3ConjugateEnd_apply, S3ConjugateEnd_apply,
    S3ConjugateEnd_apply]
  change S3OnH3Zorn τ
      (S3OnH3Zorn σ
        (D (S3OnH3Zorn (S3Perm.inverse σ)
          (S3OnH3Zorn (S3Perm.inverse τ) X)))) =
    S3OnH3ZornLinearMap ρ
      (D (S3OnH3Zorn (S3Perm.inverse ρ) X))
  rw [hρ]
  simp only [LinearMap.comp_apply, S3OnH3ZornLinearMap_apply]
  rw [hinv X]

theorem S3ConjugateInnerDerivation_mem_H3ZornF4Derivations
    (σ : S3Perm) (a b : H3Zorn ℝ) :
    S3ConjugateEnd σ
        (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) ∈
      H3ZornF4Derivations := by
  apply S3ConjugateEnd_mem_H3ZornF4Derivations
  exact h3ZornJordanInnerDerivation_mem_F4 a b

theorem continuous_S3ConjugateInnerDerivation_action
    (σ : S3Perm) (a b : H3Zorn ℝ) :
    Continuous (fun x : H3Zorn ℝ =>
      S3OnH3Zorn σ
        (a * (b * (S3OnH3Zorn (S3Perm.inverse σ) x)) -
          b * (a * (S3OnH3Zorn (S3Perm.inverse σ) x)))) := by
  have hinv : Continuous (S3OnH3Zorn (S3Perm.inverse σ)) :=
    continuous_S3OnH3Zorn (S3Perm.inverse σ)
  have hconst_a : Continuous (fun _ : H3Zorn ℝ => a) := continuous_const
  have hconst_b : Continuous (fun _ : H3Zorn ℝ => b) := continuous_const
  have hbx : Continuous (fun x : H3Zorn ℝ =>
      b * S3OnH3Zorn (S3Perm.inverse σ) x) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_candidateJordanMul.comp
        (hconst_b.prodMk hinv)
  have hax : Continuous (fun x : H3Zorn ℝ =>
      a * S3OnH3Zorn (S3Perm.inverse σ) x) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_candidateJordanMul.comp
        (hconst_a.prodMk hinv)
  have hab : Continuous (fun x : H3Zorn ℝ =>
      a * (b * S3OnH3Zorn (S3Perm.inverse σ) x)) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_candidateJordanMul.comp
        (hconst_a.prodMk hbx)
  have hba : Continuous (fun x : H3Zorn ℝ =>
      b * (a * S3OnH3Zorn (S3Perm.inverse σ) x)) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_candidateJordanMul.comp
        (hconst_b.prodMk hax)
  exact (continuous_S3OnH3Zorn σ).comp (hab.sub hba)

noncomputable def S3ConjugateInnerDerivationJoint (σ : S3Perm)
    (p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) : H3Zorn ℝ :=
  S3OnH3Zorn σ
    (p.1.1 * (p.1.2 * (S3OnH3Zorn (S3Perm.inverse σ) p.2)) -
      p.1.2 * (p.1.1 * (S3OnH3Zorn (S3Perm.inverse σ) p.2)))

theorem continuous_S3ConjugateInnerDerivation_joint (σ : S3Perm) :
    Continuous (S3ConjugateInnerDerivationJoint σ) := by
  have hinv : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
      S3OnH3Zorn (S3Perm.inverse σ) p.2) :=
    (continuous_S3OnH3Zorn (S3Perm.inverse σ)).comp continuous_snd
  have ha : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
      p.1.1) := continuous_fst.comp continuous_fst
  have hb : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
      p.1.2) := continuous_snd.comp continuous_fst
  have hbx : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
      p.1.2 * S3OnH3Zorn (S3Perm.inverse σ) p.2) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_candidateJordanMul.comp (hb.prodMk hinv)
  have hax : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
      p.1.1 * S3OnH3Zorn (S3Perm.inverse σ) p.2) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_candidateJordanMul.comp (ha.prodMk hinv)
  have hab : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
      p.1.1 * (p.1.2 * S3OnH3Zorn (S3Perm.inverse σ) p.2)) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_candidateJordanMul.comp (ha.prodMk hbx)
  have hba : Continuous (fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
      p.1.2 * (p.1.1 * S3OnH3Zorn (S3Perm.inverse σ) p.2)) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_candidateJordanMul.comp (hb.prodMk hax)
  exact (continuous_S3OnH3Zorn σ).comp (hab.sub hba)

noncomputable def S3ConjugateInnerDerivationJointContinuousMap
    (σ : S3Perm) :
    C((H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ, H3Zorn ℝ) :=
  ⟨S3ConjugateInnerDerivationJoint σ,
    continuous_S3ConjugateInnerDerivation_joint σ⟩

@[simp] theorem S3ConjugateInnerDerivationJointContinuousMap_apply
    (σ : S3Perm) (p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) :
    S3ConjugateInnerDerivationJointContinuousMap σ p =
      S3ConjugateInnerDerivationJoint σ p :=
  rfl

noncomputable def S3ConjugateInnerDerivationJointTopCat (σ : S3Perm) :
    TopCat.of ((H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) ⟶
      TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom (S3ConjugateInnerDerivationJointContinuousMap σ)

@[simp] theorem S3ConjugateInnerDerivationJointTopCat_apply
    (σ : S3Perm) (p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) :
    S3ConjugateInnerDerivationJointTopCat σ p =
      S3ConjugateInnerDerivationJoint σ p :=
  rfl

noncomputable def S3ConjugateInnerDerivationContinuousMap
    (σ : S3Perm) (a b : H3Zorn ℝ) :
    C(H3Zorn ℝ, H3Zorn ℝ) :=
  ContinuousMap.mk
    (fun x : H3Zorn ℝ =>
      S3OnH3Zorn σ
        (a * (b * (S3OnH3Zorn (S3Perm.inverse σ) x)) -
          b * (a * (S3OnH3Zorn (S3Perm.inverse σ) x))))
    (continuous_S3ConjugateInnerDerivation_action σ a b)

@[simp] theorem S3ConjugateInnerDerivationContinuousMap_apply
    (σ : S3Perm) (a b x : H3Zorn ℝ) :
    S3ConjugateInnerDerivationContinuousMap σ a b x =
      S3ConjugateEnd σ
        (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) x := by
  change S3OnH3Zorn σ
      (a * (b * (S3OnH3Zorn (S3Perm.inverse σ) x)) -
        b * (a * (S3OnH3Zorn (S3Perm.inverse σ) x))) = _
  rw [S3ConjugateEnd_apply, h3ZornJordanInnerDerivation_apply]

noncomputable def S3ConjugateInnerDerivationTopCat
    (σ : S3Perm) (a b : H3Zorn ℝ) :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom (S3ConjugateInnerDerivationContinuousMap σ a b)

@[simp] theorem S3ConjugateInnerDerivationTopCat_apply
    (σ : S3Perm) (a b x : H3Zorn ℝ) :
    S3ConjugateInnerDerivationTopCat σ a b x =
    S3ConjugateEnd σ
        (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) x := by
  exact S3ConjugateInnerDerivationContinuousMap_apply σ a b x

noncomputable def S3JordanProductResidual (σ : S3Perm)
    (p : H3Zorn ℝ × H3Zorn ℝ) : H3Zorn ℝ :=
  S3OnH3Zorn σ (p.1 * p.2) -
    S3OnH3Zorn σ p.1 * S3OnH3Zorn σ p.2

noncomputable def S3UResidual (σ : S3Perm)
    (p : H3Zorn ℝ × H3Zorn ℝ) : H3Zorn ℝ :=
  S3OnH3Zorn σ (H3Zorn.U p.1 p.2) -
    H3Zorn.U (S3OnH3Zorn σ p.1) (S3OnH3Zorn σ p.2)

theorem S3UResidual_eq_zero (σ : S3Perm)
    (X Y : H3Zorn ℝ) :
    S3UResidual σ (X, Y) = 0 := by
  unfold S3UResidual
  rw [S3OnH3Zorn_preserve_U]
  exact sub_self _

theorem continuous_S3UResidual (σ : S3Perm) :
    Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ => S3UResidual σ p) := by
  have hleft : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      S3OnH3Zorn σ (H3Zorn.U p.1 p.2)) :=
    (continuous_S3OnH3Zorn σ).comp continuous_h3Zorn_U
  have hpair : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      (S3OnH3Zorn σ p.1, S3OnH3Zorn σ p.2)) := by
    exact ((continuous_S3OnH3Zorn σ).comp continuous_fst).prodMk
      ((continuous_S3OnH3Zorn σ).comp continuous_snd)
  have hright : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      H3Zorn.U (S3OnH3Zorn σ p.1) (S3OnH3Zorn σ p.2)) := by
    simpa only [Function.comp_apply] using continuous_h3Zorn_U.comp hpair
  exact hleft.sub hright

noncomputable def S3UResidualContinuousMap (σ : S3Perm) :
    C(H3Zorn ℝ × H3Zorn ℝ, H3Zorn ℝ) :=
  ⟨S3UResidual σ, continuous_S3UResidual σ⟩

noncomputable def S3UResidualTopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ × H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom (S3UResidualContinuousMap σ)

@[simp] theorem S3UResidualContinuousMap_apply
    (σ : S3Perm) (p : H3Zorn ℝ × H3Zorn ℝ) :
    S3UResidualContinuousMap σ p = S3UResidual σ p :=
  rfl

theorem S3UResidualContinuousMap_eq_zero (σ : S3Perm) :
    S3UResidualContinuousMap σ = 0 := by
  apply ContinuousMap.ext
  intro p
  change S3UResidual σ p = 0
  exact S3UResidual_eq_zero σ p.1 p.2

theorem S3UResidualTopCat_eq_zeroMap (σ : S3Perm) :
    S3UResidualTopCat σ =
      TopCat.ofHom (0 : C(H3Zorn ℝ × H3Zorn ℝ, H3Zorn ℝ)) := by
  apply TopCat.hom_ext
  exact S3UResidualContinuousMap_eq_zero σ

theorem S3CrossProductResidual_s23_eq_zero (p : H3Zorn ℝ × H3Zorn ℝ) :
    S3CrossProductResidual S3Perm.s23 p = 0 := by
  unfold S3CrossProductResidual
  rw [s23_preserve_h3zorn_crossProduct]
  exact sub_self _

theorem S3CrossProductResidual_s31_eq_zero (p : H3Zorn ℝ × H3Zorn ℝ) :
    S3CrossProductResidual S3Perm.s31 p = 0 := by
  unfold S3CrossProductResidual
  rw [s31_preserve_h3zorn_crossProduct]
  exact sub_self _

theorem S3CrossProductResidual_s12_s23_eq_zero
    (p : H3Zorn ℝ × H3Zorn ℝ) :
    S3CrossProductResidual S3Perm.s12_s23 p = 0 := by
  unfold S3CrossProductResidual
  rw [s12_s23_preserve_h3zorn_crossProduct]
  exact sub_self _

theorem S3CrossProductResidual_s23_s12_eq_zero
    (p : H3Zorn ℝ × H3Zorn ℝ) :
    S3CrossProductResidual S3Perm.s23_s12 p = 0 := by
  unfold S3CrossProductResidual
  rw [s23_s12_preserve_h3zorn_crossProduct]
  exact sub_self _

theorem S3AdjointResidual_s12_eq_zero (X : H3Zorn ℝ) :
    S3AdjointResidual S3Perm.s12 X = 0 := by
  unfold S3AdjointResidual
  rw [s12_preserve_h3zorn_adjointQuad]
  exact sub_self _

theorem S3AdjointResidual_s23_eq_zero (X : H3Zorn ℝ) :
    S3AdjointResidual S3Perm.s23 X = 0 := by
  unfold S3AdjointResidual
  rw [s23_preserve_h3zorn_adjointQuad]
  exact sub_self _

theorem S3AdjointResidual_s31_eq_zero (X : H3Zorn ℝ) :
    S3AdjointResidual S3Perm.s31 X = 0 := by
  unfold S3AdjointResidual
  rw [s31_preserve_h3zorn_adjointQuad]
  exact sub_self _

theorem S3AdjointResidual_s12_s23_eq_zero (X : H3Zorn ℝ) :
    S3AdjointResidual S3Perm.s12_s23 X = 0 := by
  unfold S3AdjointResidual
  rw [s12_s23_preserve_h3zorn_adjointQuad]
  exact sub_self _

theorem S3AdjointResidual_s23_s12_eq_zero (X : H3Zorn ℝ) :
    S3AdjointResidual S3Perm.s23_s12 X = 0 := by
  unfold S3AdjointResidual
  rw [s23_s12_preserve_h3zorn_adjointQuad]
  exact sub_self _

theorem continuous_S3AdjointResidual (σ : S3Perm) :
    Continuous (S3AdjointResidual σ) := by
  have hleft : Continuous (fun X : H3Zorn ℝ =>
      S3OnH3Zorn σ X.adjointQuad) :=
    (continuous_S3OnH3Zorn σ).comp continuous_h3Zorn_adjointQuad
  have hright : Continuous (fun X : H3Zorn ℝ =>
      (S3OnH3Zorn σ X).adjointQuad) := by
    simpa only [Function.comp_apply] using
      continuous_h3Zorn_adjointQuad.comp (continuous_S3OnH3Zorn σ)
  exact hleft.sub hright

noncomputable def S3AdjointResidualContinuousMap (σ : S3Perm) :
    C(H3Zorn ℝ, H3Zorn ℝ) :=
  ⟨S3AdjointResidual σ, continuous_S3AdjointResidual σ⟩

noncomputable def S3AdjointResidualTopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom (S3AdjointResidualContinuousMap σ)

@[simp] theorem S3AdjointResidualContinuousMap_apply
    (σ : S3Perm) (X : H3Zorn ℝ) :
    S3AdjointResidualContinuousMap σ X = S3AdjointResidual σ X := rfl

theorem S3JordanProductResidual_eq_zero_iff (σ : S3Perm)
    (X Y : H3Zorn ℝ) :
    S3JordanProductResidual σ (X, Y) = 0 ↔
      S3OnH3Zorn σ (X * Y) =
        S3OnH3Zorn σ X * S3OnH3Zorn σ Y := by
  change
    (S3OnH3Zorn σ (X * Y) -
        S3OnH3Zorn σ X * S3OnH3Zorn σ Y) = 0 ↔ _
  exact sub_eq_zero

theorem S3JordanProductResidual_eq_zero (σ : S3Perm)
    (X Y : H3Zorn ℝ) :
    S3JordanProductResidual σ (X, Y) = 0 := by
  unfold S3JordanProductResidual
  rw [S3OnH3Zorn_preserve_candidateJordanMul]
  exact sub_self _

theorem continuous_S3JordanProductResidual (σ : S3Perm) :
    Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      S3JordanProductResidual σ p) := by
  have hleft : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      S3OnH3Zorn σ (p.1 * p.2)) :=
    (continuous_S3OnH3Zorn σ).comp continuous_h3Zorn_candidateJordanMul
  have hpair : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      (S3OnH3Zorn σ p.1, S3OnH3Zorn σ p.2)) := by
    exact ((continuous_S3OnH3Zorn σ).comp continuous_fst).prodMk
      ((continuous_S3OnH3Zorn σ).comp continuous_snd)
  have hright : Continuous (fun p : H3Zorn ℝ × H3Zorn ℝ =>
      S3OnH3Zorn σ p.1 * S3OnH3Zorn σ p.2) :=
    by
      simpa only [Function.comp_apply] using
        continuous_h3Zorn_candidateJordanMul.comp hpair
  exact hleft.sub hright

noncomputable def S3JordanProductResidualContinuousMap (σ : S3Perm) :
    C(H3Zorn ℝ × H3Zorn ℝ, H3Zorn ℝ) :=
  ⟨S3JordanProductResidual σ, continuous_S3JordanProductResidual σ⟩

noncomputable def S3JordanProductResidualTopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ × H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom (S3JordanProductResidualContinuousMap σ)

@[simp] theorem S3JordanProductResidualContinuousMap_apply
    (σ : S3Perm) (p : H3Zorn ℝ × H3Zorn ℝ) :
    S3JordanProductResidualContinuousMap σ p =
      S3JordanProductResidual σ p := rfl

theorem S3JordanProductResidualContinuousMap_eq_zero (σ : S3Perm) :
    S3JordanProductResidualContinuousMap σ = 0 := by
  apply ContinuousMap.ext
  intro p
  change S3JordanProductResidual σ p = 0
  exact S3JordanProductResidual_eq_zero σ p.1 p.2

theorem S3JordanProductResidualTopCat_eq_zeroMap (σ : S3Perm) :
    S3JordanProductResidualTopCat σ =
      TopCat.ofHom (0 : C(H3Zorn ℝ × H3Zorn ℝ, H3Zorn ℝ)) := by
  apply TopCat.hom_ext
  exact S3JordanProductResidualContinuousMap_eq_zero σ

end InfoGeometry.Canonical
