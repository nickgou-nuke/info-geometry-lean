import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import InfoGeometry.Clifford.Cl55RealSplitPinKernelCenter
import InfoGeometry.Clifford.Cl55WittPinAction
import InfoGeometry.Clifford.Cl55RealSplitPinReflectionImage
import InfoGeometry.Clifford.Cl55RealSplitPinReflectionEvidence

namespace InfoGeometry.Clifford.Clifford55

/-!
# Determinant readout of the corrected real split-Pin action

The determinant is kept as a native group homomorphism.  This records the
orientation character of the orthogonal action without identifying the Pin
kernel or importing a finite matrix model.
-/

noncomputable def realSplitPinOrthogonalDet : realSplitPin55 →* ℝˣ where
  toFun g :=
    LinearEquiv.det
      ((realSplitPinOrthogonalAction g : orthogonalGroup55) :
        V55 ≃ₗ[ℝ] V55)
  map_one' := by
    change LinearEquiv.det
        ((realSplitPinOrthogonalAction (1 : realSplitPin55) : orthogonalGroup55) :
          V55 ≃ₗ[ℝ] V55) = 1
    rw [map_one]
    exact LinearEquiv.det_refl
  map_mul' g h := by
    change LinearEquiv.det
        ((realSplitPinOrthogonalAction (g * h) : orthogonalGroup55) :
          V55 ≃ₗ[ℝ] V55) = _
    rw [map_mul]
    change LinearEquiv.det
        ((realSplitPinOrthogonalAction g : orthogonalGroup55) *
          (realSplitPinOrthogonalAction h : orthogonalGroup55) :
          V55 ≃ₗ[ℝ] V55) = _
    exact LinearEquiv.det.map_mul _ _

theorem realSplitPinOrthogonalDet_apply
    (g : realSplitPin55) :
    realSplitPinOrthogonalDet g =
      LinearEquiv.det
        ((realSplitPinOrthogonalAction g : orthogonalGroup55) :
          V55 ≃ₗ[ℝ] V55) :=
  rfl

theorem realSplitPin_kernel_det_eq_one
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker) :
    realSplitPinOrthogonalDet g = 1 := by
  rw [realSplitPinOrthogonalDet_apply, hg]
  exact LinearEquiv.det_refl

theorem negativeReflectionLinearEquiv_det (i : Fin 5) :
    LinearEquiv.det (negativeReflectionLinearEquiv i) = (-1 : ℝˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  rw [← LinearMap.det_toMatrix ((Pi.basisFun ℝ (Fin 5)).prod
    (Pi.basisFun ℝ (Fin 5)))]
  have hmat :
      LinearMap.toMatrix ((Pi.basisFun ℝ (Fin 5)).prod
        (Pi.basisFun ℝ (Fin 5))) ((Pi.basisFun ℝ (Fin 5)).prod
        (Pi.basisFun ℝ (Fin 5)))
        (negativeReflectionLinearEquiv i : V55 →ₗ[ℝ] V55) =
      Matrix.diagonal (fun k : Fin 5 ⊕ Fin 5 =>
        match k with
        | Sum.inl _ => 1
        | Sum.inr j => if j = i then -1 else 1) := by
    ext a b
    cases a <;> cases b <;>
      simp only [LinearMap.toMatrix_apply,
        Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
        Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Pi.basisFun_repr, Matrix.diagonal_apply_eq] <;>
      simp [negativeReflectionLinearEquiv, negativeReflection]
    all_goals simp [Matrix.diagonal, Pi.single_apply]
    all_goals split <;> simp_all
    all_goals split <;> simp_all
  rw [hmat, Matrix.det_diagonal]
  simp

theorem realSplitPinOrthogonalDet_coordinateReflection (i : Fin 5) :
    ∃ g : realSplitPin55,
      realSplitPinOrthogonalDet g = (-1 : ℝˣ) := by
  rcases realSplitPin_exists_coordinateReflection i with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  rw [realSplitPinOrthogonalDet_apply, hg]
  exact negativeReflectionLinearEquiv_det i

theorem globalSheetReflectionLinearEquiv_det :
    LinearEquiv.det globalSheetReflectionLinearEquiv = (-1 : ℝˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  rw [← LinearMap.det_toMatrix ((Pi.basisFun ℝ (Fin 5)).prod
    (Pi.basisFun ℝ (Fin 5)))]
  have hmat :
      LinearMap.toMatrix ((Pi.basisFun ℝ (Fin 5)).prod
        (Pi.basisFun ℝ (Fin 5))) ((Pi.basisFun ℝ (Fin 5)).prod
        (Pi.basisFun ℝ (Fin 5)))
        (globalSheetReflectionLinearEquiv : V55 →ₗ[ℝ] V55) =
      Matrix.diagonal (fun k : Fin 5 ⊕ Fin 5 =>
        match k with
        | Sum.inl _ => 1
        | Sum.inr _ => -1) := by
    ext a b
    cases a <;> cases b <;>
      simp only [LinearMap.toMatrix_apply,
        Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
        Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Pi.basisFun_repr, Matrix.diagonal_apply_eq] <;>
      simp [globalSheetReflectionLinearEquiv, globalSheetReflection,
        Matrix.diagonal, Pi.single_apply]
    all_goals split <;> simp_all
  rw [hmat, Matrix.det_diagonal]
  norm_num

theorem realSplitPinOrthogonalDet_globalSheet :
    ∃ g : realSplitPin55,
      realSplitPinOrthogonalDet g = (-1 : ℝˣ) := by
  rcases realSplitPinOrthogonalAction_globalSheet with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  rw [realSplitPinOrthogonalDet_apply, hg]
  exact globalSheetReflectionLinearEquiv_det

end InfoGeometry.Clifford.Clifford55
