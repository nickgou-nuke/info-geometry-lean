import InfoGeometry.Canonical.SouriauOnsagerBKMEquiv

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace SouriauOnsagerBKM

variable {n : ℕ}

noncomputable def finiteOperatorStarRealCLM (n : ℕ) :
    FiniteOperatorAlgebra n →L[ℝ] FiniteOperatorAlgebra n :=
  (starL' ℝ :
    FiniteOperatorAlgebra n ≃L[ℝ] FiniteOperatorAlgebra n).toContinuousLinearMap

@[simp] theorem finiteOperatorStarRealCLM_apply
    (A : FiniteOperatorAlgebra n) :
    finiteOperatorStarRealCLM n A = star A :=
  rfl

theorem FaithfulDensityOperator.modularInterpolation_star_reflection
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (hA : star A = A)
    (s : ℝ) :
    star (D.modularInterpolation s A) =
      D.modularInterpolation (1 - s) A := by
  simp [FaithfulDensityOperator.modularInterpolation, hA, mul_assoc]

theorem FaithfulDensityOperator.modularInterpolation_star
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (s : ℝ) :
    star (D.modularInterpolation s A) =
      D.modularInterpolation (1 - s) (star A) := by
  simp [FaithfulDensityOperator.modularInterpolation, mul_assoc]

theorem intervalIntegral_one_sub_eq
    (f : ℝ → FiniteOperatorAlgebra n) :
    (∫ s in (0 : ℝ)..1, f (1 - s)) =
      ∫ s in (0 : ℝ)..1, f s := by
  simpa only [sub_self, sub_zero] using
    (intervalIntegral.integral_comp_sub_left
      (f := f) (a := (0 : ℝ)) (b := 1) 1)

theorem star_intervalIntegral
    (f : ℝ → FiniteOperatorAlgebra n)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) :
    star (∫ s in (0 : ℝ)..1, f s) =
      ∫ s in (0 : ℝ)..1, star (f s) := by
  letI : NormedSpace ℝ (FiniteOperatorAlgebra n) :=
    NormedSpace.restrictScalars ℝ ℂ (FiniteOperatorAlgebra n)
  change
    finiteOperatorStarRealCLM n (∫ s in (0 : ℝ)..1, f s) =
      ∫ s in (0 : ℝ)..1, finiteOperatorStarRealCLM n (f s)
  symm
  exact
    ContinuousLinearMap.intervalIntegral_comp_comm
      (finiteOperatorStarRealCLM n) hf

theorem FaithfulDensityOperator.kuboMoriTransform_preserves_selfAdjoint
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n)
    (hA : star A = A) :
    star (D.kuboMoriTransform A) = D.kuboMoriTransform A := by
  have h_integrable :
      IntervalIntegrable
        (fun s : ℝ => D.modularInterpolation s A)
        MeasureTheory.volume 0 1 :=
    D.intervalIntegrable_modularInterpolation_of_continuous_rpow A h_rpow
  unfold FaithfulDensityOperator.kuboMoriTransform
  rw [star_intervalIntegral
    (f := fun s : ℝ => D.modularInterpolation s A) h_integrable]
  have hreflect :
      (∫ s in (0 : ℝ)..1, star (D.modularInterpolation s A)) =
        ∫ s in (0 : ℝ)..1, D.modularInterpolation (1 - s) A := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact D.modularInterpolation_star_reflection A hA s
  rw [hreflect]
  exact intervalIntegral_one_sub_eq
    (fun s : ℝ => D.modularInterpolation s A)

theorem FaithfulDensityOperator.kuboMoriTransform_star
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n) :
    star (D.kuboMoriTransform A) =
      D.kuboMoriTransform (star A) := by
  have h_integrable :
      IntervalIntegrable
        (fun s : ℝ => D.modularInterpolation s A)
        MeasureTheory.volume 0 1 :=
    D.intervalIntegrable_modularInterpolation_of_continuous_rpow A h_rpow
  unfold FaithfulDensityOperator.kuboMoriTransform
  rw [star_intervalIntegral
    (f := fun s : ℝ => D.modularInterpolation s A) h_integrable]
  have hreflect :
      (∫ s in (0 : ℝ)..1, star (D.modularInterpolation s A)) =
        ∫ s in (0 : ℝ)..1, D.modularInterpolation (1 - s) (star A) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact D.modularInterpolation_star A s
  rw [hreflect]
  exact intervalIntegral_one_sub_eq
    (fun s : ℝ => D.modularInterpolation s (star A))

theorem FaithfulDensityOperator.inverseKuboMoriCLM_preserves_selfAdjoint
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n)
    (hA : star A = A) :
    star (D.inverseKuboMoriCLM h_rpow A) =
      D.inverseKuboMoriCLM h_rpow A := by
  apply D.kuboMoriTransformCLM_injective h_rpow
  simpa [D.kuboMoriTransformCLM_apply] using
    (calc
      D.kuboMoriTransform (star (D.inverseKuboMoriCLM h_rpow A)) =
          star (D.kuboMoriTransform
            (D.inverseKuboMoriCLM h_rpow A)) := by
            symm
            exact D.kuboMoriTransform_star h_rpow _
      _ = star A := by
        rw [D.transform_apply_inverseKuboMoriCLM h_rpow]
      _ = A := hA
      _ = D.kuboMoriTransform
          (D.inverseKuboMoriCLM h_rpow A) := by
        symm
        exact D.transform_apply_inverseKuboMoriCLM h_rpow A)

noncomputable def FaithfulDensityOperator.restrictedKuboMoriCLM
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    selfAdjoint (FiniteOperatorAlgebra n) →L[ℝ]
      selfAdjoint (FiniteOperatorAlgebra n) :=
  ((ContinuousLinearMap.restrictScalars ℝ
      (D.kuboMoriTransformCLM h_rpow)).comp
      (selfAdjoint.submodule ℝ (FiniteOperatorAlgebra n)).subtypeL).codRestrict
    (selfAdjoint.submodule ℝ (FiniteOperatorAlgebra n))
    (fun A => D.kuboMoriTransform_preserves_selfAdjoint h_rpow
      (A : FiniteOperatorAlgebra n) A.property)

@[simp] theorem restrictedKuboMoriCLM_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    (D.restrictedKuboMoriCLM h_rpow A : FiniteOperatorAlgebra n) =
      D.kuboMoriTransform (A : FiniteOperatorAlgebra n) := by
  rfl

theorem FaithfulDensityOperator.restrictedKuboMoriCLM_injective
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    Function.Injective (D.restrictedKuboMoriCLM h_rpow) := by
  intro A B hAB
  apply Subtype.ext
  apply D.kuboMoriTransformCLM_injective h_rpow
  exact congrArg Subtype.val hAB

noncomputable def FaithfulDensityOperator.restrictedInverseKuboMoriCLM
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    selfAdjoint (FiniteOperatorAlgebra n) →L[ℝ]
      selfAdjoint (FiniteOperatorAlgebra n) :=
  ((ContinuousLinearMap.restrictScalars ℝ
      (D.inverseKuboMoriCLM h_rpow)).comp
      (selfAdjoint.submodule ℝ (FiniteOperatorAlgebra n)).subtypeL).codRestrict
    (selfAdjoint.submodule ℝ (FiniteOperatorAlgebra n))
    (fun A => D.inverseKuboMoriCLM_preserves_selfAdjoint h_rpow
      (A : FiniteOperatorAlgebra n) A.property)

@[simp] theorem restrictedInverseKuboMoriCLM_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    (D.restrictedInverseKuboMoriCLM h_rpow A : FiniteOperatorAlgebra n) =
      D.inverseKuboMoriCLM h_rpow (A : FiniteOperatorAlgebra n) := by
  rfl

theorem FaithfulDensityOperator.restrictedInverseKuboMoriCLM_apply_restricted
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    D.restrictedInverseKuboMoriCLM h_rpow
        (D.restrictedKuboMoriCLM h_rpow A) = A := by
  apply Subtype.ext
  simpa using D.inverseKuboMoriCLM_apply_transform h_rpow (A : FiniteOperatorAlgebra n)

theorem FaithfulDensityOperator.restrictedKuboMoriCLM_apply_restrictedInverse
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    D.restrictedKuboMoriCLM h_rpow
        (D.restrictedInverseKuboMoriCLM h_rpow A) = A := by
  apply Subtype.ext
  simpa using D.transform_apply_inverseKuboMoriCLM h_rpow (A : FiniteOperatorAlgebra n)

theorem FaithfulDensityOperator.restrictedKuboMoriCLM_surjective
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    Function.Surjective (D.restrictedKuboMoriCLM h_rpow) := by
  intro A
  exact ⟨D.restrictedInverseKuboMoriCLM h_rpow A,
    D.restrictedKuboMoriCLM_apply_restrictedInverse h_rpow A⟩

noncomputable def FaithfulDensityOperator.restrictedKuboMoriLE
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    selfAdjoint (FiniteOperatorAlgebra n) ≃ₗ[ℝ]
      selfAdjoint (FiniteOperatorAlgebra n) :=
  LinearEquiv.ofBijective
    (D.restrictedKuboMoriCLM h_rpow).toLinearMap
    ⟨D.restrictedKuboMoriCLM_injective h_rpow,
      D.restrictedKuboMoriCLM_surjective h_rpow⟩

@[simp] theorem FaithfulDensityOperator.restrictedKuboMoriLE_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    D.restrictedKuboMoriLE h_rpow A =
      D.restrictedKuboMoriCLM h_rpow A := by
  rfl

theorem FaithfulDensityOperator.restrictedKuboMoriLE_symm_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : selfAdjoint (FiniteOperatorAlgebra n)) :
    (D.restrictedKuboMoriLE h_rpow).symm A =
      D.restrictedInverseKuboMoriCLM h_rpow A := by
  apply D.restrictedKuboMoriCLM_injective h_rpow
  change (D.restrictedKuboMoriLE h_rpow)
      ((D.restrictedKuboMoriLE h_rpow).symm A) =
    D.restrictedKuboMoriCLM h_rpow
      (D.restrictedInverseKuboMoriCLM h_rpow A)
  rw [(D.restrictedKuboMoriLE h_rpow).apply_symm_apply]
  exact (D.restrictedKuboMoriCLM_apply_restrictedInverse h_rpow A).symm

end SouriauOnsagerBKM
