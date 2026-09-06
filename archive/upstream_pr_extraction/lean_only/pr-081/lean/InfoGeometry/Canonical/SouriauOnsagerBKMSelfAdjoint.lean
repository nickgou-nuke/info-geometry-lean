import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability

noncomputable section

namespace SouriauOnsagerBKM

variable {n : ℕ}

/-- The adjoint on the finite operator algebra, bundled once as a real
continuous-linear map.  Using the real scalar field is essential: operator
adjunction is conjugate-linear over `ℂ`, but linear over `ℝ`. -/
noncomputable def finiteOperatorStarRealCLM (n : ℕ) :
    FiniteOperatorAlgebra n →L[ℝ] FiniteOperatorAlgebra n :=
  (starL' ℝ :
    FiniteOperatorAlgebra n ≃L[ℝ] FiniteOperatorAlgebra n).toContinuousLinearMap

@[simp] theorem finiteOperatorStarRealCLM_apply
    (A : FiniteOperatorAlgebra n) :
    finiteOperatorStarRealCLM n A = star A :=
  rfl

/-- Taking the adjoint reflects the Kubo--Mori modular interpolation parameter
`s ↦ 1 - s` whenever the inserted operator is self-adjoint.  The pointwise
interpolation itself is not asserted to be self-adjoint. -/
theorem FaithfulDensityOperator.modularInterpolation_star_reflection
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (hA : star A = A)
    (s : ℝ) :
    star (D.modularInterpolation s A) =
      D.modularInterpolation (1 - s) A := by
  simp [FaithfulDensityOperator.modularInterpolation, hA]

/-- Reflection of an operator-valued interval integral across the midpoint of
`[0,1]`.  This is a direct specialization of Mathlib's affine
change-of-variable formula and contains no star operation. -/
theorem intervalIntegral_one_sub_eq
    (f : ℝ → FiniteOperatorAlgebra n) :
    (∫ s in (0 : ℝ)..1, f (1 - s)) =
      ∫ s in (0 : ℝ)..1, f s := by
  simpa using
    (intervalIntegral.integral_comp_sub_left
      (f := f) (a := (0 : ℝ)) (b := 1) 1)

/-- Adjunction commutes with an operator-valued interval integral whenever the
integrand is interval-integrable.  All continuous-linear-map data are supplied
explicitly to keep typeclass/elaboration search local. -/
theorem star_intervalIntegral
    (f : ℝ → FiniteOperatorAlgebra n)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) :
    star (∫ s in (0 : ℝ)..1, f s) =
      ∫ s in (0 : ℝ)..1, star (f s) := by
  change
    finiteOperatorStarRealCLM n (∫ s in (0 : ℝ)..1, f s) =
      ∫ s in (0 : ℝ)..1, finiteOperatorStarRealCLM n (f s)
  symm
  exact
    ContinuousLinearMap.intervalIntegral_comp_comm
      (finiteOperatorStarRealCLM n) hf

/-- The full noncommutative Kubo--Mori transform preserves self-adjointness.

Pointwise modular interpolation need not be self-adjoint. Its adjoint is the
reflected integrand at `1-s`; interval reflection restores equality only after
integration. -/
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

end SouriauOnsagerBKM
