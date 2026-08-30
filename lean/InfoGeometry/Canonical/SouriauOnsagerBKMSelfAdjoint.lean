import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability

noncomputable section

namespace SouriauOnsagerBKM

variable {n : ℕ}

/-- Taking the adjoint reflects the Kubo--Mori modular interpolation parameter
` s ↦ 1 - s ` whenever the inserted operator is self-adjoint. -/
theorem FaithfulDensityOperator.modularInterpolation_star_reflection
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (hA : star A = A)
    (s : ℝ) :
    star (D.modularInterpolation s A) =
      D.modularInterpolation (1 - s) A := by
  simp [FaithfulDensityOperator.modularInterpolation, hA]

/-- Reflection of an operator-valued interval integral across the midpoint of
`[0,1]`. This is a direct specialization of Mathlib's affine change-of-variable
formula. -/
theorem intervalIntegral_one_sub_eq
    (f : ℝ → FiniteOperatorAlgebra n) :
    (∫ s in (0 : ℝ)..1, f (1 - s)) =
      ∫ s in (0 : ℝ)..1, f s := by
  simpa using
    (intervalIntegral.integral_comp_sub_left
      (f := f) (a := (0 : ℝ)) (b := 1) 1)

/-- The full noncommutative Kubo--Mori transform preserves self-adjointness.

Pointwise modular interpolation need not be self-adjoint. Its adjoint is the
reflected integrand at `1-s`, and the interval reflection restores equality
after integration. -/
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
  calc
    star (∫ s in (0 : ℝ)..1, D.modularInterpolation s A) =
        (starL' ℝ :
          FiniteOperatorAlgebra n ≃L[ℝ] FiniteOperatorAlgebra n)
          (∫ s in (0 : ℝ)..1, D.modularInterpolation s A) := by
            rfl
    _ = ∫ s in (0 : ℝ)..1,
          (starL' ℝ :
            FiniteOperatorAlgebra n ≃L[ℝ] FiniteOperatorAlgebra n)
            (D.modularInterpolation s A) := by
          symm
          exact ContinuousLinearMap.intervalIntegral_comp_comm
            (starL' ℝ :
              FiniteOperatorAlgebra n ≃L[ℝ] FiniteOperatorAlgebra n).toContinuousLinearMap
            h_integrable
    _ = ∫ s in (0 : ℝ)..1, D.modularInterpolation (1 - s) A := by
          apply intervalIntegral.integral_congr
          intro s hs
          simpa using D.modularInterpolation_star_reflection A hA s
    _ = ∫ s in (0 : ℝ)..1, D.modularInterpolation s A :=
          intervalIntegral_one_sub_eq _

end SouriauOnsagerBKM
