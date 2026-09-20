import InfoGeometry.HodgeCohomology.TwistedCubic

namespace InfoGeometry.HodgeCohomology.TwistedCubicTests

open TwistedCubic

example : parameter (1 : ℚ) 2 = ![1, 2, 4, 8] := by
  norm_num [parameter]

example : OnCurve (![1, 2, 4, 8] : Fin 4 → ℚ) := by
  norm_num [OnCurve]

example : OnCurve ((-3 : ℚ) • parameter 1 2) :=
  onCurve_smul _ _ (parameter_onCurve _ _)

example : (quadric (Scalar := ℂ) 0 2 1 1).IsHomogeneous 2 :=
  quadric_homogeneous _ _ _ _

theorem residual_line_has_point_outside_curve :
    ∃ point : Fin 4 → ℚ,
      point ≠ 0 ∧ point 0 = 0 ∧ point 1 = 0 ∧ ¬ OnCurve point := by
  refine ⟨![0, 0, 1, 0], ?_, by norm_num, by norm_num, ?_⟩
  · intro equality
    have entry := congrArg (fun point : Fin 4 → ℚ => point 2) equality
    norm_num at entry
  · norm_num [OnCurve]

example : OnCurve (parameter (0 : ℚ) 1) ∧
    parameter (0 : ℚ) 1 0 = 0 ∧ parameter (0 : ℚ) 1 1 = 0 := by
  exact ⟨parameter_onCurve 0 1, by norm_num [parameter], by norm_num [parameter]⟩

example : OnCurve (parameter (1 : ℚ) 2) ↔
    ∃ first second : ℚ, ∃ nonzero : parameter first second ≠ 0,
      Projectivization.mk ℚ (parameter 1 2)
        (parameter_nonzero 1 2 (Or.inl one_ne_zero)) =
      Projectivization.mk ℚ (parameter first second) nonzero :=
  onCurve_iff_projective_parameterized _ _

#print axioms quadric_homogeneous
#print axioms onCurve_iff_quadrics
#print axioms parameter_onCurve
#print axioms parameter_nonzero
#print axioms parameter_scale
#print axioms scaled_relation
#print axioms onCurve_smul
#print axioms onCurve_smul_iff
#print axioms zero_patch
#print axioms nonzero_patch
#print axioms projective_parameterization
#print axioms onCurve_iff_projective_parameterized
#print axioms two_quadrics_decompose
#print axioms residual_line_has_point_outside_curve

end InfoGeometry.HodgeCohomology.TwistedCubicTests
