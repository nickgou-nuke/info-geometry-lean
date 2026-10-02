import InfoGeometry.NumberTheory.SymmetricSpacesRandomMatrix

namespace InfoGeometry.NumberTheory.SymmetricSpacesRandomMatrix

example {L : Type*} [LieRing L] [LieAlgebra ℝ L] (vector : L) :
    ∃! parts : L × L,
      parts.1 ∈ fixedSpace (LieHom.id : L →ₗ⁅ℝ⁆ L) ∧
      parts.2 ∈ negatedSpace (LieHom.id : L →ₗ⁅ℝ⁆ L) ∧
      vector = parts.1 + parts.2 :=
  symmetric_pair_decomposition LieHom.id (fun _ => rfl) vector

example {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (σ : L →ₗ⁅ℝ⁆ L) (first second : L)
    (hfirst : σ first = -first) (hsecond : σ second = -second) :
    ⁅first, second⁆ ∈ fixedSpace σ :=
  (symmetric_pair_grading σ).p_p first second
    ((mem_negatedSpace σ first).mpr hfirst)
    ((mem_negatedSpace σ second).mpr hsecond)

example : azLabelEquiv AZLabel.CI = 9 := rfl

example : Function.Bijective azLabelEquiv := azLabelEquiv.bijective

example : Fintype.card DysonLabel = 3 := dyson_label_count

example : Fintype.card ArithmeticCompactGroupLabel = 4 := arithmetic_label_count

example : ¬ PointwiseSpacingLimit (fun _ _ => 0) (fun _ => 1) := by
  intro hlimit
  have heq := (constant_spacing_limit_iff (fun _ => 0) (fun _ => 1)).mp hlimit
  have hzero := congrFun heq 0
  norm_num at hzero

example (target : ℝ → ℝ) :
    ¬ ∀ empirical : ℝ → ℝ → ℝ, PointwiseSpacingLimit empirical target :=
  no_universal_spacing_limit target

#print axioms symmetric_pair_decomposition
#print axioms symmetric_pair_grading
#print axioms azLabelEquiv
#print axioms spacing_limit_unique
#print axioms no_universal_spacing_limit

example {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (symmetric : InfoGeometry.Core.Generic.SymmetricLieAlgebra ℝ L) (vector : L) :
    (((symmetricPairLinearEquiv symmetric vector).1 : L) +
      (symmetricPairLinearEquiv symmetric vector).2) = vector := by
  exact (symmetricPairLinearEquiv symmetric).symm_apply_apply vector

#print axioms symmetric_pair_isCompl
#print axioms symmetricPairLinearEquiv
#print axioms symmetricPairLinearEquiv_apply

end InfoGeometry.NumberTheory.SymmetricSpacesRandomMatrix
