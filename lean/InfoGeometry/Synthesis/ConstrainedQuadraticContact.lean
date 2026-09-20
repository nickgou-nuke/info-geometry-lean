import InfoGeometry.Synthesis.ImpedanceMatchingDuality

noncomputable section

namespace InfoGeometry.Synthesis.ConstrainedQuadraticContact

open ImpedanceMatchingDuality

def optimalEfficiency (coupling : ℝ) : ℝ :=
  if coupling ≤ 1 / 2 then 1 else 1 / (2 * coupling)

def optimalCapacity (coupling : ℝ) : ℝ :=
  if coupling ≤ 1 / 2 then coupling * (1 - coupling) else 1 / 4

theorem vertex_feasible_iff (coupling : ℝ) (positive : 0 < coupling) :
    1 / (2 * coupling) ∈ Set.Icc (0 : ℝ) 1 ↔ 1 / 2 ≤ coupling := by
  have denominator : 0 < 2 * coupling := by positivity
  constructor
  · intro feasible
    have bound := (div_le_iff₀ denominator).mp feasible.2
    linarith
  · intro bound
    constructor
    · positivity
    · apply (div_le_iff₀ denominator).mpr
      linarith

theorem optimalEfficiency_mem (coupling : ℝ) :
    optimalEfficiency coupling ∈ Set.Icc (0 : ℝ) 1 := by
  unfold optimalEfficiency
  split_ifs with below
  · norm_num
  · exact (vertex_feasible_iff coupling (by linarith)).mpr (by linarith)

theorem capacity_at_optimum (coupling : ℝ) :
    fisher_capacity coupling (optimalEfficiency coupling) = optimalCapacity coupling := by
  unfold optimalEfficiency optimalCapacity
  split_ifs with below
  · rw [capacity_vertex]
    ring
  · exact fisher_capacity_reaches_max coupling (by linarith)

theorem capacity_le_endpoint (coupling efficiency : ℝ)
    (nonnegative : 0 ≤ coupling) (below : coupling ≤ 1 / 2)
    (feasible : efficiency ∈ Set.Icc (0 : ℝ) 1) :
    fisher_capacity coupling efficiency ≤ coupling * (1 - coupling) := by
  have product_le : coupling * efficiency ≤ coupling :=
    mul_le_of_le_one_right nonnegative feasible.2
  have factor_nonnegative : 0 ≤ 1 - coupling - coupling * efficiency := by linarith
  have difference_nonnegative := mul_nonneg (sub_nonneg.mpr product_le) factor_nonnegative
  rw [capacity_vertex]
  nlinarith

theorem capacity_isGreatest_on_unitInterval (coupling : ℝ) (nonnegative : 0 ≤ coupling) :
    IsGreatest (fisher_capacity coupling '' Set.Icc (0 : ℝ) 1)
      (optimalCapacity coupling) := by
  refine ⟨⟨optimalEfficiency coupling, optimalEfficiency_mem coupling,
    capacity_at_optimum coupling⟩, ?_⟩
  rintro value ⟨efficiency, feasible, rfl⟩
  unfold optimalCapacity
  split_ifs with below
  · exact capacity_le_endpoint coupling efficiency nonnegative below feasible
  · exact fisher_capacity_le_max coupling efficiency

def constrainedGap (coupling : ℝ) : ℝ :=
  sInf (Set.range criticalValue) -
    sSup (fisher_capacity coupling '' Set.Icc (0 : ℝ) 1)

theorem constrainedGap_formula (coupling : ℝ) (nonnegative : 0 ≤ coupling) :
    constrainedGap coupling =
      if coupling ≤ 1 / 2 then (coupling - 1 / 2) ^ 2 else 0 := by
  rw [constrainedGap, criticalValue_isLeast.csInf_eq,
    (capacity_isGreatest_on_unitInterval coupling nonnegative).csSup_eq]
  unfold optimalCapacity
  split_ifs <;> ring

theorem constrainedGap_nonnegative (coupling : ℝ) (nonnegative : 0 ≤ coupling) :
    0 ≤ constrainedGap coupling := by
  rw [constrainedGap_formula coupling nonnegative]
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

theorem constrainedGap_zero_iff (coupling : ℝ) (nonnegative : 0 ≤ coupling) :
    constrainedGap coupling = 0 ↔ 1 / 2 ≤ coupling := by
  rw [constrainedGap_formula coupling nonnegative]
  split_ifs with below
  · rw [sq_eq_zero_iff, sub_eq_zero]
    exact ⟨fun equal => equal.ge, fun above => le_antisymm below above⟩
  · constructor
    · intro _
      linarith
    · intro _
      rfl

theorem constrainedGap_le_pointwise (coupling efficiency momentum : ℝ)
    (nonnegative : 0 ≤ coupling) (feasible : efficiency ∈ Set.Icc (0 : ℝ) 1) :
    constrainedGap coupling ≤ criticalValue momentum - fisher_capacity coupling efficiency := by
  have capacity_bound := (capacity_isGreatest_on_unitInterval coupling nonnegative).2
    ⟨efficiency, feasible, rfl⟩
  have spectral_bound := criticalValue_lower_bound momentum
  rw [constrainedGap, criticalValue_isLeast.csInf_eq,
    (capacity_isGreatest_on_unitInterval coupling nonnegative).csSup_eq]
  linarith

theorem constrainedGap_attained (coupling : ℝ) (nonnegative : 0 ≤ coupling) :
    criticalValue 0 - fisher_capacity coupling (optimalEfficiency coupling) =
      constrainedGap coupling := by
  rw [capacity_at_optimum, constrainedGap, criticalValue_isLeast.csInf_eq,
    (capacity_isGreatest_on_unitInterval coupling nonnegative).csSup_eq,
    criticalValue_formula]
  norm_num

theorem constrainedGap_isLeast (coupling : ℝ) (nonnegative : 0 ≤ coupling) :
    IsLeast
      ((fun point : ℝ × ℝ => criticalValue point.2 - fisher_capacity coupling point.1) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
      (constrainedGap coupling) := by
  refine ⟨⟨(optimalEfficiency coupling, 0),
    ⟨optimalEfficiency_mem coupling, Set.mem_univ _⟩,
    constrainedGap_attained coupling nonnegative⟩, ?_⟩
  rintro value ⟨point, feasible, rfl⟩
  exact constrainedGap_le_pointwise coupling point.1 point.2 nonnegative feasible.1

end InfoGeometry.Synthesis.ConstrainedQuadraticContact
