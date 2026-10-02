import InfoGeometry.Spectrometry.DecoupledThermodynamics

namespace InfoGeometry.Spectrometry.DecoupledThermodynamics.RegressionAudit

open scoped BigOperators Topology
open Filter

example {count : ℕ} (values : Fin count → ℝ) (positive_count : 0 < count) :
    (∑ acquisition, (clrVector values positive_count).val acquisition) = 0 :=
  (clrVector values positive_count).property

example {count : ℕ} (values : Fin count → ℝ) (amplitude : ℝ)
    (positive_count : 0 < count) (positive_amplitude : 0 < amplitude)
    (positive_values : ∀ acquisition, 0 < values acquisition) :
    clrVector (fun acquisition => amplitude * values acquisition) positive_count =
      clrVector values positive_count :=
  clr_cancels_line_amplitude values amplitude positive_count positive_amplitude positive_values

example (energy cutoff temperature : ℝ) :
    0 < lineWeight energy cutoff temperature ∧
    lineWeight energy cutoff temperature < 1 ∧
    lineWeight energy cutoff temperature = 1 / (1 + Real.exp ((energy - cutoff) / temperature)) :=
  ⟨(line_weight_bounds energy cutoff temperature).1,
    (line_weight_bounds energy cutoff temperature).2,
    line_weight_eq_logistic energy cutoff temperature⟩

example (cutoff temperature : ℝ) :
    activeSupport (fun _ : Fin 3 => cutoff) cutoff temperature ≠ 1 := by
  rw [active_support_at_cutoff]
  norm_num

example : activeSupport (fun line : Fin 0 => (line : ℝ)) 1 1 = 0 := by
  simp [activeSupport]

example (energies : Fin 11 → ℝ) (cutoff temperature margin : ℝ)
    (positive_temperature : 0 < temperature)
    (retained : ∀ line : Fin 11, line ≠ 10 → energies line ≤ cutoff - margin * temperature) :
    10 / (1 + Real.exp (-margin)) ≤ activeSupport energies cutoff temperature := by
  have bound := active_support_ge_retained_subset energies cutoff temperature margin
    positive_temperature (Finset.univ.erase 10)
    (fun line member => retained line (Finset.mem_erase.mp member).1)
  simpa using bound

example {Line : Type*} [DecidableEq Line] (energies : Line → ℝ)
    (cutoff temperature value : ℝ) (line other : Line) (distinct : line ≠ other) :
    HasDerivAt (fun replacement =>
      lineWeight ((Function.update energies other replacement) line) cutoff temperature) 0 value :=
  hasDerivAt_other_line_weight energies cutoff temperature value line other distinct

example {Line Parameter : Type*} [Fintype Line]
    [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    (energies : Line → Parameter → ℝ) (derivatives : Line → Parameter →L[ℝ] ℝ)
    (point : Parameter) (cutoff temperature : ℝ) (positive_temperature : 0 < temperature)
    (differentiable : ∀ line, HasFDerivAt (energies line) (derivatives line) point)
    (within_cutoff : ∀ line, energies line point ≤ cutoff) :
    HasFDerivAt
      (fun parameter => totalFreeEnergy (fun line => energies line parameter) cutoff temperature)
      (∑ line, lineWeight (energies line point) cutoff temperature • derivatives line) point ∧
    (Fintype.card Line : ℝ) / 2 ≤ activeSupport (fun line => energies line point) cutoff temperature :=
  ⟨hasFDerivAt_totalFreeEnergy energies derivatives point cutoff temperature
      positive_temperature differentiable,
    active_support_ge_half_ensemble _ cutoff temperature positive_temperature within_cutoff⟩

example (energy cutoff : ℝ) : lineWeight energy cutoff 0 = 1 / 2 := by
  norm_num [line_weight_eq_logistic]

example (energy cutoff : ℝ) (below_cutoff : energy < cutoff) :
    Tendsto (fun temperature => lineWeight energy cutoff temperature) (𝓝[>] 0) (𝓝 1) :=
  tendsto_line_weight_low_temperature_of_lt energy cutoff below_cutoff

example (cutoff temperature : ℝ) (positive_temperature : 0 < temperature) :
    HasDerivAt (fun residual => lineFreeEnergy (residual ^ 2 / 2) cutoff temperature)
      (quadraticScore 0 cutoff temperature) 0 ∧
    Tendsto (fun residual => quadraticScore residual cutoff temperature) atTop (𝓝 0) ∧
    Tendsto (fun residual => quadraticScore residual cutoff temperature) atBot (𝓝 0) :=
  ⟨hasDerivAt_quadratic_freeEnergy 0 cutoff temperature positive_temperature,
    tendsto_quadratic_score_atTop cutoff temperature positive_temperature,
    tendsto_quadratic_score_atBot cutoff temperature positive_temperature⟩

#print axioms clr_cancels_line_amplitude
#print axioms line_partition_pos
#print axioms line_weight_bounds
#print axioms line_weight_eq_logistic
#print axioms line_weight_ge_half_iff
#print axioms line_weight_ge_of_margin
#print axioms line_weight_depends_only_on_own_energy
#print axioms hasDerivAt_other_line_weight
#print axioms hasFDerivAt_lineFreeEnergy
#print axioms hasFDerivAt_totalFreeEnergy
#print axioms fderiv_totalFreeEnergy
#print axioms hasDerivAt_quadratic_freeEnergy
#print axioms tendsto_quadratic_score_atTop
#print axioms tendsto_quadratic_score_atBot
#print axioms active_support_ge_half_ensemble
#print axioms active_support_ge_retained_subset
#print axioms active_support_at_cutoff
#print axioms tendsto_line_weight_low_temperature_of_lt
#print axioms tendsto_line_weight_low_temperature_of_gt
#print axioms ProofDependency.dependency_branches
#print axioms ProofDependency.derivative_and_retention_incomparable

end InfoGeometry.Spectrometry.DecoupledThermodynamics.RegressionAudit
