import InfoGeometry.Spectrometry.RobustThermodynamicRegression

namespace InfoGeometry.Spectrometry.DecoupledThermodynamics

open scoped BigOperators Topology
open Filter

namespace ProofDependency

inductive Archetype
  | clrProjection
  | twoStatePartition
  | logisticWeight
  | additiveFreeEnergy
  | freeEnergyDerivative
  | retainedSupport
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | clrProjection => {clrProjection}
  | twoStatePartition => {twoStatePartition}
  | logisticWeight => {twoStatePartition, logisticWeight}
  | additiveFreeEnergy => {twoStatePartition, additiveFreeEnergy}
  | freeEnergyDerivative =>
      {twoStatePartition, logisticWeight, additiveFreeEnergy, freeEnergyDerivative}
  | retainedSupport => {twoStatePartition, logisticWeight, retainedSupport}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem dependency_branches :
    twoStatePartition ≤ logisticWeight ∧
    twoStatePartition ≤ additiveFreeEnergy ∧
    logisticWeight ≤ freeEnergyDerivative ∧
    additiveFreeEnergy ≤ freeEnergyDerivative ∧
    logisticWeight ≤ retainedSupport := by
  change
    prerequisites twoStatePartition ⊆ prerequisites logisticWeight ∧
    prerequisites twoStatePartition ⊆ prerequisites additiveFreeEnergy ∧
    prerequisites logisticWeight ⊆ prerequisites freeEnergyDerivative ∧
    prerequisites additiveFreeEnergy ⊆ prerequisites freeEnergyDerivative ∧
    prerequisites logisticWeight ⊆ prerequisites retainedSupport
  decide

theorem derivative_and_retention_incomparable :
    ¬ freeEnergyDerivative ≤ retainedSupport ∧
    ¬ retainedSupport ≤ freeEnergyDerivative := by
  change
    ¬ prerequisites freeEnergyDerivative ⊆ prerequisites retainedSupport ∧
    ¬ prerequisites retainedSupport ⊆ prerequisites freeEnergyDerivative
  decide

end ProofDependency

noncomputable section

section CenteredGeometry

variable {acquisitionCount : ℕ}

def zeroSumSpace (acquisitionCount : ℕ) : Submodule ℝ (Fin acquisitionCount → ℝ) where
  carrier := {values | ∑ acquisition, values acquisition = 0}
  zero_mem' := by simp
  add_mem' := by
    intro first second first_zero second_zero
    change (∑ acquisition, (first acquisition + second acquisition)) = 0
    rw [Finset.sum_add_distrib, first_zero, second_zero, add_zero]
  smul_mem' := by
    intro scalar values values_zero
    change ∑ acquisition, scalar * values acquisition = 0
    rw [← Finset.mul_sum, values_zero, mul_zero]

def clrVector (values : Fin acquisitionCount → ℝ) (count_pos : 0 < acquisitionCount) :
    zeroSumSpace acquisitionCount :=
  ⟨RobustThermodynamics.clr values, RobustThermodynamics.clr_sum_zero values count_pos⟩

theorem clr_cancels_line_amplitude
    (values : Fin acquisitionCount → ℝ) (amplitude : ℝ)
    (count_pos : 0 < acquisitionCount) (amplitude_pos : 0 < amplitude)
    (values_pos : ∀ acquisition, 0 < values acquisition) :
    clrVector (fun acquisition => amplitude * values acquisition) count_pos =
      clrVector values count_pos := by
  apply Subtype.ext
  exact RobustThermodynamics.clr_scale_invariant values amplitude count_pos
    amplitude_pos values_pos

def centeredEnergy
    (precision : Matrix (Fin acquisitionCount) (Fin acquisitionCount) ℝ)
    (observed shifts : zeroSumSpace acquisitionCount) : ℝ :=
  RobustThermodynamics.quadraticEnergy precision observed shifts

theorem centered_energy_nonneg
    (precision : Matrix (Fin acquisitionCount) (Fin acquisitionCount) ℝ)
    (precision_psd : precision.PosSemidef)
    (observed shifts : zeroSumSpace acquisitionCount) :
    0 ≤ centeredEnergy precision observed shifts := by
  exact RobustThermodynamics.quadratic_energy_nonneg precision precision_psd observed shifts

theorem centered_energy_self
    (precision : Matrix (Fin acquisitionCount) (Fin acquisitionCount) ℝ)
    (observed : zeroSumSpace acquisitionCount) :
    centeredEnergy precision observed observed = 0 := by
  exact RobustThermodynamics.quadratic_energy_self precision observed

end CenteredGeometry

section TwoStateWeights

def linePartition (energy cutoff temperature : ℝ) : ℝ :=
  Real.exp (-energy / temperature) + Real.exp (-cutoff / temperature)

def lineWeight (energy cutoff temperature : ℝ) : ℝ :=
  Real.exp (-energy / temperature) / linePartition energy cutoff temperature

theorem line_partition_pos (energy cutoff temperature : ℝ) :
    0 < linePartition energy cutoff temperature := by
  exact add_pos (Real.exp_pos _) (Real.exp_pos _)

theorem line_weight_bounds (energy cutoff temperature : ℝ) :
    0 < lineWeight energy cutoff temperature ∧ lineWeight energy cutoff temperature < 1 := by
  constructor
  · exact div_pos (Real.exp_pos _) (line_partition_pos _ _ _)
  · apply (div_lt_one (line_partition_pos _ _ _)).mpr
    exact lt_add_of_pos_right _ (Real.exp_pos _)

theorem line_weight_eq_logistic (energy cutoff temperature : ℝ) :
    lineWeight energy cutoff temperature =
      1 / (1 + Real.exp ((energy - cutoff) / temperature)) := by
  have factorization :
      Real.exp (-cutoff / temperature) =
        Real.exp (-energy / temperature) * Real.exp ((energy - cutoff) / temperature) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold lineWeight linePartition
  rw [factorization]
  have denominator_pos : 0 < 1 + Real.exp ((energy - cutoff) / temperature) := by positivity
  field_simp [ne_of_gt (Real.exp_pos (-energy / temperature)), ne_of_gt denominator_pos]

theorem line_weight_at_cutoff (cutoff temperature : ℝ) :
    lineWeight cutoff cutoff temperature = 1 / 2 := by
  norm_num [line_weight_eq_logistic]

theorem line_weight_strictAnti
    (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    StrictAnti (fun energy => lineWeight energy cutoff temperature) := by
  intro first second energy_lt
  dsimp only
  rw [line_weight_eq_logistic, line_weight_eq_logistic]
  apply one_div_lt_one_div_of_lt (by positivity)
  apply add_lt_add_right
  exact Real.exp_lt_exp.mpr
    ((div_lt_div_iff_of_pos_right temperature_pos).mpr (sub_lt_sub_right energy_lt cutoff))

theorem line_weight_ge_half_iff
    (energy cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    1 / 2 ≤ lineWeight energy cutoff temperature ↔ energy ≤ cutoff := by
  rw [← line_weight_at_cutoff cutoff temperature]
  exact (line_weight_strictAnti cutoff temperature temperature_pos).le_iff_ge

theorem line_weight_gt_half_iff
    (energy cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    1 / 2 < lineWeight energy cutoff temperature ↔ energy < cutoff := by
  rw [← line_weight_at_cutoff cutoff temperature]
  exact (line_weight_strictAnti cutoff temperature temperature_pos).lt_iff_gt

theorem line_weight_complement (energy cutoff temperature : ℝ) :
    1 - lineWeight energy cutoff temperature = lineWeight cutoff energy temperature := by
  have denominator_ne := ne_of_gt (line_partition_pos energy cutoff temperature)
  unfold lineWeight linePartition at *
  rw [add_comm (Real.exp (-cutoff / temperature)) (Real.exp (-energy / temperature))]
  field_simp
  ring

theorem line_weight_ge_of_margin
    (energy cutoff temperature margin : ℝ) (temperature_pos : 0 < temperature)
    (energy_bound : energy ≤ cutoff - margin * temperature) :
    1 / (1 + Real.exp (-margin)) ≤ lineWeight energy cutoff temperature := by
  have weight_bound :=
    (line_weight_strictAnti cutoff temperature temperature_pos).antitone energy_bound
  have gap : (cutoff - margin * temperature - cutoff) / temperature = -margin := by
    field_simp
    ring
  simpa only [line_weight_eq_logistic, gap] using weight_bound

theorem line_weight_le_of_margin
    (energy cutoff temperature margin : ℝ) (temperature_pos : 0 < temperature)
    (energy_bound : cutoff + margin * temperature ≤ energy) :
    lineWeight energy cutoff temperature ≤ 1 / (1 + Real.exp margin) := by
  have weight_bound :=
    (line_weight_strictAnti cutoff temperature temperature_pos).antitone energy_bound
  have gap : (cutoff + margin * temperature - cutoff) / temperature = margin := by
    field_simp
    ring
  simpa only [line_weight_eq_logistic, gap] using weight_bound

theorem line_weight_depends_only_on_own_energy
    {Line : Type*} (energies alternative : Line → ℝ)
    (cutoff temperature : ℝ) (line : Line)
    (same_energy : energies line = alternative line) :
    lineWeight (energies line) cutoff temperature =
      lineWeight (alternative line) cutoff temperature := by
  rw [same_energy]

theorem line_weight_le_exp_gap (energy cutoff temperature : ℝ) :
    lineWeight energy cutoff temperature ≤ Real.exp ((cutoff - energy) / temperature) := by
  rw [line_weight_eq_logistic]
  have reverse_gap : (cutoff - energy) / temperature = -((energy - cutoff) / temperature) := by
    ring
  rw [reverse_gap, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) (by linarith)

theorem tendsto_line_weight_atTop
    (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    Tendsto (fun energy => lineWeight energy cutoff temperature) atTop (𝓝 0) := by
  have energy_limit : Tendsto (fun energy : ℝ => energy / temperature) atTop atTop :=
    tendsto_id.atTop_div_const temperature_pos
  have boltzmann_limit := Real.tendsto_exp_neg_atTop_nhds_zero.comp energy_limit
  simpa [lineWeight, linePartition, Function.comp_def, Pi.div_apply, neg_div] using
    boltzmann_limit.div (boltzmann_limit.add tendsto_const_nhds)
      (ne_of_gt (by simpa [neg_div] using Real.exp_pos (-cutoff / temperature)))

end TwoStateWeights

section FreeEnergy

def lineFreeEnergy (energy cutoff temperature : ℝ) : ℝ :=
  -temperature * Real.log (linePartition energy cutoff temperature)

def totalFreeEnergy {Line : Type*} [Fintype Line]
    (energies : Line → ℝ) (cutoff temperature : ℝ) : ℝ :=
  ∑ line, lineFreeEnergy (energies line) cutoff temperature

variable {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

theorem hasFDerivAt_lineFreeEnergy
    (energy : Parameter → ℝ) (derivative : Parameter →L[ℝ] ℝ)
    (point : Parameter) (cutoff temperature : ℝ) (temperature_pos : 0 < temperature)
    (energy_derivative : HasFDerivAt energy derivative point) :
    HasFDerivAt (fun parameter => lineFreeEnergy (energy parameter) cutoff temperature)
      (lineWeight (energy point) cutoff temperature • derivative) point := by
  have temperature_ne := ne_of_gt temperature_pos
  have partition_ne := ne_of_gt (line_partition_pos (energy point) cutoff temperature)
  have boltzmann_derivative :
      HasFDerivAt (fun parameter => Real.exp (-energy parameter / temperature))
        (Real.exp (-energy point / temperature) • ((-1 / temperature) • derivative)) point := by
    convert (energy_derivative.const_mul (-1 / temperature)).exp using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  have free_derivative :=
    ((boltzmann_derivative.add_const (Real.exp (-cutoff / temperature))).log
      partition_ne).const_mul (-temperature)
  convert free_derivative using 1
  simp only [smul_smul]
  congr 1
  dsimp [lineWeight, linePartition] at *
  field_simp

theorem hasFDerivAt_totalFreeEnergy
    {Line : Type*} [Fintype Line]
    (energies : Line → Parameter → ℝ)
    (derivatives : Line → Parameter →L[ℝ] ℝ)
    (point : Parameter) (cutoff temperature : ℝ) (temperature_pos : 0 < temperature)
    (energy_derivatives : ∀ line, HasFDerivAt (energies line) (derivatives line) point) :
    HasFDerivAt
      (fun parameter => totalFreeEnergy (fun line => energies line parameter) cutoff temperature)
      (∑ line, lineWeight (energies line point) cutoff temperature • derivatives line) point := by
  exact HasFDerivAt.fun_sum (fun line _ =>
    hasFDerivAt_lineFreeEnergy (energies line) (derivatives line) point cutoff temperature
      temperature_pos (energy_derivatives line))

theorem fderiv_totalFreeEnergy
    {Line : Type*} [Fintype Line]
    (energies : Line → Parameter → ℝ)
    (derivatives : Line → Parameter →L[ℝ] ℝ)
    (point : Parameter) (cutoff temperature : ℝ) (temperature_pos : 0 < temperature)
    (energy_derivatives : ∀ line, HasFDerivAt (energies line) (derivatives line) point) :
    fderiv ℝ
        (fun parameter => totalFreeEnergy (fun line => energies line parameter) cutoff temperature)
        point =
      ∑ line, lineWeight (energies line point) cutoff temperature • derivatives line := by
  exact (hasFDerivAt_totalFreeEnergy energies derivatives point cutoff temperature
    temperature_pos energy_derivatives).fderiv

end FreeEnergy

section QuadraticInfluence

def quadraticScore (residual cutoff temperature : ℝ) : ℝ :=
  residual * lineWeight (residual ^ 2 / 2) cutoff temperature

theorem hasDerivAt_quadratic_freeEnergy
    (residual cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    HasDerivAt (fun value => lineFreeEnergy (value ^ 2 / 2) cutoff temperature)
      (quadraticScore residual cutoff temperature) residual := by
  have energy_derivative :
      HasDerivAt (fun value : ℝ => value ^ 2 / 2) residual residual := by
    convert ((hasDerivAt_id residual).pow 2).div_const 2 using 1
    simp
  have free_derivative := hasFDerivAt_lineFreeEnergy _ _ residual cutoff temperature
    temperature_pos energy_derivative.hasFDerivAt
  simpa [quadraticScore, smul_eq_mul, mul_comm] using free_derivative.hasDerivAt

theorem quadratic_score_neg (residual cutoff temperature : ℝ) :
    quadraticScore (-residual) cutoff temperature =
      -quadraticScore residual cutoff temperature := by
  simp [quadraticScore]

theorem tendsto_quadratic_score_atTop
    (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    Tendsto (fun residual => quadraticScore residual cutoff temperature) atTop (𝓝 0) := by
  have majorant_limit :
      Tendsto (fun residual : ℝ => Real.exp (cutoff / temperature) *
        (residual * Real.exp (-residual))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul
      (Real.exp (cutoff / temperature))
  apply squeeze_zero' ?_ ?_ majorant_limit
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with residual residual_nonneg
    exact mul_nonneg residual_nonneg (line_weight_bounds _ _ _).1.le
  · filter_upwards [eventually_ge_atTop (2 * temperature)] with residual residual_large
    have residual_nonneg : 0 ≤ residual := by linarith
    have exponent_bound : (cutoff - residual ^ 2 / 2) / temperature ≤
        cutoff / temperature - residual := by
      apply (div_le_iff₀ temperature_pos).mpr
      have product_nonneg := mul_nonneg residual_nonneg (sub_nonneg.mpr residual_large)
      have cancel_temperature : (cutoff / temperature) * temperature = cutoff :=
        div_mul_cancel₀ _ (ne_of_gt temperature_pos)
      nlinarith
    calc
      quadraticScore residual cutoff temperature
          ≤ residual * Real.exp ((cutoff - residual ^ 2 / 2) / temperature) :=
        mul_le_mul_of_nonneg_left (line_weight_le_exp_gap _ _ _) residual_nonneg
      _ ≤ residual * Real.exp (cutoff / temperature - residual) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponent_bound) residual_nonneg
      _ = Real.exp (cutoff / temperature) * (residual * Real.exp (-residual)) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring

theorem tendsto_quadratic_score_atBot
    (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    Tendsto (fun residual => quadraticScore residual cutoff temperature) atBot (𝓝 0) := by
  simpa [Function.comp_def, quadratic_score_neg] using
    ((tendsto_quadratic_score_atTop cutoff temperature temperature_pos).comp
      tendsto_neg_atBot_atTop).neg

end QuadraticInfluence

section RetainedSupport

variable {Line : Type*} [Fintype Line]

def activeSupport (energies : Line → ℝ) (cutoff temperature : ℝ) : ℝ :=
  ∑ line, lineWeight (energies line) cutoff temperature

theorem active_support_bounds [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    0 < activeSupport energies cutoff temperature ∧
      activeSupport energies cutoff temperature < (Fintype.card Line : ℝ) := by
  constructor
  · exact Finset.sum_pos (fun line _ => (line_weight_bounds _ _ _).1) Finset.univ_nonempty
  · have bound := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun line _ => (line_weight_bounds (energies line) cutoff temperature).2)
    simpa [activeSupport] using bound

theorem active_support_ge_half_ensemble
    (energies : Line → ℝ) (cutoff temperature : ℝ) (temperature_pos : 0 < temperature)
    (energies_bound : ∀ line, energies line ≤ cutoff) :
    (Fintype.card Line : ℝ) / 2 ≤ activeSupport energies cutoff temperature := by
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun line _ =>
    (line_weight_ge_half_iff (energies line) cutoff temperature temperature_pos).mpr
      (energies_bound line))
  simpa [activeSupport, div_eq_mul_inv] using bound

theorem active_support_ge_retained_subset
    (energies : Line → ℝ) (cutoff temperature margin : ℝ)
    (temperature_pos : 0 < temperature) (retained : Finset Line)
    (energies_bound : ∀ line ∈ retained, energies line ≤ cutoff - margin * temperature) :
    (retained.card : ℝ) / (1 + Real.exp (-margin)) ≤
      activeSupport energies cutoff temperature := by
  have retained_bound := Finset.sum_le_sum (s := retained) (fun line membership =>
    line_weight_ge_of_margin (energies line) cutoff temperature margin temperature_pos
      (energies_bound line membership))
  have total_bound : (∑ line ∈ retained, lineWeight (energies line) cutoff temperature) ≤
      activeSupport energies cutoff temperature := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ retained)
    intro line _ _
    exact (line_weight_bounds _ _ _).1.le
  refine le_trans ?_ total_bound
  simpa [div_eq_mul_inv] using retained_bound

theorem active_support_at_cutoff (cutoff temperature : ℝ) :
    activeSupport (fun _ : Line => cutoff) cutoff temperature =
      (Fintype.card Line : ℝ) / 2 := by
  simp [activeSupport, line_weight_at_cutoff, div_eq_mul_inv]

end RetainedSupport

end

end InfoGeometry.Spectrometry.DecoupledThermodynamics
