import InfoGeometry.Spectrometry.DecoupledThermodynamicsFluctuations
import InfoGeometry.Spectrometry.FiniteWeightDispersion

namespace InfoGeometry.Spectrometry.DecoupledThermodynamics

open scoped BigOperators

namespace ThermodynamicGeometryDependency

inductive Archetype
  | varianceDecomposition
  | dispersion
  | stateEnvelope
  | quadraticPeak
  | universalBound
  | freeEnergyCalculus
  | shiftHessian
  | susceptibilityBound
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | varianceDecomposition => {varianceDecomposition}
  | dispersion => {dispersion}
  | stateEnvelope => {varianceDecomposition, dispersion, stateEnvelope}
  | quadraticPeak => {quadraticPeak}
  | universalBound =>
      {varianceDecomposition, dispersion, stateEnvelope, quadraticPeak, universalBound}
  | freeEnergyCalculus => {freeEnergyCalculus}
  | shiftHessian => {varianceDecomposition, freeEnergyCalculus, shiftHessian}
  | susceptibilityBound =>
      {varianceDecomposition, dispersion, stateEnvelope, freeEnergyCalculus,
        shiftHessian, susceptibilityBound}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem dependency_edges :
    varianceDecomposition ≤ stateEnvelope ∧ dispersion ≤ stateEnvelope ∧
    stateEnvelope ≤ universalBound ∧ quadraticPeak ≤ universalBound ∧
    varianceDecomposition ≤ shiftHessian ∧ freeEnergyCalculus ≤ shiftHessian ∧
    stateEnvelope ≤ susceptibilityBound ∧ shiftHessian ≤ susceptibilityBound := by
  change
    prerequisites varianceDecomposition ⊆ prerequisites stateEnvelope ∧
    prerequisites dispersion ⊆ prerequisites stateEnvelope ∧
    prerequisites stateEnvelope ⊆ prerequisites universalBound ∧
    prerequisites quadraticPeak ⊆ prerequisites universalBound ∧
    prerequisites varianceDecomposition ⊆ prerequisites shiftHessian ∧
    prerequisites freeEnergyCalculus ⊆ prerequisites shiftHessian ∧
    prerequisites stateEnvelope ⊆ prerequisites susceptibilityBound ∧
    prerequisites shiftHessian ⊆ prerequisites susceptibilityBound
  decide

theorem envelope_and_hessian_incomparable :
    ¬ stateEnvelope ≤ shiftHessian ∧ ¬ shiftHessian ≤ stateEnvelope := by
  change ¬ prerequisites stateEnvelope ⊆ prerequisites shiftHessian ∧
    ¬ prerequisites shiftHessian ⊆ prerequisites stateEnvelope
  decide

end ThermodynamicGeometryDependency

open InfoGeometry.Spectrometry.FiniteWeightDispersion

noncomputable section

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

theorem accepted_count_variance_decomposition
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    acceptedCountVariance energies cutoff temperature =
      activeSupport energies cutoff temperature -
        squaredWeightSum (fun line => lineWeight (energies line) cutoff temperature) := by
  rw [accepted_count_variance_eq_sum]
  unfold activeSupport squaredWeightSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro line _
  ring

theorem accepted_count_envelope_defect [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    varianceEnvelope (Fintype.card Line) (activeSupport energies cutoff temperature) -
        acceptedCountVariance energies cutoff temperature =
      dispersion (fun line => lineWeight (energies line) cutoff temperature) := by
  rw [accepted_count_variance_decomposition, dispersion_eq]
  unfold varianceEnvelope activeSupport
  ring

theorem accepted_count_variance_le_state_envelope [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    acceptedCountVariance energies cutoff temperature ≤
      varianceEnvelope (Fintype.card Line) (activeSupport energies cutoff temperature) := by
  have nonnegative := dispersion_nonneg (fun line => lineWeight (energies line) cutoff temperature)
  rw [← accepted_count_envelope_defect] at nonnegative
  linarith

theorem accepted_count_variance_eq_envelope_iff [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    acceptedCountVariance energies cutoff temperature =
        varianceEnvelope (Fintype.card Line) (activeSupport energies cutoff temperature) ↔
      ∀ line, lineWeight (energies line) cutoff temperature =
        activeSupport energies cutoff temperature / Fintype.card Line := by
  rw [eq_comm, ← sub_eq_zero, accepted_count_envelope_defect]
  exact dispersion_eq_zero_iff _

theorem accepted_count_variance_lt_envelope_of_nonuniform [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature : ℝ)
    (nonuniform : ∃ line, lineWeight (energies line) cutoff temperature ≠
      activeSupport energies cutoff temperature / Fintype.card Line) :
    acceptedCountVariance energies cutoff temperature <
      varianceEnvelope (Fintype.card Line) (activeSupport energies cutoff temperature) := by
  refine lt_of_le_of_ne (accepted_count_variance_le_state_envelope energies cutoff temperature) ?_
  intro equality
  obtain ⟨line, different⟩ := nonuniform
  exact different ((accepted_count_variance_eq_envelope_iff energies cutoff temperature).mp equality line)

theorem accepted_count_variance_le_quarter_via_envelope [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    acceptedCountVariance energies cutoff temperature ≤ (Fintype.card Line : ℝ) / 4 :=
  (accepted_count_variance_le_state_envelope energies cutoff temperature).trans
    (envelope_le_quarter _ _ Fintype.card_pos)

theorem eleven_line_variance_bound_of_support_ten
    (energies : Fin 11 → ℝ) (cutoff temperature : ℝ)
    (support_ten : activeSupport energies cutoff temperature = 10) :
    acceptedCountVariance energies cutoff temperature ≤ 10 / 11 := by
  have bound := accepted_count_variance_le_state_envelope energies cutoff temperature
  norm_num [support_ten, varianceEnvelope] at bound ⊢
  exact bound

def shiftedFreeEnergy (energies : Line → ℝ) (cutoff temperature shift : ℝ) : ℝ :=
  totalFreeEnergy (fun line => energies line + shift) cutoff temperature

omit [DecidableEq Line] in
theorem hasDerivAt_shiftedFreeEnergy
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (temperature_pos : 0 < temperature) :
    HasDerivAt (shiftedFreeEnergy energies cutoff temperature)
      (activeSupport (fun line => energies line + shift) cutoff temperature) shift := by
  have line_derivative (line : Line) :
      HasDerivAt (fun offset => lineFreeEnergy (energies line + offset) cutoff temperature)
        (lineWeight (energies line + shift) cutoff temperature) shift := by
    simpa using
      (hasDerivAt_lineFreeEnergy (energies line + shift) cutoff temperature temperature_pos).comp
        shift ((hasDerivAt_id shift).const_add (energies line))
  exact HasDerivAt.fun_sum (fun line _ => line_derivative line)

omit [DecidableEq Line] in
theorem deriv_shiftedFreeEnergy_eq
    (energies : Line → ℝ) (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    deriv (shiftedFreeEnergy energies cutoff temperature) =
      fun shift => activeSupport (fun line => energies line + shift) cutoff temperature := by
  funext shift
  exact (hasDerivAt_shiftedFreeEnergy energies cutoff temperature shift temperature_pos).deriv

theorem hasDerivAt_shiftedActiveSupport
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) :
    HasDerivAt
      (fun offset => activeSupport (fun line => energies line + offset) cutoff temperature)
      (-acceptedCountVariance (fun line => energies line + shift) cutoff temperature / temperature)
      shift := by
  have line_derivative (line : Line) :
      HasDerivAt (fun offset => lineWeight (energies line + offset) cutoff temperature)
        (-lineWeight (energies line + shift) cutoff temperature *
          (1 - lineWeight (energies line + shift) cutoff temperature) / temperature) shift := by
    simpa using (hasDerivAt_lineWeight (energies line + shift) cutoff temperature).comp
      shift ((hasDerivAt_id shift).const_add (energies line))
  convert HasDerivAt.fun_sum (fun line _ => line_derivative line) using 1
  simp only [accepted_count_variance_eq_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib, neg_mul]

theorem hasDerivAt_deriv_shiftedFreeEnergy
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (temperature_pos : 0 < temperature) :
    HasDerivAt (deriv (shiftedFreeEnergy energies cutoff temperature))
      (-acceptedCountVariance (fun line => energies line + shift) cutoff temperature / temperature)
      shift := by
  rw [deriv_shiftedFreeEnergy_eq energies cutoff temperature temperature_pos]
  exact hasDerivAt_shiftedActiveSupport energies cutoff temperature shift

def shiftSusceptibility (energies : Line → ℝ) (cutoff temperature shift : ℝ) : ℝ :=
  -deriv (deriv (shiftedFreeEnergy energies cutoff temperature)) shift

theorem shift_susceptibility_eq_variance_div_temperature
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (temperature_pos : 0 < temperature) :
    shiftSusceptibility energies cutoff temperature shift =
      acceptedCountVariance (fun line => energies line + shift) cutoff temperature / temperature := by
  unfold shiftSusceptibility
  rw [(hasDerivAt_deriv_shiftedFreeEnergy energies cutoff temperature shift temperature_pos).deriv]
  ring

theorem shift_susceptibility_nonneg
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (temperature_pos : 0 < temperature) :
    0 ≤ shiftSusceptibility energies cutoff temperature shift := by
  rw [shift_susceptibility_eq_variance_div_temperature energies cutoff temperature shift temperature_pos]
  exact div_nonneg (accepted_count_variance_nonneg _ _ _) temperature_pos.le

theorem shift_susceptibility_pos [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (temperature_pos : 0 < temperature) :
    0 < shiftSusceptibility energies cutoff temperature shift := by
  rw [shift_susceptibility_eq_variance_div_temperature energies cutoff temperature shift temperature_pos]
  exact div_pos (accepted_count_variance_pos _ _ _) temperature_pos

theorem shift_susceptibility_le_state_envelope [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (temperature_pos : 0 < temperature) :
    shiftSusceptibility energies cutoff temperature shift ≤
      varianceEnvelope (Fintype.card Line)
        (activeSupport (fun line => energies line + shift) cutoff temperature) / temperature := by
  rw [shift_susceptibility_eq_variance_div_temperature energies cutoff temperature shift temperature_pos]
  exact div_le_div_of_nonneg_right
    (accepted_count_variance_le_state_envelope _ _ _) temperature_pos.le

theorem shift_susceptibility_at_cutoff (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    shiftSusceptibility (fun _line : Line => cutoff) cutoff temperature 0 =
      (Fintype.card Line : ℝ) / (4 * temperature) := by
  rw [shift_susceptibility_eq_variance_div_temperature _ _ _ _ temperature_pos]
  simp only [add_zero, accepted_count_variance_at_cutoff]
  ring

end

end InfoGeometry.Spectrometry.DecoupledThermodynamics
