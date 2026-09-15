import InfoGeometry.Spectrometry.SvdClrEquivalence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace InfoGeometry.Spectrometry.RobustThermodynamics

open scoped BigOperators

namespace ProofDependency

inductive Archetype
  | clrProjection
  | devianceEnergy
  | gibbsEnsemble
  | energyShift
  | freeEnergyDerivative
  | effectiveSupport
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | clrProjection => {clrProjection}
  | devianceEnergy => {clrProjection, devianceEnergy}
  | gibbsEnsemble => {clrProjection, devianceEnergy, gibbsEnsemble}
  | energyShift => {clrProjection, devianceEnergy, gibbsEnsemble, energyShift}
  | freeEnergyDerivative =>
      {clrProjection, devianceEnergy, gibbsEnsemble, freeEnergyDerivative}
  | effectiveSupport => {clrProjection, devianceEnergy, gibbsEnsemble, effectiveSupport}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem dependency_branches :
    clrProjection ≤ devianceEnergy ∧ devianceEnergy ≤ gibbsEnsemble ∧
    gibbsEnsemble ≤ energyShift ∧ gibbsEnsemble ≤ freeEnergyDerivative ∧
    gibbsEnsemble ≤ effectiveSupport := by
  change
    prerequisites clrProjection ⊆ prerequisites devianceEnergy ∧
    prerequisites devianceEnergy ⊆ prerequisites gibbsEnsemble ∧
    prerequisites gibbsEnsemble ⊆ prerequisites energyShift ∧
    prerequisites gibbsEnsemble ⊆ prerequisites freeEnergyDerivative ∧
    prerequisites gibbsEnsemble ⊆ prerequisites effectiveSupport
  decide

theorem derivative_and_support_incomparable :
    ¬ freeEnergyDerivative ≤ effectiveSupport ∧
    ¬ effectiveSupport ≤ freeEnergyDerivative := by
  change
    ¬ prerequisites freeEnergyDerivative ⊆ prerequisites effectiveSupport ∧
    ¬ prerequisites effectiveSupport ⊆ prerequisites freeEnergyDerivative
  decide

end ProofDependency

noncomputable section

section Centering

variable {acquisitionCount : ℕ}

def clr (values : Fin acquisitionCount → ℝ) : Fin acquisitionCount → ℝ :=
  SvdClrEquivalence.center (fun acquisition => Real.log (values acquisition))

theorem clr_sum_zero
    (values : Fin acquisitionCount → ℝ) (count_pos : 0 < acquisitionCount) :
    ∑ acquisition, clr values acquisition = 0 := by
  exact SvdClrEquivalence.sum_center _ count_pos

theorem clr_scale_invariant
    (values : Fin acquisitionCount → ℝ) (amplitude : ℝ)
    (count_pos : 0 < acquisitionCount) (amplitude_pos : 0 < amplitude)
    (values_pos : ∀ acquisition, 0 < values acquisition) :
    clr (fun acquisition => amplitude * values acquisition) = clr values := by
  unfold clr
  simp_rw [Real.log_mul (ne_of_gt amplitude_pos) (ne_of_gt (values_pos _))]
  exact SvdClrEquivalence.center_add_constant _ _ count_pos

def quadraticEnergy
    (precision : Matrix (Fin acquisitionCount) (Fin acquisitionCount) ℝ)
    (observed shifts : Fin acquisitionCount → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct (observed - shifts) (precision.mulVec (observed - shifts))

theorem quadratic_energy_nonneg
    (precision : Matrix (Fin acquisitionCount) (Fin acquisitionCount) ℝ)
    (precision_psd : precision.PosSemidef)
    (observed shifts : Fin acquisitionCount → ℝ) :
    0 ≤ quadraticEnergy precision observed shifts := by
  have form_nonneg := precision_psd.dotProduct_mulVec_nonneg (observed - shifts)
  simp only [star_trivial] at form_nonneg
  exact mul_nonneg (by norm_num) form_nonneg

theorem quadratic_energy_self
    (precision : Matrix (Fin acquisitionCount) (Fin acquisitionCount) ℝ)
    (observed : Fin acquisitionCount → ℝ) :
    quadraticEnergy precision observed observed = 0 := by
  simp [quadraticEnergy]

end Centering

section PoissonEnergy

def poissonHalfDeviance (observed expected : ℝ) : ℝ :=
  expected - observed + observed * Real.log (observed / expected)

theorem poisson_half_deviance_self (observed : ℝ) :
    poissonHalfDeviance observed observed = 0 := by
  by_cases observed_zero : observed = 0
  · simp [poissonHalfDeviance, observed_zero]
  · simp [poissonHalfDeviance, observed_zero]

theorem poisson_half_deviance_at_zero (expected : ℝ) :
    poissonHalfDeviance 0 expected = expected := by
  simp [poissonHalfDeviance]

theorem poisson_half_deviance_nonneg
    (observed expected : ℝ) (observed_nonneg : 0 ≤ observed) (expected_pos : 0 < expected) :
    0 ≤ poissonHalfDeviance observed expected := by
  rcases observed_nonneg.eq_or_lt with observed_zero | observed_pos
  · rw [← observed_zero, poisson_half_deviance_at_zero]
    exact expected_pos.le
  · have observed_ne := ne_of_gt observed_pos
    have expected_ne := ne_of_gt expected_pos
    have log_bound := Real.log_le_sub_one_of_pos (div_pos expected_pos observed_pos)
    have weighted_bound := mul_le_mul_of_nonneg_left log_bound observed_pos.le
    have cancel_ratio : observed * (expected / observed) = expected := by
      field_simp
    have log_ratio : Real.log (observed / expected) = -Real.log (expected / observed) := by
      rw [Real.log_div observed_ne expected_ne, Real.log_div expected_ne observed_ne]
      ring
    dsimp [poissonHalfDeviance]
    rw [log_ratio]
    nlinarith

end PoissonEnergy

section Ensemble

variable {Line : Type*} [Fintype Line] [Nonempty Line]

def partition (energies : Line → ℝ) (temperature : ℝ) : ℝ :=
  ∑ line, Real.exp (-energies line / temperature)

def gibbsWeight (energies : Line → ℝ) (temperature : ℝ) (line : Line) : ℝ :=
  Real.exp (-energies line / temperature) / partition energies temperature

def freeEnergy (energies : Line → ℝ) (temperature : ℝ) : ℝ :=
  -temperature * Real.log ((1 / (Fintype.card Line : ℝ)) * partition energies temperature)

theorem partition_pos (energies : Line → ℝ) (temperature : ℝ) :
    0 < partition energies temperature := by
  apply Finset.sum_pos
  · intro line _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

theorem gibbs_weight_pos (energies : Line → ℝ) (temperature : ℝ) (line : Line) :
    0 < gibbsWeight energies temperature line := by
  exact div_pos (Real.exp_pos _) (partition_pos energies temperature)

theorem gibbs_weights_sum_one (energies : Line → ℝ) (temperature : ℝ) :
    ∑ line, gibbsWeight energies temperature line = 1 := by
  simp only [gibbsWeight, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos energies temperature))

theorem gibbs_weight_antitone_energy
    (energies : Line → ℝ) (temperature : ℝ) (temperature_pos : 0 < temperature)
    (first second : Line) (energy_order : energies first ≤ energies second) :
    gibbsWeight energies temperature second ≤ gibbsWeight energies temperature first := by
  apply div_le_div_of_nonneg_right _ (partition_pos energies temperature).le
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg energy_order) temperature_pos.le

theorem boltzmann_shift (energy offset temperature : ℝ) :
    Real.exp (-(energy + offset) / temperature) =
      Real.exp (-energy / temperature) * Real.exp (-offset / temperature) := by
  rw [show -(energy + offset) / temperature =
    -energy / temperature + -offset / temperature by ring, Real.exp_add]

omit [Nonempty Line] in
theorem partition_shift (energies : Line → ℝ) (temperature offset : ℝ) :
    partition (fun line => energies line + offset) temperature =
      partition energies temperature * Real.exp (-offset / temperature) := by
  simp only [partition, boltzmann_shift, Finset.sum_mul]

omit [Nonempty Line] in
theorem gibbs_weight_shift_invariant
    (energies : Line → ℝ) (temperature offset : ℝ) (line : Line) :
    gibbsWeight (fun index => energies index + offset) temperature line =
      gibbsWeight energies temperature line := by
  unfold gibbsWeight
  rw [boltzmann_shift, partition_shift]
  exact mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos _))

theorem free_energy_shift_equivariant
    (energies : Line → ℝ) (temperature offset : ℝ) (temperature_pos : 0 < temperature) :
    freeEnergy (fun line => energies line + offset) temperature =
      freeEnergy energies temperature + offset := by
  have count_pos : (0 : ℝ) < Fintype.card Line := by
    exact_mod_cast Fintype.card_pos
  have argument_pos :
      0 < (1 / (Fintype.card Line : ℝ)) * partition energies temperature :=
    mul_pos (one_div_pos.mpr count_pos) (partition_pos energies temperature)
  unfold freeEnergy
  rw [partition_shift, ← mul_assoc,
    Real.log_mul (ne_of_gt argument_pos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  field_simp [ne_of_gt temperature_pos]
  ring

theorem gibbs_weight_constant (energy temperature : ℝ) (line : Line) :
    gibbsWeight (fun _ : Line => energy) temperature line = 1 / (Fintype.card Line : ℝ) := by
  have count_ne : (Fintype.card Line : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Fintype.card_pos)
  simp only [gibbsWeight, partition, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [ne_of_gt (Real.exp_pos (-energy / temperature))]

theorem gibbs_weight_ratio
    (energies : Line → ℝ) (temperature : ℝ) (first second : Line) :
    gibbsWeight energies temperature first / gibbsWeight energies temperature second =
      Real.exp ((energies second - energies first) / temperature) := by
  rw [show (energies second - energies first) / temperature =
    -energies first / temperature - -energies second / temperature by ring, Real.exp_sub]
  unfold gibbsWeight
  field_simp [ne_of_gt (partition_pos energies temperature),
    ne_of_gt (Real.exp_pos (-energies second / temperature))]

end Ensemble

section FreeEnergyDerivative

variable {Line Parameter : Type*} [Fintype Line] [Nonempty Line]
variable [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

theorem hasFDerivAt_freeEnergy
    (energies : Line → Parameter → ℝ)
    (derivatives : Line → Parameter →L[ℝ] ℝ)
    (point : Parameter) (temperature : ℝ) (temperature_pos : 0 < temperature)
    (energy_derivatives : ∀ line, HasFDerivAt (energies line) (derivatives line) point) :
    HasFDerivAt (fun parameter => freeEnergy (fun line => energies line parameter) temperature)
      (∑ line, gibbsWeight (fun index => energies index point) temperature line • derivatives line)
      point := by
  have temperature_ne := ne_of_gt temperature_pos
  have count_pos : (0 : ℝ) < Fintype.card Line := by
    exact_mod_cast Fintype.card_pos
  have count_ne := ne_of_gt count_pos
  have partition_ne := ne_of_gt (partition_pos (fun line => energies line point) temperature)
  have term_derivatives (line : Line) :
      HasFDerivAt (fun parameter => Real.exp (-energies line parameter / temperature))
        (Real.exp (-energies line point / temperature) • ((-1 / temperature) • derivatives line))
        point := by
    convert ((energy_derivatives line).const_mul (-1 / temperature)).exp using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  have partition_derivative :
      HasFDerivAt (fun parameter => partition (fun line => energies line parameter) temperature)
        (∑ line, Real.exp (-energies line point / temperature) •
          ((-1 / temperature) • derivatives line)) point :=
    HasFDerivAt.fun_sum (fun line _ => term_derivatives line)
  have argument_pos :
      0 < (1 / (Fintype.card Line : ℝ)) * partition (fun line => energies line point) temperature :=
    mul_pos (one_div_pos.mpr count_pos) (partition_pos _ _)
  have free_derivative :=
    ((partition_derivative.const_mul (1 / (Fintype.card Line : ℝ))).log
      (ne_of_gt argument_pos)).const_mul (-temperature)
  convert free_derivative using 1
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro line _
  congr 1
  dsimp [gibbsWeight]
  field_simp

theorem fderiv_freeEnergy
    (energies : Line → Parameter → ℝ)
    (derivatives : Line → Parameter →L[ℝ] ℝ)
    (point : Parameter) (temperature : ℝ) (temperature_pos : 0 < temperature)
    (energy_derivatives : ∀ line, HasFDerivAt (energies line) (derivatives line) point) :
    fderiv ℝ (fun parameter => freeEnergy (fun line => energies line parameter) temperature) point =
      ∑ line, gibbsWeight (fun index => energies index point) temperature line • derivatives line := by
  exact (hasFDerivAt_freeEnergy energies derivatives point temperature
    temperature_pos energy_derivatives).fderiv

end FreeEnergyDerivative

section EffectiveSupport

variable {Line : Type*} [Fintype Line] [Nonempty Line]

def effectiveSupport (weights : Line → ℝ) : ℝ :=
  1 / ∑ line, weights line ^ 2

theorem effective_support_bounds
    (weights : Line → ℝ) (weights_nonneg : ∀ line, 0 ≤ weights line)
    (weights_sum : ∑ line, weights line = 1) :
    1 ≤ effectiveSupport weights ∧ effectiveSupport weights ≤ (Fintype.card Line : ℝ) := by
  have count_pos : (0 : ℝ) < Fintype.card Line := by
    exact_mod_cast Fintype.card_pos
  have squares_le : (∑ line, weights line ^ 2) ≤ 1 := by
    simpa [weights_sum] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := weights)
        (fun line _ => weights_nonneg line))
  have cauchy : (1 : ℝ) ≤ (Fintype.card Line : ℝ) * ∑ line, weights line ^ 2 := by
    simpa [weights_sum] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Line => (1 : ℝ)) weights)
  have squares_pos : 0 < ∑ line, weights line ^ 2 := by
    nlinarith
  constructor
  · apply (le_div_iff₀ squares_pos).mpr
    simpa using squares_le
  · exact (div_le_iff₀ squares_pos).mpr cauchy

theorem gibbs_effective_support_bounds (energies : Line → ℝ) (temperature : ℝ) :
    1 ≤ effectiveSupport (gibbsWeight energies temperature) ∧
      effectiveSupport (gibbsWeight energies temperature) ≤ (Fintype.card Line : ℝ) := by
  exact effective_support_bounds _ (fun line => (gibbs_weight_pos _ _ line).le)
    (gibbs_weights_sum_one _ _)

theorem effective_support_uniform :
    effectiveSupport (fun _ : Line => 1 / (Fintype.card Line : ℝ)) =
      (Fintype.card Line : ℝ) := by
  have count_ne : (Fintype.card Line : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Fintype.card_pos)
  simp [effectiveSupport]
  field_simp

omit [Nonempty Line] in
theorem effective_support_single_line [DecidableEq Line] (selected : Line) :
    effectiveSupport (fun line => if line = selected then (1 : ℝ) else 0) = 1 := by
  simp [effectiveSupport]

end EffectiveSupport

end

end InfoGeometry.Spectrometry.RobustThermodynamics
