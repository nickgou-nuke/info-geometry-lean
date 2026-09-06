import InfoGeometry.Core.Entropy
import InfoGeometry.Potential.Thermo
import InfoGeometry.Probability.GromovConcentration
import SelfReference.RobustThermodynamicRegression

open scoped BigOperators ENNReal

/-!
# Thermodynamic fitting bridges

This module connects the repo's thermodynamic fitting backbone to:
- Gibbs surprisal identities
- temperature-regularized Hamiltonian defects
- finite weighted outlier control
-/

set_option autoImplicit false

namespace InfoGeometry.Probability

open InfoGeometry
open InfoGeometry.LogPotential

section GibbsBridge

variable {Data : Type} [Fintype Data] [Nonempty Data] [DecidableEq Data]
variable {Theta : Type}

local notation "partFn" => SelfReference.partitionFunction (Data := Data) (Theta := Theta)
local notation "gibbsW" => SelfReference.gibbsWeights (Data := Data) (Theta := Theta)

omit [DecidableEq Data] in
lemma partitionFunction_pos
    (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) :
    0 < partFn E θ ε := by
  classical
  unfold SelfReference.partitionFunction
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Data))
      (f := fun i => Real.exp (-(E i θ) / ε))
      (by
        intro i hi
        exact Real.exp_pos _)
      Finset.univ_nonempty)

omit [DecidableEq Data] in
lemma partitionFunction_ne_zero
    (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) :
    partFn E θ ε ≠ 0 :=
  (partitionFunction_pos E θ ε).ne'

omit [DecidableEq Data] in
lemma gibbsWeights_nonneg
    (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) (i : Data) :
    0 ≤ gibbsW E θ ε i := by
  unfold SelfReference.gibbsWeights
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (partitionFunction_pos E θ ε))

omit [DecidableEq Data] in
lemma gibbsWeights_pos
    (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) (i : Data) :
    0 < gibbsW E θ ε i := by
  unfold SelfReference.gibbsWeights
  exact div_pos (Real.exp_pos _) (partitionFunction_pos E θ ε)

omit [DecidableEq Data] in
lemma gibbsWeights_sum_one
    (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) :
    ∑ i : Data, gibbsW E θ ε i = 1 := by
  unfold SelfReference.gibbsWeights
  have hZne : partFn E θ ε ≠ 0 := partitionFunction_ne_zero E θ ε
  calc
    ∑ i : Data, Real.exp (-(E i θ) / ε) / partFn E θ ε
        = (∑ i : Data, Real.exp (-(E i θ) / ε)) / partFn E θ ε := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset Data))
                (f := fun i => Real.exp (-(E i θ) / ε))
                (a := partFn E θ ε))
    _ = partFn E θ ε / partFn E θ ε := by
          simp [SelfReference.partitionFunction]
    _ = 1 := by
          exact div_self hZne

noncomputable def gibbsProbabilityDist
    (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) : ProbabilityDist Data :=
  InfoGeometry.FinProb.of_fintype
    (fun i => ENNReal.ofReal (gibbsW E θ ε i))
    (by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sum_of_nonneg]
      · simpa using gibbsWeights_sum_one E θ ε
      · intro i hi
        exact gibbsWeights_nonneg E θ ε i)

omit [DecidableEq Data] in
@[simp] lemma gibbsProbabilityDist_apply
    (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) (i : Data) :
    gibbsProbabilityDist E θ ε i = ENNReal.ofReal (gibbsW E θ ε i) := by
  simp [gibbsProbabilityDist, InfoGeometry.FinProb.of_fintype]

omit [DecidableEq Data] in
theorem surprisal_gibbsWeights_eq_scaled_energy_add_logPartition
    (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) (i : Data) :
    InfoGeometry.surprisal (gibbsProbabilityDist E θ ε) i =
      E i θ / ε + Real.log (partFn E θ ε) := by
  rw [InfoGeometry.Core.surprisal_def, InfoGeometry.Core.logDensity_def]
  rw [gibbsProbabilityDist_apply]
  rw [ENNReal.toReal_ofReal (gibbsWeights_nonneg E θ ε i)]
  unfold SelfReference.gibbsWeights
  rw [Real.log_div (by positivity) (partitionFunction_ne_zero E θ ε)]
  rw [Real.log_exp]
  ring

omit [DecidableEq Data] in
/-- Generic Gibbs-mass outlier control for an energy observable. -/
theorem gibbs_outlier_control
    (E : Data → Theta → ℝ) (θ : Theta) (ε μ δ : ℝ)
    (hδ : 0 < δ) :
    (∑ i ∈ Finset.univ.filter (fun i : Data => δ ≤ |E i θ - μ|),
        gibbsW E θ ε i) * δ^2
      ≤
      ∑ i : Data, gibbsW E θ ε i * (E i θ - μ)^2 := by
  exact Gromov.Concentration.unnormalized_concentration_inequality
    (w := gibbsW E θ ε)
    (f := fun i : Data => E i θ)
    (μ := μ)
    (ε := δ)
    (h_nonneg := gibbsWeights_nonneg E θ ε)
    (h_eps := hδ)

end GibbsBridge

section ThermodynamicDefectBridge

variable {Data : Type} [Fintype Data] [Nonempty Data] [DecidableEq Data]

local notation "partFnR" => SelfReference.partitionFunction (Data := Data) (Theta := ℝ)
local notation "gibbsWR" => SelfReference.gibbsWeights (Data := Data) (Theta := ℝ)

/--
Read a temperature-regularized Hamiltonian defect as the fitting energy surface
fed into robust thermodynamic regression.
-/
def temperatureRegularizedEnergy
    (M : LogPotential.LegendreModel) (β : ℝ) (η : Data → ℝ) :
    Data → ℝ → ℝ :=
  fun i θ => M.temperatureRegularizedHamiltonian β θ (η i)

omit [Fintype Data] [Nonempty Data] [DecidableEq Data] in
@[simp] theorem temperatureRegularizedEnergy_apply
    (M : LogPotential.LegendreModel) (β : ℝ) (η : Data → ℝ)
    (i : Data) (θ : ℝ) :
    temperatureRegularizedEnergy M β η i θ =
      M.temperatureRegularizedHamiltonian β θ (η i) := rfl

omit [Nonempty Data] [DecidableEq Data] in
@[simp] theorem gibbsWeights_temperatureRegularizedEnergy
    (M : LogPotential.LegendreModel) (β ε θ : ℝ) (η : Data → ℝ) (i : Data) :
    gibbsWR (temperatureRegularizedEnergy M β η) θ ε i =
      Real.exp (-(M.temperatureRegularizedHamiltonian β θ (η i)) / ε) /
        partFnR (temperatureRegularizedEnergy M β η) θ ε := by
  rfl

omit [DecidableEq Data] in
theorem surprisal_temperatureRegularizedEnergy
    (M : LogPotential.LegendreModel) (β ε θ : ℝ) (η : Data → ℝ) (i : Data) :
    InfoGeometry.surprisal
        (gibbsProbabilityDist (Data := Data) (Theta := ℝ)
          (temperatureRegularizedEnergy M β η) θ ε) i =
      M.temperatureRegularizedHamiltonian β θ (η i) / ε +
        Real.log (partFnR (temperatureRegularizedEnergy M β η) θ ε) := by
  simpa [temperatureRegularizedEnergy] using
    (surprisal_gibbsWeights_eq_scaled_energy_add_logPartition
      (Data := Data) (Theta := ℝ)
      (E := temperatureRegularizedEnergy M β η) (θ := θ) (ε := ε) (i := i))

omit [DecidableEq Data] in
theorem surprisal_temperatureRegularizedEnergy_centered_eq_scaled_defect
    (M : LogPotential.LegendreModel) (β ε θ : ℝ) (η : Data → ℝ) (i : Data) :
    InfoGeometry.surprisal
        (gibbsProbabilityDist (Data := Data) (Theta := ℝ)
          (temperatureRegularizedEnergy M β η) θ ε) i -
      Real.log (partFnR (temperatureRegularizedEnergy M β η) θ ε) =
        M.temperatureRegularizedHamiltonian β θ (η i) / ε := by
  rw [surprisal_temperatureRegularizedEnergy]
  ring

omit [DecidableEq Data] in
theorem temperatureRegularizedEnergy_outlier_control
    (M : LogPotential.LegendreModel) (β ε θ μ δ : ℝ) (η : Data → ℝ)
    (hδ : 0 < δ) :
    (∑ i ∈ Finset.univ.filter
        (fun i : Data => δ ≤ |M.temperatureRegularizedHamiltonian β θ (η i) - μ|),
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i) * δ^2
      ≤
      ∑ i : Data,
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i *
          (M.temperatureRegularizedHamiltonian β θ (η i) - μ)^2 := by
  simpa [temperatureRegularizedEnergy] using
    (gibbs_outlier_control
      (Data := Data) (Theta := ℝ)
      (E := temperatureRegularizedEnergy M β η)
      (θ := θ) (ε := ε) (μ := μ) (δ := δ) hδ)

omit [DecidableEq Data] in
theorem surprisal_temperatureRegularizedEnergy_abs_centered_eq_scaled_abs_defect
    (M : LogPotential.LegendreModel) (β ε θ : ℝ) (η : Data → ℝ) (i : Data)
    (hε : 0 < ε) :
    |InfoGeometry.surprisal
        (gibbsProbabilityDist (Data := Data) (Theta := ℝ)
          (temperatureRegularizedEnergy M β η) θ ε) i -
      Real.log (partFnR (temperatureRegularizedEnergy M β η) θ ε)| =
        |M.temperatureRegularizedHamiltonian β θ (η i)| / ε := by
  rw [surprisal_temperatureRegularizedEnergy_centered_eq_scaled_defect
    (Data := Data) (M := M) (β := β) (ε := ε) (θ := θ) (η := η) (i := i)]
  rw [abs_div, abs_of_pos hε]

omit [DecidableEq Data] in
theorem surprisal_temperatureRegularizedEnergy_threshold_iff
    (M : LogPotential.LegendreModel) (β ε θ δ : ℝ) (η : Data → ℝ) (i : Data)
    (hε : 0 < ε) :
    δ ≤ |InfoGeometry.surprisal
        (gibbsProbabilityDist (Data := Data) (Theta := ℝ)
          (temperatureRegularizedEnergy M β η) θ ε) i -
      Real.log (partFnR (temperatureRegularizedEnergy M β η) θ ε)| ↔
      ε * δ ≤ |M.temperatureRegularizedHamiltonian β θ (η i)| := by
  rw [surprisal_temperatureRegularizedEnergy_abs_centered_eq_scaled_abs_defect
    (Data := Data) (M := M) (β := β) (ε := ε) (θ := θ) (η := η) (i := i) hε]
  simpa [mul_comm] using (le_div_iff₀ hε)

omit [DecidableEq Data] in
theorem surprisal_temperatureRegularizedEnergy_outlier_weight_eq_scaled_defect_outlier_weight
    (M : LogPotential.LegendreModel) (β ε θ δ : ℝ) (η : Data → ℝ)
    (hε : 0 < ε) :
    (∑ i ∈ Finset.univ.filter
        (fun i : Data =>
          δ ≤ |InfoGeometry.surprisal
            (gibbsProbabilityDist (Data := Data) (Theta := ℝ)
              (temperatureRegularizedEnergy M β η) θ ε) i -
            Real.log (partFnR (temperatureRegularizedEnergy M β η) θ ε)|),
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i) =
      ∑ i ∈ Finset.univ.filter
        (fun i : Data => ε * δ ≤ |M.temperatureRegularizedHamiltonian β θ (η i)|),
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i := by
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using
    (surprisal_temperatureRegularizedEnergy_threshold_iff
      (Data := Data) (M := M) (β := β) (ε := ε) (θ := θ) (δ := δ) (η := η) (i := i) hε)

omit [DecidableEq Data] in
theorem surprisal_temperatureRegularizedEnergy_outlier_control
    (M : LogPotential.LegendreModel) (β ε θ δ : ℝ) (η : Data → ℝ)
    (hδ : 0 < δ) :
    (∑ i ∈ Finset.univ.filter
        (fun i : Data =>
          δ ≤ |InfoGeometry.surprisal
            (gibbsProbabilityDist (Data := Data) (Theta := ℝ)
              (temperatureRegularizedEnergy M β η) θ ε) i -
            Real.log (partFnR (temperatureRegularizedEnergy M β η) θ ε)|),
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i) * δ^2
      ≤
      ∑ i : Data,
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i *
          (InfoGeometry.surprisal
            (gibbsProbabilityDist (Data := Data) (Theta := ℝ)
              (temperatureRegularizedEnergy M β η) θ ε) i -
            Real.log (partFnR (temperatureRegularizedEnergy M β η) θ ε))^2 := by
  exact Gromov.Concentration.unnormalized_concentration_inequality
    (w := gibbsWR (temperatureRegularizedEnergy M β η) θ ε)
    (f := fun i : Data =>
      InfoGeometry.surprisal
        (gibbsProbabilityDist (Data := Data) (Theta := ℝ)
          (temperatureRegularizedEnergy M β η) θ ε) i)
    (μ := Real.log (partFnR (temperatureRegularizedEnergy M β η) θ ε))
    (ε := δ)
    (h_nonneg := by
      intro i
      exact gibbsWeights_nonneg
        (Data := Data) (Theta := ℝ)
        (E := temperatureRegularizedEnergy M β η) (θ := θ) (ε := ε) i)
    (h_eps := hδ)

omit [DecidableEq Data] in
theorem temperatureRegularizedEnergy_abs_outlier_control
    (M : LogPotential.LegendreModel) (β ε θ δ : ℝ) (η : Data → ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    (∑ i ∈ Finset.univ.filter
        (fun i : Data => ε * δ ≤ |M.temperatureRegularizedHamiltonian β θ (η i)|),
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i) * (ε * δ)^2
      ≤
      ∑ i : Data,
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i *
          (M.temperatureRegularizedHamiltonian β θ (η i))^2 := by
  simpa [sub_zero] using
    (temperatureRegularizedEnergy_outlier_control
      (Data := Data) (M := M) (β := β) (ε := ε) (θ := θ) (μ := 0) (δ := ε * δ)
      (η := η) (mul_pos hε hδ))

omit [DecidableEq Data] in
theorem surprisal_temperatureRegularizedEnergy_outlier_control_rescaled_to_defect
    (M : LogPotential.LegendreModel) (β ε θ δ : ℝ) (η : Data → ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    (∑ i ∈ Finset.univ.filter
        (fun i : Data =>
          δ ≤ |InfoGeometry.surprisal
            (gibbsProbabilityDist (Data := Data) (Theta := ℝ)
              (temperatureRegularizedEnergy M β η) θ ε) i -
            Real.log (partFnR (temperatureRegularizedEnergy M β η) θ ε)|),
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i) * (ε * δ)^2
      ≤
      ∑ i : Data,
        gibbsWR (temperatureRegularizedEnergy M β η) θ ε i *
          (M.temperatureRegularizedHamiltonian β θ (η i))^2 := by
  rw [surprisal_temperatureRegularizedEnergy_outlier_weight_eq_scaled_defect_outlier_weight
    (Data := Data) (M := M) (β := β) (ε := ε) (θ := θ) (δ := δ) (η := η) hε]
  exact temperatureRegularizedEnergy_abs_outlier_control
    (Data := Data) (M := M) (β := β) (ε := ε) (θ := θ) (δ := δ) (η := η) hε hδ

end ThermodynamicDefectBridge

end InfoGeometry.Probability
