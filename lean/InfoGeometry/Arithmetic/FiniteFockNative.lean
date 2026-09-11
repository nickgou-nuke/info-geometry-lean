import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.FiniteFockNative

abbrev State (ι : Type*) := ι → Bool
abbrev Vec (ι : Type*) := State ι → ℂ

def energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (occ : State ι) : ℝ :=
  ∑ i, if occ i then ε i else 0

def localBoltzmann (εi β : ℝ) : ℝ :=
  Real.exp (-β * εi)

def numberProjectorLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) : Vec ι →ₗ[ℂ] Vec ι where
  toFun ψ := fun occ => (if occ i then (1 : ℂ) else 0) * ψ occ
  map_add' ψ φ := by
    funext occ
    simp only [Pi.add_apply]
    ring

  map_smul' c ψ := by
    funext occ
    simp only [Pi.smul_apply]
    change (if occ i then (1 : ℂ) else 0) * (c * ψ occ) =
      c * ((if occ i then (1 : ℂ) else 0) * ψ occ)
    ring

def gibbsLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    Vec ι →ₗ[ℂ] Vec ι where
  toFun ψ := fun occ => (Real.exp (-β * energy ε occ) : ℂ) * ψ occ
  map_add' ψ φ := by
    funext occ
    simp only [Pi.add_apply]
    ring

  map_smul' c ψ := by
    funext occ
    simp only [Pi.smul_apply]
    change (Real.exp (-β * energy ε occ) : ℂ) * (c * ψ occ) =
      c * ((Real.exp (-β * energy ε occ) : ℂ) * ψ occ)
    ring

def grandGibbsLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β μ : ℝ) : Vec ι →ₗ[ℂ] Vec ι :=
  gibbsLinear (fun i => ε i - μ) β

def hamiltonianLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) :
    Vec ι →ₗ[ℂ] Vec ι where
  toFun ψ := fun occ => (energy ε occ : ℂ) * ψ occ
  map_add' ψ φ := by
    funext occ
    simp only [Pi.add_apply]
    ring

  map_smul' c ψ := by
    funext occ
    simp only [Pi.smul_apply]
    change (energy ε occ : ℂ) * (c * ψ occ) =
      c * ((energy ε occ : ℂ) * ψ occ)
    ring

def totalNumberLinear {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Vec ι →ₗ[ℂ] Vec ι :=
  ∑ i : ι, numberProjectorLinear i

def grandHamiltonianLinear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (μ : ℝ) : Vec ι →ₗ[ℂ] Vec ι :=
  hamiltonianLinear ε - (μ : ℂ) • totalNumberLinear

theorem energy_sub_const
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (μ : ℝ) (occ : State ι) :
    energy (fun i => ε i - μ) occ =
      energy ε occ - μ * ∑ i : ι, if occ i then (1 : ℝ) else 0 := by
  unfold energy
  change (∑ i : ι, if occ i then ε i - μ else 0) = _
  rw [show (∑ i : ι, if occ i then ε i - μ else 0) =
      ∑ i : ι, ((if occ i then ε i else 0) -
        (if occ i then μ else 0)) by
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases h : occ i <;> simp [h]]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i : ι, if occ i then μ else 0) =
      μ * ∑ i : ι, if occ i then (1 : ℝ) else 0 by
        calc
          (∑ i : ι, if occ i then μ else 0) =
              ∑ i : ι, μ * (if occ i then (1 : ℝ) else 0) := by
                apply Finset.sum_congr rfl
                intro i _hi
                by_cases h : occ i <;> simp [h]
          _ = μ * ∑ i : ι, if occ i then (1 : ℝ) else 0 := by
            rw [Finset.mul_sum]]

theorem grandHamiltonianLinear_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (μ : ℝ) (ψ : Vec ι) (occ : State ι) :
    grandHamiltonianLinear ε μ ψ occ =
      (energy ε occ : ℂ) * ψ occ -
        (μ : ℂ) * ∑ i : ι,
          (if occ i then (1 : ℂ) else 0) * ψ occ := by
  simp [grandHamiltonianLinear, hamiltonianLinear, totalNumberLinear,
    numberProjectorLinear]

theorem hamiltonianLinear_commute_totalNumber
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) :
    (hamiltonianLinear ε).comp totalNumberLinear =
      totalNumberLinear.comp (hamiltonianLinear ε) := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [LinearMap.comp_apply, hamiltonianLinear, totalNumberLinear,
    numberProjectorLinear]

theorem grandHamiltonianLinear_commute_totalNumber
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (μ : ℝ) :
    (grandHamiltonianLinear ε μ).comp totalNumberLinear =
      totalNumberLinear.comp (grandHamiltonianLinear ε μ) := by
  rw [grandHamiltonianLinear, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_smul, LinearMap.smul_comp,
    hamiltonianLinear_commute_totalNumber]

theorem gibbsLinear_commute_totalNumber
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    (gibbsLinear ε β).comp totalNumberLinear =
      totalNumberLinear.comp (gibbsLinear ε β) := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [LinearMap.comp_apply, gibbsLinear, totalNumberLinear,
    numberProjectorLinear]

theorem numberProjectorLinear_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    (numberProjectorLinear i).comp (numberProjectorLinear i) =
      numberProjectorLinear i := by
  apply LinearMap.ext
  intro ψ
  funext occ
  unfold numberProjectorLinear
  by_cases h : occ i <;> simp [h]

theorem numberProjectorLinear_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (numberProjectorLinear i).comp (numberProjectorLinear j) =
      (numberProjectorLinear j).comp (numberProjectorLinear i) := by
  apply LinearMap.ext
  intro ψ
  funext occ
  unfold numberProjectorLinear
  by_cases hi : occ i <;> by_cases hj : occ j <;> simp [hi, hj]

theorem hamiltonianLinear_eq_sum_numberProjector
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ι → ℝ) :
    hamiltonianLinear ε =
      ∑ i : ι, (ε i : ℂ) • numberProjectorLinear i := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp only [hamiltonianLinear, LinearMap.sum_apply, LinearMap.smul_apply]
  simp [numberProjectorLinear]
  change (energy ε occ : ℂ) * ψ occ =
    ∑ i : ι, (if occ i then (ε i : ℂ) * ψ occ else 0)
  rw [show (energy ε occ : ℂ) =
      ∑ i : ι, (if occ i then (ε i : ℂ) else 0) by
        simp only [energy]
        change Complex.ofRealHom (∑ i : ι,
          (if occ i then ε i else 0)) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases h : occ i <;> simp [h]]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases h : occ i <;> simp [h]

theorem trace_gibbsLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    LinearMap.trace ℂ (Vec ι) (gibbsLinear ε β) =
      ∑ occ : State ι, (Real.exp (-β * energy ε occ) : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (State ι))]
  simp [gibbsLinear, Matrix.trace]

theorem trace_hamiltonianLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) :
    LinearMap.trace ℂ (Vec ι) (hamiltonianLinear ε) =
      ∑ occ : State ι, (energy ε occ : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (State ι))]
  simp [hamiltonianLinear, Matrix.trace]

theorem exp_neg_energy_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) (occ : State ι) :
    Real.exp (-β * energy ε occ) =
      ∏ i, if occ i then localBoltzmann (ε i) β else 1 := by
  classical
  unfold energy localBoltzmann
  rw [show -β * (∑ i, if occ i then ε i else 0) =
      ∑ i, (-β) * (if occ i then ε i else 0) by rw [Finset.mul_sum]]
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  by_cases h : occ i <;> simp [h]

theorem trace_gibbsLinear_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    LinearMap.trace ℂ (Vec ι) (gibbsLinear ε β) =
      ∏ i, (1 + (localBoltzmann (ε i) β : ℂ)) := by
  classical
  rw [trace_gibbsLinear]
  norm_cast
  simp_rw [exp_neg_energy_eq_product]
  have hlocal : ∀ i : ι,
      ((∑ b : Bool, if b then localBoltzmann (ε i) β else 1) : ℝ) =
        1 + localBoltzmann (ε i) β := by
    intro i
    simp
    ring
  rw [← Finset.prod_congr rfl (fun i _hi => hlocal i)]
  rw [← Finset.sum_prod_piFinset]
  rw [Fintype.piFinset_univ]

theorem trace_gibbsLinear_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    LinearMap.trace ℂ (Vec ι) (gibbsLinear ε β) ≠ 0 := by
  rw [trace_gibbsLinear_eq_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  have hpos : 0 < 1 + localBoltzmann (ε i) β := by
    unfold localBoltzmann
    positivity
  exact_mod_cast hpos.ne'

theorem trace_grandGibbsLinear_eq_product
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β μ : ℝ) :
    LinearMap.trace ℂ (Vec ι) (grandGibbsLinear ε β μ) =
      ∏ i, (1 +
        (localBoltzmann (ε i - μ) β : ℂ)) := by
  exact trace_gibbsLinear_eq_product (fun i => ε i - μ) β

theorem trace_grandGibbsLinear_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β μ : ℝ) :
    LinearMap.trace ℂ (Vec ι) (grandGibbsLinear ε β μ) ≠ 0 := by
  exact trace_gibbsLinear_ne_zero (fun i => ε i - μ) β

end InfoGeometry.Arithmetic.FiniteFockNative
