import InfoGeometry.Arithmetic.FiniteFockNative
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.FiniteFockParity

open InfoGeometry.Arithmetic.FiniteFockNative

def parityScalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (occ : State ι) : ℂ :=
  ∏ i : ι, if occ i then (-1 : ℂ) else 1

def parityLinear {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Vec ι →ₗ[ℂ] Vec ι where
  toFun ψ := fun occ => parityScalar occ * ψ occ
  map_add' ψ φ := by
    funext occ
    simp only [Pi.add_apply]
    ring
  map_smul' c ψ := by
    funext occ
    simp only [Pi.smul_apply]
    change parityScalar occ * (c * ψ occ) = c * (parityScalar occ * ψ occ)
    ring

theorem parityScalar_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (occ : State ι) : parityScalar occ * parityScalar occ = 1 := by
  unfold parityScalar
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _hi
  by_cases h : occ i <;> simp [h]

theorem parityLinear_involutive
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (parityLinear : Vec ι →ₗ[ℂ] Vec ι).comp parityLinear = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp only [LinearMap.comp_apply, parityLinear]
  change parityScalar occ * (parityScalar occ * ψ occ) = ψ occ
  rw [← mul_assoc, parityScalar_sq]
  simp

theorem parityLinear_commute_gibbs
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    (parityLinear : Vec ι →ₗ[ℂ] Vec ι).comp (gibbsLinear ε β) =
      (gibbsLinear ε β).comp parityLinear := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [LinearMap.comp_apply, parityLinear, gibbsLinear]
  ring

theorem parityLinear_commute_numberProjector
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    (parityLinear : Vec ι →ₗ[ℂ] Vec ι).comp (numberProjectorLinear i) =
      (numberProjectorLinear i).comp parityLinear := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [LinearMap.comp_apply, parityLinear, numberProjectorLinear]

theorem parityLinear_commute_hamiltonian
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ι → ℝ) :
    (parityLinear : Vec ι →ₗ[ℂ] Vec ι).comp (hamiltonianLinear ε) =
      (hamiltonianLinear ε).comp parityLinear := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [LinearMap.comp_apply, parityLinear, hamiltonianLinear]
  ring

theorem parityLinear_commute_totalNumber
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (parityLinear : Vec ι →ₗ[ℂ] Vec ι).comp totalNumberLinear =
      totalNumberLinear.comp parityLinear := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [LinearMap.comp_apply, parityLinear, totalNumberLinear,
    numberProjectorLinear]

theorem parityLinear_commute_grandHamiltonian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (μ : ℝ) :
    (parityLinear : Vec ι →ₗ[ℂ] Vec ι).comp
        (grandHamiltonianLinear ε μ) =
      (grandHamiltonianLinear ε μ).comp parityLinear := by
  rw [grandHamiltonianLinear, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_smul, LinearMap.smul_comp,
    parityLinear_commute_hamiltonian,
    parityLinear_commute_totalNumber]

def signedGibbsLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) : Vec ι →ₗ[ℂ] Vec ι :=
  parityLinear.comp (gibbsLinear ε β)

theorem signedGibbsLinear_commute_totalNumber
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    (signedGibbsLinear ε β).comp totalNumberLinear =
      totalNumberLinear.comp (signedGibbsLinear ε β) := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [signedGibbsLinear, LinearMap.comp_apply, parityLinear,
    gibbsLinear, totalNumberLinear, numberProjectorLinear]

theorem signedGibbsLinear_commute_hamiltonian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    (signedGibbsLinear ε β).comp (hamiltonianLinear ε) =
      (hamiltonianLinear ε).comp (signedGibbsLinear ε β) := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [signedGibbsLinear, LinearMap.comp_apply, parityLinear,
    gibbsLinear, hamiltonianLinear]
  ring

theorem signedGibbsLinear_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) (ψ : Vec ι) (occ : State ι) :
    signedGibbsLinear ε β ψ occ =
      parityScalar occ * (Real.exp (-β * energy ε occ) : ℂ) * ψ occ := by
  simp [signedGibbsLinear, parityLinear, gibbsLinear, LinearMap.comp_apply,
    mul_assoc]

theorem trace_signedGibbsLinear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    LinearMap.trace ℂ (Vec ι) (signedGibbsLinear ε β) =
      ∑ occ : State ι,
        parityScalar occ * (Real.exp (-β * energy ε occ) : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (State ι))]
  simp [signedGibbsLinear, parityLinear, gibbsLinear, Matrix.trace]

theorem trace_signedGibbsLinear_eq_product
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (β : ℝ) :
    LinearMap.trace ℂ (Vec ι) (signedGibbsLinear ε β) =
      ∏ i : ι, (1 - (localBoltzmann (ε i) β : ℂ)) := by
  classical
  rw [trace_signedGibbsLinear]
  have hpointwise : ∀ occ : State ι,
      parityScalar occ * (Real.exp (-β * energy ε occ) : ℂ) =
        ∏ i : ι,
          if occ i then (-localBoltzmann (ε i) β : ℂ) else 1 := by
    intro occ
    rw [exp_neg_energy_eq_product]
    unfold parityScalar
    push_cast
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _hi
    by_cases h : occ i <;> simp [h]
  simp_rw [hpointwise]
  have hlocal : ∀ i : ι,
      ((∑ b : Bool, if b then -localBoltzmann (ε i) β else 1) : ℂ) =
        1 - (localBoltzmann (ε i) β : ℂ) := by
    intro i
    simp
    ring
  rw [← Finset.prod_congr rfl (fun i _hi => hlocal i)]
  rw [← Finset.sum_prod_piFinset]
  rw [Fintype.piFinset_univ]

theorem trace_parityLinear_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    LinearMap.trace ℂ (Vec ι) parityLinear = 0 := by
  have h := trace_signedGibbsLinear_eq_product
    (ε := fun _ : ι => 0) (β := 0)
  simpa [signedGibbsLinear, gibbsLinear, localBoltzmann] using h

end InfoGeometry.Arithmetic.FiniteFockParity
