import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.InformationTheory.KullbackLeibler.Basic

open scoped BigOperators ENNReal
open MeasureTheory

namespace JaynesRNMaxEnt

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
## 1. Constraints as moments (expectations)
We package a finite family of observables `f i : Ω → ℝ` with target moments `d i : ℝ`.
-/

/-- A finite family of moment constraints `∫ f_i dP = d_i`. -/
structure MomentFamily (ι : Type*) [Fintype ι] where
  f : ι → Ω → ℝ
  measurable_f : ∀ i, Measurable (f i)
  d : ι → ℝ

/-- A probability measure satisfies all the moment constraints. -/
def Satisfies {ι : Type*} [Fintype ι] (C : MomentFamily (Ω := Ω) ι)
    (P : ProbabilityMeasure Ω) : Prop :=
  ∀ i, (∫ x, C.f i x ∂(P : Measure Ω)) = C.d i

/-- Integrability-aware satisfaction of all moment constraints. -/
def SatisfiesIntegrable {ι : Type*} [Fintype ι] (C : MomentFamily (Ω := Ω) ι)
    (P : ProbabilityMeasure Ω) : Prop :=
  ∀ i, Integrable (C.f i) (P : Measure Ω) ∧
    (∫ x, C.f i x ∂(P : Measure Ω)) = C.d i

/-- The feasible set of probability measures. -/
def FeasibleSet {ι : Type*} [Fintype ι] (C : MomentFamily (Ω := Ω) ι) :
    Set (ProbabilityMeasure Ω) :=
  {P | Satisfies (Ω := Ω) C P}

/-- Integrability-aware feasible set of probability measures. -/
def FeasibleSetIntegrable {ι : Type*} [Fintype ι] (C : MomentFamily (Ω := Ω) ι) :
    Set (ProbabilityMeasure Ω) :=
  {P | SatisfiesIntegrable (Ω := Ω) C P}

/-- Integrability-aware constraint satisfaction implies plain satisfaction. -/
lemma SatisfiesIntegrable.satisfies
    {ι : Type*} [Fintype ι]
    {C : MomentFamily (Ω := Ω) ι} {P : ProbabilityMeasure Ω}
    (hP : SatisfiesIntegrable (Ω := Ω) C P) :
    Satisfies (Ω := Ω) C P := by
  intro i
  exact (hP i).2

/-- The integrable feasible set is contained in the plain feasible set. -/
lemma FeasibleSetIntegrable_subset_FeasibleSet
    {ι : Type*} [Fintype ι]
    (C : MomentFamily (Ω := Ω) ι) :
    FeasibleSetIntegrable (Ω := Ω) C ⊆ FeasibleSet (Ω := Ω) C := by
  intro P hP
  exact (SatisfiesIntegrable.satisfies (Ω := Ω) hP)

/-!
## 2. Objective = KL divergence relative to a prior `μ₀`

Jaynes’ “invariant measure” is the prior `μ₀`.
MaxEnt w.r.t. `μ₀` is Min-KL: minimize `kl_div P μ₀`.
-/

variable (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀]

/-- KL divergence objective: `D_KL(P || μ₀)` (value in `ℝ≥0∞`). -/
noncomputable def objectiveKL (P : ProbabilityMeasure Ω) : ℝ≥0∞ :=
  InformationTheory.klDiv (P : Measure Ω) μ₀

/-!
## 3. Gibbs / exponential-family solution via exponential tilting

Given multipliers `lam : ι → ℝ`, define the Jaynes potential
`Φ(x) = - ∑ᵢ lamᵢ fᵢ(x)` and set `P_lam := μ₀.tilted Φ`.
-/

section Gibbs

variable {ι : Type*} [Fintype ι]
variable (C : MomentFamily (Ω := Ω) ι)

/-- Jaynes/Gibbs potential `Φ(x) = -∑ᵢ lamᵢ fᵢ(x)`. -/
noncomputable def potential (lam : ι → ℝ) : Ω → ℝ :=
  fun x => -∑ i, (lam i) * (C.f i x)

/-- Partition function `Z(lam) = ∫ exp(Φ(x)) dμ₀`. -/
noncomputable def partitionFunction (lam : ι → ℝ) : ℝ :=
  ∫ x, Real.exp (potential (C := C) lam x) ∂μ₀

/-- Finiteness hypothesis for the partition function integrand. -/
def PartitionIntegrable (lam : ι → ℝ) : Prop :=
  Integrable (fun x => Real.exp (potential (C := C) lam x)) μ₀

/-- The Gibbs measure (not yet packaged as `ProbabilityMeasure`). -/
noncomputable def gibbsMeasure (lam : ι → ℝ) : Measure Ω :=
  μ₀.tilted (potential (C := C) lam)

omit [IsProbabilityMeasure μ₀] in theorem gibbsMeasure_ac (lam : ι → ℝ) :
    gibbsMeasure (μ₀ := μ₀) (C := C) lam ≪ μ₀ := by
  simpa [gibbsMeasure] using
    (MeasureTheory.tilted_absolutelyContinuous μ₀ (potential (C := C) lam))

omit [IsProbabilityMeasure μ₀] in theorem aemeasurable_potential (lam : ι → ℝ) :
    AEMeasurable (potential (C := C) lam) μ₀ := by
  classical
  have hmeas : Measurable (potential (C := C) lam) := by
    unfold potential
    simpa using
      ((Finset.measurable_fun_sum (s := (Finset.univ : Finset ι))
        (f := fun i : ι => fun x : Ω => (lam i) * C.f i x)
        (by
          intro i hi
          exact (C.measurable_f i).const_mul (lam i))).neg)
  exact hmeas.aemeasurable

/--
RN-derivative of the Gibbs measure w.r.t. the prior:
`d(μ₀.tilted Φ)/dμ₀ = exp(Φ)/Z` almost everywhere.
-/
theorem rnDeriv_gibbsMeasure_eq (lam : ι → ℝ) :
    (gibbsMeasure (μ₀ := μ₀) (C := C) lam).rnDeriv μ₀
      =ᵐ[μ₀] fun x =>
        ENNReal.ofReal (Real.exp (potential (C := C) lam x)
          / partitionFunction (μ₀ := μ₀) (C := C) lam) := by
  simpa [gibbsMeasure, partitionFunction] using
    (MeasureTheory.rnDeriv_tilted_left_self (μ := μ₀)
      (f := potential (C := C) lam)
      (aemeasurable_potential (μ₀ := μ₀) (C := C) lam))

omit [IsProbabilityMeasure μ₀] in
/-- The Gibbs partition function is nonnegative. -/
lemma partitionFunction_nonneg (lam : ι → ℝ) :
    0 ≤ partitionFunction (μ₀ := μ₀) (C := C) lam := by
  unfold partitionFunction
  exact integral_nonneg (fun x => by positivity)

/-- The Gibbs partition function is strictly positive when the exponential tilt is integrable. -/
theorem partitionFunction_pos (lam : ι → ℝ)
    (hInt : PartitionIntegrable (μ₀ := μ₀) (C := C) lam) :
    0 < partitionFunction (μ₀ := μ₀) (C := C) lam := by
  simpa [partitionFunction, PartitionIntegrable] using
    (MeasureTheory.integral_exp_pos
      (μ := μ₀)
      (f := potential (C := C) lam)
      hInt)

/-- Scalar RN-density form for the Gibbs measure (`toReal` version). -/
theorem rnDeriv_gibbsMeasure_toReal_eq (lam : ι → ℝ) :
    (fun x => ((gibbsMeasure (μ₀ := μ₀) (C := C) lam).rnDeriv μ₀ x).toReal)
      =ᵐ[μ₀] fun x =>
        Real.exp (potential (C := C) lam x)
          / partitionFunction (μ₀ := μ₀) (C := C) lam := by
  filter_upwards [rnDeriv_gibbsMeasure_eq (μ₀ := μ₀) (C := C) lam] with x hx
  have hnonneg :
      0 ≤ Real.exp (potential (C := C) lam x)
        / partitionFunction (μ₀ := μ₀) (C := C) lam := by
    exact div_nonneg (le_of_lt (Real.exp_pos _))
      (partitionFunction_nonneg (μ₀ := μ₀) (C := C) lam)
  calc
    ((gibbsMeasure (μ₀ := μ₀) (C := C) lam).rnDeriv μ₀ x).toReal
        = (ENNReal.ofReal
            (Real.exp (potential (C := C) lam x)
              / partitionFunction (μ₀ := μ₀) (C := C) lam)).toReal := by
              simp [hx]
    _ = Real.exp (potential (C := C) lam x)
          / partitionFunction (μ₀ := μ₀) (C := C) lam := by
            exact ENNReal.toReal_ofReal hnonneg

/--
If `exp(Φ)` is integrable, the tilted measure is a probability measure.
We bundle it as `ProbabilityMeasure Ω`.
-/
noncomputable def gibbs (lam : ι → ℝ)
    (hInt : Integrable (fun x => Real.exp (potential (C := C) lam x)) μ₀) :
    ProbabilityMeasure Ω := by
  refine ⟨gibbsMeasure (μ₀ := μ₀) (C := C) lam, ?_⟩
  simpa [gibbsMeasure] using
    (MeasureTheory.isProbabilityMeasure_tilted
      (μ := μ₀) (f := potential (C := C) lam) hInt)

end Gibbs

/-!
## 4. “MaxEnt = MinKL” theorem (statement)

The full variational proof (existence/uniqueness + Lagrange multipliers) is substantial.
-/

/-- Proposition interface expressing that Gibbs minimizes KL on the feasible set. -/
def gibbs_minimizes_kl
    {ι : Type*} [Fintype ι]
    (C : MomentFamily (Ω := Ω) ι)
    (lam : ι → ℝ)
    (hInt : Integrable (fun x => Real.exp (potential (C := C) lam x)) μ₀)
    (hFeas : gibbs (μ₀ := μ₀) (C := C) lam hInt ∈ FeasibleSetIntegrable (Ω := Ω) C) :
    Prop :=
  let _ := hFeas
  ∀ P : ProbabilityMeasure Ω,
    P ∈ FeasibleSetIntegrable (Ω := Ω) C →
      objectiveKL (μ₀ := μ₀) (gibbs (μ₀ := μ₀) (C := C) lam hInt)
        ≤ objectiveKL (μ₀ := μ₀) P

/-- CamelCase alias for the Gibbs-minimizes-KL proposition interface. -/
def GibbsMinimizesKL
    {ι : Type*} [Fintype ι]
    (C : MomentFamily (Ω := Ω) ι)
    (lam : ι → ℝ)
    (hInt : Integrable (fun x => Real.exp (potential (C := C) lam x)) μ₀)
    (hFeas : gibbs (μ₀ := μ₀) (C := C) lam hInt ∈ FeasibleSetIntegrable (Ω := Ω) C) :
    Prop :=
  gibbs_minimizes_kl (μ₀ := μ₀) C lam hInt hFeas

end JaynesRNMaxEnt
