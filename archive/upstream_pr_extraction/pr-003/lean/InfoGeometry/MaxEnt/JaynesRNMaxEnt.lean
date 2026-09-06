import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic.Measurability

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

/-- The feasible set of probability measures. -/
def FeasibleSet {ι : Type*} [Fintype ι] (C : MomentFamily (Ω := Ω) ι) :
    Set (ProbabilityMeasure Ω) :=
  {P | Satisfies (Ω := Ω) C P}

/-!
## 2. Objective = KL divergence relative to a prior `μ₀`

Jaynes’ “invariant measure” is the prior `μ₀`.
MaxEnt w.r.t. `μ₀` is Min-KL: minimize `klDiv P μ₀`.
-/

variable (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀]

/-- KL divergence objective: `D_KL(P || μ₀)` (value in `ℝ≥0∞`). -/
noncomputable def objectiveKL (P : ProbabilityMeasure Ω) : ℝ≥0∞ :=
  InformationTheory.klDiv (P : Measure Ω) μ₀

/-!
## 3. Gibbs / exponential-family solution via exponential tilting

Given multipliers `λ : ι → ℝ`, define the Jaynes potential
`Φ(x) = - ∑ᵢ λᵢ fᵢ(x)` and set `P_λ := μ₀.tilted Φ`.
-/

section Gibbs

variable {ι : Type*} [Fintype ι]
variable (C : MomentFamily (Ω := Ω) ι)

/-- Jaynes/Gibbs potential `Φ(x) = -∑ᵢ λᵢ fᵢ(x)`. -/
noncomputable def potential (lam : ι → ℝ) : Ω → ℝ :=
  fun x => -∑ i, (lam i) * (C.f i x)

/-- Partition function `Z(λ) = ∫ exp(Φ(x)) dμ₀`. -/
noncomputable def partitionFunction (lam : ι → ℝ) : ℝ :=
  ∫ x, Real.exp (potential (C := C) lam x) ∂μ₀

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

def gibbs_minimizes_kl
    {ι : Type*} [Fintype ι]
    (C : MomentFamily (Ω := Ω) ι)
    (lam : ι → ℝ)
    (hInt : Integrable (fun x => Real.exp (potential (C := C) lam x)) μ₀)
    (_hFeas : gibbs (μ₀ := μ₀) (C := C) lam hInt ∈ FeasibleSet (Ω := Ω) C) :
    Prop :=
  ∀ P : ProbabilityMeasure Ω,
    P ∈ FeasibleSet (Ω := Ω) C →
      objectiveKL (μ₀ := μ₀) (gibbs (μ₀ := μ₀) (C := C) lam hInt)
        ≤ objectiveKL (μ₀ := μ₀) P

def GibbsMinimizesKL
    {ι : Type*} [Fintype ι]
    (C : MomentFamily (Ω := Ω) ι)
    (lam : ι → ℝ)
    (hInt : Integrable (fun x => Real.exp (potential (C := C) lam x)) μ₀)
    (_hFeas : gibbs (μ₀ := μ₀) (C := C) lam hInt ∈ FeasibleSet (Ω := Ω) C) :
    Prop :=
  gibbs_minimizes_kl (μ₀ := μ₀) C lam hInt _hFeas

end JaynesRNMaxEnt
