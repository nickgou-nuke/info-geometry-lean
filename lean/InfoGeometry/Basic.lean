import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Basic

Foundational types and definitions for InfoGeometry.

## Main results
- `EmpiricalCounts`
- `ProbabilityDist`
- `partitionFunction`
- `relativeSurprisal`
- `logRNDensity`

-/


namespace InfoGeometry

open Finset
open scoped BigOperators

-- EmpiricalCounts: type for empirical counts on a finite set

structure EmpiricalCounts (α : Type) where
  count : α → ℕ

instance {α : Type} : CoeFun (EmpiricalCounts α) (fun _ => α → ℕ) where
  coe N := N.count


structure ProbabilityDist (α : Type) [Fintype α] where
  prob : α → ℝ
  sum_one : ∑ x, prob x = 1
  nonneg : ∀ x, 0 ≤ prob x

/-- Strict finite probability distribution: pointwise positivity. -/
structure StrictProbabilityDist (α : Type) [Fintype α] where
  prob : α → ℝ
  sum_one : ∑ x, prob x = 1
  pos : ∀ x, 0 < prob x

namespace StrictProbabilityDist

variable {α : Type} [Fintype α]

/-- Forgetful map to the non-strict distribution. -/
def toProbabilityDist (P : StrictProbabilityDist α) : ProbabilityDist α :=
  { prob := P.prob
    sum_one := P.sum_one
    nonneg := fun x => le_of_lt (P.pos x) }

instance : Coe (StrictProbabilityDist α) (ProbabilityDist α) :=
  ⟨toProbabilityDist⟩

@[simp] lemma toProbabilityDist_prob (P : StrictProbabilityDist α) (x : α) :
    (P.toProbabilityDist).prob x = P.prob x := rfl

@[simp] lemma prob_pos (P : StrictProbabilityDist α) (x : α) : 0 < P.prob x :=
  P.pos x

end StrictProbabilityDist

/-- Finite probability vectors (`FinProb`) kept for compatibility with older modules.

This is a thin, record-style finite probability type with the same field names
used across the repository (`toFun`, `nonneg`, `sum_eq_one`).  We provide
conversions to/from `ProbabilityDist` so callers can use either API.
-/
structure FinProb (α : Type*) [Fintype α] where
  toFun : α → ℝ
  nonneg : ∀ x, 0 ≤ toFun x
  sum_eq_one : ∑ x, toFun x = 1

instance {α : Type*} [Fintype α] : CoeFun (FinProb α) (fun _ => α → ℝ) where
  coe := FinProb.toFun

/-- `sum_eq_one` as a `simp` lemma for `FinProb`. -/
@[simp] lemma FinProb.sum_eq_one (p : FinProb α) : ∑ x, p.toFun x = 1 := p.sum_eq_one

/-- Convert `FinProb` → `ProbabilityDist` (core representation). -/
def FinProb.toProbabilityDist {α : Type*} [Fintype α] (p : FinProb α) : ProbabilityDist α :=
  { prob := p.toFun, sum_one := p.sum_eq_one, nonneg := p.nonneg }

/-- Convert `ProbabilityDist` → `FinProb` for compatibility. -/
def ProbabilityDist.toFinProb {α : Type*} [Fintype α] (P : ProbabilityDist α) : FinProb α :=
  { toFun := P.prob, nonneg := P.nonneg, sum_eq_one := P.sum_one }

instance {α : Type*} [Fintype α] : Coe (FinProb α) (ProbabilityDist α) := ⟨FinProb.toProbabilityDist⟩

/-!
  Note: All definitions below require [Fintype α] at use sites.
  Lean defines Real.log 0 = 0, so analytic theorems may require strict positivity of probabilities.
-/

variable {α : Type} [Fintype α]


/-- Expectation under a finite distribution. -/
noncomputable def expectation (P : ProbabilityDist α) (f : α → ℝ) : ℝ :=
  ∑ x, P.prob x * f x

/-- Log density (finite Radon–Nikodym derivative). -/
noncomputable def logDensity (P : ProbabilityDist α) (x : α) : ℝ :=
  Real.log (P.prob x)

/-- Negative log density (self-information). -/
noncomputable def surprisal (P : ProbabilityDist α) (x : α) : ℝ :=
  - logDensity P x

/-- Shannon entropy as expectation of surprisal. -/
noncomputable def entropy (P : ProbabilityDist α) : ℝ :=
  expectation P (surprisal P)

/-- Kullback–Leibler divergence as expectation of log-density difference. -/
noncomputable def klDiv (P Q : ProbabilityDist α) : ℝ :=
  expectation P (fun x => logDensity P x - logDensity Q x)



/-- Convenience: nonnegativity of probabilities. -/
@[simp]
lemma prob_nonneg (Q : ProbabilityDist α) (x : α) : 0 ≤ Q.prob x :=
  Q.nonneg x

end InfoGeometry
