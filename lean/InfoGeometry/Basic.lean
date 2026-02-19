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


structure ProbabilityDist (α : Type*) [Fintype α] where
  prob : α → ℝ
  sum_one : ∑ x, prob x = 1
  nonneg : ∀ x, 0 ≤ prob x

/-- Strict finite probability distribution: pointwise positivity. -/
structure StrictProbabilityDist (α : Type*) [Fintype α] where
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

/-- Mark the `sum_one` projection on `FinProb` as `simp`. -/
attribute [simp] FinProb.sum_one

/-- Convert `FinProb` → `ProbabilityDist` (core representation). -/
def FinProb.toProbabilityDist {α : Type*} [Fintype α] (p : FinProb α) : ProbabilityDist α :=
  { prob := p.toFun, sum_one := p.sum_one, nonneg := p.nonneg }

/-- Convert `ProbabilityDist` → `FinProb` for compatibility. -/
def ProbabilityDist.toFinProb {α : Type*} [Fintype α] (P : ProbabilityDist α) : FinProb α :=
  { toFun := P.prob, nonneg := P.nonneg, sum_one := P.sum_one }

instance {α : Type*} [Fintype α] : Coe (FinProb α) (ProbabilityDist α) := ⟨FinProb.toProbabilityDist⟩

/-- Normalize nonnegative weights into a `FinProb`. -/
noncomputable def normalize {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hZ : 0 < (∑ a, w a)) : FinProb α := by
  classical
  let Z : ℝ := ∑ a, w a
  have hZ0 : Z ≠ 0 := ne_of_gt hZ
  refine { toFun := fun a => w a / Z, nonneg := ?, sum_one := ? }
  · intro a; exact div_nonneg (hw a) (le_of_lt hZ)
  · calc
      (∑ a : α, w a / Z) = (∑ a : α, w a) / Z := by simp [div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := by simp [Z, hZ0]

/-- Point mass / Dirac distribution on a finite type. -/
noncomputable def dirac {α : Type*} [Fintype α] [DecidableEq α] (a0 : α) : FinProb α := by
  classical
  let w : α → ℝ := fun a => if a = a0 then (1 : ℝ) else 0
  have hw : ∀ a, 0 ≤ w a := by intro a; by_cases h : a = a0 <;> simp [w, h]
  have hZ : 0 < (∑ a, w a) := by simp [w]
  exact normalize (w := w) hw hZ

/-- In a finite probability vector some atom has strictly positive mass. -/
@[simp] lemma FinProb.exists_pos {α : Type*} [Fintype α] (q : FinProb α) : ∃ a, 0 < q a := by
  classical
  by_contra h
  push_neg at h
  have hzero : ∀ a, q a = 0 := by
    intro a
    have : q a ≤ 0 := h a
    have : q a = 0 := le_antisymm this (q.nonneg a)
    exact this
  have : (∑ a, q a) = 0 := by simp [hzero]
  linarith [q.sum_one, this]

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
