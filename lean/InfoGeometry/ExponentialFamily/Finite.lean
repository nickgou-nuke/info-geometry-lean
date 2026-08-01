import Mathlib.Tactic
import InfoGeometry.Basic
import InfoGeometry.ExponentialFamily.Class

/-!

Finite Exponential Family

-/

namespace InfoGeometry.ExponentialFamily

open Finset
open scoped BigOperators

/-

BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

familyPartition_pos

familyDensity_eq

familyDensity_pos

familyNormalization

toFiniteExponentialFamily

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported verified premises.]

None.

BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields, witnesses, certificates, or renamed placeholders.]

None.
-/

def FiniteExponentialFamilyData (α : Type _) [Fintype α] : Type _ :=
  {p : ProbabilityDist α × (α → ℝ) //
    ∀ x, 0 < (p.1 x).toReal}

namespace FiniteExponentialFamilyData

/-- Native product projection for the base probability distribution. -/
abbrev base {α : Type _} [Fintype α]
    (F : FiniteExponentialFamilyData α) : ProbabilityDist α :=
  F.1.1

/-- Native product projection for the sufficient statistic. -/
abbrev stat {α : Type _} [Fintype α]
    (F : FiniteExponentialFamilyData α) : α → ℝ :=
  F.1.2

/-- Native subtype proof of strict positivity of the base distribution. -/
theorem base_pos {α : Type _} [Fintype α]
    (F : FiniteExponentialFamilyData α) :
    ∀ x, 0 < (F.base x).toReal :=
  F.2

end FiniteExponentialFamilyData

variable {α : Type _} [Fintype α]

noncomputable def familyPartition (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
  ∑ x, (F.base x).toReal * Real.exp (θ * F.stat x)

noncomputable def familyLogPartition (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
  Real.log (familyPartition F θ)

noncomputable def familyStatistic (F : FiniteExponentialFamilyData α) (x : α) (θ : ℝ) : ℝ :=
  θ * F.stat x + Real.log ((F.base x).toReal)

noncomputable def familyDensity (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) : ℝ :=
  (F.base x).toReal * Real.exp (θ * F.stat x) / familyPartition F θ

section Nonempty

variable [Nonempty α]

lemma familyPartition_pos (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    0 < familyPartition F θ := by
  unfold familyPartition
  exact
    Finset.sum_pos
      (fun x _ => mul_pos (F.base_pos x) (Real.exp_pos _))
      Finset.univ_nonempty

lemma familyDensity_eq (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    familyDensity F θ x =
    Real.exp (familyStatistic F x θ - familyLogPartition F θ) := by
  unfold familyDensity familyStatistic familyLogPartition
  have hZpos : 0 < familyPartition F θ := familyPartition_pos F θ
  have hbpos : 0 < (F.base x).toReal := F.base_pos x
  rw [Real.exp_sub, Real.exp_add]
  rw [Real.exp_log hbpos, Real.exp_log hZpos]
  simp [mul_comm]

lemma familyDensity_pos (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    0 < familyDensity F θ x := by
  unfold familyDensity
  exact div_pos
    (mul_pos (F.base_pos x) (Real.exp_pos _))
    (familyPartition_pos F θ)

lemma familyNormalization (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    ∑ x, familyDensity F θ x = 1 := by
  classical
  unfold familyDensity familyPartition
  have hZne : (∑ y : α, (F.base y).toReal * Real.exp (θ * F.stat y)) ≠ 0 :=
    ne_of_gt (by simpa [familyPartition] using familyPartition_pos F θ)
  calc
    ∑ x : α,
      (F.base x).toReal * Real.exp (θ * F.stat x) /
      (∑ y : α, (F.base y).toReal * Real.exp (θ * F.stat y))
        = (∑ x : α, (F.base x).toReal * Real.exp (θ * F.stat x)) /
          (∑ y : α, (F.base y).toReal * Real.exp (θ * F.stat y)) := by
      rw [Finset.sum_div]
    _ = 1 := by
      exact div_self hZne

noncomputable def toFiniteExponentialFamily (F : FiniteExponentialFamilyData α) :
    FiniteExponentialFamily α ℝ where
  statistic := familyStatistic F
  logPartition := familyLogPartition F
  density := familyDensity F
  density_eq := familyDensity_eq F
  normalization := familyNormalization F

end Nonempty

end InfoGeometry.ExponentialFamily
