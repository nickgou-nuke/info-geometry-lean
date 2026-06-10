import Mathlib
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

structure FiniteExponentialFamilyData (α : Type _) [Fintype α] where
  base : ProbabilityDist α
  stat : α → ℝ
  base_pos : ∀ x, 0 < (base x).toReal

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
/-
#### BUCKET 1: CLOSED FINITE THEOREMS

1. **`familyPartition_pos`** — proves `0 < familyPartition F θ` using `Finset.sum_pos` with `F.base_pos` and `Real.exp_pos`. Requires `[Nonempty α]`. ✅

2. **`familyDensity_eq`** — proves `familyDensity F θ x = exp(familyStatistic F x θ - familyLogPartition F θ)` using `Real.exp_sub`, `Real.exp_log`, `ring`. Depends on `familyPartition_pos`. ✅

3. **`familyDensity_pos`** — proves `0 < familyDensity F θ x` using `div_pos` with `mul_pos` and `familyPartition_pos`. ✅

4. **`familyNormalization`** — proves `∑ x, familyDensity F θ x = 1` using `Finset.sum_div` and `div_self`. Depends on `familyPartition_pos`. ✅

5. **`toFiniteExponentialFamily`** — constructs the `FiniteExponentialFamily α ℝ` instance using all four lemmas above. ✅

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

None. (All theorems use the existing structure fields and imported lemmas only.)

#### BUCKET 3: OPEN CLOSURE DEBT

None. No `sorry`, `axiom`, `_True`, `_sorryProof`, certificate wrappers, or data-as-proof patterns.
-/
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
  ring

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
