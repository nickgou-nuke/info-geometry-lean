import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic

open scoped BigOperators

/--
`ExponentialFamily α θ` abstracts exponential families of probability
distributions on sample space `α` with parameter `θ`.
-/
class ExponentialFamily (α θ : Type) where
  statistic : α → θ → ℝ
  logPartition : θ → ℝ
  density : θ → α → ℝ
  density_eq :
    ∀ θ a,
      density θ a =
        Real.exp (statistic a θ - logPartition θ)

/--
Finite exponential families with normalization.
-/
class FiniteExponentialFamily
    (α θ : Type)
    [Fintype α]
    extends ExponentialFamily α θ where
  normalization :
    ∀ θ, Finset.univ.sum (density θ) = 1

/-!
## Multinomial Family
-/

noncomputable section
open Finset

variable {α : Type} [Fintype α] [Nonempty α]

def multinomialStatistic
    (a : α) (θ : α → ℝ) : ℝ :=
  θ a

def multinomialLogPartition
    (θ : α → ℝ) : ℝ :=
  Real.log (∑ b, Real.exp (θ b))

def multinomialDensity
    (θ : α → ℝ) (a : α) : ℝ :=
  Real.exp (θ a)
    / (∑ b, Real.exp (θ b))

lemma multinomial_partition_pos
    (θ : α → ℝ) :
    0 < ∑ a, Real.exp (θ a) := by
  classical
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset α))
      (f := fun a => Real.exp (θ a))
      (by
        intro a ha
        exact Real.exp_pos _)
      Finset.univ_nonempty)

lemma multinomial_density_pos
    (θ : α → ℝ) (a : α) :
    0 < multinomialDensity θ a := by
  classical
  unfold multinomialDensity
  apply div_pos
  · exact Real.exp_pos _
  · exact multinomial_partition_pos θ

lemma multinomial_density_eq
    (θ : α → ℝ) (a : α) :
    multinomialDensity θ a
      =
      Real.exp
        (multinomialStatistic a θ
          - multinomialLogPartition θ) := by
  unfold multinomialDensity multinomialStatistic multinomialLogPartition
  rw [Real.exp_sub]
  have hpos : 0 < ∑ b, Real.exp (θ b) := multinomial_partition_pos θ
  rw [Real.exp_log hpos]

lemma multinomial_normalization
    (θ : α → ℝ) :
    ∑ a, multinomialDensity θ a = 1 := by
  unfold multinomialDensity
  have hne : (∑ a, Real.exp (θ a)) ≠ 0 := ne_of_gt (multinomial_partition_pos θ)
  calc
    ∑ a, Real.exp (θ a) / ∑ b, Real.exp (θ b)
        = (∑ a, Real.exp (θ a)) / ∑ b, Real.exp (θ b) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset α))
                (f := fun a => Real.exp (θ a))
                (a := ∑ b, Real.exp (θ b)))
    _ = 1 := by
          exact div_self hne

/--
Multinomial exponential family instance.
-/
noncomputable instance
    MultinomialExponentialFamily :
    FiniteExponentialFamily α (α → ℝ) where
  statistic := multinomialStatistic
  logPartition := multinomialLogPartition
  density := multinomialDensity
  density_eq := multinomial_density_eq
  normalization := multinomial_normalization

end
