import Mathlib

/-!
# Finite Penrose--Onsager--Yang occupation spectra

This file isolates the representation-independent spectral content of quantum
condensation. A reduced density operator is read through its nonnegative
occupation eigenvalues. A mode is called macroscopic when its occupation
retains a fixed positive fraction of the linear population scale along a
family. Simple and fragmented condensation are then exact predicates on the
number of macroscopic modes.

The definitions are deliberately independent of whether the relevant reduced
operator is one-body, two-body, or higher-body. No Bose/Fermi statistics,
Hamiltonian, spontaneous symmetry breaking, ODLRO limit, or microscopic
superconducting model is inferred here.
-/

noncomputable section

namespace InfoGeometry.Quantum.PenroseOnsagerYang

open scoped BigOperators Topology
open Filter

variable {ι : Type*} [Fintype ι]

/-- A finite list of nonnegative occupation eigenvalues. -/
structure OccupationSpectrum (ι : Type*) [Fintype ι] where
  occupation : ι → ℝ
  occupation_nonneg : ∀ i, 0 ≤ occupation i

/-- Total occupation carried by a finite spectrum. -/
def totalOccupation (S : OccupationSpectrum ι) : ℝ :=
  ∑ i, S.occupation i

/-- Every occupation is bounded above by the total occupation. -/
theorem occupation_le_total (S : OccupationSpectrum ι) (i : ι) :
    S.occupation i ≤ totalOccupation S := by
  classical
  unfold totalOccupation
  exact Finset.single_le_sum
    (fun j _hj => S.occupation_nonneg j)
    (Finset.mem_univ i)

/-- Occupation fraction relative to the total spectral mass. -/
def occupationFraction (S : OccupationSpectrum ι) (i : ι) : ℝ :=
  S.occupation i / totalOccupation S

/-- Occupation fractions are nonnegative whenever the total mass is positive. -/
theorem occupationFraction_nonneg
    (S : OccupationSpectrum ι)
    (hS : 0 < totalOccupation S)
    (i : ι) :
    0 ≤ occupationFraction S i := by
  exact div_nonneg (S.occupation_nonneg i) (le_of_lt hS)

/-- No occupation fraction exceeds one. -/
theorem occupationFraction_le_one
    (S : OccupationSpectrum ι)
    (hS : 0 < totalOccupation S)
    (i : ι) :
    occupationFraction S i ≤ 1 := by
  rw [occupationFraction, div_le_one hS]
  exact occupation_le_total S i

/-- Positive total mass normalizes the finite occupation fractions. -/
theorem sum_occupationFraction_eq_one
    (S : OccupationSpectrum ι)
    (hS : 0 < totalOccupation S) :
    ∑ i, occupationFraction S i = 1 := by
  classical
  unfold occupationFraction
  calc
    ∑ i, S.occupation i / totalOccupation S
        = (∑ i, S.occupation i) / totalOccupation S := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset ι))
                (f := fun i => S.occupation i)
                (a := totalOccupation S))
    _ = totalOccupation S / totalOccupation S := by rfl
    _ = 1 := div_self hS.ne'

/-! ## Families and macroscopic scaling -/

/-- A population-indexed family of nonnegative occupation spectra.

The natural-number argument is the population parameter. No condition is
placed on the trace because one-body and higher-body reduced density matrices
use different trace normalizations. -/
structure OccupationFamily (ι : Type*) [Fintype ι] where
  occupation : ℕ → ι → ℝ
  occupation_nonneg : ∀ N i, 0 ≤ occupation N i

/-- Positive linear population scale, written with a successor to avoid the
zero-population denominator. -/
def populationScale (n : ℕ) : ℝ :=
  (n.succ : ℝ)

@[simp] theorem populationScale_pos (n : ℕ) :
    0 < populationScale n := by
  unfold populationScale
  positivity

/-- Occupation divided by the linear population scale. -/
def scaledOccupation
    (F : OccupationFamily ι) (i : ι) (n : ℕ) : ℝ :=
  F.occupation n.succ i / populationScale n

/-- Scaled occupations are nonnegative. -/
theorem scaledOccupation_nonneg
    (F : OccupationFamily ι) (i : ι) (n : ℕ) :
    0 ≤ scaledOccupation F i n := by
  exact div_nonneg (F.occupation_nonneg n.succ i)
    (le_of_lt (populationScale_pos n))

/-- A mode is macroscopic when it retains a fixed positive fraction of the
linear population scale eventually. -/
def IsMacroscopicMode
    (F : OccupationFamily ι) (i : ι) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ scaledOccupation F i n

/-- A normal family has no macroscopic mode. -/
def IsNormalFamily (F : OccupationFamily ι) : Prop :=
  ∀ i, ¬ IsMacroscopicMode F i

/-- Simple condensation means that exactly one mode is macroscopic. -/
def IsSimpleCondensate (F : OccupationFamily ι) : Prop :=
  ∃ i, IsMacroscopicMode F i ∧
    ∀ j, IsMacroscopicMode F j → j = i

/-- Fragmented condensation means that two distinct modes are macroscopic. -/
def IsFragmentedCondensate (F : OccupationFamily ι) : Prop :=
  ∃ i j, i ≠ j ∧ IsMacroscopicMode F i ∧ IsMacroscopicMode F j

/-- The distinguished macroscopic mode of a simple condensate is unique. -/
theorem simple_macroscopic_mode_unique
    {F : OccupationFamily ι}
    (hF : IsSimpleCondensate F)
    {i j : ι}
    (hi : IsMacroscopicMode F i)
    (hj : IsMacroscopicMode F j) :
    i = j := by
  rcases hF with ⟨k, _hk, huniq⟩
  exact (huniq i hi).trans (huniq j hj).symm

/-- Simple and fragmented condensation are mutually exclusive. -/
theorem simple_not_fragmented
    {F : OccupationFamily ι}
    (hF : IsSimpleCondensate F) :
    ¬ IsFragmentedCondensate F := by
  rintro ⟨i, j, hij, hi, hj⟩
  exact hij (simple_macroscopic_mode_unique hF hi hj)

/-- A normal family cannot be simply condensed. -/
theorem normal_not_simple
    {F : OccupationFamily ι}
    (hF : IsNormalFamily F) :
    ¬ IsSimpleCondensate F := by
  rintro ⟨i, hi, _huniq⟩
  exact hF i hi

/-- A normal family cannot be fragmented. -/
theorem normal_not_fragmented
    {F : OccupationFamily ι}
    (hF : IsNormalFamily F) :
    ¬ IsFragmentedCondensate F := by
  rintro ⟨i, _j, _hij, hi, _hj⟩
  exact hF i hi

/-- A pointwise linear population bound gives scaled occupation at most one. -/
def IsLinearlyPopulationBounded (F : OccupationFamily ι) : Prop :=
  ∀ n i, F.occupation n.succ i ≤ populationScale n

/-- Under the explicit population bound, every scaled occupation lies in the
unit interval. -/
theorem scaledOccupation_le_one
    {F : OccupationFamily ι}
    (hF : IsLinearlyPopulationBounded F)
    (i : ι) (n : ℕ) :
    scaledOccupation F i n ≤ 1 := by
  rw [scaledOccupation, div_le_one (populationScale_pos n)]
  exact hF n i

/-- A macroscopic mode in a linearly bounded family satisfies an eventual
positive linear sandwich `c ≤ occupation/N ≤ 1`. -/
theorem macroscopic_linear_sandwich
    {F : OccupationFamily ι}
    (hbound : IsLinearlyPopulationBounded F)
    {i : ι}
    (hi : IsMacroscopicMode F i) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n in atTop,
        c ≤ scaledOccupation F i n ∧ scaledOccupation F i n ≤ 1 := by
  rcases hi with ⟨c, hc, hcevent⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hcevent] with n hn
  exact ⟨hn, scaledOccupation_le_one hbound i n⟩

/-- Compact classification packet. -/
theorem occupation_classification_packet
    {F : OccupationFamily ι}
    (hsimple : IsSimpleCondensate F) :
    (∃ i, IsMacroscopicMode F i) ∧
      ¬ IsFragmentedCondensate F := by
  rcases hsimple with ⟨i, hi, huniq⟩
  refine ⟨⟨i, hi⟩, ?_⟩
  exact simple_not_fragmented ⟨i, hi, huniq⟩

end InfoGeometry.Quantum.PenroseOnsagerYang
