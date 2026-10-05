import InfoGeometry.Dynamics.RapiditySpace
import InfoGeometry.Krein.FiniteGramFactorization
import InfoGeometry.Krein.BornRuleCore
import InfoGeometry.Krein.HilbertBridge

/-!
# Doubled-real Gram/Born/KAN synthesis

This file is only a composition layer.  The factors remain distinct:

* `A` is the positive exponential factor and has an additive group law;
* a Gram matrix is an amplitude factorisation `B * Bᵀ`;
* the Dirac/Krein amplitude is converted to a probability by the Born rule.

No signed cross-Gram entry is silently treated as a probability.
-/

noncomputable section

namespace InfoGeometry.Synthesis.DoubledRealBornGramKAN

open Matrix
open InfoGeometry.Dynamics.HyperbolicComponent
open InfoGeometry.Dynamics.RapiditySpace
open InfoGeometry.Krein
open InfoGeometry.Krein.BornRuleCore
open InfoGeometry.Krein.FiniteGramFactorization

/-! ## KAN `A` factor -/

theorem positiveA_diagonal (rapidity : ℝ) :
    0 < componentAReal rapidity 0 0 ∧ 0 < componentAReal rapidity 1 1 := by
  exact componentAReal_diagonal_positive rapidity

theorem positiveA_group_law (rapidity₁ rapidity₂ : ℝ) :
    componentAReal rapidity₁ * componentAReal rapidity₂ =
      componentAReal (rapidity₁ + rapidity₂) := by
  exact rapidity_additive_composition rapidity₁ rapidity₂

/-! ## Gram factorisation -/

theorem gram_diagonal_nonnegative
    {n m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (i : n) :
    0 ≤ gramMatrix B i i := by
  exact gramMatrix_diag_nonneg B i

theorem gram_quadratic_nonnegative
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (x : n → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * gramMatrix B i j * x j := by
  exact gramMatrix_quadratic_nonneg B x

/-! ## Dirac/Krein Born layer on the doubled real carrier -/

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev BornState (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] := HilbertDoubled E

def bornWeight (final initial : BornState E) : ℝ :=
  kreinAdaptedProbability final initial

theorem bornWeight_nonnegative (final initial : BornState E) :
    0 ≤ bornWeight final initial := by
  exact kreinAdaptedProbability_nonnegative final initial

theorem bornWeight_le_one
    (final initial : BornState E)
    (hfinal : final ≠ 0) (hinitial : initial ≠ 0) :
    bornWeight final initial ≤ 1 := by
  exact kreinAdaptedProbability_le_one final initial hfinal hinitial

theorem bornWeight_mem_unitInterval
    (final initial : BornState E)
    (hfinal : final ≠ 0) (hinitial : initial ≠ 0) :
    bornWeight final initial ∈ Set.Icc (0 : ℝ) 1 := by
  exact kreinAdaptedProbability_mem_unitInterval final initial hfinal hinitial

end InfoGeometry.Synthesis.DoubledRealBornGramKAN
