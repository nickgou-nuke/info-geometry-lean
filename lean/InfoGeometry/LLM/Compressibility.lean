import Mathlib
import InfoGeometry.LLM.NonCommutativeDAG

namespace InfoGeometry.LLM.Compressibility

/-!
# A Small Model of DAG Compression

## Abstract
This file formalizes a deliberately small combinatorial model: a linear-size
description can specify a binary-doubling expansion of exponential size. It
does not assert empirical growth rates for human mathematics or formal proofs.

## Archetypes in Causal Poset Order
1. `DagNode`: An abstract datum recording description and expansion lengths.
2. `causallyPrecedes`: Strict ordering by depth.
3. `wrap_length` and `unwrap_length`: Description and expansion lengths.
4. `expansion_factor`: The exact size of a uniform branching expansion.
-/

section Archetype1_CausalPoset

/-- A node in the mathematical dependency DAG representing a theorem or definition. -/
structure DagNode where
  id : ℕ
  depth : ℕ
  wrap_length : ℕ
  unwrap_length : ℕ
  unwrap_length_pos : 0 < unwrap_length
  wrap_le_unwrap : wrap_length ≤ unwrap_length

/-- A strict partial order induced by node depth. -/
def causallyPrecedes (a b : DagNode) : Prop :=
  a.depth < b.depth

theorem causal_trans (a b c : DagNode)
    (hab : causallyPrecedes a b) (hbc : causallyPrecedes b c) :
    causallyPrecedes a c :=
  Nat.lt_trans hab hbc

theorem causal_asymm (a b : DagNode) (hab : causallyPrecedes a b) :
  ¬ causallyPrecedes b a :=
  Nat.not_lt_of_lt hab

theorem causal_irrefl (a : DagNode) : ¬ causallyPrecedes a a :=
  Nat.lt_irrefl a.depth

end Archetype1_CausalPoset

section Archetype2_GrowthRates

/-- The size of a linear description of depth `r`. -/
def linear_description_size (r : ℕ) : ℕ := r

/-- The number of leaves in a full binary expansion of depth `r`. -/
def binary_expansion_size (r : ℕ) : ℕ := 2 ^ r

/-- For every positive depth, binary expansion has more leaves than the
description has tokens. This is a statement about the model above only. -/
theorem linear_description_lt_binary_expansion :
    ∀ r : ℕ, linear_description_size r < binary_expansion_size r
  | 0 => by decide
  | r + 1 => by
    have ih := linear_description_lt_binary_expansion r
    have h_pos : 1 ≤ binary_expansion_size r := Nat.one_le_two_pow
    dsimp [linear_description_size, binary_expansion_size] at *
    rw [Nat.pow_succ, Nat.mul_two]
    omega

end Archetype2_GrowthRates

section Archetype3_ExpansionCoverage

/-- The exponential expansion factor provided by modular definitions.
If every macro expands to `k` primitive axioms, a DAG of depth `d` expands to `k^d`. -/
def expansion_factor (depth macro_branching : ℕ) : ℕ :=
  macro_branching ^ depth

/-- The description-to-expansion ratio. Positivity rules out division by zero. -/
def compression_ratio (node : DagNode) : ℚ :=
  node.wrap_length / node.unwrap_length

theorem compression_ratio_nonneg (node : DagNode) :
    0 ≤ compression_ratio node := by
  unfold compression_ratio
  apply div_nonneg
  · exact_mod_cast Nat.zero_le node.wrap_length
  · exact le_of_lt (by exact_mod_cast node.unwrap_length_pos)

theorem compression_ratio_le_one (node : DagNode) :
    compression_ratio node ≤ 1 := by
  unfold compression_ratio
  rw [div_le_iff₀ (by exact_mod_cast node.unwrap_length_pos)]
  exact_mod_cast node.wrap_le_unwrap

/-- Theorem: A DAG with uniform macro branching `k` yields an exact 
exponential unwrap length bound. -/
theorem unwrap_length_exponential (depth k : ℕ) :
    expansion_factor depth k = k ^ depth :=
  rfl

/-! The concrete binary-doubling instance and its exact compression theorem
are proved in `InfoGeometry.LLM.NonCommutativeDAG`. -/

theorem binary_doubling_expansion_from_description_length (n : ℕ) :
    InfoGeometry.ProofTheory.NonCommutativeDAG.ncDoublingUnwrap n =
      2 ^ ((InfoGeometry.ProofTheory.NonCommutativeDAG.ncDoublingWrap n - 1) / 2) := by
  exact InfoGeometry.ProofTheory.NonCommutativeDAG.nc_doubling_compression n

end Archetype3_ExpansionCoverage

end InfoGeometry.LLM.Compressibility
