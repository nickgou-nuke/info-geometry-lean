/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Exact Algebraic Structure of the Log Lattice in the Primon Gas Capstone

This capstone formally integrates the exact algebraic definition and properties of
the **Log Lattice** $\Lambda_{\text{log}}$:

1. **Free $\mathbb{Z}$-Module of Prime Generators**:
   - The Log Lattice is the free abelian group over prime indices:
     $\Lambda_{\text{log}} = \bigoplus_{p \in \mathbb{P}} \mathbb{Z} \cdot [p]$.
2. **The Logarithmic Evaluation Homomorphism**:
   - Evaluation map $\text{ev} : \Lambda_{\text{log}} \to \mathbb{R}$ sending $\sum a_p [p] \mapsto \sum a_p \ln p$.
   - Proved group homomorphism: $\text{ev}(v_1 + v_2) = \text{ev}(v_1) + \text{ev}(v_2)$ and $\text{ev}(0) = 0$.
3. **Generator Surprisal Scaling**:
   - Single prime generator: $\text{ev}([p]) = \ln p$.
   - Integer multiple: $\text{ev}(k \cdot [p]) = k \cdot \ln p$.

All proofs are complete in native Mathlib 4 with 0 `sorry`s, 0 custom axioms, and 0 wrappers.
-/

open scoped BigOperators Real

noncomputable section

namespace InfoGeometry.Arithmetic.LogLattice

/-- The type of prime numbers as a subtype of ℕ+. -/
def PrimeIndex := { p : ℕ+ // Nat.Prime p.val }

/-- The formal Log Lattice $\Lambda_{\text{log}} = \bigoplus_{p \in \mathbb{P}} \mathbb{Z} \cdot \ln p$,
    represented algebraically as the free $\mathbb{Z}$-module over prime generators. -/
abbrev LogLatticeElement := PrimeIndex →₀ ℤ

/-- The logarithmic embedding map $\text{ev} : \Lambda_{\text{log}} \to \mathbb{R}$
    sending $\sum a_p [p] \mapsto \sum a_p \ln p$. -/
def logLatticeEval (v : LogLatticeElement) : ℝ :=
  Finsupp.sum v (fun p a => (a : ℝ) * Real.log (p.val.val : ℝ))

/-- 🏆 THEOREM 1 (Evaluation Map Additivity / Group Homomorphism):
    $\text{ev}(v_1 + v_2) = \text{ev}(v_1) + \text{ev}(v_2)$. -/
theorem logLatticeEval_add (v1 v2 : LogLatticeElement) :
    logLatticeEval (v1 + v2) = logLatticeEval v1 + logLatticeEval v2 := by
  unfold logLatticeEval
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

/-- 🏆 THEOREM 2 (Zero Lattice Vector Evaluates to 0):
    $\text{ev}(0) = 0$. -/
theorem logLatticeEval_zero :
    logLatticeEval 0 = 0 := by
  unfold logLatticeEval
  exact Finsupp.sum_zero_index

/-- 🏆 THEOREM 3 (Single Prime Generator Surprisal Evaluation):
    $\text{ev}([p]) = \ln p$. -/
theorem logLatticeEval_single (p : PrimeIndex) :
    logLatticeEval (Finsupp.single p 1) = Real.log (p.val.val : ℝ) := by
  unfold logLatticeEval
  simp

/-- 🏆 THEOREM 4 (Integer Multiple Scaling on Generators):
    $\text{ev}(k \cdot [p]) = k \cdot \ln p$. -/
theorem logLatticeEval_single_smul (p : PrimeIndex) (k : ℤ) :
    logLatticeEval (Finsupp.single p k) = (k : ℝ) * Real.log (p.val.val : ℝ) := by
  unfold logLatticeEval
  simp

end InfoGeometry.Arithmetic.LogLattice
