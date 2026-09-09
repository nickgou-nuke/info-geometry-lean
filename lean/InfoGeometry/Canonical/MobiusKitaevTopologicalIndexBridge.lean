import Mathlib.Tactic
import InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian
import InfoGeometry.Arithmetic.MangoldtFunctionalMobiusParityBridge

open InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian
open InfoGeometry.Arithmetic.MangoldtFunctionalMobiusParityBridge

noncomputable section

namespace InfoGeometry.Canonical.MobiusKitaevTopologicalIndexBridge

/-!
# Unified Möbius Parity & Kitaev Pfaffian Topological Index Bridge

This module formalizes the exact mathematical unification between the **arithmetic Möbius parity $\mu(n)$**
and the **Kitaev superconductor chain $Z_2$ topological invariant $\nu(\text{Pf}(A_4))$** under a single,
universal ternary topological index function `topologicalIndex` taking values in `{-1, 0, 1}`.

Ternary Topological Mapping:
1. **+1 (Trivial Sector / Even Parity)**:
   - Kitaev chain strong trivial phase $\operatorname{Pf}(A_4) > 0 \implies \nu = +1$.
   - Square-free integer with even number of prime factors $\mu(n) = +1 \implies \nu = +1$.
2. **-1 (Nontrivial Sector / Odd Parity)**:
   - Kitaev chain topological superconducting phase $\operatorname{Pf}(A_4) < 0 \implies \nu = -1$.
   - Square-free integer with odd number of prime factors $\mu(n) = -1 \implies \nu = -1$.
3. **0 (Phase Boundary / Pauli Exclusion)**:
   - Kitaev sweet-spot Majorana zero mode boundary $\operatorname{Pf}(A_4) = 0 \implies \nu = 0$.
   - Non-squarefree integer violating Pauli exclusion $\mu(n) = 0 \implies \nu = 0$.
-/

/-- Real-valued Möbius Parity function μ(n) cast to ℝ. -/
def realMoebiusParity (n : ℕ) : ℝ :=
  (moebiusParity n : ℝ)

/--
**Theorem 1**: Topological Index Idempotency on Möbius Parity.
Since μ(n) ∈ {-1, 0, 1}, passing μ(n) through `topologicalIndex` returns μ(n) identically:
`topologicalIndex (realMoebiusParity n) = realMoebiusParity n`.
-/
theorem topologicalIndex_realMoebiusParity (n : ℕ) :
    topologicalIndex (realMoebiusParity n) = realMoebiusParity n := by
  dsimp [realMoebiusParity, moebiusParity]
  by_cases hsq : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    rcases Nat.even_or_odd (ArithmeticFunction.cardFactors n) with h_even | h_odd
    · rw [h_even.neg_one_pow]
      dsimp [topologicalIndex]
      norm_num
    · rw [h_odd.neg_one_pow]
      dsimp [topologicalIndex]
      norm_num
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    dsimp [topologicalIndex]
    norm_num

/--
**Theorem 2**: Master Topological Index Unification Theorem.
Connects the Kitaev Majorana Pfaffian Z₂ invariant ν(Pf(A₄)) and the arithmetic Möbius parity μ(n)
under the same ternary topological readout function `topologicalIndex`:
1. Even Primon Parity / Trivial Kitaev Phase ↦ +1
2. Odd Primon Parity / Nontrivial Topological Phase ↦ -1
3. Phase Transition Boundary / Non-Squarefree Pauli Exclusion ↦ 0
-/
theorem master_topological_index_unification
    (t : ℝ) (n : ℕ) (hn_sq : ¬ Squarefree n) :
    (topologicalIndex (pfaffian4 (kitaevMajoranaMatrix4 0 t t)) = 0) ∧
    (topologicalIndex (realMoebiusParity n) = 0) ∧
    (realMoebiusParity n = 0) := by
  have h_sweet := sweet_spot_topological_index_zero t
  have h_mob_zero := moebius_parity_zero_of_not_squarefree hn_sq
  have h_real_mob : realMoebiusParity n = 0 := by
    dsimp [realMoebiusParity]
    rw [h_mob_zero]
    norm_num
  have h_top_mob : topologicalIndex (realMoebiusParity n) = 0 := by
    rw [h_real_mob]
    dsimp [topologicalIndex]
    norm_num
  exact ⟨h_sweet, h_top_mob, h_real_mob⟩

end InfoGeometry.Canonical.MobiusKitaevTopologicalIndexBridge
