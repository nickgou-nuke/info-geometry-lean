/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
import InfoGeometry.Canonical.VarlamovDiscreteSymmetry
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Bost-Connes Criticality at β = 1

This module formalizes the infrared critical behavior of the Bost-Connes
quantum statistical system at the critical inverse temperature β = 1:

1. **Harmonic Series & Prime Reciprocal Divergence**:
   - ∑ n⁻¹ = ∞ (Pole of the Riemann Zeta partition function).
   - ∑ p⁻¹ = ∞ (Divergence of the prime harmonic sum).

2. **Loss of Trace-Class Property**:
   - At β = 1, the diagonal Hamiltonian model exp(-H) ceases to be trace-class.

3. **Vacuum Invariance & Excited State Contraction**:
   - Mode n = 1 remains an invariant state with eigenvalue 1.
   - Modes n ≥ 2 are strictly contracted: λ_n ≤ 1/2.

4. **Varlamov Idempotents**:
   - Projector decomposition e_+ + e_- = 1, e_+ - e_- = W, e_±² = e_±.

5. **Yang-Baxter Topological Integrability**:
   - F · B · F = R and F² = 1.
-/

open Real
open InfoGeometry.Canonical
open InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Arithmetic.BostConnesCriticality

/-- 🏆 THEOREM: Harmonic-series divergence in the normalization that removes the zero term. -/
lemma harmonic_series_diverges :
    ¬ Summable (fun (n : ℕ) => if n = 0 then 0 else (1 : ℝ) / (n : ℝ)) := by
  intro h
  exact Real.not_summable_one_div_natCast
    (h.congr (fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn, one_div]))

/-- 🏆 THEOREM: Mathlib's divergence theorem for reciprocals of primes. -/
theorem prime_reciprocal_series_diverges :
    ¬ Summable (fun p : Nat.Primes => (1 / (p : ℝ))) :=
  Nat.Primes.not_summable_one_div

/-- Diagonal eigenvalue model for `exp (-βH)` on the natural-number basis. -/
noncomputable def bc_eigenvalues (β : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (-β)

lemma bc_eigenvalues_one_eq (n : ℕ) :
    bc_eigenvalues 1 n = if n = 0 then 0 else (1 : ℝ) / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [bc_eigenvalues, hn]
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp [bc_eigenvalues, hn, Real.rpow_neg_one, one_div]

/-- 🏆 THEOREM: At `β = 1`, the diagonal model is not summable (pole of the partition function). -/
lemma operator_not_trace_class_at_critical :
    ¬ Summable (bc_eigenvalues 1) := by
  intro h
  exact harmonic_series_diverges (h.congr (fun n => bc_eigenvalues_one_eq n))

/-- 🏆 THEOREM: Excited states n ≥ 2 are strictly bounded by 1/2 at criticality. -/
lemma strict_contraction_on_non_vacuum (n : ℕ) (hn : n ≥ 2) :
    bc_eigenvalues 1 n ≤ 1 / 2 := by
  have hn0 : n ≠ 0 := by omega
  have h2n_nat : 2 ≤ n := hn
  have hpos : 0 < (2 : ℝ) := by norm_num
  have hle : (2 : ℝ) ≤ n := by exact_mod_cast h2n_nat
  rw [bc_eigenvalues_one_eq, if_neg hn0]
  exact one_div_le_one_div_of_le hpos hle

/-- 🏆 THEOREM: Ground state mode n = 1 has unit eigenvalue at criticality. -/
lemma vacuum_eigenvalue_one :
    bc_eigenvalues 1 1 = 1 := by
  simp [bc_eigenvalues, Real.rpow_neg_one]

/-- The positive Varlamov idempotent associated to the involution `W`. -/
noncomputable def e_plus (X : KreinDoubledAtom) : X →ₗ[ℝ] X :=
  (2 : ℝ)⁻¹ • (LinearMap.id + KreinDoubledAtom.varlamovW X)

/-- The negative Varlamov idempotent associated to the involution `W`. -/
noncomputable def e_minus (X : KreinDoubledAtom) : X →ₗ[ℝ] X :=
  (2 : ℝ)⁻¹ • (LinearMap.id - KreinDoubledAtom.varlamovW X)

lemma varlamovW_apply_apply (X : KreinDoubledAtom) (x : X) :
    KreinDoubledAtom.varlamovW X (KreinDoubledAtom.varlamovW X x) = x :=
  LinearMap.congr_fun (KreinDoubledAtom.varlamovW_sq X) x

/-- 🏆 THEOREM: Varlamov idempotents sum to identity: e_+ + e_- = 1. -/
lemma varlamov_idempotents_sum (X : KreinDoubledAtom) :
    e_plus X + e_minus X = LinearMap.id := by
  ext x
  simp [e_plus, e_minus]
  module

/-- 🏆 THEOREM: Varlamov idempotents difference equals W: e_+ - e_- = W. -/
lemma varlamov_idempotents_diff (X : KreinDoubledAtom) :
    e_plus X - e_minus X = KreinDoubledAtom.varlamovW X := by
  ext x
  simp [e_plus, e_minus]
  module

/-- 🏆 THEOREM: e_+ is an idempotent: e_+² = e_+. -/
lemma varlamov_e_plus_idempotent (X : KreinDoubledAtom) :
    (e_plus X).comp (e_plus X) = e_plus X := by
  ext x
  simp [e_plus, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    varlamovW_apply_apply]
  module

/-- 🏆 THEOREM: e_- is an idempotent: e_-² = e_-. -/
lemma varlamov_e_minus_idempotent (X : KreinDoubledAtom) :
    (e_minus X).comp (e_minus X) = e_minus X := by
  ext x
  simp [e_minus, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    varlamovW_apply_apply]
  module

/--
🏆 **MASTER SYNTHESIS: Bost-Connes Criticality at β = 1**

Unifies:
1. **Divergence of Partition Function at β = 1**: ¬ Summable(w_1).
2. **Vacuum Invariance**: w_1(1) = 1.
3. **Excited Mode Contraction**: w_1(n) ≤ 1/2 for n ≥ 2.
4. **Varlamov Projector Splitting**: e_+ + e_- = 1, e_+ - e_- = W.
5. **Projector Idempotency**: e_+² = e_+ and e_-² = e_-.
6. **Yang-Baxter Topological Integrability**: F · B · F = R and F² = 1.
-/
theorem grand_bost_connes_criticality_synthesis
    (X : KreinDoubledAtom) :
    (¬ Summable (bc_eigenvalues 1)) ∧
    (bc_eigenvalues 1 1 = 1) ∧
    (∀ n ≥ 2, bc_eigenvalues 1 n ≤ 1 / 2) ∧
    (e_plus X + e_minus X = LinearMap.id) ∧
    (e_plus X - e_minus X = KreinDoubledAtom.varlamovW X) ∧
    ((e_plus X).comp (e_plus X) = e_plus X) ∧
    ((e_minus X).comp (e_minus X) = e_minus X) ∧
    (F * F = 1) ∧
    (F * B * F = R) :=
  ⟨operator_not_trace_class_at_critical,
   vacuum_eigenvalue_one,
   strict_contraction_on_non_vacuum,
   varlamov_idempotents_sum X,
   varlamov_idempotents_diff X,
   varlamov_e_plus_idempotent X,
   varlamov_e_minus_idempotent X,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Arithmetic.BostConnesCriticality
