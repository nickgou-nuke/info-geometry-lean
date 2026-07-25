import Mathlib.Tactic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import InfoGeometry.JordanDecomposition.CyclicNilpotent

/-!
# Jordan Normal Form — Nilpotent Endomorphisms

Layer-by-layer construction of a Jordan basis for nilpotent N : V → V.
Combined with mathlib's `JordanChevalley`, this gives full JNF over ℂ.

## Proven lemmas:
1. `image_ker_succ_sub_ker`: N(ker N^{m+1}) ⊆ ker N^m
2. `chain_linear_independent`: {x, Nx, ..., N^{j-1}x} linearly independent
3. `jordanBasis` in this file is not provided as a complete classical theorem; it is intentionally
   left to a dedicated decomposition module.
-/

open FiniteDimensional
open Submodule

noncomputable section

namespace JordanDecomposition

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-! ### Lemma 1: Kernel chain inclusion -/

lemma image_ker_succ_sub_ker (N : Module.End K V) (m : ℕ) :
    (LinearMap.ker (N ^ (m + 1))).map N ≤ LinearMap.ker (N ^ m) := by
  rintro y hx
  rcases Submodule.mem_map.mp hx with ⟨z, hz, rfl⟩
  rw [LinearMap.mem_ker] at hz ⊢
  calc (N ^ m) (N z) = (N ^ m * N) z := rfl
    _ = (N ^ (m + 1)) z := by rw [pow_succ]
    _ = 0 := hz

lemma quotient_well_defined (N : Module.End K V) (j : ℕ) (hj : 1 ≤ j) :
    LinearMap.ker (N ^ (j - 1)) ⊔ (LinearMap.ker (N ^ (j + 1))).map N ≤
    LinearMap.ker (N ^ j) := by
  apply sup_le
  · rintro x hx; rw [LinearMap.mem_ker] at hx ⊢
    have h_comm : (N ^ (j - 1)) * N = N * (N ^ (j - 1)) := by
      calc (N ^ (j - 1)) * N = N ^ ((j - 1) + 1) := by rw [pow_succ]
        _ = N ^ j := by rw [Nat.sub_add_cancel hj]
        _ = N ^ (1 + (j - 1)) := by rw [add_comm, Nat.sub_add_cancel hj]
        _ = (N ^ 1 : Module.End K V) * (N ^ (j - 1)) := by rw [pow_add]
        _ = N * (N ^ (j - 1)) := by simp
    calc (N ^ j) x = ((N ^ (j - 1)) * N) x := by rw [← pow_succ, Nat.sub_add_cancel hj]
      _ = (N * (N ^ (j - 1))) x := by rw [h_comm]
      _ = N ((N ^ (j - 1)) x) := rfl
      _ = N 0 := by rw [hx]
      _ = 0 := by simp
  · exact image_ker_succ_sub_ker N j

/-! ### Lemma 2: Jordan chains are linearly independent -/

lemma chain_linear_independent (N : Module.End K V) {x : V} {j : ℕ}
    (hx : (N ^ (j - 1)) x ≠ 0) (hN : (N ^ j) x = 0) :
    LinearIndependent K (λ (i : Fin j) => (N ^ (i : ℕ)) x) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  have hzero : ∀ (m : ℕ) (hm : m < j), g ⟨m, hm⟩ = 0 := by
    intro m hm
    refine Nat.strong_induction_on m (λ k ih' hk => ?_) hm
    have h_apply'' : (N ^ (j - 1 - k)) (∑ i : Fin j, g i • (N ^ (i : ℕ)) x) = 0 := by
      rw [hsum, map_zero]
    rw [map_sum (N ^ (j - 1 - k))] at h_apply''
    have h_simplify : (∑ i : Fin j, (N ^ (j - 1 - k)) (g i • (N ^ (i : ℕ)) x)) =
        (∑ i : Fin j, g i • ((N ^ (j - 1 - k)) ((N ^ (i : ℕ)) x))) := by
      refine Finset.sum_congr rfl (λ i _ => by rw [LinearMap.map_smul])
    rw [h_simplify] at h_apply''
    have h_pow : ∀ (i : Fin j), (N ^ (j - 1 - k)) ((N ^ (i : ℕ)) x) =
        (N ^ (j - 1 - k + (i : ℕ))) x := by
      intro i
      calc (N ^ (j - 1 - k)) ((N ^ (i : ℕ)) x) = ((N ^ (j - 1 - k)) * (N ^ (i : ℕ))) x := rfl
        _ = (N ^ ((j - 1 - k) + (i : ℕ))) x := by rw [pow_add]
    simp_rw [h_pow] at h_apply''
    have h_gt : ∀ (i : Fin j), (i : ℕ) > k →
        g i • (N ^ (j - 1 - k + (i : ℕ))) x = 0 := by
      intro i hi
      have hpow_ge_j : j ≤ j - 1 - k + (i : ℕ) := by
        omega
      rcases Nat.le.dest hpow_ge_j with ⟨b, hb⟩
      have hzero_term : (N ^ (j - 1 - k + (i : ℕ))) x = 0 := by
        rw [← hb, add_comm j b, pow_add]
        simp [hN]
      rw [hzero_term, smul_zero]
    have h_lt : ∀ (i : Fin j), (i : ℕ) < k →
        g i • (N ^ (j - 1 - k + (i : ℕ))) x = 0 := by
      intro i hi
      have hgi : g i = 0 := ih' i.val hi (by omega)
      rw [hgi, zero_smul]
    have h_sum_reduce : (∑ i : Fin j, g i • (N ^ (j - 1 - k + (i : ℕ))) x) =
        g ⟨k, hk⟩ • (N ^ (j - 1 - k + k)) x := by
      -- All i ≠ k contribute 0; only i = k contributes. Use Finset.sum_eq_single.
      refine Finset.sum_eq_single (s := Finset.univ) (⟨k, hk⟩ : Fin j) ?_ ?_
      · intro b hb hb_ne
        by_cases hb_lt : (b : ℕ) < k
        · exact h_lt b hb_lt
        · have hb_gt : (b : ℕ) > k := by
            have : (b : ℕ) ≠ k := fun h => hb_ne (Fin.ext h); omega
          exact h_gt b hb_gt
      · intro h; exfalso; exact h (Finset.mem_univ _)
    rw [h_sum_reduce] at h_apply''
    have h_exp : (j - 1 - k + k) = (j - 1) := by omega
    rw [h_exp] at h_apply''
    exact (smul_eq_zero.mp h_apply'').resolve_right hx
  intro i; exact hzero i.val i.2

end JordanDecomposition
