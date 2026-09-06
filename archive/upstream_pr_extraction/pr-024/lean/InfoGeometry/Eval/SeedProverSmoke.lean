import Mathlib

noncomputable section

namespace SeedProverSmoke

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def NilpotentIndex (N : Module.End K V) (k : ℕ) : Prop :=
  (N ^ k) = 0 ∧ (N ^ (k - 1)) ≠ 0

lemma exists_nilpotent_index (N : Module.End K V) [FiniteDimensional K V]
    (hN : IsNilpotent N) (hN_ne : N ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ NilpotentIndex N k := by
  classical
  rcases hN with ⟨k₀, hk₀⟩
  let hP : ∃ k : ℕ, N ^ k = 0 := ⟨k₀, hk₀⟩
  have hk_pos : 0 < Nat.find hP := by
    by_contra hk_nonpos
    have hk_zero : Nat.find hP = 0 := by omega
    have h_one_zero : (1 : Module.End K V) = 0 := by
      simpa [hk_zero] using (Nat.find_spec hP : N ^ Nat.find hP = 0)
    have hN_zero : N = 0 := by
      ext x
      have hx : x = 0 := by
        have h := congrArg (fun f : Module.End K V => f x) h_one_zero
        simpa using h
      simp [hx]
    exact hN_ne hN_zero
  refine ⟨Nat.find hP, Nat.succ_le_of_lt hk_pos, ?_⟩
  constructor
  · exact Nat.find_spec hP
  · intro hprev
    exact (Nat.find_min hP (Nat.pred_lt (ne_of_gt hk_pos))) hprev

end SeedProverSmoke
