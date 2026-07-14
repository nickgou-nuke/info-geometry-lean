import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite permutation action and secondary normalization

This file uses mathlib's canonical `Set.image`, equivalences, and real division
notation directly.  It avoids local wrappers for normalization or measure
structures.

The statements are finite/projective algebra facts only: no analytic
concentration theorem, projective-limit measure, or Radon--Nikodym boundary
construction is asserted.
-/

set_option autoImplicit false

namespace GromovPermutationNormalization

/-- The identity permutation acts trivially on subsets of the finite state space. -/
theorem permute_set_identity {n : ℕ} {V : Type*} (U : Set (Fin n → V)) :
    (fun f : Fin n → V => f ∘ (1 : Equiv.Perm (Fin n)).symm) '' U = U := by
  ext f
  constructor
  · intro hf
    rcases hf with ⟨g, hgU, hgf⟩
    simpa using hgf ▸ hgU
  · intro hf
    exact ⟨f, hf, by rfl⟩

/-- Common nonzero scaling cancels under secondary normalization by real division. -/
theorem normalization_projective_scaling (W total c : ℝ)
    (hc : c ≠ 0) :
    (c * W) / (c * total) = W / total := by
  rw [mul_div_mul_left W total hc]

/-- Concrete finite counterexample: secondary normalization is not additive. -/
theorem normalization_non_additive_counterexample :
    (1 + 1 : ℝ) / (2 + 3) ≠ (1 : ℝ) / 2 + (1 : ℝ) / 3 := by
  norm_num

end GromovPermutationNormalization
