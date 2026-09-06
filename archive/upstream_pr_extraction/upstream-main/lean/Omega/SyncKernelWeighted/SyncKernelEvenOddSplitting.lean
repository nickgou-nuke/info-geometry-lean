import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The affine block `B(u) = B₀ + u B₁`. -/
def sync_kernel_even_odd_splitting_B (B0 B1 u : ℚ) : ℚ :=
  B0 + u * B1

/-- The `Π`-even part `(B₀ + B₁)/2`. -/
def sync_kernel_even_odd_splitting_Bsym (B0 B1 : ℚ) : ℚ :=
  (1 / 2 : ℚ) * (B0 + B1)

/-- The `Π`-odd part `(B₁ - B₀)/2`. -/
def sync_kernel_even_odd_splitting_Basym (B0 B1 : ℚ) : ℚ :=
  (1 / 2 : ℚ) * (B1 - B0)

/-- Direct expansion of `B(u)` into its `Π`-even and `Π`-odd parts. -/
def splitFormula (B0 B1 : ℚ) : Prop :=
  ∀ u : ℚ,
    sync_kernel_even_odd_splitting_B B0 B1 u =
      (1 + u) * sync_kernel_even_odd_splitting_Bsym B0 B1 +
        (u - 1) * sync_kernel_even_odd_splitting_Basym B0 B1

/-- The conjugation action fixes the `Π`-even part and negates the `Π`-odd part. -/
def piParityFormula (B0 B1 : ℚ) (Pi : ℚ → ℚ) : Prop :=
  Pi (sync_kernel_even_odd_splitting_Bsym B0 B1) =
      sync_kernel_even_odd_splitting_Bsym B0 B1 ∧
    Pi (sync_kernel_even_odd_splitting_Basym B0 B1) =
      -sync_kernel_even_odd_splitting_Basym B0 B1

/-- Uniqueness of the affine decomposition in the basis `1 + u`, `u - 1`. -/
def uniqueSplitFormula (B0 B1 : ℚ) : Prop :=
  ∀ S A : ℚ,
    (∀ u : ℚ,
      sync_kernel_even_odd_splitting_B B0 B1 u = (1 + u) * S + (u - 1) * A) →
        S = sync_kernel_even_odd_splitting_Bsym B0 B1 ∧
          A = sync_kernel_even_odd_splitting_Basym B0 B1

/-- Paper label: `lem:sync-kernel-even-odd-splitting`. The affine kernel block splits uniquely
into its `Π`-even and `Π`-odd components, and the conjugation action exchanges the odd part by a
sign. -/
theorem paper_sync_kernel_even_odd_splitting
    (B0 B1 : ℚ) (Pi : ℚ → ℚ)
    (pi_add : ∀ x y : ℚ, Pi (x + y) = Pi x + Pi y)
    (pi_rat : ∀ q x : ℚ, Pi (q * x) = q * Pi x)
    (pi_B0 : Pi B0 = B1)
    (pi_B1 : Pi B1 = B0) :
    splitFormula B0 B1 ∧ piParityFormula B0 B1 Pi ∧ uniqueSplitFormula B0 B1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    unfold sync_kernel_even_odd_splitting_B sync_kernel_even_odd_splitting_Bsym
      sync_kernel_even_odd_splitting_Basym
    ring
  · constructor
    · calc
        Pi (sync_kernel_even_odd_splitting_Bsym B0 B1)
            = Pi ((1 / 2 : ℚ) * B0 + (1 / 2 : ℚ) * B1) := by
                unfold sync_kernel_even_odd_splitting_Bsym
                congr 1
                ring
        _ = (1 / 2 : ℚ) * Pi B0 + (1 / 2 : ℚ) * Pi B1 := by
              rw [pi_add, pi_rat, pi_rat]
        _ = (1 / 2 : ℚ) * B1 + (1 / 2 : ℚ) * B0 := by
              rw [pi_B0, pi_B1]
        _ = sync_kernel_even_odd_splitting_Bsym B0 B1 := by
              unfold sync_kernel_even_odd_splitting_Bsym
              ring
    · calc
        Pi (sync_kernel_even_odd_splitting_Basym B0 B1)
            = Pi ((1 / 2 : ℚ) * B1 + (-1 / 2 : ℚ) * B0) := by
                unfold sync_kernel_even_odd_splitting_Basym
                congr 1
                ring
        _ = (1 / 2 : ℚ) * Pi B1 + (-1 / 2 : ℚ) * Pi B0 := by
              rw [pi_add, pi_rat, pi_rat]
        _ = (1 / 2 : ℚ) * B0 + (-1 / 2 : ℚ) * B1 := by
              rw [pi_B1, pi_B0]
        _ = -sync_kernel_even_odd_splitting_Basym B0 B1 := by
              unfold sync_kernel_even_odd_splitting_Basym
              ring
  · intro S A hsplit
    have h0 : B0 = S - A := by
      simpa [sync_kernel_even_odd_splitting_B, sub_eq_add_neg] using hsplit 0
    have h1 : B0 + B1 = 2 * S := by
      have h1' := hsplit 1
      have h1'' : B0 + B1 = (1 + 1 : ℚ) * S := by
        simpa [sync_kernel_even_odd_splitting_B] using h1'
      linarith
    have hS : S = sync_kernel_even_odd_splitting_Bsym B0 B1 := by
      unfold sync_kernel_even_odd_splitting_Bsym
      linarith
    have hA : A = sync_kernel_even_odd_splitting_Basym B0 B1 := by
      unfold sync_kernel_even_odd_splitting_Basym
      linarith [h0, hS]
    exact ⟨hS, hA⟩

end Omega.SyncKernelWeighted
