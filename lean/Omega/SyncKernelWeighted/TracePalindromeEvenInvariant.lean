import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.SyncKernelWeighted.TracePalindrome

namespace Omega.SyncKernelWeighted

/-- The even degree `n = 2k`. -/
def evenDegree (halfDegree : ℕ) : ℕ :=
  2 * halfDegree

/-- The even-palindrome normalization `u^{-k} a_{2k}(u)`, written in the equivalent
division-free form `u^k a_{2k}(u^{-1})`. -/
def normalizedTrace (halfDegree : ℕ) (u : ℚ) : ℚ :=
  u ^ halfDegree * tracePalindromeFamily (evenDegree halfDegree) u⁻¹

/-- The inversion-invariant coordinate `t = u + u^{-1}`. -/
def invariantCoordinate (u : ℚ) : ℚ :=
  u + u⁻¹

/-- The descended polynomial in the coordinate `t = u + u^{-1}`. -/
def invariantPolynomial (halfDegree : ℕ) (t : ℚ) : ℚ :=
  (t + 2) ^ halfDegree

/-- The normalized even trace factors through the inversion-invariant coordinate. -/
def descendsToInvariantCoordinate (halfDegree : ℕ) : Prop :=
  ∀ u : ℚ, u ≠ 0 → normalizedTrace halfDegree u =
    invariantPolynomial halfDegree (invariantCoordinate u)

/-- The normalized even trace is fixed by `u ↦ u^{-1}`. -/
def fixedByInversion (halfDegree : ℕ) : Prop :=
  ∀ u : ℚ, u ≠ 0 → normalizedTrace halfDegree u⁻¹ = normalizedTrace halfDegree u

/-- The descended polynomial is the unique decomposition witness on the image of the substitution
`t = u + u^{-1}`. -/
def invariantPolynomialUniqueOnImage (halfDegree : ℕ) : Prop :=
  ∀ P : ℚ → ℚ,
    (∀ u : ℚ, u ≠ 0 → normalizedTrace halfDegree u = P (invariantCoordinate u)) →
      ∀ t : ℚ, (∃ u : ℚ, u ≠ 0 ∧ invariantCoordinate u = t) →
        P t = invariantPolynomial halfDegree t

/-- Paper-facing invariant decomposition package for the normalized even palindrome. -/
def hasInvariantDecomposition (halfDegree : ℕ) : Prop :=
  descendsToInvariantCoordinate halfDegree ∧ fixedByInversion halfDegree ∧
    invariantPolynomialUniqueOnImage halfDegree

lemma normalizedTrace_eq_invariant (halfDegree : ℕ) (u : ℚ) (hu : u ≠ 0) :
    normalizedTrace halfDegree u = invariantPolynomial halfDegree (invariantCoordinate u) := by
  unfold normalizedTrace invariantPolynomial invariantCoordinate evenDegree tracePalindromeFamily
  have hbase : u * (u⁻¹ + 1) ^ 2 = u + u⁻¹ + 2 := by
    field_simp [hu]
    ring
  calc
    u ^ halfDegree * (u⁻¹ + 1) ^ (2 * halfDegree)
        = u ^ halfDegree * ((u⁻¹ + 1) ^ 2) ^ halfDegree := by rw [pow_mul]
    _ = (u * (u⁻¹ + 1) ^ 2) ^ halfDegree := by rw [← mul_pow]
    _ = (u + u⁻¹ + 2) ^ halfDegree := by rw [hbase]
    _ = (u + u⁻¹ + 2) ^ halfDegree := rfl

lemma descendsToInvariantCoordinate_true (halfDegree : ℕ) :
    descendsToInvariantCoordinate halfDegree := by
  intro u hu
  exact normalizedTrace_eq_invariant halfDegree u hu

lemma fixedByInversion_true (halfDegree : ℕ) : fixedByInversion halfDegree := by
  intro u hu
  rw [normalizedTrace_eq_invariant halfDegree u⁻¹ (inv_ne_zero hu),
    normalizedTrace_eq_invariant halfDegree u hu]
  simp [invariantCoordinate, add_comm]

lemma invariantPolynomialUniqueOnImage_true (halfDegree : ℕ) :
    invariantPolynomialUniqueOnImage halfDegree := by
  intro P hP t ht
  rcases ht with ⟨u, hu, rfl⟩
  rw [← hP u hu, normalizedTrace_eq_invariant halfDegree u hu]

/-- Paper label: `lem:trace-palindrome-even-invariant`. -/
theorem paper_trace_palindrome_even_invariant (halfDegree : ℕ) :
    hasInvariantDecomposition halfDegree := by
  let _ := paper_trace_palindrome
  exact ⟨descendsToInvariantCoordinate_true halfDegree, fixedByInversion_true halfDegree,
    invariantPolynomialUniqueOnImage_true halfDegree⟩

end Omega.SyncKernelWeighted
