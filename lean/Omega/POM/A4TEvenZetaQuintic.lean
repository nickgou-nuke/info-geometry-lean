import Mathlib.Tactic

namespace Omega.POM

/-- The two quadratic factors appearing in the closed even-spectrum determinant factorization. -/
def evenFactorLeft (t u : ℤ) : ℤ :=
  u ^ 2 + (t + 1) * u + 1

/-- The conjugate quadratic factor. -/
def evenFactorRight (t u : ℤ) : ℤ :=
  u ^ 2 + (1 - t) * u + 1

/-- The explicit quintic obtained by expanding `- (u - 1) * evenFactorLeft * evenFactorRight`. -/
def evenQuintic (t u : ℤ) : ℤ :=
  -u ^ 5 - u ^ 4 + (t ^ 2 - 1) * u ^ 3 + (1 - t ^ 2) * u ^ 2 + u + 1

/-- The discriminant factorization used to isolate the unique nonnegative degeneration point. -/
def discriminant (t : ℤ) : ℤ :=
  (t - 1) ^ 2 * (t ^ 2 + 1)

/-- Determinant identity for the explicit even-spectrum quintic. -/
def detMulNeg_eq_evenQuintic (t : ℤ) : Prop :=
  ∀ u : ℤ, -(u - 1) * (evenFactorLeft t u * evenFactorRight t u) = evenQuintic t u

/-- On the nonnegative `t`-axis the discriminant vanishes only at `t = 1`. -/
def discNonzeroAwayFromOne (t : ℤ) : Prop :=
  0 ≤ t → t ≠ 1 → discriminant t ≠ 0

lemma detMulNeg_eq_evenQuintic_holds (t : ℤ) : detMulNeg_eq_evenQuintic t := by
  intro u
  dsimp [detMulNeg_eq_evenQuintic, evenFactorLeft, evenFactorRight, evenQuintic]
  ring

lemma positive_discriminant_tail (t : ℤ) (ht : 0 ≤ t) : 0 < t ^ 2 + 1 := by
  have ht' : 0 ≤ t := ht
  nlinarith [ht']

lemma discNonzeroAwayFromOne_holds (t : ℤ) : discNonzeroAwayFromOne t := by
  intro ht hne
  have hsq : (t - 1) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr hne)
  have htail : t ^ 2 + 1 ≠ 0 := by
    have hpos := positive_discriminant_tail t ht
    linarith
  simpa [discriminant] using mul_ne_zero hsq htail

/-- Paper label: `prop:pom-a4t-even-zeta-quintic`. The explicit even-spectrum determinant factors
through two quadratic terms, and the displayed discriminant factorization leaves `t = 1` as the
only nonnegative degeneration point. -/
theorem paper_pom_a4t_even_zeta_quintic (t : ℤ) :
    detMulNeg_eq_evenQuintic t ∧ discNonzeroAwayFromOne t := by
  exact ⟨detMulNeg_eq_evenQuintic_holds t, discNonzeroAwayFromOne_holds t⟩

end Omega.POM
