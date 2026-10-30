import Mathlib.Tactic

namespace Omega.Zeta

lemma xi_finite_prime_refutation_audit_int_eq_zero_of_natAbs_lt_of_dvd {q : ℕ} {z : ℤ}
    (hz : Int.natAbs z < q) (hdiv : (q : ℤ) ∣ z) : z = 0 := by
  rcases hdiv with ⟨k, rfl⟩
  by_cases hk : k = 0
  · simp [hk]
  · have hkabs : 0 < Int.natAbs k := Int.natAbs_pos.mpr hk
    have hq : q ≤ Int.natAbs ((q : ℤ) * k) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.le_mul_of_pos_right q hkabs
    exact False.elim (Nat.not_lt_of_ge hq hz)

/-- Paper label: `prop:xi-finite-prime-refutation-audit`. If every integer residual entry is
divisible by a finite product and that product is strictly larger than twice every entry's
absolute value, then all residual entries vanish. No primality property of the factors is
needed for this implication. -/
theorem paper_xi_finite_prime_refutation_audit {n d : ℕ} (F : Fin n → Fin d → ℤ)
    (P : Finset ℕ)
    (hdiv : ∀ i j, (((∏ p ∈ P, p) : ℕ) : ℤ) ∣ F i j)
    (hbound : ∀ i j, 2 * Int.natAbs (F i j) < ∏ p ∈ P, p) : F = 0 := by
  ext i j
  apply xi_finite_prime_refutation_audit_int_eq_zero_of_natAbs_lt_of_dvd
  · have hentry : Int.natAbs (F i j) ≤ 2 * Int.natAbs (F i j) := by omega
    exact lt_of_le_of_lt hentry (hbound i j)
  · exact hdiv i j

end Omega.Zeta
