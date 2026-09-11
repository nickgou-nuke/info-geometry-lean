import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Möbius parity and Möbius/glide-twisted Witten index

This module records finite cancellation and parity facts for a
Möbius/glide-twisted Witten index:

* positive-energy SUSY pairs cancel in a `G(-1)^F exp(-βH)` trace;
* on the Brillouin Klein fixed line, `pg` glide parity extinguishes odd modes.
-/

noncomputable section

namespace MobiusWittenKleinIndex

/-! ## Twisted Witten index cancellation -/

/-- One positive-energy supersymmetric boson/fermion doublet with the same glide eigenvalue. -/
structure SUSYPair where
  weight : ℂ
  glideEigenvalue : ℂ

/-- Contribution of one paired doublet to `Tr G(-1)^F e^{-βH}`. -/
def pairContribution (P : SUSYPair) : ℂ :=
  P.glideEigenvalue * P.weight - P.glideEigenvalue * P.weight

/-- Positive-energy superpairs cancel exactly. -/
theorem pairContribution_zero (P : SUSYPair) : pairContribution P = 0 := by
  unfold pairContribution
  ring

/-! ## Brillouin Klein fixed-line glide filter -/

/-- `pg` glide phase. -/
def pgPhase (k : ℕ) : ℂ := (-1 : ℂ) ^ k

/-- Odd fixed-line modes have phase `-1`. -/
theorem pgPhase_odd {k : ℕ} (hodd : Odd k) : pgPhase k = -1 := by
  simpa [pgPhase] using hodd.neg_one_pow

/-- Odd fixed-line Fourier coefficients vanish. -/
theorem pg_fixed_line_extinction {k : ℕ} {c : ℂ}
    (hodd : Odd k) (hrel : c = pgPhase k * c) : c = 0 := by
  rw [pgPhase_odd hodd] at hrel
  have hneg : c = -c := by simpa using hrel
  have hsub : c - (-c) = 0 := sub_eq_zero.mpr hneg
  have h2 : (2 : ℂ) * c = 0 := by
    calc
      (2 : ℂ) * c = c - (-c) := by ring
      _ = 0 := hsub
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Nonzero fixed-line modes cannot be odd. -/
theorem surviving_fixed_line_mode_not_odd {k : ℕ} {c : ℂ}
    (hrel : c = pgPhase k * c) (hnz : c ≠ 0) : ¬ Odd k := by
  intro hodd
  apply hnz
  exact pg_fixed_line_extinction hodd hrel

/-- Consolidated finite Witten-index and glide-parity synthesis. -/
theorem mobius_witten_klein_index_synthesis :
    (∀ P : SUSYPair, pairContribution P = 0) ∧
    (∀ {k : ℕ} {c : ℂ}, Odd k → c = pgPhase k * c → c = 0) ∧
    (∀ {k : ℕ} {c : ℂ}, c = pgPhase k * c → c ≠ 0 → ¬ Odd k) := by
  exact ⟨fun P => pairContribution_zero P,
    fun hodd hrel => pg_fixed_line_extinction hodd hrel,
    fun hrel hnz => surviving_fixed_line_mode_not_odd hrel hnz⟩

end MobiusWittenKleinIndex
