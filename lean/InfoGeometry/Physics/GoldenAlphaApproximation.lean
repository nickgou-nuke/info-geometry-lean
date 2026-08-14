import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import InfoGeometry.BostConnes.BostConnesParity
import InfoGeometry.Physics.PellisFineStructure

/-!
# Pellis numerical readout

This file defines and bounds the following real expression:

  α⁻¹ ≈ 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵

where φ = (1 + √5)/2 is the golden ratio.

The remaining declarations are arithmetic identities and interval estimates;
they do not identify the readout with a physical constant.
-/

namespace InfoGeometry.Physics.GoldenAlphaApproximation

open InfoGeometry.BostConnes

/-- The scalar `(1 + √5) / 2`. -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- The displayed real rational expression in `goldenRatio`. -/
noncomputable def pellis_alpha_inv : ℝ :=
  360 / goldenRatio^2 - 2 / goldenRatio^3 + 1 / (3 * goldenRatio)^5

/-- 
  ARITHMETIC FOUNDATION LEMMA:

  The Möbius function decomposes as the squarefree projection of Liouville
  parity.  The theorem is the arithmetic identity only; Fock-space,
  Witten-index, and determinant interpretations are separate owner obligations.
-/
theorem arithmetic_foundation :
    ∀ n : ℕ, ArithmeticFunction.moebius n = squarefreeProj n * liouvilleParity n := by
  intro n
  exact moebius_eq_squarefreeProj_mul_liouvilleParity n

/-- 
  PAULI EXCLUSION COROLLARY:

  On non-squarefree integers, `μ(n) = 0`.  This theorem is an arithmetic
  consequence of the Möbius/squarefree identity.
-/
theorem pauli_exclusion_arithmetic :
    ∀ n : ℕ, ¬Squarefree n → ArithmeticFunction.moebius n = 0 := by
  intro n hn
  exact moebius_eq_zero_of_not_squarefree hn

/-- 
  BOSONIC/FERMIONIC SECTOR DECOMPOSITION:

  The Liouville grading λ(n) = ±1 defines two sectors:
  - λ(n) = +1: bosonic (even Ω(n))
  - λ(n) = -1: fermionic (odd Ω(n))

  The Möbius function further restricts to squarefree sectors:
  - μ(n) ≠ 0: fermionic exterior algebra states
  - μ(n) = 0: Pauli-excluded non-squarefree states
-/
def is_bosonic_sector (n : ℕ) : Prop :=
  liouvilleParity n = 1

def is_fermionic_sector (n : ℕ) : Prop :=
  liouvilleParity n = -1

def is_mobius_active_sector (n : ℕ) : Prop :=
  ArithmeticFunction.moebius n ≠ 0

theorem mobius_active_iff_squarefree (n : ℕ) :
    is_mobius_active_sector n ↔ Squarefree n := by
  constructor
  · intro h
    by_contra hns
    have : ArithmeticFunction.moebius n = 0 := pauli_exclusion_arithmetic n hns
    contradiction
  · intro hs
    have := moebius_eq_liouvilleParity_of_squarefree hs
    have h_parity_ne_zero : liouvilleParity n ≠ 0 := by
      simp [liouvilleParity]
    simpa [is_mobius_active_sector, this] using h_parity_ne_zero

/-- 
  THEOREM: The Pellis readout falls within the empirical QED window.
  
  This proves the arithmetic inequality:
    137.0359991 < pellis_alpha_inv < 137.0359992
  
  The proof uses interval arithmetic and exact bounds on √5.
  No physical axioms are invoked; this is pure real arithmetic.
  
  No physical running-coupling, Witten-index, or zeta theorem is asserted here.
-/
theorem pellis_alpha_inv_bounds : 
    (1370359991 : ℝ) / 10000000 < pellis_alpha_inv ∧
      pellis_alpha_inv < (171294999 : ℝ) / 1250000 := by
  simpa [pellis_alpha_inv, goldenRatio, PellisFineStructure.pellis_alpha_inv,
    PellisFineStructure.phi] using PellisFineStructure.pellis_bounds

/-- 
  Corollary: the Pellis approximation lies within the displayed CODATA-window tolerance.
  
  CODATA 2018: α⁻¹ = 137.035999084(21)
  Pellis readout: 137.0359991647...
  
  The difference is approximately 8×10⁻⁸, well within the precision
  of this algebraic approximation.
  
  This is a numerical inequality only; no physical interpretation is proved.
-/
theorem pellis_alpha_inv_matches_codata :
    |pellis_alpha_inv - (137035999084 : ℝ) / 1000000000| < (1 : ℝ) / 10000000 := by
  simpa [pellis_alpha_inv, goldenRatio, PellisFineStructure.pellis_alpha_inv,
    PellisFineStructure.phi] using PellisFineStructure.codata_agreement

/-- 
  Interval-membership restatement of `pellis_alpha_inv_bounds`.
-/
theorem pellis_alpha_inv_in_interval :
    pellis_alpha_inv ∈ Set.Ioo ((1370359991 : ℝ) / 10000000) ((171294999 : ℝ) / 1250000) := by
  exact pellis_alpha_inv_bounds

end InfoGeometry.Physics.GoldenAlphaApproximation
