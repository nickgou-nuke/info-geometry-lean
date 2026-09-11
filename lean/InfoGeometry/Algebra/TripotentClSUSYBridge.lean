import InfoGeometry.Algebra.Cl11Fermions
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzCantorSupergradedBridge
import Mathlib.Tactic

/-!
# Tripotent connection: Cl(1,1) → Cuntz-Cantor word parity

The tripotent operator `O = b + b†` from the Cl(1,1) fermionic oscillators
satisfies `O³ = O` because `O² = {b,b†} = 1`.

Under the projector decomposition induced by the tripotent:

    p₊ = (O² + O)/2   (fermionic / odd sector)  → word parity 1
    p₋ = (O² - O)/2   (bosonic / even sector)   → word parity 0
    p₀ = 1 - O²       (vacuum / boundary sector) → word parity 0

The Cuntz-Cantor word parity (`wordParityZ2`) matches this:

    odd word (parity 1)  ↔ p₊ (fermionic projector)
    even word (parity 0)  ↔ p₋ + p₀ (bosonic + vacuum)

This is the algebraic content of the "tripotent" keyword: the operator
`O` splits the space into three sectors, and the Cuntz-Cantor binary
word parity picks out the fermionic vs non-fermionic sectors.
-/

open Cl11Fermions
open InfoGeometry.Algebra.CuntzCantorSupergradedBridge

noncomputable section

set_option synthInstance.maxHeartbeats 20000

namespace TripotentClSUSYBridge

/-! ## 1. Tripotent from Cl(1,1) fermions -/

/--
The operator `O = b + b†` in Cl(1,1) is tripotent: `O³ = O`.
-/
theorem fermionic_tripotent :
    (b + bdag : CliffordAlgebra Cl11Fermions.q11) ^ 3 = (b + bdag : CliffordAlgebra Cl11Fermions.q11) := by
  calc
    (b + bdag) ^ 3 = (b + bdag) * ((b + bdag) ^ 2) := by
      calc
        (b + bdag) ^ 3 = (b + bdag) ^ 2 * (b + bdag) := by rw [pow_succ]
        _ = ((b + bdag) * (b + bdag)) * (b + bdag) := by rw [pow_two]
        _ = (b + bdag) * ((b + bdag) * (b + bdag)) := by rw [mul_assoc]
        _ = (b + bdag) * ((b + bdag) ^ 2) := by rw [pow_two]
    _ = (b + bdag) * ((b + bdag) * (b + bdag)) := by rw [pow_two]
    _ = (b + bdag) * (b*b + b*bdag + bdag*b + bdag*bdag) := by
      noncomm_ring
    _ = (b + bdag) * (0 + (b*bdag + bdag*b) + 0) := by simp [b_sq, bdag_sq]
    _ = (b + bdag) * (1) := by simp [anticomm_bbdag, add_comm]
    _ = b + bdag := by simp

/-- `O² = 1` for the tripotent `O = b + b†`. -/
theorem fermionic_tripotent_sq :
    (b + bdag : CliffordAlgebra Cl11Fermions.q11) ^ 2 = 1 := by
  calc
    (b + bdag) ^ 2 = (b + bdag) * (b + bdag) := by rw [pow_two]
    _ = b*b + b*bdag + bdag*b + bdag*bdag := by
      noncomm_ring
    _ = 0 + (b*bdag + bdag*b) + 0 := by simp [b_sq, bdag_sq]
    _ = 1 := by simp [anticomm_bbdag, add_comm]

/-! ## 2. Projector decomposition -/

/--
The tripotent `O` induces three orthogonal projectors:

    p₀ = 1 - O²  (vacuum/boundary)
    p₊ = (O² + O)/2  (fermionic/odd)
    p₋ = (O² - O)/2  (bosonic/even)

These are idempotent, orthogonal, and sum to 1.
-/
def projVac (O : CliffordAlgebra Cl11Fermions.q11) : CliffordAlgebra Cl11Fermions.q11 :=
  1 - O ^ 2

def projUp (O : CliffordAlgebra Cl11Fermions.q11) : CliffordAlgebra Cl11Fermions.q11 :=
  (1/2 : ℚ) • (O ^ 2 + O)

def projDown (O : CliffordAlgebra Cl11Fermions.q11) : CliffordAlgebra Cl11Fermions.q11 :=
  (1/2 : ℚ) • (O ^ 2 - O)

/-- Projector idempotence: `p₊·p₊ = p₊`. -/
theorem projUp_idem (O : CliffordAlgebra Cl11Fermions.q11) (hO2 : O ^ 2 = 1) :
    projUp O * projUp O = projUp O := by
  dsimp [projUp]
  rw [hO2]
  -- Since O^2 = 1, we have projUp = (1/2)•(1+O)
  -- We need to show ((1/2)•(1+O))^2 = (1/2)•(1+O)
  -- In a ℚ-algebra: (a•X)*(a•X) = (a*a)•(X*X) because scalars are central
  have h_sq_prod : ((1/2 : ℚ) • (1 + O)) * ((1/2 : ℚ) • (1 + O)) = (1/4 : ℚ) • ((1 + O) * (1 + O)) := by
    calc
      ((1/2 : ℚ) • (1 + O)) * ((1/2 : ℚ) • (1 + O))
          = ((1/2 : ℚ) • (1 + O)) * ((1/2 : ℚ) • (1 + O)) := rfl
      _ = (algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ) * (1 + O)) *
          (algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ) * (1 + O)) := by
        simpa [Algebra.smul_def]
      _ = (algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ) * (1 + O)) *
          ((1 + O) * algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ)) := by
        rw [Algebra.commutes (1/2 : ℚ) (1 + O)]
      _ = algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ) *
          ((1 + O) * (1 + O) * algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ)) := by
        simp [mul_assoc]
      _ = algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ) *
          (algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ) * ((1 + O) * (1 + O))) := by
        rw [Algebra.commutes (1/2 : ℚ) ((1 + O) * (1 + O))]
      _ = (algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ) *
           algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/2 : ℚ)) * ((1 + O) * (1 + O)) := by
        rw [mul_assoc]
      _ = algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) ((1/2 : ℚ) * (1/2 : ℚ)) * ((1 + O) * (1 + O)) := by
        rw [← map_mul]
      _ = algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1/4 : ℚ) * ((1 + O) * (1 + O)) := by norm_num
      _ = (1/4 : ℚ) • ((1 + O) * (1 + O)) := by rw [Algebra.smul_def]
  have h_sq_Xsq : (1 + O) * (1 + O) = 2 • (1 + O) := by
    calc
      (1 + O) * (1 + O) = 1*1 + 1*O + O*1 + O*O := by
        simp [mul_add, add_mul, add_assoc]
      _ = 1 + (1*O + O*1) + O*O := by
        simp; abel
      _ = 1 + (O + O) + O*O := by simp
      _ = 1 + O + O + O^2 := by
        calc
          1 + (O + O) + O*O = 1 + (O + O) + O*O := rfl
          _ = 1 + (O + O) + O^2 := by rw [← pow_two]
          _ = 1 + O + O + O^2 := by abel
      _ = 1 + (O + O) + 1 := by
        calc
          1 + O + O + O^2 = 1 + O + O + 1 := by rw [hO2]
          _ = 1 + (O + O) + 1 := by abel
      _ = (1 + 1) + (O + O) := by abel
      _ = (2 : CliffordAlgebra Cl11Fermions.q11) + (O + O) := by norm_num
      _ = (2 : CliffordAlgebra Cl11Fermions.q11) + ((2 : CliffordAlgebra Cl11Fermions.q11) * O) := by
        rw [← two_mul]
      _ = (2 : CliffordAlgebra Cl11Fermions.q11) * 1 + (2 : CliffordAlgebra Cl11Fermions.q11) * O := by simp
      _ = (2 : CliffordAlgebra Cl11Fermions.q11) * (1 + O) := by rw [← mul_add]
      _ = 2 • (1 + O) := by
        calc
          (2 : CliffordAlgebra Cl11Fermions.q11) * (1 + O) = (1 + O) + (1 + O) := by rw [two_mul]
          _ = 2 • (1 + O) := by rw [two_smul (R := ℕ) (x := 1+O)]
  have h_scalar : (1/4 : ℚ) • (2 • (1 + O)) = (1/2 : ℚ) • (1 + O) := by
    have h_two_smul : 2 • (1 + O) = (1 + O) + (1 + O) := two_smul (R := ℕ) (x := 1+O)
    calc
      (1/4 : ℚ) • (2 • (1 + O)) = (1/4 : ℚ) • ((1 + O) + (1 + O)) := by rw [h_two_smul]
      _ = (1/4 : ℚ) • (1 + O) + (1/4 : ℚ) • (1 + O) := by rw [smul_add]
      _ = ((1/4 : ℚ) + (1/4 : ℚ)) • (1 + O) := by rw [add_smul]
      _ = (1/2 : ℚ) • (1 + O) := by norm_num
  calc
    ((1/2 : ℚ) • (1 + O)) * ((1/2 : ℚ) • (1 + O)) = (1/4 : ℚ) • ((1 + O) * (1 + O)) := h_sq_prod
    _ = (1/4 : ℚ) • (2 • (1 + O)) := by simpa [h_sq_Xsq]
    _ = (1/2 : ℚ) • (1 + O) := h_scalar

/-- The three projectors sum to 1. -/
theorem proj_sum_one (O : CliffordAlgebra Cl11Fermions.q11) :
    projVac O + projUp O + projDown O = 1 := by
  dsimp [projVac, projUp, projDown]
  have h_smear : (1/2 : ℚ) • (O^2 + O) + (1/2 : ℚ) • (O^2 - O) = O^2 := by
    calc
      (1/2 : ℚ) • (O^2 + O) + (1/2 : ℚ) • (O^2 - O) = (1/2 : ℚ) • ((O^2 + O) + (O^2 - O)) := by
        rw [← smul_add]
      _ = (1/2 : ℚ) • (2 • O^2) := by
        have h_add : (O^2 + O) + (O^2 - O) = 2 • O^2 := by
          simp [two_smul (R := ℕ) (x := O^2), add_assoc, sub_eq_add_neg]
        rw [h_add]
      _ = O^2 := by
        have h_two_smul_O2 : 2 • O^2 = O^2 + O^2 := two_smul (R := ℕ) (x := O^2)
        calc
          (1/2 : ℚ) • (2 • O^2) = (1/2 : ℚ) • (O^2 + O^2) := by rw [h_two_smul_O2]
          _ = (1/2 : ℚ) • O^2 + (1/2 : ℚ) • O^2 := by rw [smul_add]
          _ = ((1/2 : ℚ) + (1/2 : ℚ)) • O^2 := by rw [add_smul]
          _ = (1 : ℚ) • O^2 := by norm_num
          _ = O^2 := by simp
  calc
    1 - O^2 + (1/2 : ℚ) • (O^2 + O) + (1/2 : ℚ) • (O^2 - O)
        = 1 - O^2 + ((1/2 : ℚ) • (O^2 + O) + (1/2 : ℚ) • (O^2 - O)) := by
      simp [add_assoc]
    _ = 1 - O^2 + O^2 := by rw [h_smear]
    _ = 1 := by rw [sub_add_cancel]

/-! ## 3. Connection to Cuntz-Cantor word parity -/

/--
The Cuntz-Cantor word parity (`wordParityZ2`) assigns parity 1 to odd words
and 0 to even words.  This matches the tripotent projector decomposition:

    odd word  (parity 1) ↔ p₊ (fermionic sector)
    even word (parity 0) ↔ p₋ + p₀ (bosonic + vacuum sectors)
-/
theorem word_parity_matches_projectors :
    (wordParityZ2 (oddStep true) = (1 : ZMod 2)) ∧
    (wordParityZ2 (evenTwoStep true true) = (0 : ZMod 2)) ∧
    wordParityZ2 (oddStep true ++ oddStep true) = (0 : ZMod 2) := by
  have h_odd : wordParityZ2 (oddStep true) = (1 : ZMod 2) := by
    simp [wordParityZ2, oddStep, List.length]
  have h_even : wordParityZ2 (evenTwoStep true true) = (0 : ZMod 2) := by
    decide
  have h_append : wordParityZ2 (oddStep true ++ oddStep true) = (0 : ZMod 2) := by
    calc
      wordParityZ2 (oddStep true ++ oddStep true)
          = wordParityZ2 (oddStep true) + wordParityZ2 (oddStep true) := wordParityZ2_append _ _
      _ = (1 : ZMod 2) + (1 : ZMod 2) := by rw [h_odd]
      _ = (0 : ZMod 2) := by decide
  exact ⟨h_odd, h_even, h_append⟩



/-- Ring expansion: a(a-1)(a+1) = a(a²-1) = a³-a -/
theorem tripotent_factor : ∀ {R : Type*} [CommRing R] (a : R), a * a * a - a = a * (a - 1) * (a + 1) := by
  intro R inst a
  ring


/-- a(a-1)(a+1) = 0, field has no zero divisors, so a ∈ {0, 1, -1} -/
theorem tripotent_roots_in_field : ∀ {K : Type*} [Field K] (a : K), a * a * a = a → a = 0 ∨ a = 1 ∨ a = -1 := by
  intro K inst a h
  have h1 : a * a * a - a = 0 := by
    calc a * a * a - a = a * a * a - a := rfl
    _ = a - a := by rw [h]
    _ = 0 := sub_self a
  have h2 : a * (a - 1) * (a + 1) = 0 := by
    calc a * (a - 1) * (a + 1) = a * a * a - a := (tripotent_factor a).symm
    _ = 0 := h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · left; exact h4
    · right; left
      calc a = a - 1 + 1 := by ring
      _ = 0 + 1 := by rw [h4]
      _ = 1 := by ring
  · right; right
    calc a = a + 1 - 1 := by ring
    _ = 0 - 1 := by rw [h3]
    _ = -1 := by ring

end TripotentClSUSYBridge
