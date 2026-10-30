/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Algebra.Ring.Equiv

/-!
# Peirce spine A₂₆–A₂₈: inner derivations by `Q_± = N_± N_∓` and graded derivations

* A₂₆ the inner derivations `[Q₊, ·]`, `[Q₋, ·]`, `[V, ·]`, `[Σ, ·]`;
* A₂₇ parities under `S = P - (1 - P)`: `N₊, N₋, Φ, J` are odd, `V, Σ` are even;
* A₂₈ graded derivations `d_x(Y) = x Y - (S Y S) x` and the codifferentials
  `d̄_x(Y) = x Y + (S Y S) x` for `x = N₊, N₋`: nilpotency, graded Leibniz rule,
  anticommutators.

**Correction to the intake.** A random `6 × 6` numerical model refutes the A₂₈
claim `d₊ d̄₋ + d̄₋ d₊ = [Σ, ·]`. The proved value is the Jordan
multiplication `{V, ·}`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def qgtPlus (P A C : B) : B := conePlus P A * coneMinus P C
def qgtMinus (P A C : B) : B := coneMinus P C * conePlus P A

def connV (P A C X : B) : B := comm (genV P A C) X
def connSig (P A C X : B) : B := comm (genSig P A C) X
def connPlus (P A C X : B) : B := comm (qgtPlus P A C) X
def connMinus (P A C X : B) : B := comm (qgtMinus P A C) X

/-- Grade inversion `X ↦ S X S`. -/
def parityConj (P X : B) : B := invS P * X * invS P

/-- `d₊(X) = N₊ X - (S X S) N₊`. -/
def superDerivPlus (P A X : B) : B := conePlus P A * X - parityConj P X * conePlus P A
/-- `d₋(X) = N₋ X - (S X S) N₋`. -/
def superDerivMinus (P C X : B) : B := coneMinus P C * X - parityConj P X * coneMinus P C
/-- `d̄₊(X) = N₊ X + (S X S) N₊`. -/
def superDerivPlusBar (P A X : B) : B := conePlus P A * X + parityConj P X * conePlus P A
/-- `d̄₋(X) = N₋ X + (S X S) N₋`. -/
def superDerivMinusBar (P C X : B) : B := coneMinus P C * X + parityConj P X * coneMinus P C
/-- `d_Φ = d₊ + d₋`. -/
def superDerivPhi (P A C X : B) : B := superDerivPlus P A X + superDerivMinus P C X
/-- `d_J = d₊ - d₋`. -/
def superDerivJ (P A C X : B) : B := superDerivPlus P A X - superDerivMinus P C X

variable {P : B} (hP : P * P = P)
include hP

/-! ### A₂₆ -/

theorem archetype_A26_qgt_inner_derivations (A C X : B) :
    connPlus P A C X + connMinus P A C X = connV P A C X ∧
    connPlus P A C X - connMinus P A C X = connSig P A C X ∧
    (2 : ℤ) • connPlus P A C X = connV P A C X + connSig P A C X ∧
    (2 : ℤ) • connMinus P A C X = connV P A C X - connSig P A C X ∧
    connPlus P A C (connMinus P A C X) = connMinus P A C (connPlus P A C X) ∧
    connV P A C (connSig P A C X) = connSig P A C (connV P A C X) ∧
    connPlus P A C (connMinus P A C X) =
      -(qgtPlus P A C * X * qgtMinus P A C + qgtMinus P A C * X * qgtPlus P A C) ∧
    connV P A C (conePlus P A) = 0 ∧
    connV P A C (coneMinus P C) = 0 ∧
    connV P A C (genPhi P A C) = 0 ∧
    connV P A C (genJ P A C) = 0 ∧
    connPlus P A C (conePlus P A) = genV P A C * conePlus P A ∧
    connMinus P A C (conePlus P A) = -(genV P A C * conePlus P A) ∧
    connPlus P A C (coneMinus P C) = -(genV P A C * coneMinus P C) ∧
    connMinus P A C (coneMinus P C) = genV P A C * coneMinus P C ∧
    connPlus P A C (genPhi P A C) = genV P A C * genJ P A C ∧
    connMinus P A C (genPhi P A C) = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [connV, connSig, connPlus, connMinus, qgtPlus, qgtMinus]); peirce_nf hP)

/-! ### A₂₇ -/

theorem archetype_A27_grading_parities (A C : B) :
    invS P * conePlus P A = conePlus P A ∧
    conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C = -coneMinus P C ∧
    coneMinus P C * invS P = coneMinus P C ∧
    anticomm (invS P) (conePlus P A) = 0 ∧
    anticomm (invS P) (coneMinus P C) = 0 ∧
    invS P * genPhi P A C = genJ P A C ∧
    genPhi P A C * invS P = -genJ P A C ∧
    invS P * genJ P A C = genPhi P A C ∧
    genJ P A C * invS P = -genPhi P A C ∧
    anticomm (invS P) (genPhi P A C) = 0 ∧
    anticomm (invS P) (genJ P A C) = 0 ∧
    invS P * qgtPlus P A C = qgtPlus P A C ∧
    invS P * qgtMinus P A C = -qgtMinus P A C ∧
    parityConj P (genV P A C) = genV P A C ∧
    parityConj P (genSig P A C) = genSig P A C ∧
    parityConj P (genPhi P A C) = -genPhi P A C ∧
    parityConj P (genJ P A C) = -genJ P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [qgtPlus, qgtMinus, parityConj]); peirce_nf hP)

/-- Ordered mixed-supercharge products. Their odd residuals lie in the
`N₋` corner for these factor orders; replacing them by `N₊` is false. -/
theorem mixed_supercharge_product_expansions (A C : B) :
    (1 + genJ P A C) * (1 - genPhi P A C) =
      1 - genSig P A C - (2 : ℤ) • coneMinus P C ∧
    (1 - genJ P A C) * (1 + genPhi P A C) =
      1 - genSig P A C + (2 : ℤ) • coneMinus P C ∧
    (1 - genPhi P A C) * (1 + genJ P A C) =
      1 + genSig P A C - (2 : ℤ) • coneMinus P C ∧
    (1 + genPhi P A C) * (1 - genJ P A C) =
      1 + genSig P A C + (2 : ℤ) • coneMinus P C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The swapped-corner version of the second mixed-product formula is valid
exactly when the doubled Peirce corners agree. This isolates the precise
extra condition hidden by replacing `N₋` with `N₊`. -/
theorem mixed_supercharge_wrong_corner_claim_iff (A C : B) :
    (1 - genJ P A C) * (1 + genPhi P A C) =
        1 - genSig P A C + (2 : ℤ) • conePlus P A ↔
      (2 : ℤ) • coneMinus P C = (2 : ℤ) • conePlus P A := by
  rw [(mixed_supercharge_product_expansions hP A C).2.1]
  constructor
  · intro h
    exact add_left_cancel h
  · intro h
    rw [h]

/-- Both swapped-corner formulas from the intake hold simultaneously exactly
when the two doubled Peirce corners agree. Their general residuals are both
in the `N₋` corner, with opposite `Σ` terms. -/
theorem mixed_supercharge_wrong_corner_claims_iff (A C : B) :
    ((1 - genJ P A C) * (1 + genPhi P A C) =
        1 - genSig P A C + (2 : ℤ) • conePlus P A ∧
      (1 + genPhi P A C) * (1 - genJ P A C) =
        1 + genSig P A C + (2 : ℤ) • conePlus P A) ↔
      (2 : ℤ) • coneMinus P C = (2 : ℤ) • conePlus P A := by
  constructor
  · rintro ⟨h₁, _⟩
    exact (mixed_supercharge_wrong_corner_claim_iff hP A C).1 h₁
  · intro h
    refine ⟨(mixed_supercharge_wrong_corner_claim_iff hP A C).2 h, ?_⟩
    rw [(mixed_supercharge_product_expansions hP A C).2.2.2, h]

/-- Conjugation by the Peirce reflection is an additive, multiplicative
involution of the ambient ring. This proves an involutive ring action; it does
not assert that any larger operator family is a Galois extension. -/
theorem parityConj_involutive_ring_action (X Y : B) :
    parityConj P (parityConj P X) = X ∧
    parityConj P (X * Y) = parityConj P X * parityConj P Y ∧
    parityConj P (X + Y) = parityConj P X + parityConj P Y ∧
    parityConj P 1 = 1 := by
  have hS : invS P * invS P = 1 := by
    simp only [invS]
    noncomm_ring [hP]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold parityConj
    calc
      invS P * (invS P * X * invS P) * invS P =
          (invS P * invS P) * X * (invS P * invS P) := by noncomm_ring
      _ = X := by rw [hS]; simp
  · unfold parityConj
    have hExpand :
        (invS P * X * invS P) * (invS P * Y * invS P) =
          invS P * X * (invS P * invS P) * Y * invS P := by
      noncomm_ring
    calc
      invS P * (X * Y) * invS P = invS P * X * Y * invS P := by noncomm_ring
      _ = invS P * X * (invS P * invS P) * Y * invS P := by
        rw [hS]
        simp
      _ = (invS P * X * invS P) * (invS P * Y * invS P) := hExpand.symm
  · unfold parityConj
    noncomm_ring
  · unfold parityConj
    calc
      invS P * 1 * invS P = invS P * invS P := by simp
      _ = 1 := hS

/-- The Peirce parity action as an actual ring equivalence. Its inverse is
itself; this packages the `C₂` action without asserting a larger Galois
extension. -/
def parityConjRingEquiv : RingEquiv B B where
  toFun := parityConj P
  invFun := parityConj P
  left_inv := by
    intro X
    exact (parityConj_involutive_ring_action hP X 1).1
  right_inv := by
    intro X
    exact (parityConj_involutive_ring_action hP X 1).1
  map_mul' := by
    intro X Y
    exact (parityConj_involutive_ring_action hP X Y).2.1
  map_add' := by
    intro X Y
    exact (parityConj_involutive_ring_action hP X Y).2.2.1

/-- The fixed elements of parity conjugation are exactly the centralizer of
the Peirce grading involution. No characteristic restriction is needed. -/
theorem parityConj_fixed_iff_commutes_with_grading (X : B) :
    parityConj P X = X ↔ invS P * X = X * invS P := by
  have hS : invS P * invS P = 1 := by
    simp only [invS]
    noncomm_ring [hP]
  constructor
  · intro h
    unfold parityConj at h
    calc
      invS P * X = invS P * X * (invS P * invS P) := by rw [hS, mul_one]
      _ = (invS P * X * invS P) * invS P := by noncomm_ring
      _ = X * invS P := by rw [h]
  · intro h
    unfold parityConj
    calc
      invS P * X * invS P = X * invS P * invS P := by rw [h]
      _ = X * (invS P * invS P) := by rw [mul_assoc]
      _ = X := by rw [hS, mul_one]

theorem parityConj_fixed_iff_commutator_zero (X : B) :
    parityConj P X = X ↔ comm (invS P) X = 0 := by
  rw [parityConj_fixed_iff_commutes_with_grading hP, comm, sub_eq_zero]

/-! ### A₂₈ -/

theorem archetype_A28_graded_derivations (A C X Y : B) :
    superDerivPlus P A (superDerivPlus P A X) = 0 ∧
    superDerivMinus P C (superDerivMinus P C X) = 0 ∧
    superDerivPlusBar P A (superDerivPlusBar P A X) = 0 ∧
    superDerivMinusBar P C (superDerivMinusBar P C X) = 0 ∧
    superDerivPlus P A (X * Y) =
      superDerivPlus P A X * Y + parityConj P X * superDerivPlus P A Y ∧
    superDerivMinus P C (X * Y) =
      superDerivMinus P C X * Y + parityConj P X * superDerivMinus P C Y ∧
    superDerivPlus P A (superDerivMinus P C X) +
      superDerivMinus P C (superDerivPlus P A X) = connV P A C X ∧
    superDerivPhi P A C (superDerivPhi P A C X) = connV P A C X ∧
    superDerivJ P A C (superDerivJ P A C X) = -connV P A C X ∧
    superDerivPhi P A C (superDerivJ P A C X) + superDerivJ P A C (superDerivPhi P A C X) = 0 ∧
    superDerivPlus P A (superDerivMinusBar P C X) +
      superDerivMinusBar P C (superDerivPlus P A X) = anticomm (genV P A C) X ∧
    superDerivPlus P A (coneMinus P C) = genV P A C ∧
    superDerivMinus P C (conePlus P A) = genV P A C ∧
    superDerivPlusBar P A (coneMinus P C) = genSig P A C ∧
    superDerivMinusBar P C (conePlus P A) = -genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [superDerivPhi, superDerivJ, superDerivPlus, superDerivMinus, superDerivPlusBar,
      superDerivMinusBar, parityConj, connV]); peirce_nf hP)

end InfoGeometry.OperatorAlgebra.PeirceSpine
