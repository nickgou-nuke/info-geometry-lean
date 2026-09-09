import Mathlib

open Complex Matrix BigOperators

-- 1. Restrict the index set for the Vandermonde matrix to exactly N = 2^k basis states.
-- Each split (⊕) models the inclusion/exclusion of the k-th prime (fermionic primon).
@[reducible]
def PrimonIdx : ℕ → Type
  | 0 => Fin 1
  | k + 1 => PrimonIdx k ⊕ PrimonIdx k

-- Help Lean infer Fintype across the inductive hierarchy for the 2^k states
instance (k : ℕ) : Fintype (PrimonIdx k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype (Fin 1))
  | succ k ih => exact @instFintypeSum _ _ ih ih

-- Help Lean infer DecidableEq across the inductive hierarchy
instance (k : ℕ) : DecidableEq (PrimonIdx k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq (Fin 1))
  | succ k ih => exact @instDecidableEqSum _ _ ih ih

-- 2. Ensure the scalars used for the Vandermonde evaluation map are over the Complex numbers ℂ.
def vandermondeMatrix : (k : ℕ) → Matrix (PrimonIdx k) (PrimonIdx k) ℂ
  | 0 => fun _ _ => 1
  | k + 1 => fromBlocks (vandermondeMatrix k) (vandermondeMatrix k) 0 (vandermondeMatrix k)

-- 3. Integrate the ℤ₂-grading parity operator directly onto the inverse matrix.
-- The (-M) in the top-right block maps the Möbius function to the Pin(5,5) parity flip,
-- where each new distinct prime factor introduces a fermion parity flip.
def mobiusMatrix : (k : ℕ) → Matrix (PrimonIdx k) (PrimonIdx k) ℂ
  | 0 => fun _ _ => 1
  | k + 1 => fromBlocks (mobiusMatrix k) (-mobiusMatrix k) 0 (mobiusMatrix k)

-- 4. Prove that the inverse of this 2^k × 2^k Vandermonde matrix generates the Möbius inversion homomorphism.
-- 5. Verify completely with no proof placeholders or custom axioms.
theorem vandermonde_mobius_inv : ∀ (k : ℕ), vandermondeMatrix k * mobiusMatrix k = 1
  | 0 => by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      have : i = j := by omega
      subst this
      have : hi = hj := rfl
      subst this
      change ∑ x : Fin 1, (1 : ℂ) * (1 : ℂ) = if (⟨i, hi⟩ : Fin 1) = ⟨i, hi⟩ then 1 else 0
      simp
  | k + 1 => by
      unfold vandermondeMatrix mobiusMatrix
      have ih := vandermonde_mobius_inv k
      rw [fromBlocks_multiply]
      simp [ih]
