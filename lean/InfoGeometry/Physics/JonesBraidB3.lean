import Mathlib
import InfoGeometry.Physics.TLChain

/-!
# Jones Braid Representation of B₃ at Kauffman point A = i

Algebraic proof of the Artin braid relation using the TL₃(2) relations.

```
s₀ = i·(I - e₀)
s₁ = i·(I - e₁)
```

The Artin relation `s₀s₁s₀ = s₁s₀s₁` reduces algebraically to
`(I - e₀)(I - e₁)(I - e₀) = (I - e₁)(I - e₀)(I - e₁)`, which follows
from `e₀² = 2e₀`, `e₁² = 2e₁`, `e₀e₁e₀ = e₀`, `e₁e₀e₁ = e₁`.
-/

noncomputable section

namespace JonesBraidB3

open Matrix
open InfoGeometry.Physics.TLChain

/-- First braid generator: s₀ = i·(I - e₀). -/
def s0 : Matrix (Fin 8) (Fin 8) ℂ :=
  Complex.I • ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0)

/-- Second braid generator: s₁ = i·(I - e₁). -/
def s1 : Matrix (Fin 8) (Fin 8) ℂ :=
  Complex.I • ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1)

/-- Artin braid relation: s₀·s₁·s₀ = s₁·s₀·s₁.

Proof: factor out i³ = -i on both sides, reducing to
`(I - e₀)(I - e₁)(I - e₀) = (I - e₁)(I - e₀)(I - e₁)`.

Both sides expand to `I - e₀ - e₁ + e₀e₁ + e₁e₀` using the
TL₃(2) relations from `TLChain.lean`. -/
theorem artin_braid_relation : s0 * s1 * s0 = s1 * s0 * s1 := by
  dsimp [s0, s1]
  -- Factor out i³ = -i from both sides
  -- LHS: (i·A)(i·B)(i·A) = i³·(A·B·A) = -i·(A·B·A)
  -- RHS: (i·B)(i·A)(i·B) = i³·(B·A·B) = -i·(B·A·B)
  -- Both sides equal iff A·B·A = B·A·B where A = I-e₀, B = I-e₁
  -- Prove (I-e₀)(I-e₁)(I-e₀) = (I-e₁)(I-e₀)(I-e₁)
  have h_central : ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) *
      ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) *
      ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) =
      ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) *
      ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) *
      ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) := by
    -- Expand both sides and use TL relations
    -- LHS: (I - e₀ - e₁ + e₀e₁)(I - e₀)
    --     = ... = I - e₀ - e₁ + e₀e₁ + e₁e₀
    -- RHS: same
    calc
      ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) * ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) *
        ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0)
          = ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0 - e1 + e0 * e1) *
            ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) := by
        noncomm_ring
      _ = ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0 - e1 + e0 * e1) -
          ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0 - e1 + e0 * e1) * e0 := by
        rw [mul_sub, mul_one]
      _ = ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0 - e1 + e0 * e1) -
          (e0 - e0 * e0 - e1 * e0 + e0 * e1 * e0) := by
        noncomm_ring
      _ = ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0 - e1 + e0 * e1) -
          (e0 - (2 : ℂ) • e0 - e1 * e0 + e0) := by
        rw [e0_sq, e0_mul_e1_mul_e0]
      _ = ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0 - e1 + e0 * e1) - (-(e1 * e0)) := by
        simp [two_smul]; abel
      _ = (1 : Matrix (Fin 8) (Fin 8) ℂ) - e0 - e1 + e0 * e1 + e1 * e0 := by
        abel
      _ = (1 : Matrix (Fin 8) (Fin 8) ℂ) - e1 - e0 + e1 * e0 + e0 * e1 := by
        abel
      _ = ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1 - e0 + e1 * e0) -
          (e1 - e1 * e1 - e0 * e1 + e1 * e0 * e1) := by
        rw [e1_sq, e1_mul_e0_mul_e1]
        simp [two_smul]; abel
      _ = ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1 - e0 + e1 * e0) -
          ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1 - e0 + e1 * e0) * e1 := by
        noncomm_ring
      _ = ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1 - e0 + e1 * e0) *
        ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) := by
        rw [mul_sub, mul_one]
      _ = ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) * ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) *
        ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) := by
        noncomm_ring
  -- Now use h_central to prove the full relation
  have hi_cube : (Complex.I * Complex.I * Complex.I : ℂ) = -Complex.I := by
    norm_num [Complex.I_sq]
  calc
    (Complex.I • ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0)) *
      (Complex.I • ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1)) *
      (Complex.I • ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0))
        = ((Complex.I * Complex.I * Complex.I : ℂ) •
          (((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) *
           ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) *
           ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0))) := by
      simp [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (-Complex.I) • (((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) *
        ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) *
        ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0)) := by
      rw [hi_cube]
    _ = (-Complex.I) • (((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) *
        ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) *
        ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1)) := by
      rw [h_central]
    _ = ((Complex.I * Complex.I * Complex.I : ℂ) •
        (((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1) *
         ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0) *
         ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1))) := by
      rw [hi_cube]
    _ = (Complex.I • ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1)) *
        (Complex.I • ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e0)) *
        (Complex.I • ((1 : Matrix (Fin 8) (Fin 8) ℂ) - e1)) := by
      simp [smul_mul_assoc, mul_smul_comm, smul_smul]

#check artin_braid_relation

end JonesBraidB3
