import Mathlib
import proofs.ChiralCausalCone

/-!
# Chiral Fierz Completeness — Swap = CPT compass + chiral solders

The Fierz identity in the chiral Pauli basis `{I, σ⁺, σ⁻, σ₃}` on `M₂(ℂ) ⊗ₖ M₂(ℂ)`:

  ½(I⊗ₖI + σ₃⊗ₖσ₃) + σ⁺⊗ₖσ⁻ + σ⁻⊗ₖσ⁺ = Swap

The swap operator τ that exchanges tensor factors is the Fierz dual of
the CPT compass alignment and chiral raising/lowering operators.

Zero sorries, zero axioms. Canonical `kroneckerMap` + `fin_cases`.
-/

namespace FierzIdentities

open Matrix
open ChiralCausalCone

/-- The swap operator on `M₂(ℂ) ⊗ₖ M₂(ℂ)` ≅ `M₄(ℂ)`.
Exchanges the two tensor slots: `|ab⟩ ↦ |ba⟩`.
Swap (a,b) (c,d) = δ_{a,d} · δ_{b,c}. -/
def Swap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  λ ⟨a, b⟩ ⟨c, d⟩ => if a = d ∧ b = c then 1 else 0

/-- Kronecker product shorthand. -/
local notation A "⊗ₖ" B => Matrix.kroneckerMap (fun a b : ℂ => a * b) A B

/-- **Chiral Fierz identity**: the swap operator decomposes into the CPT compass
alignment `½(I⊗ₖI + σ₃⊗ₖσ₃)` plus the chiral solders `σ⁺⊗ₖσ⁻ + σ⁻⊗ₖσ⁺`. -/
theorem chiral_fierz_identity :
    (1/2 : ℂ) • (Matrix.kroneckerMap (fun (a b : ℂ) => a * b) (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Matrix.kroneckerMap (fun (a b : ℂ) => a * b) σ3c σ3c) +
    Matrix.kroneckerMap (fun (a b : ℂ) => a * b) σPlus σMinus +
    Matrix.kroneckerMap (fun (a b : ℂ) => a * b) σMinus σPlus = Swap := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [Swap, kroneckerMap, σPlus, σMinus, σ3c] <;> ring

end FierzIdentities
