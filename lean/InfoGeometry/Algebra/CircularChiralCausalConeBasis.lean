/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornMatrix

/-!
# The Circular Chiral Causal Cone Basis (The Witt / Zorn Basis) of Split Octonions 𝕆ₛ

This module formalizes the native **Circular Chiral Causal Cone Basis**
$$(u^+, u^-, \sigma_1^+, \sigma_2^+, \sigma_3^+, \sigma_1^-, \sigma_2^-, \sigma_3^-) \equiv (E^+, E^-, \text{up}_1, \text{up}_2, \text{up}_3, \text{down}_1, \text{down}_2, \text{down}_3)$$
for the split-octonion algebra $\mathbb{O}_s \cong \text{Zorn}(R)$.

### Geometric and Physical Anatomy:
1. **Causal Horizon Vacuum Projectors**:
   - $u^+$ (`uPlus` / $E_{11}$): future causal vacuum pole / projector.
   - $u^-$ (`uMinus` / $E_{22}$): past causal vacuum pole / projector.
   - $(u^\pm)^2 = u^\pm$, $u^+ u^- = u^- u^+ = 0$, $u^+ + u^- = I$.
2. **Chiral Lightlike Rays (Null Parafermions)**:
   - $\sigma_i^+$ (`up i` / $U_i$): positive chiral null generators ($(\sigma_i^+)^2 = 0$).
   - $\sigma_i^-$ (`down i` / $V_i$): negative chiral null generators ($(\sigma_i^-)^2 = 0$).
3. **Chiral Collision / Annihilation**:
   - $\sigma_i^+ \sigma_j^- = \delta_{ij} u^+$
   - $\sigma_i^- \sigma_j^+ = \delta_{ij} u^-$
   - $\sigma_i^+ \sigma_j^- + \sigma_j^- \sigma_i^+ = \delta_{ij} I$ (Clifford supercharge anticommutator).

All proofs are complete in native Lean 4 + Mathlib with **0 sorrys, 0 admits, and 0 custom axioms**.
-/

namespace InfoGeometry.Algebra.CircularChiralCausalConeBasis

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

/-- The 8-element Circular Chiral Causal Cone Basis (The Witt Basis) of 𝕆ₛ. -/
inductive ChiralBasis : Type
  | uPlus            -- E⁺ / u⁺ (Future causal horizon pole)
  | uMinus           -- E⁻ / u⁻ (Past causal horizon pole)
  | up (i : Fin 3)   -- σ⁺₁, σ⁺₂, σ⁺₃ (Positive chiral lightlike rays)
  | down (i : Fin 3) -- σ⁻₁, σ⁻₂, σ⁻₃ (Negative chiral lightlike rays)
deriving DecidableEq, Repr

instance : Fintype ChiralBasis :=
  Fintype.ofEquiv (Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 3)
    { toFun := fun | .inl () => .uPlus
                   | .inr (.inl ()) => .uMinus
                   | .inr (.inr (.inl i)) => .up i
                   | .inr (.inr (.inr i)) => .down i
      invFun := fun | .uPlus => .inl ()
                    | .uMinus => .inr (.inl ())
                    | .up i => .inr (.inr (.inl i))
                    | .down i => .inr (.inr (.inr i))
      left_inv := by intro x; rcases x with _ | _ | _ | _ <;> rfl
      right_inv := by intro x; cases x <;> rfl }

/-- 🏆 THEOREM 1: The Circular Chiral Causal Cone Basis has dimension exactly 8. -/
theorem chiral_basis_card : Fintype.card ChiralBasis = 8 := by
  change Fintype.card (Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 3) = 8
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]

variable {R : Type*} [CommRing R]

/-- Canonical embedding of the 8-element Chiral Basis into the Zorn matrix split-octonions. -/
def toZorn (R : Type*) [CommRing R] : ChiralBasis → ZornMatrix R
  | ChiralBasis.uPlus => E11
  | ChiralBasis.uMinus => E22
  | ChiralBasis.up i => U i
  | ChiralBasis.down i => V i

/-- 🏆 THEOREM 2: The causal vacuum poles are orthogonal idempotents summing to identity. -/
theorem uPlus_sq : (toZorn R ChiralBasis.uPlus) * (toZorn R ChiralBasis.uPlus) = toZorn R ChiralBasis.uPlus :=
  E11_mul_E11

theorem uMinus_sq : (toZorn R ChiralBasis.uMinus) * (toZorn R ChiralBasis.uMinus) = toZorn R ChiralBasis.uMinus :=
  E22_mul_E22

theorem uPlus_mul_uMinus : (toZorn R ChiralBasis.uPlus) * (toZorn R ChiralBasis.uMinus) = 0 :=
  E11_mul_E22

theorem uMinus_mul_uPlus : (toZorn R ChiralBasis.uMinus) * (toZorn R ChiralBasis.uPlus) = 0 :=
  E22_mul_E11

theorem uPlus_add_uMinus : (toZorn R ChiralBasis.uPlus) + (toZorn R ChiralBasis.uMinus) = I :=
  E11_add_E22

/-- 🏆 THEOREM 3: All 6 chiral lightlike rays are strictly nilpotent (null rays). -/
theorem up_sq_zero (i : Fin 3) : (toZorn R (ChiralBasis.up i)) * (toZorn R (ChiralBasis.up i)) = 0 :=
  U_mul_self_zero i

theorem down_sq_zero (i : Fin 3) : (toZorn R (ChiralBasis.down i)) * (toZorn R (ChiralBasis.down i)) = 0 :=
  V_mul_self_zero i

/-- 🏆 THEOREM 4: Peirce chiral vacuum action. -/
theorem uPlus_mul_up (i : Fin 3) :
    (toZorn R ChiralBasis.uPlus) * (toZorn R (ChiralBasis.up i)) = toZorn R (ChiralBasis.up i) :=
  E11_mul_U i

theorem up_mul_uMinus (i : Fin 3) :
    (toZorn R (ChiralBasis.up i)) * (toZorn R ChiralBasis.uMinus) = toZorn R (ChiralBasis.up i) :=
  U_mul_E22 i

theorem uMinus_mul_down (i : Fin 3) :
    (toZorn R ChiralBasis.uMinus) * (toZorn R (ChiralBasis.down i)) = toZorn R (ChiralBasis.down i) :=
  E22_mul_V i

theorem down_mul_uPlus (i : Fin 3) :
    (toZorn R (ChiralBasis.down i)) * (toZorn R ChiralBasis.uPlus) = toZorn R (ChiralBasis.down i) :=
  V_mul_E11 i

theorem uMinus_mul_up (i : Fin 3) :
    (toZorn R ChiralBasis.uMinus) * (toZorn R (ChiralBasis.up i)) = 0 :=
  E22_mul_U i

theorem up_mul_uPlus (i : Fin 3) :
    (toZorn R (ChiralBasis.up i)) * (toZorn R ChiralBasis.uPlus) = 0 :=
  U_mul_E11 i

theorem uPlus_mul_down (i : Fin 3) :
    (toZorn R ChiralBasis.uPlus) * (toZorn R (ChiralBasis.down i)) = 0 :=
  E11_mul_V i

theorem down_mul_uMinus (i : Fin 3) :
    (toZorn R (ChiralBasis.down i)) * (toZorn R ChiralBasis.uMinus) = 0 :=
  V_mul_E22 i

/-- 🏆 THEOREM 5: Chiral collision / Causal contraction yielding vacuum states. -/
theorem up_mul_down (i j : Fin 3) :
    (toZorn R (ChiralBasis.up i)) * (toZorn R (ChiralBasis.down j)) =
      if i = j then toZorn R ChiralBasis.uPlus else 0 :=
  U_mul_V i j

theorem down_mul_up (i j : Fin 3) :
    (toZorn R (ChiralBasis.down i)) * (toZorn R (ChiralBasis.up j)) =
      if i = j then toZorn R ChiralBasis.uMinus else 0 :=
  V_mul_U i j

/-- 🏆 THEOREM 6: Exact Clifford supercharge anticommutator. -/
theorem up_down_anticommutator (i j : Fin 3) :
    (toZorn R (ChiralBasis.up i)) * (toZorn R (ChiralBasis.down j)) +
    (toZorn R (ChiralBasis.down j)) * (toZorn R (ChiralBasis.up i)) =
      if i = j then I else 0 :=
  U_V_anticommutator i j

/-- The Chirality operator $\chi = u^+ - u^-$. -/
def chiralityOp (R : Type*) [CommRing R] : ZornMatrix R :=
  toZorn R ChiralBasis.uPlus - toZorn R ChiralBasis.uMinus

/-- 🏆 THEOREM 7: Chirality is an involution ($\chi^2 = I$). -/
theorem chirality_sq : (chiralityOp R) * (chiralityOp R) = I := by
  dsimp [chiralityOp, toZorn]
  apply ZornMatrix.ext
  · simp [E11, E22, I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext k; fin_cases k <;>
      simp [E11, E22, I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext k; fin_cases k <;>
      simp [E11, E22, I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · simp [E11, E22, I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- The chirality operator acts by `+1` on the upper Peirce sector. -/
theorem chirality_mul_up (i : Fin 3) :
    chiralityOp R * toZorn R (ChiralBasis.up i) =
      toZorn R (ChiralBasis.up i) := by
  dsimp [chiralityOp, toZorn]
  apply ZornMatrix.ext
  · simp [E11, E22, U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext k; fin_cases i <;> fin_cases k <;>
      simp [E11, E22, U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis]
  · funext k; fin_cases i <;> fin_cases k <;>
      simp [E11, E22, U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis]
  · simp [E11, E22, U, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- The chirality operator acts by `-1` on the lower Peirce sector. -/
theorem chirality_mul_down (i : Fin 3) :
    chiralityOp R * toZorn R (ChiralBasis.down i) =
      smul (-1 : R) (toZorn R (ChiralBasis.down i)) := by
  dsimp [chiralityOp, toZorn]
  apply ZornMatrix.ext
  · simp [E11, E22, V, mul, smul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]
  · funext k; fin_cases i <;> fin_cases k <;>
      simp [E11, E22, V, mul, smul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis]
  · funext k; fin_cases i <;> fin_cases k <;>
      simp [E11, E22, V, mul, smul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis]
  · simp [E11, E22, V, mul, smul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

end InfoGeometry.Algebra.CircularChiralCausalConeBasis
