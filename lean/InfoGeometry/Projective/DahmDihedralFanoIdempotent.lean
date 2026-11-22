/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.DahmHexasphericalHodgeSymplectic

/-!
# Dahm (J. Phys. Conf. Ser. 3152 (2025) 012008) over an operator ring

All statements are over an arbitrary, in general noncommutative, ring of operators.

* **`D₄` generators (Sec. 2.4)** as `2 × 2` matrices over an operator ring `B`:
  `r₁ = !![0,-1;1,0]`, `s₀ = !![1,0;0,-1]`, `s₁ = !![0,1;1,0]` satisfy `r₁² = -1`,
  `s₀² = s₁² = 1`, `s₀ s₁ = -r₁`, `s₁ s₀ = r₁`, and in the cut frame
  `s₀ = 2P - 1`, `s₁ = N₊ + N₋`, `r₁ = -(N₊ - N₋)`.  `s₀ s₁ ≠ s₁ s₀` whenever
  `2 ≠ 0` in `B`.
* **One Fano line generates the spinor idempotents (Sec. 3, p. 7).**  In any ring,
  for commuting involutions `a, b`, the elements `(1 ± a)(1 ± b)` are `4×`
  idempotents, mutually orthogonal, summing to `4`, and `a + b` is tripotent up to
  `4`.
* **Clifford-module realization.**  In any ring containing pairwise anticommuting
  `e₁, e₂, e₃` with `e₁² = e₂² = 1`, `e₃² = -1` (a `Cl(2,1)`-module), the pair
  `a = e₁e₃`, `b = e₂` is a commuting pair of involutions, so Lounesto's
  `4f = (1 + a)(1 + b)` and the whole idempotent tower live in the operator ring.

## Scope

Dahm's determinant action of `D₄` on `2 × 2` minors is a statement about commuting
coordinates and is not asserted here.  Not proved: Veblen–Young, octonion claims
(`PG(2,2)` is itself Desarguesian), wave–particle and photon-gate readings.
-/

namespace InfoGeometry.Projective.DahmDihedralFanoIdempotent

open Matrix

/-! ### `D₄` over an operator ring -/

section Dihedral

variable {B : Type*} [Ring B]

def r1 : Matrix (Fin 2) (Fin 2) B := !![0, -1; 1, 0]
def s0 : Matrix (Fin 2) (Fin 2) B := !![1, 0; 0, -1]
def s1 : Matrix (Fin 2) (Fin 2) B := !![0, 1; 1, 0]
def cutP : Matrix (Fin 2) (Fin 2) B := !![1, 0; 0, 0]
def nPlus : Matrix (Fin 2) (Fin 2) B := !![0, 1; 0, 0]
def nMinus : Matrix (Fin 2) (Fin 2) B := !![0, 0; 1, 0]

/-- The `D₄` relations of Dahm Sec. 2.4 over an operator ring. -/
theorem dihedral_relations :
    (r1 : Matrix (Fin 2) (Fin 2) B) * r1 = -1 ∧ (s0 : Matrix (Fin 2) (Fin 2) B) * s0 = 1 ∧
      (s1 : Matrix (Fin 2) (Fin 2) B) * s1 = 1 ∧ (s0 : Matrix (Fin 2) (Fin 2) B) * s1 = -r1 ∧
      (s1 : Matrix (Fin 2) (Fin 2) B) * s0 = r1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp [r1, s0, s1, Matrix.mul_apply, Fin.sum_univ_two])

/-- The generators in the cut frame: `s₀ = 2P - 1`, `s₁ = N₊ + N₋`, `r₁ = -(N₊ - N₋)`. -/
theorem dihedral_cut_frame :
    (s0 : Matrix (Fin 2) (Fin 2) B) = (2 : B) • cutP - 1 ∧
      (s1 : Matrix (Fin 2) (Fin 2) B) = nPlus + nMinus ∧
      (r1 : Matrix (Fin 2) (Fin 2) B) = -(nPlus - nMinus) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [r1, s0, s1, cutP, nPlus, nMinus, Matrix.mul_apply, Fin.sum_univ_two]) <;> norm_num

/-- `s₀ s₁ ≠ s₁ s₀` in any operator ring where `2 ≠ 0`. -/
theorem s0_s1_ne (h2 : (2 : B) ≠ 0) : (s0 : Matrix (Fin 2) (Fin 2) B) * s1 ≠ s1 * s0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [s0, s1, Matrix.mul_apply, Fin.sum_univ_two] at h01
  apply h2
  rw [← one_add_one_eq_two]
  rw [eq_neg_iff_add_eq_zero] at h01
  exact h01

/-- Noncommutativity witness in any characteristic-zero operator ring. -/
theorem s0_s1_ne_charZero {B : Type*} [Ring B] [CharZero B] :
    (s0 : Matrix (Fin 2) (Fin 2) B) * s1 ≠ s1 * s0 :=
  s0_s1_ne two_ne_zero

end Dihedral

/-! ### One Fano line `{a, b, ab}` and the four spinor idempotents -/

section FanoLine

variable {B : Type*} [Ring B] {a b : B}

/-- For commuting involutions `a, b` in an operator ring: the four `(1 ± a)(1 ± b)`
idempotents (scaled by `4`), their orthogonality and partition of unity, and the
tripotent law of `h = a + b`. -/
theorem fano_line_idempotents (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (a * b) * (a * b) = 1 ∧
    (1 + a) * (1 + b) * ((1 + a) * (1 + b)) = 4 * ((1 + a) * (1 + b)) ∧
    (1 - a) * (1 - b) * ((1 - a) * (1 - b)) = 4 * ((1 - a) * (1 - b)) ∧
    (2 * (1 - a * b)) * (2 * (1 - a * b)) = 4 * (2 * (1 - a * b)) ∧
    (1 + a) * (1 + b) * ((1 - a) * (1 - b)) = 0 ∧
    (1 + a) * (1 + b) * (2 * (1 - a * b)) = 0 ∧
    (1 + a) * (1 + b) + 2 * (1 - a * b) + (1 - a) * (1 - b) = 4 ∧
    (1 + a) * (1 + b) - (1 - a) * (1 - b) = 2 * (a + b) ∧
    (a + b) * (a + b) = 2 * (1 + a * b) ∧
    (a + b) * ((a + b) * (a + b)) = 4 * (a + b) := by
  have aa : ∀ z : B, a * (a * z) = z := fun z => by rw [← mul_assoc, ha, one_mul]
  have ba : b * a = a * b := hab.symm
  have ba' : ∀ z : B, b * (a * z) = a * (b * z) := fun z => by rw [← mul_assoc, ba, mul_assoc]
  have a2 : ∀ z : B, a * (2 * z) = 2 * (a * z) := fun z => by
    rw [← mul_assoc, ← mul_assoc, (Commute.ofNat_left 2 a).eq]
  have b2 : ∀ z : B, b * (2 * z) = 2 * (b * z) := fun z => by
    rw [← mul_assoc, ← mul_assoc, (Commute.ofNat_left 2 b).eq]
  -- Normalize every word to `aⁱ bʲ` (right-associated), then compare in the free ring.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc,
      ha, hb, aa, ba, ba', a2, b2] <;>
    noncomm_ring
  all_goals
    simp only [zsmul_eq_mul, mul_one, Int.cast_ofNat, Int.cast_neg, neg_mul]
    abel_nf
  all_goals norm_num

end FanoLine

/-! ### Clifford-module realization of the Fano line -/

section CliffordModule

variable {B : Type*} [Ring B] {e₁ e₂ e₃ : B}

/-- In a `Cl(2,1)`-module over any operator ring (`e₁² = e₂² = 1`, `e₃² = -1`, pairwise
anticommuting), `a = e₁e₃` and `b = e₂` are commuting involutions. -/
theorem clifford_fano_pair (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1) (h₃ : e₃ * e₃ = -1)
    (h₁₂ : e₁ * e₂ = -(e₂ * e₁)) (h₁₃ : e₁ * e₃ = -(e₃ * e₁)) (h₂₃ : e₂ * e₃ = -(e₃ * e₂)) :
    (e₁ * e₃) * (e₁ * e₃) = 1 ∧ e₂ * e₂ = 1 ∧ (e₁ * e₃) * e₂ = e₂ * (e₁ * e₃) := by
  refine ⟨?_, h₂, ?_⟩
  · calc (e₁ * e₃) * (e₁ * e₃) = e₁ * (e₃ * e₁) * e₃ := by noncomm_ring
      _ = e₁ * (-(e₁ * e₃)) * e₃ := by rw [h₁₃, neg_neg]
      _ = -((e₁ * e₁) * (e₃ * e₃)) := by noncomm_ring
      _ = 1 := by rw [h₁, h₃]; noncomm_ring
  · calc (e₁ * e₃) * e₂ = e₁ * (e₃ * e₂) := by noncomm_ring
      _ = e₁ * (-(e₂ * e₃)) := by rw [h₂₃, neg_neg]
      _ = -((e₁ * e₂) * e₃) := by noncomm_ring
      _ = (e₂ * e₁) * e₃ := by rw [h₁₂]; noncomm_ring
      _ = e₂ * (e₁ * e₃) := by noncomm_ring

/-- Lounesto's primitive idempotent in the Clifford module: `4f = (1 + e₁e₃)(1 + e₂)` satisfies
`(4f)² = 4 · 4f`, and the opposite-sign idempotent is orthogonal to it. -/
theorem clifford_lounesto_idempotent (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1) (h₃ : e₃ * e₃ = -1)
    (h₁₂ : e₁ * e₂ = -(e₂ * e₁)) (h₁₃ : e₁ * e₃ = -(e₃ * e₁)) (h₂₃ : e₂ * e₃ = -(e₃ * e₂)) :
    (1 + e₁ * e₃) * (1 + e₂) * ((1 + e₁ * e₃) * (1 + e₂)) = 4 * ((1 + e₁ * e₃) * (1 + e₂)) ∧
      (1 + e₁ * e₃) * (1 + e₂) * ((1 - e₁ * e₃) * (1 - e₂)) = 0 := by
  obtain ⟨ha, hb, hab⟩ := clifford_fano_pair h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
  obtain ⟨-, h4, -, -, h0, -⟩ := fano_line_idempotents ha hb hab
  exact ⟨h4, h0⟩

end CliffordModule

end InfoGeometry.Projective.DahmDihedralFanoIdempotent
