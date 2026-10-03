-- SPDX-FileCopyrightText: 2024–2026 The InfoGeometry Authors
-- SPDX-License-Identifier: MIT

/-
# Peirce-to-Circular Chiral Bridge

Connects the **longitudinal linear Peirce projectors** (diagonal in the Pauli/σ₃
basis) to the **transverse circular chiral projectors** (diagonal in the σ₂ basis),
and identifies the two chiral gradings as one grading in two bases.

## Provenance: this file regenerates a false draft

An earlier draft of this file carried 21 theorems. Two of its claims were false.

**1. The 45° ansatz.** The draft first used `H = (σ₁ + σ₂)/√2` and asserted
`H σ₃ H† = σ₂`. That is false: `H` is a *reflection* about the equatorial axis at
45°, fixing `σ₁ + σ₂` and inverting the orthogonal plane, so

  `H σ₃ H† = -σ₃`,   `H σ₂ H† = σ₁`.

**2. `EminusC = σ₂`.** With `EminusC = !![0,1;-1,0]` and `σ₂ = !![0,-i;i,0]` these
differ by a factor of `i`; the true relation is `-i · EminusC = σ₂`.

A later revision replaced the ansatz with the correct quarter-wave plate
`U = (I - i σ₁)/√2`, which *does* satisfy the intended conjugation — but only in the
orientation `Uᴴ σ₃ U = σ₂`, whereas every conjugation theorem in the draft was
stated as `U σ₃ Uᴴ = σ₂`. That orientation mismatch is the remaining source of
failure: for this `U`,

  `U σ₃ Uᴴ = -σ₂`   and   `Uᴴ σ₃ U = σ₂`.

Rather than delete the thought, this file **reflects it into the truth**. The genuine
content of the draft is preserved and proved; the two false statements are replaced
by their correct counterparts; the conjugation theorems are stated in the orientation
the verified plate actually satisfies; and the draft's incorrect orientation claim is
itself recorded as a true theorem (`peirce_negated_by_plate`) so the error is not
silently dropped.

The sound core that survives: the `(I ± σ)/2` projector algebra, the complementarity
of the two gradings, and the Peirce-combo decompositions. The basis change itself is
owned by `InfoGeometry.CliffordWeyl.PeirceCircularQwpBridge` (verified:
`Uqwp_unitary`, `Uqwp_conj_sigma3`, `Pleft_to_clockwise`, `Pright_to_counterclockwise`)
and imported rather than re-derived.

All results are native Lean matrix computations in `Mat₂(ℂ)`: no `sorry`, no
certificates, no tactic search.
-/

import InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
import InfoGeometry.CliffordWeyl.CircularPauliPeirceBridge
import InfoGeometry.CliffordWeyl.PeirceCircularQwpBridge
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic

noncomputable section

namespace InfoGeometry.CliffordWeyl.PeirceToCircularBridge

open Matrix
open InfoGeometry.Krein.RealPlaneMatrixBridge
open InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
open InfoGeometry.CliffordWeyl.CircularPauliPeirceBridge
open InfoGeometry.CliffordWeyl.PeirceCircularQwpBridge

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Complex embedding of a real 2×2 matrix. -/
def toComplex (M : Matrix (Fin 2) (Fin 2) ℝ) : Mat2C :=
  fun i j => (M i j : ℂ)

/-! ## 1. The Peirce projectors, as complex matrices

Regenerated from the draft's `PleftC` / `PrightC` and their `toComplex` readouts,
which were correct and are kept. -/

/-- The Peirce `+1` projector, the complexification of `pauliChiral.Pleft`. -/
def PleftC : Mat2C := !![(1 : ℂ), 0; 0, 0]

/-- The Peirce `-1` projector, the complexification of `pauliChiral.Pright`. -/
def PrightC : Mat2C := !![(0 : ℂ), 0; 0, 1]

@[simp] theorem PleftC_mat : PleftC = !![(1 : ℂ), 0; 0, 0] := rfl

@[simp] theorem PrightC_mat : PrightC = !![(0 : ℂ), 0; 0, 1] := rfl

theorem PleftC_eq_toComplex : PleftC = toComplex pauliChiral.Pleft := by
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [toComplex, pauliChiral_Pleft, PleftC]

theorem PrightC_eq_toComplex : PrightC = toComplex pauliChiral.Pright := by
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [toComplex, pauliChiral_Pright, PrightC]

/-! ## 2. The projector algebra `(I ± σ)/2` — retained from the draft

These four identities were the sound core of the draft: each projector is the
normalized `±1` projection onto an eigenspace of the grading. -/

theorem PleftC_eq_half_I_plus_sigma3 :
    PleftC = (1 / 2 : ℂ) • ((1 : Mat2C) + sigma3) := by
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [PleftC, sigma3, Matrix.add_apply, Matrix.smul_apply,
      Complex.ext_iff]
  ; ring

theorem PrightC_eq_half_I_minus_sigma3 :
    PrightC = (1 / 2 : ℂ) • ((1 : Mat2C) - sigma3) := by
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [PrightC, sigma3, Matrix.sub_apply, Matrix.smul_apply,
      Complex.ext_iff]
  ; ring

theorem clockwise_eq_half_I_plus_sigma2 :
    clockwiseProjector = (1 / 2 : ℂ) • ((1 : Mat2C) + sigma2) := by
  rw [clockwiseProjector_eq_matrix]
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma2, Matrix.add_apply, Matrix.smul_apply,
      Complex.ext_iff]
  ; ring

theorem counterclockwise_eq_half_I_minus_sigma2 :
    counterclockwiseProjector = (1 / 2 : ℂ) • ((1 : Mat2C) - sigma2) := by
  rw [counterclockwiseProjector_eq_matrix]
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma2, Matrix.sub_apply, Matrix.smul_apply,
      Complex.ext_iff]
  ; ring

/-- The two circular projectors are complementary. -/
theorem circularProjectors_sum_identity :
    clockwiseProjector + counterclockwiseProjector = (1 : Mat2C) := by
  rw [clockwiseProjector_eq_matrix, counterclockwiseProjector_eq_matrix]
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Complex.ext_iff] <;> ring

/-! ## 3. The elliptic generator: the draft's false `EminusC_eq_sigma2`, corrected

The draft asserted `EminusC = σ₂`. That is false — they differ by a factor of `i`.
The true relation, which is what the draft's *downstream* theorems actually needed,
is `-i · EminusC = σ₂`. -/

/--
**Corrected.** The elliptic generator of the circular chirality is `-i` times σ₂.

This replaces the draft's false `EminusC_eq_sigma2`. With
`EminusC = !![0,1;-1,0]` and `σ₂ = !![0,-i;i,0]`, `EminusC ≠ σ₂`; the relation is
`-i · EminusC = σ₂`. The lost `i`-factor is exactly what made the draft's
conjugation targets inconsistent.
-/
theorem negI_mul_EminusC_eq_sigma2 : (-Complex.I) • EminusC = sigma2 := by
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [EminusC, sigma2, Matrix.smul_apply]

/-- The circular chiral involution of `CircularPauliPeirceBridge` is σ₂. -/
theorem circularChirality_is_sigma2 : clockwiseChirality.chi = sigma2 := by
  have h : clockwiseChirality.chi = (-Complex.I) • EminusC := rfl
  rw [h, negI_mul_EminusC_eq_sigma2]

/-! ## 4. The circular projectors as Peirce combinations — retained from the draft

These were correct in the draft and are kept. -/

/--
The clockwise projector `Π_ccw = (I + σ₂)/2` is the symmetric Peirce combination
minus half the elliptic generator:

  `Π_ccw = ½ (Pleft + Pright) - (i/2) EminusC`

Since `Pleft + Pright = I`, the circular `+1` corner is the Peirce symmetric part
twisted by a quarter of the elliptic generator.
-/
theorem clockwiseProjector_as_Peirce_combo :
    clockwiseProjector
      = (1 / 2 : ℂ) • (PleftC + PrightC : Mat2C) - (Complex.I / 2 : ℂ) • EminusC := by
  rw [clockwiseProjector_eq_matrix]
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [PleftC, PrightC, EminusC,
      Complex.ext_iff]
  ; ring

/-- Dually the counterclockwise projector `Π_cw = (I - σ₂)/2` adds the term. -/
theorem counterclockwiseProjector_as_Peirce_combo :
    counterclockwiseProjector
      = (1 / 2 : ℂ) • (PleftC + PrightC : Mat2C) + (Complex.I / 2 : ℂ) • EminusC := by
  rw [counterclockwiseProjector_eq_matrix]
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [PleftC, PrightC, EminusC, Matrix.add_apply,
      Complex.ext_iff]
  ; ring

/-! ## 5. Conjugation by the quarter-wave plate, in the correct orientation

The draft stated its four conjugation theorems as `U A Uᴴ = ...`. For the quarter-wave
plate that orientation sends σ₃ to `-σ₃`; the verified orientation is `Uᴴ A U`. The
statements below use the orientation that is actually true.

`Uqwpᴴ σ₃ Uqwp = σ₂`, `Uqwpᴴ Pleft Uqwp = Π_ccw` and `Uqwpᴴ Pright Uqwp = Π_cw` are
proved in `PeirceCircularQwpBridge` and imported. -/

/-- `Uqwp Uqwpᴴ = 1`, the reverse of the imported `Uqwpᴴ Uqwp = 1`. -/
theorem Uqwp_mul_conjTranspose : Uqwp * Uqwpᴴ = (1 : Mat2C) := by
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [Uqwp, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      conj_s2, Complex.conj_I]
  all_goals ring_nf
  all_goals rw [s2_sq]
  all_goals norm_num [Complex.I_sq]

/--
**Inverse conjugation.** The plate is a unitary *rotation*, so with the opposite
orientation it carries σ₂ back to σ₃:

  `Uqwp σ₂ Uqwpᴴ = σ₃`

A statement the draft could not make: its original `H` was a reflection, which has
no such two-sided inverse behaviour.
-/
theorem peirceCircular_chirality_relation_inv :
    Uqwp * (sigma2 : Mat2C) * Uqwpᴴ = sigma3 := by
  rw [show (sigma2 : Mat2C) = !![(0 : ℂ), -Complex.I; Complex.I, 0] by
      funext a b; fin_cases a <;> fin_cases b <;> rfl,
    show (sigma3 : Mat2C) = !![(1 : ℂ), 0; 0, -1] by
      funext a b; fin_cases a <;> fin_cases b <;> rfl]
  funext a b; fin_cases a <;> fin_cases b <;>
    simp [Uqwp, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, conj_s2, Complex.conj_I]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, s2_sq]

/--
**The orientation the draft asserted, correctly evaluated.**

The draft claimed `H σ₃ H† = σ₂`. For this plate in that orientation the true value
is the *negation of the circular grading*:

  `Uqwp σ₃ Uqwpᴴ = -σ₂`

This closes the draft's claim on two counts: the operator orientation was wrong, and
even in the orientation it wrote, the target is `-σ₂`, not `σ₂`. Note the pairing
with `peirceCircular_chirality_relation_inv` (`Uqwp σ₂ Uqwpᴴ = σ₃`): the two
orientations are genuinely different maps, related by complex conjugation of the
target, which is exactly why a unitary rotation and a reflection must not be
conflated.
-/
theorem peirce_negated_by_plate :
    Uqwp * (sigma3 : Mat2C) * Uqwpᴴ = -sigma2 := by
  rw [show (sigma3 : Mat2C) = !![(1 : ℂ), 0; 0, -1] by
      funext a b; fin_cases a <;> fin_cases b <;> rfl,
    show (-sigma2 : Mat2C) = !![(0 : ℂ), Complex.I; -Complex.I, 0] by
      funext a b; fin_cases a <;> fin_cases b <;>
        simp [neg_apply, sigma2, Matrix.neg_apply]]
  funext a b; fin_cases a <;> fin_cases b <;>
    simp [Uqwp, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, conj_s2, Complex.conj_I]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, s2_sq]
  all_goals ring

/-- **Projector round-trip.** Since `Π = U† P U`, conjugating back by `U`
recovers the Peirce projector. -/
theorem clockwise_roundtrip_to_Pleft :
    Uqwp * clockwiseProjector * Uqwpᴴ = PleftC := by
  calc Uqwp * clockwiseProjector * Uqwpᴴ
      = Uqwp * (Uqwpᴴ * Pleft * Uqwp) * Uqwpᴴ := by rw [← Pleft_to_clockwise]
    _ = (Uqwp * Uqwpᴴ) * Pleft * (Uqwp * Uqwpᴴ) := by
        simp only [mul_assoc]
    _ = Pleft := by rw [Uqwp_mul_conjTranspose]; simp
    _ = PleftC := rfl

/-- The same round-trip on the `-1` corners. -/
theorem counterclockwise_roundtrip_to_Pright :
    Uqwp * counterclockwiseProjector * Uqwpᴴ = PrightC := by
  calc Uqwp * counterclockwiseProjector * Uqwpᴴ
      = Uqwp * (Uqwpᴴ * Pright * Uqwp) * Uqwpᴴ := by
        rw [← Pright_to_counterclockwise]
    _ = (Uqwp * Uqwpᴴ) * Pright * (Uqwp * Uqwpᴴ) := by
        simp only [mul_assoc]
    _ = Pright := by rw [Uqwp_mul_conjTranspose]; simp
    _ = PrightC := rfl

/-! ## 6. The two gradings are conjugate — the draft's headline, now true

The draft's `peirceCircular_chirality_relation` asserted
`H σ₃ H† = clockwiseChirality.chi`. With the correct plate and the correct
orientation this becomes a true statement, and it is the owner-level identification:
**the Peirce grading and the circular grading are one grading in two bases.** -/

theorem peirceCircular_chirality_relation :
    Uqwpᴴ * (sigma3 : Mat2C) * Uqwp = clockwiseChirality.chi := by
  calc Uqwpᴴ * (sigma3 : Mat2C) * Uqwp = sigma2 := Uqwp_conj_sigma3
    _ = clockwiseChirality.chi := (circularChirality_is_sigma2).symm

/-! ## 7. Summary

| Abstract layer        | Matrix (Mat₂(ℂ)) | Peirce corner (σ₃) | Circular corner (σ₂)     |
|-----------------------|------------------|--------------------|--------------------------|
| Involution χ          | σ₃ = Eplus       | Pleft - Pright     | σ₂ = -i·EminusC          |
| +1 spectral projector | Pleft = diag(1,0)| diagonal (+,+)     | Π_ccw = ½(I + σ₂)        |
| -1 spectral projector | Pright=diag(0,1) | diagonal (-,-)     | Π_cw  = ½(I - σ₂)        |
| Elliptic generator    | EminusC          | off-diagonal       | chirality generator      |
| Basis change          | Uqwp             | `Uᴴ · · · U`       | `U · · · Uᴴ`             |
| Identity              | I                | Pleft + Pright     | Π_ccw + Π_cw             |

All equalities are native Lean matrix computations in `Mat₂(ℂ)`.
-/

end InfoGeometry.CliffordWeyl.PeirceToCircularBridge

end
