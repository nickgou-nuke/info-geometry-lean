/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm
import InfoGeometry.Canonical.SouriauOnsagerBKMStrictPositivity
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cauchy--Schwarz for the finite noncommutative BKM response

The finite Kubo--Mori owner supplies a symmetric real bilinear form.  The
positivity owner supplies its nonnegative and strict diagonal readouts.  This
file proves the exact algebraic consequence needed downstream: the real BKM
pairing satisfies the Cauchy--Schwarz inequality under the native continuity
hypothesis on the functional-calculus power.

No new metric or Cramér--Rao statement is introduced.
-/

noncomputable section

namespace SouriauOnsagerBKM

variable {n : ℕ}

theorem FaithfulDensityOperator.kuboMoriPairing_real_cauchySchwarz
    (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow)
    (hpos : ∀ A : FiniteOperatorAlgebra n,
      0 ≤ (D.kuboMoriPairing A A).re)
    (hstrict : ∀ A : FiniteOperatorAlgebra n, A ≠ 0 →
      0 < (D.kuboMoriPairing A A).re)
    (A B : FiniteOperatorAlgebra n) :
    (D.kuboMoriPairing A B).re ^ 2 ≤
      (D.kuboMoriPairing A A).re *
        (D.kuboMoriPairing B B).re := by
  let G := D.bkmRealBilinForm hpow
  have hsym : ∀ X Y, G X Y = G Y X :=
    (D.bkmRealBilinForm_symm hpow).eq
  have hGpos : ∀ X, 0 ≤ G X X := by
    intro X
    exact hpos X
  have hAB : G A B = (D.kuboMoriPairing A B).re := rfl
  have hAA : G A A = (D.kuboMoriPairing A A).re := rfl
  have hBB : G B B = (D.kuboMoriPairing B B).re := rfl
  by_cases hBzero : B = 0
  · subst B
    change (G A 0) ^ 2 ≤ G A A * G 0 0
    simp
  · have hBpos : 0 < G B B := hstrict B hBzero
    have hquad :
        0 ≤ G (A - (G A B / G B B) • B)
          (A - (G A B / G B B) • B) :=
      hGpos _
    have hquad' := hquad
    simp [sub_eq_add_neg, map_add, map_neg, map_smul, hsym] at hquad'
    have hdet : 0 ≤ G A A * G B B - (G A B) ^ 2 := by
      field_simp [ne_of_gt hBpos] at hquad'
      nlinarith
    change (G A B) ^ 2 ≤ G A A * G B B
    linarith

/-! The finite positivity owners discharge the diagonal hypotheses for the
    native BKM pairing, so downstream users need only continuity of the
    functional-calculus power. -/

theorem FaithfulDensityOperator.kuboMoriPairing_real_cauchySchwarz_of_continuous_rpow
    (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) :
    (D.kuboMoriPairing A B).re ^ 2 ≤
      (D.kuboMoriPairing A A).re *
        (D.kuboMoriPairing B B).re := by
  apply D.kuboMoriPairing_real_cauchySchwarz hpow
  · intro X
    exact D.kuboMoriPairing_self_re_nonneg X hpow
  · intro X hX
    exact D.kuboMoriPairing_self_pos X hpow hX

end SouriauOnsagerBKM
