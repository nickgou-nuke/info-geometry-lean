import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cauchy--Schwarz for the finite noncommutative BKM response

The finite Kubo--Mori owner supplies a symmetric real bilinear form, while
positivity is intentionally still a model theorem rather than an owner
field.  This file proves the exact algebraic consequence needed downstream:
once diagonal positivity is supplied, the real BKM pairing satisfies the
Cauchy--Schwarz inequality.

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

end SouriauOnsagerBKM
