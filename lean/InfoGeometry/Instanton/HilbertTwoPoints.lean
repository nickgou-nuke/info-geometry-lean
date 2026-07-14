import Mathlib
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Algebra.Polynomial.Bivariate

open Polynomial
open scoped Polynomial.Bivariate

namespace HilbertTwoPoints

noncomputable section

/-- The coordinate ring of the two-point subscheme defined by `x(x - 1)` and `y`. -/
abbrev R := MvPolynomial (Fin 2) ℚ

/-- The ideal `I = (x(x - 1), y)` in `ℚ[x, y]`. -/
def I : Ideal R :=
  Ideal.span {MvPolynomial.X 0 * (MvPolynomial.X 0 - 1), MvPolynomial.X 1}

/-- The corresponding ideal in the bivariate polynomial presentation. -/
def J : Ideal ℚ[X][Y] :=
  Ideal.span {C (Polynomial.X * (Polynomial.X - C (1 : ℚ))), X - C (0 : ℚ[X])}

/-- The quotient coordinate ring is two-dimensional over `ℚ`. -/
theorem dim_quotient_two : Module.finrank ℚ (R ⧸ I) = 2 := by
  have hI : I = J.map (Polynomial.Bivariate.equivMvPolynomial ℚ) := by
    ext p
    simp [I, J, Ideal.map_span, Set.image_pair,
      Polynomial.Bivariate.equivMvPolynomial_C_X,
      Polynomial.Bivariate.equivMvPolynomial_X]

  have hdeg : (Polynomial.X * (Polynomial.X - C (1 : ℚ))).natDegree = 2 := by
    rw [Polynomial.Monic.natDegree_mul Polynomial.monic_X (Polynomial.monic_X_sub_C (1 : ℚ))]
    rw [Polynomial.natDegree_X_sub_C]
    norm_num

  have hq : Module.finrank ℚ (ℚ[X] ⧸ Ideal.span ({Polynomial.X * (Polynomial.X - C (1 : ℚ))} : Set ℚ[X])) = 2 := by
    have hq0 := (_root_.finrank_quotient_span_eq_natDegree (K := ℚ)
      (f := Polynomial.X * (Polynomial.X - C (1 : ℚ))))
    rw [hdeg] at hq0
    exact hq0

  have hbiv : Module.finrank ℚ (ℚ[X][Y] ⧸ J) = 2 := by
    have e := (Polynomial.quotientSpanCXSubCAlgEquiv
      (R := ℚ[X]) (x := Polynomial.X * (Polynomial.X - C (1 : ℚ))) (y := (0 : ℚ[X]))).restrictScalars ℚ
    have hfin := e.toLinearEquiv.finrank_eq
    simpa [J] using hfin.trans hq

  have hmv : Module.finrank ℚ (R ⧸ I) = Module.finrank ℚ (ℚ[X][Y] ⧸ J) := by
    simpa [I, J, hI] using
      ((Ideal.quotientEquivAlg J I (Polynomial.Bivariate.equivMvPolynomial ℚ) hI).toLinearEquiv.finrank_eq).symm

  calc
    Module.finrank ℚ (R ⧸ I) = Module.finrank ℚ (ℚ[X][Y] ⧸ J) := hmv
    _ = 2 := hbiv

end
