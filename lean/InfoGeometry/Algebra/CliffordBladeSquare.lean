/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.CliffordGA
import Mathlib.Data.Nat.Choose.Basic

/-!
# Square of an ordered orthogonal Clifford blade

Source: R. Abramowicz, Z. Oziewicz, J. Rzewuski, *Clifford algebra approach to
twistors*, J. Math. Phys. 23 (1982) 231, §III Eq. (3.1) and the blade-square
property (Hestenes–Ziegler Eq. (2.7)).

For a list of pairwise-orthogonal vectors, the square of their ordered Clifford
product is the scalar `(-1)^(k(k-1)/2) ∏ Q(v_i)`.  This generalizes the
two-vector owner lemma
`InfoGeometry.Algebra.CliffordGA.clifford_product_sq_eq_neg_quadratic_product_of_orthogonal`
to arbitrary blade length.  The sign exponent is written as `Nat.choose k 2`,
which equals `k(k-1)/2` (`Nat.choose_two_right`).  Specializing to an orthogonal
basis gives the pseudoscalar-square formula (3.1) with `det Q = ∏ Q(e_i)`.

No metric signature, twistor ideal, or Witt decomposition is assumed; the result
is a statement about the associative Clifford product and the quadratic form.
-/

noncomputable section

namespace InfoGeometry.Algebra.CliffordBladeSquare

open CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)

/-- The ordered Clifford product of a list of vectors. -/
def bladeProd (v : List M) : CliffordAlgebra Q :=
  (v.map (ι Q)).prod

@[simp] theorem bladeProd_nil : bladeProd Q [] = 1 := rfl

theorem bladeProd_cons (a : M) (v : List M) :
    bladeProd Q (a :: v) = ι Q a * bladeProd Q v := rfl

/-- Moving a vector orthogonal to every entry of a list past the ordered blade
costs the sign `(-1)^(length)`. -/
theorem bladeProd_mul_ι (a : M) (v : List M)
    (h : ∀ b ∈ v, QuadraticMap.polar Q a b = 0) :
    bladeProd Q v * ι Q a =
      (-1 : CliffordAlgebra Q) ^ v.length * (ι Q a * bladeProd Q v) := by
  induction v with
  | nil => simp [bladeProd]
  | cons b v ih =>
    have hb : QuadraticMap.polar Q a b = 0 := h b (List.mem_cons.mpr (Or.inl rfl))
    have hv : ∀ c ∈ v, QuadraticMap.polar Q a c = 0 :=
      fun c hc => h c (List.mem_cons.mpr (Or.inr hc))
    have hanti : ι Q b * ι Q a = -(ι Q a * ι Q b) :=
      InfoGeometry.Algebra.CliffordGA.clifford_orthogonal_vectors_anticommute Q a b hb
    simp only [bladeProd_cons, List.length_cons, pow_succ]
    rw [mul_assoc, ih hv]
    have hp : (-1 : CliffordAlgebra Q) ^ v.length =
        algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) := by
      rw [map_pow, map_neg, map_one]
    rw [hp]
    have hL : ι Q b * (algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
        (ι Q a * bladeProd Q v))
        = algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
          (ι Q b * (ι Q a * bladeProd Q v)) := by
      rw [← mul_assoc, ← Algebra.commutes, mul_assoc]
    rw [hL, mul_assoc]
    calc
      algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
          (ι Q b * (ι Q a * bladeProd Q v))
          = algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
              ((ι Q b * ι Q a) * bladeProd Q v) := by rw [mul_assoc]
      _ = algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
              (-(ι Q a * ι Q b) * bladeProd Q v) := by rw [hanti]
      _ = -(algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
              (ι Q a * (ι Q b * bladeProd Q v))) := by
        rw [neg_mul, mul_neg, mul_assoc]
      _ = algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
            (-1 * (ι Q a * (ι Q b * bladeProd Q v))) := by
        rw [neg_one_mul]
        exact (mul_neg
          (algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length))
          (ι Q a * (ι Q b * bladeProd Q v))).symm

/-- **Blade-square sign formula.**  The square of the ordered Clifford product of
a pairwise-orthogonal list of vectors is the scalar
`(-1)^(choose k 2) ∏ Q(v_i)`, where `k` is the list length. -/
theorem bladeProd_sq (v : List M)
    (h : v.Pairwise (fun a b => QuadraticMap.polar Q a b = 0)) :
    bladeProd Q v ^ 2 =
      algebraMap R (CliffordAlgebra Q)
        ((-1 : R) ^ Nat.choose v.length 2 * (v.map Q).prod) := by
  induction v with
  | nil => simp [bladeProd]
  | cons a v ih =>
    have hhead : ∀ b ∈ v, QuadraticMap.polar Q a b = 0 := (List.pairwise_cons.mp h).1
    have htail : v.Pairwise (fun a b => QuadraticMap.polar Q a b = 0) :=
      (List.pairwise_cons.mp h).2
    simp only [bladeProd_cons, pow_two]
    have h1 : (ι Q a * bladeProd Q v) * (ι Q a * bladeProd Q v)
        = ι Q a * (bladeProd Q v * ι Q a) * bladeProd Q v := by
      noncomm_ring
    rw [h1, bladeProd_mul_ι Q a v hhead]
    have hrearr :
        ι Q a * ((-1 : CliffordAlgebra Q) ^ v.length * (ι Q a * bladeProd Q v)) *
            bladeProd Q v
          = (-1 : CliffordAlgebra Q) ^ v.length *
              (ι Q a * ι Q a) * (bladeProd Q v * bladeProd Q v) := by
      have hp : (-1 : CliffordAlgebra Q) ^ v.length =
          algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) := by
        rw [map_pow, map_neg, map_one]
      rw [hp]
      have hL : ι Q a * (algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
          (ι Q a * bladeProd Q v))
          = algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
            (ι Q a * (ι Q a * bladeProd Q v)) := by
        calc
          ι Q a * (algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
              (ι Q a * bladeProd Q v))
              = (ι Q a * algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length)) *
                  (ι Q a * bladeProd Q v) := by rw [mul_assoc]
          _ = (algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) * ι Q a) *
                (ι Q a * bladeProd Q v) := by rw [Algebra.commutes]
          _ = algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) *
                (ι Q a * (ι Q a * bladeProd Q v)) := by rw [mul_assoc]
      rw [hL]
      noncomm_ring
    rw [hrearr, InfoGeometry.Algebra.CliffordGA.clifford_square_eq_quadratic_form,
      ← pow_two (bladeProd Q v), ih htail]
    -- combine the central scalars
    have hneg : (-1 : CliffordAlgebra Q) ^ v.length =
        algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ v.length) := by
      rw [map_pow, map_neg, map_one]
    rw [hneg, ← map_mul, ← map_mul]
    congr 1
    simp only [List.length_cons, List.map_cons, List.prod_cons,
      Nat.choose_succ_succ, Nat.choose_one_right]
    rw [pow_add]
    ac_rfl

end InfoGeometry.Algebra.CliffordBladeSquare
