import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornCore

noncomputable section

namespace ZornCore

def cartanAction (t : Vec3) (X : Zorn) : Zorn :=
  { a := X.a
    u := fun i => Real.exp (t i) * X.u i
    v := fun i => Real.exp (-t i) * X.v i
    b := X.b }

theorem cartanAction_a (t : Vec3) (X : Zorn) :
    (cartanAction t X).a = X.a := rfl

theorem cartanAction_b (t : Vec3) (X : Zorn) :
    (cartanAction t X).b = X.b := rfl

theorem cartanAction_u (t : Vec3) (X : Zorn) (i : Fin 3) :
    (cartanAction t X).u i = Real.exp (t i) * X.u i := rfl

theorem cartanAction_v (t : Vec3) (X : Zorn) (i : Fin 3) :
    (cartanAction t X).v i = Real.exp (-t i) * X.v i := rfl

theorem cartanAction_mul
    (t : Vec3) (ht : ∑ i, t i = 0) (X Y : Zorn) :
    cartanAction t (X * Y) = cartanAction t X * cartanAction t Y := by
  have hsum : t 0 + t 1 + t 2 = 0 := by
    simpa [Fin.sum_univ_three] using ht
  have h01 : -t 1 + -t 2 = t 0 := by linarith
  have h12 : -t 2 + -t 0 = t 1 := by linarith
  have h20 : -t 0 + -t 1 = t 2 := by linarith
  have h10 : t 1 + t 2 = -t 0 := by linarith
  have h21 : t 2 + t 0 = -t 1 := by linarith
  have h02 : t 0 + t 1 = -t 2 := by linarith
  have hcancel (i : Fin 3) :
      Real.exp (t i) * Real.exp (-t i) = 1 := by
    rw [← Real.exp_add]
    simp
  have he01 : Real.exp (-t 1) * Real.exp (-t 2) = Real.exp (t 0) := by
    rw [← Real.exp_add, h01]
  have he12 : Real.exp (-t 2) * Real.exp (-t 0) = Real.exp (t 1) := by
    rw [← Real.exp_add, h12]
  have he20 : Real.exp (-t 0) * Real.exp (-t 1) = Real.exp (t 2) := by
    rw [← Real.exp_add, h20]
  have he10 : Real.exp (t 1) * Real.exp (t 2) = Real.exp (-t 0) := by
    rw [← Real.exp_add, h10]
  have he21 : Real.exp (t 2) * Real.exp (t 0) = Real.exp (-t 1) := by
    rw [← Real.exp_add, h21]
  have he02 : Real.exp (t 0) * Real.exp (t 1) = Real.exp (-t 2) := by
    rw [← Real.exp_add, h02]
  apply Zorn.ext'
  · simp [cartanAction, mul_a, dot, Fin.sum_univ_three]
    linear_combination
      -(X.u 0 * Y.v 0) * (hcancel 0)
      + -(X.u 1 * Y.v 1) * (hcancel 1)
      + -(X.u 2 * Y.v 2) * (hcancel 2)
  · funext i
    fin_cases i <;>
      simp [cartanAction, mul_u, cross]
    · linear_combination
        (X.v 1 * Y.v 2) * he01 - (X.v 2 * Y.v 1) * he01
    · linear_combination
        (X.v 2 * Y.v 0) * he12 - (X.v 0 * Y.v 2) * he12
    · linear_combination
        (X.v 0 * Y.v 1) * he20 - (X.v 1 * Y.v 0) * he20
  · funext i
    fin_cases i <;>
      simp [cartanAction, mul_v, cross]
    · linear_combination
        -(X.u 1 * Y.u 2) * he10 + (X.u 2 * Y.u 1) * he10
    · linear_combination
        -(X.u 2 * Y.u 0) * he21 + (X.u 0 * Y.u 2) * he21
    · linear_combination
        -(X.u 0 * Y.u 1) * he02 + (X.u 1 * Y.u 0) * he02
  · simp [cartanAction, mul_b, dot, Fin.sum_univ_three]
    linear_combination
      -(X.v 0 * Y.u 0) * (hcancel 0)
      + -(X.v 1 * Y.u 1) * (hcancel 1)
      + -(X.v 2 * Y.u 2) * (hcancel 2)

theorem cartanAction_zero (X : Zorn) :
    cartanAction 0 X = X := by
  apply Zorn.ext'
  · simp [cartanAction]
  · funext i
    simp [cartanAction]
  · funext i
    simp [cartanAction]
  · simp [cartanAction]

theorem cartanAction_add (s t : Vec3) (X : Zorn) :
    cartanAction (s + t) X = cartanAction s (cartanAction t X) := by
  apply Zorn.ext'
  · simp [cartanAction]
  · funext i
    simp only [cartanAction, Pi.add_apply, Real.exp_add]
    ring
  · funext i
    simp only [cartanAction, Pi.add_apply, neg_add, Real.exp_add]
    ring
  · simp [cartanAction]

theorem cartanAction_commute (s t : Vec3) (X : Zorn) :
    cartanAction s (cartanAction t X) = cartanAction t (cartanAction s X) := by
  rw [← cartanAction_add, add_comm, cartanAction_add]

theorem cartanAction_det
    (t : Vec3) (X : Zorn) :
    det (cartanAction t X) = det X := by
  have hcancel (i : Fin 3) :
      Real.exp (t i) * Real.exp (-t i) = 1 := by
    rw [← Real.exp_add]
    simp
  simp [det, cartanAction, dot, Fin.sum_univ_three]
  linear_combination
    (X.u 0 * X.v 0) * (hcancel 0)
    + (X.u 1 * X.v 1) * (hcancel 1)
    + (X.u 2 * X.v 2) * (hcancel 2)

def cartanCoordinates (t : Vec3) : ℝ × ℝ := (t 0, t 1)

theorem cartan_third_coordinate
    (t : Vec3) (ht : ∑ i, t i = 0) :
    t 2 = -t 0 - t 1 := by
  have h := show t 0 + t 1 + t 2 = 0 by
    simpa [Fin.sum_univ_three] using ht
  linarith

theorem cartan_pairing_reduce
    (s t : Vec3) (ht : ∑ i, t i = 0) :
    (∑ i, s i * t i) =
      (s 0 - s 2) * t 0 + (s 1 - s 2) * t 1 := by
  simp only [Fin.sum_univ_three]
  rw [cartan_third_coordinate t ht]
  ring

theorem cartan_laplace_reduce
    (s t : Vec3) (ht : ∑ i, t i = 0) :
    Real.exp (-(∑ i, s i * t i)) =
      Real.exp (-((s 0 - s 2) * t 0 + (s 1 - s 2) * t 1)) := by
  rw [cartan_pairing_reduce s t ht]

theorem cartan_exponential_product
    (t : Vec3) (ht : ∑ i, t i = 0) :
    Real.exp (2 * t 0) * Real.exp (2 * t 1) * Real.exp (2 * t 2) = 1 := by
  have hsum : t 0 + t 1 + t 2 = 0 := by
    simpa [Fin.sum_univ_three] using ht
  rw [← Real.exp_add, ← Real.exp_add]
  have hscaled : 2 * t 0 + 2 * t 1 + 2 * t 2 = 0 := by
    linarith
  rw [hscaled]
  norm_num

theorem uniform_cartan_parameter_eq_zero
    (l : ℝ) (hl : ∑ _ : Fin 3, l = 0) :
    l = 0 := by
  simpa [Fin.sum_univ_three] using hl
  

theorem cartanAction_exp_add
    (s t : Vec3) (X : Zorn) :
    cartanAction (s + t) X = cartanAction s (cartanAction t X) :=
  cartanAction_add s t X

end ZornCore
