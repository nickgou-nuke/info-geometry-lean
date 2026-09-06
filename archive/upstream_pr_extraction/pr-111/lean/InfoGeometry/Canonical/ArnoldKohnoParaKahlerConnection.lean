import Mathlib
import InfoGeometry.Projective.ArnoldRelations

/-!
# Arnold--Kohno flatness certificate for logarithmic/KZ-type connections

This owner keeps the supplied exterior-form relation separate from the
coefficient-algebra commutator relation.  It proves the finite quadratic
curvature cancellation and does not assert closure of actual differential
forms.
-/

namespace InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection

open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]
variable {M : Type*} [AddCommGroup M] [Module R M]

abbrev Forms (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] := ExteriorAlgebra R M
abbrev CurvatureCarrier (R : Type*) (A : Type*) (M : Type*)
    [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M] :=
  A ⊗[R] Forms R M

def comm (x y : A) : A := x * y - y * x

@[simp] theorem comm_self (x : A) : comm x x = 0 := by simp [comm]

theorem comm_swap (x y : A) : comm y x = - comm x y := by
  unfold comm
  noncomm_ring

def weightedForm (x : A) (alpha : Forms R M) :
    CurvatureCarrier R A M := x ⊗ₜ[R] alpha

@[simp] theorem weightedForm_zero_left (alpha : Forms R M) :
    weightedForm (R := R) (A := A) (0 : A) alpha = 0 := by
  simp [weightedForm]

@[simp] theorem weightedForm_zero_right (x : A) :
    weightedForm (R := R) x (0 : Forms R M) = 0 := by
  simp [weightedForm]

def triangleCurvature
    (t12 t23 t31 : A)
    (w12 w23 w31 : Forms R M) : CurvatureCarrier R A M :=
  weightedForm (R := R) (comm t12 t23) (w12 * w23) +
  weightedForm (R := R) (comm t23 t31) (w23 * w31) +
  weightedForm (R := R) (comm t31 t12) (w31 * w12)

theorem kohno_third_coefficient
    (t12 t23 t31 : A)
    (h12 : comm t12 (t31 + t23) = 0) :
    comm t31 t12 = comm t12 t23 := by
  have hsum : comm t12 t31 + comm t12 t23 = 0 := by
    simpa [comm, mul_add, add_mul, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using h12
  have hfirst : comm t12 t31 = - comm t12 t23 :=
    eq_neg_of_add_eq_zero_left hsum
  calc
    comm t31 t12 = - comm t12 t31 := comm_swap t12 t31
    _ = comm t12 t23 := by rw [hfirst]; simp

theorem kohno_second_coefficient
    (t12 t23 t31 : A)
    (h23 : comm t23 (t12 + t31) = 0) :
    comm t23 t31 = comm t12 t23 := by
  have hsum : comm t23 t12 + comm t23 t31 = 0 := by
    simpa [comm, mul_add, add_mul, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using h23
  have hsecond : comm t23 t31 = - comm t23 t12 :=
    eq_neg_of_add_eq_zero_right hsum
  calc
    comm t23 t31 = - comm t23 t12 := hsecond
    _ = comm t12 t23 := by rw [comm_swap t12 t23]; simp

theorem triangleCurvature_factorizes
    (t12 t23 t31 : A) (w12 w23 w31 : Forms R M)
    (h12 : comm t12 (t31 + t23) = 0)
    (h23 : comm t23 (t12 + t31) = 0) :
    triangleCurvature (R := R) t12 t23 t31 w12 w23 w31 =
      weightedForm (R := R) (comm t12 t23)
        (w12 * w23 + w23 * w31 + w31 * w12) := by
  rw [triangleCurvature,
    kohno_second_coefficient t12 t23 t31 h23,
    kohno_third_coefficient t12 t23 t31 h12]
  simp only [weightedForm, TensorProduct.tmul_add]

theorem arnold_kohno_triangle_flat
    (t12 t23 t31 : A) (w12 w23 w31 : Forms R M)
    (hArnold : w12 * w23 + w23 * w31 + w31 * w12 = 0)
    (h12 : comm t12 (t31 + t23) = 0)
    (h23 : comm t23 (t12 + t31) = 0) :
    triangleCurvature (R := R) t12 t23 t31 w12 w23 w31 = 0 := by
  rw [triangleCurvature_factorizes t12 t23 t31 w12 w23 w31 h12 h23,
    hArnold]
  simp

theorem disjoint_channel_flat
    (tij tkl : A) (wij wkl : Forms R M)
    (hdisjoint : comm tij tkl = 0) :
    weightedForm (R := R) (comm tij tkl) (wij * wkl) = 0 := by
  rw [hdisjoint]
  simp

structure LogarithmicArnoldTriangle
    (w12 w23 w31 : Forms R M) : Type where
  closed12 : Prop
  closed23 : Prop
  closed31 : Prop
  arnold : w12 * w23 + w23 * w31 + w31 * w12 = 0

theorem logarithmicArnoldTriangle_quadratic_flat
    (t12 t23 t31 : A) (w12 w23 w31 : Forms R M)
    (H : LogarithmicArnoldTriangle (R := R) w12 w23 w31)
    (h12 : comm t12 (t31 + t23) = 0)
    (h23 : comm t23 (t12 + t31) = 0) :
    triangleCurvature (R := R) t12 t23 t31 w12 w23 w31 = 0 :=
  arnold_kohno_triangle_flat t12 t23 t31 w12 w23 w31 H.arnold h12 h23

end InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection
