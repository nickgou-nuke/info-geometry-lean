import Mathlib
import InfoGeometry.Projective.ArnoldRelations

/-!
# Arnold--Kohno flatness certificate for logarithmic/KZ-type connections

This owner keeps three layers separate.

* `omega`-type objects are supplied exterior 1-forms.  They may later be
  instantiated by genuine `d log Qᵢⱼ` forms, but this file does not manufacture
  differential forms from combinatorial edge labels.
* `tᵢⱼ` are coefficients in an associative algebra.  Their commutator is the
  Lie bracket used in the infinitesimal braid/Kohno relations.
* curvature lives in the tensor product of the coefficient algebra with the
  exterior algebra of forms.

For one three-point channel the proof is exact:

  Kohno relations make the three commutator coefficients equal;
  the Arnold three-term wedge relation then annihilates their common tensor
  factor.

Thus this is a kernel-level algebraic certificate for the quadratic part
`A ∧ A` of a KZ/Maurer--Cartan-type connection.  To conclude flatness of an
actual differential connection `F = dA + A ∧ A`, an instantiation must also
supply closure `d omegaᵢⱼ = 0` (as happens for genuine logarithmic 1-forms).

No BCFW recursion, monodromy representation, para-Kaehler identification, or
projective-state QGT theorem is asserted here without a separate bridge.
-/

namespace InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection

open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]
variable {M : Type*} [AddCommGroup M] [Module R M]

abbrev Forms := ExteriorAlgebra R M
abbrev CurvatureCarrier := A ⊗[R] Forms

/-- Associative-algebra commutator, used as the coefficient Lie bracket. -/
def comm (x y : A) : A := x * y - y * x

@[simp] theorem comm_self (x : A) : comm x x = 0 := by
  simp [comm]

theorem comm_swap (x y : A) : comm y x = - comm x y := by
  unfold comm
  noncomm_ring

/-- A coefficient-weighted exterior form. -/
def weightedForm (x : A) (alpha : Forms) : CurvatureCarrier :=
  x ⊗ₜ[R] alpha

@[simp] theorem weightedForm_zero_left (alpha : Forms) :
    weightedForm (R := R) (A := A) (0 : A) alpha = 0 := by
  simp [weightedForm]

@[simp] theorem weightedForm_zero_right (x : A) :
    weightedForm (R := R) x (0 : Forms) = 0 := by
  simp [weightedForm]

/-- The quadratic curvature contribution of one Arnold triangle.

The three factors are the three Lie brackets multiplying the three Arnold
wedge channels. -/
def triangleCurvature
    (t12 t23 t31 : A) (w12 w23 w31 : Forms) : CurvatureCarrier :=
  weightedForm (R := R) (comm t12 t23) (w12 * w23) +
  weightedForm (R := R) (comm t23 t31) (w23 * w31) +
  weightedForm (R := R) (comm t31 t12) (w31 * w12)

/-- First Kohno reduction: `[t12,t31+t23]=0` identifies the third coefficient
with `[t12,t23]`. -/
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

/-- Second Kohno reduction: `[t23,t12+t31]=0` identifies the second
coefficient with `[t12,t23]`. -/
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

/-- Under the two triangle Kohno relations, the entire quadratic curvature
factorizes through the Arnold three-term exterior expression. -/
theorem triangleCurvature_factorizes
    (t12 t23 t31 : A) (w12 w23 w31 : Forms)
    (h12 : comm t12 (t31 + t23) = 0)
    (h23 : comm t23 (t12 + t31) = 0) :
    triangleCurvature (R := R) t12 t23 t31 w12 w23 w31 =
      weightedForm (R := R) (comm t12 t23)
        (w12 * w23 + w23 * w31 + w31 * w12) := by
  rw [triangleCurvature,
    kohno_second_coefficient t12 t23 t31 h23,
    kohno_third_coefficient t12 t23 t31 h12]
  simp only [weightedForm, TensorProduct.tmul_add]
  abel

/-- **Arnold + Kohno => vanishing quadratic KZ curvature on a triangle.**

This is the exact finite algebraic core of the standard flatness argument.
The exterior hypothesis is the Arnold relation; the coefficient hypotheses are
the infinitesimal braid/Kohno relations. -/
theorem arnold_kohno_triangle_flat
    (t12 t23 t31 : A) (w12 w23 w31 : Forms)
    (hArnold : w12 * w23 + w23 * w31 + w31 * w12 = 0)
    (h12 : comm t12 (t31 + t23) = 0)
    (h23 : comm t23 (t12 + t31) = 0) :
    triangleCurvature (R := R) t12 t23 t31 w12 w23 w31 = 0 := by
  rw [triangleCurvature_factorizes t12 t23 t31 w12 w23 w31 h12 h23,
    hArnold]
  simp

/-- Disjoint Kohno channels contribute no quadratic curvature whenever their
coefficient generators commute. -/
theorem disjoint_channel_flat
    (tij tkl : A) (wij wkl : Forms)
    (hdisjoint : comm tij tkl = 0) :
    weightedForm (R := R) (comm tij tkl) (wij * wkl) = 0 := by
  rw [hdisjoint]
  simp

/-- A small contract separating the actual differential statement from the
algebraic Arnold--Kohno certificate.  `closed` is the future `d omega = 0`
socket; `arnold` records the logarithmic three-term identity. -/
structure LogarithmicArnoldTriangle
    (w12 w23 w31 : Forms) : Prop where
  closed12 : Prop
  closed23 : Prop
  closed31 : Prop
  arnold : w12 * w23 + w23 * w31 + w31 * w12 = 0

/-- The quadratic curvature part vanishes for any logarithmic Arnold triangle
once the Kohno coefficient relations are supplied.  The `closed` fields are
kept in the contract for the later genuine differential-form realization. -/
theorem logarithmicArnoldTriangle_quadratic_flat
    (t12 t23 t31 : A) (w12 w23 w31 : Forms)
    (H : LogarithmicArnoldTriangle (R := R) w12 w23 w31)
    (h12 : comm t12 (t31 + t23) = 0)
    (h23 : comm t23 (t12 + t31) = 0) :
    triangleCurvature (R := R) t12 t23 t31 w12 w23 w31 = 0 :=
  arnold_kohno_triangle_flat t12 t23 t31 w12 w23 w31 H.arnold h12 h23

end InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection
