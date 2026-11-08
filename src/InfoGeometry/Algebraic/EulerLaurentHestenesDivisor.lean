import Mathlib.Algebra.Polynomial.Laurent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Physics.SymmetricAsymmetricXP

/-!
# Finite Euler charge and Hestenes divisor transport

This owner keeps the local pole/zero layer finite and algebraic.  A local
model is a Laurent polynomial written as `T ν * U`; `ν : ℤ` is its signed
divisor order and `U` is an explicitly supplied Laurent unit.  The Euler
readout is the finite monomial rule `uⁿ ↦ n uⁿ`.

The rotor transport is deliberately supplied as a multiplicative integer
action.  This records the Hestenes replacement for winding monodromy without
introducing a complex scalar, a logarithm branch, an integral, or an analytic
continuation theorem.
-/

noncomputable section

namespace InfoGeometry.Algebraic.EulerLaurentHestenesDivisor

open InfoGeometry.Physics.SymmetricAsymmetricXP
open InfoGeometry.Krein

variable {R : Type*} [CommRing R]

/-! ## Finite Laurent Euler readout -/

/-- The finite Laurent monomial carrying coefficient `c` and exponent `n`. -/
def laurentMonomial (c : R) (n : ℤ) : LaurentPolynomial R :=
  LaurentPolynomial.C c * LaurentPolynomial.T n

/-- Algebraic Euler charge of a Laurent monomial. -/
def eulerMonomial (c : R) (n : ℤ) : LaurentPolynomial R :=
  n • laurentMonomial c n

@[simp] theorem eulerMonomial_eq_charge_mul
    (c : R) (n : ℤ) :
    eulerMonomial c n = (n : R) • laurentMonomial c n := by
  unfold eulerMonomial
  rw [Int.cast_smul_eq_zsmul]

@[simp] theorem eulerMonomial_one
    (n : ℤ) :
    eulerMonomial (1 : R) n =
      n • (LaurentPolynomial.C (1 : R) * LaurentPolynomial.T n) := by
  rfl

/-! ## Signed local divisor normal form -/

/-- A finite local Laurent normal form `F = u^ν U` with an explicit unit. -/
structure LocalLaurentNormalForm where
  order : ℤ
  unit : LaurentPolynomial R
  carrier : LaurentPolynomial R
  normal_form : carrier = LaurentPolynomial.T order * unit
  unit_isUnit : IsUnit unit

/-- Product of two finite Laurent normal forms.

The carrier and unit multiply, while the signed Laurent order adds. -/
def LocalLaurentNormalForm.mul
    (F G : LocalLaurentNormalForm (R := R)) :
    LocalLaurentNormalForm (R := R) where
  order := F.order + G.order
  unit := F.unit * G.unit
  carrier := F.carrier * G.carrier
  normal_form := by
    rw [F.normal_form, G.normal_form]
    simp only [mul_assoc, LaurentPolynomial.T_add]
    ring
  unit_isUnit := F.unit_isUnit.mul G.unit_isUnit

@[simp] theorem LocalLaurentNormalForm.mul_order
    (F G : LocalLaurentNormalForm (R := R)) :
    (F.mul G).order = F.order + G.order :=
  rfl

@[simp] theorem LocalLaurentNormalForm.mul_unit
    (F G : LocalLaurentNormalForm (R := R)) :
    (F.mul G).unit = F.unit * G.unit :=
  rfl

@[simp] theorem LocalLaurentNormalForm.mul_carrier
    (F G : LocalLaurentNormalForm (R := R)) :
    (F.mul G).carrier = F.carrier * G.carrier :=
  rfl

theorem LocalLaurentNormalForm.mul_normal_form
    (F G : LocalLaurentNormalForm (R := R)) :
    (F.mul G).carrier =
      LaurentPolynomial.T (F.order + G.order) * (F.unit * G.unit) :=
  (F.mul G).normal_form

/-- The signed pole/zero order carried by a local normal form. -/
def divisorOrder (F : LocalLaurentNormalForm (R := R)) : ℤ :=
  F.order

@[simp] theorem divisorOrder_mul
    (F G : LocalLaurentNormalForm (R := R)) :
    divisorOrder (F.mul G) = divisorOrder F + divisorOrder G :=
  rfl

@[simp] theorem divisorOrder_eq_order
    (F : LocalLaurentNormalForm (R := R)) :
    divisorOrder F = F.order :=
  rfl

theorem divisorOrder_pos_of_zero
    (F : LocalLaurentNormalForm (R := R))
    (h : 0 < F.order) :
    0 < divisorOrder F := by
  exact h

theorem divisorOrder_neg_of_pole
    (F : LocalLaurentNormalForm (R := R))
    (h : F.order < 0) :
    divisorOrder F < 0 := by
  exact h

theorem divisorOrder_eq_zero_of_regular
    (F : LocalLaurentNormalForm (R := R))
    (h : F.order = 0) :
    divisorOrder F = 0 := by
  exact h

/-! Exact order classifications.  These are equivalences for the stored
integer order; the structure does not separately encode analytic zero/pole
predicates. -/

theorem divisorOrder_pos_iff
    (F : LocalLaurentNormalForm (R := R)) :
    0 < divisorOrder F ↔ 0 < F.order := by
  rfl

theorem divisorOrder_neg_iff
    (F : LocalLaurentNormalForm (R := R)) :
    divisorOrder F < 0 ↔ F.order < 0 := by
  rfl

theorem divisorOrder_eq_zero_iff
    (F : LocalLaurentNormalForm (R := R)) :
    divisorOrder F = 0 ↔ F.order = 0 := by
  rfl

/-! ## Finite divisor index -/

/-- A finite marked divisor with signed integer order at each mark. -/
structure FiniteDivisorData (A : Type*) [Fintype A] where
  order : A → ℤ

/-- The finite pole-minus-zero charge, with signs supplied by `order`. -/
def divisorIndex
    {A : Type*} [Fintype A]
    (D : FiniteDivisorData A) : ℤ :=
  ∑ a, D.order a

@[simp] theorem divisorIndex_empty
    (D : FiniteDivisorData (Fin 0)) :
    divisorIndex D = 0 := by
  simp [divisorIndex]

theorem divisorIndex_reflection_invariant
    {A : Type*} [Fintype A]
    (D : FiniteDivisorData A)
    (reflect : A ≃ A)
    (horder : ∀ a, D.order (reflect a) = D.order a) :
    divisorIndex D = ∑ a, D.order (reflect a) := by
  simp [divisorIndex, horder]

/-- The Euler charge of the distinguished local monomial is its order. -/
theorem euler_charge_of_local_order
    (F : LocalLaurentNormalForm (R := R)) :
    divisorOrder F = F.order :=
  rfl

/-! ## Hestenes winding transport -/

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- A finite real rotor representation of the integer winding group. -/
structure WindingRotorTransport where
  transport : ℤ → EndH
  zero : transport 0 = ContinuousLinearMap.id ℝ H₂
  add : ∀ m n : ℤ,
    transport (m + n) =
      (transport m).comp (transport n)
  elliptic_axis_sq :
    (bivectorAxis (E := E)).comp bivectorAxis =
      -(ContinuousLinearMap.id ℝ H₂)

/-- Transport the signed local divisor order into the real Hestenes carrier. -/
def divisorMonodromy
    (W : WindingRotorTransport (E := E))
    (F : LocalLaurentNormalForm (R := R)) : EndH :=
  W.transport (divisorOrder F)

@[simp] theorem divisorMonodromy_eq_transport_order
    (W : WindingRotorTransport (E := E))
    (F : LocalLaurentNormalForm (R := R)) :
    divisorMonodromy W F = W.transport F.order :=
  rfl

theorem divisorMonodromy_add
    (W : WindingRotorTransport (E := E))
    (F G : LocalLaurentNormalForm (R := R))
    :
    W.transport (F.order + G.order) =
      (W.transport F.order).comp (W.transport G.order) := by
  exact W.add F.order G.order

theorem divisorMonodromy_mul
    (W : WindingRotorTransport (E := E))
    (F G : LocalLaurentNormalForm (R := R)) :
    divisorMonodromy W (F.mul G) =
      (divisorMonodromy W F).comp (divisorMonodromy W G) := by
  unfold divisorMonodromy
  exact W.add F.order G.order

/-! ## Reflection of signed divisor packets -/

section Reflection

variable {A : Type*}

/-- A finite involutive reflection carrying divisor orders. -/
structure ReflectedDivisorData where
  reflect : A → A
  involutive : Function.Involutive reflect
  order : A → ℤ
  order_reflect : ∀ a, order (reflect a) = order a

@[simp] theorem reflected_order
    (P : ReflectedDivisorData (A := A)) (a : A) :
    P.order (P.reflect a) = P.order a :=
  P.order_reflect a

theorem reflected_reflected_order
    (P : ReflectedDivisorData (A := A)) (a : A) :
    P.order (P.reflect (P.reflect a)) = P.order a := by
  rw [P.involutive a]

end Reflection

end InfoGeometry.Algebraic.EulerLaurentHestenesDivisor

end noncomputable section
