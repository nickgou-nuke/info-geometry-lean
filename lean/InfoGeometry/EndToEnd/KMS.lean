import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.EndToEnd.KMS

open Complex

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-!
=============================================================================
LAYER 3: ALGEBRAIC THERMAL EQUILIBRIUM AND LINEARIZED KMS GEOMETRY
=============================================================================

This module deliberately separates:

1. a complex-linear noncommutative derivation `D`,
2. a normalized complex-linear functional `ω`,
3. the exact first-order imaginary-time shift

      σ₁,β(Y) = Y + i β D(Y),

4. its exact algebraic KMS boundary equation

      ω(X σ₁,β(Y)) = ω(Y X),

5. the equivalent linearized KMS identity

      i β ω(X D(Y)) = ω(Y X) - ω(X Y).

No analytic-strip KMS theorem is asserted here.  The finite exponential
modular/KMS layer remains a separate owner.
-/

/-!
=============================================================================
PART 1: COMPLEX-LINEAR NONCOMMUTATIVE MODULAR DERIVATIONS
=============================================================================
-/

/--
A complex-linear derivation of a possibly noncommutative complex algebra.

Mathlib's general `LinearMap` supplies all additive/scalar-linear structure;
only the noncommutative Leibniz law is added here.
-/
structure ModularDerivation
    (A : Type*) [Ring A] [Algebra ℂ A]
    extends A →ₗ[ℂ] A where
  leibniz' :
    ∀ x y : A,
      toLinearMap (x * y) =
        toLinearMap x * y + x * toLinearMap y

namespace ModularDerivation

instance : CoeFun (ModularDerivation A) (fun _ => A → A) where
  coe D := D.toLinearMap

variable (D : ModularDerivation A)

@[simp]
theorem map_add (x y : A) :
    D (x + y) = D x + D y :=
  D.toLinearMap.map_add x y

@[simp]
theorem map_sub (x y : A) :
    D (x - y) = D x - D y :=
  D.toLinearMap.map_sub x y

@[simp]
theorem map_neg (x : A) :
    D (-x) = -D x :=
  D.toLinearMap.map_neg x

@[simp]
theorem map_zero :
    D 0 = 0 :=
  D.toLinearMap.map_zero

@[simp]
theorem map_smul (c : ℂ) (x : A) :
    D (c • x) = c • D x :=
  D.toLinearMap.map_smul c x

@[simp]
theorem leibniz (x y : A) :
    D (x * y) = D x * y + x * D y :=
  D.leibniz' x y

/--
Every complex-linear Leibniz derivation annihilates the multiplicative unit.
-/
@[simp]
theorem map_one :
    D 1 = 0 := by
  have h := D.leibniz 1 1
  simp only [one_mul, mul_one] at h
  have h' : D 1 + 0 = D 1 + D 1 := by
    simpa using h
  exact (add_left_cancel h').symm

end ModularDerivation

/-!
=============================================================================
PART 2: NORMALIZED COMPLEX-LINEAR FUNCTIONALS
=============================================================================
-/

/--
A normalized complex-linear functional.

This is intentionally weaker than a full C*-algebraic state:
positivity is not silently assumed.
-/
structure NormalizedLinearFunctional
    (A : Type*) [Ring A] [Algebra ℂ A]
    extends A →ₗ[ℂ] ℂ where
  normalized :
    toLinearMap 1 = 1

namespace NormalizedLinearFunctional

instance : CoeFun (NormalizedLinearFunctional A) (fun _ => A → ℂ) where
  coe ω := ω.toLinearMap

variable (ω : NormalizedLinearFunctional A)

@[simp]
theorem map_zero :
    ω 0 = 0 :=
  ω.toLinearMap.map_zero

@[simp]
theorem map_add (x y : A) :
    ω (x + y) = ω x + ω y :=
  ω.toLinearMap.map_add x y

@[simp]
theorem map_sub (x y : A) :
    ω (x - y) = ω x - ω y :=
  ω.toLinearMap.map_sub x y

@[simp]
theorem map_neg (x : A) :
    ω (-x) = -ω x :=
  ω.toLinearMap.map_neg x

@[simp]
theorem map_smul (c : ℂ) (x : A) :
    ω (c • x) = c * ω x := by
  simpa [smul_eq_mul] using
    ω.toLinearMap.map_smul c x

@[simp]
theorem map_one :
    ω 1 = 1 :=
  ω.normalized

end NormalizedLinearFunctional

/-!
=============================================================================
PART 3: FIRST-ORDER IMAGINARY-TIME MODULAR SHIFT
=============================================================================
-/

/--
The exact first-order imaginary-time shift

  σ₁,β = id + i β D.

It is a complex-linear map.  It is deliberately not claimed to be an
algebra homomorphism.
-/
def firstOrderImaginaryShift
    (D : ModularDerivation A)
    (β : ℝ) :
    A →ₗ[ℂ] A :=
  (LinearMap.id : A →ₗ[ℂ] A) +
    (I * (β : ℂ)) • D.toLinearMap

@[simp]
theorem firstOrderImaginaryShift_apply
    (D : ModularDerivation A)
    (β : ℝ)
    (x : A) :
    firstOrderImaginaryShift D β x =
      x + (I * (β : ℂ)) • D x := by
  simp [firstOrderImaginaryShift]

/--
The first-order imaginary-time shift preserves the unit because derivations
annihilate the unit.
-/
@[simp]
theorem firstOrderImaginaryShift_one
    (D : ModularDerivation A)
    (β : ℝ) :
    firstOrderImaginaryShift D β 1 = 1 := by
  rw [firstOrderImaginaryShift_apply, D.map_one]
  simp

/--
At β = 0 the first-order imaginary-time shift is exactly the identity.
-/
@[simp]
theorem firstOrderImaginaryShift_zero
    (D : ModularDerivation A) :
    firstOrderImaginaryShift D 0 =
      (LinearMap.id : A →ₗ[ℂ] A) := by
  apply LinearMap.ext
  intro x
  simp

/-!
=============================================================================
PART 4: ALGEBRAIC SHIFT-KMS AND LINEARIZED KMS
=============================================================================
-/

/--
Algebraic KMS boundary equation relative to a supplied linear shift `σ`.

  ω(X σ(Y)) = ω(Y X).
-/
def IsShiftKMS
    (ω : NormalizedLinearFunctional A)
    (σ : A →ₗ[ℂ] A) :
    Prop :=
  ∀ X Y : A,
    ω (X * σ Y) = ω (Y * X)

/--
The exact linearized KMS identity:

  i β ω(X D(Y)) = ω(Y X) - ω(X Y).

This is the infinitesimal/first-order KMS predicate used by this module.
-/
def IsLinearizedKMS
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A)
    (β : ℝ) :
    Prop :=
  ∀ X Y : A,
    I * (β : ℂ) * ω (X * D Y) =
      ω (Y * X) - ω (X * Y)

/--
Trace property of a normalized functional.
-/
def IsTraceFunctional
    (ω : NormalizedLinearFunctional A) :
    Prop :=
  ∀ X Y : A,
    ω (X * Y) = ω (Y * X)

/--
Exact expansion of the first-order shifted KMS pairing.
-/
theorem firstOrderShift_pairing_expansion
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A)
    (β : ℝ)
    (X Y : A) :
    ω (X * firstOrderImaginaryShift D β Y) =
      ω (X * Y) +
        (I * (β : ℂ)) * ω (X * D Y) := by
  rw [firstOrderImaginaryShift_apply]
  rw [mul_add]
  rw [mul_smul_comm]
  rw [ω.map_add, ω.map_smul]

/--
MASTER LINEARIZATION THEOREM.

The linearized KMS identity is exactly equivalent to the KMS boundary equation
for the explicit first-order imaginary-time shift

  Y ↦ Y + i β D(Y).

No asymptotic or analytic assumption is used in this equivalence.
-/
theorem firstOrderShiftKMS_iff_linearizedKMS
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A)
    (β : ℝ) :
    IsShiftKMS ω (firstOrderImaginaryShift D β) ↔
      IsLinearizedKMS ω D β := by
  constructor
  · intro hShift X Y
    have hXY := hShift X Y
    rw [firstOrderShift_pairing_expansion
      ω D β X Y] at hXY
    linear_combination hXY
  · intro hLinear X Y
    have hXY := hLinear X Y
    rw [firstOrderShift_pairing_expansion
      ω D β X Y]
    linear_combination hXY

/-!
=============================================================================
PART 5: β = 0 TRACE SECTOR
=============================================================================
-/

/--
At β = 0 the linearized KMS predicate is equivalent to the trace property.

This is an exact β = 0 theorem; it is not a statement about convergence
as β → 0.
-/
theorem linearizedKMS_zero_iff_trace
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A) :
    IsLinearizedKMS ω D 0 ↔
      IsTraceFunctional ω := by
  constructor
  · intro hKMS X Y
    have h := hKMS X Y
    have h0 :
        (0 : ℂ) =
          ω (Y * X) - ω (X * Y) := by
      simpa using h
    exact (sub_eq_zero.mp h0.symm).symm
  · intro hTrace X Y
    have h0 :
        ω (Y * X) - ω (X * Y) = 0 :=
      sub_eq_zero.mpr (hTrace X Y).symm
    simpa using h0.symm

/--
β = 0 linearized KMS implies traciality.
-/
theorem linearizedKMS_zero_is_trace
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A)
    (hKMS : IsLinearizedKMS ω D 0) :
    IsTraceFunctional ω :=
  (linearizedKMS_zero_iff_trace ω D).mp hKMS

/--
The β = 0 first-order shift-KMS condition is also exactly traciality.
-/
theorem firstOrderShiftKMS_zero_iff_trace
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A) :
    IsShiftKMS ω (firstOrderImaginaryShift D 0) ↔
      IsTraceFunctional ω := by
  rw [firstOrderShiftKMS_iff_linearizedKMS]
  exact linearizedKMS_zero_iff_trace ω D

/-!
=============================================================================
PART 6: COMMUTATOR FORM OF THE LINEARIZED KMS RELATION
=============================================================================
-/

/--
Algebra commutator.
-/
def commutator (X Y : A) : A :=
  X * Y - Y * X

/--
The linearized KMS condition determines the expectation of the commutator:

  ω([X,Y]) = - i β ω(X D(Y)).
-/
theorem linearizedKMS_commutator_expectation
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A)
    (β : ℝ)
    (hKMS : IsLinearizedKMS ω D β)
    (X Y : A) :
    ω (commutator X Y) =
      -(I * (β : ℂ) * ω (X * D Y)) := by
  have h := hKMS X Y
  calc
    ω (commutator X Y)
        = ω (X * Y) - ω (Y * X) := by
            rw [commutator, ω.map_sub]
    _ = -(ω (Y * X) - ω (X * Y)) := by
          ring
    _ = -(I * (β : ℂ) * ω (X * D Y)) := by
          rw [← h]

/-!
=============================================================================
PART 7: THERMAL STATIONARITY
=============================================================================
-/

/--
For nonzero inverse temperature, a linearized KMS functional annihilates
the modular derivation:

  ω(D X) = 0.

This is the exact infinitesimal stationarity theorem.
-/
theorem linearizedKMS_stationary
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A)
    (β : ℝ)
    (hKMS : IsLinearizedKMS ω D β)
    (hβ : (β : ℂ) ≠ 0) :
    ∀ X : A,
      ω (D X) = 0 := by
  intro X
  have h := hKMS 1 X
  simp only [one_mul, mul_one, sub_self] at h
  change
    (I * (β : ℂ)) * ω (D X) = 0
    at h
  have hIβ :
      I * (β : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero hβ
  exact (mul_eq_zero.mp h).resolve_left hIβ

/--
Bundled form of thermal stationarity:

  ω ∘ D = 0

as an equality of complex-linear maps.
-/
theorem linearizedKMS_comp_derivation_eq_zero
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A)
    (β : ℝ)
    (hKMS : IsLinearizedKMS ω D β)
    (hβ : (β : ℂ) ≠ 0) :
    ω.toLinearMap.comp D.toLinearMap = 0 := by
  apply LinearMap.ext
  intro X
  change ω (D X) = 0
  exact linearizedKMS_stationary
    ω D β hKMS hβ X

/-!
=============================================================================
PART 8: STATIONARITY FROM THE FIRST-ORDER KMS BOUNDARY EQUATION
=============================================================================
-/

/--
The first-order shift-KMS boundary equation implies infinitesimal thermal
stationarity at nonzero β.
-/
theorem firstOrderShiftKMS_stationary
    (ω : NormalizedLinearFunctional A)
    (D : ModularDerivation A)
    (β : ℝ)
    (hShift :
      IsShiftKMS ω (firstOrderImaginaryShift D β))
    (hβ : (β : ℂ) ≠ 0) :
    ∀ X : A,
      ω (D X) = 0 := by
  have hLinear :
      IsLinearizedKMS ω D β :=
    (firstOrderShiftKMS_iff_linearizedKMS
      ω D β).mp hShift
  exact linearizedKMS_stationary
    ω D β hLinear hβ

end InfoGeometry.EndToEnd.KMS

end noncomputable section
