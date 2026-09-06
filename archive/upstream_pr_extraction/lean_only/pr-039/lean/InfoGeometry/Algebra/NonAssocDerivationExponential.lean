import InfoGeometry.Algebra.NonAssocDerivationKernel
import InfoGeometry.Lie.ContinuousDerivationExponential
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Native nonassociative automorphisms from continuous derivation flows

`InfoGeometry.Lie.ContinuousDerivationExponential` already proves the hard
analytic theorem: for an arbitrary continuous bilinear multiplication, the
operator exponential of a continuous derivation is multiplicative.  This file
does not duplicate that proof.  It provides the missing adapter to the
repository-native `NonAssocAut` structure and records the unit, group-law,
fixed-kernel, and orbit equations in that interface.

Two entry points are supplied.

* `expNonAssocDerivation` starts from a continuous multiplication and a
  continuous derivation.
* `expFiniteDimensionalNonAssocDerivation` starts from a linear derivation on a
  finite-dimensional real normed carrier; only the multiplication must already
  be supplied as a continuous bilinear map.

Constructing a concrete normed realization and continuous multiplication for
the repository's coordinate-free `SplitCayley` carrier remains a separate
carrier bridge.  No path-ordered or time-dependent exponential is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra.NonAssocDerivationExponential

open InfoGeometry.Lie.BaezG2SplitOctonion

namespace CDE := InfoGeometry.Lie.ContinuousDerivationExponential

variable {A : Type*}
variable [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
variable [NonUnitalNonAssocRing A] [IsScalarTower ℝ A A]
variable [SMulCommClass ℝ A A] [One A]

abbrev ContinuousEnd := A →L[ℝ] A
abbrev ContinuousMul := A →L[ℝ] A →L[ℝ] A

/-- A supplied continuous bilinear multiplication agrees with the native
nonassociative product. -/
def RepresentsNativeMul (mul : ContinuousMul (A := A)) : Prop :=
  ∀ x y : A, mul x y = x * y

/-- The continuous derivation predicate rewritten for the native product. -/
def IsNativeContinuousDerivation
    (D : ContinuousEnd (A := A)) : Prop :=
  ∀ x y : A, D (x * y) = D x * y + x * D y

/-- Translate a native Leibniz law to the generic continuous multiplication
predicate used by `ContinuousDerivationExponential`. -/
theorem isDerivation_of_representsNativeMul
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D) :
    CDE.IsDerivation mul D := by
  intro x y
  rw [hmul x y, hmul (D x) y, hmul x (D y)]
  exact hD x y

/-- A continuous native derivation kills a supplied two-sided unit. -/
theorem continuousDerivation_kills_one
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x) :
    D (1 : A) = 0 := by
  exact InfoGeometry.Algebra.NonAssocDerivationKernel.linearDerivation_kills_one
    D.toLinearMap hD one_mul' mul_one'

/-- Every scalar identity direction is fixed infinitesimally. -/
theorem continuousDerivation_kills_smul_one
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (c : ℝ) :
    D (c • (1 : A)) = 0 := by
  exact InfoGeometry.Algebra.NonAssocDerivationKernel.linearDerivation_kills_smul_one
    D.toLinearMap hD one_mul' mul_one' c

/-- The operator exponential of a continuous nonassociative derivation,
packaged as the repository-native automorphism carrier. -/
def expNonAssocDerivation
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (t : ℝ) : NonAssocAut ℝ A where
  toLinearEquiv := CDE.flowLinearEquiv D t
  map_one' :=
    CDE.flowLinearEquiv_fixed_of_derivation_eq_zero D 1
      (continuousDerivation_kills_one D hD one_mul' mul_one') t
  map_mul' x y := by
    change CDE.flowLinearEquiv D t (x * y) =
      CDE.flowLinearEquiv D t x * CDE.flowLinearEquiv D t y
    rw [← hmul x y, ← hmul (CDE.flowLinearEquiv D t x)
      (CDE.flowLinearEquiv D t y)]
    exact CDE.exponential_derivation_is_automorphism mul D
      (isDerivation_of_representsNativeMul mul hmul D hD) t x y

@[simp]
theorem expNonAssocDerivation_apply
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (t : ℝ) (x : A) :
    expNonAssocDerivation mul hmul D hD one_mul' mul_one' t x =
      CDE.flow D t x :=
  rfl

@[simp]
theorem expNonAssocDerivation_zero_apply
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (x : A) :
    expNonAssocDerivation mul hmul D hD one_mul' mul_one' 0 x = x := by
  simp [expNonAssocDerivation_apply]

/-- Pointwise one-parameter group law in the native automorphism interface. -/
theorem expNonAssocDerivation_add_apply
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (s t : ℝ) (x : A) :
    expNonAssocDerivation mul hmul D hD one_mul' mul_one' (s + t) x =
      expNonAssocDerivation mul hmul D hD one_mul' mul_one' s
        (expNonAssocDerivation mul hmul D hD one_mul' mul_one' t x) := by
  exact CDE.flowLinearEquiv_add_apply D s t x

/-- Negative time is the inverse automorphism. -/
theorem expNonAssocDerivation_neg_apply
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (t : ℝ) (x : A) :
    expNonAssocDerivation mul hmul D hD one_mul' mul_one' (-t)
      (expNonAssocDerivation mul hmul D hD one_mul' mul_one' t x) = x := by
  exact CDE.flowLinearEquiv_neg_apply D t x

/-- Every vector in the derivation kernel is fixed by the integrated flow. -/
theorem expNonAssocDerivation_fixed_of_mem_ker
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    {x : A} (hx : x ∈ LinearMap.ker D.toLinearMap)
    (t : ℝ) :
    expNonAssocDerivation mul hmul D hD one_mul' mul_one' t x = x := by
  rw [LinearMap.mem_ker] at hx
  exact CDE.flowLinearEquiv_fixed_of_derivation_eq_zero D x hx t

/-- In particular, all scalar identity directions are fixed by the flow. -/
theorem expNonAssocDerivation_fixed_smul_one
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (c t : ℝ) :
    expNonAssocDerivation mul hmul D hD one_mul' mul_one' t
        (c • (1 : A)) = c • (1 : A) := by
  exact CDE.flowLinearEquiv_fixed_of_derivation_eq_zero D _
    (continuousDerivation_kills_smul_one D hD one_mul' mul_one' c) t

/-- Autonomous orbit equation `u'(t) = D(u(t))`. -/
theorem expNonAssocDerivation_orbit_hasDerivAt
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : ContinuousEnd (A := A))
    (hD : IsNativeContinuousDerivation D)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (u₀ : A) (t : ℝ) :
    HasDerivAt
      (fun s => expNonAssocDerivation mul hmul D hD one_mul' mul_one' s u₀)
      (D (expNonAssocDerivation mul hmul D hD one_mul' mul_one' t u₀)) t := by
  exact (CDE.hasStrictDerivAt_orbit D u₀ t).hasDerivAt

/-! ## Finite-dimensional linear-derivation adapter -/

section FiniteDimensional

variable [FiniteDimensional ℝ A]

/-- A linear endomorphism on a finite-dimensional normed carrier, viewed as a
continuous endomorphism. -/
def continuousEndOfLinear (D : Module.End ℝ A) : ContinuousEnd (A := A) :=
  LinearMap.toContinuousLinearMap D

@[simp]
theorem continuousEndOfLinear_apply
    (D : Module.End ℝ A) (x : A) :
    continuousEndOfLinear D x = D x :=
  rfl

/-- Finite-dimensional entry point from a native linear Leibniz derivation,
once a continuous bilinear realization of multiplication is supplied. -/
def expFiniteDimensionalNonAssocDerivation
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : Module.End ℝ A)
    (hD : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (t : ℝ) : NonAssocAut ℝ A :=
  expNonAssocDerivation mul hmul (continuousEndOfLinear D) hD
    one_mul' mul_one' t

@[simp]
theorem expFiniteDimensionalNonAssocDerivation_apply
    (mul : ContinuousMul (A := A))
    (hmul : RepresentsNativeMul mul)
    (D : Module.End ℝ A)
    (hD : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (one_mul' : ∀ x : A, (1 : A) * x = x)
    (mul_one' : ∀ x : A, x * (1 : A) = x)
    (t : ℝ) (x : A) :
    expFiniteDimensionalNonAssocDerivation mul hmul D hD
        one_mul' mul_one' t x =
      CDE.flow (continuousEndOfLinear D) t x :=
  rfl

end FiniteDimensional

end InfoGeometry.Algebra.NonAssocDerivationExponential
