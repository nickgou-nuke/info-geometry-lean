import InfoGeometry.Clifford.SplitCl44CausalEnvelope
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Zero-Jacobian Weyl boundary

This file proves the canonical finite-dimensional determinant fact behind the
zero-volume causal-boundary slogan:

* a finite Weyl factor multiplies the transported volume density;
* it cannot turn a zero Jacobian determinant into a nonzero one;
* identifying the zero-Jacobian locus with a metric/null cone is an additional
  compatibility condition, not an automatic consequence of Weyl scaling.

The proofs use mathlib's matrix determinant scaling theorem.  There is no
noncanonical bridge or classification theorem here.
-/

namespace InfoGeometry.Volume.ZeroJacobianWeylBoundary

open InfoGeometry.Clifford.SplitCl44CausalEnvelope

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Scalar zero-volume invariance -/

/-- Finite Weyl scaling of a scalar volume readout. -/
noncomputable def weylScaledVolume (weight phi Vol : ℝ) : ℝ :=
  Real.exp (weight * phi) * Vol

/--
The zero-volume locus is invariant under finite Weyl scaling.

This is the scalar theorem behind `0 * exp(λ) = 0`: the exponential Weyl
factor is never zero, so it cannot create or remove a zero volume.
-/
theorem weylScaledVolume_eq_zero_iff
    (weight phi Vol : ℝ) :
    weylScaledVolume weight phi Vol = 0 ↔ Vol = 0 := by
  unfold weylScaledVolume
  have hexp : Real.exp (weight * phi) ≠ 0 := Real.exp_ne_zero _
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (hexp h)
    · exact h
  · intro h
    exact Or.inr h

/-- Equivalent orientation: zero volume before scaling iff zero volume after scaling. -/
theorem zeroVolume_weylInvariant
    (weight phi Vol : ℝ) :
    Vol = 0 ↔ weylScaledVolume weight phi Vol = 0 :=
  (weylScaledVolume_eq_zero_iff weight phi Vol).symm

/-! ## Matrix Jacobian scaling -/

/-- A finite Weyl scaling of a Jacobian matrix. -/
noncomputable def weylScaledJacobian (phi : ℝ) (J : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  Real.exp phi • J

/-- The Weyl-scaled Jacobian determinant is the determinant times a nonzero scalar power. -/
theorem det_weylScaledJacobian
    (phi : ℝ) (J : Matrix ι ι ℝ) :
    (weylScaledJacobian (ι := ι) phi J).det =
      (Real.exp phi) ^ Fintype.card ι * J.det := by
  simp [weylScaledJacobian]

/--
Finite Weyl scaling preserves the zero-Jacobian locus.

This is the compact algebraic theorem:
`det DF = 0 ↔ det D(e^phi F) = 0`.
-/
theorem det_weylScaledJacobian_eq_zero_iff
    (phi : ℝ) (J : Matrix ι ι ℝ) :
    (weylScaledJacobian (ι := ι) phi J).det = 0 ↔ J.det = 0 := by
  rw [det_weylScaledJacobian]
  have hpow : (Real.exp phi) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (Real.exp_ne_zero phi)
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (hpow h)
    · exact h
  · intro h
    exact Or.inr h

/-- Zero-Jacobian boundary predicate for a finite Jacobian matrix. -/
def IsZeroJacobianBoundary (J : Matrix ι ι ℝ) : Prop :=
  J.det = 0

@[simp] theorem isZeroJacobianBoundary_iff (J : Matrix ι ι ℝ) :
    IsZeroJacobianBoundary J ↔ J.det = 0 :=
  Iff.rfl

/-- Boundary membership is invariant under finite Weyl scaling. -/
theorem isZeroJacobianBoundary_weylScaled_iff
    (phi : ℝ) (J : Matrix ι ι ℝ) :
    IsZeroJacobianBoundary (weylScaledJacobian (ι := ι) phi J)
      ↔ IsZeroJacobianBoundary J :=
  det_weylScaledJacobian_eq_zero_iff phi J

/-! ## Total transported density -/

/--
Total scalar transported density:
`exp(dim * phi) * |det J|`.

The natural geometric `dim` can be kept separate from the matrix index type,
which is useful when the density line and coordinate chart are tracked by
different owner modules.
-/
noncomputable def totalTransportDensity
    (dim : Nat) (phi : ℝ) (J : Matrix ι ι ℝ) : ℝ :=
  Real.exp ((dim : ℝ) * phi) * |J.det|

/--
The total transported density vanishes exactly when the Jacobian determinant
vanishes.  Finite Weyl volume scaling cannot remove a zero determinant.
-/
theorem totalTransportDensity_eq_zero_iff_det_eq_zero
    (dim : Nat) (phi : ℝ) (J : Matrix ι ι ℝ) :
    totalTransportDensity (ι := ι) dim phi J = 0 ↔ J.det = 0 := by
  unfold totalTransportDensity
  have hexp : Real.exp ((dim : ℝ) * phi) ≠ 0 :=
    Real.exp_ne_zero _
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (hexp h)
    · exact abs_eq_zero.mp h
  · intro h
    exact Or.inr (abs_eq_zero.mpr h)

/-- Zero total density is invariant under finite Weyl scaling. -/
theorem totalTransportDensity_zero_iff_zeroJacobianBoundary
    (dim : Nat) (phi : ℝ) (J : Matrix ι ι ℝ) :
    totalTransportDensity (ι := ι) dim phi J = 0
      ↔ IsZeroJacobianBoundary J :=
  totalTransportDensity_eq_zero_iff_det_eq_zero dim phi J

/-! ## Explicit null-locus comparisons -/

/-- A concrete Jacobian degeneracy predicate for a pointwise Jacobian map. -/
def IsZeroJacobianPointBoundary
    {Point : Type*} (jacobian : Point → Matrix ι ι ℝ) (x : Point) : Prop :=
  (jacobian x).det = 0

/-- A concrete metric-null predicate for any explicit quadratic readout `Q`. -/
def IsNullPoint {Point : Type*} (Q : Point → ℝ) (x : Point) : Prop :=
  Q x = 0

@[simp] theorem isZeroJacobianPointBoundary_iff
    {Point : Type*} (jacobian : Point → Matrix ι ι ℝ) (x : Point) :
    IsZeroJacobianPointBoundary (ι := ι) jacobian x ↔ (jacobian x).det = 0 :=
  Iff.rfl

@[simp] theorem isNullPoint_iff
    {Point : Type*} (Q : Point → ℝ) (x : Point) :
    IsNullPoint Q x ↔ Q x = 0 :=
  Iff.rfl

/--
If an explicit Jacobian map and an explicit quadratic readout have the same
zero locus at `x`, then the zero-Jacobian boundary is exactly the null locus
at `x`.
-/
theorem zeroJacobianBoundary_iff_null_of_iff
    {Point : Type*} (jacobian : Point → Matrix ι ι ℝ) (Q : Point → ℝ)
    (x : Point) (h : (jacobian x).det = 0 ↔ Q x = 0) :
    IsZeroJacobianPointBoundary (ι := ι) jacobian x ↔ IsNullPoint Q x :=
  h

/--
Under an explicit zero-locus equality at `x`, the total transported density
vanishes exactly on the null locus at `x`.
-/
theorem totalTransportDensity_zero_iff_null_of_iff
    {Point : Type*} (jacobian : Point → Matrix ι ι ℝ) (Q : Point → ℝ)
    (dim : Nat) (phi : ℝ) (x : Point)
    (h : (jacobian x).det = 0 ↔ Q x = 0) :
    totalTransportDensity (ι := ι) dim phi (jacobian x) = 0 ↔ IsNullPoint Q x :=
  (totalTransportDensity_eq_zero_iff_det_eq_zero dim phi (jacobian x)).trans h

/-! ## Split `Cl(4,4)` specialization -/

/-- The explicit null predicate for the split `(4,4)` carrier. -/
def IsSplitCl44NullPoint (x : SplitCl44Carrier) : Prop :=
  IsNullPoint SplitCl44Quad x

@[simp] theorem isSplitCl44NullPoint_iff (x : SplitCl44Carrier) :
    IsSplitCl44NullPoint x ↔ SplitCl44Quad x = 0 :=
  Iff.rfl

end InfoGeometry.Volume.ZeroJacobianWeylBoundary
