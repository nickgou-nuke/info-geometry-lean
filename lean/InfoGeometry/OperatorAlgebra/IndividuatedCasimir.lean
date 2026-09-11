/-
InfoGeometry/OperatorAlgebra/IndividuatedCasimir.lean

The individuation of the Casimir.

This file kills the first Casimir shadow.

Instead of assuming

  is_central : Prop
  is_invariant : Prop

we construct a quadratic Clifford-type Casimir

  C = sum_i gamma_i gamma_i

from a finite Clifford frame satisfying

  gamma_i gamma_i = q_i • 1.

Then we prove constructively:

  C = (sum_i q_i) • 1,
  C is central,
  C is invariant under every invertible conjugation.

This is the algebraic core needed before moving to trace/Pfaffian/Freudenthal
or Cl(4,4)-specific realizations.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open scoped BigOperators

namespace InfoGeometry.OperatorAlgebra.IndividuatedCasimir

/-! ## 1. Invertible conjugation -/

/-!
`InvertibleTransport` is the repository-facing name for Mathlib's native unit
carrier.  The alias preserves the existing API while making the inverse laws
and coercions come from `Units` rather than from a duplicate wrapper.
-/
abbrev InvertibleTransport (Op : Type*) [Monoid Op] := Opˣ

namespace InvertibleTransport

variable {Op : Type*} [Monoid Op]

/--
Conjugation by an invertible transport:

`T ↦ U T U⁻¹`.
-/
def conjugate
    (U : InvertibleTransport Op)
    (T : Op) : Op :=
  U.val * T * U.inv

end InvertibleTransport

/-! ## 2. Verified Casimir -/

/--
A verified Casimir element is an element with a proved centrality law.

This is not a vacuous `Prop` socket. Downstream users receive the centrality
theorem as data.
-/
structure VerifiedCasimir
    (Op : Type*) [Mul Op] where
  element : Op
  central :
    ∀ X : Op, element * X = X * element

namespace VerifiedCasimir

variable {Op : Type*} [Monoid Op]
variable (C : VerifiedCasimir Op)

/--
A verified Casimir is fixed by every invertible conjugation.
-/
theorem fixed_by_conjugation
    (U : InvertibleTransport Op) :
    U.conjugate C.element = C.element := by
  dsimp [InvertibleTransport.conjugate]
  calc
    U.val * C.element * U.inv
        = C.element * U.val * U.inv := by
            rw [← C.central U.val]
    _ = C.element * (U.val * U.inv) := by
            rw [mul_assoc]
    _ = C.element * 1 := by
            rw [U.val_inv]
    _ = C.element := by
            simp

end VerifiedCasimir

/-! ## 3. Scalar Casimirs are constructively central -/

/--
A scalar element of an algebra is a verified Casimir.
-/
def scalarVerifiedCasimir
    (Op : Type*) [Ring Op] [Algebra ℝ Op]
    (a : ℝ) :
    VerifiedCasimir Op where
  element := algebraMap ℝ Op a
  central := by
    intro X
    exact Algebra.commutes a X

/--
Scalar Casimirs are invariant under invertible conjugation.
-/
theorem scalarVerifiedCasimir_fixed_by_conjugation
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (a : ℝ)
    (U : InvertibleTransport Op) :
    U.conjugate (algebraMap ℝ Op a) =
      algebraMap ℝ Op a :=
  (scalarVerifiedCasimir Op a).fixed_by_conjugation U

/-! ## 4. Finite Clifford frame -/

/--
A finite Clifford-type frame.

The key constructive law is

`gamma_i gamma_i = q_i • 1`.

The anticommutation law is included because it is part of the Clifford frame,
but the first quadratic Casimir centrality theorem only needs the square laws.
-/
structure CliffordFrame
    (ι Op : Type*) [Fintype ι] [DecidableEq ι]
    [Ring Op] [Algebra ℝ Op] where

  /-- Clifford generators. -/
  gamma : ι → Op

  /-- Signature coefficient of each generator. -/
  signature : ι → ℝ

  /-- Squaring law: `gamma_i^2 = q_i · 1`. -/
  gamma_sq :
    ∀ i : ι,
      gamma i * gamma i = algebraMap ℝ Op (signature i)

  /-- Anticommutation for distinct generators. -/
  anticomm :
    ∀ i j : ι,
      i ≠ j →
        gamma i * gamma j + gamma j * gamma i = 0

namespace CliffordFrame

variable
    {ι Op : Type*}
    [Fintype ι] [DecidableEq ι]
    [Ring Op] [Algebra ℝ Op]

variable (F : CliffordFrame ι Op)

/--
Quadratic Clifford Casimir:

`C = sum_i gamma_i gamma_i`.
-/
def quadraticCasimir : Op :=
  ∑ i : ι, F.gamma i * F.gamma i

/--
Scalar value of the quadratic Casimir:

`sum_i q_i`.
-/
def quadraticScalar : ℝ :=
  ∑ i : ι, F.signature i

/--
The quadratic Clifford Casimir is exactly scalar.
-/
theorem quadraticCasimir_eq_scalar :
    F.quadraticCasimir =
      algebraMap ℝ Op F.quadraticScalar := by
  dsimp [quadraticCasimir, quadraticScalar]
  calc
    (∑ i : ι, F.gamma i * F.gamma i)
        = ∑ i : ι, algebraMap ℝ Op (F.signature i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact F.gamma_sq i
    _ = algebraMap ℝ Op (∑ i : ι, F.signature i) := by
            simp only [
              (map_sum (algebraMap ℝ Op)
                (fun i : ι => F.signature i)
                Finset.univ).symm]

/--
The quadratic Clifford Casimir is constructively central.
-/
theorem quadraticCasimir_central
    (X : Op) :
    F.quadraticCasimir * X = X * F.quadraticCasimir := by
  rw [F.quadraticCasimir_eq_scalar]
  exact Algebra.commutes F.quadraticScalar X

/--
The quadratic Clifford Casimir packaged as a verified Casimir.
-/
def quadraticVerifiedCasimir :
    VerifiedCasimir Op where
  element := F.quadraticCasimir
  central := F.quadraticCasimir_central

/--
The quadratic Clifford Casimir is invariant under every invertible conjugation.
-/
theorem quadraticCasimir_fixed_by_conjugation
    (U : InvertibleTransport Op) :
    U.conjugate F.quadraticCasimir = F.quadraticCasimir :=
  F.quadraticVerifiedCasimir.fixed_by_conjugation U

end CliffordFrame

end InfoGeometry.OperatorAlgebra.IndividuatedCasimir
