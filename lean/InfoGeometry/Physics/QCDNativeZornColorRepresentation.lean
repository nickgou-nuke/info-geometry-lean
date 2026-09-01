import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Native faithful color representation on the complex Zorn upper lane

The downstream proof workspace contains a faithful `gl₃(ℂ)` action on a larger
Dirac-spinor carrier.  Its faithfulness witness is already concentrated on the
positive `u : Fin 3 → ℂ` Zorn coordinate.  This module reconstructs that
minimal theorem-bearing core directly on the native
`SplitOctonionBraidSU3.Zorn` carrier.

For a matrix `A`, `upperColorAction A` acts by the defining matrix action on the
upper three-vector and leaves the other Zorn coordinates unchanged.  This gives
a genuine faithful associative representation, hence a faithful commutator/Lie
representation, on the native complex Zorn carrier.

No claim is made that this is the full split-octonion automorphism action or the
physical QCD gauge representation.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDNativeZornColorRepresentation

open Matrix
open InfoGeometry.Physics.SplitOctonionBraidSU3

abbrev Zorn := InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn
abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ

/-- Defining `gl₃(ℂ)` action on the upper Zorn color coordinate.  The scalar
and lower coordinates are spectators. -/
def upperColorAction (A : M3C) : Zorn →ₗ[ℂ] Zorn where
  toFun X :=
    { a := X.a
      u := fun i => ∑ j : Fin 3, A i j * X.u j
      v := X.v
      b := X.b }
  map_add' X Y := by
    apply zorn_ext
    · rfl
    · funext i
      simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    · rfl
    · rfl
  map_smul' c X := by
    apply zorn_ext
    · rfl
    · funext i
      simp [Finset.mul_sum, mul_assoc]
    · rfl
    · rfl

@[simp] theorem upperColorAction_a (A : M3C) (X : Zorn) :
    (upperColorAction A X).a = X.a := rfl

@[simp] theorem upperColorAction_u (A : M3C) (X : Zorn) (i : Fin 3) :
    (upperColorAction A X).u i = ∑ j : Fin 3, A i j * X.u j := rfl

@[simp] theorem upperColorAction_v (A : M3C) (X : Zorn) :
    (upperColorAction A X).v = X.v := rfl

@[simp] theorem upperColorAction_b (A : M3C) (X : Zorn) :
    (upperColorAction A X).b = X.b := rfl

/-- Matrix multiplication is represented by composition. -/
theorem upperColorAction_mul (A B : M3C) :
    upperColorAction (A * B) = upperColorAction A * upperColorAction B := by
  apply LinearMap.ext
  intro X
  apply zorn_ext
  · rfl
  · funext i
    simp [upperColorAction, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [mul_assoc]
  · rfl
  · rfl

/-- The zero matrix acts trivially on the color lane and leaves the spectator
coordinates unchanged. -/
theorem upperColorAction_zero (X : Zorn) :
    upperColorAction (0 : M3C) X =
      { a := X.a, u := 0, v := X.v, b := X.b } := by
  apply zorn_ext <;> simp [upperColorAction]

/-- Subtraction of matrices is represented pointwise. -/
theorem upperColorAction_sub (A B : M3C) (X : Zorn) :
    upperColorAction (A - B) X =
      upperColorAction A X - upperColorAction B X +
        { a := X.a, u := 0, v := X.v, b := X.b } := by
  apply zorn_ext
  · simp [upperColorAction, zornSub, zornAdd]
  · funext i
    simp [upperColorAction, Matrix.sub_apply, Finset.sum_sub_distrib]
  · simp [upperColorAction, zornSub, zornAdd]
  · simp [upperColorAction, zornSub, zornAdd]

/-- Pure upper-color probe carrying the `s`th standard basis vector. -/
def upperProbe (s : Fin 3) : Zorn :=
  { a := 0, u := Pi.single s 1, v := 0, b := 0 }

/-- Evaluation on the upper probes recovers every matrix coefficient. -/
theorem upperColorAction_probe (A : M3C) (r s : Fin 3) :
    (upperColorAction A (upperProbe s)).u r = A r s := by
  simp [upperColorAction, upperProbe]

/-- The native upper-lane representation is faithful. -/
theorem upperColorAction_injective : Function.Injective upperColorAction := by
  intro A B hAB
  apply Matrix.ext
  intro r s
  have h := LinearMap.congr_fun hAB (upperProbe s)
  have hu := congrArg (fun X : Zorn => X.u r) h
  simpa [upperColorAction_probe] using hu

/-- Faithful commutator representation, stated on the native Zorn carrier. -/
theorem upperColorAction_commutator (A B : M3C) :
    upperColorAction (A * B - B * A) =
      upperColorAction A * upperColorAction B -
        upperColorAction B * upperColorAction A := by
  apply LinearMap.ext
  intro X
  apply zorn_ext
  · simp [upperColorAction]
  · funext i
    simp [upperColorAction, Matrix.mul_apply, Matrix.sub_apply,
      Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    ring
  · simp [upperColorAction]
  · simp [upperColorAction]

/-- Consolidated native faithful `gl₃(ℂ)` color-representation packet. -/
theorem native_zorn_color_representation_packet :
    Function.Injective upperColorAction ∧
    (∀ A B : M3C,
      upperColorAction (A * B) = upperColorAction A * upperColorAction B) ∧
    (∀ A B : M3C,
      upperColorAction (A * B - B * A) =
        upperColorAction A * upperColorAction B -
          upperColorAction B * upperColorAction A) :=
  ⟨upperColorAction_injective, upperColorAction_mul,
    upperColorAction_commutator⟩

end InfoGeometry.Physics.QCDNativeZornColorRepresentation

end noncomputable section
