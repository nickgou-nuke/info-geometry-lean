import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Native faithful color representation on the complex Zorn upper lane

The downstream proof workspace contains a faithful `gl₃(ℂ)` action on a larger
Dirac-spinor carrier.  Its faithfulness witness is concentrated on the positive
`u : Fin 3 → ℂ` Zorn coordinate.  This module reconstructs that minimal
representation natively, without importing the downstream spinor stack.

The actual representation carrier is the upper color lane `Fin 3 → ℂ`.  It is
embedded linearly and injectively into the native complex Zorn carrier as the
pure upper off-diagonal sector.  Keeping the representation on the lane itself
avoids an affine spectator term on the scalar/lower Zorn coordinates and makes
the `gl₃(ℂ)` representation law exact.

No claim is made that this is the full split-octonion automorphism action or the
physical QCD gauge representation.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDNativeZornColorRepresentation

open Matrix
open InfoGeometry.Physics.SplitOctonionBraidSU3

abbrev Zorn := InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn
abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev ColorLane := Fin 3 → ℂ

/-- The defining matrix action on the three-component color lane. -/
def colorAction (A : M3C) : ColorLane →ₗ[ℂ] ColorLane where
  toFun u := fun i => ∑ j : Fin 3, A i j * u j
  map_add' u v := by
    funext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    funext i
    simp [mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem colorAction_apply (A : M3C) (u : ColorLane) (i : Fin 3) :
    colorAction A u i = ∑ j : Fin 3, A i j * u j := rfl

/-- Matrix multiplication is represented by composition. -/
theorem colorAction_mul (A B : M3C) :
    colorAction (A * B) = colorAction A * colorAction B := by
  apply LinearMap.ext
  intro u
  funext i
  simp [colorAction, Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- The action is additive in the matrix argument. -/
theorem colorAction_add (A B : M3C) :
    colorAction (A + B) = colorAction A + colorAction B := by
  apply LinearMap.ext
  intro u
  funext i
  simp [colorAction, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- The action respects subtraction in the matrix argument. -/
theorem colorAction_sub (A B : M3C) :
    colorAction (A - B) = colorAction A - colorAction B := by
  apply LinearMap.ext
  intro u
  funext i
  simp [colorAction, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The action is homogeneous in the matrix argument. -/
theorem colorAction_smul (c : ℂ) (A : M3C) :
    colorAction (c • A) = c • colorAction A := by
  apply LinearMap.ext
  intro u
  funext i
  simp [colorAction, Matrix.smul_apply, mul_assoc]

/-- The defining action preserves associative commutators. -/
theorem colorAction_commutator (A B : M3C) :
    colorAction (A * B - B * A) =
      colorAction A * colorAction B -
        colorAction B * colorAction A := by
  rw [colorAction_sub, colorAction_mul, colorAction_mul]

/-- Pure upper-lane embedding into the native complex Zorn carrier. -/
def upperLaneEmbedding : ColorLane →ₗ[ℂ] Zorn where
  toFun u := { a := 0, u := u, v := 0, b := 0 }
  map_add' u v := by
    apply zorn_ext
    · rfl
    · rfl
    · rfl
    · rfl
  map_smul' c u := by
    apply zorn_ext
    · rfl
    · rfl
    · rfl
    · rfl

@[simp] theorem upperLaneEmbedding_a (u : ColorLane) :
    (upperLaneEmbedding u).a = 0 := rfl

@[simp] theorem upperLaneEmbedding_u (u : ColorLane) :
    (upperLaneEmbedding u).u = u := rfl

@[simp] theorem upperLaneEmbedding_v (u : ColorLane) :
    (upperLaneEmbedding u).v = 0 := rfl

@[simp] theorem upperLaneEmbedding_b (u : ColorLane) :
    (upperLaneEmbedding u).b = 0 := rfl

/-- The upper-lane embedding loses no color information. -/
theorem upperLaneEmbedding_injective : Function.Injective upperLaneEmbedding := by
  intro u v huv
  have hu := congrArg (fun X : Zorn => X.u) huv
  simpa using hu

/-- Standard color basis vector. -/
def colorBasis (s : Fin 3) : ColorLane := Pi.single s 1

/-- Evaluation on basis vectors recovers every matrix coefficient. -/
theorem colorAction_basis (A : M3C) (r s : Fin 3) :
    colorAction A (colorBasis s) r = A r s := by
  simp [colorAction, colorBasis]

/-- The defining color representation is faithful. -/
theorem colorAction_injective : Function.Injective colorAction := by
  intro A B hAB
  apply Matrix.ext
  intro r s
  have h := LinearMap.congr_fun hAB (colorBasis s)
  have hr := congrFun h r
  simpa [colorAction_basis] using hr

/-- The native Zorn embedding realizes the faithful action on its upper lane. -/
theorem upperLaneEmbedding_action (A : M3C) (u : ColorLane) :
    upperLaneEmbedding (colorAction A u) =
      { a := 0
        u := fun i => ∑ j : Fin 3, A i j * u j
        v := 0
        b := 0 } := rfl

/-- Consolidated native faithful `gl₃(ℂ)` representation and Zorn realization. -/
theorem native_zorn_color_representation_packet :
    Function.Injective colorAction ∧
    Function.Injective upperLaneEmbedding ∧
    (∀ A B : M3C,
      colorAction (A * B) = colorAction A * colorAction B) ∧
    (∀ A B : M3C,
      colorAction (A * B - B * A) =
        colorAction A * colorAction B -
          colorAction B * colorAction A) :=
  ⟨colorAction_injective, upperLaneEmbedding_injective,
    colorAction_mul, colorAction_commutator⟩

end InfoGeometry.Physics.QCDNativeZornColorRepresentation

end noncomputable section
