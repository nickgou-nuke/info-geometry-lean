import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis
import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native faithful color representation on the complex Zorn upper lane

The downstream proof workspace contains a faithful `gl₃(ℂ)` action on a larger
Dirac-spinor carrier.  Its faithfulness witness is concentrated on the positive
`u : Fin 3 → ℂ` Zorn coordinate.  This module reconstructs that minimal
representation natively, without importing the downstream spinor stack.

The actual representation carrier is the upper color lane `Fin 3 → ℂ`.  The
lane embeds injectively into the native complex Zorn carrier as the pure upper
off-diagonal sector.  Since that Zorn owner intentionally uses explicit
`zornAdd`/`zornSmul` operations instead of installing a global module instance,
linearity of the embedding is recorded by explicit preservation theorems.

No claim is made that this is the full split-octonion automorphism action or the
physical QCD gauge representation.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDNativeZornColorRepresentation

open Matrix
open InfoGeometry.Physics.SplitOctonionBraidSU3

abbrev Zorn := InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn
abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C
abbrev ColorLane := Fin 3 → ℂ

/-- The defining matrix action on the three-component color lane. -/
def colorAction (A : M3C) : ColorLane →ₗ[ℂ] ColorLane where
  toFun u := fun i => ∑ j : Fin 3, A i j * u j
  map_add' u v := by
    funext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ j, A i j * (c * u j)) = ∑ j, c * (A i j * u j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = c * ∑ j, A i j * u j := by rw [Finset.mul_sum]

@[simp] theorem colorAction_apply (A : M3C) (u : ColorLane) (i : Fin 3) :
    colorAction A u i = ∑ j : Fin 3, A i j * u j := rfl

/-- Matrix multiplication is represented by composition. -/
theorem colorAction_mul (A B : M3C) :
    colorAction (A * B) = colorAction A * colorAction B := by
  apply LinearMap.ext
  intro u
  funext i
  change (∑ x, (∑ j, A i j * B j x) * u x) =
    ∑ j, A i j * (∑ x, B j x * u x)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

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
  simp [colorAction, Matrix.smul_apply, mul_assoc, smul_eq_mul,
    Finset.mul_sum]

/-- The defining action preserves associative commutators. -/
theorem colorAction_commutator (A B : M3C) :
    colorAction (A * B - B * A) =
      colorAction A * colorAction B -
        colorAction B * colorAction A := by
  rw [colorAction_sub, colorAction_mul, colorAction_mul]

/-- Pure upper-lane embedding into the native complex Zorn carrier. -/
def upperLaneEmbedding (u : ColorLane) : Zorn :=
  { a := 0, u := u, v := 0, b := 0 }

@[simp] theorem upperLaneEmbedding_a (u : ColorLane) :
    (upperLaneEmbedding u).a = 0 := rfl

@[simp] theorem upperLaneEmbedding_u (u : ColorLane) :
    (upperLaneEmbedding u).u = u := rfl

@[simp] theorem upperLaneEmbedding_v (u : ColorLane) :
    (upperLaneEmbedding u).v = 0 := rfl

@[simp] theorem upperLaneEmbedding_b (u : ColorLane) :
    (upperLaneEmbedding u).b = 0 := rfl

/-- The coordinate embedding preserves lane addition using the explicit Zorn
addition operation. -/
theorem upperLaneEmbedding_add (u v : ColorLane) :
    upperLaneEmbedding (u + v) =
      zornAdd (upperLaneEmbedding u) (upperLaneEmbedding v) := by
  apply zorn_ext
  · simp [upperLaneEmbedding, zornAdd]
  · funext i; rfl
  · funext i; simp [upperLaneEmbedding, zornAdd]
  · simp [upperLaneEmbedding, zornAdd]

/-- The coordinate embedding preserves scalar multiplication using the explicit
Zorn scalar operation. -/
theorem upperLaneEmbedding_smul (c : ℂ) (u : ColorLane) :
    upperLaneEmbedding (c • u) =
      zornSmul c (upperLaneEmbedding u) := by
  apply zorn_ext
  · simp [upperLaneEmbedding, zornSmul]
  · funext i; rfl
  · funext i; simp [upperLaneEmbedding, zornSmul]
  · simp [upperLaneEmbedding, zornSmul]

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
  classical
  simp [colorAction, colorBasis, Pi.single_apply, Finset.sum_eq_single]

/-- The defining color representation is faithful. -/
theorem colorAction_injective : Function.Injective colorAction := by
  intro A B hAB
  apply Matrix.ext
  intro r s
  have h := LinearMap.congr_fun hAB (colorBasis s)
  have hr := congrFun h r
  rw [colorAction_basis A r s, colorAction_basis B r s] at hr
  exact hr

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
          colorAction B * colorAction A) ∧
    (∀ c : ℂ, ∀ u : ColorLane,
      upperLaneEmbedding (c • u) =
        zornSmul c (upperLaneEmbedding u)) :=
  ⟨colorAction_injective, upperLaneEmbedding_injective,
    colorAction_mul, colorAction_commutator, upperLaneEmbedding_smul⟩

end InfoGeometry.Physics.QCDNativeZornColorRepresentation

end noncomputable section
