import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis
import proofs.ZornColorLieAction
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Bundled faithful color Lie representation

The matrix-unit commutator proved in `ZornColorLieAction` is extended by
linearity to a native Mathlib `LinearMap` from `gl₃(ℂ)`, with an explicit
commutator-preservation theorem. Faithfulness is proved by evaluating on the
positive-`u` coordinate sector, where the action is the defining matrix action.
-/

noncomputable section

namespace ZornColorLieRepresentation

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open InfoGeometry.Physics.SplitOctonionBraidSU3
open ZornThreeChannelCAR ZornColorLieAction

/-- Linear extension of the color matrix-unit operators. -/
def colorLieActionLinear :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ DiracSpinor16 where
  toFun A := ∑ r : Fin 3, ∑ s : Fin 3, A r s • colorEvenOp r s
  map_add' A B := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp [Matrix.smul_apply, Finset.smul_sum, smul_smul]

@[simp] theorem colorLieActionLinear_apply (A : Matrix (Fin 3) (Fin 3) ℂ) :
    colorLieActionLinear A =
      ∑ r : Fin 3, ∑ s : Fin 3, A r s • colorEvenOp r s := rfl

/-- The linear extension sends a matrix unit to its proved color operator. -/
@[simp] theorem colorLieActionLinear_single (r s : Fin 3) (c : ℂ) :
    colorLieActionLinear (Matrix.single r s c) = c • colorEvenOp r s := by
  fin_cases r <;> fin_cases s <;>
    simp [colorLieActionLinear, Fin.sum_univ_three]

private theorem matrixSingle_mul (r s t u : Fin 3) (a b : ℂ) :
    Matrix.single r s a * Matrix.single t u b =
      colorDelta s t • Matrix.single r u (a * b) := by
  classical
  by_cases hst : s = t
  · subst t
    simp [colorDelta]
  · simp [colorDelta, hst]

/-- The linear extension preserves the associative commutator. -/
theorem colorLieActionLinear_commutator (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorLieActionLinear (A * B - B * A) =
      colorLieActionLinear A * colorLieActionLinear B -
        colorLieActionLinear B * colorLieActionLinear A := by
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A₁ A₂ h₁ h₂ =>
      calc
        colorLieActionLinear ((A₁ + A₂) * B - B * (A₁ + A₂)) =
            colorLieActionLinear ((A₁ * B - B * A₁) +
              (A₂ * B - B * A₂)) := by congr 1; noncomm_ring
        _ = colorLieActionLinear (A₁ * B - B * A₁) +
              colorLieActionLinear (A₂ * B - B * A₂) :=
                colorLieActionLinear.map_add _ _
        _ = _ := by simp only [map_add]; rw [h₁, h₂]; noncomm_ring
  | h_std_basis r s a =>
      induction B using Matrix.induction_on' with
      | h_zero => simp
      | h_add B₁ B₂ h₁ h₂ =>
          calc
            colorLieActionLinear
                (Matrix.single r s a * (B₁ + B₂) -
                  (B₁ + B₂) * Matrix.single r s a) =
                colorLieActionLinear
                  ((Matrix.single r s a * B₁ - B₁ * Matrix.single r s a) +
                   (Matrix.single r s a * B₂ - B₂ * Matrix.single r s a)) := by
                    congr 1; noncomm_ring
            _ = colorLieActionLinear
                  (Matrix.single r s a * B₁ - B₁ * Matrix.single r s a) +
                colorLieActionLinear
                  (Matrix.single r s a * B₂ - B₂ * Matrix.single r s a) :=
                    colorLieActionLinear.map_add _ _
            _ = _ := by simp only [map_add]; rw [h₁, h₂]; noncomm_ring
      | h_std_basis t u b =>
          rw [matrixSingle_mul, matrixSingle_mul, map_sub, map_smul,
            map_smul, colorLieActionLinear_single,
            colorLieActionLinear_single, colorLieActionLinear_single,
            colorLieActionLinear_single]
          calc
            colorDelta s t • (a * b) • colorEvenOp r u -
                colorDelta u r • (b * a) • colorEvenOp t s =
              (a * b) •
                (colorDelta s t • colorEvenOp r u -
                  colorDelta u r • colorEvenOp t s) := by
                    rw [mul_comm b a]
                    module

            _ = (a * b) •
                (colorEvenOp r s * colorEvenOp t u -
                  colorEvenOp t u * colorEvenOp r s) := by
                    rw [colorEvenOp_commutator]
            _ = a • colorEvenOp r s * b • colorEvenOp t u -
                b • colorEvenOp t u * a • colorEvenOp r s := by
                    simp only [smul_sub, smul_mul_smul]
                    module

/-- Positive-`u` probe carrying the `s`th standard color vector. -/
def positiveUProbe (s : Fin 3) : DiracSpinor16 :=
  (⟨{ a := 0, u := Pi.single s 1, v := 0, b := 0 }⟩, 0)

/-- Linear extraction of one positive-`u` coordinate. -/
def positiveUCoord (r : Fin 3) : DiracSpinor16 →ₗ[ℂ] ℂ where
  toFun X := X.1.val.u r
  map_add' X Y := by rw [Prod.fst_add, copy_add_val]; rfl
  map_smul' c X := by rw [Prod.smul_fst, copy_smul_val]; rfl

@[simp] theorem positiveUCoord_apply (r : Fin 3) (X : DiracSpinor16) :
    positiveUCoord r X = X.1.val.u r := rfl

theorem colorEvenOp_probe_u (r s i j : Fin 3) :
    (colorEvenOp r s (positiveUProbe j)).1.val.u i =
      colorDelta i r * colorDelta s j := by
  rw [colorEvenOp_fst_exact]
  by_cases hsj : s = j <;> by_cases hir : i = r <;>
    simp [positiveUProbe, colorPlusZorn, mixedPlusZorn, colorDelta,
      hsj, hir, InfoGeometry.Physics.SplitOctonionBraidSU3.zornSmul]

/-- Evaluation on the positive-`u` probes recovers every matrix coefficient. -/
theorem colorLieActionLinear_probe_u (A : Matrix (Fin 3) (Fin 3) ℂ)
    (r s : Fin 3) :
    ((colorLieActionLinear A) (positiveUProbe s)).1.val.u r = A r s := by
  change positiveUCoord r ((colorLieActionLinear A) (positiveUProbe s)) = A r s
  rw [colorLieActionLinear_apply, LinearMap.sum_apply, map_sum]
  change (∑ x : Fin 3, positiveUCoord r
    (∑ y : Fin 3, A x y • colorEvenOp x y (positiveUProbe s))) = A r s
  simp_rw [map_sum, map_smul, positiveUCoord_apply, colorEvenOp_probe_u]
  simp [colorDelta]

/-- The color representation is faithful.  Together with
`colorLieActionLinear_commutator`, this is the faithful `gl₃` representation
packet without an elaboration-heavy wrapper. -/
theorem colorLieActionLinear_injective : Function.Injective colorLieActionLinear := by
  intro A B hAB
  apply Matrix.ext
  intro r s
  have hprobe := congrArg
    (fun F : Module.End ℂ DiracSpinor16 =>
      positiveUCoord r (F (positiveUProbe s))) hAB
  change ((colorLieActionLinear A) (positiveUProbe s)).1.val.u r =
    ((colorLieActionLinear B) (positiveUProbe s)).1.val.u r at hprobe
  rw [colorLieActionLinear_probe_u, colorLieActionLinear_probe_u] at hprobe
  exact hprobe

end ZornColorLieRepresentation

end noncomputable section
