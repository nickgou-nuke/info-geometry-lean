import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

noncomputable section

set_option linter.unusedSectionVars false

namespace InfoGeometry.Lie.ContinuousDerivationExponential

variable {A : Type*}
variable
  [NormedAddCommGroup A]
  [NormedSpace ℝ A]
  [CompleteSpace A]

local notation "EndA" => A →L[ℝ] A

noncomputable local instance : NormedRing EndA := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndA := inferInstance
local instance : NormedAlgebra ℚ EndA := NormedAlgebra.restrictScalars ℚ ℝ EndA
local instance : IsTopologicalRing EndA := inferInstance
local instance : CompleteSpace EndA := inferInstance

def IsDerivation
    (mul : A →L[ℝ] A →L[ℝ] A)
    (D : EndA) : Prop :=
  ∀ x y : A,
    D (mul x y) =
      mul (D x) y + mul x (D y)

noncomputable def flow
    (D : EndA)
    (t : ℝ) : EndA :=
  NormedSpace.exp (t • D)

@[simp]
theorem flow_zero
    (D : EndA) :
    flow D 0 = 1 := by
  dsimp [flow]
  rw [zero_smul, NormedSpace.exp_zero]

theorem smul_commute_smul
    (D : EndA)
    (s t : ℝ) :
    Commute (s • D) (t • D) := by
  exact ((Commute.refl D).smul_left s).smul_right t

theorem flow_add
    (D : EndA)
    (s t : ℝ) :
    flow D (s + t) =
      flow D s * flow D t := by
  simpa [flow, add_smul] using
    (NormedSpace.exp_add_of_commute
      (smul_commute_smul D s t))

@[simp]
theorem flow_neg_generator
    (D : EndA)
    (t : ℝ) :
    flow (-D) t = flow D (-t) := by
  simp [flow, smul_neg, neg_smul]

theorem flow_mul_flow_neg
    (D : EndA)
    (t : ℝ) :
    flow D t * flow (-D) t = 1 := by
  rw [flow_neg_generator]
  simpa using (flow_add D t (-t)).symm

theorem flow_neg_mul_flow
    (D : EndA)
    (t : ℝ) :
    flow (-D) t * flow D t = 1 := by
  rw [flow_neg_generator]
  simpa using (flow_add D (-t) t).symm

@[simp]
theorem flow_apply_flow_neg
    (D : EndA)
    (t : ℝ)
    (x : A) :
    flow D t (flow (-D) t x) = x := by
  have h := flow_mul_flow_neg D t
  exact ContinuousLinearMap.ext_iff.mp h x

@[simp]
theorem flow_neg_apply_flow
    (D : EndA)
    (t : ℝ)
    (x : A) :
    flow (-D) t (flow D t x) = x := by
  have h := flow_neg_mul_flow D t
  exact ContinuousLinearMap.ext_iff.mp h x

theorem hasStrictDerivAt_flow_left
    (D : EndA)
    (t : ℝ) :
    HasStrictDerivAt
      (flow D)
      (D * flow D t)
      t := by
  simpa [flow] using
    (hasStrictDerivAt_exp_smul_const' D t)

theorem hasStrictDerivAt_flow_right
    (D : EndA)
    (t : ℝ) :
    HasStrictDerivAt
      (flow D)
      (flow D t * D)
      t := by
  simpa [flow] using
    (hasStrictDerivAt_exp_smul_const D t)

private noncomputable def evalOp :
    EndA →L[ℝ] A →L[ℝ] A :=
  (ContinuousLinearMap.apply ℝ A).flip

@[simp]
private theorem evalOp_apply
    (T : EndA)
    (x : A) :
    evalOp T x = T x := by
  rfl

theorem hasStrictDerivAt_orbit
    (D : EndA)
    (x : A)
    (t : ℝ) :
    HasStrictDerivAt
      (fun s : ℝ => flow D s x)
      (D (flow D t x))
      t := by
  have h :=
    (evalOp (A := A)).hasStrictDerivAt_of_bilinear
      (hasStrictDerivAt_flow_left D t)
      (hasStrictDerivAt_const t x)
  simpa [evalOp] using h

theorem hasStrictDerivAt_orbit_right
    (D : EndA)
    (x : A)
    (t : ℝ) :
    HasStrictDerivAt
      (fun s : ℝ => flow D s x)
      (flow D t (D x))
      t := by
  have h :=
    (evalOp (A := A)).hasStrictDerivAt_of_bilinear
      (hasStrictDerivAt_flow_right D t)
      (hasStrictDerivAt_const t x)
  simpa [evalOp] using h

theorem flow_apply_derivation
    (D : EndA)
    (t : ℝ)
    (x : A) :
    flow D t (D x) =
      D (flow D t x) := by
  have h :=
    (hasStrictDerivAt_orbit D x t).hasDerivAt.unique
      (hasStrictDerivAt_orbit_right D x t).hasDerivAt
  exact h.symm

theorem hasStrictDerivAt_mul_orbit
    (mul : A →L[ℝ] A →L[ℝ] A)
    (D : EndA)
    (hD : IsDerivation mul D)
    (x y : A)
    (t : ℝ) :
    HasStrictDerivAt
      (fun s : ℝ =>
        mul (flow D s x) (flow D s y))
      (D (mul (flow D t x) (flow D t y)))
      t := by
  have h :=
    mul.hasStrictDerivAt_of_bilinear
      (hasStrictDerivAt_orbit D x t)
      (hasStrictDerivAt_orbit D y t)
  convert h using 1
  rw [hD]
  abel

noncomputable def interaction
    (mul : A →L[ℝ] A →L[ℝ] A)
    (D : EndA)
    (x y : A)
    (t : ℝ) : A :=
  flow (-D) t
    (mul (flow D t x) (flow D t y))

theorem hasStrictDerivAt_interaction_zero
    (mul : A →L[ℝ] A →L[ℝ] A)
    (D : EndA)
    (hD : IsDerivation mul D)
    (x y : A)
    (t : ℝ) :
    HasStrictDerivAt
      (interaction mul D x y)
      0
      t := by
  let p : ℝ → A :=
    fun s =>
      mul (flow D s x) (flow D s y)
  have hp :
      HasStrictDerivAt
        p
        (D (p t))
        t := by
    simpa [p] using
      hasStrictDerivAt_mul_orbit
        mul D hD x y t
  have hback :
      HasStrictDerivAt
        (flow (-D))
        (flow (-D) t * (-D))
        t :=
    hasStrictDerivAt_flow_right (-D) t
  have h :=
    (evalOp (A := A)).hasStrictDerivAt_of_bilinear
      hback hp
  have hz :
      flow (-D) t (D (p t)) +
          (flow (-D) t * (-D)) (p t)
        =
      0 := by
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply, add_neg_cancel]
  have h_eq : (fun s => (evalOp (flow (-D) s)) (p s)) = interaction mul D x y := by
    ext s; rfl
  rw [← h_eq]
  simpa [evalOp, hz] using h

theorem interaction_eq_initial
    (mul : A →L[ℝ] A →L[ℝ] A)
    (D : EndA)
    (hD : IsDerivation mul D)
    (x y : A)
    (t : ℝ) :
    interaction mul D x y t =
      mul x y := by
  have hder :
      ∀ s : ℝ,
        HasDerivAt
          (interaction mul D x y)
          0
          s :=
    fun s =>
      (hasStrictDerivAt_interaction_zero
        mul D hD x y s).hasDerivAt
  have hdiff :
      Differentiable ℝ
        (interaction mul D x y) :=
    fun s =>
      (hder s).differentiableAt
  have hzero :
      ∀ s : ℝ,
        deriv (interaction mul D x y) s = 0 :=
    fun s =>
      (hder s).deriv
  have hconst :=
    is_const_of_deriv_eq_zero
      hdiff
      hzero
      t
      0
  simpa [interaction] using hconst

theorem flow_map_mul
    (mul : A →L[ℝ] A →L[ℝ] A)
    (D : EndA)
    (hD : IsDerivation mul D)
    (t : ℝ)
    (x y : A) :
    flow D t (mul x y) =
      mul (flow D t x) (flow D t y) := by
  have h := interaction_eq_initial mul D hD x y t
  calc flow D t (mul x y)
    = flow D t (interaction mul D x y t) := by rw [h]
    _ = mul (flow D t x) (flow D t y) := by
      unfold interaction
      rw [flow_apply_flow_neg]

noncomputable def flowLinearEquiv
    (D : EndA)
    (t : ℝ) :
    A ≃ₗ[ℝ] A where
  toFun := flow D t
  invFun := flow (-D) t
  left_inv := by
    intro x
    exact flow_neg_apply_flow D t x
  right_inv := by
    intro x
    exact flow_apply_flow_neg D t x
  map_add' := by
    intro x y
    exact (flow D t).map_add x y
  map_smul' := by
    intro r x
    exact (flow D t).map_smul r x

@[simp]
theorem flowLinearEquiv_apply
    (D : EndA)
    (t : ℝ)
    (x : A) :
    flowLinearEquiv D t x =
      flow D t x := by
  rfl

@[simp]
theorem flowLinearEquiv_symm_apply
    (D : EndA)
    (t : ℝ)
    (x : A) :
    (flowLinearEquiv D t).symm x =
      flow (-D) t x := by
  rfl

theorem exponential_derivation_is_automorphism
    (mul : A →L[ℝ] A →L[ℝ] A)
    (D : EndA)
    (hD : IsDerivation mul D)
    (t : ℝ)
    (x y : A) :
    flowLinearEquiv D t (mul x y) =
      mul
        (flowLinearEquiv D t x)
        (flowLinearEquiv D t y) := by
  exact flow_map_mul mul D hD t x y

theorem flow_add_apply
    (D : EndA)
    (s t : ℝ)
    (x : A) :
    flow D (s + t) x =
      flow D s (flow D t x) := by
  have h :=
    congrArg
      (fun T : EndA => T x)
      (flow_add D s t)
  simpa using h

theorem flowLinearEquiv_add_apply
    (D : EndA)
    (s t : ℝ)
    (x : A) :
    flowLinearEquiv D (s + t) x =
      flowLinearEquiv D s
        (flowLinearEquiv D t x) := by
  exact flow_add_apply D s t x

theorem flowLinearEquiv_neg_apply
    (D : EndA)
    (t : ℝ)
    (x : A) :
    flowLinearEquiv D (-t)
        (flowLinearEquiv D t x)
      =
    x := by
  dsimp [flowLinearEquiv]
  rw [← flow_neg_generator]
  exact flow_neg_apply_flow D t x

theorem deriv_flow_at_zero
    (D : EndA) :
    deriv (flow D) 0 = D := by
  have h : HasStrictDerivAt (flow D) (D * flow D 0) 0 := hasStrictDerivAt_flow_left D 0
  have h₁ : HasDerivAt (flow D) (D * flow D 0) 0 := h.hasDerivAt
  have h₂ : deriv (flow D) 0 = D * flow D 0 := h₁.deriv
  rw [h₂, flow_zero, mul_one]

end InfoGeometry.Lie.ContinuousDerivationExponential

end noncomputable section
