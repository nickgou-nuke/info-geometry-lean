/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ReversibleGateVariation
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Native differential of a reversible Peirce gate

The three independent arguments are the two ambient gate parameters and the
input. The cut `P` is fixed. The derivative is an actual Fréchet derivative
on a normed noncommutative algebra. Idempotence is needed only when rewriting
it using the output and the reconstructed midpoint.
-/

noncomputable section

namespace InfoGeometry.Analysis.PeirceReversibleDifferential

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]

/-- The full differential in the independent directions `(dA, dC, dx)`. -/
def epistemicCornerShearActionDifferential (P A C x : B) :
    B × B × B →L[𝕜] B :=
  let plus := (ContinuousLinearMap.mulLeftRight 𝕜 B P (1 - P)).comp
    (ContinuousLinearMap.fst 𝕜 B (B × B))
  let minus := (ContinuousLinearMap.mulLeftRight 𝕜 B (1 - P) P).comp
    ((ContinuousLinearMap.fst 𝕜 B B).comp (ContinuousLinearMap.snd 𝕜 B (B × B)))
  ((ContinuousLinearMap.mul 𝕜 B).flip x).comp
    (((ContinuousLinearMap.mul 𝕜 B).flip (1 + coneMinus P C)).comp plus +
      (ContinuousLinearMap.mul 𝕜 B (1 + conePlus P A)).comp minus) +
    (ContinuousLinearMap.mul 𝕜 B (epistemicCornerShear P A C)).comp
      ((ContinuousLinearMap.snd 𝕜 B B).comp (ContinuousLinearMap.snd 𝕜 B (B × B)))

@[simp] theorem epistemicCornerShearActionDifferential_apply
    (P A C x dA dC dx : B) :
    epistemicCornerShearActionDifferential 𝕜 P A C x (dA, dC, dx) =
      (conePlus P dA * (1 + coneMinus P C) +
        (1 + conePlus P A) * coneMinus P dC) * x +
        epistemicCornerShear P A C * dx := rfl

/-- Native noncommutative product rule, with no constraint on the parameters. -/
theorem hasFDerivAt_epistemicCornerShear_action (P A C x : B) :
    HasFDerivAt
      (fun z : B × B × B => epistemicCornerShear P z.1 z.2.1 * z.2.2)
      (epistemicCornerShearActionDifferential 𝕜 P A C x) (A, C, x) := by
  let plus := (ContinuousLinearMap.mulLeftRight 𝕜 B P (1 - P)).comp
    (ContinuousLinearMap.fst 𝕜 B (B × B))
  let minus := (ContinuousLinearMap.mulLeftRight 𝕜 B (1 - P) P).comp
    ((ContinuousLinearMap.fst 𝕜 B B).comp (ContinuousLinearMap.snd 𝕜 B (B × B)))
  let input := (ContinuousLinearMap.snd 𝕜 B B).comp
    (ContinuousLinearMap.snd 𝕜 B (B × B))
  have hp : HasFDerivAt (fun z : B × B × B => conePlus P z.1)
      plus (A, C, x) := plus.hasFDerivAt
  have hm : HasFDerivAt (fun z : B × B × B => coneMinus P z.2.1)
      minus (A, C, x) := minus.hasFDerivAt
  have hx : HasFDerivAt (fun z : B × B × B => z.2.2)
      input (A, C, x) := input.hasFDerivAt
  have h := ((hp.const_add (1 : B)).mul' (hm.const_add (1 : B))).mul' hx
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro d
  simp only [epistemicCornerShearActionDifferential, plus, minus, input,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_apply,
    op_smul_eq_mul, smul_eq_mul, Pi.mul_apply, conePlus, coneMinus, epistemicCornerShear]
  noncomm_ring

/-- The native derivative evaluated on an arbitrary parameter/input direction. -/
theorem fderiv_epistemicCornerShear_action_apply (P A C x dA dC dx : B) :
    fderiv 𝕜
      (fun z : B × B × B => epistemicCornerShear P z.1 z.2.1 * z.2.2)
      (A, C, x) (dA, dC, dx) =
      (conePlus P dA * (1 + coneMinus P C) +
        (1 + conePlus P A) * coneMinus P dC) * x +
        epistemicCornerShear P A C * dx := by
  rw [(hasFDerivAt_epistemicCornerShear_action 𝕜 P A C x).fderiv]
  rfl

/-- Output coordinates remove the explicit lower-gate coefficient from the
parameter terms. The output itself still depends on both gate parameters. -/
theorem fderiv_epistemicCornerShear_action_output {P : B} (hP : P * P = P)
    (A C x dA dC dx : B) :
    fderiv 𝕜
      (fun z : B × B × B => epistemicCornerShear P z.1 z.2.1 * z.2.2)
      (A, C, x) (dA, dC, dx) =
      conePlus P dA * (epistemicCornerShear P A C * x) +
        (1 + conePlus P A) * coneMinus P dC *
          ((1 - conePlus P A) * (epistemicCornerShear P A C * x)) +
        epistemicCornerShear P A C * dx := by
  rw [fderiv_epistemicCornerShear_action_apply]
  exact epistemicCornerShear_outputVariation hP A C dA dC x dx

end InfoGeometry.Analysis.PeirceReversibleDifferential
