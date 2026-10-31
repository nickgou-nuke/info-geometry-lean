/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DirectedFlowMagneticResolvent

/-!
# Operator identities for measure-weighted reversibility

This module formalizes algebraic identities motivated by parametrized reversible
operators. The parameter `M` is an arbitrary self-adjoint operator; no positivity
or probability-measure interpretation is assumed in a general star-ring.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B]

/-- Self-adjoint flux associated with an operator parameter and a directed operator. -/
def parpicFlux (M W : B) : B := M * W + star W * M

/-- Skew-adjoint circulation associated with an operator parameter and a directed operator. -/
def parpicCirc (M W : B) : B := M * W - star W * M

/-- Reversible operator obtained by left normalization of the flux. -/
def parpicOp (piInv M W : B) : B := piInv * parpicFlux M W

/-- Self-adjointly sandwiched flux. The parameter is not assumed to be related to a
square root or inverse square root of another operator. -/
def parpicSymKernel (piHalfInv M W : B) : B :=
  piHalfInv * parpicFlux M W * piHalfInv

/-- Power iteration, with zeroth iterate equal to the identity. -/
def parpicPowerIter (n : ℕ) (T : B) : B := T ^ n

/-- Generalized self-adjoint measure-parameter Laplacian. -/
def parpicLaplacian (pi M W : B) : B := pi - parpicFlux M W

/-- Flux and circulation reconstruct twice the ordered weighted edge operator. -/
theorem parpicFlux_add_circ (M W : B) :
    parpicFlux M W + parpicCirc M W = (2 : ℤ) • (M * W) := by
  unfold parpicFlux parpicCirc
  noncomm_ring

/-- The weighted flux is self-adjoint when its left parameter is self-adjoint. -/
theorem star_parpicFlux {M : B} (hM : star M = M) (W : B) :
    star (parpicFlux M W) = parpicFlux M W := by
  unfold parpicFlux
  rw [star_add, star_mul, star_mul, star_star, hM, add_comm]

/-- The weighted circulation is skew-adjoint when its left parameter is self-adjoint. -/
theorem star_parpicCirc {M : B} (hM : star M = M) (W : B) :
    star (parpicCirc M W) = -parpicCirc M W := by
  unfold parpicCirc
  rw [star_sub, star_mul, star_mul, star_star, hM, neg_sub]

/-- A two-sided inverse hypothesis follows from a self-adjoint left inverse. -/
theorem parpic_inverse_right {pi piInv : B}
    (hPi : star pi = pi) (hPiInv : star piInv = piInv) (hInv : pi * piInv = 1) :
    piInv * pi = 1 := by
  have h := congrArg star hInv
  simpa [hPi, hPiInv] using h

/-- The normalized flux obeys detailed balance under the stated inverse hypotheses. -/
theorem parpicOp_detailed_balance
    {M pi piInv : B} (hM : star M = M) (hPi : star pi = pi)
    (hPiInv : star piInv = piInv) (hInv : pi * piInv = 1) (W : B) :
    pi * parpicOp piInv M W = parpicFlux M W ∧
    pi * parpicOp piInv M W = star (parpicOp piInv M W) * pi := by
  have hFlux := star_parpicFlux hM W
  have hInvRight := parpic_inverse_right hPi hPiInv hInv
  constructor
  · unfold parpicOp
    rw [← mul_assoc, hInv, one_mul]
  · rw [show pi * parpicOp piInv M W = parpicFlux M W from by
      unfold parpicOp; rw [← mul_assoc, hInv, one_mul]]
    unfold parpicOp
    rw [star_mul, hFlux, hPiInv, mul_assoc, hInvRight, mul_one]

/-- Reversibility is preserved under every natural-number power. -/
theorem parpicPowerIter_detailed_balance {pi T : B}
    (hRev : pi * T = star T * pi) (n : ℕ) :
    pi * parpicPowerIter n T = star (parpicPowerIter n T) * pi := by
  have hIter : ∀ n : ℕ, pi * T ^ n = (star T) ^ n * pi := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← mul_assoc, ih, mul_assoc, hRev, ← mul_assoc, pow_succ]
  simpa [parpicPowerIter, star_pow] using hIter n

/-- The normalized similarity kernel is self-adjoint. -/
theorem star_parpicSymKernel {M piHalfInv : B}
    (hM : star M = M) (hPiHalf : star piHalfInv = piHalfInv) (W : B) :
    star (parpicSymKernel piHalfInv M W) = parpicSymKernel piHalfInv M W := by
  unfold parpicSymKernel
  calc
    star (piHalfInv * parpicFlux M W * piHalfInv) =
        star piHalfInv * (star (parpicFlux M W) * star piHalfInv) := by
          rw [star_mul, star_mul]
    _ = piHalfInv * (parpicFlux M W * piHalfInv) := by
          rw [hPiHalf, star_parpicFlux hM]
    _ = piHalfInv * parpicFlux M W * piHalfInv := by rw [mul_assoc]

/-- The generalized measure-parameter Laplacian is self-adjoint. -/
theorem star_parpicLaplacian {pi M : B}
    (hPi : star pi = pi) (hM : star M = M) (W : B) :
    star (parpicLaplacian pi M W) = parpicLaplacian pi M W := by
  unfold parpicLaplacian
  rw [star_sub, hPi, star_parpicFlux hM]

/-- Uniform, source, and sink operator parameters recover the corresponding Peirce fluxes;
the grading parameter recovers the existing self-adjoint twisted adjacency. -/
theorem parpicFlux_peirce_specializations
    {P : B} (hP : P * P = P) (hPs : star P = P) (A : B) :
    parpicFlux 1 (conePlus P A) = genPhi P A (star A) ∧
    parpicCirc 1 (conePlus P A) = genJ P A (star A) ∧
    parpicFlux (invS P) (conePlus P A) = gradingTwistedAdj P A ∧
    parpicFlux (invS P) (conePlus P A) * parpicFlux (invS P) (conePlus P A) =
      genV P A (star A) ∧
    parpicFlux P (conePlus P A) = genPhi P A (star A) ∧
    parpicFlux (1 - P) (conePlus P A) = 0 := by
  have hStarCone := star_conePlus (P := P) hPs A
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold parpicFlux genPhi
    rw [one_mul, mul_one, hStarCone]
  · unfold parpicCirc genJ
    rw [one_mul, mul_one, hStarCone]
  · rfl
  · rw [show parpicFlux (invS P) (conePlus P A) = gradingTwistedAdj P A from rfl]
    exact gradingTwistedAdj_sq hPs hP A
  · unfold parpicFlux genPhi
    rw [hStarCone]
    peirce_nf hP
  · unfold parpicFlux
    rw [hStarCone]
    peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
