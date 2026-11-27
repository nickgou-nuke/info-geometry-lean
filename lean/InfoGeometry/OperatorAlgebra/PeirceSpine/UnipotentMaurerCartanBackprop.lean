/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Square-zero Maurer–Cartan identity for paired Peirce gates

This file proves a ring-level first-variation identity for the paired gate
`(1 + N₊)(1 + N₋)`, together with an exact state reconstruction theorem. It
does not define a derivative, loss, trace pairing, parameter gradient, or
neural-network memory bound.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

section PairedGate

variable {B : Type*} [Ring B]

/-- Product-rule variation of the paired unipotent Gaussian
`(1 + N₊)(1 + N₋)` in two independent directions. -/
def pairedGateVariation (Np Nm dNp dNm : B) : B :=
  dNp * (1 + Nm) + (1 + Np) * dNm

/-- Exact right Maurer–Cartan expression for the product-rule variation of
two square-zero gates. The corner hypotheses `dNp * Np = 0` and
`dNm * Nm = 0` remove the two redundant terms. -/
theorem pairedGate_rightMaurerCartan
    (Np Nm dNp dNm : B)
    (hNp : Np * Np = 0) (hNm : Nm * Nm = 0)
    (hdNp : dNp * Np = 0) (hdNm : dNm * Nm = 0) :
    pairedGateVariation Np Nm dNp dNm *
        ((1 - Nm) * (1 - Np)) =
      dNp + (1 + Np) * dNm * (1 - Np) := by
  have hminus : (1 + Nm) * (1 - Nm) = 1 := by
    calc
      (1 + Nm) * (1 - Nm) = 1 - Nm * Nm := by noncomm_ring
      _ = 1 := by rw [hNm]; simp
  have hdplus : dNp * (1 - Np) = dNp := by
    calc
      dNp * (1 - Np) = dNp - dNp * Np := by noncomm_ring
      _ = dNp := by rw [hdNp, sub_zero]
  have hdminus : dNm * (1 - Nm) = dNm := by
    calc
      dNm * (1 - Nm) = dNm - dNm * Nm := by noncomm_ring
      _ = dNm := by rw [hdNm, sub_zero]
  unfold pairedGateVariation
  calc
    (dNp * (1 + Nm) + (1 + Np) * dNm) * ((1 - Nm) * (1 - Np)) =
        dNp * ((1 + Nm) * (1 - Nm)) * (1 - Np) +
          (1 + Np) * (dNm * (1 - Nm)) * (1 - Np) := by noncomm_ring
    _ = dNp * (1 - Np) + (1 + Np) * dNm * (1 - Np) := by rw [hminus, mul_one, hdminus]
    _ = dNp + (1 + Np) * dNm * (1 - Np) := by rw [hdplus]

/-- Peirce specialization: both gate directions and their tangent directions
lie in the corresponding square-zero corners, so the generic right
Maurer–Cartan identity applies without extra vanishing assumptions. -/
theorem peirce_attention_rightMaurerCartan
    {P A C dA dC : B} (hP : P * P = P) :
    pairedGateVariation (conePlus P A) (coneMinus P C)
        (conePlus P dA) (coneMinus P dC) *
        ((1 - coneMinus P C) * (1 - conePlus P A)) =
      conePlus P dA +
        (1 + conePlus P A) * coneMinus P dC * (1 - conePlus P A) := by
  apply pairedGate_rightMaurerCartan
  · exact conePlus_mul_conePlus hP A A
  · exact coneMinus_mul_coneMinus hP C C
  · exact conePlus_mul_conePlus hP dA A
  · exact coneMinus_mul_coneMinus hP dC C

/-- Exact input reconstruction for the paired Peirce gate. `Xmid` is the
state after the lower gate and `Xout` after both gates. -/
theorem peirce_attention_state_reconstruction
    {P A C X : B} (hP : P * P = P) :
    let Np := conePlus P A
    let Nm := coneMinus P C
    let Xout := (1 + Np) * ((1 + Nm) * X)
    (1 - Np) * Xout = (1 + Nm) * X ∧
      (1 - Nm) * ((1 - Np) * Xout) = X := by
  dsimp
  have hNp := conePlus_mul_conePlus hP A A
  have hNm := coneMinus_mul_coneMinus hP C C
  have hMid :
      (1 - conePlus P A) * ((1 + conePlus P A) * ((1 + coneMinus P C) * X)) =
        (1 + coneMinus P C) * X := by
    calc
      (1 - conePlus P A) * ((1 + conePlus P A) * ((1 + coneMinus P C) * X)) =
          ((1 - conePlus P A) * (1 + conePlus P A)) * ((1 + coneMinus P C) * X) := by
            rw [mul_assoc]
      _ = (1 - conePlus P A * conePlus P A) * ((1 + coneMinus P C) * X) := by noncomm_ring
      _ = (1 + coneMinus P C) * X := by rw [hNp]; simp
  constructor
  · exact hMid
  · calc
      (1 - coneMinus P C) *
          ((1 - conePlus P A) * ((1 + conePlus P A) * ((1 + coneMinus P C) * X))) =
          (1 - coneMinus P C) * ((1 + coneMinus P C) * X) := by
            exact congrArg (fun Y => (1 - coneMinus P C) * Y) hMid
      _ = ((1 - coneMinus P C) * (1 + coneMinus P C)) * X := by rw [mul_assoc]
      _ = (1 - coneMinus P C * coneMinus P C) * X := by noncomm_ring
      _ = X := by rw [hNm]; simp

end PairedGate

end InfoGeometry.OperatorAlgebra.PeirceSpine
