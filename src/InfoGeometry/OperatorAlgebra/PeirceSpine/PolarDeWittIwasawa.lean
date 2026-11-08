/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.SylvesterWignerDeWittCompleteSpine

/-!
# Peirce–Cartan polar identities and DeWitt factorization

This source-specific A84–A87 owner records the valid ring identities from the
shared AI Studio transcript.  It treats “unitary” as an exact Cartan-norm
identity, and does not assert a polar decomposition for arbitrary elements,
positivity of the Weyl scale, or a Lie-group Iwasawa theorem.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PolarDeWittIwasawa

open InfoGeometry.OperatorAlgebra.PeirceSpine.SylvesterWignerDeWittCompleteSpine

variable {B : Type*} [Ring B]

def parity (P : B) : B := P + P - 1
def complement (P : B) : B := 1 - P
def theta (P X : B) : B := parity P * X * parity P
def cliffordNorm (P X : B) : B := X * theta P X
def comm (X Y : B) : B := X * Y - Y * X
def anticomm (X Y : B) : B := X * Y + Y * X
def defect (X : B) : B := X * X - X

def nPlus (P A : B) : B := P * A * complement P
def nMinus (P C : B) : B := complement P * C * P
def phi (P A C : B) : B := nPlus P A + nMinus P C
def chirality (P A C : B) : B := nPlus P A - nMinus P C
def metric (P A C : B) : B := anticomm (nPlus P A) (nMinus P C)
def curvature (P A C : B) : B := comm (nPlus P A) (nMinus P C)
def qPlus (P A C : B) : B := nPlus P A * nMinus P C
def qMinus (P A C : B) : B := nMinus P C * nPlus P A

def chiralScale (P Lplus Lminus : B) : B :=
  P * Lplus * P + complement P * Lminus * complement P

def weylPhase (P A C : B) : B := 1 - metric P A C + chirality P A C
def weylPhaseTheta (P A C : B) : B := 1 - metric P A C - chirality P A C
def bruHat (P A C : B) : B := (1 + nPlus P A) * (1 - nMinus P C)
def bruHatInv (P A C : B) : B := (1 + nMinus P C) * (1 - nPlus P A)
def steinberg (P A C : B) : B := bruHat P A C * (1 + nPlus P A)

theorem complement_cut_laws {P : B} (hP : P * P = P) :
    complement P * complement P = complement P ∧
    P * complement P = 0 ∧ complement P * P = 0 ∧ parity P * parity P = 1 := by
  unfold complement parity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring [hP]

/-! ### A84: Cartan action and exact split-Clifford norm laws -/

theorem archetype_A84_cartan_clifford_norm
    {P : B} (hP : P * P = P) (A C : B) :
    theta P (nPlus P A) = -nPlus P A ∧
    theta P (nMinus P C) = -nMinus P C ∧
    theta P (1 + nPlus P A) = 1 - nPlus P A ∧
    theta P (1 + nMinus P C) = 1 - nMinus P C ∧
    cliffordNorm P (parity P) = 1 ∧
    cliffordNorm P (1 + nPlus P A) = 1 ∧
    cliffordNorm P (1 + nMinus P C) = 1 ∧
    cliffordNorm P (chirality P A C) = metric P A C ∧
    cliffordNorm P (phi P A C) = -metric P A C ∧
    theta P (weylPhase P A C) = weylPhaseTheta P A C ∧
    cliffordNorm P (weylPhase P A C) =
      metric P A C * metric P A C - metric P A C + 1 := by
  unfold cliffordNorm weylPhase weylPhaseTheta phi chirality metric theta parity
    nPlus nMinus complement anticomm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals peirce_nf hP

/-! ### A85: exact parity-times-scale factorizations, without a general polar claim -/

theorem archetype_A85_parity_scale_factorizations
    {P : B} (hP : P * P = P) (A C : B) :
    curvature P A C = parity P * metric P A C ∧
    curvature P A C = metric P A C * parity P ∧
    parity P * curvature P A C = metric P A C ∧
    cliffordNorm P (curvature P A C) =
      metric P A C * metric P A C ∧
    curvature P A C + chirality P A C =
      parity P * (metric P A C + phi P A C) ∧
    (curvature P A C + chirality P A C) *
      (curvature P A C + chirality P A C) = defect (metric P A C) ∧
    weylPhase P A C * theta P (weylPhase P A C) =
      1 + defect (metric P A C) := by
  unfold cliffordNorm weylPhase curvature chirality phi metric theta parity defect
    comm anticomm nPlus nMinus complement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-! ### A86: the block-diagonal scale and its exact corner actions -/

theorem archetype_A86_chiral_scale_corner_actions
    {P : B} (hP : P * P = P) (A C Lplus Lminus : B) :
    theta P (chiralScale P Lplus Lminus) = chiralScale P Lplus Lminus ∧
    chiralScale P Lplus Lminus * nPlus P A =
      P * Lplus * nPlus P A ∧
    nPlus P A * chiralScale P Lplus Lminus =
      nPlus P A * Lminus * complement P ∧
    chiralScale P Lplus Lminus * nMinus P C =
      complement P * Lminus * nMinus P C ∧
    nMinus P C * chiralScale P Lplus Lminus =
      nMinus P C * Lplus * P := by
  unfold theta parity chiralScale nPlus nMinus complement
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The chiral scale is fixed by the Cartan involution and multiplies by
composing its two Peirce blocks. The specializations at `(1,1)` and `(1,-1)`
are the identity and the parity element, respectively. -/
theorem archetype_A86_chiral_scale_theta_multiplication_and_special_values
    {P Lplus Lminus Gplus Gminus : B} (hP : P * P = P) :
    theta P (chiralScale P Lplus Lminus) = chiralScale P Lplus Lminus ∧
    chiralScale P Lplus Lminus * chiralScale P Gplus Gminus =
      chiralScale P
        ((P * Lplus * P) * (P * Gplus * P))
        (((1 - P) * Lminus * (1 - P)) * ((1 - P) * Gminus * (1 - P))) ∧
    chiralScale P 1 1 = 1 ∧
    chiralScale P 1 (-1) = parity P := by
  unfold theta parity chiralScale complement
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- For the source's specific polynomial scales `V - 1` and `V + 1`, the
rescaled nilpotent corners have anticommutator `(V² - 1) V`. This concrete
equivariance does not assert the same formula for unrelated scale elements. -/
theorem archetype_A86_chiral_scale_clifford_metric_rescaling
    {P : B} (hP : P * P = P) (A C : B) :
    anticomm
        (chiralScale P (metric P A C - 1) (metric P A C + 1) * nPlus P A)
        (chiralScale P (metric P A C - 1) (metric P A C + 1) * nMinus P C) =
      (metric P A C * metric P A C - 1) * metric P A C := by
  have hNil : nPlus P A * nPlus P A = 0 ∧ nMinus P C * nMinus P C = 0 := by
    change conePlus P A * conePlus P A = 0 ∧
      coneMinus P C * coneMinus P C = 0
    exact ⟨conePlus_mul_conePlus hP A A, coneMinus_mul_coneMinus hP C C⟩
  have hAction := archetype_A86_chiral_scale_corner_actions hP A C
    (metric P A C - 1) (metric P A C + 1)
  have hLeft : P * (metric P A C - 1) * nPlus P A =
      (metric P A C - 1) * nPlus P A := by
    unfold metric nPlus nMinus complement anticomm
    peirce_nf hP
  have hRight : complement P * (metric P A C + 1) * nMinus P C =
      (metric P A C + 1) * nMinus P C := by
    unfold metric nPlus nMinus complement anticomm
    peirce_nf hP
  have hGeneric (a b : B) (ha : a * a = 0) (hb : b * b = 0) :
      anticomm ((a * b + b * a - 1) * a) ((a * b + b * a + 1) * b) =
        ((a * b + b * a) * (a * b + b * a) - 1) * (a * b + b * a) := by
    unfold anticomm
    noncomm_ring [ha, hb]
    simp only [← mul_assoc, ha, hb, zero_mul, mul_zero, add_zero]
  rw [hAction.2.1, hAction.2.2.2.1, hLeft, hRight]
  simpa [metric, nPlus, nMinus, complement, anticomm] using
    hGeneric (nPlus P A) (nMinus P C) hNil.1 hNil.2

/-! ### A87: Bruhat, Steinberg, and DeWitt path factorizations -/

theorem archetype_A87_bruhat_and_dewitt_factorizations
    {P : B} (hP : P * P = P) (A C : B) :
    bruHat P A C = weylPhase P A C + qMinus P A C ∧
    bruHatInv P A C = weylPhaseTheta P A C + qPlus P A C ∧
    bruHat P A C * bruHatInv P A C = 1 ∧
    bruHatInv P A C * bruHat P A C = 1 ∧
    steinberg P A C =
      (weylPhase P A C + qMinus P A C) * (1 + nPlus P A) ∧
    (1 - nMinus P C) * (P + phi P A C) * (1 - nPlus P A) =
      chiralScale P 1 (-metric P A C) ∧
    P + phi P A C =
      (1 + nMinus P C) * chiralScale P 1 (-metric P A C) *
        (1 + nPlus P A) := by
  unfold steinberg bruHat bruHatInv weylPhase weylPhaseTheta
    chiralScale phi chirality metric qPlus qMinus anticomm nPlus nMinus complement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The Clifford norm of the lower DeWitt scale is the upper idempotent plus
the square of the lower return corner. This is the final operator identity
in the source A87 packet, expressed in the owner's `chiralScale` notation. -/
theorem archetype_A87_dewitt_scale_clifford_norm
    {P : B} (hP : P * P = P) (A C : B) :
    cliffordNorm P (chiralScale P 1 (-metric P A C)) =
      P + qMinus P A C * qMinus P A C := by
  unfold cliffordNorm theta parity chiralScale metric qMinus anticomm
    nPlus nMinus complement
  peirce_nf hP

/-- The Cartan conjugate of the ordered Bruhat factor and the expanded
Steinberg factorization used in the A87 source. -/
theorem archetype_A87_cartan_and_expanded_iwasawa_readout
    {P : B} (hP : P * P = P) (A C : B) :
    theta P (bruHat P A C) = bruHatInv P A C - curvature P A C ∧
    steinberg P A C =
      weylPhase P A C * dewittU P A + qMinus P A C := by
  unfold theta parity steinberg bruHat bruHatInv curvature weylPhase
    dewittU metric chirality qMinus comm anticomm nPlus nMinus complement conePlus
  exact ⟨by peirce_nf hP, by peirce_nf hP⟩

/-- Exact A87 readout for the `(1 - V, 1)` middle scale. The source's short
factorization drops the three displayed return paths; this equation retains
their ordered residuals. -/
theorem archetype_A87_chiral_scale_factorization_with_residual
    {P : B} (hP : P * P = P) (A C : B) :
    dewittL P C * chiralScale P (1 - metric P A C) 1 * dewittU P A =
      1 - qPlus P A C + phi P A C + qMinus P A C -
        nPlus P A * nMinus P C * nPlus P A -
        nMinus P C * nPlus P A * nMinus P C -
        qMinus P A C * qMinus P A C := by
  unfold dewittL dewittU chiralScale metric phi qPlus qMinus
    nPlus nMinus complement anticomm conePlus coneMinus
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine.PolarDeWittIwasawa
