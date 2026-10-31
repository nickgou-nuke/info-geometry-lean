/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Parity conjugation and the Steinberg braid

For an idempotent Peirce decomposition, parity conjugation sends each
off-diagonal corner to its negative. The palindromic three-factor braid is
therefore sent to its explicitly defined inverse. This is an algebraic
identity in an associative ring; no analytic phase-conjugation model is
assumed.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

/-- Parity conjugation sends the upper Steinberg braid to its inverse. -/
theorem parityConj_steinbergBraid (A C : B) :
    parityConj P (steinbergBraid P A C) = steinbergBraidInv P A C := by
  simp only [parityConj, steinbergBraid, steinbergBraidInv, invS,
    conePlus, coneMinus]
  peirce_nf hP

/-- Applying the braid conjugation, parity conjugation, and braid conjugation
again returns the original element. -/
theorem parityConj_steinberg_round_trip (A C X : B) :
    parityConj P
      (steinbergBraid P A C *
        parityConj P (steinbergBraid P A C * X * steinbergBraidInv P A C) *
        steinbergBraidInv P A C) = X := by
  let b := steinbergBraid P A C
  let bInv := steinbergBraidInv P A C
  have hb : parityConj P b = bInv := parityConj_steinbergBraid hP A C
  have hbInv : parityConj P bInv = b := by
    rw [← hb]
    exact (parityConj_involutive_ring_action hP b 1).1
  have hmul (Y Z : B) : parityConj P (Y * Z) = parityConj P Y * parityConj P Z :=
    (parityConj_involutive_ring_action hP Y Z).2.1
  have hbinv := steinbergBraid_mul_inv hP A C
  calc
    parityConj P (b * parityConj P (b * X * bInv) * bInv) =
        parityConj P b * parityConj P (parityConj P (b * X * bInv)) *
          parityConj P bInv := by
      rw [hmul, hmul]
    _ = bInv * (b * X * bInv) * b := by
      rw [hb, hbInv, (parityConj_involutive_ring_action hP (b * X * bInv) 1).1]
    _ = X := by
      rcases hbinv with ⟨h₁, h₂⟩
      calc
        bInv * (b * X * bInv) * b = bInv * (b * X) * (bInv * b) := by
          noncomm_ring
        _ = bInv * (b * X) := by rw [h₂, mul_one]
        _ = (bInv * b) * X := by rw [← mul_assoc]
        _ = X := by rw [h₂, one_mul]

/-- Parity conjugation sends the dual Steinberg braid to its inverse and maps
each displayed Bruhat factor to its one-factor inverse (`A72`–`A73`). The
factor order is retained, so this statement does not identify the image of a
two-factor product with the group inverse of that product. -/
theorem parityConj_steinbergBraidDual_and_bruhat_factors (A C : B) :
    parityConj P (steinbergBraidDual P A C) = steinbergBraidDualInv P A C ∧
    parityConj P ((1 + conePlus P A) * (1 - coneMinus P C)) =
      (1 - conePlus P A) * (1 + coneMinus P C) ∧
    parityConj P ((1 + coneMinus P C) * (1 - conePlus P A)) =
      (1 - coneMinus P C) * (1 + conePlus P A) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [parityConj, steinbergBraidDual, steinbergBraidDualInv,
      invS, conePlus, coneMinus]; peirce_nf hP)

/-- Unipotent single-pass and double-pass conjugation of `genPhi`, parity-conjugate
round-trip cancellation for upper and lower unipotent shears, and invariance of
`sandwichSame` under even `genV`/`genSig` shifts (`A71`). -/
theorem unipotentPlus_double_pass_and_parityConj_round_trip (A C X : B) :
    (1 + conePlus P A) * genPhi P A C * (1 - conePlus P A) =
      genPhi P A C + genSig P A C -
        conePlus P A * coneMinus P C * conePlus P A ∧
    (1 + conePlus P A) *
        ((1 + conePlus P A) * genPhi P A C * (1 - conePlus P A)) *
        (1 - conePlus P A) =
      genPhi P A C + (2 : ℤ) • genSig P A C -
        (4 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A) ∧
    parityConj P
      ((1 + conePlus P A) *
        parityConj P ((1 + conePlus P A) * X * (1 - conePlus P A)) *
        (1 - conePlus P A)) = X ∧
    parityConj P
      ((1 + coneMinus P C) *
        parityConj P ((1 + coneMinus P C) * X * (1 - coneMinus P C)) *
        (1 - coneMinus P C)) = X ∧
    sandwichSame P A C (X + genV P A C + genSig P A C) =
      sandwichSame P A C X := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [parityConj, sandwichSame, invS]); peirce_nf hP)

end InfoGeometry.OperatorAlgebra.PeirceSpine
