/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.OperatorValuedJonesProduct
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Operator-valued causal coordinates in the Peirce tetraktys

This module makes one carrier bridge explicit.  The coefficients are
endomorphisms of an arbitrary complex module `W`, the sheet algebra is
`M₂(Endℂ(W))`, and its Peirce generators are computed from the existing
causal-coordinate reconstruction.  Thus the products in `V` and `Σ` retain
their order when the operator coefficients do not commute.

The results here are finite associative operator-algebra identities.  They do
not assert a Yang–Mills bound, a Zorn-algebra embedding, or an infinite-colimit
theorem.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TetraktysZornYangMillsBridge

open InfoGeometry.Clifford
open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev Operator (W : Type*) [AddCommGroup W] [Module ℂ W] := Module.End ℂ W
abbrev SheetAlgebra (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  Matrix (Fin 2) (Fin 2) (Operator W)

/-- The first-sheet projection in the full operator matrix algebra. -/
def firstSheetProjection (W : Type*) [AddCommGroup W] [Module ℂ W] :
    SheetAlgebra W := !![1, 0; 0, 0]

theorem firstSheetProjection_idempotent :
    firstSheetProjection (W := W) * firstSheetProjection (W := W) =
      firstSheetProjection (W := W) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [firstSheetProjection]

/-- The upper-right operator coefficient in the causal reconstruction. -/
def causalUpperCoefficient (x : CausalOperatorCoordinates (Operator W)) : Operator W :=
  x.exchange - Complex.I • x.circular

/-- The lower-left operator coefficient in the causal reconstruction. -/
def causalLowerCoefficient (x : CausalOperatorCoordinates (Operator W)) : Operator W :=
  x.exchange + Complex.I • x.circular

/-- The outgoing Peirce corner is exactly the upper-right causal operator. -/
theorem conePlus_causal_reconstruction
    (x : CausalOperatorCoordinates (Operator W)) :
    conePlus (firstSheetProjection (W := W)) (reconstruct_causal x) =
      !![0, causalUpperCoefficient x; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conePlus, firstSheetProjection, reconstruct_causal,
      causalUpperCoefficient, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.one_apply]

/-- The incoming Peirce corner is exactly the lower-left causal operator. -/
theorem coneMinus_causal_reconstruction
    (x : CausalOperatorCoordinates (Operator W)) :
    coneMinus (firstSheetProjection (W := W)) (reconstruct_causal x) =
      !![0, 0; causalLowerCoefficient x, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coneMinus, firstSheetProjection, reconstruct_causal,
      causalLowerCoefficient, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.one_apply]

/-- The complete tetraktys multiplication table in the operator-valued sheet
coordinates.  The diagonal entries of `V` and `Σ` preserve the two product
orders; no commutation hypothesis on `W`'s endomorphisms is used. -/
theorem tetraktys_causal_reconstruction
    (x y : CausalOperatorCoordinates (Operator W)) :
    genPhi (firstSheetProjection (W := W)) (reconstruct_causal x)
        (reconstruct_causal y) =
      !![0, causalUpperCoefficient x; causalLowerCoefficient y, 0] ∧
    genJ (firstSheetProjection (W := W)) (reconstruct_causal x)
        (reconstruct_causal y) =
      !![0, causalUpperCoefficient x; -(causalLowerCoefficient y), 0] ∧
    genV (firstSheetProjection (W := W)) (reconstruct_causal x)
        (reconstruct_causal y) =
      !![causalUpperCoefficient x * causalLowerCoefficient y, 0;
        0, causalLowerCoefficient y * causalUpperCoefficient x] ∧
    genSig (firstSheetProjection (W := W)) (reconstruct_causal x)
        (reconstruct_causal y) =
      !![causalUpperCoefficient x * causalLowerCoefficient y, 0;
        0, -(causalLowerCoefficient y * causalUpperCoefficient x)] := by
  have hP := firstSheetProjection_idempotent (W := W)
  have hPlus := conePlus_causal_reconstruction (W := W)
  have hMinus := coneMinus_causal_reconstruction (W := W)
  constructor
  · simp only [genPhi, hPlus x, hMinus y]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  constructor
  · simp only [genJ, hPlus x, hMinus y]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  constructor
  · simp only [genV, anticomm, hPlus x, hMinus y]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simp only [genSig, PeirceSpine.comm, hPlus x, hMinus y]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end InfoGeometry.OperatorAlgebra.TetraktysZornYangMillsBridge
