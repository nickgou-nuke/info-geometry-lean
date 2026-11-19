/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Peirce Bi-Sandwich Core Primitives

Shared noncommutative associative-ring primitives for the bi-sandwich architecture
`(P, N₊, N₋, Q₊, Q₋, V, σ, Φ, J, u₀)`:
- Defect maps `delta X = X^2 - X`, `deltaBar X = X - X^2`, and `tau X = X^3 - X`
- Peirce corner operators `Nplus P A = P * A * (1 - P)` and `Nminus P C = (1 - P) * C * P`,
  bridged to both `InfoGeometry.Core.PeirceDecomposition` and `InfoGeometry.OperatorAlgebra.PeirceSpine`
- Quadratic Casimir `casimirV = Qplus + Qminus`, split chirality `sigmaOp = Qplus - Qminus`,
  and odd generators `phiOp = Nplus + Nminus`, `jOp = Nplus - Nminus`
- Pinched projectors `P0_plus = P * (1 - V)` and `P0_minus = (1 - P) * (1 - V)`
- Explicit `Matrix (Fin 2) (Fin 2) B` non-commutativity witness showing `Qplus ≠ Qminus`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich

def delta {B : Type*} [Ring B] (X : B) : B := X ^ 2 - X
def deltaBar {B : Type*} [Ring B] (X : B) : B := X - X ^ 2
def tau {B : Type*} [Ring B] (X : B) : B := X ^ 3 - X
def comm {B : Type*} [Ring B] (X Y : B) : B := X * Y - Y * X
def anticomm {B : Type*} [Ring B] (X Y : B) : B := X * Y + Y * X

def Nplus {B : Type*} [Ring B] (P A : B) : B := P * A * (1 - P)
def Nminus {B : Type*} [Ring B] (P C : B) : B := (1 - P) * C * P
def Qplus {B : Type*} [Ring B] (P A C : B) : B := Nplus P A * Nminus P C
def Qminus {B : Type*} [Ring B] (P A C : B) : B := Nminus P C * Nplus P A
def casimirV {B : Type*} [Ring B] (P A C : B) : B := Qplus P A C + Qminus P A C
def sigmaOp {B : Type*} [Ring B] (P A C : B) : B := Qplus P A C - Qminus P A C
def phiOp {B : Type*} [Ring B] (P A C : B) : B := Nplus P A + Nminus P C
def jOp {B : Type*} [Ring B] (P A C : B) : B := Nplus P A - Nminus P C
def uZero {B : Type*} [Ring B] (P A C : B) : B := 1 - casimirV P A C + jOp P A C

def P0_plus {B : Type*} [Ring B] (P A C : B) : B := P * (1 - casimirV P A C)
def P0_minus {B : Type*} [Ring B] (P A C : B) : B := (1 - P) * (1 - casimirV P A C)

section CoreBridge

variable {B : Type*} [Ring B]

/-- Dictionary identifying every `PeirceBiSandwich` primitive with the canonical
`InfoGeometry.Core.PeirceDecomposition` and `InfoGeometry.OperatorAlgebra.PeirceSpine`
owners, together with the non-trivial complement sum law for `P0_plus + P0_minus`. -/
theorem peirceBiSandwich_spine_dictionary (P A C X : B) :
    Nplus P A = InfoGeometry.Core.PeirceDecomposition.component10 P A ∧
    Nminus P C = InfoGeometry.Core.PeirceDecomposition.component01 P C ∧
    Nplus P A = InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A ∧
    Nminus P C = InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C ∧
    phiOp P A C = InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C ∧
    jOp P A C = InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C ∧
    casimirV P A C = InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A C ∧
    sigmaOp P A C = InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P A C ∧
    2 * P - 1 = InfoGeometry.OperatorAlgebra.PeirceSpine.invS P ∧
    deltaBar X = -delta X ∧
    P0_plus P A C + P0_minus P A C = 1 - casimirV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Nplus, InfoGeometry.Core.PeirceDecomposition.component10,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent]
  · simp only [Nminus, InfoGeometry.Core.PeirceDecomposition.component01,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent]
  · simp only [Nplus, InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus]
  · simp only [Nminus, InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
  · simp only [phiOp, InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi,
      Nplus, Nminus, InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
  · simp only [jOp, InfoGeometry.OperatorAlgebra.PeirceSpine.genJ,
      Nplus, Nminus, InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
  · simp only [casimirV, Qplus, Qminus, InfoGeometry.OperatorAlgebra.PeirceSpine.genV,
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm, Nplus, Nminus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
  · simp only [sigmaOp, Qplus, Qminus, InfoGeometry.OperatorAlgebra.PeirceSpine.genSig,
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm, Nplus, Nminus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
  · dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.invS]; noncomm_ring
  · dsimp [deltaBar, delta]; noncomm_ring
  · dsimp [P0_plus, P0_minus]; noncomm_ring

theorem delta_eq_zero_iff_isIdempotent (P : B) :
    delta P = 0 ↔ IsIdempotentElem P := by
  dsimp [delta, IsIdempotentElem]
  rw [sq, sub_eq_zero]

end CoreBridge

section AlgebraicCore

variable {B : Type*} [Ring B]

lemma P_mul_P {P : B} (hP : delta P = 0) : P * P = P := by
  have h : P ^ 2 - P = 0 := hP
  calc P * P = (P ^ 2 - P) + P := by noncomm_ring
    _ = P := by rw [h, zero_add]

lemma P_mul_Nplus {P : B} (hP : delta P = 0) (A : B) : P * Nplus P A = Nplus P A := by
  dsimp [Nplus]
  calc P * (P * A * (1 - P)) = (P * P) * A * (1 - P) := by noncomm_ring
    _ = P * A * (1 - P) := by rw [P_mul_P hP]

lemma Nplus_mul_P {P : B} (hP : delta P = 0) (A : B) : Nplus P A * P = 0 := by
  dsimp [Nplus]
  calc P * A * (1 - P) * P = P * A * (P - P * P) := by noncomm_ring
    _ = 0 := by rw [P_mul_P hP]; noncomm_ring

lemma P_mul_Nminus {P : B} (hP : delta P = 0) (C : B) : P * Nminus P C = 0 := by
  dsimp [Nminus]
  calc P * ((1 - P) * C * P) = (P - P * P) * C * P := by noncomm_ring
    _ = 0 := by rw [P_mul_P hP]; noncomm_ring

lemma Nminus_mul_P {P : B} (hP : delta P = 0) (C : B) : Nminus P C * P = Nminus P C := by
  dsimp [Nminus]
  calc (1 - P) * C * P * P = (1 - P) * C * (P * P) := by noncomm_ring
    _ = (1 - P) * C * P := by rw [P_mul_P hP]

lemma Nplus_sq {P : B} (hP : delta P = 0) (A : B) : Nplus P A * Nplus P A = 0 := by
  calc Nplus P A * Nplus P A = (Nplus P A * P) * Nplus P A := by rw [mul_assoc, P_mul_Nplus hP]
    _ = 0 := by rw [Nplus_mul_P hP, zero_mul]

lemma Nminus_sq {P : B} (hP : delta P = 0) (C : B) : Nminus P C * Nminus P C = 0 := by
  calc Nminus P C * Nminus P C = Nminus P C * (P * Nminus P C) := by rw [← mul_assoc, Nminus_mul_P hP]
    _ = 0 := by rw [P_mul_Nminus hP, mul_zero]

lemma Qplus_mul_Qminus {P : B} (hP : delta P = 0) (A C : B) : Qplus P A C * Qminus P A C = 0 := by
  dsimp [Qplus, Qminus]
  calc (Nplus P A * Nminus P C) * (Nminus P C * Nplus P A)
      = Nplus P A * (Nminus P C * Nminus P C) * Nplus P A := by noncomm_ring
    _ = 0 := by rw [Nminus_sq hP]; noncomm_ring

lemma Qminus_mul_Qplus {P : B} (hP : delta P = 0) (A C : B) : Qminus P A C * Qplus P A C = 0 := by
  dsimp [Qplus, Qminus]
  calc (Nminus P C * Nplus P A) * (Nplus P A * Nminus P C)
      = Nminus P C * (Nplus P A * Nplus P A) * Nminus P C := by noncomm_ring
    _ = 0 := by rw [Nplus_sq hP]; noncomm_ring

lemma V_mul_P {P : B} (hP : delta P = 0) (A C : B) : casimirV P A C * P = Qplus P A C := by
  dsimp [casimirV, Qplus, Qminus]
  calc (Nplus P A * Nminus P C + Nminus P C * Nplus P A) * P
      = Nplus P A * (Nminus P C * P) + Nminus P C * (Nplus P A * P) := by noncomm_ring
    _ = Nplus P A * Nminus P C := by rw [Nminus_mul_P hP, Nplus_mul_P hP]; noncomm_ring

lemma P_mul_V {P : B} (hP : delta P = 0) (A C : B) : P * casimirV P A C = Qplus P A C := by
  dsimp [casimirV, Qplus, Qminus]
  calc P * (Nplus P A * Nminus P C + Nminus P C * Nplus P A)
      = (P * Nplus P A) * Nminus P C + (P * Nminus P C) * Nplus P A := by noncomm_ring
    _ = Nplus P A * Nminus P C := by rw [P_mul_Nplus hP, P_mul_Nminus hP]; noncomm_ring

lemma V_comm_Nplus {P : B} (hP : delta P = 0) (A C : B) : casimirV P A C * Nplus P A = Nplus P A * casimirV P A C := by
  dsimp [casimirV, Qplus, Qminus]
  calc (Nplus P A * Nminus P C + Nminus P C * Nplus P A) * Nplus P A
      = Nplus P A * Nminus P C * Nplus P A + Nminus P C * (Nplus P A * Nplus P A) := by noncomm_ring
    _ = (Nplus P A * Nplus P A) * Nminus P C + Nplus P A * Nminus P C * Nplus P A := by
        rw [Nplus_sq hP]; noncomm_ring
    _ = Nplus P A * (Nplus P A * Nminus P C + Nminus P C * Nplus P A) := by noncomm_ring

lemma V_comm_Nminus {P : B} (hP : delta P = 0) (A C : B) : casimirV P A C * Nminus P C = Nminus P C * casimirV P A C := by
  dsimp [casimirV, Qplus, Qminus]
  calc (Nplus P A * Nminus P C + Nminus P C * Nplus P A) * Nminus P C
      = Nplus P A * (Nminus P C * Nminus P C) + Nminus P C * Nplus P A * Nminus P C := by noncomm_ring
    _ = Nminus P C * Nplus P A * Nminus P C + (Nminus P C * Nminus P C) * Nplus P A := by
        rw [Nminus_sq hP]; noncomm_ring
    _ = Nminus P C * (Nplus P A * Nminus P C + Nminus P C * Nplus P A) := by noncomm_ring

lemma jOp_anticomm_sigmaOp {P : B} (hP : delta P = 0) (A C : B) :
    jOp P A C * sigmaOp P A C + sigmaOp P A C * jOp P A C = 0 := by
  dsimp [jOp, sigmaOp, Qplus, Qminus]
  calc (Nplus P A - Nminus P C) * (Nplus P A * Nminus P C - Nminus P C * Nplus P A) +
       (Nplus P A * Nminus P C - Nminus P C * Nplus P A) * (Nplus P A - Nminus P C)
      = (Nplus P A * Nplus P A) * Nminus P C - Nminus P C * (Nplus P A * Nplus P A) -
        Nplus P A * (Nminus P C * Nminus P C) + (Nminus P C * Nminus P C) * Nplus P A := by
        noncomm_ring
    _ = 0 := by rw [Nplus_sq hP, Nminus_sq hP]; noncomm_ring

end AlgebraicCore

/-- Explicit non-commutativity witness for `Matrix (Fin 2) (Fin 2) B` showing `Qplus ≠ Qminus`
(`Nplus P A * Nminus P C ≠ Nminus P C * Nplus P A`) over any nontrivial ring. -/
theorem peirce_biSandwich_noncommuting {B : Type*} [Ring B] [Nontrivial B] :
    ∃ A C : Matrix (Fin 2) (Fin 2) B, A * C ≠ C * A := by
  let P : Matrix (Fin 2) (Fin 2) B := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0
  let A : Matrix (Fin 2) (Fin 2) B := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let C : Matrix (Fin 2) (Fin 2) B := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨Nplus P A, Nminus P C, ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Nplus, Nminus, P, A, C, Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply,
    Fin.sum_univ_two] at h00

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich
