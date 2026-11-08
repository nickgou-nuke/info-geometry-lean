/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure

/-!
# Cl(5,5) CAR modes as Peirce superderivation generators

The causal chain proved here is CAR pair → Peirce idempotent and its two
directed corners → Tetraktys unit mass → Peirce superderivation identities,
with the same creation/annihilation modes in the existing five-grade spaces.
This is a specialization on the native Clifford carrier, not a new Fock or
matrix model.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl55PeirceSuperderivationBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- The occupied Peirce idempotent associated to one native Cl(5,5) CAR mode. -/
def carModePeirce (i : Fin 5) : Cl55 := creation55 i * annihilation55 i

/-- The CAR relation makes the occupied mode an idempotent. -/
theorem carModePeirce_idempotent (i : Fin 5) :
    carModePeirce i * carModePeirce i = carModePeirce i := by
  let c := creation55 i
  let a := annihilation55 i
  have hc : c * c = 0 := creation55_sq i
  have ha : a * a = 0 := annihilation55_sq i
  have hcar : a * c + c * a = 1 := annihilation55_creation55_anticommutator i
  have hca : c * a = 1 - a * c := by
    rw [← hcar]
    noncomm_ring
  change (c * a) * (c * a) = c * a
  calc
    (c * a) * (c * a) = c * (a * c) * a := by noncomm_ring
    _ = c * (1 - c * a) * a := by rw [← hcar]; noncomm_ring
    _ = c * a := by
      have hzero : c * (c * a) = 0 := by
        calc
          c * (c * a) = (c * c) * a := by rw [← mul_assoc]
          _ = 0 := by rw [hc, zero_mul]
      calc
        c * (1 - c * a) * a = c * a - c * (c * a) * a := by
          noncomm_ring
        _ = c * a := by rw [hzero]; simp

/-- The mode CAR pair is exactly the pair of directed Peirce corners of its
occupied projector. -/
theorem carModePeirce_recovers_CAR_corners (i : Fin 5) :
    conePlus (carModePeirce i) (creation55 i) = creation55 i ∧
    coneMinus (carModePeirce i) (annihilation55 i) = annihilation55 i := by
  let c := creation55 i
  let a := annihilation55 i
  have hc : c * c = 0 := creation55_sq i
  have ha : a * a = 0 := annihilation55_sq i
  have hcar : a * c + c * a = 1 := annihilation55_creation55_anticommutator i
  have hac : a * c = 1 - c * a := by
    rw [← hcar]
    noncomm_ring
  have hca : c * a = 1 - a * c := by
    rw [← hcar]
    noncomm_ring
  have hOneMinusCA : 1 - c * a = a * c := by
    rw [← hcar]
    noncomm_ring
  have hcac : c * a * c = c := by
    calc
      c * a * c = (1 - a * c) * c := by rw [hca]
      _ = c := by rw [sub_mul, one_mul, mul_assoc a c c, hc, mul_zero, sub_zero]
  have haca : a * c * a = a := by
    calc
      a * c * a = (1 - c * a) * a := by rw [hac]
      _ = a := by rw [sub_mul, one_mul, mul_assoc c a a, ha, mul_zero, sub_zero]
  constructor
  · change c * a * c * (1 - c * a) = c
    rw [hcac, hOneMinusCA]
    calc
      c * (a * c) = c * a * c := by noncomm_ring
      _ = c := hcac
  · change (1 - c * a) * a * (c * a) = a
    rw [hOneMinusCA]
    calc
      (a * c) * a * (c * a) = a * (c * a) := by rw [haca]
      _ = a * c * a := by noncomm_ring
      _ = a := haca

/-- The CAR-derived Peirce cut has unit Tetraktys mass and its chiral
superderivations act on the two CAR generators by the exact CAR contraction. -/
theorem carMode_peirce_tetraktys_superderivation_and_five_grade
    (i : Fin 5) (X : Cl55) :
    let P := carModePeirce i
    P * P = P ∧
    conePlus P (creation55 i) = creation55 i ∧
    coneMinus P (annihilation55 i) = annihilation55 i ∧
    genPhi P (creation55 i) (annihilation55 i) = creation55 i + annihilation55 i ∧
    genJ P (creation55 i) (annihilation55 i) = creation55 i - annihilation55 i ∧
    genV P (creation55 i) (annihilation55 i) = 1 ∧
    superDerivPhi P (creation55 i) (annihilation55 i)
      (superDerivPhi P (creation55 i) (annihilation55 i) X) = 0 ∧
    superDerivPlus P (creation55 i) (annihilation55 i) = 1 ∧
    superDerivMinus P (annihilation55 i) (creation55 i) = 1 ∧
    creation55 i ∈ cl55GradeSubmodule 1 ∧
    annihilation55 i ∈ cl55GradeSubmodule (-1) := by
  intro P
  have hP : P * P = P := carModePeirce_idempotent i
  rcases carModePeirce_recovers_CAR_corners i with ⟨hPlus, hMinus⟩
  have hA28 := archetype_A28_graded_derivations hP
    (creation55 i) (annihilation55 i) X (annihilation55 i)
  rcases hA28 with
    ⟨_, _, _, _, _, _, _, hPhiSq, _, _, _, hPlusContract, hMinusContract, _, _⟩
  have hV : genV P (creation55 i) (annihilation55 i) = 1 := by
    rw [genV, anticomm, hPlus, hMinus]
    calc
      creation55 i * annihilation55 i + annihilation55 i * creation55 i =
          annihilation55 i * creation55 i + creation55 i * annihilation55 i := by abel
      _ = 1 := annihilation55_creation55_anticommutator i
  have hPhiSq' : superDerivPhi P (creation55 i) (annihilation55 i)
      (superDerivPhi P (creation55 i) (annihilation55 i) X) = 0 := by
    rw [hPhiSq]
    change PeirceSpine.comm (genV P (creation55 i) (annihilation55 i)) X = 0
    rw [hV]
    simp [PeirceSpine.comm]
  have hPlusContract' : superDerivPlus P (creation55 i) (annihilation55 i) = 1 := by
    calc
      superDerivPlus P (creation55 i) (annihilation55 i) =
          superDerivPlus P (creation55 i) (coneMinus P (annihilation55 i)) := by rw [hMinus]
      _ = genV P (creation55 i) (annihilation55 i) := hPlusContract
      _ = 1 := hV
  have hMinusContract' : superDerivMinus P (annihilation55 i) (creation55 i) = 1 := by
    calc
      superDerivMinus P (annihilation55 i) (creation55 i) =
          superDerivMinus P (annihilation55 i) (conePlus P (creation55 i)) := by rw [hPlus]
      _ = genV P (creation55 i) (annihilation55 i) := hMinusContract
      _ = 1 := hV
  refine ⟨hP, hPlus, hMinus, ?_, ?_, hV, hPhiSq', ?_, ?_,
    creation55_mem_grade_one i, annihilation55_mem_grade_neg_one i⟩
  · rw [genPhi, hPlus, hMinus]
  · rw [genJ, hPlus, hMinus]
  · exact hPlusContract'
  · exact hMinusContract'

end InfoGeometry.OperatorAlgebra.Cl55PeirceSuperderivationBridge

end
