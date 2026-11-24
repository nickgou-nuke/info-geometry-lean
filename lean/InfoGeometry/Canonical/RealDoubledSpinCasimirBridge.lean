/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.RealDiracLorentzBridge
import InfoGeometry.Algebra.AssociativeNambuPeirceBridge
import Mathlib.Data.Matrix.Block

/-!
# Doubled real spin blocks, projected Casimirs, and associative alternation

The carrier is the native real matrix algebra on `Fin 4 ⊕ Fin 4`.
The same rotation acts on both summands, while the boost changes sign.
With the shared square-minus-one phase, the two combinations are exactly
the lower and upper rotation blocks. They commute across the two sectors,
and the exchange matrix interchanges their quadratic Casimir readouts.

These are two commuting rotation triples in a larger real endomorphism
algebra. Multiplication by the shared phase is an operator action, not a
real scalar coefficient in the six-dimensional Lorentz span. No real Lie
algebra splitting of `so(3,1)` into two compact factors is asserted.

The second Lorentz quadratic readout has the sign
`C₂ = -(3/4) Γ Ω = -Ω (C_A - C_B)`. The final identities specialize the
existing associative Nambu alternator to these actual spin operators.
They assert no Filippov fundamental identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealDoubledSpinCasimirBridge

open scoped Matrix BigOperators
open InfoGeometry.Canonical.RealPauliPfaffianKernel
open InfoGeometry.Canonical.RealDiracLorentzBridge
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge
open InfoGeometry.Algebra.NoncommutativeZornNambu

abbrev Matrix8 := Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ

def sharedPhase : Matrix8 := Matrix.fromBlocks realPhaseAxis 0 0 realPhaseAxis

def cut : Matrix8 := Matrix.fromBlocks (1 : Matrix4) 0 0 (-1 : Matrix4)

def mirror : Matrix8 := Matrix.fromBlocks (0 : Matrix4) 1 1 (0 : Matrix4)

def sectorPlus : Matrix8 := Matrix.fromBlocks (1 : Matrix4) 0 0 (0 : Matrix4)

def sectorMinus : Matrix8 := Matrix.fromBlocks (0 : Matrix4) 0 0 (1 : Matrix4)

def doubledRotation (a : Vector3) : Matrix8 :=
  Matrix.fromBlocks (rotation a) 0 0 (rotation a)

def doubledBoost (a : Vector3) : Matrix8 :=
  Matrix.fromBlocks (boost a) 0 0 (-boost a)

def chiralA (a : Vector3) : Matrix8 :=
  (1 / 2 : ℝ) • (doubledRotation a + sharedPhase * doubledBoost a)

def chiralB (a : Vector3) : Matrix8 :=
  (1 / 2 : ℝ) • (doubledRotation a - sharedPhase * doubledBoost a)

theorem sharedPhase_sq : sharedPhase * sharedPhase = -(1 : Matrix8) := by
  simp only [sharedPhase, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
    add_zero, zero_add, realPhaseAxis_sq]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem cut_sq : cut * cut = (1 : Matrix8) := by
  simp [cut, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem mirror_sq : mirror * mirror = (1 : Matrix8) := by
  simp [mirror, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/-- The sector distinction and exchange are concrete noncommuting operators. -/
theorem cut_mirror_noncommute : cut * mirror ≠ mirror * cut := by
  intro h
  have h01 := congrArg
    (fun M : Matrix8 => M (Sum.inl (0 : Fin 4)) (Sum.inr (0 : Fin 4))) h
  norm_num [cut, mirror, Matrix.fromBlocks_multiply] at h01

theorem chiralA_eq_lower (a : Vector3) :
    chiralA a = Matrix.fromBlocks (0 : Matrix4) 0 0 (rotation a) := by
  simp [chiralA, doubledRotation, sharedPhase, doubledBoost,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.fromBlocks_smul,
    phase_mul_boost]
  module

theorem chiralB_eq_upper (a : Vector3) :
    chiralB a = Matrix.fromBlocks (rotation a) 0 0 (0 : Matrix4) := by
  simp [chiralB, doubledRotation, sharedPhase, doubledBoost, sub_eq_add_neg,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_smul, phase_mul_boost]
  module

/-- Full cross-product bracket law on the lower rotation sector. -/
theorem chiralA_commutator (a b : Vector3) :
    chiralA a * chiralA b - chiralA b * chiralA a = chiralA (a ⨯₃ b) := by
  simpa [chiralA_eq_lower, Matrix.fromBlocks_multiply, sub_eq_add_neg,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_add] using
      congrArg (fun M : Matrix4 => (Matrix.fromBlocks (0 : Matrix4) 0 0 M : Matrix8))
        (rotation_comm_rotation a b)

theorem chiralB_commutator (a b : Vector3) :
    chiralB a * chiralB b - chiralB b * chiralB a = chiralB (a ⨯₃ b) := by
  simpa [chiralB_eq_upper, Matrix.fromBlocks_multiply, sub_eq_add_neg,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_add] using
      congrArg (fun M : Matrix4 => (Matrix.fromBlocks M 0 0 (0 : Matrix4) : Matrix8))
        (rotation_comm_rotation a b)

/-- Every lower-sector rotation commutes with every upper-sector rotation. -/
theorem chiralA_chiralB_commute (a b : Vector3) :
    chiralA a * chiralB b - chiralB b * chiralA a = 0 := by
  simp [chiralA_eq_lower, chiralB_eq_upper, Matrix.fromBlocks_multiply]

theorem mirror_chiralA (a : Vector3) : mirror * chiralA a * mirror = chiralB a := by
  simp [mirror, chiralA_eq_lower, chiralB_eq_upper, Matrix.fromBlocks_multiply]

theorem mirror_chiralB (a : Vector3) : mirror * chiralB a * mirror = chiralA a := by
  simp [mirror, chiralA_eq_lower, chiralB_eq_upper, Matrix.fromBlocks_multiply]

def chiralCasimirA : Matrix8 :=
  ∑ i : Fin 3, chiralA (Pi.single i 1) * chiralA (Pi.single i 1)

def chiralCasimirB : Matrix8 :=
  ∑ i : Fin 3, chiralB (Pi.single i 1) * chiralB (Pi.single i 1)

def firstLorentzCasimir : Matrix8 :=
  (∑ i : Fin 3, doubledRotation (Pi.single i 1) * doubledRotation (Pi.single i 1)) -
    (∑ i : Fin 3, doubledBoost (Pi.single i 1) * doubledBoost (Pi.single i 1))

def secondLorentzCasimir : Matrix8 :=
  ∑ i : Fin 3, doubledRotation (Pi.single i 1) * doubledBoost (Pi.single i 1)

theorem chiralCasimirA_value : chiralCasimirA = (-3 / 4 : ℝ) • sectorMinus := by
  have hsq (i : Fin 3) :
      chiralA (Pi.single i 1) * chiralA (Pi.single i 1) =
        (-1 / 4 : ℝ) • sectorMinus := by
    simp only [chiralA_eq_lower, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
      add_zero, zero_add]
    change Matrix.fromBlocks (0 : Matrix4) 0 0 (rotationAxis i * rotationAxis i) = _
    rw [rotationAxis_sq]
    simp [sectorMinus, Matrix.fromBlocks_smul]
  simp only [chiralCasimirA, hsq, Fin.sum_univ_three]
  module

theorem chiralCasimirB_value : chiralCasimirB = (-3 / 4 : ℝ) • sectorPlus := by
  have hsq (i : Fin 3) :
      chiralB (Pi.single i 1) * chiralB (Pi.single i 1) =
        (-1 / 4 : ℝ) • sectorPlus := by
    simp only [chiralB_eq_upper, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
      add_zero]
    change Matrix.fromBlocks (rotationAxis i * rotationAxis i) 0 0 (0 : Matrix4) = _
    rw [rotationAxis_sq]
    simp [sectorPlus, Matrix.fromBlocks_smul]
  simp only [chiralCasimirB, hsq, Fin.sum_univ_three]
  module

private theorem doubledRotation_axis_sq (i : Fin 3) :
    doubledRotation (Pi.single i 1) * doubledRotation (Pi.single i 1) =
      (-1 / 4 : ℝ) • (1 : Matrix8) := by
  simp only [doubledRotation, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
    add_zero, zero_add]
  change Matrix.fromBlocks (rotationAxis i * rotationAxis i) 0 0
    (rotationAxis i * rotationAxis i) = _
  rw [rotationAxis_sq]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

private theorem doubledBoost_axis_sq (i : Fin 3) :
    doubledBoost (Pi.single i 1) * doubledBoost (Pi.single i 1) =
      (1 / 4 : ℝ) • (1 : Matrix8) := by
  simp only [doubledBoost, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
    add_zero, zero_add, neg_mul_neg]
  change Matrix.fromBlocks (boostAxis i * boostAxis i) 0 0
    (boostAxis i * boostAxis i) = _
  rw [boostAxis_sq]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem firstLorentzCasimir_value :
    firstLorentzCasimir = (-3 / 2 : ℝ) • (1 : Matrix8) := by
  simp only [firstLorentzCasimir, doubledRotation_axis_sq, doubledBoost_axis_sq,
    Fin.sum_univ_three]
  module

theorem firstLorentzCasimir_eq_chiral_sum :
    firstLorentzCasimir = (2 : ℝ) • (chiralCasimirA + chiralCasimirB) := by
  rw [firstLorentzCasimir_value, chiralCasimirA_value, chiralCasimirB_value]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [sectorPlus, sectorMinus, Matrix.fromBlocks, Matrix.one_apply] <;> ring

private theorem doubledRotation_axis_mul_boost (i : Fin 3) :
    doubledRotation (Pi.single i 1) * doubledBoost (Pi.single i 1) =
      (-1 / 4 : ℝ) • (cut * sharedPhase) := by
  simpa [doubledRotation, doubledBoost, cut, sharedPhase, rotationAxis, boostAxis,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul] using
      congrArg (fun M : Matrix4 => (Matrix.fromBlocks M 0 0 (-M) : Matrix8))
        (rotationAxis_mul_boostAxis i)

/-- Corrected sign of the doubled mixed Lorentz quadratic readout. -/
theorem secondLorentzCasimir_value :
    secondLorentzCasimir = (-3 / 4 : ℝ) • (cut * sharedPhase) := by
  simp only [secondLorentzCasimir, doubledRotation_axis_mul_boost, Fin.sum_univ_three]
  module

theorem secondLorentzCasimir_eq_chiral_difference :
    secondLorentzCasimir = -sharedPhase * (chiralCasimirA - chiralCasimirB) := by
  rw [secondLorentzCasimir_value, chiralCasimirA_value, chiralCasimirB_value]
  simp only [cut, sharedPhase, sectorMinus, sectorPlus, sub_eq_add_neg,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
    Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks]

theorem mirror_chiralCasimirA : mirror * chiralCasimirA * mirror = chiralCasimirB := by
  rw [chiralCasimirA_value, chiralCasimirB_value]
  simp [mirror, sectorMinus, sectorPlus, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_multiply]

/-- The existing associative alternator evaluates to the real spin Casimir. -/
theorem rotation_nambu :
    nambu ⟨rotationAxis 0, rotationAxis 1, rotationAxis 2⟩ =
      (-3 / 4 : ℝ) • (1 : Matrix4) := by
  calc
    nambu ⟨rotationAxis 0, rotationAxis 1, rotationAxis 2⟩ =
        rotationAxis 0 * rotationAxis 0 + rotationAxis 1 * rotationAxis 1 +
          rotationAxis 2 * rotationAxis 2 := by
      exact nambu_eq_sum_squares_of_cyclic_comm rotationAxis_commutators.1
        rotationAxis_commutators.2.1 rotationAxis_commutators.2.2
    _ = (-3 / 4 : ℝ) • (1 : Matrix4) := by
      simpa only [Fin.sum_univ_three] using rotation_casimir

theorem chiralA_nambu :
    nambu ⟨chiralA (Pi.single 0 1), chiralA (Pi.single 1 1), chiralA (Pi.single 2 1)⟩ =
      (-3 / 4 : ℝ) • sectorMinus := by
  have h01 : comm (chiralA (Pi.single 0 1)) (chiralA (Pi.single 1 1)) =
      chiralA (Pi.single 2 1) := by
    simpa [InfoGeometry.Algebra.NoncommutativeZornNambu.comm, chiralA_eq_lower,
      rotationAxis, Matrix.fromBlocks_multiply, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add] using
        congrArg (fun M : Matrix4 => (Matrix.fromBlocks (0 : Matrix4) 0 0 M : Matrix8))
          rotationAxis_commutators.1
  have h12 : comm (chiralA (Pi.single 1 1)) (chiralA (Pi.single 2 1)) =
      chiralA (Pi.single 0 1) := by
    simpa [InfoGeometry.Algebra.NoncommutativeZornNambu.comm, chiralA_eq_lower,
      rotationAxis, Matrix.fromBlocks_multiply, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add] using
        congrArg (fun M : Matrix4 => (Matrix.fromBlocks (0 : Matrix4) 0 0 M : Matrix8))
          rotationAxis_commutators.2.1
  have h20 : comm (chiralA (Pi.single 2 1)) (chiralA (Pi.single 0 1)) =
      chiralA (Pi.single 1 1) := by
    simpa [InfoGeometry.Algebra.NoncommutativeZornNambu.comm, chiralA_eq_lower,
      rotationAxis, Matrix.fromBlocks_multiply, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add] using
        congrArg (fun M : Matrix4 => (Matrix.fromBlocks (0 : Matrix4) 0 0 M : Matrix8))
          rotationAxis_commutators.2.2
  calc
    nambu ⟨chiralA (Pi.single 0 1), chiralA (Pi.single 1 1), chiralA (Pi.single 2 1)⟩ =
        chiralCasimirA := by
      simpa only [chiralCasimirA, Fin.sum_univ_three] using
        nambu_eq_sum_squares_of_cyclic_comm h01 h12 h20
    _ = (-3 / 4 : ℝ) • sectorMinus := chiralCasimirA_value

theorem chiralB_nambu :
    nambu ⟨chiralB (Pi.single 0 1), chiralB (Pi.single 1 1), chiralB (Pi.single 2 1)⟩ =
      (-3 / 4 : ℝ) • sectorPlus := by
  have h01 : comm (chiralB (Pi.single 0 1)) (chiralB (Pi.single 1 1)) =
      chiralB (Pi.single 2 1) := by
    simpa [InfoGeometry.Algebra.NoncommutativeZornNambu.comm, chiralB_eq_upper,
      rotationAxis, Matrix.fromBlocks_multiply, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add] using
        congrArg (fun M : Matrix4 => (Matrix.fromBlocks M 0 0 (0 : Matrix4) : Matrix8))
          rotationAxis_commutators.1
  have h12 : comm (chiralB (Pi.single 1 1)) (chiralB (Pi.single 2 1)) =
      chiralB (Pi.single 0 1) := by
    simpa [InfoGeometry.Algebra.NoncommutativeZornNambu.comm, chiralB_eq_upper,
      rotationAxis, Matrix.fromBlocks_multiply, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add] using
        congrArg (fun M : Matrix4 => (Matrix.fromBlocks M 0 0 (0 : Matrix4) : Matrix8))
          rotationAxis_commutators.2.1
  have h20 : comm (chiralB (Pi.single 2 1)) (chiralB (Pi.single 0 1)) =
      chiralB (Pi.single 1 1) := by
    simpa [InfoGeometry.Algebra.NoncommutativeZornNambu.comm, chiralB_eq_upper,
      rotationAxis, Matrix.fromBlocks_multiply, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add] using
        congrArg (fun M : Matrix4 => (Matrix.fromBlocks M 0 0 (0 : Matrix4) : Matrix8))
          rotationAxis_commutators.2.2
  calc
    nambu ⟨chiralB (Pi.single 0 1), chiralB (Pi.single 1 1), chiralB (Pi.single 2 1)⟩ =
        chiralCasimirB := by
      simpa only [chiralCasimirB, Fin.sum_univ_three] using
        nambu_eq_sum_squares_of_cyclic_comm h01 h12 h20
    _ = (-3 / 4 : ℝ) • sectorPlus := chiralCasimirB_value

end InfoGeometry.Canonical.RealDoubledSpinCasimirBridge

end
