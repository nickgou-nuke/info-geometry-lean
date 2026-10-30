/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

set_option maxHeartbeats 5000000

/-!
# Pure Non-Commutative Operator Spine: Archetypes A₁–A₂₅
# Complete causal poset of non-commutative operator algebra over a ring B with idempotent P (P*P=P).
# Ring identities with the focused repository Peirce owners as proof dependencies.
-/

namespace InfoGeometry.PureNonCommutativeOperatorSpine

variable {B : Type*} [Ring B]

def comm (X Y : B) : B := X * Y - Y * X
def anticomm (X Y : B) : B := X * Y + Y * X

def invS (P : B) : B := P - (1 - P)
def conePlus (P A : B) : B := P * A * (1 - P)
def coneMinus (P C : B) : B := (1 - P) * C * P

def peirce11 (P X : B) : B := P * X * P
def peirce00 (P X : B) : B := (1 - P) * X * (1 - P)
def evenGrade (P X : B) : B := P * X * P + (1 - P) * X * (1 - P)
def oddGrade (P X : B) : B := P * X * (1 - P) + (1 - P) * X * P

def genPhi (P A C : B) : B := conePlus P A + coneMinus P C
def genJ   (P A C : B) : B := conePlus P A - coneMinus P C
def genV   (P A C : B) : B := anticomm (conePlus P A) (coneMinus P C)
def genSig (P A C : B) : B := comm (conePlus P A) (coneMinus P C)

def derivSqPhi (P A C X : B) : B := -comm (genPhi P A C) (comm (genPhi P A C) X)
def derivSqJ   (P A C X : B) : B := comm (genJ P A C) (comm (genJ P A C) X)
def derivSqSig (P A C X : B) : B := -comm (genSig P A C) (comm (genSig P A C) X)
def derivCasimir (P A C X : B) : B := derivSqPhi P A C X + derivSqJ P A C X + derivSqSig P A C X

def projV   (P A C X : B) : B := (8 : ℤ) • X + derivCasimir P A C X
def projPhi (P A C X : B) : B := derivSqPhi P A C X - derivSqJ P A C X - derivSqSig P A C X
def projJ   (P A C X : B) : B := derivSqJ P A C X - derivSqPhi P A C X - derivSqSig P A C X
def projSig (P A C X : B) : B := derivSqSig P A C X - derivSqPhi P A C X - derivSqJ P A C X

def hProjV (P A C X : B) : B :=
  (8 : ℤ) • ((genV P A C * genV P A C) * X) +
  (genV P A C * derivSqPhi P A C X + genV P A C * derivSqJ P A C X + derivSqSig P A C X)

def hProjPhi (P A C X : B) : B :=
  genV P A C * derivSqPhi P A C X - genV P A C * derivSqJ P A C X - derivSqSig P A C X

def hProjJ (P A C X : B) : B :=
  genV P A C * derivSqJ P A C X - genV P A C * derivSqPhi P A C X - derivSqSig P A C X

def hProjSig (P A C X : B) : B :=
  derivSqSig P A C X - genV P A C * derivSqPhi P A C X - genV P A C * derivSqJ P A C X

def sandwichCross (P A C X : B) : B :=
  conePlus P A * X * coneMinus P C + coneMinus P C * X * conePlus P A

def sandwichSame (P A C X : B) : B :=
  conePlus P A * X * conePlus P A + coneMinus P C * X * coneMinus P C

def ladderMinus (P A C X : B) : B := comm (genPhi P A C) (comm (genJ P A C) X)
def ladderPlus  (P A C X : B) : B := comm (genJ P A C) (comm (genPhi P A C) X)
def ladderSum   (P A C X : B) : B := ladderMinus P A C X + ladderPlus P A C X

def conjPlus (P A X : B) : B := (1 + conePlus P A) * X * (1 - conePlus P A)
def conjPlusInv (P A X : B) : B := (1 - conePlus P A) * X * (1 + conePlus P A)
def conjMinus (P C X : B) : B := (1 + coneMinus P C) * X * (1 - coneMinus P C)
def conjMinusInv (P C X : B) : B := (1 - coneMinus P C) * X * (1 + coneMinus P C)

def weylJ (P A C : B) : B := genJ P A C + (1 - genV P A C)
def weylJInv (P A C : B) : B := -genJ P A C + (1 - genV P A C)
def weylPhi (P A C : B) : B := genPhi P A C + (1 - genV P A C)

def steinbergBraid (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C) * (1 + conePlus P A)

def steinbergBraidInv (P A C : B) : B :=
  (1 - conePlus P A) * (1 + coneMinus P C) * (1 - conePlus P A)

def steinbergBraidDual (P A C : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A) * (1 + coneMinus P C)

def steinbergBraidDualInv (P A C : B) : B :=
  (1 - coneMinus P C) * (1 + conePlus P A) * (1 - coneMinus P C)

lemma P_assoc {P : B} (hP : P * P = P) (X : B) : P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

lemma P_assoc_right {P : B} (hP : P * P = P) (X : B) : (X * P) * P = X * P := by
  calc
    (X * P) * P = X * (P * P) := by rw [mul_assoc]
    _ = X * P := by rw [hP]

lemma conePlus_mul_P {P : B} (hP : P * P = P) (A : B) : conePlus P A * P = 0 := by
  calc
    conePlus P A * P = P * A * (1 - P) * P := by rw [conePlus]
    _ = P * A * ((1 - P) * P) := by rw [mul_assoc]
    _ = P * A * (P - P * P) := by
      simp [mul_sub, sub_mul, mul_one, one_mul]
      <;> abel
    _ = P * A * (P - P) := by rw [hP]
    _ = P * A * 0 := by simp [sub_self]
    _ = 0 := by simp

lemma P_mul_coneMinus {P : B} (hP : P * P = P) (C : B) : P * coneMinus P C = 0 := by
  calc
    P * coneMinus P C = P * ((1 - P) * C * P) := by rw [coneMinus]
    _ = (P * (1 - P)) * C * P := by noncomm_ring
    _ = (P - P * P) * C * P := by
      simp [mul_sub, sub_mul, mul_one, one_mul]
      <;> abel
    _ = (P - P) * C * P := by rw [hP]
    _ = 0 * C * P := by simp [sub_self]
    _ = 0 := by simp [mul_zero]

lemma P_mul_conePlus {P : B} (hP : P * P = P) (A : B) : P * conePlus P A = conePlus P A := by
  calc
    P * conePlus P A = P * (P * A * (1 - P)) := by rw [conePlus]
    _ = (P * P) * A * (1 - P) := by noncomm_ring
    _ = P * A * (1 - P) := by rw [hP]
    _ = conePlus P A := by rw [conePlus]

lemma coneMinus_mul_P {P : B} (hP : P * P = P) (C : B) : coneMinus P C * P = coneMinus P C := by
  calc
    coneMinus P C * P = ((1 - P) * C * P) * P := by rw [coneMinus]
    _ = (1 - P) * C * (P * P) := by rw [mul_assoc]
    _ = (1 - P) * C * P := by rw [hP]
    _ = coneMinus P C := by rw [coneMinus]

lemma conePlus_sq_zero {P : B} (hP : P * P = P) (A : B) : conePlus P A * conePlus P A = 0 := by
  have h₁ : conePlus P A * conePlus P A = 0 := by
    -- N₊ * N₊ = P*A*(1-P) * P*A*(1-P) = P*A*(1-P)*P*A*(1-P)
    -- (1-P)*P = P - P*P = 0
    calc
      conePlus P A * conePlus P A = (P * A * (1 - P)) * (P * A * (1 - P)) := by rw [conePlus]
      _ = P * A * ((1 - P) * P) * A * (1 - P) := by
        rw [mul_assoc, mul_assoc]
        <;> simp [mul_assoc]
        <;> abel
      _ = P * A * (P - P * P) * A * (1 - P) := by
        simp [mul_sub, sub_mul, mul_one, one_mul]
        <;> abel
      _ = P * A * (P - P) * A * (1 - P) := by rw [hP]
      _ = P * A * 0 * A * (1 - P) := by simp [sub_self]
      _ = 0 := by simp [mul_zero]
  exact h₁

lemma coneMinus_sq_zero {P : B} (hP : P * P = P) (C : B) : coneMinus P C * coneMinus P C = 0 := by
  have h₁ : coneMinus P C * coneMinus P C = 0 := by
    calc
      coneMinus P C * coneMinus P C = ((1 - P) * C * P) * ((1 - P) * C * P) := by rw [coneMinus]
      _ = (1 - P) * C * (P * (1 - P)) * C * P := by
        rw [mul_assoc, mul_assoc]
        <;> simp [mul_assoc]
        <;> abel
      _ = (1 - P) * C * (P - P * P) * C * P := by
        simp [mul_sub, sub_mul, mul_one, one_mul]
        <;> abel
      _ = (1 - P) * C * (P - P) * C * P := by rw [hP]
      _ = (1 - P) * C * 0 * C * P := by simp [sub_self]
      _ = 0 := by simp [mul_zero]
  exact h₁

lemma conePlus_mul_conePlus {P : B} (hP : P * P = P) (A X : B) : conePlus P A * conePlus P X = 0 := by
  calc
    conePlus P A * conePlus P X = (P * A * (1 - P)) * (P * X * (1 - P)) := by rw [conePlus, conePlus]
    _ = P * A * ((1 - P) * P) * X * (1 - P) := by
      rw [mul_assoc, mul_assoc]
      <;> simp [mul_assoc]
      <;> abel
    _ = P * A * (P - P * P) * X * (1 - P) := by
      simp [mul_sub, sub_mul, mul_one, one_mul]
      <;> abel
    _ = P * A * (P - P) * X * (1 - P) := by rw [hP]
    _ = P * A * 0 * X * (1 - P) := by simp [sub_self]
    _ = 0 := by simp [mul_zero]

lemma coneMinus_mul_coneMinus {P : B} (hP : P * P = P) (C Y : B) : coneMinus P C * coneMinus P Y = 0 := by
  calc
    coneMinus P C * coneMinus P Y = ((1 - P) * C * P) * ((1 - P) * Y * P) := by rw [coneMinus, coneMinus]
    _ = (1 - P) * C * (P * (1 - P)) * Y * P := by
      rw [mul_assoc, mul_assoc]
      <;> simp [mul_assoc]
      <;> abel
    _ = (1 - P) * C * (P - P * P) * Y * P := by
      simp [mul_sub, sub_mul, mul_one, one_mul]
      <;> abel
    _ = (1 - P) * C * (P - P) * Y * P := by rw [hP]
    _ = (1 - P) * C * 0 * Y * P := by simp [sub_self]
    _ = 0 := by simp [mul_zero]

macro "peirce_abel" hP:ident : tactic =>
  `(tactic| (
    simp [weylJ, weylJInv, weylPhi, steinbergBraid,
          steinbergBraidInv, steinbergBraidDual, steinbergBraidDualInv,
          hProjV, hProjPhi, hProjJ, hProjSig,
          conjPlus, conjPlusInv, conjMinus, conjMinusInv,
          projV, projPhi, projJ, projSig, derivCasimir,
          derivSqPhi, derivSqJ, derivSqSig,
          ladderSum, ladderMinus, ladderPlus,
          sandwichCross, sandwichSame,
          genPhi, genJ, genV, genSig,
          evenGrade, oddGrade, peirce11, peirce00,
          invS, comm, anticomm, conePlus, coneMinus,
          sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
          add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
          mul_assoc, $hP:ident, P_assoc $hP:ident, P_assoc_right $hP:ident,
          conePlus_mul_P $hP:ident, P_mul_coneMinus $hP:ident,
          P_mul_conePlus $hP:ident, coneMinus_mul_P $hP:ident,
          conePlus_sq_zero $hP:ident, coneMinus_sq_zero $hP:ident,
          conePlus_mul_conePlus $hP:ident, coneMinus_mul_coneMinus $hP:ident]
    <;>
    abel))

/-! ========================================================================
   ARCHETYPES A₁–A₁₆ (from the established spine)
   ======================================================================== -/

/-! ### Archetype A₁: Dual Lie–Jordan Leibniz Laws & Mixed Jacobi Identity -/

theorem archetype_A1_dual_leibniz_and_jacobi (H U V : B) :
    comm H (U * V) = comm H U * V + U * comm H V ∧
    comm H (U * V) = anticomm H U * V - U * anticomm H V ∧
    comm H (comm U V) + comm U (comm V H) + comm V (comm H U) = 0 ∧
    comm H (anticomm U V) - anticomm U (comm H V) = anticomm (comm H U) V ∧
    comm H (anticomm H U) = comm (H * H) U ∧
    anticomm H (comm H U) = comm (H * H) U := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [comm, anticomm, add_mul, mul_add, sub_mul, mul_sub, mul_assoc]; abel)

/-! ### Archetype A₂: Peirce–Cartan `Z₂`-Grading, `ad_P³ = ad_P` & Tangent Product Closure -/

theorem archetype_A2_peirce_cartan_grading_and_tangent_closure
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * invS P = 1 ∧
    comm P (comm P A) = oddGrade P A ∧
    A - comm P (comm P A) = evenGrade P A ∧
    comm P (comm P (comm P A)) = comm P A ∧
    anticomm P (comm P A) = comm P A ∧
    comm P (comm P A * comm P C) = 0 ∧
    invS P * A * invS P = evenGrade P A - oddGrade P A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₃: Nilpotent Cones & The Split-Quaternion `Cl_{1,1}` Tetraktys Table -/

theorem archetype_A3_nilpotent_cones_and_tetraktys_table
    {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C = -genSig P A C ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    genSig P A C = invS P * genV P A C ∧
    genV P A C = invS P * genSig P A C ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C ∧
    comm (conePlus P A) (genV P A C) = 0 ∧
    comm (coneMinus P C) (genV P A C) = 0 ∧
    anticomm (conePlus P A) (genSig P A C) = 0 ∧
    anticomm (coneMinus P C) (genSig P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₄: Sandwich Complementarity, Vertex Factorization & Double-Derivation Trinity -/

theorem archetype_A4_sandwich_complementarity_and_trinity
    {P : B} (hP : P * P = P) (A C X : B) :
    sandwichCross P A C X + sandwichSame P A C X = genPhi P A C * X * genPhi P A C ∧
    sandwichCross P A C X - sandwichSame P A C X = -(genJ P A C * X * genJ P A C) ∧
    -(comm (conePlus P A) (comm (coneMinus P C) X) + comm (coneMinus P C) (comm (conePlus P A) X)) =
      (2 : ℤ) • sandwichCross P A C X - anticomm (genV P A C) X ∧
    (2 : ℤ) • ((2 : ℤ) • sandwichCross P A C X - anticomm (genV P A C) X) =
      derivSqPhi P A C X + derivSqJ P A C X ∧
    derivSqPhi P A C X - derivSqJ P A C X = (4 : ℤ) • sandwichSame P A C X ∧
    sandwichCross P A C (genV P A C) = genV P A C * genV P A C ∧
    sandwichCross P A C (genSig P A C) = -(genV P A C * genSig P A C) ∧
    sandwichCross P A C (genPhi P A C) = 0 ∧
    sandwichCross P A C (genJ P A C) = 0 ∧
    sandwichSame P A C (genV P A C) = 0 ∧
    sandwichSame P A C (genSig P A C) = 0 ∧
    sandwichSame P A C (genPhi P A C) = genV P A C * genPhi P A C ∧
    sandwichSame P A C (genJ P A C) = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₅: Klein–Hadamard `Z₂ × Z₂` Eigenvalue Matrix & Partition of Unity -/

theorem archetype_A5_klein_hadamard_spectra_and_partition
    {P : B} (hP : P * P = P) (A C X : B) :
    projV P A C X + projPhi P A C X + projJ P A C X + projSig P A C X = (8 : ℤ) • X ∧
    derivSqPhi P A C (genPhi P A C) = 0 ∧
    derivSqPhi P A C (genV P A C) = 0 ∧
    derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    derivSqPhi P A C (genSig P A C) = -((4 : ℤ) • (genV P A C * genSig P A C)) ∧
    derivSqJ P A C (genJ P A C) = 0 ∧
    derivSqJ P A C (genV P A C) = 0 ∧
    derivSqJ P A C (genPhi P A C) = -((4 : ℤ) • (genV P A C * genPhi P A C)) ∧
    derivSqJ P A C (genSig P A C) = -((4 : ℤ) • (genV P A C * genSig P A C)) ∧
    derivSqSig P A C (genSig P A C) = 0 ∧
    derivSqSig P A C (genV P A C) = 0 ∧
    derivSqSig P A C (genPhi P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    derivSqSig P A C (genJ P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₆: Second-Level Superoperator Nilpotent Ladder Recursion -/

theorem archetype_A6_superoperator_ladder_recursion
    {P : B} (hP : P * P = P) (A C X : B) :
    ladderMinus P A C (genPhi P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    ladderMinus P A C (genJ P A C) = 0 ∧
    ladderPlus P A C (genJ P A C) = (4 : ℤ) • (genV P A C * genPhi P A C) ∧
    ladderPlus P A C (genPhi P A C) = 0 ∧
    ladderMinus P A C (ladderMinus P A C (genPhi P A C)) = 0 ∧
    ladderPlus P A C (ladderPlus P A C (genJ P A C)) = 0 ∧
    ladderMinus P A C X - ladderPlus P A C X = -((2 : ℤ) • comm (genSig P A C) X) ∧
    ladderSum P A C (genV P A C) = 0 ∧
    ladderSum P A C (genSig P A C) = 0 ∧
    ladderSum P A C (ladderSum P A C (genPhi P A C)) =
      -((16 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    ladderSum P A C (ladderSum P A C (genJ P A C)) =
      -((16 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₇: Symmetry-Adapted `so(1,2) ≅ sl₂` Lie Brackets & Cubic Inversions -/

theorem archetype_A7_so12_lie_brackets_and_cubic_inversions
    {P : B} (hP : P * P = P) (A C : B) :
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) ∧
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    comm (genSig P A C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) ∧
    comm (genSig P A C) (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    genPhi P A C * conePlus P A * genPhi P A C = genV P A C * coneMinus P C ∧
    genPhi P A C * coneMinus P C * genPhi P A C = conePlus P A * genV P A C ∧
    genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C ∧
    genJ P A C * genJ P A C * genJ P A C = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₈: Same-Cone Commutativity & Two-Channel Superposition Identity -/

theorem archetype_A8_same_cone_commutativity_and_superposition
    {P : B} (hP : P * P = P) (A₁ A₂ C₁ C₂ : B) :
    conePlus P A₁ * conePlus P A₂ = 0 ∧
    coneMinus P C₁ * coneMinus P C₂ = 0 ∧
    comm (conePlus P A₁) (conePlus P A₂) = 0 ∧
    comm (coneMinus P C₁) (coneMinus P C₂) = 0 ∧
    genV P (A₁ + A₂) (C₁ + C₂) =
      genV P A₁ C₁ + genV P A₂ C₂ +
      (anticomm (conePlus P A₁) (coneMinus P C₂) +
       anticomm (conePlus P A₂) (coneMinus P C₁)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₉: Peirce Block-Diagonal Splits of `V` and `Σ` & Grading Parity -/

theorem archetype_A9_peirce_block_diagonal_splits
    {P : B} (hP : P * P = P) (A C X : B) :
    peirce11 P X + peirce00 P X + conePlus P X + coneMinus P X = X ∧
    peirce11 P (genV P A C) = conePlus P A * coneMinus P C ∧
    peirce00 P (genV P A C) = coneMinus P C * conePlus P A ∧
    peirce11 P (genSig P A C) = conePlus P A * coneMinus P C ∧
    peirce00 P (genSig P A C) = -(coneMinus P C * conePlus P A) ∧
    genV P A C + genSig P A C = (2 : ℤ) • (conePlus P A * coneMinus P C) ∧
    genV P A C - genSig P A C = (2 : ℤ) • (coneMinus P C * conePlus P A) ∧
    evenGrade P (genV P A C) = genV P A C ∧
    oddGrade P (genV P A C) = 0 ∧
    evenGrade P (genSig P A C) = genSig P A C ∧
    oddGrade P (genSig P A C) = 0 ∧
    evenGrade P (genPhi P A C) = 0 ∧
    oddGrade P (genPhi P A C) = genPhi P A C ∧
    evenGrade P (genJ P A C) = 0 ∧
    oddGrade P (genJ P A C) = genJ P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₁₀: Casimir Spectrum & Superoperator Commutator Algebra -/

theorem archetype_A10_casimir_and_superoperator_commutators
    {P : B} (hP : P * P = P) (A C : B) :
    derivCasimir P A C (genV P A C) = 0 ∧
    derivCasimir P A C (genSig P A C) = -((8 : ℤ) • (genV P A C * genSig P A C)) ∧
    derivCasimir P A C (genPhi P A C) =
      -((4 : ℤ) • (genV P A C * genPhi P A C + (genV P A C * genV P A C) * genPhi P A C)) ∧
    derivCasimir P A C (genJ P A C) =
      -((4 : ℤ) • (genV P A C * genJ P A C + (genV P A C * genV P A C) * genJ P A C)) ∧
    ladderPlus P A C (ladderMinus P A C (genPhi P A C)) =
      -((16 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    ladderMinus P A C (ladderPlus P A C (genJ P A C)) =
      -((16 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)) ∧
    derivSqPhi P A C (derivSqJ P A C (genPhi P A C)) = 0 ∧
    derivSqJ P A C (derivSqPhi P A C (genJ P A C)) = 0 ∧
    derivSqPhi P A C (derivSqJ P A C (genSig P A C)) =
      (16 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) ∧
    derivSqJ P A C (derivSqPhi P A C (genSig P A C)) =
      (16 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₁₁: Raw Character Selection & `V`-Polynomial Defect Laws -/

theorem archetype_A11_klein_hadamard_character_selection
    {P : B} (hP : P * P = P) (A C : B) :
    projV P A C (genV P A C) = (8 : ℤ) • genV P A C ∧
    projPhi P A C (genV P A C) = 0 ∧
    projPhi P A C (genSig P A C) = 0 ∧
    projJ P A C (genV P A C) = 0 ∧
    projJ P A C (genSig P A C) = 0 ∧
    projSig P A C (genV P A C) = 0 ∧
    projSig P A C (genSig P A C) = (8 : ℤ) • (genV P A C * genSig P A C) ∧
    projV P A C (genSig P A C) = (8 : ℤ) • (genSig P A C - genV P A C * genSig P A C) ∧
    projPhi P A C (genPhi P A C) =
      (4 : ℤ) • (genV P A C * genPhi P A C + (genV P A C * genV P A C) * genPhi P A C) ∧
    projJ P A C (genJ P A C) =
      (4 : ℤ) • (genV P A C * genJ P A C + (genV P A C * genV P A C) * genJ P A C) ∧
    projPhi P A C (genJ P A C) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C - genV P A C * genJ P A C) ∧
    projJ P A C (genPhi P A C) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C - genV P A C * genPhi P A C) ∧
    projSig P A C (genPhi P A C) =
      (4 : ℤ) • (genV P A C * genPhi P A C - (genV P A C * genV P A C) * genPhi P A C) ∧
    projSig P A C (genJ P A C) =
      (4 : ℤ) • (genV P A C * genJ P A C - (genV P A C * genV P A C) * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₁₂: Non-Commutative Nilpotent Baker–Campbell–Hausdorff Conjugation Group -/

theorem archetype_A12_nilpotent_bch_conjugation_group
    {P : B} (hP : P * P = P) (A₁ A₂ C₁ C₂ X : B) :
    conjPlus P A₁ X = X + comm (conePlus P A₁) X - conePlus P A₁ * X * conePlus P A₁ ∧
    conjMinus P C₁ X = X + comm (coneMinus P C₁) X - coneMinus P C₁ * X * coneMinus P C₁ ∧
    conjPlus P A₁ (conjPlusInv P A₁ X) = X ∧
    conjPlusInv P A₁ (conjPlus P A₁ X) = X ∧
    conjMinus P C₁ (conjMinusInv P C₁ X) = X ∧
    conjMinusInv P C₁ (conjMinus P C₁ X) = X ∧
    conjPlus P A₁ (conjPlus P A₂ X) = conjPlus P (A₁ + A₂) X ∧
    conjMinus P C₁ (conjMinus P C₂ X) = conjMinus P (C₁ + C₂) X ∧
    conjPlus P A₁ P = P - conePlus P A₁ ∧
    conjMinus P C₁ P = P + coneMinus P C₁ ∧
    conjPlus P A₁ (invS P) = invS P - (2 : ℤ) • conePlus P A₁ ∧
    conjMinus P C₁ (invS P) = invS P + (2 : ℤ) • coneMinus P C₁ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel hP

/-! ### Archetype A₁₃: Universal Off-Shell Homogenized Klein–Hadamard Diagonalization -/

theorem archetype_A13_universal_off_shell_homogenized_projectors
    {P : B} (hP : P * P = P) (A C X : B) :
    hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X =
      (8 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    hProjV P A C (genV P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genV P A C) ∧
    hProjV P A C (genPhi P A C) = 0 ∧
    hProjV P A C (genJ P A C) = 0 ∧
    hProjV P A C (genSig P A C) = 0 ∧
    hProjPhi P A C (genPhi P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    hProjPhi P A C (genV P A C) = 0 ∧
    hProjPhi P A C (genJ P A C) = 0 ∧
    hProjPhi P A C (genSig P A C) = 0 ∧
    hProjJ P A C (genJ P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    hProjJ P A C (genV P A C) = 0 ∧
    hProjJ P A C (genPhi P A C) = 0 ∧
    hProjJ P A C (genSig P A C) = 0 ∧
    hProjSig P A C (genSig P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) ∧
    hProjSig P A C (genV P A C) = 0 ∧
    hProjSig P A C (genPhi P A C) = 0 ∧
    hProjSig P A C (genJ P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_abel hP

/-! ### Archetype A₁₄: Unipotent BCH Conjugation of the Tetraktys & Exact Invariance of `V` -/

theorem archetype_A14_unipotent_bch_tetraktys_action_c1 {P : B} (hP : P * P = P) (A C : B) :
    conjPlus P A (genV P A C) = genV P A C := by
  peirce_abel hP

theorem archetype_A14_unipotent_bch_tetraktys_action_c2 {P : B} (hP : P * P = P) (A C : B) :
    conjPlusInv P A (genV P A C) = genV P A C := by
  peirce_abel hP

theorem archetype_A14_unipotent_bch_tetraktys_action_c3 {P : B} (hP : P * P = P) (A C : B) :
    conjMinus P C (genV P A C) = genV P A C := by
  peirce_abel hP

theorem archetype_A14_unipotent_bch_tetraktys_action_c4 {P : B} (hP : P * P = P) (A C : B) :
    conjMinusInv P C (genV P A C) = genV P A C := by
  peirce_abel hP

theorem archetype_A14_unipotent_bch_tetraktys_action_c5 {P : B} (hP : P * P = P) (A C : B) :
    conjPlus P A (conjMinus P C (genV P A C)) = genV P A C := by
  peirce_abel hP

theorem archetype_A14_unipotent_bch_tetraktys_action_c6 {P : B} (hP : P * P = P) (A C : B) :
    conjPlus P A (genSig P A C) =
      genSig P A C - (2 : ℤ) • (genV P A C * conePlus P A) := by
  peirce_abel hP

theorem archetype_A14_unipotent_bch_tetraktys_action_c7 {P : B} (hP : P * P = P) (A C : B) :
    conjMinus P C (genSig P A C) =
      genSig P A C + (2 : ℤ) • (genV P A C * coneMinus P C) := by
  peirce_abel hP

theorem archetype_A14_unipotent_bch_tetraktys_action_c8 {P : B} (hP : P * P = P) (A C : B) :
    conjPlus P A (genPhi P A C) =
      genPhi P A C + genSig P A C - genV P A C * conePlus P A := by
  peirce_abel hP

theorem archetype_A14_unipotent_bch_tetraktys_action_c9 {P : B} (hP : P * P = P) (A C : B) :
    conjMinus P C (genPhi P A C) =
      genPhi P A C - genSig P A C - genV P A C * coneMinus P C := by
  peirce_abel hP

theorem archetype_A14_unipotent_bch_tetraktys_action_c10 {P : B} (hP : P * P = P) (A C : B) :
    conjPlus P A (conjMinus P C P) - conjMinus P C (conjPlus P A P) =
      -(genV P A C * genPhi P A C) := by
  exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A14_unipotent_tetraktys_action hP A C).2.2.2.2.2.2.2.2.2

/-! ### Archetype A₁₅: Second-Order Superoperator Orthogonality -/

theorem archetype_A15_second_order_off_shell_superoperator_orthogonality
    {P : B} (hP : P * P = P) (A C : B) :
    hProjV P A C (hProjV P A C (genV P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjV P A C (genV P A C)) ∧
    hProjPhi P A C (hProjPhi P A C (genPhi P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjPhi P A C (genPhi P A C)) ∧
    hProjJ P A C (hProjJ P A C (genJ P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjJ P A C (genJ P A C)) ∧
    hProjSig P A C (hProjSig P A C (genSig P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjSig P A C (genSig P A C)) ∧
    hProjPhi P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjJ P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjSig P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjV P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjJ P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjSig P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjV P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjPhi P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjSig P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjV P A C (hProjSig P A C (genSig P A C)) = 0 ∧
    hProjPhi P A C (hProjSig P A C (genSig P A C)) = 0 ∧
    hProjJ P A C (hProjSig P A C (genSig P A C)) = 0 := by
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A15_second_order_orthogonality hP A C

/-! ### Archetype A₁₆: Cayley–Weyl Reflection `W = J + 1 - V` & Steinberg Cross-Cone Braid -/

theorem archetype_A16_cayley_weyl_steinberg_reflection
    {P : B} (hP : P * P = P) (A C : B) :
    weylJ P A C * weylJInv P A C - 1 = genV P A C * genV P A C - genV P A C ∧
    weylJInv P A C * weylJ P A C - 1 = genV P A C * genV P A C - genV P A C ∧
    comm (weylJ P A C) (genV P A C) = 0 ∧
    genJ P A C * peirce11 P (genV P A C) * (-genJ P A C) = peirce00 P (genV P A C * genV P A C) ∧
    genJ P A C * peirce00 P (genV P A C) * (-genJ P A C) = peirce11 P (genV P A C * genV P A C) ∧
    genPhi P A C * peirce11 P (genV P A C) * genPhi P A C = peirce00 P (genV P A C * genV P A C) ∧
    genPhi P A C * peirce00 P (genV P A C) * genPhi P A C = peirce11 P (genV P A C * genV P A C) ∧
    steinbergBraid P A C = weylJ P A C + (1 - genV P A C) * conePlus P A ∧
    conjPlus P A (conjMinusInv P C (conjPlus P A P)) =
      P - (2 : ℤ) • conePlus P A - coneMinus P C - (2 : ℤ) • genSig P A C +
      (3 : ℤ) • (genV P A C * conePlus P A) + genV P A C * coneMinus P C +
      genV P A C * genSig P A C - genV P A C * genV P A C * conePlus P A := by
  rcases InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A16_cayley_weyl_steinberg_reflection hP A C with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8,
    InfoGeometry.OperatorAlgebra.PeirceSpine.steinberg_image_idem hP A C⟩

/-! ========================================================================
   ARCHETYPE A₂₁: Operator Projective Line `ℙ¹(B)` & North-to-South Pole Inversion
   ======================================================================== -/

/-! **Upper Affine Chart of the Operator Projective Line `ℙ¹(B)` (`projChartPlus P X`):**
Maps any ring element `X : B` to the graph idempotent `P(X) = Ad(1 + N₊(X))(P) = P - conePlus P X`
centered at the North Pole `P(0) = P`. -/
def projChartPlus (P X : B) : B := P - conePlus P X

/-! **Lower Affine Chart of the Operator Projective Line `ℙ¹(B)` (`projChartMinus P Y`):**
Maps any ring element `Y : B` to the dual graph idempotent `Q(Y) = Ad(1 + N₋(Y))(1 - P) = (1 - P) - coneMinus P Y`
centered at the South Pole `Q(0) = 1 - P`. -/
def projChartMinus (P Y : B) : B := (1 - P) - coneMinus P Y

/-! **Non-Commutative Biprojective Cross-Ratio / Distance Operator (`operatorCrossRatio`):**
Pairs two points `X₁, X₂` in the upper chart with two points `Y₁, Y₂` in the lower chart via
`{P(X₁) - P(X₂), Q(Y₁) - Q(Y₂)} = {conePlus P (X₁ - X₂), coneMinus P (Y₁ - Y₂)}`. -/
def operatorCrossRatio (P X₁ X₂ Y₁ Y₂ : B) : B :=
  anticomm (projChartPlus P X₁ - projChartPlus P X₂)
           (projChartMinus P Y₁ - projChartMinus P Y₂)

/-! === A₂₁ Individual Conjunct Theorems === -/

theorem archetype_A21_chart_idempotent_plus {P : B} (hP : P * P = P) (X : B) :
    projChartPlus P X * projChartPlus P X = projChartPlus P X := by
  simp [projChartPlus]
  <;> simp [conePlus_mul_P hP, P_mul_conePlus hP, conePlus_sq_zero hP, hP,
            add_mul, mul_add, sub_mul, mul_sub, mul_assoc]
  <;> abel

theorem archetype_A21_chart_idempotent_minus {P : B} (hP : P * P = P) (C : B) :
    projChartMinus P C * projChartMinus P C = projChartMinus P C := by
  simp [projChartMinus]
  <;> simp [coneMinus_mul_P hP, P_mul_coneMinus hP, coneMinus_sq_zero hP, hP,
            add_mul, mul_add, sub_mul, mul_sub, mul_assoc]
  <;> abel

theorem archetype_A21_conjPlus_translation {P : B} (hP : P * P = P) (A X : B) :
    conjPlus P A (projChartPlus P X) = projChartPlus P (X + A) := by
  have h_add : conePlus P (X + A) = conePlus P X + conePlus P A := by
    calc
      conePlus P (X + A) = P * (X + A) * (1 - P) := by rw [conePlus]
      _ = (P * X + P * A) * (1 - P) := by
        rw [mul_add]
        <;> simp [mul_assoc]
        <;> abel
      _ = P * X * (1 - P) + P * A * (1 - P) := by
        rw [add_mul]
        <;> simp [mul_assoc]
        <;> abel
      _ = conePlus P X + conePlus P A := by
        simp [conePlus]
        <;> abel
  calc
    conjPlus P A (projChartPlus P X)
      = (1 + conePlus P A) * (P - conePlus P X) * (1 - conePlus P A) := by
        rw [conjPlus, projChartPlus]
      _ = P - conePlus P X - conePlus P A := by
        simp [conePlus_mul_P hP, P_mul_conePlus hP, conePlus_sq_zero hP,
              conePlus_mul_conePlus hP, hP,
              add_mul, mul_add, sub_mul, mul_sub, mul_assoc]
        <;> abel
      _ = P - conePlus P (X + A) := by
        rw [h_add]
        <;> abel
      _ = projChartPlus P (X + A) := by
        simp [projChartPlus]

theorem archetype_A21_conjMinus_translation {P : B} (hP : P * P = P) (C X : B) :
    conjMinus P C (projChartMinus P X) = projChartMinus P (X + C) := by
  exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A21_operator_projective_line hP (0 : B) C X).2.2.2.1

theorem archetype_A21_pole_interpolation {P : B} (hP : P * P = P) (A C : B) :
    P - genSig P A C = (1 - P) * genV P A C + P * (1 - genV P A C) := by
  exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A21_operator_projective_line hP A C (0 : B)).2.2.2.2.1

theorem archetype_A21_pole_interpolation_dual {P : B} (hP : P * P = P) (A C : B) :
    (1 - P) + genSig P A C = P * genV P A C + (1 - P) * (1 - genV P A C) := by
  peirce_abel hP

theorem archetype_A21_steinberg_north_to_south {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraid P A C * P * steinbergBraidInv P A C =
      P - (2 : ℤ) • conePlus P A - coneMinus P C - (2 : ℤ) • genSig P A C +
      (3 : ℤ) • (genV P A C * conePlus P A) + genV P A C * coneMinus P C +
      genV P A C * genSig P A C - genV P A C * genV P A C * conePlus P A := by
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A21_steinberg_north_to_south hP A C

/-! === A₂₂ Individual Conjunct Theorems === -/

/-! Hua–Bertram Projective Distance Identity: `(P(X) - Q(C))² = 1 - V(X, C)`.
   The sign is minus because both upper-chart and lower-chart difference terms are nilpotent
   cross-cone terms whose product vanishes under the idempotent constraint `P*P=P`. -/
theorem archetype_A22_hua_bertram_distance {P : B} (hP : P * P = P) (X C : B) :
    (projChartPlus P X - projChartMinus P C) *
      (projChartPlus P X - projChartMinus P C) =
      1 - genV P X C := by
  exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A22_hua_distance_and_cross_ratio hP (0 : B) 0 X C 0 0 0 0).1

theorem archetype_A22_cross_ratio_definition {P : B} (hP : P * P = P) (X₁ X₂ Y₁ Y₂ : B) :
    operatorCrossRatio P X₁ X₂ Y₁ Y₂ = genV P (X₁ - X₂) (Y₁ - Y₂) := by
  exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A22_hua_distance_and_cross_ratio hP (0 : B) 0 0 0 X₁ X₂ Y₁ Y₂).2.1

theorem archetype_A22_cross_ratio_origin {P : B} (hP : P * P = P) (A C : B) :
    operatorCrossRatio P A 0 C 0 = genV P A C := by
  have h₁ : operatorCrossRatio P A 0 C 0 = genV P (A - 0) (C - 0) := by
    exact archetype_A22_cross_ratio_definition hP A 0 C 0
  rw [h₁]
  <;> simp [zero_sub, sub_zero]
  <;> rfl

theorem archetype_A22_cross_ratio_shift_invariance {P : B} (hP : P * P = P)
    (A C X₁ X₂ Y₁ Y₂ : B) :
    operatorCrossRatio P (X₁ + A) (X₂ + A) (Y₁ + C) (Y₂ + C) =
      operatorCrossRatio P X₁ X₂ Y₁ Y₂ := by
  have h₁ : operatorCrossRatio P (X₁ + A) (X₂ + A) (Y₁ + C) (Y₂ + C) =
      genV P ((X₁ + A) - (X₂ + A)) ((Y₁ + C) - (Y₂ + C)) := by
    exact archetype_A22_cross_ratio_definition hP (X₁ + A) (X₂ + A) (Y₁ + C) (Y₂ + C)
  have h₂ : operatorCrossRatio P X₁ X₂ Y₁ Y₂ = genV P (X₁ - X₂) (Y₁ - Y₂) := by
    exact archetype_A22_cross_ratio_definition hP X₁ X₂ Y₁ Y₂
  rw [h₁, h₂]
  <;> simp [add_assoc, add_comm, add_left_comm, add_sub_cancel, sub_add_cancel]
  <;> rfl

theorem archetype_A22_cross_ratio_conjPlus_invariance {P : B} (hP : P * P = P)
    (X₁ X₂ Y₁ Y₂ : B) :
    conjPlus P (X₁ - X₂) (operatorCrossRatio P X₁ X₂ Y₁ Y₂) =
      operatorCrossRatio P X₁ X₂ Y₁ Y₂ := by
  have h₁ : operatorCrossRatio P X₁ X₂ Y₁ Y₂ = genV P (X₁ - X₂) (Y₁ - Y₂) := by
    exact archetype_A22_cross_ratio_definition hP X₁ X₂ Y₁ Y₂
  rw [h₁]
  have h₂ : conjPlus P (X₁ - X₂) (genV P (X₁ - X₂) (Y₁ - Y₂)) = genV P (X₁ - X₂) (Y₁ - Y₂) := by
    have h₃ := archetype_A14_unipotent_bch_tetraktys_action_c1 hP (X₁ - X₂) (Y₁ - Y₂)
    exact h₃
  rw [h₂]
  <;> rw [h₁]

theorem archetype_A22_cross_ratio_conjMinus_invariance {P : B} (hP : P * P = P)
    (X₁ X₂ Y₁ Y₂ : B) :
    conjMinus P (Y₁ - Y₂) (operatorCrossRatio P X₁ X₂ Y₁ Y₂) =
      operatorCrossRatio P X₁ X₂ Y₁ Y₂ := by
  have h₁ : operatorCrossRatio P X₁ X₂ Y₁ Y₂ = genV P (X₁ - X₂) (Y₁ - Y₂) := by
    exact archetype_A22_cross_ratio_definition hP X₁ X₂ Y₁ Y₂
  rw [h₁]
  have h₂ : conjMinus P (Y₁ - Y₂) (genV P (X₁ - X₂) (Y₁ - Y₂)) = genV P (X₁ - X₂) (Y₁ - Y₂) := by
    have h₃ := archetype_A14_unipotent_bch_tetraktys_action_c3 hP (X₁ - X₂) (Y₁ - Y₂)
    exact h₃
  rw [h₂]
  <;> rw [h₁]

/-! ========================================================================
   ARCHETYPES A23–A25: Division-Free Hua, Symplectic Form, Jordan Triple & Zorn–Krein Norm
   ======================================================================== -/

/-! Bergman Kernel Operator `B(N₊, N₋)(X) = (1 - N₊ N₋) * X * (1 - N₋ N₊)`. -/
def bergmanOp (P A C X : B) : B :=
  (1 - conePlus P A * coneMinus P C) * X * (1 - coneMinus P C * conePlus P A)

/-! Operator Symplectic 2-Form `Ω_symp(X₁, X₂; Y₁, Y₂)` on `ℙ¹(B)`:
`comm (P(X₁) - P(X₂), Q(Y₁) - Q(Y₂))`. -/
def operatorSymplecticForm (P X₁ X₂ Y₁ Y₂ : B) : B :=
  comm (projChartPlus P X₁ - projChartPlus P X₂)
       (projChartMinus P Y₁ - projChartMinus P Y₂)

/-! Jordan Triple Product `{X, Y, Z}_JB = X * Y * Z + Z * Y * X`. -/
def jordanTriple (X Y Z : B) : B := X * Y * Z + Z * Y * X

/-! Zorn–Krein Grade-Inversion Conjugate `zornConj P X = S_P * X * S_P`. -/
def zornConj (P X : B) : B := invS P * X * invS P

/-! The Two Chiral Operator Quantum Geometric Tensors `Q₊ = N₊ N₋` and `Q₋ = N₋ N₊`. -/
def qgtPlus  (P A C : B) : B := conePlus P A * coneMinus P C
def qgtMinus (P A C : B) : B := coneMinus P C * conePlus P A

lemma qgtPlus_mul_qgtMinus {P : B} (hP : P * P = P) (A C : B) : qgtPlus P A C * qgtMinus P A C = 0 := by
  calc
    qgtPlus P A C * qgtMinus P A C = (conePlus P A * coneMinus P C) * (coneMinus P C * conePlus P A) := by rw [qgtPlus, qgtMinus]
    _ = conePlus P A * (coneMinus P C * coneMinus P C) * conePlus P A := by
      rw [mul_assoc, mul_assoc]
      <;> simp [mul_assoc]
      <;> abel
    _ = conePlus P A * 0 * conePlus P A := by rw [coneMinus_sq_zero hP]
    _ = 0 := by simp [mul_zero]

lemma qgtMinus_mul_qgtPlus {P : B} (hP : P * P = P) (A C : B) : qgtMinus P A C * qgtPlus P A C = 0 := by
  calc
    qgtMinus P A C * qgtPlus P A C = (coneMinus P C * conePlus P A) * (conePlus P A * coneMinus P C) := by rw [qgtMinus, qgtPlus]
    _ = coneMinus P C * (conePlus P A * conePlus P A) * coneMinus P C := by
      rw [mul_assoc, mul_assoc]
      <;> simp [mul_assoc]
      <;> abel
    _ = coneMinus P C * 0 * coneMinus P C := by rw [conePlus_sq_zero hP]
    _ = 0 := by simp [mul_zero]

lemma invS_sq_one {P : B} (hP : P * P = P) : invS P * invS P = 1 := by
  have h₁ : P * (1 - P) = 0 := by
    calc
      P * (1 - P) = P - P * P := by
        simp [mul_sub, sub_mul, mul_one, one_mul]
        <;> abel
      _ = P - P := by rw [hP]
      _ = 0 := by simp [sub_self]
  have h₂ : (1 - P) * P = 0 := by
    calc
      (1 - P) * P = P - P * P := by
        simp [mul_sub, sub_mul, mul_one, one_mul]
        <;> abel
      _ = P - P := by rw [hP]
      _ = 0 := by simp [sub_self]
  have h₃ : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by
        simp [mul_sub, sub_mul, mul_one, one_mul]
        <;> abel
      _ = 1 - P - P + P := by rw [hP]
      _ = 1 - P := by abel
  calc
    invS P * invS P = (P - (1 - P)) * (P - (1 - P)) := by rw [invS]
    _ = P * P - P * (1 - P) - (1 - P) * P + (1 - P) * (1 - P) := by
      simp [mul_sub, sub_mul, mul_one, one_mul]
      <;> abel
    _ = P - 0 - 0 + (1 - P) := by
      rw [h₁, h₂, h₃]
      <;> simp [hP]
      <;> abel
    _ = 1 := by abel

macro "peirce_abel_zorn" hP:ident : tactic =>
  `(tactic| (
    simp only [bergmanOp, operatorSymplecticForm, jordanTriple, zornConj,
               operatorCrossRatio, projChartPlus, projChartMinus,
               weylJ, weylJInv, weylPhi,
               steinbergBraid, steinbergBraidInv, steinbergBraidDual, steinbergBraidDualInv,
               hProjV, hProjPhi, hProjJ, hProjSig,
               conjPlus, conjPlusInv, conjMinus, conjMinusInv,
               projV, projPhi, projJ, projSig, derivCasimir,
               derivSqPhi, derivSqJ, derivSqSig,
               ladderSum, ladderMinus, ladderPlus,
               sandwichCross, sandwichSame,
               genPhi, genJ, genV, genSig,
               evenGrade, oddGrade, peirce11, peirce00,
               invS, comm, anticomm, conePlus, coneMinus,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_zero, zero_mul, sub_self,
               mul_assoc, $hP:ident, P_assoc $hP:ident, P_assoc_right $hP:ident,
               conePlus_mul_P $hP:ident, P_mul_coneMinus $hP:ident,
               P_mul_conePlus $hP:ident, coneMinus_mul_P $hP:ident,
               conePlus_sq_zero $hP:ident, coneMinus_sq_zero $hP:ident]
    abel))

/-! ### Archetype A23: Division-Free Hua–Bergman Identity -/

/-- Correct action of the two-sided Bergman sandwich on Peirce generators.
The `N₊` component acquires two left factors, the `N₋` component is fixed,
and the two unipotent conjugates have distinct ordered correction terms. -/
theorem archetype_A23_division_free_hua_and_bergman_kernel
    {P : B} (hP : P * P = P) (A C : B) :
    bergmanOp P A C 1 = 1 - genV P A C ∧
    bergmanOp P A C (conePlus P A) =
      (1 - genV P A C) * (1 - genV P A C) * conePlus P A ∧
    bergmanOp P A C (coneMinus P C) = coneMinus P C ∧
    bergmanOp P A C (genPhi P A C) =
      (1 - genV P A C) * (1 - genV P A C) * conePlus P A + coneMinus P C ∧
    bergmanOp P A C (genV P A C) = (1 - genV P A C) * genV P A C ∧
    conjPlus P A (1 - coneMinus P C * conePlus P A) =
      1 - coneMinus P C * conePlus P A - genV P A C * conePlus P A ∧
    conjMinusInv P C (1 - conePlus P A * coneMinus P C) =
      1 - conePlus P A * coneMinus P C + genV P A C * coneMinus P C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel_zorn hP

/-! ### Archetype A24: Operator Symplectic 2-Form on `ℙ¹(B)` & Möbius Laws -/

theorem archetype_A24_operator_symplectic_form_moebius_laws
    {P : B} (hP : P * P = P) (A C X₁ X₂ Y₁ Y₂ : B) :
    operatorSymplecticForm P X₁ X₂ Y₁ Y₂ = genSig P (X₁ - X₂) (Y₁ - Y₂) ∧
    operatorSymplecticForm P A 0 C 0 = genSig P A C ∧
    operatorSymplecticForm P (X₁ + A) (X₂ + A) (Y₁ + C) (Y₂ + C) =
      operatorSymplecticForm P X₁ X₂ Y₁ Y₂ ∧
    invS P * operatorSymplecticForm P X₁ X₂ Y₁ Y₂ =
      operatorCrossRatio P X₁ X₂ Y₁ Y₂ ∧
    genPhi P A C * operatorSymplecticForm P A 0 C 0 * genPhi P A C =
      -(genV P A C * operatorSymplecticForm P A 0 C 0) ∧
    genJ P A C * operatorSymplecticForm P A 0 C 0 * (-genJ P A C) =
      -(genV P A C * operatorSymplecticForm P A 0 C 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel_zorn hP

/-! ### Archetype A25: JB-Algebra Triple Product & Zorn–Krein Split-Octonion Norm -/

theorem archetype_A25_jordan_triple_and_zorn_krein_split_norm
    {P : B} (hP : P * P = P) (A C : B) :
    jordanTriple (conePlus P A) (coneMinus P C) (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    jordanTriple (coneMinus P C) (conePlus P A) (coneMinus P C) =
      (2 : ℤ) • (genV P A C * coneMinus P C) ∧
    jordanTriple (genPhi P A C) (genPhi P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    jordanTriple (genPhi P A C) (genJ P A C) (genPhi P A C) =
      -((2 : ℤ) • (genV P A C * genJ P A C)) ∧
    zornConj P (genV P A C + genPhi P A C) = genV P A C - genPhi P A C ∧
    zornConj P (genV P A C + genJ P A C) = genV P A C - genJ P A C ∧
    (genV P A C + genPhi P A C) * zornConj P (genV P A C + genPhi P A C) =
      genV P A C * genV P A C - genV P A C ∧
    (genV P A C + genJ P A C) * zornConj P (genV P A C + genJ P A C) =
      genV P A C * genV P A C + genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel_zorn hP

/-! ========================================================================
   ARCHETYPES A₂₆–A₂₈: Chiral Parity Supercharge Algebra & SUSY Cohomology
   ======================================================================== -/

/-! ### Stage 2: Chiral Parity Supercharges & Graded Super-Derivations -/

/-- The Metric (Levi-Civita / Hodge) Connection `∇_V(X) = [V, X]`. -/
def connV     (P A C X : B) : B := comm (genV P A C) X

/-- The Berry Curvature Connection `∇_Σ(X) = [Σ, X]`. -/
def connSig   (P A C X : B) : B := comm (genSig P A C) X

/-- The (+) and (-) Amari–Nagaoka Connections `∇^(±)(X) = [Q_±, X]`. -/
def connPlus  (P A C X : B) : B := comm (qgtPlus P A C) X
def connMinus (P A C X : B) : B := comm (qgtMinus P A C) X

/-- Chiral Parity Conjugation `parityConj P X = S * X * S` where `S = invS P = 2P - 1`. -/
def parityConj (P X : B) : B := invS P * X * invS P

/-- **The Graded Super-Derivation (Coboundary Operator) `d_+(X) = N₊ * X - (S * X * S) * N₊`:**
On even-parity elements (`S X S = X`), `d_+(X) = [N₊, X]`;
on odd-parity elements (`S X S = -X`), `d_+(X) = {N₊, X}`. -/
def superDerivPlus (P A X : B) : B :=
  conePlus P A * X - parityConj P X * conePlus P A

/-- **The Graded Super-Derivation `d_-(X) = N₋ * X - (S * X * S) * N₋`. -/
def superDerivMinus (P C X : B) : B :=
  coneMinus P C * X - parityConj P X * coneMinus P C

/-- **The Dual Graded Super-Derivations `d̄_±(X) = N_± * X + (S * X * S) * N_±`. -/
def superDerivPlusBar (P A X : B) : B :=
  conePlus P A * X + parityConj P X * conePlus P A

def superDerivMinusBar (P C X : B) : B :=
  coneMinus P C * X + parityConj P X * coneMinus P C

/-- **Total Dirac–Kähler Graded Super-Derivations `d_Φ = d_+ + d_-` and `d_J = d_+ - d_-`. -/
def superDerivPhi (P A C X : B) : B :=
  superDerivPlus P A X + superDerivMinus P C X

def superDerivJ (P A C X : B) : B :=
  superDerivPlus P A X - superDerivMinus P C X

macro "peirce_abel_susy" hP:ident : tactic =>
  `(tactic| (
    simp only [superDerivPhi, superDerivJ,
               superDerivPlus, superDerivMinus,
               superDerivPlusBar, superDerivMinusBar,
               parityConj,
               connV, connSig, connPlus, connMinus,
               qgtPlus, qgtMinus,
               genPhi, genJ, genV, genSig,
               evenGrade, oddGrade, peirce11, peirce00,
               invS, comm, anticomm, conePlus, coneMinus,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_zero, zero_mul, sub_self,
               mul_assoc, $hP:ident, P_assoc $hP:ident, P_assoc_right $hP:ident,
               conePlus_mul_P $hP:ident, P_mul_coneMinus $hP:ident,
               P_mul_conePlus $hP:ident, coneMinus_mul_P $hP:ident,
               conePlus_sq_zero $hP:ident, coneMinus_sq_zero $hP:ident,
               qgtPlus_mul_qgtMinus $hP:ident, qgtMinus_mul_qgtPlus $hP:ident,
               invS_sq_one $hP:ident]
    abel))

/-! ### Archetype A₂₆: Amari–Nagaoka Dually Flat Connections (`∇^(+), ∇^(-), ∇_V, ∇_Σ`) -/

theorem archetype_A26_amari_nagaoka_dually_flat_connections
    {P : B} (hP : P * P = P) (A C X : B) :
    connPlus P A C X + connMinus P A C X = connV P A C X ∧
    connPlus P A C X - connMinus P A C X = connSig P A C X ∧
    (2 : ℤ) • connPlus P A C X = connV P A C X + connSig P A C X ∧
    (2 : ℤ) • connMinus P A C X = connV P A C X - connSig P A C X ∧
    connPlus P A C (connMinus P A C X) = connMinus P A C (connPlus P A C X) ∧
    connV P A C (connSig P A C X) = connSig P A C (connV P A C X) ∧
    connPlus P A C (connMinus P A C X) =
      -(qgtPlus P A C * X * qgtMinus P A C + qgtMinus P A C * X * qgtPlus P A C) ∧
    connV P A C (conePlus P A) = 0 ∧
    connV P A C (coneMinus P C) = 0 ∧
    connV P A C (genPhi P A C) = 0 ∧
    connV P A C (genJ P A C) = 0 ∧
    connPlus P A C (conePlus P A) = genV P A C * conePlus P A ∧
    connMinus P A C (conePlus P A) = -(genV P A C * conePlus P A) ∧
    connPlus P A C (coneMinus P C) = -(genV P A C * coneMinus P C) ∧
    connMinus P A C (coneMinus P C) = genV P A C * coneMinus P C ∧
    connPlus P A C (genPhi P A C) = genV P A C * genJ P A C ∧
    connMinus P A C (genPhi P A C) = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_abel_susy hP

/-! ### Archetype A₂₇: Chiral Parity Supercharge Algebra (`S = 2P - 1`, `N_±`, `Φ`, `J`, `Q_±`) -/

/-- **Theorem A₂₇.1 (The `N = 2` Chiral Parity Supercharge & Witten Index Algebra):**
For ANY idempotent `P * P = P` and ANY `A, C : B`:
1. **Chiral Eigen-Relations of `N_+` and `N_-` under `S = invS P`:**
   - `S * N₊ = +N₊` and `N₊ * S = -N₊`,
   - `S * N₋ = -N₋` and `N₋ * S = +N₋`,
   - `{S, N₊} = 0` and `{S, N₋} = 0`,
   - `[S, N₊] = +2 N₊` and `[S, N₋] = -2 N₋`.
2. **Chiral Parity Duality Between `Φ` and `J` (`J = S Φ = -Φ S`):**
   - `S * Φ = J` and `Φ * S = -J`,
   - `S * J = Φ` and `J * S = -Φ`,
   - `{S, Φ} = 0` and `{S, J} = 0`.
3. **Chiral Eigen-Projection of the Quantum Geometric Tensor (`S Q_± = ± Q_±`):**
   - `S * Q_+ = Q_+` and `Q_+ * S = Q_+` (even parity),
   - `S * Q_- = -Q_-` and `Q_- * S = -Q_-` (odd parity),
   - `[S, V] = 0` and `[S, Σ] = 0` (both even parity)! -/
theorem archetype_A27_chiral_parity_supercharge_algebra
    {P : B} (hP : P * P = P) (A C : B) :
    -- 1. Chiral Eigen-Relations of `N_+` and `N_-` under `S = invS P`:
    invS P * conePlus P A = conePlus P A ∧
    conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C = -coneMinus P C ∧
    coneMinus P C * invS P = coneMinus P C ∧
    anticomm (invS P) (conePlus P A) = 0 ∧
    anticomm (invS P) (coneMinus P C) = 0 ∧
    -- 2. Chiral Parity Twist Relating `Φ` and `J` (`S Φ = J`, `S J = Φ`):
    invS P * genPhi P A C = genJ P A C ∧
    genPhi P A C * invS P = -genJ P A C ∧
    invS P * genJ P A C = genPhi P A C ∧
    genJ P A C * invS P = -genPhi P A C ∧
    anticomm (invS P) (genPhi P A C) = 0 ∧
    anticomm (invS P) (genJ P A C) = 0 ∧
    -- 3. Chiral Parity Eigenvalues of `Q_+` (`+1`) and `Q_-` (`-1`) & Parity of `(V, Σ, Φ, J)`:
    invS P * qgtPlus P A C = qgtPlus P A C ∧
    invS P * qgtMinus P A C = -qgtMinus P A C ∧
    parityConj P (genV P A C) = genV P A C ∧
    parityConj P (genSig P A C) = genSig P A C ∧
    parityConj P (genPhi P A C) = -genPhi P A C ∧
    parityConj P (genJ P A C) = -genJ P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_abel_susy hP

/-! ### Archetype A₂₈: Graded Super-Derivations and Operator Identities -/

/-- **Theorem A₂₈.1 (Universal Cochain Nilpotency and Mixed Operator Identities):**
For ANY idempotent `P * P = P` and ANY `A, C, X, Y : B`:
1. **Exact Cochain Nilpotency (`d_+²(X) = 0`, `d_-²(X) = 0`, `d̄_+²(X) = 0`, `d̄_-²(X) = 0`):**
   - `d_+(d_+(X)) = 0`,
   - `d_-(d_-(X)) = 0`,
   - `d̄_+(d̄_+(X)) = 0`,
   - `d̄_-(d̄_-(X)) = 0`.
2. **Universal Graded Leibniz Rule on the Entire Ring `B`:**
   `d_+(X * Y) = d_+(X) * Y + (S X S) * d_+(Y)`
   and
   `d_-(X * Y) = d_-(X) * Y + (S X S) * d_-(Y)`.
3. **Supersymmetric Hodge Factorization of the Metric Connection `∇_V` (`{d_+, d_-} = ∇_V`):**
   - `d_+(d_-(X)) + d_-(d_+(X)) = [V, X] = ∇_V(X)`,
   - `d_Φ(d_Φ(X)) = ∇_V(X)`,
   - `d_J(d_J(X)) = -∇_V(X)`,
   - `d_Φ(d_J(X)) + d_J(d_Φ(X)) = 0`!
4. **Mixed Anticommutator Identity:**
   `d_+(d̄_-(X)) + d̄_-(d_+(X)) = V * X + X * V = {V, X}`.
   This is the anticommutator with `V`; it is not the commutator connection
   `[Σ, X]` defined separately above. -/
theorem archetype_A28_graded_superderivations_and_susy_connection_factorization
    {P : B} (hP : P * P = P) (A C X Y : B) :
    -- 1. Universal Cochain Nilpotency (`d_+² = 0`, `d_-² = 0`, `d̄_+² = 0`, `d̄_-² = 0` on ALL `X : B`):
    superDerivPlus P A (superDerivPlus P A X) = 0 ∧
    superDerivMinus P C (superDerivMinus P C X) = 0 ∧
    superDerivPlusBar P A (superDerivPlusBar P A X) = 0 ∧
    superDerivMinusBar P C (superDerivMinusBar P C X) = 0 ∧
    -- 2. Universal Graded Leibniz Rule (`d_±(X Y) = d_±(X) Y + (S X S) d_±(Y)`):
    superDerivPlus P A (X * Y) =
      superDerivPlus P A X * Y + parityConj P X * superDerivPlus P A Y ∧
    superDerivMinus P C (X * Y) =
      superDerivMinus P C X * Y + parityConj P X * superDerivMinus P C Y ∧
    -- 3. Exact Supersymmetric Factorization of the Metric Connection `∇_V` (`{d_+, d_-} = ∇_V`):
    superDerivPlus P A (superDerivMinus P C X) +
      superDerivMinus P C (superDerivPlus P A X) = connV P A C X ∧
    superDerivPhi P A C (superDerivPhi P A C X) = connV P A C X ∧
    superDerivJ P A C (superDerivJ P A C X) = -connV P A C X ∧
    superDerivPhi P A C (superDerivJ P A C X) +
      superDerivJ P A C (superDerivPhi P A C X) = 0 ∧
    -- 4. Mixed anticommutator identity `{V, X}`:
    superDerivPlus P A (superDerivMinusBar P C X) +
      superDerivMinusBar P C (superDerivPlus P A X) = genV P A C * X + X * genV P A C ∧
    -- 5. Action of `d_+` and `d_-` on the Supercharges `(N_+, N_-)` Produces `V`:
    superDerivPlus P A (coneMinus P C) = genV P A C ∧
    superDerivMinus P C (conePlus P A) = genV P A C ∧
    superDerivPlusBar P A (coneMinus P C) = genSig P A C ∧
    superDerivMinusBar P C (conePlus P A) = -genSig P A C := by
  have h₁ : superDerivPlus P A (superDerivPlus P A X) = 0 := by peirce_abel_susy hP
  have h₂ : superDerivMinus P C (superDerivMinus P C X) = 0 := by peirce_abel_susy hP
  have h₃ : superDerivPlusBar P A (superDerivPlusBar P A X) = 0 := by peirce_abel_susy hP
  have h₄ : superDerivMinusBar P C (superDerivMinusBar P C X) = 0 := by peirce_abel_susy hP
  have h₅ : superDerivPlus P A (X * Y) = superDerivPlus P A X * Y + parityConj P X * superDerivPlus P A Y := by peirce_abel_susy hP
  have h₆ : superDerivMinus P C (X * Y) = superDerivMinus P C X * Y + parityConj P X * superDerivMinus P C Y := by peirce_abel_susy hP
  have h₇ : superDerivPlus P A (superDerivMinus P C X) + superDerivMinus P C (superDerivPlus P A X) = connV P A C X := by peirce_abel_susy hP
  have h₈ : superDerivPhi P A C (superDerivPhi P A C X) = connV P A C X := by peirce_abel_susy hP
  have h₉ : superDerivJ P A C (superDerivJ P A C X) = -connV P A C X := by peirce_abel_susy hP
  have h₁₀ : superDerivPhi P A C (superDerivJ P A C X) + superDerivJ P A C (superDerivPhi P A C X) = 0 := by peirce_abel_susy hP
  have h₁₁ : superDerivPlus P A (superDerivMinusBar P C X) + superDerivMinusBar P C (superDerivPlus P A X) = genV P A C * X + X * genV P A C := by peirce_abel_susy hP
  have h₁₂ : superDerivPlus P A (coneMinus P C) = genV P A C := by peirce_abel_susy hP
  have h₁₃ : superDerivMinus P C (conePlus P A) = genV P A C := by peirce_abel_susy hP
  have h₁₄ : superDerivPlusBar P A (coneMinus P C) = genSig P A C := by peirce_abel_susy hP
  have h₁₅ : superDerivMinusBar P C (conePlus P A) = -genSig P A C := by
    have h_reflection :
        invS P * conePlus P A * invS P = -conePlus P A := by
      simp only [invS, conePlus]
      noncomm_ring [hP, P_assoc hP]
    calc
      superDerivMinusBar P C (conePlus P A)
        = coneMinus P C * conePlus P A + parityConj P (conePlus P A) * coneMinus P C := by rw [superDerivMinusBar]
      _ = coneMinus P C * conePlus P A + (-conePlus P A) * coneMinus P C := by
        rw [parityConj, h_reflection]
      _ = coneMinus P C * conePlus P A - conePlus P A * coneMinus P C := by
        noncomm_ring
      _ = -(conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) := by
        noncomm_ring
      _ = -genSig P A C := by
        rw [genSig, comm]
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅⟩

end InfoGeometry.PureNonCommutativeOperatorSpine
