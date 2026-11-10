/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Integer and cyclotomic readouts of the canonical operator-word charge

The generator and word charge are owned by the native OperatorAlgebra owner.
This file adds only the Algebra-layer grade/readout constructions.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

def ChiralWordGrade (k : ℤ) :=
  {w : List ChiralGenerator // wordDegree w = k}

def chiralChargeModThree (k : ℤ) : ZMod 3 := k

def chiralChargeModThreeHom : ℤ →+ ZMod 3 := Int.castAddHom (ZMod 3)

@[simp] theorem chiralChargeModThree_zero :
    chiralChargeModThree 0 = 0 := by
  change ((0 : ℤ) : ZMod 3) = 0
  norm_num

@[simp] theorem chiralChargeModThree_neg (k : ℤ) :
    chiralChargeModThree (-k) = -chiralChargeModThree k := by
  change ((-k : ℤ) : ZMod 3) = -((k : ℤ) : ZMod 3)
  rw [Int.cast_neg]

def chiralWordCyclotomicCharge
    (w : List ChiralGenerator) : ZMod 3 :=
  chiralChargeModThree (wordDegree w)

theorem chiralChargeModThree_add (r s : ℤ) :
    chiralChargeModThree (r + s) =
      chiralChargeModThree r + chiralChargeModThree s := by
  change ((r + s : ℤ) : ZMod 3) =
    (r : ZMod 3) + (s : ZMod 3)
  rw [Int.cast_add]

theorem chiralChargeModThree_period_three (k : ℤ) :
    chiralChargeModThree (k + 3) = chiralChargeModThree k := by
  rw [chiralChargeModThree_add]
  change (k : ZMod 3) + (3 : ZMod 3) = (k : ZMod 3)
  have hthree : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  rw [hthree, add_zero]

theorem chiralChargeModThreeHom_apply (k : ℤ) :
    chiralChargeModThreeHom k = chiralChargeModThree k ∧
    chiralChargeModThree (k + 3) = chiralChargeModThree k := by
  constructor
  · rfl
  · exact chiralChargeModThree_period_three k

theorem chiralChargeModThree_pos_two_eq_neg_one :
    chiralChargeModThree 2 = chiralChargeModThree (-1) := by
  calc
    chiralChargeModThree 2 = chiralChargeModThree ((-1 : ℤ) + 3) := by
      exact congrArg chiralChargeModThree (by norm_num : (2 : ℤ) = -1 + 3)
    _ = chiralChargeModThree (-1) := chiralChargeModThree_period_three (-1)

theorem chiralChargeModThree_neg_two_eq_pos_one :
    chiralChargeModThree (-2) = chiralChargeModThree 1 := by
  change ((-2 : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3)
  rw [ZMod.intCast_eq_intCast_iff']
  norm_num

theorem chiralWordCyclotomicCharge_append
    (u v : List ChiralGenerator) :
    chiralWordCyclotomicCharge (u ++ v) =
      chiralWordCyclotomicCharge u + chiralWordCyclotomicCharge v := by
  unfold chiralWordCyclotomicCharge
  rw [wordDegree_append, chiralChargeModThree_add]

def ChiralWordCyclotomicGrade (q : ZMod 3) :=
  {w : List ChiralGenerator // chiralWordCyclotomicCharge w = q}

def chiralWordCyclotomicGradeAppend {q r : ZMod 3}
    (u : ChiralWordCyclotomicGrade q)
    (v : ChiralWordCyclotomicGrade r) :
    ChiralWordCyclotomicGrade (q + r) :=
  ⟨u.1 ++ v.1, by
    rw [chiralWordCyclotomicCharge_append, u.2, v.2]⟩

theorem chiralWordCyclotomicGradeAppend_val {q r : ZMod 3}
    (u : ChiralWordCyclotomicGrade q)
    (v : ChiralWordCyclotomicGrade r) :
    (chiralWordCyclotomicGradeAppend u v).1 = u.1 ++ v.1 ∧
    chiralWordCyclotomicCharge
        (chiralWordCyclotomicGradeAppend u v).1 = q + r := by
  constructor
  · rfl
  · exact (chiralWordCyclotomicGradeAppend u v).2

def chiralGeneratorWordGrade
    (g : ChiralGenerator) : ChiralWordGrade (generatorDegree g) :=
  ⟨[g], by simp [wordDegree]⟩

def chiralWordGradeAppend {i j : ℤ}
    (u : ChiralWordGrade i) (v : ChiralWordGrade j) :
    ChiralWordGrade (i + j) :=
  ⟨u.1 ++ v.1, by
    rw [wordDegree_append, u.2, v.2]⟩

theorem chiralWordGradeAppend_val
    {i j : ℤ} (u : ChiralWordGrade i) (v : ChiralWordGrade j) :
    (chiralWordGradeAppend u v).1 = u.1 ++ v.1 ∧
    word (R := ℝ) (chiralWordGradeAppend u v).1 =
      word (R := ℝ) u.1 * word (R := ℝ) v.1 := by
  constructor
  · rfl
  · change word (R := ℝ) (u.1 ++ v.1) = _
    rw [word_append]

theorem chiralWordGradeAppend_operator
    {i j : ℤ} (u : ChiralWordGrade i) (v : ChiralWordGrade j) :
    word (R := ℝ) (chiralWordGradeAppend u v).1 =
      word (R := ℝ) u.1 * word (R := ℝ) v.1 := by
  change word (R := ℝ) (u.1 ++ v.1) = _
  rw [word_append]

def chiralPairWordGrade
    (g h : ChiralGenerator) :
    ChiralWordGrade (generatorDegree g + generatorDegree h) :=
  chiralWordGradeAppend
    (chiralGeneratorWordGrade g)
    (chiralGeneratorWordGrade h)

def chiralTripleWordGrade
    (g h k : ChiralGenerator) :
    ChiralWordGrade
      (generatorDegree g + generatorDegree h + generatorDegree k) :=
  chiralWordGradeAppend
    (chiralPairWordGrade g h)
    (chiralGeneratorWordGrade k)

theorem chiralTripleWordGrade_operator
    (g h k : ChiralGenerator) :
    word (R := ℝ) (chiralTripleWordGrade g h k).1 =
      word (R := ℝ) [g, h] * ofGenerator (R := ℝ) k := by
  change word (R := ℝ)
      (chiralWordGradeAppend (chiralPairWordGrade g h)
        (chiralGeneratorWordGrade k)).1 = _
  rw [chiralWordGradeAppend_operator]
  change word (R := ℝ)
      (chiralWordGradeAppend (chiralGeneratorWordGrade g)
        (chiralGeneratorWordGrade h)).1 *
      word (R := ℝ) (chiralGeneratorWordGrade k).1 = _
  rw [chiralWordGradeAppend_operator]
  simp [chiralGeneratorWordGrade, word, mul_assoc]

theorem sPlus_pair_has_charge_two (i j : Fin 3) :
    wordDegree [ChiralGenerator.sPlus i, ChiralGenerator.sPlus j] = 2 := by
  norm_num [wordDegree, generatorDegree]

theorem sPlus_triple_has_charge_three (i j k : Fin 3) :
    wordDegree [ChiralGenerator.sPlus i,
      ChiralGenerator.sPlus j, ChiralGenerator.sPlus k] = 3 := by
  norm_num [wordDegree, generatorDegree]

theorem sMinus_pair_has_charge_neg_two (i j : Fin 3) :
    wordDegree [ChiralGenerator.sMinus i, ChiralGenerator.sMinus j] = -2 := by
  norm_num [wordDegree, generatorDegree]

theorem sMinus_triple_has_charge_neg_three (i j k : Fin 3) :
    wordDegree [ChiralGenerator.sMinus i,
      ChiralGenerator.sMinus j, ChiralGenerator.sMinus k] = -3 := by
  norm_num [wordDegree, generatorDegree]

theorem mixed_pair_has_charge_zero (g h : Fin 3) :
    wordDegree [ChiralGenerator.sPlus g, ChiralGenerator.sMinus h] = 0 := by
  norm_num [wordDegree, generatorDegree]

@[simp] theorem sPlus_pair_cyclotomicCharge (i j : Fin 3) :
    chiralWordCyclotomicCharge
        [ChiralGenerator.sPlus i, ChiralGenerator.sPlus j] =
      (-1 : ZMod 3) := by
  rw [chiralWordCyclotomicCharge, sPlus_pair_has_charge_two]
  decide

@[simp] theorem sMinus_pair_cyclotomicCharge (i j : Fin 3) :
    chiralWordCyclotomicCharge
        [ChiralGenerator.sMinus i, ChiralGenerator.sMinus j] =
      (1 : ZMod 3) := by
  rw [chiralWordCyclotomicCharge, sMinus_pair_has_charge_neg_two]
  decide

@[simp] theorem sPlus_triple_cyclotomicCharge (i j k : Fin 3) :
    chiralWordCyclotomicCharge
        [ChiralGenerator.sPlus i, ChiralGenerator.sPlus j,
          ChiralGenerator.sPlus k] = 0 := by
  rw [chiralWordCyclotomicCharge, sPlus_triple_has_charge_three]
  decide

@[simp] theorem sMinus_triple_cyclotomicCharge (i j k : Fin 3) :
    chiralWordCyclotomicCharge
        [ChiralGenerator.sMinus i, ChiralGenerator.sMinus j,
          ChiralGenerator.sMinus k] = 0 := by
  rw [chiralWordCyclotomicCharge, sMinus_triple_has_charge_neg_three]
  decide

@[simp] theorem mixed_pair_cyclotomicCharge (i j : Fin 3) :
    chiralWordCyclotomicCharge
        [ChiralGenerator.sPlus i, ChiralGenerator.sMinus j] = 0 := by
  rw [chiralWordCyclotomicCharge, mixed_pair_has_charge_zero]
  rfl

end InfoGeometry.Algebra
