import InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

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

def chiralWordCyclotomicCharge
    (w : List ChiralGenerator) : ZMod 3 :=
  chiralChargeModThree (wordDegree w)

theorem chiralChargeModThree_add (r s : ℤ) :
    chiralChargeModThree (r + s) =
      chiralChargeModThree r + chiralChargeModThree s := by
  exact Int.cast_add r s

theorem chiralChargeModThree_pos_two_eq_neg_one :
    chiralChargeModThree 2 = chiralChargeModThree (-1) := by
  decide

theorem chiralChargeModThree_neg_two_eq_pos_one :
    chiralChargeModThree (-2) = chiralChargeModThree 1 := by
  decide

theorem chiralWordCyclotomicCharge_append
    (u v : List ChiralGenerator) :
    chiralWordCyclotomicCharge (u ++ v) =
      chiralWordCyclotomicCharge u + chiralWordCyclotomicCharge v := by
  simp [chiralWordCyclotomicCharge, chiralChargeModThree,
    wordDegree_append]

def chiralGeneratorWordGrade
    (g : ChiralGenerator) : ChiralWordGrade (generatorDegree g) :=
  ⟨[g], by simp [wordDegree]⟩

def chiralWordGradeAppend {i j : ℤ}
    (u : ChiralWordGrade i) (v : ChiralWordGrade j) :
    ChiralWordGrade (i + j) :=
  ⟨u.1 ++ v.1, by
    rw [wordDegree_append, u.2, v.2]⟩

@[simp] theorem chiralWordGradeAppend_val {i j : ℤ}
    (u : ChiralWordGrade i) (v : ChiralWordGrade j) :
    (chiralWordGradeAppend u v).1 = u.1 ++ v.1 :=
  rfl

theorem chiralWordGradeAppend_operator
    {i j : ℤ} (u : ChiralWordGrade i) (v : ChiralWordGrade j) :
    word (R := ℝ) (chiralWordGradeAppend u v).1 =
      word (R := ℝ) u.1 * word (R := ℝ) v.1 := by
  rw [chiralWordGradeAppend_val, word_append]

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
  rw [chiralTripleWordGrade]
  simp [chiralPairWordGrade, chiralGeneratorWordGrade, word, mul_assoc]

theorem sPlus_pair_has_charge_two (i j : Fin 3) :
    wordDegree [ChiralGenerator.sPlus i, ChiralGenerator.sPlus j] = 2 := by
  simp [wordDegree, generatorDegree]

theorem sPlus_triple_has_charge_three (i j k : Fin 3) :
    wordDegree [ChiralGenerator.sPlus i,
      ChiralGenerator.sPlus j, ChiralGenerator.sPlus k] = 3 := by
  simp [wordDegree, generatorDegree]

theorem sMinus_pair_has_charge_neg_two (i j : Fin 3) :
    wordDegree [ChiralGenerator.sMinus i, ChiralGenerator.sMinus j] = -2 := by
  simp [wordDegree, generatorDegree]

theorem sMinus_triple_has_charge_neg_three (i j k : Fin 3) :
    wordDegree [ChiralGenerator.sMinus i,
      ChiralGenerator.sMinus j, ChiralGenerator.sMinus k] = -3 := by
  simp [wordDegree, generatorDegree]

theorem mixed_pair_has_charge_zero (g h : Fin 3) :
    wordDegree [ChiralGenerator.sPlus g, ChiralGenerator.sMinus h] = 0 := by
  simp [wordDegree, generatorDegree]

end InfoGeometry.Algebra
