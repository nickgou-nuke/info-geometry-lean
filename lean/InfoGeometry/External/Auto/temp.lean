import Mathlib

abbrev Q := ℚ

def allOnes3 : Matrix (Fin 3) (Fin 3) Q := 1

def alternatingFourEntryProduct (V : Matrix (Fin 3) (Fin 3) Q) : Q :=
  V 0 1 * V 1 2 * V 0 2 * V 1 1 - V 0 2 * V 1 1 * V 0 1 * V 1 2

def allOnesAlternatingProduct : Q := alternatingFourEntryProduct allOnes3

theorem allOnesAlternatingProduct_eq_zero : allOnesAlternatingProduct = 0 := by
  dsimp [allOnesAlternatingProduct, alternatingFourEntryProduct, allOnes3]
  norm_num [Matrix.one_apply]
