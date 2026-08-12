import InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout

/-!
# Transported chiral Cayley product

The outer `2 × 2` quaternion-entry matrices are only a linear carrier.  The
operation below is the transported split-Cayley product; it is deliberately
not ordinary matrix multiplication.  For pure imaginary quaternion entries,
the scalar channels use anticommutators and the chiral channels use
commutators.
-/

namespace InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout

noncomputable section

private def half : ChiralEntry := (1 / 2 : ℝ) • entryOne

def chiralStar (X Y : ChiralMatrix) : ChiralMatrix :=
  !![ X 0 0 * Y 0 0 + half * (X 0 1 * Y 1 0 + Y 1 0 * X 0 1),
      X 0 0 * Y 0 1 + Y 1 1 * X 0 1 + half * (X 1 0 * Y 1 0 - Y 1 0 * X 1 0);
      Y 0 0 * X 1 0 + X 1 1 * Y 1 0 + half * (X 0 1 * Y 0 1 - Y 0 1 * X 0 1),
      X 1 1 * Y 1 1 + half * (X 1 0 * Y 0 1 + Y 0 1 * X 1 0) ]

/-- Left multiplication by a chiral element, viewed as an operator on the
carrier.  It is a function rather than an asserted associative matrix
representation; the associator records the obstruction to composing these
operators as ordinary multiplication operators. -/
def leftChiralStar (X : ChiralMatrix) : ChiralMatrix → ChiralMatrix :=
  fun Y => chiralStar X Y

def rightChiralStar (Y : ChiralMatrix) : ChiralMatrix → ChiralMatrix :=
  fun X => chiralStar X Y

def chiralAssociator (X Y Z : ChiralMatrix) : ChiralMatrix :=
  chiralStar (chiralStar X Y) Z - chiralStar X (chiralStar Y Z)

def leftProductDefect (X Y : ChiralMatrix) : ChiralMatrix → ChiralMatrix :=
  fun Z => leftChiralStar (chiralStar X Y) Z - leftChiralStar X (leftChiralStar Y Z)

def leftRightCommutatorDefect (X Y : ChiralMatrix) : ChiralMatrix → ChiralMatrix :=
  fun Z => leftChiralStar X (rightChiralStar Y Z) -
    rightChiralStar Y (leftChiralStar X Z)

/-- The two four-component chiral operator frames.  They are frames of the
carrier; neither is asserted to be a subalgebra. -/
def sheetPlus : Fin 4 → ChiralMatrix :=
  ![uPlus, uOne, uTwo, uThree]

def sheetMinus : Fin 4 → ChiralMatrix :=
  ![uMinus, vOne, vTwo, vThree]

def leftSheetAction (a : Fin 4) : ChiralMatrix → ChiralMatrix :=
  leftChiralStar (sheetPlus a)

def rightSheetAction (b : Fin 4) : ChiralMatrix → ChiralMatrix :=
  rightChiralStar (sheetMinus b)

def sheetCommutantDefect (a b : Fin 4) : ChiralMatrix → ChiralMatrix :=
  fun Z => leftSheetAction a (rightSheetAction b Z) -
    rightSheetAction b (leftSheetAction a Z)

theorem leftChiralStar_apply (X Y : ChiralMatrix) :
    leftChiralStar X Y = chiralStar X Y := rfl

theorem rightChiralStar_apply (X Y : ChiralMatrix) :
    rightChiralStar Y X = chiralStar X Y := rfl

theorem leftRightStar_defect (X Y Z : ChiralMatrix) :
    leftChiralStar X (rightChiralStar Y Z) -
        rightChiralStar Y (leftChiralStar X Z) =
      chiralStar X (chiralStar Z Y) - chiralStar (chiralStar X Z) Y := rfl

theorem leftProductDefect_apply (X Y Z : ChiralMatrix) :
    leftProductDefect X Y Z = chiralAssociator X Y Z := rfl

theorem leftRightCommutatorDefect_apply (X Y Z : ChiralMatrix) :
    leftRightCommutatorDefect X Y Z =
      chiralStar X (chiralStar Z Y) - chiralStar (chiralStar X Z) Y := rfl

theorem sheetCommutantDefect_apply (a b : Fin 4) (Z : ChiralMatrix) :
    sheetCommutantDefect a b Z =
      chiralStar (sheetPlus a) (chiralStar Z (sheetMinus b)) -
        chiralStar (chiralStar (sheetPlus a) Z) (sheetMinus b) := rfl

@[simp] theorem chiralStar_zero_left (X : ChiralMatrix) :
    chiralStar 0 X = 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half]

@[simp] theorem chiralStar_zero_right (X : ChiralMatrix) :
    chiralStar X 0 = 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half]

theorem chiralStar_uOne_uTwo : chiralStar uOne uTwo = vThree := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, uTwo, vThree, entryZero, entryI, entryJ,
      entryK] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, entryOne]

theorem chiralStar_uOne_vOne : chiralStar uOne vOne = -rhoPlus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, vOne, rhoPlus, entryZero, entryOne, entryI] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul]

theorem chiralStar_vOne_uOne : chiralStar vOne uOne = -rhoMinus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, vOne, rhoMinus, entryZero, entryOne, entryI] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul]

theorem chiralStar_associator_uOne_uTwo_uThree :
    chiralStar (chiralStar uOne uTwo) uThree ≠
      chiralStar uOne (chiralStar uTwo uThree) := by
  intro h
  have h00 := congrArg (fun M : ChiralMatrix => M 0 0) h
  have h00' := congrArg (fun q : ChiralEntry => q.re) h00
  norm_num [chiralStar_uOne_uTwo, chiralStar_uOne_vOne, rhoMinus, rhoPlus,
    chiralStar, half, uOne, uTwo, uThree, vThree, entryZero, entryOne,
    entryI, entryJ, entryK] at h00'

theorem chiralAssociator_uOne_uTwo_uThree_ne_zero :
    chiralAssociator uOne uTwo uThree ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : ChiralMatrix => M 0 0) h
  have h00' := congrArg (fun q : ChiralEntry => q.re) h00
  norm_num [chiralAssociator, chiralStar_uOne_uTwo, chiralStar_uOne_vOne,
    rhoMinus, rhoPlus, chiralStar, half, uOne, uTwo, uThree, vThree,
    entryZero, entryOne, entryI, entryJ, entryK] at h00'

end
end InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout
