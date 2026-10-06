import os
import re

with open('lean/InfoGeometry/Canonical/Cl11LeftRightDoubleBridge.lean', 'r') as f:
    content = f.read()

content = re.sub(
    r'@\[simp\] theorem leftStageTwo_mul.*?exact h\.symm',
    '''@[simp] theorem leftStageTwo_mul (A B : Atom) :
    leftStageTwo (A * B) = leftStageTwo A * leftStageTwo B := by
  dsimp [leftStageTwo]
  have h := Matrix.mul_kronecker_mul (atomToStageOne A) (atomToStageOne B) (1 : Atom) (1 : Atom)
  rw [mul_one] at h
  rw [map_mul]
  exact h''',
    content,
    flags=re.DOTALL
)

content = re.sub(
    r'@\[simp\] theorem rightStageTwo_mul.*?exact h\.symm',
    '''@[simp] theorem rightStageTwo_mul (A B : Atom) :
    rightStageTwo (A * B) = rightStageTwo A * rightStageTwo B := by
  dsimp [rightStageTwo]
  have h := Matrix.mul_kronecker_mul (1 : StageOne) (1 : StageOne) A B
  rw [mul_one] at h
  exact h''',
    content,
    flags=re.DOTALL
)

content = re.sub(
    r'theorem leftStageTwo_rightStageTwo_commute.*?rw \[← h1, ← h2\]',
    '''theorem leftStageTwo_rightStageTwo_commute (A B : Atom) :
    leftStageTwo A * rightStageTwo B =
      rightStageTwo B * leftStageTwo A := by
  have h1 := Matrix.mul_kronecker_mul (atomToStageOne A) (1 : StageOne) (1 : Atom) B
  have h2 := Matrix.mul_kronecker_mul (1 : StageOne) (atomToStageOne A) B (1 : Atom)
  rw [mul_one, one_mul] at h1
  rw [one_mul, mul_one] at h2
  exact Eq.trans h1.symm h2''',
    content,
    flags=re.DOTALL
)

content = re.sub(
    r'theorem leftStageTwo_mul_rightStageTwo.*?rw \[← h1\]',
    '''theorem leftStageTwo_mul_rightStageTwo (A B : Atom) :
    leftStageTwo A * rightStageTwo B =
      atomToStageOne A ⊗ₖ B := by
  have h1 := Matrix.mul_kronecker_mul (atomToStageOne A) (1 : StageOne) (1 : Atom) B
  rw [mul_one, one_mul] at h1
  exact h1.symm''',
    content,
    flags=re.DOTALL
)

with open('lean/InfoGeometry/Canonical/Cl11LeftRightDoubleBridge.lean', 'w') as f:
    f.write(content)
