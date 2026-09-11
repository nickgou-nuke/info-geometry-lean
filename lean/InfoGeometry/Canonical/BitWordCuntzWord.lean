import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Canonical.BitWordCuntzWord

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.CuntzTensorQuotient

abbrev Target := CuntzAlg 2

def letter (b : Bool) : Target :=
  if b then cuntzS 2 1 else cuntzS 2 0

def eval : (n : ℕ) → BitWord n → Target
  | 0, _ => 1
  | n + 1, w => letter (w 0) * eval n (fun i => w i.succ)

@[simp] theorem eval_zero (w : BitWord 0) : eval 0 w = 1 := rfl

@[simp] theorem eval_succ (n : ℕ) (w : BitWord (n + 1)) :
    eval (n + 1) w = letter (w 0) * eval n (fun i => w i.succ) := rfl

@[simp] theorem letter_false : letter false = cuntzS 2 0 := by rfl

@[simp] theorem letter_true : letter true = cuntzS 2 1 := by rfl

def matrixUnitWord (n : ℕ) (i j : BitWord n) : Target :=
  eval n i * star (eval n j)

@[simp] theorem matrixUnitWord_zero (i j : BitWord 0) :
    matrixUnitWord 0 i j = 1 := by
  simp [matrixUnitWord]

theorem matrixUnitWord_succ (n : ℕ) (i j : BitWord (n + 1)) :
    matrixUnitWord (n + 1) i j =
      (letter (i 0) * eval n (fun k => i k.succ)) *
        star (letter (j 0) * eval n (fun k => j k.succ)) := by
  rfl

end InfoGeometry.Canonical.BitWordCuntzWord
