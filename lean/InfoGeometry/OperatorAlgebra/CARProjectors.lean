import InfoGeometry.Physics.SplitCliffordAlgebras
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Projectors and chirality from a CAR pair

The construction is purely associative: square-zero annihilation and creation
operators produce complementary idempotents, and their difference is an
involution.
-/

namespace InfoGeometry.OperatorAlgebra.CARProjectors

open SplitClifford

variable {A : Type*} [Ring A]

def plus (P : CARPair A) : A := P.ann * P.cre

def minus (P : CARPair A) : A := P.cre * P.ann

def chirality (P : CARPair A) : A := plus P - minus P

/-- Explicit particle--hole convention swap for a CAR pair. -/
def particleHole (P : CARPair A) : CARPair A :=
  { ann := P.cre
    cre := P.ann
    ann_sq := P.cre_sq
    cre_sq := P.ann_sq
    anti := by simpa [add_comm] using P.anti }

theorem particleHole_plus (P : CARPair A) :
    plus (particleHole P) = minus P := by
  rfl

theorem particleHole_minus (P : CARPair A) :
    minus (particleHole P) = plus P := by
  rfl

theorem particleHole_chirality (P : CARPair A) :
    chirality (particleHole P) = -chirality P := by
  simp only [chirality, particleHole_plus, particleHole_minus]
  abel

theorem plus_idempotent (P : CARPair A) : plus P * plus P = plus P := by
  unfold plus
  have h : P.cre * P.ann = 1 - P.ann * P.cre := by
    apply (eq_sub_iff_add_eq).2
    rw [add_comm]
    exact P.anti
  simp only [mul_assoc]
  rw [← mul_assoc P.cre P.ann P.cre]
  rw [h]
  simp only [sub_mul, one_mul]
  simp [mul_assoc, P.cre_sq]

theorem minus_idempotent (P : CARPair A) : minus P * minus P = minus P := by
  unfold minus
  have h : P.ann * P.cre = 1 - P.cre * P.ann := by
    apply (eq_sub_iff_add_eq).2
    exact P.anti
  simp only [mul_assoc]
  rw [← mul_assoc P.ann P.cre P.ann]
  rw [h]
  simp only [sub_mul, one_mul]
  simp [mul_assoc, P.ann_sq]

theorem plus_mul_minus (P : CARPair A) : plus P * minus P = 0 := by
  unfold plus minus
  simp only [mul_assoc]
  rw [← mul_assoc P.cre P.cre P.ann]
  rw [P.cre_sq]
  simp

theorem minus_mul_plus (P : CARPair A) : minus P * plus P = 0 := by
  unfold plus minus
  simp only [mul_assoc]
  rw [← mul_assoc P.ann P.ann P.cre]
  rw [P.ann_sq]
  simp

theorem projectors_add (P : CARPair A) : plus P + minus P = 1 :=
  P.anti

theorem chirality_sq (P : CARPair A) : chirality P * chirality P = 1 := by
  unfold chirality
  simp only [sub_mul, mul_sub]
  rw [plus_idempotent, minus_idempotent, plus_mul_minus, minus_mul_plus]
  simpa [sub_eq_add_neg, add_assoc] using projectors_add P

end InfoGeometry.OperatorAlgebra.CARProjectors
