import Mathlib

/-! Native symmetric `ℤ₂` block grading of the split `(5,5)` matrix carrier.
The external generator-count artifact is intentionally not imported; the
structural matrix theorem is independent of that enumeration.
-/
noncomputable section
namespace InfoGeometry.Clifford.O55SymmetricBlockGrading

open Matrix
abbrev SplitIndex := Fin 5 ⊕ Fin 5
abbrev Mat55 := Matrix SplitIndex SplitIndex ℝ

def splitMetric : Mat55 := Matrix.fromBlocks 1 0 0 (-1)

@[simp] theorem splitMetric_sq : splitMetric * splitMetric = (1 : Mat55) := by
  rw [splitMetric, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

def cartanInvolution (X : Mat55) : Mat55 := splitMetric * X * splitMetric

@[simp] theorem cartanInvolution_involutive (X : Mat55) :
    cartanInvolution (cartanInvolution X) = X := by
  unfold cartanInvolution
  calc
    splitMetric * (splitMetric * X * splitMetric) * splitMetric =
        (splitMetric * splitMetric) * X * (splitMetric * splitMetric) := by
          noncomm_ring
    _ = X := by rw [splitMetric_sq]; simp

theorem cartanInvolution_add (X Y : Mat55) :
    cartanInvolution (X + Y) = cartanInvolution X + cartanInvolution Y := by
  unfold cartanInvolution
  simp only [mul_add, add_mul]

theorem cartanInvolution_sub (X Y : Mat55) :
    cartanInvolution (X - Y) = cartanInvolution X - cartanInvolution Y := by
  unfold cartanInvolution
  simp only [mul_sub, sub_mul]

theorem cartanInvolution_mul (X Y : Mat55) :
    cartanInvolution (X * Y) = cartanInvolution X * cartanInvolution Y := by
  unfold cartanInvolution
  calc
    splitMetric * (X * Y) * splitMetric =
        (splitMetric * X * splitMetric) *
          (splitMetric * Y * splitMetric) := by
            rw [show (splitMetric * X * splitMetric) *
                (splitMetric * Y * splitMetric) =
                splitMetric * X * (splitMetric * splitMetric) * Y * splitMetric by
                  noncomm_ring]
            rw [splitMetric_sq]
            simp only [mul_one, mul_assoc]

def commutator (X Y : Mat55) : Mat55 := X * Y - Y * X
def IsEven (X : Mat55) : Prop := cartanInvolution X = X
def IsOdd (X : Mat55) : Prop := cartanInvolution X = -X

theorem cartanInvolution_commutator (X Y : Mat55) :
    cartanInvolution (commutator X Y) =
      commutator (cartanInvolution X) (cartanInvolution Y) := by
  change cartanInvolution (X * Y - Y * X) =
    cartanInvolution X * cartanInvolution Y -
      cartanInvolution Y * cartanInvolution X
  rw [cartanInvolution_sub, cartanInvolution_mul, cartanInvolution_mul]

theorem commutator_even_even {X Y : Mat55}
    (hX : IsEven X) (hY : IsEven Y) : IsEven (commutator X Y) := by
  unfold IsEven at hX hY ⊢
  rw [cartanInvolution_commutator, hX, hY]

theorem commutator_even_odd {X Y : Mat55}
    (hX : IsEven X) (hY : IsOdd Y) : IsOdd (commutator X Y) := by
  unfold IsEven at hX
  unfold IsOdd at hY ⊢
  rw [cartanInvolution_commutator, hX, hY]
  unfold commutator
  noncomm_ring

theorem commutator_odd_even {X Y : Mat55}
    (hX : IsOdd X) (hY : IsEven Y) : IsOdd (commutator X Y) := by
  unfold IsOdd at hX ⊢
  unfold IsEven at hY
  rw [cartanInvolution_commutator, hX, hY]
  unfold commutator
  noncomm_ring

theorem commutator_odd_odd {X Y : Mat55}
    (hX : IsOdd X) (hY : IsOdd Y) : IsEven (commutator X Y) := by
  unfold IsOdd at hX hY
  unfold IsEven
  rw [cartanInvolution_commutator, hX, hY]
  unfold commutator
  noncomm_ring

def IsO55Lie (X : Mat55) : Prop :=
  X.transpose * splitMetric + splitMetric * X = 0

theorem commutator_mem_o55 {X Y : Mat55}
    (hX : IsO55Lie X) (hY : IsO55Lie Y) :
    IsO55Lie (commutator X Y) := by
  unfold IsO55Lie at hX hY ⊢
  unfold commutator
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  have hX' : Xᵀ * splitMetric = -(splitMetric * X) := by
    have h := congrArg Neg.neg (neg_eq_iff_add_eq_zero.mpr hX)
    simpa only [neg_neg] using h
  have hY' : Yᵀ * splitMetric = -(splitMetric * Y) := by
    have h := congrArg Neg.neg (neg_eq_iff_add_eq_zero.mpr hY)
    simpa only [neg_neg] using h
  calc
    (Yᵀ * Xᵀ - Xᵀ * Yᵀ) * splitMetric +
        splitMetric * (X * Y - Y * X)
        = Yᵀ * (Xᵀ * splitMetric) - Xᵀ * (Yᵀ * splitMetric) +
            splitMetric * X * Y - splitMetric * Y * X := by
            noncomm_ring
    _ = Yᵀ * (-(splitMetric * X)) - Xᵀ * (-(splitMetric * Y)) +
            splitMetric * X * Y - splitMetric * Y * X := by rw [hY', hX']
    _ = -(Yᵀ * splitMetric) * X + (Xᵀ * splitMetric) * Y +
          splitMetric * X * Y - splitMetric * Y * X := by
          simp only [mul_neg, neg_mul]
          rw [← mul_assoc, ← mul_assoc]
          noncomm_ring
    _ = 0 := by
      rw [hY', hX']
      noncomm_ring

def IsO55Even (X : Mat55) : Prop := IsO55Lie X ∧ IsEven X
def IsO55Odd (X : Mat55) : Prop := IsO55Lie X ∧ IsOdd X

theorem o55_even_even {X Y : Mat55} (hX : IsO55Even X) (hY : IsO55Even Y) :
    IsO55Even (commutator X Y) :=
  ⟨commutator_mem_o55 hX.1 hY.1, commutator_even_even hX.2 hY.2⟩

theorem o55_even_odd {X Y : Mat55} (hX : IsO55Even X) (hY : IsO55Odd Y) :
    IsO55Odd (commutator X Y) :=
  ⟨commutator_mem_o55 hX.1 hY.1, commutator_even_odd hX.2 hY.2⟩

theorem o55_odd_odd {X Y : Mat55} (hX : IsO55Odd X) (hY : IsO55Odd Y) :
    IsO55Even (commutator X Y) :=
  ⟨commutator_mem_o55 hX.1 hY.1, commutator_odd_odd hX.2 hY.2⟩

end InfoGeometry.Clifford.O55SymmetricBlockGrading
end noncomputable section
