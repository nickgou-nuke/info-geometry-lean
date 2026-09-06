import Mathlib

/-!
# Projective Cuntz--Toeplitz CAR/CCR finite algebra

This file records finite algebraic identities:

* the supergrading is visible on alternating `+ - + - ...` binary/qubit words;
* Fibonacci substitution supplies the `PSL(2,ℤ)`/continued-fraction matrix seed;
* projective geometry enters because Möbius transformations are invariant under
  nonzero scalar rescaling of the representing `2×2` matrix.
-/

noncomputable section

namespace ProjectiveCuntzToeplitzCARCCR

open Matrix

/-! ## Alternating supergrading on binary words -/

/-- Finite binary/qubit word. -/
abbrev BinaryWord (n : ℕ) : Type := Fin n → Bool

/-- Infinite binary/qubit word. -/
abbrev InfiniteBinaryWord : Type := ℕ → Bool

/-- Alternating `+1,-1,+1,-1,...` sign chain. -/
def alternatingSign (k : ℕ) : ℤ := if k % 2 = 0 then 1 else -1

@[simp] theorem alternatingSign_sq (k : ℕ) : alternatingSign k * alternatingSign k = 1 := by
  unfold alternatingSign
  split <;> norm_num

/-- Convert a bit to a parity sign. -/
def bitSign (b : Bool) : ℤ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> norm_num [bitSign]

/-- Finite supergrading sign of a binary word. -/
def wordParitySign {n : ℕ} (w : BinaryWord n) : ℤ :=
  ∏ i, bitSign (w i)

@[simp] theorem wordParitySign_sq {n : ℕ} (w : BinaryWord n) :
    wordParitySign w * wordParitySign w = 1 := by
  classical
  unfold wordParitySign
  rw [← Finset.prod_mul_distrib]
  simp

/-! ## Fibonacci / PSL(2,Z) seed -/

/-- Fibonacci substitution / continued-fraction generator. -/
def FibM : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1;
     1, 0]

@[simp] theorem FibM_det : FibM.det = -1 := by
  rw [Matrix.det_fin_two]
  norm_num [FibM]

/-- Fibonacci matrix identity `F²=F+I`. -/
theorem FibM_sq : FibM * FibM = FibM + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [FibM, Matrix.mul_apply, Fin.sum_univ_two]

/-- Fibonacci numbers with `F₀=0,F₁=1`. -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

@[simp] theorem fib_zero : fib 0 = 0 := rfl
@[simp] theorem fib_one : fib 1 = 1 := rfl
@[simp] theorem fib_two : fib 2 = 1 := rfl
@[simp] theorem fib_three : fib 3 = 2 := rfl
@[simp] theorem fib_four : fib 4 = 3 := rfl
@[simp] theorem fib_five : fib 5 = 5 := rfl

/-! ## Projective Möbius action -/

/-- Fractional-linear action of a `2×2` matrix on an affine coordinate. -/
def mobius (a b c d z : ℂ) : ℂ := (a * z + b) / (c * z + d)

/-- Projective geometry enters because `M` and `λM` define the same Möbius map. -/
theorem mobius_smul_same {lam a b c d z : ℂ} (hlam : lam ≠ 0) (hden : c * z + d ≠ 0) :
    mobius (lam*a) (lam*b) (lam*c) (lam*d) z = mobius a b c d z := by
  unfold mobius
  have hden' : lam * (c * z + d) ≠ 0 := mul_ne_zero hlam hden
  field_simp [hlam, hden, hden']

/-- In particular, `M` and `-M` have identical projective action. -/
theorem mobius_neg_same {a b c d z : ℂ} (hden : c * z + d ≠ 0) :
    mobius (-a) (-b) (-c) (-d) z = mobius a b c d z := by
  simpa using mobius_smul_same (lam := (-1 : ℂ)) (a := a) (b := b) (c := c) (d := d)
    (z := z) (by norm_num) hden

/-! ## q-CCR endpoint algebra -/

/-- Algebraic q-CCR relation for one pair of formal generators.  The relation is
`a† a = δ·1 + q a a†`; for one mode, `δ=1`. -/
def qCCRRelation {A : Type*} [Mul A] [Add A] [SMul ℝ A] [OfNat A 1]
    (q : ℝ) (ann cre : A) : Prop :=
  cre * ann = (1 : A) + q • (ann * cre)

/-- At `q=0`, the q-CCR relation is the Cuntz--Toeplitz/isometry relation
`a†a=1`. -/
theorem qCCR_zero_iff {A : Type*} [Mul A] [AddCommMonoid A] [Module ℝ A]
    [OfNat A 1] (ann cre : A) :
    qCCRRelation 0 ann cre ↔ cre * ann = (1 : A) := by
  simp [qCCRRelation]

/-- At `q=-1`, the q-CCR relation is the CAR anticommutator relation. -/
theorem qCCR_minus_one_iff_CAR {A : Type*} [Mul A] [AddCommGroup A] [Module ℝ A]
    [OfNat A 1] (ann cre : A) :
    qCCRRelation (-1) ann cre ↔ cre * ann + ann * cre = (1 : A) := by
  constructor
  · intro h
    rw [qCCRRelation] at h
    rw [h]
    simp
  · intro h
    rw [qCCRRelation]
    rw [← h]
    simp

/-- At `q=+1`, the q-CCR relation is the CCR commutator relation. -/
theorem qCCR_plus_one_iff_CCR {A : Type*} [Mul A] [AddCommGroup A] [Module ℝ A]
    [OfNat A 1] (ann cre : A) :
    qCCRRelation 1 ann cre ↔ cre * ann - ann * cre = (1 : A) := by
  constructor
  · intro h
    rw [qCCRRelation] at h
    rw [h]
    simp
  · intro h
    rw [qCCRRelation]
    rw [← h]
    simp

/-- Interior q-CCR parameter domain from Kuzmin's theorem. -/
def IsInteriorQ (q : ℝ) : Prop := |q| < 1

/-- Scalar `1/sqrt(1-|q|)` associated with the interior q-CCR parameter. -/
noncomputable def qCCRNormScale (q : ℝ) : ℝ :=
  (Real.sqrt (1 - |q|))⁻¹

/-! ## Toeplitz finite shift and vacuum defect -/

/-- One-mode finite Toeplitz shift, the `2×2` truncation of the unilateral shift. -/
def toeplitzShift2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0;
     1, 0]

/-- Range projection of the finite Toeplitz shift. -/
def toeplitzRangeProj2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0;
     0, 1]

/-- Vacuum projection for the finite Toeplitz shift. -/
def vacuumProj2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, 0]

@[simp] theorem toeplitz_range_defect_projection :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) - toeplitzRangeProj2 = vacuumProj2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [toeplitzRangeProj2, vacuumProj2]

/-- The finite vacuum defect is a projection. -/
@[simp] theorem vacuumProj2_idempotent : vacuumProj2 * vacuumProj2 = vacuumProj2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vacuumProj2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite Toeplitz shift has initial projection equal to the vacuum projection. -/
@[simp] theorem toeplitzShift2_star_mul_self :
    toeplitzShift2ᵀ * toeplitzShift2 = vacuumProj2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toeplitzShift2, vacuumProj2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite Toeplitz shift has range projection `SS*`. -/
@[simp] theorem toeplitzShift2_mul_star_self :
    toeplitzShift2 * toeplitzShift2ᵀ = toeplitzRangeProj2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toeplitzShift2, toeplitzRangeProj2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite range projection is a projection. -/
@[simp] theorem toeplitzRangeProj2_idempotent :
    toeplitzRangeProj2 * toeplitzRangeProj2 = toeplitzRangeProj2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toeplitzRangeProj2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Vacuum and range projections are orthogonal. -/
@[simp] theorem vacuum_range_orthogonal :
    vacuumProj2 * toeplitzRangeProj2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vacuumProj2, toeplitzRangeProj2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Range and vacuum projections are orthogonal in the opposite order too. -/
@[simp] theorem range_vacuum_orthogonal :
    toeplitzRangeProj2 * vacuumProj2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vacuumProj2, toeplitzRangeProj2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The vacuum/range pair resolves the identity in the finite Toeplitz model. -/
theorem vacuum_range_partition :
    vacuumProj2 + toeplitzRangeProj2 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [vacuumProj2, toeplitzRangeProj2]

end ProjectiveCuntzToeplitzCARCCR
