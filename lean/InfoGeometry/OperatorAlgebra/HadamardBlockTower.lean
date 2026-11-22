/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Hadamard block tower over an operator ring

All block statements are over an arbitrary (noncommutative) ring `A`, with blocks in
`Matrix (Fin 2) (Fin 2) A`; iterating `A ↦ Matrix (Fin 2) (Fin 2) A` gives the tower.

* `H = S + Φ`, `H² = 2`, `H S H = 2Φ`, `H Φ H = 2S`, `H J H = -2J`.
* Four-channel block transform of `M = !![a,b;c,d]` and `H (H M H) H = 4 M`.
* Tower step `lift G = !![G,G;G,-G]`: `G² = k ⇒ (lift G)² = 2k`, and
  `lift G · bisym X Y · lift G = diag(2 G(X+Y)G, 2 G(X-Y)G)`.
* `H₄ = lift H`, `H₈ = lift H₄`: `H₄² = 4`, `H₈² = 8`, full diagonalisation of the
  two-level Walsh block.
* Integer Sylvester `H₈` and Paley `H₁₂`, `H₂₄ = H₂ ⊗ H₁₂` with `H Hᵀ = N`, transported to
  matrices over any operator ring.

## BUCKET 1: Kernel-verified noncommutative ring identities
The block identities and the Walsh tensor recurrence are proved over the
declared arbitrary ring carriers.

## BUCKET 2: Finite integer/combinatorial statements
The Paley and bent-spectrum results are finite-dimensional exact statements
with their stated index sets.

## BUCKET 3: Interpretations not established here
This module does not prove quantization performance, lattice identification,
or a bridge to quantum gravity or physical systems.
-/

namespace InfoGeometry.OperatorAlgebra.HadamardBlockTower

open Matrix
open scoped Kronecker

section Block

variable {A : Type*} [Ring A]

/-- Diagonal parity matrix `diag(1,-1)`. -/
def hS : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, -1]
/-- Symmetric off-diagonal transition matrix. -/
def hPhi : Matrix (Fin 2) (Fin 2) A := !![0, 1; 1, 0]
/-- Antisymmetric off-diagonal matrix. -/
def hJ : Matrix (Fin 2) (Fin 2) A := !![0, 1; -1, 0]
/-- Sylvester's two-dimensional Hadamard matrix. -/
def hH : Matrix (Fin 2) (Fin 2) A := !![1, 1; 1, -1]

/-- Tower step `H₂ ⊗ G`. -/
def lift (G : A) : Matrix (Fin 2) (Fin 2) A := !![G, G; G, -G]

/-- Bisymmetric block `!![X, Y; Y, X]`. -/
def bisym (X Y : A) : Matrix (Fin 2) (Fin 2) A := !![X, Y; Y, X]

/-- Decompose the Hadamard matrix as parity plus transition. -/
theorem hH_eq : (hH : Matrix (Fin 2) (Fin 2) A) = hS + hPhi := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hH, hS, hPhi]

/-- Verify the squared gate, its two conjugation identities, and anticommutation. -/
theorem hH_gate :
    (hH : Matrix (Fin 2) (Fin 2) A) * hH = (2 : ℕ) • 1 ∧
      (hH : Matrix (Fin 2) (Fin 2) A) * hS * hH = (2 : ℕ) • hPhi ∧
      (hH : Matrix (Fin 2) (Fin 2) A) * hPhi * hH = (2 : ℕ) • hS ∧
      (hH : Matrix (Fin 2) (Fin 2) A) * hJ * hH = -((2 : ℕ) • hJ) ∧
      (hS : Matrix (Fin 2) (Fin 2) A) * hPhi = -(hPhi * hS) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hH, hS, hPhi, hJ, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Noncommutativity witness: `S Φ ≠ Φ S` in any characteristic-zero operator ring. -/
theorem hS_hPhi_ne {B : Type*} [Ring B] [CharZero B] :
    (hS : Matrix (Fin 2) (Fin 2) B) * hPhi ≠ hPhi * hS := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [hS, hPhi, Matrix.mul_apply, Fin.sum_univ_two] at h01
  have : (2 : B) = 0 := by rw [← one_add_one_eq_two]; rw [eq_neg_iff_add_eq_zero] at h01; exact h01
  exact two_ne_zero this

/-- Four-channel Hadamard block transform over any ring. -/
theorem hH_conj (a b c d : A) :
    hH * !![a, b; c, d] * hH =
      !![(a + d) + (b + c), (a - d) - (b - c); (a - d) + (b - c), (a + d) - (b + c)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hH, Matrix.mul_apply, Fin.sum_univ_two] <;> abel

/-- Lossless inversion `H (H M H) H = 4 M`. -/
theorem hH_conj_conj (M : Matrix (Fin 2) (Fin 2) A) :
    hH * (hH * M * hH) * hH = (4 : ℕ) • M := by
  have h2 := (hH_gate (A := A)).1
  calc hH * (hH * M * hH) * hH = (hH * hH) * M * (hH * hH) := by simp only [Matrix.mul_assoc]
    _ = (4 : ℕ) • M := by
      rw [h2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
      norm_num

/-- Tower step squares: `lift G * lift G = diag(2 G², 2 G²)`. -/
theorem lift_sq (G : A) : lift G * lift G = !![2 * (G * G), 0; 0, 2 * (G * G)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lift, Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

/-- Tower step diagonalises bisymmetric blocks. -/
theorem lift_bisym (G X Y : A) :
    lift G * bisym X Y * lift G = !![2 * (G * (X + Y) * G), 0; 0, 2 * (G * (X - Y) * G)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lift, bisym, Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul, mul_sub, sub_mul] <;>
    noncomm_ring

/-- The base gate is the tower lift of the scalar identity. -/
theorem hH_eq_lift_one : (hH : Matrix (Fin 2) (Fin 2) A) = lift 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hH, lift]

/-- `H · bisym x y · H = diag(2(x+y), 2(x-y))` over any ring. -/
theorem hH_bisym (x y : A) : hH * bisym x y * hH = !![2 * (x + y), 0; 0, 2 * (x - y)] := by
  rw [hH_eq_lift_one, lift_bisym]; simp

end Block

section Tower

variable {A : Type*} [Ring A]

/-- `H₄ = H₂ ⊗ H₂` as a block matrix over `Matrix (Fin 2) (Fin 2) A`. -/
def hH4 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A) := lift hH

/-- `H₈ = H₂ ⊗ H₄`. -/
def hH8 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) := lift hH4

/-- The two-stage lifted Hadamard square. -/
theorem hH4_sq :
    (hH4 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) * hH4 =
      !![2 * ((2 : ℕ) • 1), 0; 0, 2 * ((2 : ℕ) • 1)] := by
  rw [hH4, lift_sq, (hH_gate (A := A)).1]

/-- The three-stage lifted Hadamard square. -/
theorem hH8_sq :
    (hH8 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A))) * hH8 =
      !![2 * !![2 * ((2 : ℕ) • 1), 0; 0, 2 * ((2 : ℕ) • 1)], 0;
         0, 2 * !![2 * ((2 : ℕ) • 1), 0; 0, 2 * ((2 : ℕ) • 1)]] := by
  rw [hH8, lift_sq, hH4_sq]

/-- Two-level Walsh block `bisym (bisym c₀ c₁) (bisym c₂ c₃)` is diagonalised by `H₄`. -/
theorem hH4_walsh (c₀ c₁ c₂ c₃ : A) :
    hH4 * bisym (bisym c₀ c₁) (bisym c₂ c₃) * hH4 =
      !![2 * !![2 * (c₀ + c₂ + (c₁ + c₃)), 0; 0, 2 * (c₀ + c₂ - (c₁ + c₃))], 0;
         0, 2 * !![2 * (c₀ - c₂ + (c₁ - c₃)), 0; 0, 2 * (c₀ - c₂ - (c₁ - c₃))]] := by
  rw [hH4, lift_bisym]
  have e1 : bisym c₀ c₁ + bisym c₂ c₃ = bisym (c₀ + c₂) (c₁ + c₃) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [bisym]
  have e2 : bisym c₀ c₁ - bisym c₂ c₃ = bisym (c₀ - c₂) (c₁ - c₃) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [bisym]
  rw [e1, e2, hH_bisym, hH_bisym]

end Tower

/-! ### Noncommutative adjugate, Schur complement, and the Hadamard sandwich -/

section NoncommutativeQuasideterminants

variable {A : Type*} [Ring A]

/-- The commutator convention `[x,y] = x*y - y*x`. -/
def opCommutator (x y : A) : A := x * y - y * x

/-- A concrete `2 × 2` matrix over an arbitrary, possibly noncommutative ring. -/
def opMat2 (a b c d : A) : Matrix (Fin 2) (Fin 2) A := !![a, b; c, d]

/-- The classical formal adjugate expression; over a noncommutative ring it is not
in general an adjugate in the determinant sense. -/
def formalAdjugate2 (a b c d : A) : Matrix (Fin 2) (Fin 2) A := !![d, -b; -c, a]

/-- The lower-right Schur complement for a supplied inverse `aInv` of the upper-left pivot. -/
def schurComplement11 (b c d aInv : A) : A := d - c * aInv * b

/-- The left adjugate product exposes its two off-diagonal commutators. -/
theorem formalAdjugate2_mul (a b c d : A) :
    formalAdjugate2 a b c d * opMat2 a b c d =
      opMat2 (d * a - b * c) (opCommutator d b)
        (opCommutator a c) (a * d - c * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formalAdjugate2, opMat2, opCommutator, Matrix.mul_apply,
      Fin.sum_univ_two] <;> noncomm_ring

/-- The right adjugate product has a different pair of commutator defects. -/
theorem opMat2_mul_formalAdjugate2 (a b c d : A) :
    opMat2 a b c d * formalAdjugate2 a b c d =
      opMat2 (a * d - b * c) (opCommutator b a)
        (opCommutator c d) (d * a - c * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formalAdjugate2, opMat2, opCommutator, Matrix.mul_apply,
      Fin.sum_univ_two] <;> noncomm_ring

/-- A factorized matrix is left-singular, although its naive `ad-bc` expression
is exactly the commutator `[c,b]`. -/
theorem factorized_operator_matrix_aporia (b c : A) :
    opMat2 (-c) 1 0 0 * opMat2 1 b c (c * b) = 0 ∧
    1 * (c * b) - b * c = opCommutator c b := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [opMat2, Matrix.mul_apply, Fin.sum_univ_two]
  · dsimp [opCommutator]; noncomm_ring

/-- Under the three `2 × 2` Manin commutator relations, the formal adjugate
product is diagonal with a common operator-valued entry. -/
theorem manin_left_cramer
    (a b c d : A)
    (hAC : opCommutator a c = 0)
    (hDB : opCommutator d b = 0)
    (hCross : opCommutator a d = opCommutator c b) :
    formalAdjugate2 a b c d * opMat2 a b c d =
      opMat2 (d * a - b * c) 0 0 (d * a - b * c) := by
  have hDiag : d * a - b * c = a * d - c * b := by
    dsimp [opCommutator] at hCross
    calc
      d * a - b * c = (a * d - (a * d - d * a)) - b * c := by noncomm_ring
      _ = (a * d - (c * b - b * c)) - b * c := by rw [hCross]
      _ = a * d - c * b := by noncomm_ring
  rw [formalAdjugate2_mul]
  simp [hAC, hDB, hDiag]

/-- Exact Gauss–Bruhat factorization with a two-sided inverse for the pivot. -/
theorem schur_complement_ldu
    (a b c d aInv : A)
    (hInvL : aInv * a = 1) (hInvR : a * aInv = 1) :
    (opMat2 1 0 (c * aInv) 1 *
        opMat2 a 0 0 (schurComplement11 b c d aInv)) *
      opMat2 1 (aInv * b) 0 1 = opMat2 a b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [opMat2, schurComplement11, Matrix.mul_apply, Fin.sum_univ_two,
      mul_assoc] <;>
    first
    | rfl
    | rw [← mul_assoc, hInvR, one_mul]
    | rw [hInvL, mul_one]
    | rw [show c * (aInv * (a * (aInv * b))) = c * (aInv * b) by
        calc
          c * (aInv * (a * (aInv * b))) = c * ((aInv * a) * (aInv * b)) := by noncomm_ring
          _ = c * (aInv * b) := by rw [hInvL, one_mul]]
  all_goals abel

/-- The Schur complement vanishes for a factorized matrix
`[[a, a*w], [v*a, v*a*w]]` when `aInv` is a right inverse of `a`. -/
theorem schur_complement_vanishes_on_factorization
    (a aInv v w : A) (hInvR : a * aInv = 1) :
    schurComplement11 (a * w) (v * a) (v * a * w) aInv = 0 := by
  dsimp [schurComplement11]
  rw [show v * a * aInv * (a * w) = v * (a * w) by
    calc
      v * a * aInv * (a * w) = v * (a * aInv) * (a * w) := by noncomm_ring
      _ = v * (a * w) := by rw [hInvR]; simp]
  rw [mul_assoc v a w, sub_self]

/-- The naive difference of squares for a bisymmetric operator block has a
commutator defect in each order. -/
theorem bisymmetric_product_commutator (x y : A) :
    (x + y) * (x - y) = (x * x - y * y) - opCommutator x y ∧
    (x - y) * (x + y) = (x * x - y * y) + opCommutator x y := by
  constructor <;> dsimp [opCommutator] <;> noncomm_ring

/-- Corrected operator product for a bisymmetric block: inserting the inverse
of `x` makes both orders equal to its lower-right Schur complement. -/
theorem hadamard_schur_sandwich
    (x y xInv : A) (hInvL : xInv * x = 1) (hInvR : x * xInv = 1) :
    (x + y) * xInv * (x - y) = x - y * xInv * y ∧
    (x - y) * xInv * (x + y) = x - y * xInv * y := by
  constructor
  · calc
      (x + y) * xInv * (x - y) =
          x * xInv * x - x * xInv * y + y * xInv * x - y * xInv * y := by
            noncomm_ring
      _ = x - x * xInv * y + y * xInv * x - y * xInv * y := by rw [hInvR, one_mul]
      _ = x - y * xInv * y := by
        rw [mul_assoc y xInv x, hInvL, mul_one]
        rw [hInvR, one_mul]
        noncomm_ring
  · calc
      (x - y) * xInv * (x + y) =
          x * xInv * x + x * xInv * y - y * xInv * x - y * xInv * y := by
            noncomm_ring
      _ = x + y - y * xInv * x - y * xInv * y := by rw [hInvR]; simp
      _ = x + y - y - y * xInv * y := by
        rw [mul_assoc y xInv x, hInvL, mul_one]
      _ = x - y * xInv * y := by noncomm_ring

end NoncommutativeQuasideterminants

/-! ### Integer Sylvester `H₈`, Paley `H₁₂`, `H₂₄ = H₂ ⊗ H₁₂` -/

section Integer

/-- Integer Sylvester Hadamard matrix of order two. -/
def zH2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, -1]

/-- Sylvester `H₈ = H₂ ⊗ H₂ ⊗ H₂`. -/
def zH8 : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℤ := (zH2 ⊗ₖ zH2) ⊗ₖ zH2

/-- Paley `H₁₂` from the quadratic residues `{1,3,4,5,9}` mod `11`. -/
def zH12 : Matrix (Fin 12) (Fin 12) ℤ := fun i j =>
  if i.val = 0 then 1
  else if j.val = 0 then -1
  else if i.val = j.val then 1
  else if (11 + j.val - i.val) % 11 ∈ ({1, 3, 4, 5, 9} : Finset ℕ) then 1
  else -1

/-- Hybrid order-24 Hadamard matrix, the Kronecker product of `zH2` and `zH12`. -/
def zH24 : Matrix (Fin 2 × Fin 12) (Fin 2 × Fin 12) ℤ := zH2 ⊗ₖ zH12

/-- Integer parity `σ_z`. -/
def zS : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- Sign normalisation of the first Paley row/column. -/
def zP12 : Matrix (Fin 12) (Fin 12) ℤ := Matrix.diagonal fun i => if i.val = 0 then -1 else 1

/-- Integer witnesses: the Hadamard matrices do not commute with the parity operators. -/
theorem zH2_zS_ne : zH2 * zS ≠ zS * zH2 := by decide

/-- The Paley matrix and its first-coordinate sign normalization do not commute. -/
theorem zH12_zP12_ne : zH12 * zP12 ≠ zP12 * zH12 := by decide

/-- The order-two Sylvester matrix has row norm squared two. -/
theorem zH2_orth : zH2 * zH2ᵀ = (2 : ℤ) • 1 := by decide

/-- The explicitly defined Paley matrix has row norm squared twelve. -/
theorem zH12_orth : zH12 * zH12ᵀ = (12 : ℤ) • 1 := by decide

/-- The order-eight Sylvester tensor matrix has row norm squared eight. -/
theorem zH8_orth : zH8 * zH8ᵀ = (8 : ℤ) • 1 := by
  rw [zH8, ← Matrix.kroneckerMap_transpose, ← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [zH2_orth, Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one,
    smul_smul]
  norm_num

/-- The order-24 Kronecker matrix has row norm squared twenty-four. -/
theorem zH24_orth : zH24 * zH24ᵀ = (24 : ℤ) • 1 := by
  rw [zH24, ← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, zH2_orth, zH12_orth,
    Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]
  norm_num

/-- `H₂₄` over an arbitrary operator ring: `H Hᵀ = 24`. -/
theorem opH24_orth (B : Type*) [Ring B] :
    (Int.castRingHom B).mapMatrix zH24 * ((Int.castRingHom B).mapMatrix zH24)ᵀ =
      (Int.castRingHom B).mapMatrix ((24 : ℤ) • 1) := by
  rw [← zH24_orth, map_mul]
  congr 1

end Integer


/-! ### The Walsh–Sylvester tower `H_{2ⁿ}` for every `n` -/

section Walsh

/-- One-bit character `(-1)^{a b}` on `Fin 2`. -/
def bitSign (a b : Fin 2) : ℤ := if a = 1 ∧ b = 1 then -1 else 1

/-- Sylvester–Walsh matrix `H_{2ⁿ}(x, y) = ∏ₖ (-1)^{xₖ yₖ}` indexed by `n`-bit words. -/
def walsh (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℤ := fun x y => ∏ k, bitSign (x k) (y k)

/-- The two one-bit Walsh characters are orthogonal, with squared norm two. -/
theorem bitSign_orth (a c : Fin 2) : ∑ b : Fin 2, bitSign a b * bitSign c b = if a = c then 2 else 0 := by
  revert a c; decide

/-- Each one-bit Walsh character has square one. -/
theorem bitSign_sq (a b : Fin 2) : bitSign a b * bitSign a b = 1 := by revert a b; decide

/-- The one-bit Walsh pairing is symmetric in its arguments. -/
theorem bitSign_comm (a b : Fin 2) : bitSign a b = bitSign b a := by revert a b; decide

/-- **Orthogonality of the whole tower:** `H_{2ⁿ} H_{2ⁿ}ᵀ = 2ⁿ` (character orthogonality). -/
theorem walsh_orth (n : ℕ) : walsh n * (walsh n)ᵀ = ((2 : ℤ) ^ n) • 1 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, walsh, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k b => bitSign (x k) b * bitSign (y k) b)]
  simp only [bitSign_orth]
  by_cases hxy : x = y
  · subst hxy; simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp hxy
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])]
    simp [hxy]

/-- Every entry of the tower is `±1` (flat modulus). -/
theorem walsh_entry (n : ℕ) (x y : Fin n → Fin 2) : walsh n x y = 1 ∨ walsh n x y = -1 := by
  have h : walsh n x y * walsh n x y = 1 := by
    simp only [walsh, ← Finset.prod_mul_distrib, bitSign_sq, Finset.prod_const_one]
  exact mul_self_eq_one_iff.mp h

/-- Every column carries energy `2ⁿ`. -/
theorem walsh_column_energy (n : ℕ) (j : Fin n → Fin 2) : ∑ x, walsh n x j * walsh n x j = 2 ^ n := by
  have h := congrFun (congrFun (walsh_orth n) j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [show walsh n x j = walsh n j x by simp [walsh, bitSign_comm]]

/-- Walsh transform of a Walsh-character sign mask. Orthogonality says that
the full DC amplitude is relocated to exactly one output character. -/
def walshCharacterTransform (n : ℕ) (a x : Fin n → Fin 2) : ℤ :=
  ∑ y, walsh n x y * walsh n a y

/-- The transform of a Walsh character is supported at its matching index. -/
theorem walshCharacterTransform_exact (n : ℕ) (a x : Fin n → Fin 2) :
    walshCharacterTransform n a x = if x = a then (2 : ℤ) ^ n else 0 := by
  have h := congrFun (congrFun (walsh_orth n) x) a
  simpa [walshCharacterTransform, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.one_apply] using h

/-- A linear Walsh-character sign mask does not suppress a DC spike: it moves
the entire amplitude `2^n` to its own character index. -/
theorem walshCharacterTransform_transports_spike (n : ℕ) (a : Fin n → Fin 2) :
    walshCharacterTransform n a a = (2 : ℤ) ^ n ∧
    ∀ x, x ≠ a → walshCharacterTransform n a x = 0 := by
  constructor
  · rw [walshCharacterTransform_exact]
    simp
  · intro x hxa
    rw [walshCharacterTransform_exact]
    simp [hxa]

/-- Three-bit quadratic sign phase `(-1)^(y₀y₁)`, the semi-bent mask used at
Walsh length eight. -/
def semiBentSign8 (y : Fin 3 → Fin 2) : ℤ :=
  if decide (y 0 = 1 ∧ y 1 = 1) then -1 else 1

/-- Walsh spectrum of the three-bit semi-bent sign phase. -/
def semiBentWalshTransform8 (x : Fin 3 → Fin 2) : ℤ :=
  ∑ y, walsh 3 x y * semiBentSign8 y

/-- Exact semi-bent spectrum: coefficients are `±4` when the third character
coordinate is zero, and vanish otherwise. -/
theorem semiBentSign8_walsh_spectrum (x : Fin 3 → Fin 2) :
    (semiBentWalshTransform8 x).natAbs = if x 2 = 0 then 4 else 0 := by
  classical
  fin_cases x <;> decide

/-- In particular, the three-bit quadratic phase has no Walsh coefficient
larger than four, and some coefficient attains four. -/
theorem semiBentSign8_walsh_bound_and_attainment :
    (∀ x, (semiBentWalshTransform8 x).natAbs ≤ 4) ∧
    ∃ x, (semiBentWalshTransform8 x).natAbs = 4 := by
  constructor
  · intro x
    rw [semiBentSign8_walsh_spectrum]
    split <;> norm_num
  · refine ⟨fun _ => 0, ?_⟩
    rw [semiBentSign8_walsh_spectrum]
    simp

/-- Walsh spectrum for an arbitrary Boolean sign assignment on the eight
three-bit words. -/
def signMaskWalshTransform8 (ε : (Fin 3 → Fin 2) → Fin 2) (x : Fin 3 → Fin 2) : ℤ :=
  ∑ y, walsh 3 x y * (if ε y = 1 then -1 else 1)

set_option maxRecDepth 10000 in
/-- Every sign assignment on eight coordinates has a Walsh coefficient of
magnitude at least four. The finite function space here enumerates all 256
sign masks, so this result is specific to length eight. -/
theorem signMaskWalshTransform8_lower_bound :
    ∀ ε : (Fin 3 → Fin 2) → Fin 2, ∃ x : Fin 3 → Fin 2,
      4 ≤ (signMaskWalshTransform8 ε x).natAbs := by
  classical
  decide

/-- Walsh columns multiplied by any pointwise involutive signs remain
orthogonal. The proof keeps the full `n`-bit Walsh carrier and only uses
`ε(y)^2 = 1`; it does not rely on a specific finite sign table. -/
def signedWalsh (n : ℕ) (ε : (Fin n → Fin 2) → ℤ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℤ :=
  fun x y => walsh n x y * ε y

/-- Column sign changes preserve Walsh orthogonality when every sign squares to one. -/
theorem signedWalsh_orth (n : ℕ) (ε : (Fin n → Fin 2) → ℤ)
    (hε : ∀ y, ε y * ε y = 1) :
    signedWalsh n ε * (signedWalsh n ε)ᵀ = ((2 : ℤ) ^ n) • 1 := by
  ext x z
  have h := congrFun (congrFun (walsh_orth n) x) z
  calc
    (signedWalsh n ε * (signedWalsh n ε)ᵀ) x z =
        ∑ y, walsh n x y * walsh n z y := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, signedWalsh]
      refine Finset.sum_congr rfl ?_
      intro y hy
      calc
        (walsh n x y * ε y) * (walsh n z y * ε y) =
            (walsh n x y * walsh n z y) * (ε y * ε y) := by ring
        _ = walsh n x y * walsh n z y := by rw [hε y, mul_one]
    _ = (((2 : ℤ) ^ n) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℤ)) x z := by
      simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.one_apply] using h

/-- The quadratic Boolean phase on four bits given by the sum of two disjoint
products. Its sign sequence is a bent sign vector for the 16-point Walsh
transform. -/
def bentSign16 (y : Fin 4 → Fin 2) : ℤ :=
  if xor (decide (y 0 = 1 ∧ y 1 = 1)) (decide (y 2 = 1 ∧ y 3 = 1)) then -1 else 1

/-- Walsh transform of the four-bit quadratic bent sign sequence. -/
def bentWalshTransform16 (x : Fin 4 → Fin 2) : ℤ :=
  ∑ y, walsh 4 x y * bentSign16 y

/-- Sylvester matrix with the four-bit quadratic phase applied to its columns. -/
def bentWalshMatrix16 : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℤ :=
  signedWalsh 4 bentSign16

/-- The four-bit bent sign sequence is pointwise an involutive sign. -/
theorem bentSign16_sq (y : Fin 4 → Fin 2) : bentSign16 y * bentSign16 y = 1 := by
  unfold bentSign16
  split <;> norm_num

/-- The bent-sign transform retains exact Hadamard orthogonality `16 I`. -/
theorem bentWalshMatrix16_orth :
    bentWalshMatrix16 * bentWalshMatrix16ᵀ = (16 : ℤ) • 1 := by
  simpa [bentWalshMatrix16, bentSign16_sq] using
    (signedWalsh_orth 4 bentSign16 bentSign16_sq)

/-- Every Walsh coefficient of the four-bit quadratic bent sign sequence has
absolute value `4`, the square root of the transform length `16`. This is the
finite flat-spectrum statement; no lattice or quantization conclusion is
included. -/
theorem bentSign16_walsh_flat (x : Fin 4 → Fin 2) :
    (bentWalshTransform16 x).natAbs = 4 := by
  classical
  fin_cases x <;> decide

/-- The tower over an arbitrary operator ring. -/
def opWalsh (B : Type*) [Ring B] (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) B :=
  (Int.castRingHom B).mapMatrix (walsh n)

/-- Walsh orthogonality transported to any ring by the integer cast homomorphism. -/
theorem opWalsh_orth (B : Type*) [Ring B] (n : ℕ) :
    opWalsh B n * (opWalsh B n)ᵀ = (Int.castRingHom B).mapMatrix (((2 : ℤ) ^ n) • 1) := by
  rw [← walsh_orth, map_mul]
  rfl

/-- **Spike spreading over an operator ring:** a spike `m` at `j` is sent to `±m` in every
coordinate (`H_{2ⁿ} e_j m = (H_{2ⁿ}(x, j) m)ₓ`, `H_{2ⁿ}(x, j) = ±1`). -/
theorem opWalsh_spread (B : Type*) [Ring B] (n : ℕ) (j : Fin n → Fin 2) (m : B)
    (x : Fin n → Fin 2) :
    (opWalsh B n *ᵥ Pi.single j m) x = m ∨ (opWalsh B n *ᵥ Pi.single j m) x = -m := by
  rw [Matrix.mulVec_single]
  rcases walsh_entry n x j with h | h <;> [left; right] <;>
    simp [opWalsh, RingHom.mapMatrix_apply, h]

/-- After the real Walsh transform is normalized by `1 / sqrt (2^n)`, a
coordinate spike has exactly `1 / 2^n` of its squared amplitude in every
output coordinate.  This is a coordinatewise energy identity; no probabilistic
or Gaussian claim is part of it. -/
theorem normalized_walsh_spike_coordinate_sq
    (n : ℕ) (j x : Fin n → Fin 2) (m : ℝ) :
    ((opWalsh ℝ n *ᵥ Pi.single j (m / Real.sqrt ((2 : ℝ) ^ n))) x) ^ 2 =
      m ^ 2 / (2 : ℝ) ^ n := by
  have hspread := opWalsh_spread ℝ n j (m / Real.sqrt ((2 : ℝ) ^ n)) x
  have hnonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
  rcases hspread with hspread | hspread
  · rw [hspread, div_pow, Real.sq_sqrt hnonneg]
  · rw [hspread, neg_sq, div_pow, Real.sq_sqrt hnonneg]

end Walsh

end InfoGeometry.OperatorAlgebra.HadamardBlockTower
