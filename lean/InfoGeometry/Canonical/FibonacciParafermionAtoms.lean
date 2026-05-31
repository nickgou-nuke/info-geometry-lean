import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# InfoGeometry.Canonical.FibonacciParafermionAtoms

Finite algebraic atoms for Fibonacci recoupling and `Z₃` parafermion
projectors.

No braid-group representation theorem.
No conformal-block construction.
No topological-protection theorem.
No axioms or placeholders.
-/

namespace InfoGeometry.Canonical.FibonacciParafermionAtoms

/-! ## Fibonacci `F` matrix -/

/-- The `2 × 2` Fibonacci fusion/recoupling matrix `[[a,b],[b,-a]]`. -/
def F_matrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, b; b, -a]

/-- Algebraic relation for the real Fibonacci recoupling parameters. -/
def IsFibonacciRelation (a b : ℝ) : Prop :=
  a ^ 2 + b ^ 2 = 1

/-- The real Fibonacci recoupling matrix is involutive under `a² + b² = 1`. -/
theorem F_matrix_sq (a b : ℝ) (h : IsFibonacciRelation a b) :
    F_matrix a b * F_matrix a b = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold IsFibonacciRelation at h
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, F_matrix]
    have h1 : a * a + b * b = a ^ 2 + b ^ 2 := by ring
    rw [h1, h]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, F_matrix]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, F_matrix]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, F_matrix]
    have h1 : b * b + a * a = a ^ 2 + b ^ 2 := by ring
    rw [h1, h]

/-- Diagonal two-channel braid matrix `diag(q⁻⁴, q³)`. -/
noncomputable def R_matrix (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![q ^ (-4 : ℤ), 0; 0, q ^ 3]

/-- The dual-basis braid matrix obtained by conjugating `R_matrix` with `F_matrix`. -/
noncomputable def B_matrix (a b q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  F_matrix a b * R_matrix q * F_matrix a b

/-- Conjugating `B = F R F` by the involutive fusion matrix recovers `R`. -/
theorem F_B_F_eq_R (a b q : ℝ) (h : IsFibonacciRelation a b) :
    F_matrix a b * B_matrix a b q * F_matrix a b = R_matrix q := by
  unfold B_matrix
  have hF : F_matrix a b * F_matrix a b = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
    F_matrix_sq a b h
  calc
    F_matrix a b * (F_matrix a b * R_matrix q * F_matrix a b) * F_matrix a b
        = (F_matrix a b * F_matrix a b) * R_matrix q *
            (F_matrix a b * F_matrix a b) := by
          simp only [mul_assoc]
    _ = 1 * R_matrix q * 1 := by rw [hF]
    _ = R_matrix q := by simp

/-- Top-left entry of the dual-basis braid matrix `B = F R F`. -/
theorem B_matrix_apply_zero_zero (a b q : ℝ) :
    B_matrix a b q 0 0 = a * a * q ^ (-4 : ℤ) + b * b * q ^ 3 := by
  simp [B_matrix, F_matrix, R_matrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Top-right entry of the dual-basis braid matrix `B = F R F`. -/
theorem B_matrix_apply_zero_one (a b q : ℝ) :
    B_matrix a b q 0 1 = a * b * q ^ (-4 : ℤ) - a * b * q ^ 3 := by
  simp [B_matrix, F_matrix, R_matrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Bottom-left entry of the dual-basis braid matrix `B = F R F`. -/
theorem B_matrix_apply_one_zero (a b q : ℝ) :
    B_matrix a b q 1 0 = a * b * q ^ (-4 : ℤ) - a * b * q ^ 3 := by
  simp [B_matrix, F_matrix, R_matrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Bottom-right entry of the dual-basis braid matrix `B = F R F`. -/
theorem B_matrix_apply_one_one (a b q : ℝ) :
    B_matrix a b q 1 1 = b * b * q ^ (-4 : ℤ) + a * a * q ^ 3 := by
  simp [B_matrix, F_matrix, R_matrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The dual-basis braid matrix `B = F R F` is symmetric. -/
theorem B_matrix_symmetric (a b q : ℝ) :
    B_matrix a b q 0 1 = B_matrix a b q 1 0 := by
  rw [B_matrix_apply_zero_one, B_matrix_apply_one_zero]

/-- Diagonal two-channel braid matrix with independent diagonal entries. -/
noncomputable def diagonalBraidMatrix (r t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r, 0; 0, t]

/-- Dual-basis braid matrix for an arbitrary diagonal pair `(r,t)`. -/
noncomputable def B_matrix_diag (a b r t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  F_matrix a b * diagonalBraidMatrix r t * F_matrix a b

/--
Finite two-channel Artin relation from explicit scalar constraints.

This proves the matrix identity `R B R = B R B` for a diagonal braid matrix
`diag(r,t)` and `B = F R F`, assuming only the finite algebraic relations
`a² + b² = 1` and `a²(r-t)² + r t = 0`.
-/
theorem diagonal_artin_relation (a b r t : ℝ)
    (hF : IsFibonacciRelation a b)
    (hA : a ^ 2 * (r - t) ^ 2 + r * t = 0) :
    diagonalBraidMatrix r t * B_matrix_diag a b r t * diagonalBraidMatrix r t =
      B_matrix_diag a b r t * diagonalBraidMatrix r t * B_matrix_diag a b r t := by
  unfold IsFibonacciRelation at hF
  have hg : a ^ 2 + b ^ 2 - 1 = 0 := by nlinarith [hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B_matrix_diag, diagonalBraidMatrix, F_matrix, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination
      (-t * (3 * a ^ 2 * r ^ 2 - 3 * a ^ 2 * r * t + a ^ 2 * t ^ 2 + b ^ 2 * r * t - r ^ 2 + r * t)) * hg +
      (-(a - 1) * (a + 1) * (r - t)) * hA
  · linear_combination
      (-2 * a * b * r * t * (r - t)) * hg +
      (-a * b * (r - t)) * hA
  · linear_combination
      (-2 * a * b * r * t * (r - t)) * hg +
      (-a * b * (r - t)) * hA
  · linear_combination
      (-r * (a ^ 2 * r ^ 2 - 3 * a ^ 2 * r * t + 3 * a ^ 2 * t ^ 2 + b ^ 2 * r * t + r * t - t ^ 2)) * hg +
      ((a - 1) * (a + 1) * (r - t)) * hA

/--
Finite two-channel braid relation for `R_matrix q` and `B_matrix a b q`.

The theorem is conditional on the explicit scalar Artin constraint for the two
chosen diagonal phases.  It does not assert a general braid-group
representation.
-/
theorem R_B_R_eq_B_R_B (a b q : ℝ)
    (hF : IsFibonacciRelation a b)
    (hA : a ^ 2 * (q ^ (-4 : ℤ) - q ^ 3) ^ 2 + q ^ (-4 : ℤ) * q ^ 3 = 0) :
    R_matrix q * B_matrix a b q * R_matrix q =
      B_matrix a b q * R_matrix q * B_matrix a b q := by
  simpa [R_matrix, B_matrix, B_matrix_diag, diagonalBraidMatrix] using
    (diagonal_artin_relation a b (q ^ (-4 : ℤ)) (q ^ 3) hF hA)

/-- Diagonal braid matrices compose by multiplying their diagonal entries. -/
theorem diagonalBraidMatrix_mul (r₁ t₁ r₂ t₂ : ℝ) :
    diagonalBraidMatrix r₁ t₁ * diagonalBraidMatrix r₂ t₂ =
      diagonalBraidMatrix (r₁ * r₂) (t₁ * t₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalBraidMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/--
Dual-basis braid matrices compose by multiplying the underlying diagonal
phases, because `F² = 1`.
-/
theorem B_matrix_diag_mul (a b r₁ t₁ r₂ t₂ : ℝ)
    (hF : IsFibonacciRelation a b) :
    B_matrix_diag a b r₁ t₁ * B_matrix_diag a b r₂ t₂ =
      B_matrix_diag a b (r₁ * r₂) (t₁ * t₂) := by
  unfold B_matrix_diag
  have hFsq : F_matrix a b * F_matrix a b = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
    F_matrix_sq a b hF
  calc
    (F_matrix a b * diagonalBraidMatrix r₁ t₁ * F_matrix a b) *
        (F_matrix a b * diagonalBraidMatrix r₂ t₂ * F_matrix a b)
        = F_matrix a b * diagonalBraidMatrix r₁ t₁ *
            (F_matrix a b * F_matrix a b) * diagonalBraidMatrix r₂ t₂ * F_matrix a b := by
          simp only [mul_assoc]
    _ = F_matrix a b * diagonalBraidMatrix r₁ t₁ * 1 * diagonalBraidMatrix r₂ t₂ * F_matrix a b := by
          rw [hFsq]
    _ = F_matrix a b * (diagonalBraidMatrix r₁ t₁ * diagonalBraidMatrix r₂ t₂) * F_matrix a b := by
          simp only [mul_one, mul_assoc]
    _ = F_matrix a b * diagonalBraidMatrix (r₁ * r₂) (t₁ * t₂) * F_matrix a b := by
          rw [diagonalBraidMatrix_mul]

/-- Squaring a dual-basis braid matrix squares the underlying diagonal phases. -/
theorem B_matrix_diag_sq (a b r t : ℝ) (hF : IsFibonacciRelation a b) :
    B_matrix_diag a b r t * B_matrix_diag a b r t =
      B_matrix_diag a b (r * r) (t * t) := by
  exact B_matrix_diag_mul a b r t r t hF

/-- Composition law for two `B_matrix` values with independent phase parameters. -/
theorem B_matrix_mul_eq_diag (a b q₁ q₂ : ℝ) (hF : IsFibonacciRelation a b) :
    B_matrix a b q₁ * B_matrix a b q₂ =
      B_matrix_diag a b (q₁ ^ (-4 : ℤ) * q₂ ^ (-4 : ℤ)) (q₁ ^ 3 * q₂ ^ 3) := by
  simpa [B_matrix, R_matrix, B_matrix_diag, diagonalBraidMatrix] using
    (B_matrix_diag_mul a b (q₁ ^ (-4 : ℤ)) (q₁ ^ 3) (q₂ ^ (-4 : ℤ)) (q₂ ^ 3) hF)

/-! ## `Z₃` parafermion composite charge -/

section ParafermionCharge

variable {A : Type*} [Ring A]
variable {ω χ₁ χ₂ : A}

/--
Composite `Z₃` parafermion charge conservation.

If `ω` is central with `ω³ = 1`, `χ₁³ = χ₂³ = 1`, and
`χ₁χ₂ = ω χ₂χ₁`, then `(χ₁χ₂)³ = 1`.
-/
theorem parafermion_composite_charge
    (hωc : ∀ x : A, ω * x = x * ω)
    (hω3 : ω * ω * ω = 1)
    (hχ1 : χ₁ * χ₁ * χ₁ = 1)
    (hχ2 : χ₂ * χ₂ * χ₂ = 1)
    (hbraid : χ₁ * χ₂ = ω * (χ₂ * χ₁)) :
    (χ₁ * χ₂) * (χ₁ * χ₂) * (χ₁ * χ₂) = 1 := by
  let q : A := ω * ω
  have hbinv : χ₂ * χ₁ = q * (χ₁ * χ₂) := by
    calc
      χ₂ * χ₁ = 1 * (χ₂ * χ₁) := by simp
      _ = (ω * ω * ω) * (χ₂ * χ₁) := by rw [hω3]
      _ = (ω * ω) * (ω * (χ₂ * χ₁)) := by noncomm_ring
      _ = q * (χ₁ * χ₂) := by rw [hbraid]
  have hqc (z : A) : q * z = z * q := by
    dsimp [q]
    calc
      (ω * ω) * z = ω * (ω * z) := by noncomm_ring
      _ = ω * (z * ω) := by rw [hωc z]
      _ = (ω * z) * ω := by noncomm_ring
      _ = (z * ω) * ω := by rw [hωc z]
      _ = z * (ω * ω) := by noncomm_ring
  have q_pull (z y : A) : z * (q * y) = q * (z * y) := by
    calc
      z * (q * y) = (z * q) * y := by noncomm_ring
      _ = (q * z) * y := by rw [← hqc z]
      _ = q * (z * y) := by noncomm_ring
  have hswap (X : A) : χ₂ * (χ₁ * X) = q * (χ₁ * (χ₂ * X)) := by
    calc
      χ₂ * (χ₁ * X) = (χ₂ * χ₁) * X := by noncomm_ring
      _ = (q * (χ₁ * χ₂)) * X := by rw [hbinv]
      _ = q * (χ₁ * (χ₂ * X)) := by noncomm_ring
  have hq3 : q * (q * q) = 1 := by
    dsimp [q]
    calc
      (ω * ω) * ((ω * ω) * (ω * ω)) = (ω * ω * ω) * (ω * ω * ω) := by
        noncomm_ring
      _ = 1 := by rw [hω3]; simp
  have hyy : χ₂ * (χ₂ * (χ₁ * χ₂)) = q * (q * (χ₁ * (χ₂ * (χ₂ * χ₂)))) := by
    calc
      χ₂ * (χ₂ * (χ₁ * χ₂)) = χ₂ * ((χ₂ * χ₁) * χ₂) := by noncomm_ring
      _ = χ₂ * ((q * (χ₁ * χ₂)) * χ₂) := by rw [hbinv]
      _ = χ₂ * (q * ((χ₁ * χ₂) * χ₂)) := by noncomm_ring
      _ = q * (χ₂ * ((χ₁ * χ₂) * χ₂)) := by rw [q_pull]
      _ = q * (χ₂ * (χ₁ * (χ₂ * χ₂))) := by noncomm_ring
      _ = q * (q * (χ₁ * (χ₂ * (χ₂ * χ₂)))) := by rw [hswap]
  calc
    (χ₁ * χ₂) * (χ₁ * χ₂) * (χ₁ * χ₂)
        = χ₁ * (χ₂ * (χ₁ * (χ₂ * (χ₁ * χ₂)))) := by noncomm_ring
    _ = χ₁ * (q * (χ₁ * (χ₂ * (χ₂ * (χ₁ * χ₂))))) := by rw [hswap]
    _ = q * (χ₁ * (χ₁ * (χ₂ * (χ₂ * (χ₁ * χ₂))))) := by rw [q_pull]
    _ = q * (χ₁ * χ₁ * (χ₂ * (χ₂ * (χ₁ * χ₂)))) := by noncomm_ring
    _ = q * (χ₁ * χ₁ * (q * (q * (χ₁ * (χ₂ * (χ₂ * χ₂)))))) := by rw [hyy]
    _ = q * (q * (χ₁ * χ₁ * (q * (χ₁ * (χ₂ * (χ₂ * χ₂)))))) := by rw [q_pull]
    _ = q * (q * (q * (χ₁ * χ₁ * (χ₁ * (χ₂ * (χ₂ * χ₂)))))) := by
      rw [q_pull (χ₁ * χ₁) (χ₁ * (χ₂ * (χ₂ * χ₂)))]
    _ = q * (q * q) * ((χ₁ * χ₁ * χ₁) * (χ₂ * χ₂ * χ₂)) := by noncomm_ring
    _ = 1 * (1 * 1) := by rw [hq3, hχ1, hχ2]
    _ = 1 := by simp

end ParafermionCharge

/-! ## `Z₃` projector algebra

Honesty status for the algebraic projector fragment below:

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining goals. Kernel-checked in this file.]
- `Z3Parafermion.half_add_half_eq_one`
- `Z3Parafermion.half_mul_two_eq`
- `Z3Parafermion.proj_completeness`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Kernel-checked theorems whose statements explicitly require the witness `O^3 = O`.]
- `Z3Parafermion.O_pow_4`
- `Z3Parafermion.O_pow_4_eq_O_sq`
- `Z3Parafermion.proj_up_orthogonal_down`
- `Z3Parafermion.proj_up_orthogonal_vac`
- `Z3Parafermion.proj_down_orthogonal_vac`
- `Z3Parafermion.proj_vac_idempotent`
- `Z3Parafermion.proj_up_idempotent`
- `Z3Parafermion.proj_down_idempotent`

#### BUCKET 3: OPEN CLOSURE DEBT
- None inside this algebraic fragment.
-/

namespace Z3Parafermion

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Up-sector algebraic projector. -/
def P_up (O : A) : A :=
  algebraMap ℝ A (1 / 2) * (O ^ 2 + O)

/-- Down-sector algebraic projector. -/
def P_down (O : A) : A :=
  algebraMap ℝ A (1 / 2) * (O ^ 2 - O)

/-- Vacancy-sector algebraic projector. -/
def P_vac (O : A) : A :=
  1 - O ^ 2

omit [Algebra ℝ A] in
lemma O_pow_4 {O : A} (hO3 : O ^ 3 = O) : O ^ 4 = O ^ 2 := by
  have h1 : O ^ 4 = O ^ 3 * O := by noncomm_ring
  have h2 : O * O = O ^ 2 := by noncomm_ring
  rw [h1, hO3, h2]

omit [Algebra ℝ A] in
lemma O_pow_4_eq_O_sq {O : A} (hO3 : O ^ 3 = O) : O ^ 4 = O ^ 2 :=
  O_pow_4 hO3

lemma half_add_half_eq_one :
    algebraMap ℝ A (1 / 2) + algebraMap ℝ A (1 / 2) = 1 := by
  rw [← map_add]
  have : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  rw [this, map_one]

lemma algebraMap_two_eq :
    (1 + 1 : A) = algebraMap ℝ A (2 : ℝ) := by
  rw [show (1 + 1 : A) = (2 : A) by norm_num]
  exact (map_ofNat (algebraMap ℝ A) 2).symm

lemma half_mul_two_eq (x : A) :
    algebraMap ℝ A (1 / 2) * (x + x) = x := by
  have h1 : x + x = (1 + 1) * x := by noncomm_ring
  rw [h1, ← mul_assoc]
  have h2 : algebraMap ℝ A (1 / 2) * (1 + 1 : A) = 1 := by
    rw [algebraMap_two_eq]
    rw [← map_mul]
    norm_num
  rw [h2, one_mul]

theorem proj_completeness {O : A} :
    P_up O + P_down O + P_vac O = 1 := by
  dsimp [P_up, P_down, P_vac]
  set c := algebraMap ℝ A (1 / 2)
  calc
    c * (O ^ 2 + O) + c * (O ^ 2 - O) + (1 - O ^ 2)
        = (c + c) * O ^ 2 + 1 - O ^ 2 := by noncomm_ring
    _ = 1 * O ^ 2 + 1 - O ^ 2 := by rw [half_add_half_eq_one]
    _ = 1 := by noncomm_ring

theorem proj_up_orthogonal_down {O : A} (hO3 : O ^ 3 = O) :
    P_up O * P_down O = 0 := by
  dsimp [P_up, P_down]
  set c := algebraMap ℝ A (1 / 2)
  have h_comm : (O ^ 2 + O) * c = c * (O ^ 2 + O) :=
    (Algebra.commutes (1 / 2 : ℝ) (O ^ 2 + O)).symm
  calc
    c * (O ^ 2 + O) * (c * (O ^ 2 - O))
        = c * ((O ^ 2 + O) * c) * (O ^ 2 - O) := by noncomm_ring
    _ = c * (c * (O ^ 2 + O)) * (O ^ 2 - O) := by rw [h_comm]
    _ = c * c * ((O ^ 2 + O) * (O ^ 2 - O)) := by noncomm_ring
    _ = c * c * (O ^ 4 - O ^ 2) := by
        have id : (O ^ 2 + O) * (O ^ 2 - O) = O ^ 4 - O ^ 2 := by noncomm_ring
        rw [id]
    _ = c * c * (O ^ 2 - O ^ 2) := by rw [O_pow_4 hO3]
    _ = 0 := by noncomm_ring

theorem proj_up_orthogonal_vac {O : A} (hO3 : O ^ 3 = O) :
    P_up O * P_vac O = 0 := by
  dsimp [P_up, P_vac]
  set c := algebraMap ℝ A (1 / 2)
  calc
    c * (O ^ 2 + O) * (1 - O ^ 2)
        = c * ((O ^ 2 + O) * (1 - O ^ 2)) := by noncomm_ring
    _ = c * (O ^ 2 - O ^ 4 + O - O ^ 3) := by
        have id : (O ^ 2 + O) * (1 - O ^ 2) = O ^ 2 - O ^ 4 + O - O ^ 3 := by
          noncomm_ring
        rw [id]
    _ = c * (O ^ 2 - O ^ 2 + O - O) := by rw [O_pow_4 hO3, hO3]
    _ = 0 := by noncomm_ring

theorem proj_down_orthogonal_vac {O : A} (hO3 : O ^ 3 = O) :
    P_down O * P_vac O = 0 := by
  dsimp [P_down, P_vac]
  set c := algebraMap ℝ A (1 / 2)
  calc
    c * (O ^ 2 - O) * (1 - O ^ 2)
        = c * ((O ^ 2 - O) * (1 - O ^ 2)) := by noncomm_ring
    _ = c * (O ^ 2 - O ^ 4 - O + O ^ 3) := by
        have id : (O ^ 2 - O) * (1 - O ^ 2) = O ^ 2 - O ^ 4 - O + O ^ 3 := by
          noncomm_ring
        rw [id]
    _ = c * (O ^ 2 - O ^ 2 - O + O) := by rw [O_pow_4 hO3, hO3]
    _ = 0 := by noncomm_ring

omit [Algebra ℝ A] in
theorem proj_vac_idempotent {O : A} (hO3 : O ^ 3 = O) :
    P_vac O * P_vac O = P_vac O := by
  dsimp [P_vac]
  calc
    (1 - O ^ 2) * (1 - O ^ 2)
        = 1 - O ^ 2 - O ^ 2 + O ^ 4 := by noncomm_ring
    _ = 1 - O ^ 2 - O ^ 2 + O ^ 2 := by rw [O_pow_4 hO3]
    _ = 1 - O ^ 2 := by noncomm_ring

theorem proj_up_idempotent {O : A} (hO3 : O ^ 3 = O) :
    P_up O * P_up O = P_up O := by
  dsimp [P_up]
  set c := algebraMap ℝ A (1 / 2)
  have h_comm : (O ^ 2 + O) * c = c * (O ^ 2 + O) :=
    (Algebra.commutes (1 / 2 : ℝ) (O ^ 2 + O)).symm
  calc
    c * (O ^ 2 + O) * (c * (O ^ 2 + O))
        = c * ((O ^ 2 + O) * c) * (O ^ 2 + O) := by noncomm_ring
    _ = c * (c * (O ^ 2 + O)) * (O ^ 2 + O) := by rw [h_comm]
    _ = c * c * ((O ^ 2 + O) * (O ^ 2 + O)) := by noncomm_ring
    _ = c * c * (O ^ 4 + O ^ 3 + O ^ 3 + O ^ 2) := by
        have id : (O ^ 2 + O) * (O ^ 2 + O) = O ^ 4 + O ^ 3 + O ^ 3 + O ^ 2 := by
          noncomm_ring
        rw [id]
    _ = c * c * (O ^ 2 + O + O + O ^ 2) := by rw [O_pow_4 hO3, hO3]
    _ = c * (c * ((O ^ 2 + O) + (O ^ 2 + O))) := by noncomm_ring
    _ = c * (O ^ 2 + O) := by rw [half_mul_two_eq]

theorem proj_down_idempotent {O : A} (hO3 : O ^ 3 = O) :
    P_down O * P_down O = P_down O := by
  dsimp [P_down]
  set c := algebraMap ℝ A (1 / 2)
  have h_comm : (O ^ 2 - O) * c = c * (O ^ 2 - O) :=
    (Algebra.commutes (1 / 2 : ℝ) (O ^ 2 - O)).symm
  calc
    c * (O ^ 2 - O) * (c * (O ^ 2 - O))
        = c * ((O ^ 2 - O) * c) * (O ^ 2 - O) := by noncomm_ring
    _ = c * (c * (O ^ 2 - O)) * (O ^ 2 - O) := by rw [h_comm]
    _ = c * c * ((O ^ 2 - O) * (O ^ 2 - O)) := by noncomm_ring
    _ = c * c * (O ^ 4 - O ^ 3 - O ^ 3 + O ^ 2) := by
        have id : (O ^ 2 - O) * (O ^ 2 - O) = O ^ 4 - O ^ 3 - O ^ 3 + O ^ 2 := by
          noncomm_ring
        rw [id]
    _ = c * c * (O ^ 2 - O - O + O ^ 2) := by rw [O_pow_4 hO3, hO3]
    _ = c * (c * ((O ^ 2 - O) + (O ^ 2 - O))) := by noncomm_ring
    _ = c * (O ^ 2 - O) := by rw [half_mul_two_eq]

end

end Z3Parafermion

/-! ## Scalar-smul projector presentation -/

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Scalar-smul presentation of the `+` algebraic sector projector. -/
def proj_up (O : A) : A :=
  (1 / 2 : ℝ) • (O ^ 2 + O)

/-- Scalar-smul presentation of the `-` algebraic sector projector. -/
def proj_down (O : A) : A :=
  (1 / 2 : ℝ) • (O ^ 2 - O)

/-- Scalar-smul presentation of the vacancy algebraic sector projector. -/
def proj_vacancy (O : A) : A :=
  1 - O ^ 2

/-- Orthogonality of the `+` sector and the vacancy sector under `O³ = O`. -/
theorem proj_up_orthogonal_vacancy (O : A) (h : O ^ 3 = O) :
    proj_up O * proj_vacancy O = 0 := by
  unfold proj_up proj_vacancy
  rw [smul_mul_assoc]
  have h_eq : (O ^ 2 + O) * (1 - O ^ 2) = 0 := by
    calc
      (O ^ 2 + O) * (1 - O ^ 2)
          = O ^ 2 - O ^ 4 + O - O ^ 3 := by noncomm_ring
      _ = O ^ 2 - O * O ^ 3 + O - O ^ 3 := by
          have h_pow4 : O ^ 4 = O * O ^ 3 := by noncomm_ring
          rw [h_pow4]
      _ = O ^ 2 - O * O + O - O := by rw [h]
      _ = 0 := by noncomm_ring
  rw [h_eq, smul_zero]

/-- Orthogonality of the `-` sector and the vacancy sector under `O³ = O`. -/
theorem proj_down_orthogonal_vacancy (O : A) (h : O ^ 3 = O) :
    proj_down O * proj_vacancy O = 0 := by
  unfold proj_down proj_vacancy
  rw [smul_mul_assoc]
  have h_eq : (O ^ 2 - O) * (1 - O ^ 2) = 0 := by
    calc
      (O ^ 2 - O) * (1 - O ^ 2)
          = O ^ 2 - O ^ 4 - O + O ^ 3 := by noncomm_ring
      _ = O ^ 2 - O * O ^ 3 - O + O ^ 3 := by
          have h_pow4 : O ^ 4 = O * O ^ 3 := by noncomm_ring
          rw [h_pow4]
      _ = O ^ 2 - O * O - O + O := by rw [h]
      _ = 0 := by noncomm_ring
  rw [h_eq, smul_zero]

/-- Completeness of the scalar-smul trinary projector presentation. -/
theorem proj_completeness (O : A) :
    proj_up O + proj_down O + proj_vacancy O = 1 := by
  unfold proj_up proj_down proj_vacancy
  simp only [smul_add, smul_sub]
  have step1 :
      (1 / 2 : ℝ) • O ^ 2 + (1 / 2 : ℝ) • O +
        ((1 / 2 : ℝ) • O ^ 2 - (1 / 2 : ℝ) • O) =
      (1 / 2 : ℝ) • O ^ 2 + (1 / 2 : ℝ) • O ^ 2 := by
    abel
  rw [step1, ← add_smul]
  have step2 : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  rw [step2, one_smul]
  abel

end

/-! ## Three-state computational/leakage projection -/

/-- Finite three-state projection onto the first two computational coordinates. -/
def computationalProjection3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, 0]

/-- First computational basis vector. -/
def compVec0 : Fin 3 → ℝ :=
  ![1, 0, 0]

/-- Second computational basis vector. -/
def compVec1 : Fin 3 → ℝ :=
  ![0, 1, 0]

/-- Non-computational basis vector in a finite three-state register. -/
def nonComputationalVec : Fin 3 → ℝ :=
  ![0, 0, 1]

/-- The finite computational projection is idempotent. -/
theorem computationalProjection3_idempotent :
    computationalProjection3 * computationalProjection3 = computationalProjection3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [computationalProjection3, Matrix.mul_apply, Fin.sum_univ_three]

/-- The finite computational projection preserves the first computational basis vector. -/
theorem computationalProjection3_preserves_compVec0 :
    computationalProjection3.mulVec compVec0 = compVec0 := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, computationalProjection3, compVec0]

/-- The finite computational projection preserves the second computational basis vector. -/
theorem computationalProjection3_preserves_compVec1 :
    computationalProjection3.mulVec compVec1 = compVec1 := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, computationalProjection3, compVec1]

/-- The finite computational projection kills the non-computational basis vector. -/
theorem computationalProjection3_kills_nonComputationalVec :
    computationalProjection3.mulVec nonComputationalVec = 0 := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, computationalProjection3, nonComputationalVec]

/-- Every projected finite three-state vector has zero non-computational coordinate. -/
theorem computationalProjection3_range_third_zero (v : Fin 3 → ℝ) :
    (computationalProjection3.mulVec v) 2 = 0 := by
  simp [Matrix.mulVec, computationalProjection3]

end InfoGeometry.Canonical.FibonacciParafermionAtoms
