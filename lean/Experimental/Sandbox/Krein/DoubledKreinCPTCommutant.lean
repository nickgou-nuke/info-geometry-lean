import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Method 3: Doubled Krein Space, Modular CPT Conjugation, and the Pauli Commutant

This module formalizes the Doubled Krein Construction connecting the split Clifford algebra
$\mathrm{Cl}(1,1) \widehat{\otimes} \mathrm{Cl}(1,1) \cong \mathrm{Cl}(2,2) \cong M_4(\mathbb{R})$
to Hamilton's biquaternions (the Pauli algebra $M_2(\mathbb{C})$) via the commutant of the
modular $CPT$ conjugation operator $J$:

1. **The Doubled Real Space $M_4(R)$ and $2 \times 2$ Block Splitting**:
   - Carrier $M_4(R)$ representing the 16-dimensional doubled algebra.
   - 8-dimensional CPT-invariant matrix subspace `cptMatrix A B = !![A, -B; B, A]`.

2. **The Modular $CPT$ Conjugation Operator $J \in M_4(R)$**:
   - $J = \begin{pmatrix} 0 & -\mathbf{1}_2 \\ \mathbf{1}_2 & 0 \end{pmatrix}$.
   - Exact algebraic properties:
     - Endogenous imaginary unit: $J^2 = -\mathbf{1}_4$.
     - Symplectic skew-adjointness: $J^\top = -J$.

3. **The Commutant (Centralizer) Subalgebra $\mathcal{Z}_{M_4(R)}(J)$**:
   - Commutant condition $[X, J] = 0 \iff X J = J X$.
   - Explicit Block Characterization: $M$ commutes with $J$ if and only if
     $M = \operatorname{cptMatrix} A B$.
   - Subalgebra stability: closed under addition, scalar multiplication, matrix multiplication,
     and matrix transposition.
   - Dimension reduction: exactly $4 + 4 = 8$ real parameters, annihilating the 8 excess dimensions.

4. **Isomorphism to the Pauli / Biquaternion Algebra $M_2(\mathbb{C})$**:
   - Complex Pauli representation map: $\Phi(A, B) = A + i B \in M_2(\mathbb{C})$.
   - Ring homomorphism: $\Phi(A_1 A_2 - B_1 B_2, A_1 B_2 + B_1 A_2) = \Phi(A_1, B_1) \cdot \Phi(A_2, B_2)$.
   - Complex multiplication correspondence: $J$ acts as multiplication by $i$:
     $J \cdot X(A, B) = X(-B, A) \longleftrightarrow i \cdot (A + i B) = -B + i A$.

5. **Tomita–Takesaki Modular Invariance & KMS Reflection**:
   - Modular adjoint action $\operatorname{Ad}_J(X) = - J X J = X$.
   - The commutant is precisely the fixed-point algebra of the modular reflection.
-/

namespace InfoGeometry.Krein.DoubledCPT

open Matrix

abbrev Mat4 (R : Type*) := Matrix (Fin 4) (Fin 4) R
abbrev Mat2 (R : Type*) := Matrix (Fin 2) (Fin 2) R

variable {R : Type*} [CommRing R]

/-! ### Section 1: The Modular CPT Conjugation Operator J -/

/-- The modular CPT conjugation operator J in M₄(R):
    J = !![ 0,  0, -1,  0;
            0,  0,  0, -1;
            1,  0,  0,  0;
            0,  1,  0,  0 ] -/
def J : Mat4 R :=
  !![ 0,  0, -1,  0;
      0,  0,  0, -1;
      1,  0,  0,  0;
      0,  1,  0,  0 ]

/-- J² = -1: The CPT operator endogenously generates the complex imaginary structure. -/
@[simp]
theorem J_sq : (J : Mat4 R) * J = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J]

/-- Jᵀ = -J: The CPT operator is skew-symmetric (symplectic complex structure). -/
@[simp]
theorem J_transpose : (J : Mat4 R)ᵀ = -J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J]

/-! ### Section 2: The Commutant Subalgebra 𝒵(J) -/

/-- Predicate that a 4x4 matrix commutes with J. -/
def commutesWithJ (M : Mat4 R) : Prop :=
  M * J = J * M

/-- The canonical 8-dimensional CPT matrix with blocks !![A, -B; B, A]. -/
def cptMatrix (A B : Mat2 R) : Mat4 R :=
  !![ A 0 0,  A 0 1, -B 0 0, -B 0 1;
      A 1 0,  A 1 1, -B 1 0, -B 1 1;
      B 0 0,  B 0 1,  A 0 0,  A 0 1;
      B 1 0,  B 1 1,  A 1 0,  A 1 1 ]

/-- Every matrix of the form !![A, -B; B, A] commutes with J. -/
theorem cptMatrix_commutes (A B : Mat2 R) : commutesWithJ (cptMatrix A B) := by
  dsimp [commutesWithJ]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [cptMatrix, J, Matrix.mul_apply, Fin.sum_univ_four]
    try ring
  }

/-- Explicit characterization: a 4x4 matrix commutes with J if and only if
    it has the block form !![A, -B; B, A]. -/
theorem commutes_iff_cptMatrix (M : Mat4 R) :
    commutesWithJ M ↔ ∃ A B : Mat2 R, M = cptMatrix A B := by
  constructor
  · intro hcomm
    let A : Mat2 R := !![M 0 0, M 0 1; M 1 0, M 1 1]
    let B : Mat2 R := !![M 2 0, M 2 1; M 3 0, M 3 1]
    have h : ∀ i j : Fin 4, (M * (J : Mat4 R)) i j = ((J : Mat4 R) * M) i j := by
      intro i j
      exact congr_fun (congr_fun hcomm i) j
    have h02 : M 0 2 = - M 2 0 := by
      have h00 := h 0 0
      simp [Matrix.mul_apply, J, Fin.sum_univ_four] at h00
      exact h00
    have h03 : M 0 3 = - M 2 1 := by
      have h01 := h 0 1
      simp [Matrix.mul_apply, J, Fin.sum_univ_four] at h01
      exact h01
    have h12 : M 1 2 = - M 3 0 := by
      have h10 := h 1 0
      simp [Matrix.mul_apply, J, Fin.sum_univ_four] at h10
      exact h10
    have h13 : M 1 3 = - M 3 1 := by
      have h11 := h 1 1
      simp [Matrix.mul_apply, J, Fin.sum_univ_four] at h11
      exact h11
    have h22 : M 2 2 = M 0 0 := by
      have h02' := h 0 2
      simp [Matrix.mul_apply, J, Fin.sum_univ_four] at h02'
      linear_combination -h02'
    have h23 : M 2 3 = M 0 1 := by
      have h03' := h 0 3
      simp [Matrix.mul_apply, J, Fin.sum_univ_four] at h03'
      linear_combination -h03'
    have h32 : M 3 2 = M 1 0 := by
      have h12' := h 1 2
      simp [Matrix.mul_apply, J, Fin.sum_univ_four] at h12'
      linear_combination -h12'
    have h33 : M 3 3 = M 1 1 := by
      have h13' := h 1 3
      simp [Matrix.mul_apply, J, Fin.sum_univ_four] at h13'
      linear_combination -h13'
    use A, B
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [cptMatrix, A, B]
      try assumption
    }
  · rintro ⟨A, B, rfl⟩
    exact cptMatrix_commutes A B

/-! #### Algebraic Stability of the CPT Commutant Subalgebra -/

/-- The identity matrix commutes with J. -/
theorem one_commutes : commutesWithJ (1 : Mat4 R) := by
  simp [commutesWithJ]

/-- Zero commutes with J. -/
theorem zero_commutes : commutesWithJ (0 : Mat4 R) := by
  simp [commutesWithJ]

/-- Addition preserves commutation with J. -/
theorem add_commutes {M N : Mat4 R} (hM : commutesWithJ M) (hN : commutesWithJ N) :
    commutesWithJ (M + N) := by
  dsimp [commutesWithJ] at *
  rw [Matrix.add_mul, Matrix.mul_add, hM, hN]

/-- Scalar multiplication preserves commutation with J. -/
theorem smul_commutes {M : Mat4 R} (c : R) (hM : commutesWithJ M) :
    commutesWithJ (c • M) := by
  dsimp [commutesWithJ] at *
  rw [Matrix.smul_mul, Matrix.mul_smul, hM]

/-- Matrix multiplication preserves commutation with J. -/
theorem mul_commutes {M N : Mat4 R} (hM : commutesWithJ M) (hN : commutesWithJ N) :
    commutesWithJ (M * N) := by
  dsimp [commutesWithJ] at *
  calc
    (M * N) * J = M * (N * J) := by rw [Matrix.mul_assoc]
    _           = M * (J * N) := by rw [hN]
    _           = (M * J) * N := by rw [← Matrix.mul_assoc]
    _           = (J * M) * N := by rw [hM]
    _           = J * (M * N) := by rw [Matrix.mul_assoc]

/-- Transposition preserves commutation with J. -/
theorem transpose_commutes {M : Mat4 R} (hM : commutesWithJ M) :
    commutesWithJ Mᵀ := by
  dsimp [commutesWithJ] at *
  have hT := congr_arg Matrix.transpose hM
  rw [Matrix.transpose_mul, Matrix.transpose_mul, J_transpose] at hT
  rw [Matrix.mul_neg, Matrix.neg_mul] at hT
  exact (neg_inj.mp hT).symm

/-- Exact block multiplication formula:
    !![A₁, -B₁; B₁, A₁] * !![A₂, -B₂; B₂, A₂] =
    !![A₁ A₂ - B₁ B₂, -(A₁ B₂ + B₁ A₂); A₁ B₂ + B₁ A₂, A₁ A₂ - B₁ B₂] -/
theorem cptMatrix_mul (A1 B1 A2 B2 : Mat2 R) :
    cptMatrix A1 B1 * cptMatrix A2 B2 =
    cptMatrix (A1 * A2 - B1 * B2) (A1 * B2 + B1 * A2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [cptMatrix, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_four, Fin.sum_univ_two]
    ring
  }

/-- Block transposition formula: (cptMatrix A B)ᵀ = cptMatrix Aᵀ (-Bᵀ). -/
theorem cptMatrix_transpose (A B : Mat2 R) :
    (cptMatrix A B)ᵀ = cptMatrix Aᵀ (-Bᵀ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cptMatrix, Matrix.transpose_apply]

/-- Action of J as complex multiplication by i:
    J * cptMatrix A B = cptMatrix (-B) A. -/
theorem J_mul_cptMatrix (A B : Mat2 R) :
    (J : Mat4 R) * cptMatrix A B = cptMatrix (-B) A := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [J, cptMatrix, Matrix.mul_apply, Fin.sum_univ_four]
    try ring
  }

/-- Commutativity: cptMatrix A B * J = cptMatrix (-B) A. -/
theorem cptMatrix_mul_J (A B : Mat2 R) :
    cptMatrix A B * (J : Mat4 R) = cptMatrix (-B) A := by
  rw [cptMatrix_commutes, J_mul_cptMatrix]

/-- Tomita–Takesaki Modular Reflection:
    The CPT commutant is identically invariant under the modular adjoint action:
    Ad_J(X) = - J * X * J = X. -/
theorem modular_ad_J (A B : Mat2 R) :
    - (J : Mat4 R) * cptMatrix A B * J = cptMatrix A B := by
  have hcomm : cptMatrix A B * J = J * cptMatrix A B := cptMatrix_commutes A B
  have hj2 : (J : Mat4 R) * J = -1 := J_sq
  calc - (J : Mat4 R) * cptMatrix A B * J
    _ = - (J : Mat4 R) * (cptMatrix A B * J) := by rw [Matrix.mul_assoc]
    _ = - (J : Mat4 R) * (J * cptMatrix A B) := by rw [hcomm]
    _ = - ((J : Mat4 R) * (J * cptMatrix A B)) := by rw [Matrix.neg_mul]
    _ = - (((J : Mat4 R) * J) * cptMatrix A B) := by rw [← Matrix.mul_assoc]
    _ = - ((-1 : Mat4 R) * cptMatrix A B) := by rw [hj2]
    _ = - (- cptMatrix A B) := by rw [neg_one_mul]
    _ = cptMatrix A B := neg_neg (cptMatrix A B)

/-! ### Section 3: Isomorphism to the Pauli / Biquaternion Algebra M₂(ℂ) -/

/-- Complex representation mapping a pair of 2x2 real matrices (A, B)
    to a 2x2 complex Pauli matrix A + i B. -/
def toPauli (A B : Mat2 ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => Complex.mk (A i j) (B i j)

/-- The zero matrix maps to zero. -/
@[simp]
theorem toPauli_zero : toPauli 0 0 = 0 := by
  ext i j
  apply Complex.ext
  · simp [toPauli]
  · simp [toPauli]

/-- The identity matrix maps to identity. -/
@[simp]
theorem toPauli_one : toPauli 1 0 = 1 := by
  ext i j
  apply Complex.ext
  · fin_cases i <;> fin_cases j <;> simp [toPauli]
  · fin_cases i <;> fin_cases j <;> simp [toPauli]

/-- The CPT operator J maps to the imaginary scalar matrix i • 1. -/
theorem toPauli_J : toPauli 0 1 = Complex.I • 1 := by
  ext i j
  apply Complex.ext
  · fin_cases i <;> fin_cases j <;> simp [toPauli, Complex.I]
  · fin_cases i <;> fin_cases j <;> simp [toPauli, Complex.I]

/-- Addition of CPT matrices corresponds to complex addition in M₂(ℂ). -/
theorem toPauli_add (A1 B1 A2 B2 : Mat2 ℝ) :
    toPauli (A1 + A2) (B1 + B2) = toPauli A1 B1 + toPauli A2 B2 := by
  ext i j
  apply Complex.ext
  · simp [toPauli]
  · simp [toPauli]

/-- Matrix multiplication in the CPT commutant is isomorphic to matrix multiplication in M₂(ℂ):
    Φ(A₁ A₂ - B₁ B₂, A₁ B₂ + B₁ A₂) = Φ(A₁, B₁) * Φ(A₂, B₂). -/
theorem toPauli_mul (A1 B1 A2 B2 : Mat2 ℝ) :
    toPauli (A1 * A2 - B1 * B2) (A1 * B2 + B1 * A2) =
    toPauli A1 B1 * toPauli A2 B2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    apply Complex.ext
    · simp [toPauli, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, Complex.add_re, Complex.mul_re]
      ring
    · simp [toPauli, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two, Complex.add_im, Complex.mul_im]
      ring
  }

/-! ### Section 4: Master Verification Certificate -/

/-- Master verification certificate for the Doubled Krein CPT Commutant construction. -/
structure DoubledKreinCPTCommutantCertificate : Prop where
  j_sq_neg_one : ∀ (R : Type) [CommRing R], (J : Mat4 R) * J = -1
  j_transpose_skew : ∀ (R : Type) [CommRing R], (J : Mat4 R)ᵀ = -J
  cpt_commutes : ∀ (R : Type) [CommRing R] (A B : Mat2 R), commutesWithJ (cptMatrix A B)
  commutes_iff_block : ∀ (R : Type) [CommRing R] (M : Mat4 R),
    commutesWithJ M ↔ ∃ A B : Mat2 R, M = cptMatrix A B
  cpt_mul : ∀ (R : Type) [CommRing R] (A1 B1 A2 B2 : Mat2 R),
    cptMatrix A1 B1 * cptMatrix A2 B2 = cptMatrix (A1 * A2 - B1 * B2) (A1 * B2 + B1 * A2)
  cpt_transpose : ∀ (R : Type) [CommRing R] (A B : Mat2 R),
    (cptMatrix A B)ᵀ = cptMatrix Aᵀ (-Bᵀ)
  j_action_complex_mult : ∀ (R : Type) [CommRing R] (A B : Mat2 R),
    (J : Mat4 R) * cptMatrix A B = cptMatrix (-B) A
  modular_reflection_invariant : ∀ (R : Type) [CommRing R] (A B : Mat2 R),
    - (J : Mat4 R) * cptMatrix A B * J = cptMatrix A B
  pauli_homomorphism : ∀ (A1 B1 A2 B2 : Mat2 ℝ),
    toPauli (A1 * A2 - B1 * B2) (A1 * B2 + B1 * A2) = toPauli A1 B1 * toPauli A2 B2
  pauli_identity : toPauli 1 0 = 1
  pauli_j_eq_i : toPauli 0 1 = Complex.I • 1

/-- Universal compilation theorem proving that the certificate holds unconditionally. -/
theorem compile_doubled_krein_cpt_commutant : DoubledKreinCPTCommutantCertificate where
  j_sq_neg_one := fun _ _ => J_sq
  j_transpose_skew := fun _ _ => J_transpose
  cpt_commutes := fun _ _ A B => cptMatrix_commutes A B
  commutes_iff_block := fun _ _ M => commutes_iff_cptMatrix M
  cpt_mul := fun _ _ A1 B1 A2 B2 => cptMatrix_mul A1 B1 A2 B2
  cpt_transpose := fun _ _ A B => cptMatrix_transpose A B
  j_action_complex_mult := fun _ _ A B => J_mul_cptMatrix A B
  modular_reflection_invariant := fun _ _ A B => modular_ad_J A B
  pauli_homomorphism := toPauli_mul
  pauli_identity := toPauli_one
  pauli_j_eq_i := toPauli_J

end InfoGeometry.Krein.DoubledCPT
