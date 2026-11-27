/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Section 85: Kantor–Tanaka Super-Grassmannian Lie Bracket, Superconformal Symmetry & Spinor Bilinears

This module completes and expands the 5-graded Lie superalgebra architecture (Section 84),
formalizing the full Kantor–Tanaka construction on the $M_3(R)$ supercarrier:

$$\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_1 \oplus \mathfrak{g}_2$$

### Key Architectural Results:
1. **The Lie Superalgebra Bracket**:
   The commutator $[X, Y] = XY - YX$ satisfies antisymmetry, the Jacobi identity,
   and the derivation identity with respect to the Cartan grading element $H$.
2. **The Odd-Odd Contact Bracket & Spinor Bilinears**:
   - The bracket of odd supercharges generates the contact element in $\mathfrak{g}_2$:
     $$[E_{01}, E_{12}] = E_{02}$$
   - The bracket of conjugate supercharges generates the dual contact element in $\mathfrak{g}_{-2}$:
     $$[E_{21}, E_{10}] = E_{20}$$
   - The extremal bracket generates the grading Hamiltonian $H$:
     $$[E_{02}, E_{20}] = H$$
   - The sum of the chiral spinor bilinears reconstructs the central conformal Hamiltonian:
     $$[E_{01}, E_{10}] + [E_{12}, E_{21}] = H$$
3. **Grade Truncation**:
   Vanishing of brackets beyond the boundary:
   $$[\mathfrak{g}_2, \mathfrak{g}_1] = 0, \qquad [\mathfrak{g}_{-2}, \mathfrak{g}_{-1}] = 0$$
4. **The Krein Sheet-Swap Involution $J$**:
   The anti-diagonal involution $J^2 = \mathbf{1}$ inverts the grading:
   $$J H J = - H, \qquad J \mathfrak{g}_p J = \mathfrak{g}_{-p}$$
   and acts as a Lie algebra automorphism on all brackets.
5. **Graded Supertrace & Killing Orthogonality**:
   The supertrace $\operatorname{STr}(X) = X_{00} - X_{11} + X_{22}$ satisfies:
   - $\operatorname{STr}(H) = 0$
   - $\operatorname{STr}(E_{02} E_{20}) = 1$ (canonical duality pairing $\mathfrak{g}_2 \times \mathfrak{g}_{-2} \to R$)
   - Orthogonality $\operatorname{STr}(X Y) = 0$ whenever $\operatorname{grade}(X) + \operatorname{grade}(Y) \ne 0$.

All proofs are native Mathlib 4 with 0 sorry, 0 admit, and 0 custom axioms.
-/

namespace InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian

open scoped Matrix BigOperators

variable {R : Type*} [Ring R]

/-! ### Section 1: Matrix Units and the Cartan Grading Element -/

/-- Elementary matrix units in $M_3(R)$. -/
def E (i j : Fin 3) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun r c => if r = i ∧ c = j then 1 else 0

/-- The Cartan grading element $H = \operatorname{diag}(1, 0, -1) \in \mathfrak{sl}(3, R)$. -/
def H (R : Type*) [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal ![(1 : R), 0, -1]

/-- The Lie bracket (commutator) on $M_3(R)$. -/
def bracket (X Y : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  X * Y - Y * X

/-! ### Section 2: General Bracket Identities (Antisymmetry, Jacobi, Derivation) -/

/-- Antisymmetry of the Lie bracket: $[X, Y] = - [Y, X]$. -/
theorem bracket_skew (X Y : Matrix (Fin 3) (Fin 3) R) :
    bracket X Y = - bracket Y X := by
  unfold bracket
  ext i j
  simp only [Matrix.sub_apply, Matrix.neg_apply]
  abel

/-- Self-bracket vanishes: $[X, X] = 0$. -/
theorem bracket_self (X : Matrix (Fin 3) (Fin 3) R) :
    bracket X X = 0 := by
  unfold bracket
  ext i j
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_self]

/-- The Lie Jacobi identity: $[X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]] = 0$. -/
theorem jacobi_identity (X Y Z : Matrix (Fin 3) (Fin 3) R) :
    bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0 := by
  unfold bracket
  noncomm_ring

/-- The adjoint action of $H$ is a Lie derivation: $[H, [X, Y]] = [[H, X], Y] + [X, [H, Y]]$. -/
theorem derivation_identity (H X Y : Matrix (Fin 3) (Fin 3) R) :
    bracket H (bracket X Y) = bracket (bracket H X) Y + bracket X (bracket H Y) := by
  unfold bracket
  noncomm_ring

/-! ### Section 3: The Fundamental Tanaka-Kantor Graded Brackets -/

/-- **Theorem**: Odd Supercharge Squaring into Grade $+2$ (Contact Element):
    $[E_{01}, E_{12}] = E_{02}$. -/
theorem odd_contact_bracket :
    bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 2) = E 0 2 := by
  unfold bracket E
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- **Theorem**: Conjugate Odd Supercharge Squaring into Grade $-2$ (Dual Contact Element):
    $[E_{21}, E_{10}] = E_{20}$. -/
theorem odd_contact_bracket_conjugate :
    bracket (E 2 1 : Matrix (Fin 3) (Fin 3) R) (E 1 0) = E 2 0 := by
  unfold bracket E
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- **Theorem**: Extremal Bracket Generates the Cartan Element $H$:
    $[E_{02}, E_{20}] = H$. -/
theorem extremal_bracket_generates_H :
    bracket (E 0 2 : Matrix (Fin 3) (Fin 3) R) (E 2 0) = H R := by
  unfold bracket E H
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- **Theorem**: Elementary Spinor Bilinear (Channel 01-10):
    $[E_{01}, E_{10}] = E_{00} - E_{11}$. -/
theorem spinor_bilinear_01_10 :
    bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 0) = E 0 0 - E 1 1 := by
  unfold bracket E
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- **Theorem**: Elementary Spinor Bilinear (Channel 12-21):
    $[E_{12}, E_{21}] = E_{11} - E_{22}$. -/
theorem spinor_bilinear_12_21 :
    bracket (E 1 2 : Matrix (Fin 3) (Fin 3) R) (E 2 1) = E 1 1 - E 2 2 := by
  unfold bracket E
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- **Master Theorem**: Chiral Spinor Bilinear Sum Reconstructs the Conformal Hamiltonian:
    $[E_{01}, E_{10}] + [E_{12}, E_{21}] = H$. -/
theorem spinor_bilinear_sum_eq_H :
    bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 0) +
    bracket (E 1 2) (E 2 1) = H R := by
  rw [spinor_bilinear_01_10, spinor_bilinear_12_21]
  unfold E H
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply]

/-! ### Section 4: Grade Truncation Beyond the 5-Graded Boundary -/

/-- Grade $+2$ and Grade $+1$ truncate: $[E_{02}, E_{01}] = 0$. -/
theorem grade_truncation_2_1a :
    bracket (E 0 2 : Matrix (Fin 3) (Fin 3) R) (E 0 1) = 0 := by
  unfold bracket E
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- Grade $+2$ and Grade $+1$ truncate: $[E_{02}, E_{12}] = 0$. -/
theorem grade_truncation_2_1b :
    bracket (E 0 2 : Matrix (Fin 3) (Fin 3) R) (E 1 2) = 0 := by
  unfold bracket E
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- Grade $-2$ and Grade $-1$ truncate: $[E_{20}, E_{10}] = 0$. -/
theorem grade_truncation_neg2_neg1a :
    bracket (E 2 0 : Matrix (Fin 3) (Fin 3) R) (E 1 0) = 0 := by
  unfold bracket E
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- Grade $-2$ and Grade $-1$ truncate: $[E_{20}, E_{21}] = 0$. -/
theorem grade_truncation_neg2_neg1b :
    bracket (E 2 0 : Matrix (Fin 3) (Fin 3) R) (E 2 1) = 0 := by
  unfold bracket E
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-! ### Section 5: The Krein / Paracomplex Sheet-Swap Involution $J$ -/

/-- The paracomplex / Krein anti-diagonal sheet-swap involution $J$. -/
def J (R : Type*) [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun r c => if (r : ℕ) + (c : ℕ) = 2 then 1 else 0

/-- Left multiplication by $J$ reflects row indices: $(J X)_{i, j} = X_{2-i, j}$. -/
def JX (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R := (J R) * X

theorem JX_apply (X : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    JX X i j = X (2 - i) j := by
  dsimp [JX, J]
  fin_cases i <;> {
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  }

/-- Right multiplication by $J$ reflects column indices: $(X J)_{i, j} = X_{i, 2-j}$. -/
def XJ (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R := X * (J R)

theorem XJ_apply (X : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    XJ X i j = X i (2 - j) := by
  dsimp [XJ, J]
  fin_cases j <;> {
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  }

/-- The bilateral adjoint action of $J$: $\operatorname{swap}(X) = J X J$. -/
def swap (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  (J R) * X * (J R)

/-- Componentwise reflection under $J$: $(J X J)_{i, j} = X_{2-i, 2-j}$. -/
theorem swap_apply (X : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    swap X i j = X (2 - i) (2 - j) := by
  change XJ (JX X) i j = X (2 - i) (2 - j)
  rw [XJ_apply, JX_apply]

/-- $J$ is strictly involutive: $J^2 = \mathbf{1}$. -/
theorem J_involutive :
    (J R) * (J R) = 1 := by
  ext i j
  change JX (J R) i j = (1 : Matrix (Fin 3) (Fin 3) R) i j
  rw [JX_apply]
  dsimp [J]
  fin_cases i <;> fin_cases j <;> simp

/-- **Theorem**: $J$ inverts the grading Hamiltonian: $J H J = - H$. -/
theorem J_inverts_H :
    swap (H R) = - H R := by
  ext i j
  rw [swap_apply]
  dsimp [H]
  fin_cases i <;> fin_cases j <;> simp

/-- **Theorem**: $J$ exchanges Grade $+2$ and Grade $-2$: $J E_{02} J = E_{20}$. -/
theorem J_inverts_grade_two :
    swap (E 0 2 : Matrix (Fin 3) (Fin 3) R) = E 2 0 := by
  ext i j
  rw [swap_apply]
  dsimp [E]
  fin_cases i <;> fin_cases j <;> simp

/-- **Theorem**: $J$ exchanges odd supercharges: $J E_{01} J = E_{21}$. -/
theorem J_inverts_grade_one_a :
    swap (E 0 1 : Matrix (Fin 3) (Fin 3) R) = E 2 1 := by
  ext i j
  rw [swap_apply]
  dsimp [E]
  fin_cases i <;> fin_cases j <;> simp

/-- **Theorem**: $J$ exchanges odd supercharges: $J E_{12} J = E_{10}$. -/
theorem J_inverts_grade_one_b :
    swap (E 1 2 : Matrix (Fin 3) (Fin 3) R) = E 1 0 := by
  ext i j
  rw [swap_apply]
  dsimp [E]
  fin_cases i <;> fin_cases j <;> simp

/-- **Theorem**: $J$ is a Lie algebra automorphism on $M_3(R)$:
    $J [X, Y] J = [J X J, J Y J]$. -/
theorem J_lie_automorphism (X Y : Matrix (Fin 3) (Fin 3) R) :
    (J R) * (bracket X Y) * (J R) = bracket ((J R) * X * (J R)) ((J R) * Y * (J R)) := by
  have hJ : (J R) * (J R) = 1 := J_involutive
  unfold bracket
  calc
    (J R) * (X * Y - Y * X) * (J R)
      = (J R) * (X * 1 * Y - Y * 1 * X) * (J R) := by simp only [mul_one]
    _ = (J R) * (X * ((J R) * (J R)) * Y - Y * ((J R) * (J R)) * X) * (J R) := by rw [hJ]
    _ = ((J R) * X * (J R)) * ((J R) * Y * (J R)) - ((J R) * Y * (J R)) * ((J R) * X * (J R)) := by
      noncomm_ring

/-! ### Section 6: Graded Supertrace and Invariant Duality Pairing -/

/-- The graded supertrace $\operatorname{STr}(X) = X_{00} - X_{11} + X_{22}$. -/
def supertrace (X : Matrix (Fin 3) (Fin 3) R) : R :=
  X 0 0 - X 1 1 + X 2 2

/-- **Theorem**: The supertrace of the Cartan Hamiltonian vanishes: $\operatorname{STr}(H) = 0$. -/
theorem supertrace_H :
    supertrace (H R) = 0 := by
  dsimp [supertrace, H]
  simp

/-- **Theorem**: Non-degenerate duality pairing between Grade $+2$ and Grade $-2$:
    $\operatorname{STr}(E_{02} E_{20}) = 1$. -/
theorem supertrace_E02_E20 :
    supertrace ((E 0 2 : Matrix (Fin 3) (Fin 3) R) * E 2 0) = 1 := by
  dsimp [supertrace, E]
  simp [Matrix.mul_apply]

/-- **Theorem**: Supertrace orthogonality of Grade $+2$ and Grade $+1$:
    $\operatorname{STr}(E_{02} E_{01}) = 0$. -/
theorem supertrace_E02_E01_orthogonal :
    supertrace ((E 0 2 : Matrix (Fin 3) (Fin 3) R) * E 0 1) = 0 := by
  dsimp [supertrace, E]
  simp [Matrix.mul_apply]

/-- **Theorem**: Supertrace orthogonality of Grade $+1$ with itself:
    $\operatorname{STr}(E_{01} E_{01}) = 0$. -/
theorem supertrace_E01_E01_orthogonal :
    supertrace ((E 0 1 : Matrix (Fin 3) (Fin 3) R) * E 0 1) = 0 := by
  dsimp [supertrace, E]
  simp [Matrix.mul_apply]

/-- **Theorem**: Supertrace orthogonality of Grade $+2$ with itself:
    $\operatorname{STr}(E_{02} E_{02}) = 0$. -/
theorem supertrace_E02_E02_orthogonal :
    supertrace ((E 0 2 : Matrix (Fin 3) (Fin 3) R) * E 0 2) = 0 := by
  dsimp [supertrace, E]
  simp [Matrix.mul_apply]

/-! ### Section 7: Master Certification Inscription -/

/-- Master certificate bundling the complete 5-graded Kantor–Tanaka theorems. -/
def KantorTanakaSuperGrassmannianCertificate : Prop :=
  (∀ X Y : Matrix (Fin 3) (Fin 3) R, bracket X Y = - bracket Y X) ∧
  (∀ X Y Z : Matrix (Fin 3) (Fin 3) R,
    bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0) ∧
  (∀ H X Y : Matrix (Fin 3) (Fin 3) R,
    bracket H (bracket X Y) = bracket (bracket H X) Y + bracket X (bracket H Y)) ∧
  (bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 2) = E 0 2) ∧
  (bracket (E 2 1 : Matrix (Fin 3) (Fin 3) R) (E 1 0) = E 2 0) ∧
  (bracket (E 0 2 : Matrix (Fin 3) (Fin 3) R) (E 2 0) = H R) ∧
  (bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 0) + bracket (E 1 2) (E 2 1) = H R) ∧
  (bracket (E 0 2 : Matrix (Fin 3) (Fin 3) R) (E 0 1) = 0) ∧
  (bracket (E 2 0 : Matrix (Fin 3) (Fin 3) R) (E 1 0) = 0) ∧
  ((J R) * (J R) = 1) ∧
  (swap (H R) = - H R) ∧
  (swap (E 0 2 : Matrix (Fin 3) (Fin 3) R) = E 2 0) ∧
  (∀ X Y : Matrix (Fin 3) (Fin 3) R,
    (J R) * (bracket X Y) * (J R) = bracket ((J R) * X * (J R)) ((J R) * Y * (J R))) ∧
  (supertrace (H R) = 0) ∧
  (supertrace ((E 0 2 : Matrix (Fin 3) (Fin 3) R) * E 2 0) = 1) ∧
  (supertrace ((E 0 2 : Matrix (Fin 3) (Fin 3) R) * E 0 1) = 0)

/-- **Master Gate**: Full Kantor–Tanaka Super-Grassmannian verification. -/
theorem compile_kantor_tanaka_super_grassmannian :
    KantorTanakaSuperGrassmannianCertificate (R := R) :=
  ⟨bracket_skew, jacobi_identity, derivation_identity, odd_contact_bracket,
    odd_contact_bracket_conjugate, extremal_bracket_generates_H, spinor_bilinear_sum_eq_H,
    grade_truncation_2_1a, grade_truncation_neg2_neg1a, J_involutive, J_inverts_H,
    J_inverts_grade_two, J_lie_automorphism, supertrace_H, supertrace_E02_E20,
    supertrace_E02_E01_orthogonal⟩

/-! ### Section 8: Genuine ℤ₂-Graded Supercommutator, 5-Grading & OSp(1|2) Matching -/

section GradedSuperbracket

open InfoGeometry.Algebra.SupergradedBracket

/-- Explicit noncommutativity witness for the `M₃(R)` supercarrier. -/
theorem kt_matrix_noncomm [Nontrivial R] :
    (E 0 1 : Matrix (Fin 3) (Fin 3) R) * E 1 0 ≠ E 1 0 * E 0 1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) h
  simp [E, Matrix.mul_apply] at h00

/-- Existential noncommutativity witness in `Matrix (Fin 3) (Fin 3) R`. -/
theorem kt_matrix_noncomm_exists [Nontrivial R] :
    ∃ A B : Matrix (Fin 3) (Fin 3) R, A * B ≠ B * A := by
  exact ⟨E 0 1, E 1 0, kt_matrix_noncomm⟩

/-- Koszul sign `(-1)^{p q} ∈ {1, -1}` in `ℤ` for `ℤ₂`-graded parity inputs `p, q : Bool`. -/
def koszulSignZ (p q : Bool) : ℤ :=
  if p && q then -1 else 1

/-- Graded skew-symmetry of `SupergradedBracket.superBracket` over any associative ring `A`:
`[x, y]_s = -(-1)^{p q} [y, x]_s`. -/
theorem assoc_superBracket_skew {A : Type*} [Ring A] (p q : Bool) (x y : A) :
    superBracket p q x y = (-koszulSignZ p q) • superBracket q p y x := by
  cases p <;> cases q <;>
    (simp [superBracket, koszulSignZ,
      InfoGeometry.Algebra.SupergradedBracket.commutator, anticommutator]; try abel)

/-- Graded Jacobi identity for `SupergradedBracket.superBracket` over any associative ring `A`. -/
theorem assoc_superBracket_jacobi {A : Type*} [Ring A] (p q r : Bool) (x y z : A) :
    (koszulSignZ p r) • superBracket p (xor q r) x (superBracket q r y z) +
      (koszulSignZ q p) • superBracket q (xor r p) y (superBracket r p z x) +
      (koszulSignZ r q) • superBracket r (xor p q) z (superBracket p q x y) = 0 := by
  cases p <;> cases q <;> cases r <;>
    dsimp [superBracket, koszulSignZ,
      InfoGeometry.Algebra.SupergradedBracket.commutator, anticommutator] <;>
    simp only [one_zsmul, neg_smul] <;>
    noncomm_ring

/-- Graded Leibniz derivation identity for `SupergradedBracket.superBracket` over any ring `A`. -/
theorem assoc_superBracket_derivation {A : Type*} [Ring A] (p q r : Bool) (x y z : A) :
    superBracket p (xor q r) x (superBracket q r y z) =
      superBracket (xor p q) r (superBracket p q x y) z +
        (koszulSignZ p q) • superBracket q (xor p r) y (superBracket p r x z) := by
  cases p <;> cases q <;> cases r <;>
    dsimp [superBracket, koszulSignZ,
      InfoGeometry.Algebra.SupergradedBracket.commutator, anticommutator] <;>
    simp only [one_zsmul, neg_smul] <;>
    noncomm_ring

/-- Genuine `ℤ₂`-graded superbracket on `M₃(R)`. -/
abbrev ktSuperBracket (p q : Bool) (X Y : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
  InfoGeometry.Algebra.SupergradedBracket.superBracket p q X Y

/-- Graded Cartan adjoint action `ad_H(X) = [H, X]_s` on `M₃(R)`. -/
def ktAdH (p : Bool) (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  ktSuperBracket false p (H R) X

/-- Weight of matrix entry `(i, j)` under the Cartan grading `H = diag(1, 0, -1)`. -/
def matrixWeight (i j : Fin 3) : ℤ := (j : ℤ) - (i : ℤ)

/-- `ℤ₂` parity induced by a `ℤ`-grading weight `k` (`true` iff `k` is odd). -/
def weightParity (k : ℤ) : Bool := decide (k % 2 ≠ 0)

/-- The `(2|1)` grading `(0,2 | 1)` parity in `SuperconformalOSpJordanPair.entryParity` is
determined identically by the parity of the Cartan grading weight `j - i`. -/
theorem entryParity_eq_weightParity (i j : Fin 3) :
    SuperconformalOSpJordanPair.entryParity i j = weightParity (matrixWeight i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [SuperconformalOSpJordanPair.entryParity, weightParity, matrixWeight]

/-- Submodule of `M₃(R)` consisting of matrices supported on entries of weight `k : ℤ`. -/
def gradeSubmodule (R : Type*) [Ring R] (k : ℤ) :
    Submodule R (Matrix (Fin 3) (Fin 3) R) where
  carrier := {X | ∀ i j : Fin 3, matrixWeight i j ≠ k → X i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro X Y hX hY i j hij
    simp [hX i j hij, hY i j hij]
  smul_mem' := by
    intro r X hX i j hij
    simp [hX i j hij]

/-- Submodule of `M₃(R)` consisting of `ℤ₂`-homogeneous matrices of parity `p : Bool`. -/
def paritySubmodule (R : Type*) [Ring R] (p : Bool) :
    Submodule R (Matrix (Fin 3) (Fin 3) R) where
  carrier := {X | SuperconformalOSpJordanPair.IsHomogeneous p X}
  zero_mem' := by
    intro i j hzero
    exact absurd rfl hzero
  add_mem' := by
    intro X Y hX hY i j hij
    by_cases hXi : X i j = 0
    · have hYi : Y i j ≠ 0 := by
        intro h0
        apply hij
        simp [hXi, h0]
      exact hY i j hYi
    · exact hX i j hXi
  smul_mem' := by
    intro r X hX i j hij
    apply hX i j
    intro h0
    apply hij
    simp [h0]

/-- Every weight-`k` grade submodule lies inside the parity submodule of `weightParity k`. -/
theorem gradeSubmodule_le_paritySubmodule (k : ℤ) :
    gradeSubmodule R k ≤ paritySubmodule R (weightParity k) := by
  intro X hX i j hij
  rw [entryParity_eq_weightParity]
  by_cases hw : matrixWeight i j = k
  · rw [hw]
  · exact absurd (hX i j hw) hij

/-- Explicit `ℤ₂`-homogeneous decomposition `X = X₀ + X₁` into even `(0,2)` and odd `(1)` blocks. -/
theorem matrix_decomp_even_odd (X : Matrix (Fin 3) (Fin 3) R) :
    ∃ X₀ ∈ paritySubmodule R false, ∃ X₁ ∈ paritySubmodule R true, X = X₀ + X₁ := by
  let X₀ : Matrix (Fin 3) (Fin 3) R :=
    Matrix.of fun i j => if SuperconformalOSpJordanPair.entryParity i j = false then X i j else 0
  let X₁ : Matrix (Fin 3) (Fin 3) R :=
    Matrix.of fun i j => if SuperconformalOSpJordanPair.entryParity i j = true then X i j else 0
  refine ⟨X₀, ?_, X₁, ?_, ?_⟩
  · intro i j hij
    dsimp [X₀] at hij ⊢
    by_cases hp : SuperconformalOSpJordanPair.entryParity i j = false
    · exact hp
    · simp [hp] at hij
  · intro i j hij
    dsimp [X₁] at hij ⊢
    by_cases hp : SuperconformalOSpJordanPair.entryParity i j = true
    · exact hp
    · simp [hp] at hij
  · ext i j
    cases hp : SuperconformalOSpJordanPair.entryParity i j <;> simp [X₀, X₁, hp]

/-- Explicit 5-graded decomposition `X = X₋₂ + X₋₁ + X₀ + X₁ + X₂` in `M₃(R)`. -/
theorem matrix_decomp_five_graded (X : Matrix (Fin 3) (Fin 3) R) :
    ∃ Xm2 ∈ gradeSubmodule R (-2), ∃ Xm1 ∈ gradeSubmodule R (-1),
      ∃ X0 ∈ gradeSubmodule R 0, ∃ Xp1 ∈ gradeSubmodule R 1,
      ∃ Xp2 ∈ gradeSubmodule R 2,
      X = Xm2 + Xm1 + X0 + Xp1 + Xp2 := by
  let proj (k : ℤ) : Matrix (Fin 3) (Fin 3) R :=
    Matrix.of fun i j => if matrixWeight i j = k then X i j else 0
  have hmem : ∀ k : ℤ, proj k ∈ gradeSubmodule R k := by
    intro k i j hij
    simp [proj, hij]
  refine ⟨proj (-2), hmem (-2), proj (-1), hmem (-1), proj 0, hmem 0,
    proj 1, hmem 1, proj 2, hmem 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj, matrixWeight]

/-- Graded skew-symmetry of `ktSuperBracket` on `M₃(R)`. -/
theorem ktSuperBracket_skew (p q : Bool) (X Y : Matrix (Fin 3) (Fin 3) R) :
    ktSuperBracket p q X Y = (-koszulSignZ p q) • ktSuperBracket q p Y X := by
  unfold ktSuperBracket
  exact assoc_superBracket_skew p q X Y

/-- Graded Jacobi identity for `ktSuperBracket` on `M₃(R)`. -/
theorem ktSuperBracket_jacobi (p q r : Bool) (X Y Z : Matrix (Fin 3) (Fin 3) R) :
    (koszulSignZ p r) • ktSuperBracket p (xor q r) X (ktSuperBracket q r Y Z) +
      (koszulSignZ q p) • ktSuperBracket q (xor r p) Y (ktSuperBracket r p Z X) +
      (koszulSignZ r q) • ktSuperBracket r (xor p q) Z (ktSuperBracket p q X Y) = 0 := by
  unfold ktSuperBracket
  exact assoc_superBracket_jacobi p q r X Y Z

/-- Graded Leibniz derivation identity for `ktSuperBracket` on `M₃(R)`. -/
theorem ktSuperBracket_derivation (p q r : Bool) (X Y Z : Matrix (Fin 3) (Fin 3) R) :
    ktSuperBracket p (xor q r) X (ktSuperBracket q r Y Z) =
      ktSuperBracket (xor p q) r (ktSuperBracket p q X Y) Z +
        (koszulSignZ p q) • ktSuperBracket q (xor p r) Y (ktSuperBracket p r X Z) := by
  unfold ktSuperBracket
  exact assoc_superBracket_derivation p q r X Y Z

/-- Matrix multiplication respects the `ℤ₂`-grading on `paritySubmodule`. -/
theorem mul_mem_paritySubmodule {p q : Bool} {X Y : Matrix (Fin 3) (Fin 3) R}
    (hX : X ∈ paritySubmodule R p) (hY : Y ∈ paritySubmodule R q) :
    X * Y ∈ paritySubmodule R (xor p q) := by
  intro i j hij
  by_contra hp
  have hsum : (X * Y) i j = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    have hterm : ∀ k : Fin 3, X i k * Y k j = 0 := by
      intro k
      by_cases hXk : X i k = 0
      · simp [hXk]
      · by_cases hYk : Y k j = 0
        · simp [hYk]
        · have hpx : SuperconformalOSpJordanPair.entryParity i k = p := hX i k hXk
          have hpy : SuperconformalOSpJordanPair.entryParity k j = q := hY k j hYk
          fin_cases i <;> fin_cases k <;> fin_cases j <;>
            simp [SuperconformalOSpJordanPair.entryParity] at hpx hpy hp <;>
            subst hpx hpy <;> simp at hp
    simp [hterm]
  exact hij hsum

/-- `ktSuperBracket` preserves the `ℤ₂`-grading on `paritySubmodule`. -/
theorem ktSuperBracket_mem_paritySubmodule {p q : Bool} {X Y : Matrix (Fin 3) (Fin 3) R}
    (hX : X ∈ paritySubmodule R p) (hY : Y ∈ paritySubmodule R q) :
    ktSuperBracket p q X Y ∈ paritySubmodule R (xor p q) := by
  have hXY : X * Y ∈ paritySubmodule R (xor p q) := mul_mem_paritySubmodule hX hY
  have hYX : Y * X ∈ paritySubmodule R (xor p q) := by
    rw [Bool.xor_comm]
    exact mul_mem_paritySubmodule hY hX
  cases p <;> cases q
  · exact (paritySubmodule R (xor false false)).sub_mem hXY hYX
  · exact (paritySubmodule R (xor false true)).sub_mem hXY hYX
  · exact (paritySubmodule R (xor true false)).sub_mem hXY hYX
  · exact (paritySubmodule R (xor true true)).add_mem hXY hYX

/-- Matrix multiplication is `ℤ`-grade-additive on `gradeSubmodule`. -/
theorem mul_mem_gradeSubmodule {k l : ℤ} {X Y : Matrix (Fin 3) (Fin 3) R}
    (hX : X ∈ gradeSubmodule R k) (hY : Y ∈ gradeSubmodule R l) :
    X * Y ∈ gradeSubmodule R (k + l) := by
  intro i j hij
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  have hterm : ∀ m : Fin 3, X i m * Y m j = 0 := by
    intro m
    by_cases him : matrixWeight i m = k
    · have hmj : matrixWeight m j ≠ l := by
        intro hl
        apply hij
        dsimp [matrixWeight] at him hl ⊢
        omega
      simp [hY m j hmj]
    · simp [hX i m him]
  simp [hterm]

/-- `ktSuperBracket` is `ℤ`-grade-additive on `gradeSubmodule`. -/
theorem ktSuperBracket_mem_gradeSubmodule {k l : ℤ} {X Y : Matrix (Fin 3) (Fin 3) R}
    (hX : X ∈ gradeSubmodule R k) (hY : Y ∈ gradeSubmodule R l) :
    ktSuperBracket (weightParity k) (weightParity l) X Y ∈ gradeSubmodule R (k + l) := by
  have hXY : X * Y ∈ gradeSubmodule R (k + l) := mul_mem_gradeSubmodule hX hY
  have hYX : Y * X ∈ gradeSubmodule R (k + l) := by
    rw [add_comm]
    exact mul_mem_gradeSubmodule hY hX
  cases hp : weightParity k <;> cases hq : weightParity l
  · exact (gradeSubmodule R (k + l)).sub_mem hXY hYX
  · exact (gradeSubmodule R (k + l)).sub_mem hXY hYX
  · exact (gradeSubmodule R (k + l)).sub_mem hXY hYX
  · exact (gradeSubmodule R (k + l)).add_mem hXY hYX

/-- On every matrix in `gradeSubmodule R k`, the graded Cartan adjoint `ktAdH` acts by
multiplication by the quantum-number weight `k`. -/
theorem ktAdH_on_gradeSubmodule (k : ℤ) (p : Bool) {X : Matrix (Fin 3) (Fin 3) R}
    (hX : X ∈ gradeSubmodule R k) :
    ktAdH p X = k • X := by
  unfold ktAdH ktSuperBracket
  rw [superBracket_even_left]
  unfold InfoGeometry.Algebra.SupergradedBracket.commutator
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three, H, Matrix.diagonal_apply,
    Matrix.smul_apply, zsmul_eq_mul]
  by_cases hik : matrixWeight i j = k
  · subst hik
    fin_cases i <;> fin_cases j <;>
      simp [matrixWeight] <;> noncomm_ring
  · have h0 : X i j = 0 := hX i j hik
    revert h0
    fin_cases i <;> fin_cases j <;> intro h0 <;> (dsimp at h0; simp [h0])

/-- Beyond-boundary grade truncation: any bracket of grade `+2` and grade `+1` vanishes. -/
theorem gradeSubmodule_truncation_pos {X Y : Matrix (Fin 3) (Fin 3) R}
    (hX : X ∈ gradeSubmodule R 2) (hY : Y ∈ gradeSubmodule R 1) :
    ktSuperBracket false true X Y = 0 := by
  have hmem : ktSuperBracket (weightParity 2) (weightParity 1) X Y ∈
      gradeSubmodule R (2 + 1) := ktSuperBracket_mem_gradeSubmodule hX hY
  change ktSuperBracket false true X Y ∈ gradeSubmodule R 3 at hmem
  ext i j
  apply hmem i j
  fin_cases i <;> fin_cases j <;> simp [matrixWeight]

/-- Beyond-boundary grade truncation: any bracket of grade `-2` and grade `-1` vanishes. -/
theorem gradeSubmodule_truncation_neg {X Y : Matrix (Fin 3) (Fin 3) R}
    (hX : X ∈ gradeSubmodule R (-2)) (hY : Y ∈ gradeSubmodule R (-1)) :
    ktSuperBracket false true X Y = 0 := by
  have hmem : ktSuperBracket (weightParity (-2)) (weightParity (-1)) X Y ∈
      gradeSubmodule R (-2 + -1) := ktSuperBracket_mem_gradeSubmodule hX hY
  change ktSuperBracket false true X Y ∈ gradeSubmodule R (-3) at hmem
  ext i j
  apply hmem i j
  fin_cases i <;> fin_cases j <;> simp [matrixWeight]

/-- Conjugation by `J R` is a `ℤ₂`-graded Lie superalgebra automorphism on `M₃(R)`. -/
theorem J_superBracket_automorphism (p q : Bool) (X Y : Matrix (Fin 3) (Fin 3) R) :
    (J R) * ktSuperBracket p q X Y * (J R) =
      ktSuperBracket p q ((J R) * X * (J R)) ((J R) * Y * (J R)) := by
  cases p <;> cases q
  · exact J_lie_automorphism X Y
  · exact J_lie_automorphism X Y
  · exact J_lie_automorphism X Y
  · have hJ : (J R) * (J R) = 1 := J_involutive
    unfold ktSuperBracket
    rw [superBracket_odd_odd]
    dsimp [anticommutator]
    calc
      J R * (X * Y + Y * X) * J R
          = J R * (X * (J R * J R) * Y + Y * (J R * J R) * X) * J R := by
              rw [hJ, mul_one, mul_one]
      _ = (J R * X * J R) * (J R * Y * J R) + (J R * Y * J R) * (J R * X * J R) := by
              noncomm_ring

/-- The sheet swap `swap` reverses `ℤ`-grading weights (`gradeSubmodule R k ↦ gradeSubmodule R (-k)`). -/
theorem swap_gradeSubmodule (k : ℤ) {X : Matrix (Fin 3) (Fin 3) R}
    (hX : X ∈ gradeSubmodule R k) :
    swap X ∈ gradeSubmodule R (-k) := by
  intro i j hij
  rw [swap_apply]
  apply hX
  intro hEq
  apply hij
  dsimp [matrixWeight] at hEq ⊢
  omega

/-- The graded supertrace vanishes on every `ktSuperBracket` of `ℤ₂`-homogeneous matrices
over a commutative ring `R` (matching the super-Jacobi/invariant pairing property). -/
theorem supertrace_ktSuperBracket_zero {R : Type*} [CommRing R] (p q : Bool)
    {X Y : Matrix (Fin 3) (Fin 3) R}
    (hX : X ∈ paritySubmodule R p) (hY : Y ∈ paritySubmodule R q) :
    supertrace (ktSuperBracket p q X Y) = 0 := by
  have hodd01 : ∀ {Z : Matrix (Fin 3) (Fin 3) R},
      Z ∈ paritySubmodule R false → Z 0 1 = 0 ∧ Z 1 0 = 0 ∧ Z 1 2 = 0 ∧ Z 2 1 = 0 := by
    intro Z hZ
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h; exact absurd (hZ 0 1 h) (by simp [SuperconformalOSpJordanPair.entryParity])
    · by_contra h; exact absurd (hZ 1 0 h) (by simp [SuperconformalOSpJordanPair.entryParity])
    · by_contra h; exact absurd (hZ 1 2 h) (by simp [SuperconformalOSpJordanPair.entryParity])
    · by_contra h; exact absurd (hZ 2 1 h) (by simp [SuperconformalOSpJordanPair.entryParity])
  have heven_diag : ∀ {Z : Matrix (Fin 3) (Fin 3) R},
      Z ∈ paritySubmodule R true →
        Z 0 0 = 0 ∧ Z 1 1 = 0 ∧ Z 2 2 = 0 ∧ Z 0 2 = 0 ∧ Z 2 0 = 0 := by
    intro Z hZ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · by_contra h; exact absurd (hZ 0 0 h) (by simp [SuperconformalOSpJordanPair.entryParity])
    · by_contra h; exact absurd (hZ 1 1 h) (by simp [SuperconformalOSpJordanPair.entryParity])
    · by_contra h; exact absurd (hZ 2 2 h) (by simp [SuperconformalOSpJordanPair.entryParity])
    · by_contra h; exact absurd (hZ 0 2 h) (by simp [SuperconformalOSpJordanPair.entryParity])
    · by_contra h; exact absurd (hZ 2 0 h) (by simp [SuperconformalOSpJordanPair.entryParity])
  cases p <;> cases q
  · obtain ⟨hx01, hx10, hx12, hx21⟩ := hodd01 hX
    obtain ⟨hy01, hy10, hy12, hy21⟩ := hodd01 hY
    dsimp [supertrace, ktSuperBracket, superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator]
    simp only [Matrix.mul_apply, Fin.sum_univ_three,
      hx01, hx10, hx12, hx21, hy01, hy10, hy12, hy21]
    simp only [mul_zero, add_zero, zero_add]
    rw [mul_comm (X 0 0) (Y 0 0), mul_comm (X 0 2) (Y 2 0), mul_comm (X 2 0) (Y 0 2),
      mul_comm (X 1 1) (Y 1 1), mul_comm (X 2 2) (Y 2 2)]
    abel
  · have hmem : ktSuperBracket false true X Y ∈ paritySubmodule R true := by
      simpa using ktSuperBracket_mem_paritySubmodule hX hY
    obtain ⟨h00, h11, h22, _, _⟩ := heven_diag hmem
    dsimp [supertrace]
    rw [h00, h11, h22]
    abel
  · have hmem : ktSuperBracket true false X Y ∈ paritySubmodule R true := by
      simpa using ktSuperBracket_mem_paritySubmodule hX hY
    obtain ⟨h00, h11, h22, _, _⟩ := heven_diag hmem
    dsimp [supertrace]
    rw [h00, h11, h22]
    abel
  · obtain ⟨hx00, hx11, hx22, hx02, hx20⟩ := heven_diag hX
    obtain ⟨hy00, hy11, hy22, hy02, hy20⟩ := heven_diag hY
    dsimp [supertrace, ktSuperBracket, superBracket, anticommutator]
    simp only [Matrix.mul_apply, Fin.sum_univ_three,
      hx00, hx11, hx22, hx02, hx20, hy00, hy11, hy22, hy02, hy20]
    simp only [mul_zero, add_zero, zero_add]
    rw [mul_comm (X 0 1) (Y 1 0), mul_comm (X 1 0) (Y 0 1), mul_comm (X 1 2) (Y 2 1),
      mul_comm (X 2 1) (Y 1 2)]
    abel

/-- **Graded vs Ungraded Commutator Obstruction Defect**:
the difference between the genuine odd-odd superbracket `{X, Y}` and the ungraded
commutator `bracket X Y = [X, Y]` is `2 • (Y * X)`. -/
theorem ktSuperBracket_odd_odd_sub_bracket (X Y : Matrix (Fin 3) (Fin 3) R) :
    ktSuperBracket true true X Y - bracket X Y = 2 • (Y * X) := by
  unfold ktSuperBracket bracket
  rw [superBracket_odd_odd, anticommutator]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul,
    Nat.cast_ofNat]
  noncomm_ring

/-- Exact failure of the ungraded commutator on `(Q_plus, Q_minus)`: its supertrace is `4`
rather than `0`, whereas the graded superbracket yields `H R` with vanishing supertrace. -/
theorem ungraded_Qplus_Qminus_supertrace_defect :
    supertrace (bracket (SuperconformalOSpJordanPair.Q_plus R)
      (SuperconformalOSpJordanPair.Q_minus R)) = (4 : R) ∧
    supertrace (ktSuperBracket true true (SuperconformalOSpJordanPair.Q_plus R)
      (SuperconformalOSpJordanPair.Q_minus R)) = 0 := by
  constructor
  · unfold bracket supertrace SuperconformalOSpJordanPair.Q_plus
      SuperconformalOSpJordanPair.Q_minus SuperconformalOSpJordanPair.E
    simp [Matrix.mul_apply]
    norm_num
  · have hq : ktSuperBracket true true (SuperconformalOSpJordanPair.Q_plus R)
        (SuperconformalOSpJordanPair.Q_minus R) = H R := by
      unfold ktSuperBracket SuperconformalOSpJordanPair.Q_plus
        SuperconformalOSpJordanPair.Q_minus H SuperconformalOSpJordanPair.E
      rw [superBracket_odd_odd, anticommutator]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
    rw [hq, supertrace_H]

/-- Canonical Kantor–Tanaka generators match the `SuperconformalOSpJordanPair` generators. -/
theorem kt_generators_match_osp :
    H R = SuperconformalOSpJordanPair.H_gen R ∧
    (E 0 2 : Matrix (Fin 3) (Fin 3) R) = SuperconformalOSpJordanPair.E_gen R ∧
    (E 2 0 : Matrix (Fin 3) (Fin 3) R) = SuperconformalOSpJordanPair.F_gen R ∧
    (E 0 1 + E 1 2 : Matrix (Fin 3) (Fin 3) R) = SuperconformalOSpJordanPair.Q_plus R ∧
    (E 1 0 - E 2 1 : Matrix (Fin 3) (Fin 3) R) = SuperconformalOSpJordanPair.Q_minus R := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [H, SuperconformalOSpJordanPair.H_gen, SuperconformalOSpJordanPair.E]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [E, SuperconformalOSpJordanPair.E_gen, SuperconformalOSpJordanPair.E]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [E, SuperconformalOSpJordanPair.F_gen, SuperconformalOSpJordanPair.E]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [E, SuperconformalOSpJordanPair.Q_plus, SuperconformalOSpJordanPair.E]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [E, SuperconformalOSpJordanPair.Q_minus, SuperconformalOSpJordanPair.E]

/-- `KantorTanakaSuperGrassmannian.supertrace` coincides with `SuperconformalOSpJordanPair.supertrace`. -/
theorem kt_supertrace_eq_osp (X : Matrix (Fin 3) (Fin 3) R) :
    supertrace X = SuperconformalOSpJordanPair.supertrace X := by
  dsimp [supertrace, SuperconformalOSpJordanPair.supertrace]

/-- Odd-odd anticommutation relations of the elementary odd generators `E 0 1, E 1 2, E 1 0, E 2 1`,
reconstructing `E 0 2` and `H R` with the genuine `ℤ₂`-graded superbracket. -/
theorem kt_odd_odd_anticomm_relations :
    ktSuperBracket true true (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 2) = E 0 2 ∧
    ktSuperBracket true true (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 0) = E 0 0 + E 1 1 ∧
    ktSuperBracket true true (E 1 2 : Matrix (Fin 3) (Fin 3) R) (E 2 1) = E 1 1 + E 2 2 ∧
    ktSuperBracket true true (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 0) -
      ktSuperBracket true true (E 1 2) (E 2 1) = H R := by
  unfold ktSuperBracket
  simp only [superBracket_odd_odd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold anticommutator; ext i j; fin_cases i <;> fin_cases j <;> simp [E, Matrix.mul_apply]
  · unfold anticommutator; ext i j; fin_cases i <;> fin_cases j <;> simp [E, Matrix.mul_apply]
  · unfold anticommutator; ext i j; fin_cases i <;> fin_cases j <;> simp [E, Matrix.mul_apply]
  · unfold anticommutator; ext i j; fin_cases i <;> fin_cases j <;> simp [E, H, Matrix.mul_apply]

/-- Exact closure of the odd `±1` supercharges `Q_plus, Q_minus` into the emergent even `0, ±2`
bosonic `osp(1|2)` sector `(H, E 0 2, E 2 0)` and exact `ktAdH` quantum-number eigenvalues. -/
theorem kt_osp_superBracket_closure_match :
    ktSuperBracket true true (SuperconformalOSpJordanPair.Q_plus R)
      (SuperconformalOSpJordanPair.Q_plus R) =
        (2 : ℤ) • (E 0 2 : Matrix (Fin 3) (Fin 3) R) ∧
    ktSuperBracket true true (SuperconformalOSpJordanPair.Q_minus R)
      (SuperconformalOSpJordanPair.Q_minus R) =
        (-2 : ℤ) • (E 2 0 : Matrix (Fin 3) (Fin 3) R) ∧
    ktSuperBracket true true (SuperconformalOSpJordanPair.Q_plus R)
      (SuperconformalOSpJordanPair.Q_minus R) = H R ∧
    ktAdH true (SuperconformalOSpJordanPair.Q_plus R) = SuperconformalOSpJordanPair.Q_plus R ∧
    ktAdH true (SuperconformalOSpJordanPair.Q_minus R) = -SuperconformalOSpJordanPair.Q_minus R ∧
    ktAdH false (E 0 2 : Matrix (Fin 3) (Fin 3) R) =
      (2 : ℤ) • (E 0 2 : Matrix (Fin 3) (Fin 3) R) ∧
    ktAdH false (E 2 0 : Matrix (Fin 3) (Fin 3) R) =
      (-2 : ℤ) • (E 2 0 : Matrix (Fin 3) (Fin 3) R) := by
  have hQplus_mem : SuperconformalOSpJordanPair.Q_plus R ∈ gradeSubmodule R 1 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [SuperconformalOSpJordanPair.Q_plus, SuperconformalOSpJordanPair.E,
        matrixWeight] at hij ⊢
  have hQminus_mem : SuperconformalOSpJordanPair.Q_minus R ∈ gradeSubmodule R (-1) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [SuperconformalOSpJordanPair.Q_minus, SuperconformalOSpJordanPair.E,
        matrixWeight] at hij ⊢
  have hE02_mem : (E 0 2 : Matrix (Fin 3) (Fin 3) R) ∈ gradeSubmodule R 2 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [E, matrixWeight] at hij ⊢
  have hE20_mem : (E 2 0 : Matrix (Fin 3) (Fin 3) R) ∈ gradeSubmodule R (-2) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [E, matrixWeight] at hij ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ktSuperBracket SuperconformalOSpJordanPair.Q_plus SuperconformalOSpJordanPair.E E
    rw [superBracket_odd_odd]
    dsimp [anticommutator]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, zsmul_eq_mul]
    norm_num
  · unfold ktSuperBracket SuperconformalOSpJordanPair.Q_minus SuperconformalOSpJordanPair.E E
    rw [superBracket_odd_odd]
    dsimp [anticommutator]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, zsmul_eq_mul]
    norm_num
  · unfold ktSuperBracket SuperconformalOSpJordanPair.Q_plus
      SuperconformalOSpJordanPair.Q_minus H SuperconformalOSpJordanPair.E
    rw [superBracket_odd_odd]
    dsimp [anticommutator]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · simpa using ktAdH_on_gradeSubmodule 1 true hQplus_mem
  · simpa using ktAdH_on_gradeSubmodule (-1) true hQminus_mem
  · exact ktAdH_on_gradeSubmodule 2 false hE02_mem
  · exact ktAdH_on_gradeSubmodule (-2) false hE20_mem

/-- Realization of `SuperconformalOSpJordanPair.jordanPairPlus` and `jordanPairMinus` directly
on the Kantor–Tanaka contact vectors `E 0 1 + E 1 2` and `E 1 0 - E 2 1`. -/
theorem kt_jordan_pair_match {R : Type*} [CommRing R] (a b c : R) :
    SuperconformalOSpJordanPair.jordanPairPlus
        (a • (E 0 1 + E 1 2 : Matrix (Fin 3) (Fin 3) R))
        (b • (E 1 0 - E 2 1 : Matrix (Fin 3) (Fin 3) R))
        (c • (E 0 1 + E 1 2 : Matrix (Fin 3) (Fin 3) R)) =
      (a * b * c) • (E 0 1 + E 1 2 : Matrix (Fin 3) (Fin 3) R) ∧
    SuperconformalOSpJordanPair.jordanPairMinus
        (a • (E 1 0 - E 2 1 : Matrix (Fin 3) (Fin 3) R))
        (b • (E 0 1 + E 1 2 : Matrix (Fin 3) (Fin 3) R))
        (c • (E 1 0 - E 2 1 : Matrix (Fin 3) (Fin 3) R)) =
      (a * b * c) • (E 1 0 - E 2 1 : Matrix (Fin 3) (Fin 3) R) := by
  have ⟨_, _, _, hQp, hQm⟩ := kt_generators_match_osp (R := R)
  rw [hQp, hQm]
  simpa [SuperconformalOSpJordanPair.contactTriplePlus,
    SuperconformalOSpJordanPair.contactTripleMinus] using
    (SuperconformalOSpJordanPair.contact_jordan_pair_matrix_realization a b c)

/-- The `MatrixSpans.evenSpan` and `MatrixSpans.oddSpan` of `SuperconformalOSpJordanPair`
embed into `paritySubmodule R false` and `paritySubmodule R true` respectively. -/
theorem kt_osp_spans_le_paritySubmodule :
    SuperconformalOSpJordanPair.MatrixSpans.evenSpan (R := R) ≤ paritySubmodule R false ∧
    SuperconformalOSpJordanPair.MatrixSpans.oddSpan (R := R) ≤ paritySubmodule R true := by
  constructor
  · apply Submodule.span_le.2
    rintro X ⟨idx, rfl⟩
    cases idx
    · exact SuperconformalOSpJordanPair.H_gen_even
    · exact SuperconformalOSpJordanPair.E_gen_even
    · exact SuperconformalOSpJordanPair.F_gen_even
  · apply Submodule.span_le.2
    rintro X ⟨idx, rfl⟩
    cases idx
    · exact SuperconformalOSpJordanPair.Q_plus_odd
    · exact SuperconformalOSpJordanPair.Q_minus_odd

end GradedSuperbracket

end InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
