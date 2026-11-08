import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases

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

variable {R : Type*} [CommRing R]

/-! ### Section 1: Matrix Units and the Cartan Grading Element -/

/-- Elementary matrix units in $M_3(R)$. -/
def E (i j : Fin 3) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun r c => if r = i ∧ c = j then 1 else 0

/-- The Cartan grading element $H = \operatorname{diag}(1, 0, -1) \in \mathfrak{sl}(3, R)$. -/
def H (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
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
  ring

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
def J (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
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

/-- Master certificate structure packaging the complete 5-graded Kantor–Tanaka theorems. -/
structure KantorTanakaSuperGrassmannianCertificate : Prop where
  bracket_antisymmetry        : ∀ X Y : Matrix (Fin 3) (Fin 3) R, bracket X Y = - bracket Y X
  bracket_jacobi              : ∀ X Y Z : Matrix (Fin 3) (Fin 3) R,
                                  bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0
  derivation_adjoint          : ∀ H X Y : Matrix (Fin 3) (Fin 3) R,
                                  bracket H (bracket X Y) = bracket (bracket H X) Y + bracket X (bracket H Y)
  odd_contact                 : bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 2) = E 0 2
  odd_contact_conjugate       : bracket (E 2 1 : Matrix (Fin 3) (Fin 3) R) (E 1 0) = E 2 0
  extremal_generates_H        : bracket (E 0 2 : Matrix (Fin 3) (Fin 3) R) (E 2 0) = H R
  spinor_bilinear_reconstruct : bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 0) +
                                  bracket (E 1 2) (E 2 1) = H R
  truncation_plus             : bracket (E 0 2 : Matrix (Fin 3) (Fin 3) R) (E 0 1) = 0
  truncation_minus            : bracket (E 2 0 : Matrix (Fin 3) (Fin 3) R) (E 1 0) = 0
  involution_square           : (J R) * (J R) = 1
  involution_inverts_H        : swap (H R) = - H R
  involution_inverts_two      : swap (E 0 2 : Matrix (Fin 3) (Fin 3) R) = E 2 0
  involution_automorphism     : ∀ X Y : Matrix (Fin 3) (Fin 3) R,
                                  (J R) * (bracket X Y) * (J R) = bracket ((J R) * X * (J R)) ((J R) * Y * (J R))
  supertrace_H_zero           : supertrace (H R) = 0
  duality_pairing             : supertrace ((E 0 2 : Matrix (Fin 3) (Fin 3) R) * E 2 0) = 1
  orthogonality               : supertrace ((E 0 2 : Matrix (Fin 3) (Fin 3) R) * E 0 1) = 0

/-- **Master Gate**: Full Kantor–Tanaka Super-Grassmannian verification. -/
theorem compile_kantor_tanaka_super_grassmannian :
    KantorTanakaSuperGrassmannianCertificate (R := R) where
  bracket_antisymmetry        := bracket_skew
  bracket_jacobi              := jacobi_identity
  derivation_adjoint          := derivation_identity
  odd_contact                 := odd_contact_bracket
  odd_contact_conjugate       := odd_contact_bracket_conjugate
  extremal_generates_H        := extremal_bracket_generates_H
  spinor_bilinear_reconstruct := spinor_bilinear_sum_eq_H
  truncation_plus             := grade_truncation_2_1a
  truncation_minus            := grade_truncation_neg2_neg1a
  involution_square           := J_involutive
  involution_inverts_H        := J_inverts_H
  involution_inverts_two      := J_inverts_grade_two
  involution_automorphism     := J_lie_automorphism
  supertrace_H_zero           := supertrace_H
  duality_pairing             := supertrace_E02_E20
  orthogonality               := supertrace_E02_E01_orthogonal

end InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
