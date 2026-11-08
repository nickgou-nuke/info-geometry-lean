import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Canonical.TKKJordanPairData

/-!
# Section 86: Superconformal 𝔬𝔰𝔭(1|2) & Kantor Jordan Pair Architecture

This module formalizes a concrete matrix relation model for the minimal
superconformal algebra in `M₃(R)`, using the `2|1` grading with even indices
`0,2` and odd index `1`. The polynomial matrix identities below hold over any
commutative ring. Their interpretation as the named Lie superalgebra
`𝔬𝔰𝔭(1|2)` is intended in characteristic different from two. This file does
not claim a classification theorem or a proved equivalence with a presented
Lie-superalgebra object. It also constructs the associated one-dimensional
Jordan pair and proves its matrix triple-product readouts:

### Key Architectural Results:
1. **Bosonic $\mathfrak{sl}(2)$ Subalgebra**:
   $$[H, E] = 2E, \quad [H, F] = -2F, \quad [E, F] = H$$
2. **Fermionic Anticommutation & Supercharge Closing**:
   $$\{Q_+, Q_+\} = 2E, \quad \{Q_-, Q_-\} = -2F, \quad \{Q_+, Q_-\} = H$$
3. **Super-Adjoint Ladder & Annihilation Actions**:
   $$[H, Q_+] = Q_+, \quad [H, Q_-] = -Q_-$$
   $$[E, Q_-] = -Q_+, \quad [F, Q_+] = -Q_-, \quad [E, Q_+] = 0, \quad [F, Q_-] = 0$$
4. **Kantor Jordan Pair Trilinear Product**:
   On the contact generators $(V^+, V^-) = (\mathbb{R} Q_+, \mathbb{R} Q_-)$:
   $$D^+(x, y) z := [\{x, y\}, z], \qquad D^-(y, x) w := - [\{x, y\}, w]$$
   with scalar contact products $(x,y,z)\mapsto xyz$ satisfying the Jordan-pair
   identities and explicit M₃ readouts on all parametrized scalar multiples
   of $Q_+$ and $Q_-$.
5. **Graded Supertrace & Vacuum Cancellation**:
   $$\operatorname{STr}(H) = 0, \qquad \operatorname{STr}(\{Q_+, Q_-\}) = 0$$

All proofs are native Mathlib 4 with no `sorry`, `admit`, or custom axioms.
Matrix theorems use the standard Mathlib matrix axiom footprint, including
`Classical.choice`; the scalar Jordan-pair identities report `[propext]`.
-/

namespace InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair

open scoped Matrix BigOperators

variable {R : Type*} [CommRing R]

/-! ### Section 1: Canonical Basis and Operators in M₃(R) -/

/-- Elementary matrix units in $M_3(R)$. -/
def E (i j : Fin 3) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun r c => if r = i ∧ c = j then 1 else 0

/-- The Cartan element $H = E_{00} - E_{22} = \operatorname{diag}(1, 0, -1)$. -/
def H_gen (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  E 0 0 - E 2 2

/-- The positive nilpotent generator $E = E_{02}$. -/
def E_gen (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  E 0 2

/-- The negative nilpotent generator $F = E_{20}$. -/
def F_gen (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  E 2 0

/-- The odd positive supercharge $Q_+ = E_{01} + E_{12}$. -/
def Q_plus (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  E 0 1 + E 1 2

/-- The odd negative supercharge $Q_- = E_{10} - E_{21}$. -/
def Q_minus (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  E 1 0 - E 2 1

/-! ### The explicit `2|1` grading used by these matrices

The odd coordinate is index `1`; indices `0` and `2` are even.  This
nonstandard ordering is why the supertrace below has signs `+ - +`.
-/

/-- Parity of a matrix entry for the `2|1` grading `(0,2 | 1)`. -/
def entryParity (i j : Fin 3) : Bool :=
  if (i = 1 ∧ j ≠ 1) ∨ (i ≠ 1 ∧ j = 1) then true else false

/-- A matrix is homogeneous when every nonzero entry has the specified parity. -/
def IsHomogeneous (p : Bool) (X : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∀ i j, X i j ≠ 0 → entryParity i j = p

theorem H_gen_even : IsHomogeneous false (H_gen R) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [H_gen, E, entryParity] at hij ⊢

theorem E_gen_even : IsHomogeneous false (E_gen R) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [E_gen, E, entryParity] at hij ⊢

theorem F_gen_even : IsHomogeneous false (F_gen R) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [F_gen, E, entryParity] at hij ⊢

theorem Q_plus_odd : IsHomogeneous true (Q_plus R) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [Q_plus, E, entryParity] at hij ⊢

theorem Q_minus_odd : IsHomogeneous true (Q_minus R) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [Q_minus, E, entryParity] at hij ⊢

/-- The matrix Lie bracket (commutator): $[A, B] = AB - BA$. -/
def commutator (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  A * B - B * A

/-- The matrix anticommutator: $\{A, B\} = AB + BA$. -/
def anticommutator (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  A * B + B * A

/-- Symmetry of the anticommutator: $\{A, B\} = \{B, A\}$. -/
theorem anticomm_symm (A B : Matrix (Fin 3) (Fin 3) R) :
    anticommutator A B = anticommutator B A := by
  unfold anticommutator
  ext i j
  simp only [Matrix.add_apply]
  ring

/-! ### Section 2: Bosonic sl(2) Subalgebra Identities -/

/-- **Theorem**: $[H, E] = 2E$. -/
theorem osp_sl2_H_E : commutator (H_gen R) (E_gen R) = 2 • (E_gen R) := by
  unfold commutator H_gen E_gen E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply]; ring

/-- **Theorem**: $[H, F] = -2F$. -/
theorem osp_sl2_H_F : commutator (H_gen R) (F_gen R) = -2 • (F_gen R) := by
  unfold commutator H_gen F_gen E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply]; ring

/-- **Theorem**: $[E, F] = H$. -/
theorem osp_sl2_E_F : commutator (E_gen R) (F_gen R) = H_gen R := by
  unfold commutator H_gen E_gen F_gen E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-! ### Section 3: Fermionic Anticommutation & Supercharge Closing -/

/-- **Theorem**: $\{Q_+, Q_+\} = 2E$. -/
theorem osp_anticomm_plus_plus : anticommutator (Q_plus R) (Q_plus R) = 2 • (E_gen R) := by
  unfold anticommutator Q_plus E_gen E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply]; ring

/-- **Theorem**: $\{Q_-, Q_-\} = -2F$. -/
theorem osp_anticomm_minus_minus : anticommutator (Q_minus R) (Q_minus R) = -2 • (F_gen R) := by
  unfold anticommutator Q_minus F_gen E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply]; ring

/-- **Theorem**: $\{Q_+, Q_-\} = H$. -/
theorem osp_anticomm_plus_minus : anticommutator (Q_plus R) (Q_minus R) = H_gen R := by
  unfold anticommutator Q_plus Q_minus H_gen E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply]

/-- **Theorem**: Reverse order closure: $\{Q_-, Q_+\} = H$. -/
theorem osp_anticomm_minus_plus : anticommutator (Q_minus R) (Q_plus R) = H_gen R := by
  rw [anticomm_symm, osp_anticomm_plus_minus]

/-! ### Section 4: Super-Adjoint Grading and Ladder Actions -/

/-- **Theorem**: Grade $+1$ eigenaction: $[H, Q_+] = Q_+$. -/
theorem osp_grad_H_Q_plus : commutator (H_gen R) (Q_plus R) = Q_plus R := by
  unfold commutator H_gen Q_plus E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply]

/-- **Theorem**: Grade $-1$ eigenaction: $[H, Q_-] = -Q_-$. -/
theorem osp_grad_H_Q_minus : commutator (H_gen R) (Q_minus R) = -Q_minus R := by
  unfold commutator H_gen Q_minus E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply]

/-- **Theorem**: Lowering supercharge ladder: $[E, Q_-] = -Q_+$. -/
theorem osp_ladder_E_Q_minus : commutator (E_gen R) (Q_minus R) = -Q_plus R := by
  unfold commutator E_gen Q_minus Q_plus E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply]

/-- **Theorem**: Raising supercharge ladder: $[F, Q_+] = -Q_-$. -/
theorem osp_ladder_F_Q_plus : commutator (F_gen R) (Q_plus R) = -Q_minus R := by
  unfold commutator F_gen Q_plus Q_minus E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply]

/-- **Theorem**: Highest weight annihilation: $[E, Q_+] = 0$. -/
theorem osp_annihilate_E_Q_plus : commutator (E_gen R) (Q_plus R) = 0 := by
  unfold commutator E_gen Q_plus E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- **Theorem**: Lowest weight annihilation: $[F, Q_-] = 0$. -/
theorem osp_annihilate_F_Q_minus : commutator (F_gen R) (Q_minus R) = 0 := by
  unfold commutator F_gen Q_minus E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-! ### Section 4a: The relations in the canonical parity-aware bracket

These readouts connect the concrete structure constants to the repository's
shared superbracket definition. The parity witnesses above ensure the chosen
arguments have the indicated homogeneous degrees.
-/

theorem superBracket_H_E :
    InfoGeometry.Algebra.SupergradedBracket.superBracket false false
      (H_gen R) (E_gen R) = 2 • E_gen R := by
  change commutator (H_gen R) (E_gen R) = 2 • E_gen R
  exact osp_sl2_H_E

theorem superBracket_Qplus_Qplus :
    InfoGeometry.Algebra.SupergradedBracket.superBracket true true
      (Q_plus R) (Q_plus R) = 2 • E_gen R := by
  change anticommutator (Q_plus R) (Q_plus R) = 2 • E_gen R
  exact osp_anticomm_plus_plus

theorem superBracket_Qminus_Qminus :
    InfoGeometry.Algebra.SupergradedBracket.superBracket true true
      (Q_minus R) (Q_minus R) = -2 • F_gen R := by
  change anticommutator (Q_minus R) (Q_minus R) = -2 • F_gen R
  exact osp_anticomm_minus_minus

theorem superBracket_Qplus_Qminus :
    InfoGeometry.Algebra.SupergradedBracket.superBracket true true
      (Q_plus R) (Q_minus R) = H_gen R := by
  change anticommutator (Q_plus R) (Q_minus R) = H_gen R
  exact osp_anticomm_plus_minus

/-! ### Section 5: The Kantor Jordan Pair & Trilinear Products -/

/-- The positive Jordan pair trilinear action: $D^+(x, y) z = [\{x, y\}, z]$. -/
def jordanPairPlus (x y z : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  InfoGeometry.Algebra.SupergradedBracket.superBracket false true
    (InfoGeometry.Algebra.SupergradedBracket.superBracket true true x y) z

/-- The negative Jordan pair trilinear action: $D^-(y, x) w = - [\{x, y\}, w]$. -/
def jordanPairMinus (y x w : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  - InfoGeometry.Algebra.SupergradedBracket.superBracket false true
    (InfoGeometry.Algebra.SupergradedBracket.superBracket true true x y) w

/-! ### Section 5a: The contact coordinates form a genuine Jordan pair

The generators `Q_plus` and `Q_minus` span one-dimensional positive and
negative spaces. Their scalar coordinates carry the Jordan pair product
`(x,y,z) ↦ xyz`. We prove both fundamental identities on these complete
coordinate spaces and identify their matrix realization by nested
superbrackets. The three-colour `R^3` Jordan pair in
`Canonical.ThreeColorChiralJordanPair` is a distinct, higher-dimensional
object; no identification with it is asserted here.
-/

/-- The positive scalar triple product for the two contact lines. -/
def contactTriplePlus (x y z : R) : R := x * y * z

/-- The negative scalar triple product for the two contact lines. -/
def contactTripleMinus (y x w : R) : R := y * x * w

theorem contactTriplePlus_outer (x y z : R) :
    contactTriplePlus x y z = contactTriplePlus z y x := by
  dsimp [contactTriplePlus]
  ring

theorem contactTripleMinus_outer (x y z : R) :
    contactTripleMinus x y z = contactTripleMinus z y x := by
  dsimp [contactTripleMinus]
  ring

theorem contactTriplePlus_fundamental (x u w y v : R) :
    contactTriplePlus x y (contactTriplePlus u v w) -
        contactTriplePlus u v (contactTriplePlus x y w) =
      contactTriplePlus (contactTriplePlus x y u) v w -
        contactTriplePlus u (contactTripleMinus y x v) w := by
  simp [contactTriplePlus, contactTripleMinus]
  ring

theorem contactTripleMinus_fundamental (x u w y v : R) :
    contactTripleMinus x y (contactTripleMinus u v w) -
        contactTripleMinus u v (contactTripleMinus x y w) =
      contactTripleMinus (contactTripleMinus x y u) v w -
        contactTripleMinus u (contactTriplePlus y x v) w := by
  simp [contactTriplePlus, contactTripleMinus]
  ring

/-- The two one-dimensional contact spaces, with their Jordan pair products. -/
def contactJordanPair : TKKJordanPairData.JordanPair R where
  Vplus := R
  Vminus := R
  triplePlus := contactTriplePlus
  tripleMinus := contactTripleMinus
  triplePlus_outer := contactTriplePlus_outer
  tripleMinus_outer := contactTripleMinus_outer
  triplePlus_fundamental := contactTriplePlus_fundamental
  tripleMinus_fundamental := contactTripleMinus_fundamental

/-- The positive matrix triple is the scalar Jordan pair triple on `Q_plus`. -/
theorem jordan_pair_plus_scalar_readout (a b c : R) :
    jordanPairPlus (a • Q_plus R) (b • Q_minus R) (c • Q_plus R) =
      (contactTriplePlus a b c) • Q_plus R := by
  unfold jordanPairPlus contactTriplePlus
    InfoGeometry.Algebra.SupergradedBracket.superBracket
    InfoGeometry.Algebra.SupergradedBracket.anticommutator
    InfoGeometry.Algebra.SupergradedBracket.commutator
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.mul_apply, Q_plus, Q_minus, E] <;> ring

/-- The negative matrix triple is the dual scalar Jordan pair triple on `Q_minus`. -/
theorem jordan_pair_minus_scalar_readout (a b c : R) :
    jordanPairMinus (a • Q_minus R) (b • Q_plus R) (c • Q_minus R) =
      (contactTripleMinus a b c) • Q_minus R := by
  unfold jordanPairMinus contactTripleMinus
    InfoGeometry.Algebra.SupergradedBracket.superBracket
    InfoGeometry.Algebra.SupergradedBracket.anticommutator
    InfoGeometry.Algebra.SupergradedBracket.commutator
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.mul_apply, Q_plus, Q_minus, E] <;> ring

/-- **Theorem**: Fundamental Jordan pair evaluation on $V^+$:
    $D^+(Q_+, Q_-) Q_+ = Q_+$. -/
theorem jordan_pair_plus_eval :
    jordanPairPlus (Q_plus R) (Q_minus R) (Q_plus R) = Q_plus R := by
  change commutator (anticommutator (Q_plus R) (Q_minus R)) (Q_plus R) = Q_plus R
  rw [osp_anticomm_plus_minus, osp_grad_H_Q_plus]

/-- **Theorem**: Fundamental Jordan pair evaluation on $V^-$:
    $D^-(Q_-, Q_+) Q_- = Q_-$. -/
theorem jordan_pair_minus_eval :
    jordanPairMinus (Q_minus R) (Q_plus R) (Q_minus R) = Q_minus R := by
  change -commutator (anticommutator (Q_plus R) (Q_minus R)) (Q_minus R) = Q_minus R
  rw [osp_anticomm_plus_minus, osp_grad_H_Q_minus, neg_neg]

/-! ### Section 6: Graded Supertrace and Invariant Cancellation -/

/-- The canonical graded supertrace on $M_3(R)$: $\operatorname{STr}(X) = X_{00} - X_{11} + X_{22}$. -/
def supertrace (X : Matrix (Fin 3) (Fin 3) R) : R :=
  X 0 0 - X 1 1 + X 2 2

/-- **Theorem**: The supertrace of the Cartan generator vanishes: $\operatorname{STr}(H) = 0$. -/
theorem supertrace_H :
    supertrace (H_gen R) = 0 := by
  dsimp [supertrace, H_gen, E]
  simp

/-- **Theorem**: Vanishing supertrace of the odd anticommutator: $\operatorname{STr}(\{Q_+, Q_-\}) = 0$. -/
theorem supertrace_anticomm_plus_minus :
    supertrace (anticommutator (Q_plus R) (Q_minus R)) = 0 := by
  rw [osp_anticomm_plus_minus, supertrace_H]

/-- **Theorem**: Vanishing supertrace of raising supercharge squared: $\operatorname{STr}(Q_+^2) = 0$. -/
theorem supertrace_Q_plus_sq :
    supertrace ((Q_plus R) * (Q_plus R)) = 0 := by
  dsimp [supertrace, Q_plus, E]
  simp [Matrix.mul_apply]

/-- **Theorem**: Vanishing supertrace of lowering supercharge squared: $\operatorname{STr}(Q_-^2) = 0$. -/
theorem supertrace_Q_minus_sq :
    supertrace ((Q_minus R) * (Q_minus R)) = 0 := by
  dsimp [supertrace, Q_minus, E]
  simp [Matrix.mul_apply]

/-! ### Section 7: The matrix realization of the scalar contact Jordan pair -/

/--
The two scalar Jordan-pair triple products are realized on the corresponding
matrix contact lines by nested parity-aware superbrackets. This identifies
the full one-dimensional pair operations with their concrete M₃ readouts;
it is stronger than evaluating only the three generators.
-/
theorem contact_jordan_pair_matrix_realization (a b c : R) :
    jordanPairPlus (a • Q_plus R) (b • Q_minus R) (c • Q_plus R) =
      (contactTriplePlus a b c) • Q_plus R ∧
    jordanPairMinus (a • Q_minus R) (b • Q_plus R) (c • Q_minus R) =
      (contactTripleMinus a b c) • Q_minus R := by
  exact ⟨jordan_pair_plus_scalar_readout a b c,
    jordan_pair_minus_scalar_readout a b c⟩

/-! ### Section 8: The concrete graded matrix spans are bracket-closed

The five displayed generators span an actual graded subspace of `M₃(R)`.
The following finite structure-constant tables are evaluated from the matrix
definitions, then bilinearity lifts their closure to every element of the two
spans. This proves a concrete graded subalgebra statement, without claiming a
classification or an equivalence to an abstractly presented `osp(1|2)`.
-/

namespace MatrixSpans

abbrev M (R : Type*) [CommRing R] := Matrix (Fin 3) (Fin 3) R

inductive EvenIndex where
  | h | e | f
  deriving DecidableEq

inductive OddIndex where
  | plus | minus
  deriving DecidableEq

def evenBasis : EvenIndex → M R
  | .h => H_gen R
  | .e => E_gen R
  | .f => F_gen R

def oddBasis : OddIndex → M R
  | .plus => Q_plus R
  | .minus => Q_minus R

def evenGenerators : Set (M R) := Set.range evenBasis
def oddGenerators : Set (M R) := Set.range oddBasis

/-- Span of the three even generators `H`, `E`, and `F`. -/
def evenSpan : Submodule R (M R) := Submodule.span R evenGenerators

/-- Span of the two odd supercharges `Q₊` and `Q₋`. -/
def oddSpan : Submodule R (M R) := Submodule.span R oddGenerators

@[simp] theorem even_H_mem : H_gen R ∈ evenSpan :=
  Submodule.subset_span ⟨.h, rfl⟩
@[simp] theorem even_E_mem : E_gen R ∈ evenSpan :=
  Submodule.subset_span ⟨.e, rfl⟩
@[simp] theorem even_F_mem : F_gen R ∈ evenSpan :=
  Submodule.subset_span ⟨.f, rfl⟩
@[simp] theorem odd_Qplus_mem : Q_plus R ∈ oddSpan :=
  Submodule.subset_span ⟨.plus, rfl⟩
@[simp] theorem odd_Qminus_mem : Q_minus R ∈ oddSpan :=
  Submodule.subset_span ⟨.minus, rfl⟩

abbrev sb (p q : Bool) (x y : M R) :=
  InfoGeometry.Algebra.SupergradedBracket.superBracket p q x y

theorem sb_add_left (p q : Bool) (x y z : M R) :
    sb p q (x + y) z = sb p q x z + sb p q y z := by
  cases p <;> cases q <;>
    ext i j <;>
    simp [sb, InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem sb_add_right (p q : Bool) (x y z : M R) :
    sb p q x (y + z) = sb p q x y + sb p q x z := by
  cases p <;> cases q <;>
    ext i j <;>
    simp [sb, InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem sb_smul_left (p q : Bool) (a : R) (x y : M R) :
    sb p q (a • x) y = a • sb p q x y := by
  cases p <;> cases q <;>
    ext i j <;>
    simp [sb, InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem sb_smul_right (p q : Bool) (a : R) (x y : M R) :
    sb p q x (a • y) = a • sb p q x y := by
  cases p <;> cases q <;>
    ext i j <;>
    simp [sb, InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem sb_zero_left (p q : Bool) (y : M R) : sb p q 0 y = 0 := by
  cases p <;> cases q <;>
    simp [sb, InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator]

theorem sb_zero_right (p q : Bool) (x : M R) : sb p q x 0 = 0 := by
  cases p <;> cases q <;>
    simp [sb, InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator]

/-- Bilinearity lifts generator-pair closure to the linear spans. -/
theorem span_pair_closure {s t : Set (M R)} (U : Submodule R (M R))
    (p q : Bool)
    (hgen : ∀ x, x ∈ s → ∀ y, y ∈ t → sb p q x y ∈ U)
    {x y : M R} (hx : x ∈ Submodule.span R s)
    (hy : y ∈ Submodule.span R t) : sb p q x y ∈ U := by
  refine Submodule.span_induction₂
    (p := fun x y _ _ => sb p q x y ∈ U)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x y hx hy
    exact hgen x hx y hy
  · intro y hy
    rw [sb_zero_left]
    exact U.zero_mem
  · intro x hx
    rw [sb_zero_right]
    exact U.zero_mem
  · intro x z y hx hz hy ihx ihz
    rw [sb_add_left]
    exact U.add_mem ihx ihz
  · intro x y z hx hy hz ihx ihz
    rw [sb_add_right]
    exact U.add_mem ihx ihz
  · intro a x y hx hy ih
    rw [sb_smul_left]
    exact U.smul_mem a ih
  · intro a x y hx hy ih
    rw [sb_smul_right]
    exact U.smul_mem a ih

def evenEvenValue : EvenIndex → EvenIndex → M R
  | .h, .h => 0
  | .h, .e => (2 : R) • E_gen R
  | .h, .f => (-2 : R) • F_gen R
  | .e, .h => (-2 : R) • E_gen R
  | .e, .e => 0
  | .e, .f => H_gen R
  | .f, .h => (2 : R) • F_gen R
  | .f, .e => -H_gen R
  | .f, .f => 0

def evenOddValue : EvenIndex → OddIndex → M R
  | .h, .plus => Q_plus R
  | .h, .minus => -Q_minus R
  | .e, .plus => 0
  | .e, .minus => -Q_plus R
  | .f, .plus => -Q_minus R
  | .f, .minus => 0

def oddEvenValue : OddIndex → EvenIndex → M R
  | .plus, .h => -Q_plus R
  | .plus, .e => 0
  | .plus, .f => Q_minus R
  | .minus, .h => Q_minus R
  | .minus, .e => Q_plus R
  | .minus, .f => 0

def oddOddValue : OddIndex → OddIndex → M R
  | .plus, .plus => (2 : R) • E_gen R
  | .plus, .minus => H_gen R
  | .minus, .plus => H_gen R
  | .minus, .minus => (-2 : R) • F_gen R

private theorem even_even_evaluation (i j : EvenIndex) :
    sb false false (evenBasis (R := R) i) (evenBasis (R := R) j) =
      evenEvenValue (R := R) i j := by
  cases i <;> cases j <;>
    ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [sb, evenBasis, evenEvenValue,
      InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      H_gen, E_gen, F_gen, E, Matrix.mul_apply] <;> ring

private theorem even_odd_evaluation (i : EvenIndex) (j : OddIndex) :
    sb false true (evenBasis (R := R) i) (oddBasis (R := R) j) =
      evenOddValue (R := R) i j := by
  cases i <;> cases j <;>
    ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [sb, evenBasis, oddBasis, evenOddValue,
      InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      H_gen, E_gen, F_gen, Q_plus, Q_minus, E, Matrix.mul_apply]

private theorem odd_even_evaluation (i : OddIndex) (j : EvenIndex) :
    sb true false (oddBasis (R := R) i) (evenBasis (R := R) j) =
      oddEvenValue (R := R) i j := by
  cases i <;> cases j <;>
    ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [sb, evenBasis, oddBasis, oddEvenValue,
      InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      H_gen, E_gen, F_gen, Q_plus, Q_minus, E, Matrix.mul_apply]

private theorem odd_odd_evaluation (i j : OddIndex) :
    sb true true (oddBasis (R := R) i) (oddBasis (R := R) j) =
      oddOddValue (R := R) i j := by
  cases i <;> cases j <;>
    ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [sb, oddBasis, oddOddValue,
      InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      H_gen, E_gen, F_gen, Q_plus, Q_minus, E, Matrix.mul_apply] <;> ring

private theorem even_even_table (x : M R) (hx : x ∈ evenGenerators)
    (y : M R) (hy : y ∈ evenGenerators) :
    sb false false x y ∈ evenSpan := by
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  rw [even_even_evaluation]
  cases i <;> cases j <;> simp only [evenEvenValue]
  · exact evenSpan.zero_mem
  · exact evenSpan.smul_mem (2 : R) even_E_mem
  · exact evenSpan.smul_mem (-2 : R) even_F_mem
  · exact evenSpan.smul_mem (-2 : R) even_E_mem
  · exact evenSpan.zero_mem
  · exact even_H_mem
  · exact evenSpan.smul_mem (2 : R) even_F_mem
  · exact (evenSpan (R := R)).neg_mem (even_H_mem (R := R))
  · exact evenSpan.zero_mem

private theorem even_odd_table (x : M R) (hx : x ∈ evenGenerators)
    (y : M R) (hy : y ∈ oddGenerators) :
    sb false true x y ∈ oddSpan := by
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  rw [even_odd_evaluation]
  cases i <;> cases j <;> simp [evenOddValue]

private theorem odd_even_table (x : M R) (hx : x ∈ oddGenerators)
    (y : M R) (hy : y ∈ evenGenerators) :
    sb true false x y ∈ oddSpan := by
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  rw [odd_even_evaluation]
  cases i <;> cases j <;> simp [oddEvenValue]

private theorem odd_odd_table (x : M R) (hx : x ∈ oddGenerators)
    (y : M R) (hy : y ∈ oddGenerators) :
    sb true true x y ∈ evenSpan := by
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  rw [odd_odd_evaluation]
  cases i <;> cases j <;> simp only [oddOddValue]
  · exact evenSpan.smul_mem (2 : R) even_E_mem
  · exact even_H_mem
  · exact even_H_mem
  · exact evenSpan.smul_mem (-2 : R) even_F_mem

/-- The even span is closed under the even-even superbracket. -/
theorem even_even_span_closed {x y : M R}
    (hx : x ∈ evenSpan) (hy : y ∈ evenSpan) :
    sb false false x y ∈ evenSpan :=
  span_pair_closure evenSpan false false even_even_table hx hy

/-- The even-odd bracket maps the even span and odd span into the odd span. -/
theorem even_odd_span_closed {x y : M R}
    (hx : x ∈ evenSpan) (hy : y ∈ oddSpan) :
    sb false true x y ∈ oddSpan :=
  span_pair_closure oddSpan false true even_odd_table hx hy

/-- The odd-even bracket maps the odd span and even span into the odd span. -/
theorem odd_even_span_closed {x y : M R}
    (hx : x ∈ oddSpan) (hy : y ∈ evenSpan) :
    sb true false x y ∈ oddSpan :=
  span_pair_closure oddSpan true false odd_even_table hx hy

/-- The odd-odd superbracket maps the odd span into the even span. -/
theorem odd_odd_span_closed {x y : M R}
    (hx : x ∈ oddSpan) (hy : y ∈ oddSpan) :
    sb true true x y ∈ evenSpan :=
  span_pair_closure evenSpan true true odd_odd_table hx hy

end MatrixSpans

end InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair
