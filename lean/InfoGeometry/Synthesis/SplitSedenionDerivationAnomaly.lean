/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Finite Split-Sedenion Dimension Arithmetic and Doubling-Matrix Identities

This module does not construct the derivation algebra of split sedenions or prove an
isomorphism $\operatorname{Der}(\mathbb{S}_s) \cong \mathfrak{g}_{2(2)} \oplus
\mathfrak{sl}(2,\mathbb{R})$. It proves finite dimension arithmetic, a generic
Cayley--Dickson derivation-lifting implication, and matrix identities for three explicit
$(2,1)$-metric matrices. Those matrices are not shown here to act by derivations of a
split-sedenion product. The contents are:

1. **Section 1 (Dimension arithmetic only)**: checks the displayed numerical equalities. It does
   not define the split-sedenion imaginary space, its representation decomposition, or its
   derivation algebra.
2. **Section 2 (Conditional Cayley--Dickson derivation lifting)**:
   - Defines the general Cayley–Dickson product `cdMul γ (a, b) (c, d) = (a * c + γ • (d⋆ * b), d * a + b * c⋆)`
     and involution `cdConj (a, b) = (a⋆, -b)` over any non-associative ring $A$ equipped with an
     involution $\star$.
   - Proves that every $\star$-derivation $D_0 \in \operatorname{Der}(A, \star)$
     ($D_0(x y) = (D_0 x) y + x (D_0 y)$ and $D_0(x^\star) = (D_0 x)^\star$) lifts diagonally via
     `cdLift D_0 (a, b) = (D_0 a, D_0 b)` to an exact derivation of `cdMul γ` that commutes with
     `cdConj`; a separate pointwise function identity records compatibility with commutators.
   - The result is conditional on a supplied star-derivation; the file does not instantiate it
     for split octonions.
3. **Section 3 (Explicit finite matrix identities)**:
   - Defines a form of signature $(2,1)$ and three concrete matrices. It proves matrix
     skewness, trace and bracket identities, bilinear-form invariance, and a quadratic matrix
     identity. Section 5 separately defines an auxiliary four-dimensional coordinate product and
     proves these matrices act on it by derivations; no identification with split sedenions is proved.
   - Proves $\eta_{(2,1)}$-skew-adjointness $X^T \eta_{(2,1)} + \eta_{(2,1)} X = 0$ and the
     displayed bracket table for these matrices
     $[J_{12}, K_{13}] = K_{23}$, $[J_{12}, K_{23}] = -K_{13}$, $[K_{13}, K_{23}] = -J_{12}$,
   and a generic left/right matrix-action identity, without concrete $G_2$ or split-sedenion
   module actions.
4. **Section 4 (Conditional first-order zero-product identity and square-zero equation)**:
   - Proves generically that a map satisfying Leibniz sends a zero-product pair into the
     corresponding first-order zero-product equation. No particular split-sedenion derivation
     or zero-divisor locus is defined.
   - Proves the square-zero equation $(u,1) \cdot_{\mathrm{CD}} (u,1) = (0,0)$ under
     $u^2 = 1$, $u^\star = -u$, and split doubling parameter $\gamma=-1$. Nonzeroness is not asserted.
-/

namespace InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly

open Matrix

/-! ## Section 1: Dimension arithmetic -/

/-- Numerical equalities associated with the split-sedenion dimension discussion.
This proposition is arithmetic only; it does not establish dimensions of algebraic
objects or a decomposition of their representations. -/
theorem split_sedenion_dimension_arithmetic_packet :
    (2 ^ 4 = 16 ∧ 8 + 8 = 16 ∧ 16 - 1 = 15) ∧
    (7 * 2 + 1 * 1 = 15) ∧
    (14 + 3 = 17 ∧ 2 * 14 - 17 = 11) ∧
    (Nat.choose 15 2 = 105) := by
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩

/-! ## Section 2: Universal Cayley–Dickson Doubling & Diagonal Derivation Lifting -/

/-- The general Cayley–Dickson multiplication on $A \times A$ with scalar parameter $\gamma \in R$
and involution $\star : A \to A$:
$$(a, b) \cdot_{\gamma} (c, d) = \big(a c + \gamma (d^\star b),\; d a + b c^\star\big).$$
Because $A$ (such as the split octonions $\mathbb{O}_s$) is not assumed associative, this formula
uses the general `[NonUnitalNonAssocRing A]` typeclass. -/
def cdMul {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    (starA : A → A) (γ : R) (x y : A × A) : A × A :=
  (x.1 * y.1 + γ • (starA y.2 * x.2), y.2 * x.1 + x.2 * starA y.1)

/-- The Cayley–Dickson involution on $A \times A$:
$$(a, b)^\star = (a^\star, -b).$$ -/
def cdConj {A : Type*} [NonUnitalNonAssocRing A] (starA : A → A) (x : A × A) : A × A :=
  (starA x.1, -x.2)

/-- Diagonal lifting of an map $D_0 : A \to A$ to the Cayley–Dickson doubled space $A \times A$:
$$D(a, b) = (D_0 a, D_0 b).$$ -/
def cdLift {A : Type*} (D₀ : A → A) (x : A × A) : A × A :=
  (D₀ x.1, D₀ x.2)

/-- Predicate packaging an $R$-linear $\star$-derivation $D_0 \in \operatorname{Der}_R(A, \star)$
of a possibly non-associative algebra $(A, \cdot, \star)$. -/
def IsStarDerivation (R : Type*) {A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    (starA : A → A) (D₀ : A → A) : Prop :=
  (∀ x y : A, D₀ (x + y) = D₀ x + D₀ y) ∧
  (∀ x : A, D₀ (-x) = -D₀ x) ∧
  (∀ (c : R) (x : A), D₀ (c • x) = c • D₀ x) ∧
  (∀ x y : A, D₀ (x * y) = D₀ x * y + x * D₀ y) ∧
  (∀ x : A, D₀ (starA x) = starA (D₀ x))

/-- **Conditional Cayley–Dickson derivation identity**:
Every $\star$-derivation $D_0$ of a (possibly non-associative) algebra $(A, \star)$ lifts
diagonally via `cdLift D₀ (a, b) = (D₀ a, D₀ b)` to an exact derivation of the Cayley–Dickson
doubled algebra `(A × A, cdMul starA γ)` and commutes with the Cayley–Dickson involution `cdConj`.
This theorem does not assert injectivity of a map on derivation algebras or instantiate a specific
octonion algebra. -/
theorem cdLift_is_cayleyDickson_star_derivation
    {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (starA : A → A) (γ : R) (D₀ : A → A)
    (hD : IsStarDerivation R starA D₀) (x y : A × A) :
    cdLift D₀ (cdMul starA γ x y) =
      cdMul starA γ (cdLift D₀ x) y + cdMul starA γ x (cdLift D₀ y) ∧
    cdLift D₀ (cdConj starA x) = cdConj starA (cdLift D₀ x) := by
  rcases hD with ⟨h_add, h_neg, h_smul, h_leibniz, h_star⟩
  refine ⟨?_, ?_⟩
  · ext
    · dsimp [cdLift, cdMul]
      rw [h_add, h_leibniz, h_smul, h_leibniz, h_star, smul_add]
      abel
    · dsimp [cdLift, cdMul]
      rw [h_add, h_leibniz, h_leibniz, h_star]
      abel
  · ext
    · dsimp [cdLift, cdConj]
      exact h_star x.1
    · dsimp [cdLift, cdConj]
      exact h_neg x.2

/-- The diagonal lift preserves pointwise commutators of maps:
$$\big[\operatorname{cdLift}(D_1), \operatorname{cdLift}(D_2)\big](x)
  = \operatorname{cdLift}\big([D_1, D_2]\big)(x).$$ -/
theorem cdLift_pointwise_commutator_identity
    {A : Type*} [AddCommGroup A] (D₁ D₂ : A → A) (x : A × A) :
    cdLift D₁ (cdLift D₂ x) - cdLift D₂ (cdLift D₁ x) =
      cdLift (fun a => D₁ (D₂ a) - D₂ (D₁ a)) x := by
  ext <;> rfl

/-! ## Section 3: Explicit `(2,1)` matrix identities -/

/-- The diagonal matrix representing a bilinear form of signature `(2,1)` on `Fin 3 → R`.
This coordinate definition does not identify the coordinates with a Cayley--Dickson carrier. -/
def eta21 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, -1]

/-- A concrete matrix generator preserving `eta21` infinitesimally:
$$J_{12}(u) = v, \quad J_{12}(v) = -u, \quad J_{12}(uv) = 0.$$ -/
def sl2GenJ12 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, -1, 0;
     1,  0, 0;
     0,  0, 0]

/-- A second concrete matrix generator preserving `eta21` infinitesimally:
$$K_{13}(u) = uv, \quad K_{13}(v) = 0, \quad K_{13}(uv) = u.$$ -/
def sl2GenK13 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1;
     0, 0, 0;
     1, 0, 0]

/-- A third concrete matrix generator preserving `eta21` infinitesimally:
$$K_{23}(u) = 0, \quad K_{23}(v) = uv, \quad K_{23}(uv) = v.$$ -/
def sl2GenK23 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 0;
     0, 0, 1;
     0, 1, 0]

/-- Matrix commutator $[X, Y] = X Y - Y X$. -/
def matBracket {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (X Y : Matrix n n R) : Matrix n n R :=
  X * Y - Y * X

/-- A commutator has trace zero, so commutator action preserves the trace-free
endomorphism subspace. -/
theorem matBracket_trace_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (X Y : Matrix n n R) :
    trace (matBracket X Y) = 0 := by
  unfold matBracket
  rw [Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self]

/-- Matrix identities for the three concrete generators; no algebra action is defined here:
1. Skew-adjoint with respect to the $(2,1)$ split metric $\eta_{(2,1)} = \operatorname{diag}(1, 1, -1)$:
   $$X^T \eta_{(2,1)} + \eta_{(2,1)} X = 0,$$
2. Trace-free ($\operatorname{tr}(J_{12}) = \operatorname{tr}(K_{13}) = \operatorname{tr}(K_{23}) = 0$),
3. Satisfy the following bracket relations:
   $$[J_{12}, K_{13}] = K_{23}, \qquad [J_{12}, K_{23}] = -K_{13}, \qquad [K_{13}, K_{23}] = -J_{12},$$
The quadratic matrix expression and its value are proved separately below. -/
theorem so21_matrix_generator_relations (R : Type*) [CommRing R] :
    ((sl2GenJ12 (R := R))ᵀ * eta21 (R := R) + eta21 (R := R) * sl2GenJ12 (R := R) = 0 ∧
     (sl2GenK13 (R := R))ᵀ * eta21 (R := R) + eta21 (R := R) * sl2GenK13 (R := R) = 0 ∧
     (sl2GenK23 (R := R))ᵀ * eta21 (R := R) + eta21 (R := R) * sl2GenK23 (R := R) = 0) ∧
    (trace (sl2GenJ12 (R := R)) = 0 ∧
     trace (sl2GenK13 (R := R)) = 0 ∧
     trace (sl2GenK23 (R := R)) = 0) ∧
    (matBracket (sl2GenJ12 (R := R)) (sl2GenK13 (R := R)) = sl2GenK23 (R := R) ∧
     matBracket (sl2GenJ12 (R := R)) (sl2GenK23 (R := R)) = -sl2GenK13 (R := R) ∧
     matBracket (sl2GenK13 (R := R)) (sl2GenK23 (R := R)) = -sl2GenJ12 (R := R)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [sl2GenJ12, eta21, mul_apply, Fin.sum_univ_three]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [sl2GenK13, eta21, mul_apply, Fin.sum_univ_three]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [sl2GenK23, eta21, mul_apply, Fin.sum_univ_three]
  · simp [sl2GenJ12, trace, diag, Fin.sum_univ_three]
  · simp [sl2GenK13, trace, diag, Fin.sum_univ_three]
  · simp [sl2GenK23, trace, diag, Fin.sum_univ_three]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [matBracket, sl2GenJ12, sl2GenK13, sl2GenK23]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [matBracket, sl2GenJ12, sl2GenK13, sl2GenK23]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [matBracket, sl2GenJ12, sl2GenK13, sl2GenK23]

/-- For every nontrivial coefficient ring, the displayed matrix generators do
not commute. This supplies a concrete operator witness for the generic matrix
carrier in this file. -/
theorem sl2_generator_products_noncommute {R : Type*} [CommRing R] [Nontrivial R] :
    sl2GenJ12 (R := R) * sl2GenK13 (R := R) ≠
      sl2GenK13 (R := R) * sl2GenJ12 (R := R) := by
  intro h
  have hzero : matBracket (sl2GenJ12 (R := R)) (sl2GenK13 (R := R)) = 0 := by
    unfold matBracket
    rw [h]
    simp
  rw [(so21_matrix_generator_relations R).2.2.1] at hzero
  have hentry := congrFun (congrFun hzero 1) 2
  simp [sl2GenK23] at hentry

/-- The concrete generators exhibit noncommutativity in this matrix algebra:
the commutator of `J₁₂` and `K₁₃` is the nonzero matrix `K₂₃`. -/
theorem sl2_generator_commutator_nonzero :
    matBracket (sl2GenJ12 (R := ℝ)) (sl2GenK13 (R := ℝ)) ≠ 0 := by
  rw [(so21_matrix_generator_relations ℝ).2.2.1]
  intro h
  have h12 := congrFun (congrFun h 1) 2
  norm_num [sl2GenK23] at h12

/-- The symmetric bilinear form of signature `(2,1)` on the coefficient space
of the three displayed doubling generators. -/
def so21BilinearForm {R : Type*} [CommRing R]
    (u v : Fin 3 → R) : R :=
  u 0 * v 0 + u 1 * v 1 - u 2 * v 2

/-- The three concrete matrices preserve the `(2,1)` bilinear form infinitesimally.

This is the vector-space metric identity
`⟨Xu,v⟩ + ⟨u,Xv⟩ = 0`; by itself it does not assert that these maps
differentiate a Cayley--Dickson product. -/
theorem sl2_so21_generators_metric_invariance {R : Type*} [CommRing R]
    (u v : Fin 3 → R) :
    so21BilinearForm ((sl2GenJ12 (R := R)).mulVec u) v +
        so21BilinearForm u ((sl2GenJ12 (R := R)).mulVec v) = 0 ∧
    so21BilinearForm ((sl2GenK13 (R := R)).mulVec u) v +
        so21BilinearForm u ((sl2GenK13 (R := R)).mulVec v) = 0 ∧
    so21BilinearForm ((sl2GenK23 (R := R)).mulVec u) v +
        so21BilinearForm u ((sl2GenK23 (R := R)).mulVec v) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [so21BilinearForm, sl2GenJ12, sl2GenK13, sl2GenK23,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The quadratic operator formed from the three displayed `(2,1)` generators.
The signs are fixed by the concrete matrices in this file. -/
def so21QuadraticMatrixExpression {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  -(sl2GenJ12 * sl2GenJ12) +
    sl2GenK13 * sl2GenK13 + sl2GenK23 * sl2GenK23

/-- For these concrete generators the quadratic expression is `2 I`; hence it
commutes with each generator. This is a finite matrix calculation, not a claim
about Casimir operators on the split-sedenion algebra. -/
theorem so21_quadratic_matrix_expression_eq_two_smul_identity_and_central
    (R : Type*) [CommRing R] :
    so21QuadraticMatrixExpression (R := R) =
        (2 : R) • (1 : Matrix (Fin 3) (Fin 3) R) ∧
    matBracket (so21QuadraticMatrixExpression (R := R)) (sl2GenJ12 (R := R)) = 0 ∧
    matBracket (so21QuadraticMatrixExpression (R := R)) (sl2GenK13 (R := R)) = 0 ∧
    matBracket (so21QuadraticMatrixExpression (R := R)) (sl2GenK23 (R := R)) = 0 := by
  have hcas : so21QuadraticMatrixExpression (R := R) =
      (2 : R) • (1 : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [so21QuadraticMatrixExpression, sl2GenJ12, sl2GenK13, sl2GenK23] <;> ring
  refine ⟨hcas, ?_, ?_, ?_⟩
  · rw [hcas]
    simp [matBracket]
  · rw [hcas]
    simp [matBracket]
  · rw [hcas]
    simp [matBracket]

/-- The induced quadratic operator for the commutator action on endomorphisms:
`-ad(J12)^2 + ad(K13)^2 + ad(K23)^2`. -/
def so21AdjointQuadraticAction {R : Type*} [CommRing R]
    (A : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  -matBracket (sl2GenJ12 (R := R)) (matBracket (sl2GenJ12 (R := R)) A) +
    matBracket (sl2GenK13 (R := R)) (matBracket (sl2GenK13 (R := R)) A) +
    matBracket (sl2GenK23 (R := R)) (matBracket (sl2GenK23 (R := R)) A)

/-- On each of the three displayed generators, the commutator (adjoint) action
has quadratic eigenvalue `2`. This identifies the eigenvalue on their span; it
does not assert that the same operator is scalar on all trace-free matrices. -/
theorem so21_adjoint_quadratic_action_on_generators (R : Type*) [CommRing R] :
    so21AdjointQuadraticAction (sl2GenJ12 (R := R)) =
        (2 : R) • sl2GenJ12 (R := R) ∧
    so21AdjointQuadraticAction (sl2GenK13 (R := R)) =
        (2 : R) • sl2GenK13 (R := R) ∧
    so21AdjointQuadraticAction (sl2GenK23 (R := R)) =
        (2 : R) • sl2GenK23 (R := R) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [so21AdjointQuadraticAction, matBracket,
        sl2GenJ12, sl2GenK13, sl2GenK23] <;> ring

/-! ### The quadratic adjoint action on trace-free endomorphisms

The trace-free endomorphisms of the three-dimensional `(2,1)` carrier are not all
the adjoint representation.  Relative to `eta21`, they split into an eta-skew
part and an eta-self-adjoint trace-free part.  The quadratic
operator below has different eigenvalues on those two parts.  These are statements
about `3 × 3` matrices only; they do not identify either part with a summand of a
split-sedenion derivation algebra. -/

/-- Skew-adjointness with respect to the displayed `(2,1)` form. -/
def so21EtaSkewAdjoint {R : Type*} [CommRing R]
    (A : Matrix (Fin 3) (Fin 3) R) : Prop :=
  Aᵀ * eta21 + eta21 * A = 0

/-- Self-adjointness with respect to the displayed `(2,1)` form. -/
def so21EtaSelfAdjoint {R : Type*} [CommRing R]
    (A : Matrix (Fin 3) (Fin 3) R) : Prop :=
  Aᵀ * eta21 - eta21 * A = 0

/-- On the eta-skew subspace, the quadratic commutator action has eigenvalue `2`.
This is the adjoint sector. -/
theorem so21_adjoint_quadratic_action_eq_two_of_eta_skew
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : so21EtaSkewAdjoint A) :
    so21AdjointQuadraticAction A = (2 : ℝ) • A := by
  change Aᵀ * eta21 + eta21 * A = 0 at hA
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h22 := congrFun (congrFun hA 2) 2
  have h01 := congrFun (congrFun hA 0) 1
  have h02 := congrFun (congrFun hA 0) 2
  have h12 := congrFun (congrFun hA 1) 2
  simp [eta21, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
    Fin.sum_univ_three]
    at h00 h11 h22 h01 h02 h12
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [so21AdjointQuadraticAction, matBracket,
      sl2GenJ12, sl2GenK13, sl2GenK23, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three] <;>
    linarith

/-- On the eta-self-adjoint trace-free subspace, the quadratic commutator action
has eigenvalue `6`. -/
theorem so21_adjoint_quadratic_action_eq_six_of_eta_selfAdjoint_trace_free
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : so21EtaSelfAdjoint A) (htrace : Matrix.trace A = 0) :
    so21AdjointQuadraticAction A = (6 : ℝ) • A := by
  change Aᵀ * eta21 - eta21 * A = 0 at hA
  have h01 := congrFun (congrFun hA 0) 1
  have h02 := congrFun (congrFun hA 0) 2
  have h12 := congrFun (congrFun hA 1) 2
  simp [eta21, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
    Fin.sum_univ_three]
    at h01 h02 h12
  have htr := htrace
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three] at htr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [so21AdjointQuadraticAction, matBracket,
      sl2GenJ12, sl2GenK13, sl2GenK23, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three] <;>
    linarith

/-- Every trace-free matrix admits an eta-skew plus eta-self-adjoint trace-free
decomposition. The components are explicitly constructed; this theorem asserts
existence and does not assert uniqueness. -/
theorem trace_free_matrix_eta_adjoint_sector_decomposition
    (A : Matrix (Fin 3) (Fin 3) ℝ) (htrace : Matrix.trace A = 0) :
    ∃ K S : Matrix (Fin 3) (Fin 3) ℝ,
      A = K + S ∧ so21EtaSkewAdjoint K ∧ so21EtaSelfAdjoint S ∧
      Matrix.trace S = 0 := by
  let K : Matrix (Fin 3) (Fin 3) ℝ :=
    (1 / 2 : ℝ) • (A - eta21 * Aᵀ * eta21)
  let S : Matrix (Fin 3) (Fin 3) ℝ :=
    (1 / 2 : ℝ) • (A + eta21 * Aᵀ * eta21)
  refine ⟨K, S, ?_, ?_, ?_, ?_⟩
  · dsimp [K, S]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eta21] <;> ring
  · dsimp [so21EtaSkewAdjoint, K]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eta21, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
        Fin.sum_univ_three] <;> ring
  · dsimp [so21EtaSelfAdjoint, S]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eta21, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
        Fin.sum_univ_three] <;> ring
  · dsimp [S]
    rw [Matrix.trace_smul, Matrix.trace_add]
    have hconj : Matrix.trace (eta21 * Aᵀ * eta21) = Matrix.trace A := by
      have heta : eta21 * eta21 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [eta21, Matrix.mul_apply, Fin.sum_univ_three]
      calc
        Matrix.trace (eta21 * Aᵀ * eta21) =
            Matrix.trace (eta21 * (eta21 * Aᵀ)) := by
          exact Matrix.trace_mul_comm (eta21 * Aᵀ) eta21
        _ = Matrix.trace ((eta21 * eta21) * Aᵀ) := by rw [← Matrix.mul_assoc]
        _ = Matrix.trace Aᵀ := by rw [heta, one_mul]
        _ = Matrix.trace A := Matrix.trace_transpose A
    rw [hconj, htrace]
    norm_num

/-- Generic left and right matrix multiplications commute on rectangular matrices.
This identity alone does not define representations of $\mathfrak{g}_{2(2)}$ or
$\mathfrak{sl}(2,R)$ on a split-sedenion carrier:
$$G (M S^T) - (G M) S^T = 0.$$ -/
theorem matrix_left_right_actions_commute {R : Type*} [CommRing R]
    (G : Matrix (Fin 7) (Fin 7) R) (S : Matrix (Fin 2) (Fin 2) R)
    (M : Matrix (Fin 7) (Fin 2) R) :
    G * (M * Sᵀ) - (G * M) * Sᵀ = 0 := by
  rw [Matrix.mul_assoc, sub_self]

/-! ## Section 4: Conditional derivation tangent identity and split-doubling zero divisor -/

/-- Conditional first-order zero-product identity: for any algebra `A` and map `D` satisfying
the Leibniz rule
$D(x y) = (D x) y + x (D y)$ and $D(0) = 0$, every zero-divisor pair $(x, y)$ with $x y = 0$
satisfies the tangent zero-divisor equation:
$$(D x) y + x (D y) = 0.$$
This does not identify a particular split-sedenion derivation or its zero-divisor locus. -/
theorem derivation_preserves_zero_divisor_tangent {A : Type*} [NonUnitalNonAssocRing A]
    (D : A → A) (hD0 : D 0 = 0)
    (hLeibniz : ∀ a b : A, D (a * b) = D a * b + a * D b)
    {x y : A} (hxy : x * y = 0) :
    D x * y + x * D y = 0 := by
  have h1 : D (x * y) = D x * y + x * D y := hLeibniz x y
  rw [hxy, hD0] at h1
  exact h1.symm

/-- **Split Cayley–Dickson square-zero identity**:
Let $(A, \star)$ be an algebra with involution and let $u \in A$ satisfy $u^2 = 1$ and
$u^\star = -u$. In the displayed doubling formula with parameter $-1$, the element $(u,1)$ has
square zero. This proposition does not assert that $(u,1)$ is nonzero:
$$(u, 1) \cdot_{-1} (u, 1) = (0, 0).$$ -/
theorem split_cayleyDickson_square_zero
    {R A : Type*} [CommRing R] [NonAssocRing A] [Module R A]
    (starA : A → A) (u : A)
    (h_star_one : starA 1 = 1)
    (h_u_sq : u * u = 1)
    (h_u_star : starA u = -u) :
    cdMul starA (-1 : R) (u, (1 : A)) (u, (1 : A)) = (0, 0) := by
  ext
  · dsimp [cdMul]
    rw [h_u_sq, h_star_one, mul_one, neg_one_smul, add_neg_cancel]
  · dsimp [cdMul]
    rw [one_mul, h_u_star, one_mul, add_neg_cancel]

/-! ## Section 5: Coordinate-algebra derivation identities -/

/-- The associator $[a, b, c] = (a b) c - a (b c)$ in a non-associative ring $B$. -/
def associator {B : Type*} [NonUnitalNonAssocRing B] (a b c : B) : B :=
  (a * b) * c - a * (b * c)

/-- On any associative ring $B$, the associator vanishes identically. -/
theorem associator_eq_zero_of_ring {B : Type*} [Ring B] (a b c : B) :
    associator a b c = 0 := by
  dsimp [associator]
  rw [mul_assoc, sub_self]

/-- The $(2,1)$-signature cross product on $Fin 3 \to R$:
$$(u \times_{(2,1)} v)_0 = u_1 v_2 - u_2 v_1, \quad
  (u \times_{(2,1)} v)_1 = u_2 v_0 - u_0 v_2, \quad
  (u \times_{(2,1)} v)_2 = u_1 v_0 - u_0 v_1.$$ -/
def so21CrossProduct {R : Type*} [CommRing R] (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 1 * v 0 - u 0 * v 1]

/-- A coordinate algebra multiplication on $R \times (Fin 3 \to R)$:
$$(x_0, \vec{x}) \cdot_{(2,1)} (y_0, \vec{y}) =
  \big(x_0 y_0 - \langle \vec{x}, \vec{y} \rangle_{(2,1)},\;
       x_0 \vec{y} + y_0 \vec{x} + \vec{x} \times_{(2,1)} \vec{y}\big).$$ -/
def socleDoublingMul {R : Type*} [CommRing R]
    (x y : R × (Fin 3 → R)) : R × (Fin 3 → R) :=
  (x.1 * y.1 - so21BilinearForm x.2 y.2,
   fun i => x.1 * y.2 i + y.1 * x.2 i + so21CrossProduct x.2 y.2 i)

/-- Action of a $3 \times 3$ matrix on the vector coordinate of this four-dimensional carrier.
No map from this coordinate algebra to split sedenions is defined in this module. -/
def socleDerivation {R : Type*} [CommRing R]
    (X : Matrix (Fin 3) (Fin 3) R) (x : R × (Fin 3 → R)) : R × (Fin 3 → R) :=
  (0, X.mulVec x.2)

/-- All three concrete $(2,1)$ matrices $J_{12}, K_{13}, K_{23}$ act as derivations of the
$(2,1)$ cross product `so21CrossProduct`:
$$X(u \times_{(2,1)} v) = (X u) \times_{(2,1)} v + u \times_{(2,1)} (X v).$$ -/
theorem so21_generators_leibniz_crossProduct {R : Type*} [CommRing R]
    (u v : Fin 3 → R) :
    (sl2GenJ12 (R := R)).mulVec (so21CrossProduct u v) =
      so21CrossProduct ((sl2GenJ12 (R := R)).mulVec u) v +
        so21CrossProduct u ((sl2GenJ12 (R := R)).mulVec v) ∧
    (sl2GenK13 (R := R)).mulVec (so21CrossProduct u v) =
      so21CrossProduct ((sl2GenK13 (R := R)).mulVec u) v +
        so21CrossProduct u ((sl2GenK13 (R := R)).mulVec v) ∧
    (sl2GenK23 (R := R)).mulVec (so21CrossProduct u v) =
      so21CrossProduct ((sl2GenK23 (R := R)).mulVec u) v +
        so21CrossProduct u ((sl2GenK23 (R := R)).mulVec v) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;>
      simp [so21CrossProduct, sl2GenJ12, dotProduct, Fin.sum_univ_three] <;>
      ring
  · ext i; fin_cases i <;>
      simp [so21CrossProduct, sl2GenK13, dotProduct, Fin.sum_univ_three] <;>
      ring
  · ext i; fin_cases i <;>
      simp [so21CrossProduct, sl2GenK23, dotProduct, Fin.sum_univ_three] <;>
      ring

/-- Each of the three displayed matrices differentiates the coordinate multiplication
`socleDoublingMul`. This statement concerns the explicitly defined four-dimensional coordinate
algebra; it does not identify an action on split sedenions:
$$D_X(x \cdot_{(2,1)} y) = D_X(x) \cdot_{(2,1)} y + x \cdot_{(2,1)} D_X(y).$$ -/
theorem so21_socleDerivation_leibniz_test {R : Type*} [CommRing R]
    (x y : R × (Fin 3 → R)) :
    socleDerivation (sl2GenJ12 (R := R)) (socleDoublingMul x y) =
      socleDoublingMul (socleDerivation (sl2GenJ12 (R := R)) x) y +
        socleDoublingMul x (socleDerivation (sl2GenJ12 (R := R)) y) ∧
    socleDerivation (sl2GenK13 (R := R)) (socleDoublingMul x y) =
      socleDoublingMul (socleDerivation (sl2GenK13 (R := R)) x) y +
        socleDoublingMul x (socleDerivation (sl2GenK13 (R := R)) y) ∧
    socleDerivation (sl2GenK23 (R := R)) (socleDoublingMul x y) =
      socleDoublingMul (socleDerivation (sl2GenK23 (R := R)) x) y +
        socleDoublingMul x (socleDerivation (sl2GenK23 (R := R)) y) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    · simp [socleDerivation, socleDoublingMul, so21BilinearForm, sl2GenJ12,
            dotProduct, Fin.sum_univ_three]
    · fin_cases i <;>
        simp [socleDerivation, socleDoublingMul, so21CrossProduct, sl2GenJ12,
              dotProduct, Fin.sum_univ_three] <;>
        ring
  · ext i
    · simp [socleDerivation, socleDoublingMul, so21BilinearForm, sl2GenK13,
            dotProduct, Fin.sum_univ_three]
    · fin_cases i <;>
        simp [socleDerivation, socleDoublingMul, so21CrossProduct, sl2GenK13,
              dotProduct, Fin.sum_univ_three] <;>
        ring
  · ext i
    · simp [socleDerivation, socleDoublingMul, so21BilinearForm, sl2GenK23,
            dotProduct, Fin.sum_univ_three]
    · fin_cases i <;>
        simp [socleDerivation, socleDoublingMul, so21CrossProduct, sl2GenK23,
              dotProduct, Fin.sum_univ_three] <;>
        ring

/-- Generic left and right matrix actions on $\operatorname{Mat}_{7 \times 2}(R)$ commute, and scalar
multiples of the $7 \times 7$ and $2 \times 2$ identities scale $M$ by the product scalar. -/
theorem generic_matrix_left_right_scalar_identity {R : Type*} [CommRing R]
    (Cg : Matrix (Fin 7) (Fin 7) R) (Csl2 : Matrix (Fin 2) (Fin 2) R)
    (M : Matrix (Fin 7) (Fin 2) R) (mg_sq cs : R) :
    Cg * (M * Csl2ᵀ) = (Cg * M) * Csl2ᵀ ∧
    ((mg_sq • (1 : Matrix (Fin 7) (Fin 7) R)) * M) *
      (cs • (1 : Matrix (Fin 2) (Fin 2) R))ᵀ = (mg_sq * cs) • M := by
  refine ⟨(Matrix.mul_assoc Cg M Csl2ᵀ).symm, ?_⟩
  rw [Matrix.smul_mul, Matrix.one_mul, transpose_smul, transpose_one,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]

end InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
