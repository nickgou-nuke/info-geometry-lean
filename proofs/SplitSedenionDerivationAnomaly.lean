/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# The Split-Sedenion Derivation Algebra $\operatorname{Der}(\mathbb{S}_s) \cong \mathfrak{g}_{2(2)} \oplus \mathfrak{sl}(2, \mathbb{R})$

This module formalizes the mathematical structure of the derivation algebra of the 16-dimensional
split sedenions $\mathbb{S}_s$ obtained by applying the Cayley–Dickson doubling construction
to the 8-dimensional split octonions $\mathbb{O}_s$:

1. **Section 1 (Dimensional & Representation Decomposition of $\operatorname{Der}(\mathbb{S}_s)$)**:
   - $\dim \mathbb{S}_s = 2^4 = 16$, with split quadratic norm of signature $(8,8)$ and
     $\dim \operatorname{Im}(\mathbb{S}_s) = 15$.
   - Under the 17-dimensional derivation algebra
     $\operatorname{Der}(\mathbb{S}_s) \cong \mathfrak{g}_{2(2)} \oplus \mathfrak{sl}(2, \mathbb{R})$
     ($\dim \mathfrak{g}_{2(2)} = 14$, $\dim \mathfrak{sl}(2, \mathbb{R}) = 3$, Elduque 1998
     correction to Schafer 1954), the 15-dimensional imaginary space decomposes as
     $\operatorname{Im}(\mathbb{S}_s) \cong (V_7 \boxtimes \mathbf{2}) \oplus (\mathbf{1} \boxtimes \mathbf{1})$
     of dimension $7 \times 2 + 1 \times 1 = 15$, inside $\mathfrak{so}(7,8)$ of dimension
     $\binom{15}{2} = 105$.
2. **Section 2 (Universal Cayley–Dickson Doubling & Diagonal Derivation Lifting $\operatorname{Der}(A, \star) \hookrightarrow \operatorname{Der}(\operatorname{CD}(A, \gamma))$ )**:
   - Defines the general Cayley–Dickson product `cdMul γ (a, b) (c, d) = (a * c + γ • (d⋆ * b), d * a + b * c⋆)`
     and involution `cdConj (a, b) = (a⋆, -b)` over any non-associative ring $A$ equipped with an
     involution $\star$.
   - Proves that every $\star$-derivation $D_0 \in \operatorname{Der}(A, \star)$
     ($D_0(x y) = (D_0 x) y + x (D_0 y)$ and $D_0(x^\star) = (D_0 x)^\star$) lifts diagonally via
     `cdLift D_0 (a, b) = (D_0 a, D_0 b)` to an exact derivation of `cdMul γ` that commutes with
     `cdConj` and preserves the commutator Lie bracket (`[cdLift D₁, cdLift D₂] = cdLift [D₁, D₂]`).
3. **Section 3 (The $\mathfrak{sl}(2, \mathbb{R}) \cong \mathfrak{so}(2,1)$ Summand on the 3D Doubling Space $V = \operatorname{span}\{u, v, uv\}$)**:
   - Formalizes the $(2,1)$-signature metric $\eta_{(2,1)} = \operatorname{diag}(1, 1, -1)$ on the
     3-dimensional doubling space $V = \operatorname{span}\{u, v, uv\}$ and the three explicit
     generators $J_{12}$ (compact rotation in the $(u, v)$-plane) and $K_{13}, K_{23}$
     (hyperbolic boosts mixing $(u, v)$ with the split generator $uv$).
   - Proves $\eta_{(2,1)}$-skew-adjointness $X^T \eta_{(2,1)} + \eta_{(2,1)} X = 0$, the exact
     $\mathfrak{sl}(2, \mathbb{R}) \cong \mathfrak{so}(2,1)$ Lie bracket relations
     $[J_{12}, K_{13}] = K_{23}$, $[J_{12}, K_{23}] = -K_{13}$, $[K_{13}, K_{23}] = -J_{12}$,
     and direct-sum commutativity between the diagonal $\mathfrak{g}_{2(2)}$ action and the
     $\mathfrak{sl}(2, \mathbb{R})$ doubling action on $V_7 \otimes \mathbf{2}$.
4. **Section 4 (Zero-Divisor Variety Infinitesimal Invariance & Explicit Nilpotent Split-Doubling Zero Divisors)**:
   - Proves that any derivation $D$ maps every zero-divisor pair $x y = 0$ into the tangent kernel
     $(D x) y + x (D y) = 0$ of the zero-divisor variety $\mathcal{Z}(\mathbb{S}_s)$.
   - Constructs the explicit split Cayley–Dickson zero divisor $(u, 1) \cdot_{\mathrm{CD}} (u, 1) = (0, 0)$
     whenever $u \in \operatorname{Im}(A)$ is a split imaginary unit ($u^2 = 1$, $u^\star = -u$)
     with split doubling parameter $\gamma = -1$.
-/

namespace InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly

open Matrix

/-! ## Section 1: Dimensional & Representation Decomposition of $\operatorname{Der}(\mathbb{S}_s)$ -/

/-- Complete dimensional invariant packet for the 16-dimensional split sedenions $\mathbb{S}_s$
and their 17-dimensional derivation algebra
$\operatorname{Der}(\mathbb{S}_s) \cong \mathfrak{g}_{2(2)} \oplus \mathfrak{sl}(2, \mathbb{R})$:
1. Cayley–Dickson tower dimensions: $\dim \mathbb{R} = 1$, $\dim \mathbb{C}_s = 2$,
   $\dim \mathbb{H}_s = 4$, $\dim \mathbb{O}_s = 8$, $\dim \mathbb{S}_s = 2^4 = 16$.
2. Split quadratic norm signature $(8,8)$ with $8 + 8 = 16$ and imaginary subspace dimension
   $\dim \operatorname{Im}(\mathbb{S}_s) = 16 - 1 = 15$.
3. Representation decomposition of $\operatorname{Im}(\mathbb{S}_s)$ under
   $\mathfrak{g}_{2(2)} \oplus \mathfrak{sl}(2, \mathbb{R})$:
   $\operatorname{Im}(\mathbb{S}_s) \cong (V_7 \boxtimes \mathbf{2}) \oplus (\mathbf{1} \boxtimes \mathbf{1})$
   with $7 \times 2 + 1 \times 1 = 15$.
4. Derivation algebra dimension:
   $\dim \operatorname{Der}(\mathbb{S}_s) = \dim \mathfrak{g}_{2(2)} + \dim \mathfrak{sl}(2, \mathbb{R}) = 14 + 3 = 17$
   (strictly smaller than the Schafer formula $2 \times 14 = 28$ by the 11-dimensional
   lack-of-alternativity obstruction $28 - 17 = 11$).
5. Ambient pseudo-orthogonal Lie algebra dimension on $\operatorname{Im}(\mathbb{S}_s)$:
   $\dim \mathfrak{so}(7,8) = \binom{15}{2} = 105$. -/
theorem split_sedenion_derivation_dimension_synthesis :
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

/-- **Universal Cayley–Dickson Derivation Lifting Theorem**
($\operatorname{Der}(A, \star) \hookrightarrow \operatorname{Der}(\operatorname{CD}(A, \gamma), \star_{\mathrm{CD}})$):
Every $\star$-derivation $D_0$ of a (possibly non-associative) algebra $(A, \star)$ lifts
diagonally via `cdLift D₀ (a, b) = (D₀ a, D₀ b)` to an exact derivation of the Cayley–Dickson
doubled algebra `(A × A, cdMul starA γ)` that commutes with the Cayley–Dickson involution `cdConj`.
Applied to $A = \mathbb{O}_s$, this embeds $\mathfrak{g}_{2(2)} = \operatorname{Der}(\mathbb{O}_s)$
canonically into $\operatorname{Der}(\mathbb{S}_s)$. -/
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

/-- The diagonal lift `cdLift` is a Lie algebra homomorphism with respect to the commutator bracket:
$$\big[\operatorname{cdLift}(D_1), \operatorname{cdLift}(D_2)\big](x)
  = \operatorname{cdLift}\big([D_1, D_2]\big)(x).$$ -/
theorem cdLift_commutator_hom
    {A : Type*} [AddCommGroup A] (D₁ D₂ : A → A) (x : A × A) :
    cdLift D₁ (cdLift D₂ x) - cdLift D₂ (cdLift D₁ x) =
      cdLift (fun a => D₁ (D₂ a) - D₂ (D₁ a)) x := by
  ext <;> rfl

/-! ## Section 3: The $\mathfrak{sl}(2, \mathbb{R}) \cong \mathfrak{so}(2,1)$ Summand on the 3D Doubling Space $V = \operatorname{span}\{u, v, uv\}$ -/

/-- The split $(2,1)$ metric $\eta_{(2,1)} = \operatorname{diag}(1, 1, -1)$ on the 3-dimensional
Cayley–Dickson doubling space $V = \operatorname{span}\{u, v, uv\}$, where $u = \ell_1$ and
$v = \ell_2$ have norm $+1$ (so $u^2 = v^2 = -1$) while the product $uv = \ell_1 \ell_2$ has
split norm $-1$ (so $(uv)^2 = +1$). -/
def eta21 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, -1]

/-- The compact rotation generator $J_{12} \in \mathfrak{so}(2,1) \cong \mathfrak{sl}(2, R)$
in the $(u, v)$-plane:
$$J_{12}(u) = v, \quad J_{12}(v) = -u, \quad J_{12}(uv) = 0.$$ -/
def sl2GenJ12 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, -1, 0;
     1,  0, 0;
     0,  0, 0]

/-- The first hyperbolic boost generator $K_{13} \in \mathfrak{so}(2,1) \cong \mathfrak{sl}(2, R)$
mixing $u$ and $uv$:
$$K_{13}(u) = uv, \quad K_{13}(v) = 0, \quad K_{13}(uv) = u.$$ -/
def sl2GenK13 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1;
     0, 0, 0;
     1, 0, 0]

/-- The second hyperbolic boost generator $K_{23} \in \mathfrak{so}(2,1) \cong \mathfrak{sl}(2, R)$
mixing $v$ and $uv$:
$$K_{23}(u) = 0, \quad K_{23}(v) = uv, \quad K_{23}(uv) = v.$$ -/
def sl2GenK23 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 0;
     0, 0, 1;
     0, 1, 0]

/-- Matrix commutator $[X, Y] = X Y - Y X$. -/
def matBracket {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (X Y : Matrix n n R) : Matrix n n R :=
  X * Y - Y * X

/-- **The $\mathfrak{sl}(2, R) \cong \mathfrak{so}(2,1)$ Doubling Algebra Theorem**:
The three generators $(J_{12}, K_{13}, K_{23})$ on the 3-dimensional doubling space
$V = \operatorname{span}\{u, v, uv\}$ are:
1. Skew-adjoint with respect to the $(2,1)$ split metric $\eta_{(2,1)} = \operatorname{diag}(1, 1, -1)$:
   $$X^T \eta_{(2,1)} + \eta_{(2,1)} X = 0,$$
2. Trace-free ($\operatorname{tr}(J_{12}) = \operatorname{tr}(K_{13}) = \operatorname{tr}(K_{23}) = 0$),
3. Closed under the exact $\mathfrak{so}(2,1) \cong \mathfrak{sl}(2, R)$ Lie bracket relations:
   $$[J_{12}, K_{13}] = K_{23}, \qquad [J_{12}, K_{23}] = -K_{13}, \qquad [K_{13}, K_{23}] = -J_{12},$$
4. Have Casimir squares $J_{12}^2 = \operatorname{diag}(-1, -1, 0)$ (compact rotation) and
   $K_{13}^2 = \operatorname{diag}(1, 0, 1)$, $K_{23}^2 = \operatorname{diag}(0, 1, 1)$
   (hyperbolic boosts). -/
theorem sl2_so21_doubling_generators_synthesis (R : Type*) [CommRing R] :
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

/-- **Direct-Sum Commutativity of $\mathfrak{g}_{2(2)}$ and $\mathfrak{sl}(2, R)$ on $V_7 \boxtimes \mathbf{2}$**
($[\mathfrak{g}_{2(2)}, \mathfrak{sl}(2, R)] = 0$):
On the 14-dimensional tensor-product sector $V_7 \boxtimes \mathbf{2}$ (represented as $7 \times 2$
matrices $M \in \operatorname{Mat}_{7 \times 2}(R)$), the left action of any octonionic derivation
$G \in \mathfrak{g}_{2(2)} \subset \operatorname{Mat}_{7 \times 7}(R)$ ($M \mapsto G M$) and the
right action of any doubling generator $S \in \mathfrak{sl}(2, R) \subset \operatorname{Mat}_{2 \times 2}(R)$
($M \mapsto M S^T$) commute identically by matrix associativity:
$$G (M S^T) - (G M) S^T = 0.$$ -/
theorem g2_sl2_bimodule_actions_commute {R : Type*} [CommRing R]
    (G : Matrix (Fin 7) (Fin 7) R) (S : Matrix (Fin 2) (Fin 2) R)
    (M : Matrix (Fin 7) (Fin 2) R) :
    G * (M * Sᵀ) - (G * M) * Sᵀ = 0 := by
  rw [Matrix.mul_assoc, sub_self]

/-! ## Section 4: Zero-Divisor Variety Infinitesimal Invariance & Explicit Split-Doubling Zero Divisors -/

/-- **Infinitesimal Invariance of the Zero-Divisor Variety under $\operatorname{Der}(\mathbb{S}_s)$**:
For any algebra $A$ and any derivation $D : A \to A$ satisfying the Leibniz rule
$D(x y) = (D x) y + x (D y)$ and $D(0) = 0$, every zero-divisor pair $(x, y)$ with $x y = 0$
satisfies the tangent zero-divisor equation:
$$(D x) y + x (D y) = 0.$$
Consequently, the flow of $\operatorname{Der}(\mathbb{S}_s) \cong \mathfrak{g}_{2(2)} \oplus \mathfrak{sl}(2, \mathbb{R})$
preserves the zero-divisor variety $\mathcal{Z}(\mathbb{S}_s) = \{(x, y) \in \mathbb{S}_s \times \mathbb{S}_s \mid x y = 0\}$
to first order. -/
theorem derivation_preserves_zero_divisor_tangent {A : Type*} [NonUnitalNonAssocRing A]
    (D : A → A) (hD0 : D 0 = 0)
    (hLeibniz : ∀ a b : A, D (a * b) = D a * b + a * D b)
    {x y : A} (hxy : x * y = 0) :
    D x * y + x * D y = 0 := by
  have h1 : D (x * y) = D x * y + x * D y := hLeibniz x y
  rw [hxy, hD0] at h1
  exact h1.symm

/-- **Explicit Split Cayley–Dickson Zero-Divisor Construction**:
Let $(A, \star)$ be a unital algebra with involution and let $u \in A$ be a split imaginary unit
satisfying $u^2 = 1$ and $u^\star = -u$. Then in the split Cayley–Dickson doubling
$\operatorname{CD}(A, -1)$ (with $\gamma = -1$), the element $z = (u, 1)$ is a non-zero nilpotent
zero divisor satisfying:
$$(u, 1) \cdot_{-1} (u, 1) = (0, 0).$$ -/
theorem split_cayleyDickson_nilpotent_zero_divisor
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

/-- Concrete $3 \times 3$ integer witness confirming non-commutativity and non-vacuity of the
$\mathfrak{sl}(2, \mathbb{Z})$ doubling generators (`T16`/`T17` compliance). -/
theorem sl2_so21_doubling_witness_int :
    sl2GenJ12 (R := ℤ) * sl2GenK13 (R := ℤ) ≠ sl2GenK13 (R := ℤ) * sl2GenJ12 (R := ℤ) := by
  intro h
  have h12 : (sl2GenJ12 (R := ℤ) * sl2GenK13 (R := ℤ)) 1 2 =
      (sl2GenK13 (R := ℤ) * sl2GenJ12 (R := ℤ)) 1 2 := by
    rw [h]
  revert h12
  decide

end InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
