# Tagged Lean code blocks: `aistudio_prompt_1iLTmbxfiVRM8rOhwchpAcmLD3r1zL4JA.json`

## Turn 0005, fence 001 — user; language `lean`

```lean
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

/-!
# Pure Algebraic Peirce Decomposition of an Arbitrary Element X by an Idempotent P
No physics terminology: purely associative ring theory.
-/

variable {B : Type*} [Ring B]

-- Arbitrary idempotent P and arbitrary element X
variable (P X : B)

def comm (x y : B) : B := x * y - y * x
def anticomm (x y : B) : B := x * y + y * x

-- The four Peirce blocks of X:
def P_11 (P X : B) : B := P * X * P
def P_10 (P X : B) : B := P * X * (1 - P)       -- N_+
def P_01 (P X : B) : B := (1 - P) * X * P       -- N_-
def P_00 (P X : B) : B := (1 - P) * X * (1 - P)

-- The derived operators:
def Phi (P X : B) : B := P_10 P X + P_01 P X
def J   (P X : B) : B := P_10 P X - P_01 P X
def V   (P X : B) : B := P_10 P X * P_01 P X + P_01 P X * P_10 P X

lemma P_idem (hP : P * P = P) (Y : B) : P * (P * Y) = P * Y := by
  rw [← mul_assoc, hP]

/--
**Theorem: Exact Ring Identities of the Peirce Decomposition**
Holds for ANY idempotent P and ANY element X in ANY ring B:
1. N_+ and N_- are strictly square-zero (N_+² = 0, N_-² = 0).
2. Φ and J anticommute ({Φ, J} = 0).
3. Φ² = V and J² = -V (so Φ² - J² = 2V and Φ² + J² = 0).
4. The double commutator -[Φ, [Φ, J]] simplifies identically to -4 * V * J.
5. ad_P³(X) = ad_P(X) (Tripotency of the derivation ad_P).
6. ad_P(X) = J and ad_P²(X) = Φ.
-/
theorem peirce_decomposition_ring_identities (hP : P * P = P) :
    -- 1. Nilpotency
    P_10 P X * P_10 P X = 0 ∧
    P_01 P X * P_01 P X = 0 ∧
    -- 2. Anticommutation
    anticomm (Phi P X) (J P X) = 0 ∧
    -- 3. Squares and metric
    Phi P X * Phi P X = V P X ∧
    J P X * J P X = - V P X ∧
    Phi P X * Phi P X - J P X * J P X = V P X + V P X ∧
    -- 4. Double commutator identity (-4 * V * J)
    - comm (Phi P X) (comm (Phi P X) (J P X)) = - (V P X + V P X + V P X + V P X) * J P X ∧
    -- 5. Tripotency of ad_P
    comm P (comm P (comm P X)) = comm P X ∧
    -- 6. Identification of ad_P and ad_P² with J and Φ
    comm P X = J P X ∧
    comm P (comm P X) = Phi P X := by
  -- Expand all definitions into raw ring multiplication
  unfold P_10 P_01 Phi J V comm anticomm
  simp only [sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
             add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
             mul_assoc, hP, P_idem P hP]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> abel
```

## Turn 0020, fence 001 — user; language `lean`

```lean
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

/-!
# Inductive Colimit of the Dyadic Matrix Tensor Tower
Formalization of the direct system of 2ⁿ × 2ⁿ matrix rings and their colimit.
-/

variable (R : Type*) [CommRing R]

-- Dimension at level n is 2ⁿ
def dim2 (n : ℕ) : ℕ := 2^n

-- Level n algebra is Mat_{2ⁿ}(R)
abbrev TowerAlgebra (n : ℕ) := Matrix (Fin (dim2 n)) (Fin (dim2 n)) R

namespace TensorTower

/-- Canonical bijection Fin (2ⁿ) ⊕ Fin (2ⁿ) ≃ Fin (2ⁿ⁺¹) -/
def finSplit (n : ℕ) : Fin (dim2 n) ⊕ Fin (dim2 n) ≃ Fin (dim2 (n + 1)) :=
  have h : dim2 n + dim2 n = dim2 (n + 1) := by
    dsimp [dim2]
    ring
  (finSumFinEquiv.trans (Fin.castEquiv h))

/--
The transition homomorphism ιₙ : Mat_{2ⁿ}(R) → Mat_{2ⁿ⁺¹}(R).
Maps X to X ⊗ I₂ = [[X, 0], [0, X]].
-/
def embed (n : ℕ) (X : TowerAlgebra R n) : TowerAlgebra R (n + 1) :=
  Matrix.reindex (finSplit n).symm (finSplit n).symm
    (Matrix.fromBlocks X 0 0 X)

lemma embed_add (n : ℕ) (X Y : TowerAlgebra R n) :
    embed R n (X + Y) = embed R n X + embed R n Y := by
  dsimp [embed]
  rw [Matrix.fromBlocks_add]
  simp only [add_zero, zero_add]
  rfl

lemma embed_mul (n : ℕ) (X Y : TowerAlgebra R n) :
    embed R n (X * Y) = embed R n X * embed R n Y := by
  dsimp [embed]
  rw [← Matrix.submatrix_mul_equiv]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

lemma embed_one (n : ℕ) :
    embed R n 1 = 1 := by
  dsimp [embed]
  have h : (Matrix.fromBlocks (1 : TowerAlgebra R n) 0 0 1) = 1 := by
    ext (i|i) (j|j) <;> rfl
  rw [h]
  ext i j
  dsimp [Matrix.submatrix]
  by_cases h_eq : (finSplit n).symm i = (finSplit n).symm j
  · have h_ij : i = j := (finSplit n).symm.injective h_eq
    subst h_ij
    simp [Matrix.one_apply_eq]
  · have h_ij : i ≠ j := fun h => h_eq (congrArg _ h)
    simp [Matrix.one_apply_ne h_eq, Matrix.one_apply_ne h_ij]

/-- Transition map along arbitrary steps m ≤ n -/
def embedLe (R : Type*) [CommRing R] : (m n : ℕ) → m ≤ n → TowerAlgebra R m → TowerAlgebra R n
  | m, 0, h => fun X => by
      have : m = 0 := Nat.eq_zero_of_nonpos_iff.mpr h
      subst this
      exact X
  | m, n + 1, h => fun X =>
      if h_mn : m = n + 1 then
        by subst h_mn; exact X
      else
        have h_le : m ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h h_mn)
        embed R n (embedLe R m n h_le X)

-- ============================================================================
-- The Inductive Colimit Construction (Disjoint Union modulo Direct Equivalence)
-- ============================================================================

/-- Disjoint union of all matrix levels -/
structure StageElement where
  level : ℕ
  val   : TowerAlgebra R level

/-- Two elements are equivalent if they become equal at some higher stage k ≥ m, n -/
def ColimitRel (x y : StageElement R) : Prop :=
  ∃ (k : ℕ) (hxk : x.level ≤ k) (hyk : y.level ≤ k),
    embedLe R x.level k hxk x.val = embedLe R y.level k hyk y.val

/-- Equivalence relation on the union -/
lemma colimitRel_refl (x : StageElement R) : ColimitRel R x x :=
  ⟨x.level, le_refl x.level, le_refl x.level, rfl⟩

/-- The Carrier of the Inductive Colimit -/
def ColimitAlgebra := Quot (ColimitRel R)

namespace ColimitAlgebra

def of {n : ℕ} (X : TowerAlgebra R n) : ColimitAlgebra R :=
  Quot.mk (ColimitRel R) ⟨n, X⟩

/-- Addition is well-defined in the colimit -/
def add : ColimitAlgebra R → ColimitAlgebra R → ColimitAlgebra R :=
  Quot.lift₂
    (fun x y =>
      let k := max x.level y.level
      let x_lift := embedLe R x.level k (le_max_left x.level y.level) x.val
      let y_lift := embedLe R y.level k (le_max_right x.level y.level) y.val
      of R (x_lift + y_lift))
    (by
      -- Standard proof that lift to maximum level respects the directed system
      sorry)

/-- Multiplication is well-defined in the colimit -/
def mul : ColimitAlgebra R → ColimitAlgebra R → ColimitAlgebra R :=
  Quot.lift₂
    (fun x y =>
      let k := max x.level y.level
      let x_lift := embedLe R x.level k (le_max_left x.level y.level) x.val
      let y_lift := embedLe R y.level k (le_max_right x.level y.level) y.val
      of R (x_lift * y_lift))
    (by
      -- Respects direct system by embed_mul
      sorry)

instance : Add (ColimitAlgebra R) := ⟨add R⟩
instance : Mul (ColimitAlgebra R) := ⟨mul R⟩
instance : Zero (ColimitAlgebra R) := ⟨of R (0 : TowerAlgebra R 0)⟩
instance : One (ColimitAlgebra R) := ⟨of R (1 : TowerAlgebra R 0)⟩

/--
**Theorem: The Inductive Colimit is an Associative Ring**
The infinite tensor tower ⨂_{k=1}^∞ Mat₂(R) possesses a rigorous
associative ring structure inherited from the finite levels.
-/
instance : Ring (ColimitAlgebra R) where
  add := add R
  mul := mul R
  zero := 0
  one := 1
  add_assoc := by sorry
  zero_add := by sorry
  add_zero := by sorry
  add_comm := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  neg := sorry
  sub := sorry
  sub_eq_add_neg := by sorry
  zsmul := sorry
  nsmul := sorry
  add_left_neg := by sorry

end ColimitAlgebra

end TensorTower
```

## Turn 0032, fence 001 — user; language `lean`

```lean
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel

/-!
# Quantum Information Geometry on a Noncommutative Star-Ring
Manifest positivity, self-adjointness, and Fubini-Study / BKM operator structures
defined intrinsically on an associative `StarRing B` without pre-existing spacetime.
-/

namespace NoncommutativeInfoGeometry

variable {B : Type*} [Ring B] [StarRing B]

def comm (x y : B) : B := x * y - y * x
def anticomm (x y : B) : B := x * y + y * x

-- The four Peirce blocks of an element X with respect to an idempotent P:
def P_11 (P X : B) : B := P * X * P
def P_10 (P X : B) : B := P * X * (1 - P)       -- N_+
def P_01 (P X : B) : B := (1 - P) * X * P       -- N_-
def P_00 (P X : B) : B := (1 - P) * X * (1 - P)

-- The derived geometric operators:
def Phi (P X : B) : B := P_10 P X + P_01 P X   -- Symmetric / Real Bridge
def J   (P X : B) : B := P_10 P X - P_01 P X   -- Skew / Phase Current
def V   (P X : B) : B := P_10 P X * P_01 P X + P_01 P X * P_10 P X -- Fubini-Study / Metric Operator
def Sigma (P X : B) : B := P_10 P X * P_01 P X - P_01 P X * P_10 P X -- Berry Curvature / Dipole

-- Quantum Geometric Tensor Chiral Blocks:
def Q_plus  (P X : B) : B := P_10 P X * P_01 P X  -- N_+ * N_-
def Q_minus (P X : B) : B := P_01 P X * P_10 P X  -- N_- * N_+

lemma P_idem {P : B} (hP : P * P = P) (Y : B) : P * (P * Y) = P * Y := by
  rw [← mul_assoc, hP]

/--
**Theorem 1: Adjoint Relations on the Peirce Subspaces**
When P is a self-adjoint projection (P* = P) and X is self-adjoint (X* = X):
1. (N_+)* = N_- and (N_-)* = N_+.
2. Phi is self-adjoint (Phi* = Phi).
3. J is skew-adjoint (J* = -J).
4. The Fubini-Study metric operator V is self-adjoint (V* = V).
5. The Berry curvature operator Sigma is self-adjoint (Sigma* = Sigma).
-/
theorem peirce_star_relations {P X : B}
    (hP : P * P = P) (hP_star : star P = P) (hX_star : star X = X) :
    star (P_10 P X) = P_01 P X ∧
    star (P_01 P X) = P_10 P X ∧
    star (Phi P X) = Phi P X ∧
    star (J P X) = - J P X ∧
    star (V P X) = V P X ∧
    star (Sigma P X) = Sigma P X := by
  have h_one_sub_P : star (1 - P) = 1 - P := by
    rw [star_sub, star_one, hP_star]
  have hN_plus : star (P_10 P X) = P_01 P X := by
    unfold P_10 P_01
    rw [star_mul, star_mul, h_one_sub_P, hX_star, hP_star]
    rw [mul_assoc]
  have hN_minus : star (P_01 P X) = P_10 P X := by
    unfold P_10 P_01
    rw [star_mul, star_mul, hP_star, hX_star, h_one_sub_P]
    rw [mul_assoc]
  have hPhi : star (Phi P X) = Phi P X := by
    unfold Phi
    rw [star_add, hN_plus, hN_minus, add_comm]
  have hJ : star (J P X) = - J P X := by
    unfold J
    rw [star_sub, hN_plus, hN_minus]
    abel
  have hV : star (V P X) = V P X := by
    unfold V
    rw [star_add, star_mul, star_mul, hN_plus, hN_minus, add_comm]
  have hSigma : star (Sigma P X) = Sigma P X := by
    unfold Sigma
    rw [star_sub, star_mul, star_mul, hN_plus, hN_minus]
  exact ⟨hN_plus, hN_minus, hPhi, hJ, hV, hSigma⟩

/--
**Theorem 2: Manifest Gramian Positivity Structure of V**
When P* = P and X* = X, the metric operator V is literally the sum of two Gramian operators:
  V = N_+ (N_+)* + (N_+)* N_+ = Q_+ + Q_-
where Q_+ and Q_- are mutually orthogonal positive operators.
-/
theorem metric_is_sum_of_gramians {P X : B}
    (hP : P * P = P) (hP_star : star P = P) (hX_star : star X = X) :
    let N_plus := P_10 P X
    V P X = N_plus * star N_plus + star N_plus * N_plus ∧
    Q_plus P X = N_plus * star N_plus ∧
    Q_minus P X = star N_plus * N_plus ∧
    star (Q_plus P X) = Q_plus P X ∧
    star (Q_minus P X) = Q_minus P X ∧
    Q_plus P X * Q_minus P X = 0 ∧
    Q_minus P X * Q_plus P X = 0 := by
  intro N_plus
  rcases peirce_star_relations hP hP_star hX_star with ⟨hN_plus, hN_minus, -, -, -, -⟩
  have hV_gram : V P X = N_plus * star N_plus + star N_plus * N_plus := by
    unfold V N_plus
    rw [hN_plus]
  have hQp : Q_plus P X = N_plus * star N_plus := by
    unfold Q_plus N_plus
    rw [hN_plus]
  have hQm : Q_minus P X = star N_plus * N_plus := by
    unfold Q_minus N_plus
    rw [hN_plus]
  have hQp_star : star (Q_plus P X) = Q_plus P X := by
    rw [hQp, star_mul, star_star]
  have hQm_star : star (Q_minus P X) = Q_minus P X := by
    rw [hQm, star_mul, star_star]
  have hOrth1 : Q_plus P X * Q_minus P X = 0 := by
    unfold Q_plus Q_minus P_10 P_01
    calc (P * X * (1 - P) * ((1 - P) * X * P)) * ((1 - P) * X * P * (P * X * (1 - P)))
      _ = (P * X * (1 - P) * ((1 - P) * X * P)) * (1 - P) * X * (P * P) * X * (1 - P) := by
          simp only [mul_assoc]
      _ = (P * X * (1 - P) * ((1 - P) * X * P)) * (1 - P) * X * P * X * (1 - P) := by
          rw [hP]
      _ = (P * X * (1 - P) * ((1 - P) * X * P * (1 - P))) * X * P * X * (1 - P) := by
          simp only [mul_assoc]
      _ = 0 := by
          have h_annihilate : P * (1 - P) = 0 := by
            calc P * (1 - P) = P * 1 - P * P := by rw [mul_sub]
              _ = P - P := by rw [mul_one, hP]
              _ = 0 := sub_self P
          calc (P * X * (1 - P) * ((1 - P) * X * P * (1 - P))) * X * P * X * (1 - P)
            _ = (P * X * (1 - P) * ((1 - P) * X * (P * (1 - P)))) * X * P * X * (1 - P) := by
                simp only [mul_assoc]
            _ = 0 := by rw [h_annihilate, mul_zero, mul_zero, mul_zero, zero_mul]
  have hOrth2 : Q_minus P X * Q_plus P X = 0 := by
    unfold Q_plus Q_minus P_10 P_01
    have h_annihilate : (1 - P) * P = 0 := by
      calc (1 - P) * P = 1 * P - P * P := by rw [sub_mul]
        _ = P - P := by rw [one_mul, hP]
        _ = 0 := sub_self P
    calc ((1 - P) * X * P * (P * X * (1 - P))) * (P * X * (1 - P) * ((1 - P) * X * P))
      _ = ((1 - P) * X * P * (P * X * (1 - P))) * P * X * (1 - P) * ((1 - P) * X * P) := by
          simp only [mul_assoc]
      _ = ((1 - P) * X * P * (P * X * ((1 - P) * P))) * X * (1 - P) * ((1 - P) * X * P) := by
          simp only [mul_assoc]
      _ = 0 := by rw [h_annihilate, mul_zero, mul_zero, mul_zero, zero_mul]
  exact ⟨hV_gram, hQp, hQm, hQp_star, hQm_star, hOrth1, hOrth2⟩

/--
**Theorem 3: Exact Fubini-Study Chordal Distance on the Projector Manifold**
The tangent displacement to the projector manifold is delta P = [P, [P, X]] = Phi.
The squared chordal distance on the Grassmannian between the orthogonal sheets is:
  (delta P)^2 = Phi^2 = V = N_+ (N_+)* + (N_+)* N_+
matching the Fubini-Study metric tensor exactly.
-/
theorem fubini_study_chordal_metric {P X : B}
    (hP : P * P = P) (hP_star : star P = P) (hX_star : star X = X) :
    let delta_P := Phi P X
    delta_P * star delta_P = V P X ∧
    star delta_P * delta_P = V P X ∧
    delta_P * delta_P = V P X := by
  intro delta_P
  rcases peirce_star_relations hP hP_star hX_star with ⟨-, -, hPhi, -, -, -⟩
  have h_sq : delta_P * delta_P = V P X := by
    unfold delta_P Phi V P_10 P_01
    simp only [add_mul, mul_add, mul_assoc]
    have h1 : P * (1 - P) = 0 := by
      calc P * (1 - P) = P * 1 - P * P := by rw [mul_sub]
        _ = P - P := by rw [mul_one, hP]
        _ = 0 := sub_self P
    have h2 : (1 - P) * P = 0 := by
      calc (1 - P) * P = 1 * P - P * P := by rw [sub_mul]
        _ = P - P := by rw [one_mul, hP]
        _ = 0 := sub_self P
    have h_P10_sq : P * X * (1 - P) * (P * X * (1 - P)) = 0 := by
      calc P * X * (1 - P) * (P * X * (1 - P))
        _ = P * X * ((1 - P) * P) * X * (1 - P) := by simp only [mul_assoc]
        _ = 0 := by rw [h2, mul_zero, zero_mul, zero_mul]
    have h_P01_sq : (1 - P) * X * P * ((1 - P) * X * P) = 0 := by
      calc (1 - P) * X * P * ((1 - P) * X * P)
        _ = (1 - P) * X * (P * (1 - P)) * X * P := by simp only [mul_assoc]
        _ = 0 := by rw [h1, mul_zero, zero_mul, zero_mul]
    rw [h_P10_sq, h_P01_sq, zero_add, add_zero]
  have h_star_left : star delta_P * delta_P = V P X := by
    rw [hPhi, h_sq]
  have h_star_right : delta_P * star delta_P = V P X := by
    rw [hPhi, h_sq]
  exact ⟨h_star_right, h_star_left, h_sq⟩

end NoncommutativeInfoGeometry
```

## Turn 0035, fence 001 — model; language `lean`

```lean
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel

/-!
# Nilpotent-First Geometry: Reconstructing Projectors from Square-Zero Operators
A coordinate-free proof that projectors, orthogonality, and the Dirac metric
precipitate out of a single nilpotent element N and its star-adjoint.
-/

namespace NilpotentFirst

variable {B : Type*} [Ring B] [StarRing B]

def comm (x y : B) : B := x * y - y * x
def anticomm (x y : B) : B := x * y + y * x

/--
**Definition:** A Regular Nilpotent of order 2.
We assume NO projectors, NO preexisting units, and NO background coordinates.
We assume only an element N such that:
1. N is square-zero (N² = 0).
2. N is von Neumann regular with its adjoint (N * N⋆ * N = N).
-/
structure RegularNilpotent (N : B) : Prop where
  nilpot : N * N = 0
  regul  : N * star N * N = N

variable {N : B} (hN : RegularNilpotent N)

-- Reconstructed objects:
def P (N : B) : B := N * star N
def Q (N : B) : B := star N * N
def Phi (N : B) : B := N + star N
def J (N : B) : B := N - star N
def CarrierUnit (N : B) : B := P N + Q N

/--
**Theorem 1: Emergence of the Projector Sheet P**
P = N * N⋆ is automatically an idempotent (P² = P) and self-adjoint (P⋆ = P).
-/
theorem P_is_orthogonal_projector :
    P N * P N = P N ∧ star (P N) = P N := by
  have h_idem : P N * P N = P N := by
    unfold P
    calc N * star N * (N * star N)
      _ = (N * star N * N) * star N := by simp only [mul_assoc]
      _ = N * star N := by rw [hN.regul]
  have h_selfadj : star (P N) = P N := by
    unfold P
    rw [star_mul, star_star]
  exact ⟨h_idem, h_selfadj⟩

/--
**Theorem 2: Emergence of the Complementary Sheet Q**
Q = N⋆ * N is also an idempotent (Q² = Q) and self-adjoint (Q⋆ = Q).
-/
theorem Q_is_orthogonal_projector :
    Q N * Q N = Q N ∧ star (Q N) = Q N := by
  have h_star_reg : star N * N * star N = star N := by
    have h := congrArg star hN.regul
    rw [star_mul, star_mul, star_star, star_star] at h
    exact h
  have h_idem : Q N * Q N = Q N := by
    unfold Q
    calc star N * N * (star N * N)
      _ = (star N * N * star N) * N := by simp only [mul_assoc]
      _ = star N * N := by rw [h_star_reg]
  have h_selfadj : star (Q N) = Q N := by
    unfold Q
    rw [star_mul, star_star]
  exact ⟨h_idem, h_selfadj⟩

/--
**Theorem 3: Mutual Annihilation / Disjointness of the Sheets**
The sheets P and Q are strictly orthogonal (P * Q = 0 and Q * P = 0)
purely because N is square-zero.
-/
theorem sheets_are_mutually_orthogonal :
    P N * Q N = 0 ∧ Q N * P N = 0 := by
  have h_nil_star : star N * star N = 0 := by
    have h := congrArg star hN.nilpot
    rw [star_mul, star_zero] at h
    exact h
  have hPQ : P N * Q N = 0 := by
    unfold P Q
    calc N * star N * (star N * N)
      _ = N * (star N * star N) * N := by simp only [mul_assoc]
      _ = N * 0 * N := by rw [h_nil_star]
      _ = 0 := by rw [mul_zero, zero_mul]
  have hQP : Q N * P N = 0 := by
    unfold P Q
    calc star N * N * (N * star N)
      _ = star N * (N * N) * star N := by simp only [mul_assoc]
      _ = star N * 0 * star N := by rw [hN.nilpot]
      _ = 0 := by rw [mul_zero, zero_mul]
  exact ⟨hPQ, hQP⟩

/--
**Theorem 4: Dynamic Ladder Relations**
The nilpotent N is a ladder operator with respect to its own generated projector P:
  [P, N] = +N
  [P, N⋆] = -N⋆
-/
theorem nilpotent_is_own_ladder :
    comm (P N) N = N ∧ comm (P N) (star N) = - star N := by
  have h_comm_pos : comm (P N) N = N := by
    unfold comm P
    have h_nil_right : N * (star N * N) * N = 0 := by
      calc N * (star N * N) * N
        _ = N * star N * (N * N) := by simp only [mul_assoc]
        _ = N * star N * 0 := by rw [hN.nilpot]
        _ = 0 := mul_zero (N * star N)
    calc N * star N * N - N * (N * star N)
      _ = N - (N * N) * star N := by rw [hN.regul, mul_assoc]
      _ = N - 0 * star N := by rw [hN.nilpot]
      _ = N - 0 := by rw [zero_mul]
      _ = N := sub_zero N
  have h_comm_neg : comm (P N) (star N) = - star N := by
    unfold comm P
    have h_star_reg : star N * N * star N = star N := by
      have h := congrArg star hN.regul
      rw [star_mul, star_mul, star_star, star_star] at h
      exact h
    have h_star_nil : star N * star N = 0 := by
      have h := congrArg star hN.nilpot
      rw [star_mul, star_zero] at h
      exact h
    calc N * star N * star N - star N * (N * star N)
      _ = N * (star N * star N) - (star N * N * star N) := by simp only [mul_assoc]
      _ = N * 0 - star N := by rw [h_star_nil, h_star_reg]
      _ = 0 - star N := by rw [mul_zero]
      _ = - star N := zero_sub (star N)
  exact ⟨h_comm_pos, h_comm_neg⟩

/--
**Theorem 5: The Emergence of the Dirac Metric**
The symmetric bridge Phi = N + N⋆ squares exactly to the carrier identity:
  Phi² = P + Q = 1_carrier
and the skew bridge J = N - N⋆ squares to:
  J² = - (P + Q) = - 1_carrier
-/
theorem dirac_metric_identity :
    Phi N * Phi N = CarrierUnit N ∧
    J N * J N = - CarrierUnit N ∧
    anticomm (Phi N) (J N) = 0 := by
  have h_phi_sq : Phi N * Phi N = CarrierUnit N := by
    unfold Phi CarrierUnit P Q
    have h_nil_star : star N * star N = 0 := by
      have h := congrArg star hN.nilpot
      rw [star_mul, star_zero] at h
      exact h
    calc (N + star N) * (N + star N)
      _ = N * N + N * star N + star N * N + star N * star N := by
          simp only [add_mul, mul_add, add_assoc]
      _ = 0 + N * star N + star N * N + 0 := by rw [hN.nilpot, h_nil_star]
      _ = N * star N + star N * N := by abel
  have h_j_sq : J N * J N = - CarrierUnit N := by
    unfold J CarrierUnit P Q
    have h_nil_star : star N * star N = 0 := by
      have h := congrArg star hN.nilpot
      rw [star_mul, star_zero] at h
      exact h
    calc (N - star N) * (N - star N)
      _ = N * N - N * star N - star N * N + star N * star N := by
          simp only [sub_mul, mul_sub, add_sub_assoc]
          abel
      _ = 0 - N * star N - star N * N + 0 := by rw [hN.nilpot, h_nil_star]
      _ = - (N * star N + star N * N) := by abel
  have h_anticomm : anticomm (Phi N) (J N) = 0 := by
    unfold anticomm Phi J
    have h_nil_star : star N * star N = 0 := by
      have h := congrArg star hN.nilpot
      rw [star_mul, star_zero] at h
      exact h
    calc (N + star N) * (N - star N) + (N - star N) * (N + star N)
      _ = (N * N - N * star N + star N * N - star N * star N) +
          (N * N + N * star N - star N * N - star N * star N) := by
          simp only [add_mul, mul_add, sub_mul, mul_sub, add_sub_assoc]
          abel
      _ = (0 - N * star N + star N * N - 0) +
          (0 + N * star N - star N * N - 0) := by rw [hN.nilpot, h_nil_star]
      _ = 0 := by abel
  exact ⟨h_phi_sq, h_j_sq, h_anticomm⟩

end NilpotentFirst
```

## Turn 0047, fence 002 — model; language `lean`

```lean
#print axioms CramerRaoOnsagerCommutatorUncertainty.cramerRao_commutator_uncertainty_bound
#print axioms CoagulatedArchetypeSynthesis.master_structural_synthesis
```

## Turn 0055, fence 001 — user; language `lean`

```lean
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

/-!
# Archetype XVII: Para-Kähler Information Geometry, Twistor SUSY Superalgebra,
# Élie Cartan Gravity (Torsion & Curvature), and Higher-Grade Uncertainty Closure
Universal symbolic verification over any non-commutative associative ring `[Ring R]`:
1. `para_kaehler_uncertainty_information_geometry`:
   Proves the Robertson–Schrödinger splitting `2 N_+ N_- = V + Σ` into the Fisher–Rao
   information metric `V = {N_+, N_-}` and the uncertainty 2-form `Σ = [N_+, N_-]`,
   locked by the para-Kähler identity `Σ = S_P * V` and `V = S_P * Σ`.
2. `susy_supergrassmannian_poincare_closure`:
   Proves that the nilpotent supercharges `Q_+ = N_+`, `Q_- = N_-` (`Q_±² = 0`) generate
   the emergent spacetime translation/metric `V = {Q_+, Q_-}` which closes centrally (`[V, Q_±] = 0`).
3. `elie_cartan_gravity_torsion_and_curvature_from_uncertainty`:
   Bundles the Lorentz spin connection `Ω_i ∈ g_0` and tetrad `Φ_i ∈ g_{±1}` into the
   Cartan connection `A_i = Ω_i + Φ_i`, proving that the curvature `[A_1, A_2]` splits
   by `S_P`-parity into the Even Riemann–Cartan Curvature `[Ω_1, Ω_2] + [Φ_1, Φ_2]`
   (with `[Φ, J] = -2 Σ = -2 S_P V`) and Odd Élie Cartan Torsion `[Ω_1, Φ_2] - [Ω_2, Φ_1]`,
   satisfying the exact Bianchi–Cartan identity.
-/

universe u
variable {R : Type u} [Ring R]

namespace ParaKaehlerTwistorCartanSupergravity

/-- Binary Lie commutator `[A, B] = A * B - B * A`. -/
def comm (A B : R) : R := A * B - B * A

/-- Jordan / SUSY anticommutator `{A, B} = A * B + B * A`. -/
def anticomm (A B : R) : R := A * B + B * A

/-- Chiral para-complex involution `S_P = 2 P - 1 = P + P - 1` (`S_P² = +1`). -/
def paraJ (P : R) : R := P + P - 1

/-- Forward chiral supercharge / super-Grassmannian tangent `Q_+(P, X) = P X (1 - P)`. -/
def superQPlus (P X : R) : R := P * X * (1 - P)

/-- Backward chiral supercharge / dual twistor tangent `Q_-(P, X) = (1 - P) X P`. -/
def superQMinus (P X : R) : R := (1 - P) * X * P

/-- Symmetric real tetrad / solder form `Φ(P, X) = Q_+(P, X) + Q_-(P, X)`. -/
def tetradPhi (P X : R) : R := superQPlus P X + superQMinus P X

/-- Chiral dual real tetrad `J(P, X) = Q_+(P, X) - Q_-(P, X)`. -/
def tetradDualJ (P X : R) : R := superQPlus P X - superQMinus P X

/-- Emergent Fisher–Rao / Poincaré spacetime metric `V(P, X) = {Q_+, Q_-}`. -/
def fisherMetricV (P X : R) : R := anticomm (superQPlus P X) (superQMinus P X)

/-- Symplectic Uncertainty Curvature 2-form `Σ(P, X) = [Q_+, Q_-]`. -/
def uncertaintySigma (P X : R) : R := comm (superQPlus P X) (superQMinus P X)

/-- Even grade-0 Lorentz spin connection `Ω(P, W) = P W P + (1 - P) W (1 - P)`. -/
def spinConn (P W : R) : R := P * W * P + (1 - P) * W * (1 - P)

/-- Unified Élie Cartan connection `𝓐(P, W, X) = Ω(P, W) + Φ(P, X)`. -/
def cartanConn (P W X : R) : R := spinConn P W + tetradPhi P X

/-- Riemann–Cartan Curvature 2-form `𝓡(Ω₁, Ω₂, Φ₁, Φ₂) = [Ω₁, Ω₂] + [Φ₁, Φ₂] ∈ g_0`. -/
def riemannCartanCurv (P W₁ X₁ W₂ X₂ : R) : R :=
  comm (spinConn P W₁) (spinConn P W₂) + comm (tetradPhi P X₁) (tetradPhi P X₂)

/-- Élie Cartan Torsion 2-form `𝓣(Ω₁, Ω₂, Φ₁, Φ₂) = [Ω₁, Φ₂] - [Ω₂, Φ₁] ∈ g_{±1}`. -/
def cartanTorsion (P W₁ X₁ W₂ X₂ : R) : R :=
  comm (spinConn P W₁) (tetradPhi P X₂) - comm (spinConn P W₂) (tetradPhi P X₁)

/--
**Theorem XVII.1 (Para-Kähler Information Geometry & Uncertainty Decomposition):**
Over any non-commutative ring `R` with idempotent `P² = P`:
1. **Para-Complex Chiral Involution:** `S_P * S_P = 1`, `S_P * Q_+ = Q_+`, `S_P * Q_- = -Q_-`.
2. **Robertson–Schrödinger Uncertainty Split:**
   `2 (Q_+ * Q_-) = V + Σ` and `2 (Q_- * Q_+) = V - Σ`, where `V = {Q_+, Q_-}` is the
   symmetric information metric and `Σ = [Q_+, Q_-]` is the antisymmetric uncertainty curvature.
3. **Para-Kähler Compatibility (`ω = g(S_P ·, ·)`):**
   `Σ = S_P * V = V * S_P` and `V = S_P * Σ = Σ * S_P`.
-/
theorem para_kaehler_uncertainty_information_geometry
    (P X : R) (hP : P * P = P) :
    let S  := paraJ P
    let Qp := superQPlus P X
    let Qm := superQMinus P X
    let V  := fisherMetricV P X
    let Σ  := uncertaintySigma P X
    -- 1. Para-complex real involution `S_P² = +1` and chiral eigen-equations:
    S * S = 1 ∧
    S * Qp = Qp ∧
    S * Qm = - Qm ∧
    -- 2. Robertson-Schrödinger decomposition into Metric `V` + Uncertainty `Σ`:
    Qp * Qm + Qp * Qm = V + Σ ∧
    Qm * Qp + Qm * Qp = V - Σ ∧
    -- 3. Exact Para-Kähler locking between Metric `V` and Uncertainty `Σ`:
    S * V = Σ ∧
    V * S = Σ ∧
    S * Σ = V ∧
    Σ * S = V := by
  have hP_assoc : ∀ Y : R, P * (P * Y) = P * Y := by
    intro Y; rw [← mul_assoc, hP]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [paraJ, superQPlus, superQMinus, fisherMetricV, uncertaintySigma,
                anticomm, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, hP, hP_assoc,
               mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub]
    abel

/--
**Theorem XVII.2 (Super-Grassmannian SUSY Superalgebra & Emergent Poincaré Closure):**
1. **Nilpotent Fermionic Supercharges:** `Q_+² = 0` and `Q_-² = 0`.
2. **Emergent Spacetime Translation Generator:** `{Q_+, Q_-} = V = Φ² = -J²`.
3. **Central Closure of the Poincaré-SUSY Superalgebra:**
   `[V, Q_+] = 0` and `[V, Q_-] = 0` (the emergent translation generator `V` commutes
   with both nilpotent supercharges without requiring `R` to be commutative!).
-/
theorem susy_supergrassmannian_poincare_closure
    (P X : R) (hP : P * P = P) :
    let Qp := superQPlus P X
    let Qm := superQMinus P X
    let Φ  := tetradPhi P X
    let J  := tetradDualJ P X
    let V  := fisherMetricV P X
    Qp * Qp = 0 ∧
    Qm * Qm = 0 ∧
    anticomm Qp Qm = V ∧
    Φ * Φ = V ∧
    J * J = - V ∧
    comm V Qp = 0 ∧
    comm V Qm = 0 := by
  have hP_assoc : ∀ Y : R, P * (P * Y) = P * Y := by
    intro Y; rw [← mul_assoc, hP]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [superQPlus, superQMinus, tetradPhi, tetradDualJ, fisherMetricV,
                anticomm, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, hP, hP_assoc,
               mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub]
    abel

/--
**Theorem XVII.3 (Élie Cartan Gravity: Torsion, Riemann–Cartan Curvature, and Uncertainty Creation):**
For any spin-connection seeds `W₁, W₂, W₃ : R` and frame/tetrad seeds `X₁, X₂, X : R`:
1. **Exact Cartan Curvature-Torsion Splitting:**
   The commutator of two unified Cartan connections `𝓐₁ = Ω₁ + Φ₁` and `𝓐₂ = Ω₂ + Φ₂`
   splits into the Even Riemann–Cartan Curvature `𝓡₁₂` and Odd Élie Cartan Torsion `𝓣₁₂`:
   `[𝓐₁, 𝓐₂] = 𝓡₁₂ + 𝓣₁₂`.
2. **Para-Kähler Grading of Curvature vs. Torsion:**
   - `𝓡₁₂` commutes with `S_P` (`[S_P, 𝓡₁₂] = 0`, even Lorentz grade `g_0`),
   - `𝓣₁₂` anticommutes with `S_P` (`{S_P, 𝓣₁₂} = 0`, odd translational grade `g_{±1}`).
3. **The Uncertainty Principle as the Creator of Curvature:**
   Even when the spin connection vanishes (`W = 0`), the non-commutativity of the chiral
   dual tetrads `Φ(P, X)` and `J(P, X)` creates the exact para-Kähler curvature:
   `[Φ(P, X), J(P, X)] = - (Σ + Σ) = - (S_P * V + S_P * V)`.
4. **Single-Operator Cartan Square:**
   `(Ω + Φ)² = (Ω² + V) + {Ω, Φ}` (Even Einstein–Cartan–MacDowell–Mansouri curvature `Ω² + V`
   plus Odd anticommutator torsion `{Ω, Φ}`).
5. **Exact Non-Abelian Bianchi–Cartan Jacobi Identity:**
   `[𝓐₁, [𝓐₂, 𝓐₃]] + [𝓐₂, [𝓐₃, 𝓐₁]] + [𝓐₃, [𝓐₁, 𝓐₂]] = 0`.
-/
theorem elie_cartan_gravity_torsion_and_curvature_from_uncertainty
    (P W₁ X₁ W₂ X₂ W₃ X₃ X : R) (hP : P * P = P) :
    let S   := paraJ P
    let 𝓐₁  := cartanConn P W₁ X₁
    let 𝓐₂  := cartanConn P W₂ X₂
    let 𝓐₃  := cartanConn P W₃ X₃
    let 𝓡₁₂ := riemannCartanCurv P W₁ X₁ W₂ X₂
    let 𝓣₁₂ := cartanTorsion P W₁ X₁ W₂ X₂
    let Ω   := spinConn P W₁
    let Φ   := tetradPhi P X
    let J   := tetradDualJ P X
    let V   := fisherMetricV P X
    let Σ   := uncertaintySigma P X
    -- 1. Unified Cartan curvature splits into Riemann–Cartan Curvature + Cartan Torsion:
    comm 𝓐₁ 𝓐₂ = 𝓡₁₂ + 𝓣₁₂ ∧
    -- 2. Para-Kähler parity separation (`[S_P, 𝓡₁₂] = 0` and `{S_P, 𝓣₁₂} = 0`):
    comm S 𝓡₁₂ = 0 ∧
    anticomm S 𝓣₁₂ = 0 ∧
    -- 3. Uncertainty commutator `[Φ, J]` directly creates the curvature `-2 Σ = -2 S_P V`:
    comm Φ J = - (Σ + Σ) ∧
    comm Φ J = - (S * V + S * V) ∧
    -- 4. Single Cartan operator square `(Ω + Φ)² = (Ω² + V) + {Ω, Φ}`:
    (Ω + Φ) * (Ω + Φ) = (Ω * Ω + V) + anticomm Ω Φ ∧
    -- 5. Exact Bianchi–Cartan Differential Identity:
    comm 𝓐₁ (comm 𝓐₂ 𝓐₃) + comm 𝓐₂ (comm 𝓐₃ 𝓐₁) + comm 𝓐₃ (comm 𝓐₁ 𝓐₂) = 0 := by
  have hP_assoc : ∀ Y : R, P * (P * Y) = P * Y := by
    intro Y; rw [← mul_assoc, hP]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [paraJ, cartanConn, riemannCartanCurv, cartanTorsion,
                spinConn, tetradPhi, tetradDualJ, superQPlus, superQMinus,
                fisherMetricV, uncertaintySigma, comm, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, hP, hP_assoc,
               mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub]
    abel

end ParaKaehlerTwistorCartanSupergravity

```
