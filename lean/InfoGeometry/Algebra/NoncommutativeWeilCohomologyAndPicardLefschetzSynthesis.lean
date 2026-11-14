/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis

/-!
# Noncommutative Graded Matrix Identities and Picard–Lefschetz-Type Symplectic Operators

This module proves four finite-stage matrix identity families over a possibly noncommutative
ring `A`. The grading is represented by `ClTower A 1 = M₂(A)`, and the iterated operators
live in `ClTower A n`. These names indicate algebraic analogies only; the results do not
construct a cohomology theory, arithmetic Frobenius, Weil conjecture, or geometric monodromy.
The dependency order is: `W₁` and `W₂` are independent matrix branches; `W₃` uses the same
matrix tower; `W₄` additionally imports the separately proved Hodge–parabolic tower.

```text
Ring A and M₂(A) ──► W₁
                 ├──► W₂
                 └──► W₃
Ring A + Hodge–parabolic tower owner ──► W₄
```
These are proof dependencies only. No arrow asserts a geometric realization or identifies
the matrix statements with a cohomology theory.

1. **Archetype $\mathcal{W}_1$: Graded Matrix Supertrace & Odd Anticommutator Cancellation**:
   Proves `lefschetzSuperTrace ((gradedFrobenius F_ev F_odd) ^ m) = F_ev ^ m - F_odd ^ m`,
   proves `lefschetzSuperTrace (anticomm D Ψ) = ⁅L_minus, ψ_plus⁆ + ⁅ψ_minus, L_plus⁆`, and
   shows vanishing under any tracial functional on `A`.
2. **Archetype $\mathcal{W}_2$: Conditional Quaternion Relations & Two-Level Matrix Realization**:
   Proves the complete quaternion relations for `(quatI, quatJ ι, quatK ι)` in `ClTower A 1`
   whenever `ι * ι = -1`, and constructs the 2-scale Brauer–Weyl quaternion triple in
   `ClTower A 2 = M₄(A)` over an arbitrary ring `A` without adjoining `√(-1)`.
3. **Archetype $\mathcal{W}_3$: Rotor Polynomial Obstruction & Iterated Cayley Identities**:
   Proves a matrix polynomial identity whose defect is exactly the entry commutator, a conditional
   symplectic-similitude implication, and trace and star-norm identities for a recursive Cayley
   operator. These do not assert arithmetic or spectral purity.
4. **Archetype $\mathcal{W}_4$: Hodge–Parabolic Symplectic Matrix Monodromy**:
   Proves that the canonical Hodge–Parabolic nilpotent generator `hpToCl (n + 1) (hodgeNilpotent n)`
   lies in `sp₂(A, ⋆)` for both the full `cupForm n` and `activeSymplecticForm n`, and that
   every winding `(hpToCl (n + 1) (hodgeMonodromy n)) ^ k` strictly preserves both symplectic forms.
-/

namespace InfoGeometry.Algebra.NoncommutativeWeilCohomologyAndPicardLefschetzSynthesis

open Matrix
open InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis

universe u

/-!
## Foundational Infrastructure
-/

section Matrix2Helpers

variable {A : Type u} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

def omegaOp : ClTower A 1 := mat2 0 (-1) 1 0

lemma omegaOp_sq : (omegaOp (A := A)) * omegaOp = -1 := by
  apply ext_fin2 <;> simp [omegaOp, mat2, Matrix.mul_apply, Fin.sum_univ_two]

end Matrix2Helpers

/-!
## Archetype $\mathcal{W}_1$: Graded Matrix Supertrace & Odd Anticommutator Cancellation
-/

section ArchetypeW1_GrothendieckLefschetzSupertrace

variable {A : Type u} [Ring A]

/-- The two-block matrix supertrace `Λ(M) = M 0 0 - M 1 1 ∈ A`. -/
def lefschetzSuperTrace (M : ClTower A 1) : A :=
  M 0 0 - M 1 1

lemma lefschetzSuperTrace_eq_superTrace (M : ClTower A 1) :
    lefschetzSuperTrace M = superTrace M := by
  dsimp [lefschetzSuperTrace, superTrace, towerTrace, chiralityOp, mat2]
  simp [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

/-- Graded Frobenius endomorphism `diag(F_ev, F_odd)` acting on `H^even ⊕ H^odd`. -/
def gradedFrobenius (F_ev F_odd : A) : ClTower A 1 :=
  mat2 F_ev 0 0 F_odd

theorem gradedFrobenius_pow (F_ev F_odd : A) (m : ℕ) :
    (gradedFrobenius F_ev F_odd) ^ m = mat2 (F_ev ^ m) 0 0 (F_odd ^ m) := by
  induction m with
  | zero =>
      apply ext_fin2 <;> simp [gradedFrobenius, mat2]
  | succ k ih =>
      rw [pow_succ, ih, pow_succ, pow_succ]
      apply ext_fin2 <;> simp [gradedFrobenius, mat2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Graded Matrix Power Formula & Odd Anticommutator Identity ($\mathcal{W}_1$)**:
1. For any `m : ℕ`, `lefschetzSuperTrace ((gradedFrobenius F_ev F_odd) ^ m) = F_ev ^ m - F_odd ^ m`,
2. For any odd differential `D = mat2 0 L_minus L_plus 0` and odd homotopy
   `Ψ = mat2 0 ψ_minus ψ_plus 0`, `lefschetzSuperTrace (anticomm D Ψ) = ⁅L_minus, ψ_plus⁆ + ⁅ψ_minus, L_plus⁆`. -/
theorem grothendieck_lefschetz_formula_and_coboundary_cancellation
    (F_ev F_odd L_plus L_minus ψ_plus ψ_minus : A) (m : ℕ) :
    let D : ClTower A 1 := mat2 0 L_minus L_plus 0
    let Ψ : ClTower A 1 := mat2 0 ψ_minus ψ_plus 0
    lefschetzSuperTrace ((gradedFrobenius F_ev F_odd) ^ m) = F_ev ^ m - F_odd ^ m ∧
    lefschetzSuperTrace (anticomm D Ψ) = ⁅L_minus, ψ_plus⁆ + ⁅ψ_minus, L_plus⁆ := by
  refine ⟨?_, ?_⟩
  · rw [gradedFrobenius_pow]; rfl
  · dsimp [lefschetzSuperTrace, anticomm]
    simp only [Ring.lie_def, mat2, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.of_apply, mul_zero, add_zero, zero_add]
    noncomm_ring

/-- **Cohomological Invariance under Tracial Functionals**:
Any tracial `ℤ`-linear map `τ : A →+ R` (`∀ x y, τ (x * y) = τ (y * x)`) annihilates
`lefschetzSuperTrace (anticomm D Ψ)`. -/
theorem tracial_lefschetzSuperTrace_odd_anticommutator {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (h_tr : ∀ x y : A, τ (x * y) = τ (y * x))
    (L_plus L_minus ψ_plus ψ_minus : A) :
    let D : ClTower A 1 := mat2 0 L_minus L_plus 0
    let Ψ : ClTower A 1 := mat2 0 ψ_minus ψ_plus 0
    τ (lefschetzSuperTrace (anticomm D Ψ)) = 0 := by
  have h := (grothendieck_lefschetz_formula_and_coboundary_cancellation
    (0 : A) 0 L_plus L_minus ψ_plus ψ_minus 0).2
  dsimp only at h ⊢
  rw [h, Ring.lie_def, Ring.lie_def, map_add, map_sub, map_sub,
      h_tr L_minus ψ_plus, h_tr ψ_minus L_plus, sub_self, sub_self, add_zero]

end ArchetypeW1_GrothendieckLefschetzSupertrace

/-!
## Archetype $\mathcal{W}_2$: Conditional Quaternion Relations & Two-Level Matrix Realization
-/

section ArchetypeW2_SupersingularQuaternionSplitting

variable {A : Type u} [Ring A]

def quatI : ClTower A 1 := mat2 0 (-1) 1 0
def quatJ (ι : A) : ClTower A 1 := mat2 ι 0 0 (-ι)
def quatK (ι : A) : ClTower A 1 := mat2 0 ι ι 0

/-- **Quaternion Relations in `M₂(A)` ($\mathcal{W}_2$)**:
Whenever `ι : A` satisfies `ι * ι = -1`, `(quatI, quatJ ι, quatK ι)` satisfy the exact
Hamilton quaternion relations in `ClTower A 1 = M₂(A)`. -/
theorem weil_supersingular_quaternion_splitting {ι : A} (hι : ι * ι = -1) :
    (quatI : ClTower A 1) * quatI = -1 ∧
    quatJ ι * quatJ ι = -1 ∧
    quatK ι * quatK ι = -1 ∧
    quatI * quatJ ι = quatK ι ∧
    quatJ ι * quatI = -quatK ι ∧
    ⁅(quatI : ClTower A 1), quatJ ι⁆ = 2 • quatK ι := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [quatI, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  · apply ext_fin2 <;> simp [quatJ, mat2, Matrix.mul_apply, Fin.sum_univ_two, hι]
  · apply ext_fin2 <;> simp [quatK, mat2, Matrix.mul_apply, Fin.sum_univ_two, hι]
  · apply ext_fin2 <;> simp [quatI, quatJ, quatK, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  · apply ext_fin2 <;> simp [quatI, quatJ, quatK, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Ring.lie_def]
    apply ext_fin2 <;>
      simp [quatI, quatJ, quatK, mat2, Matrix.mul_apply, Fin.sum_univ_two, two_smul]

/-- **2-Scale Brauer–Weyl Quaternion Realization in `ClTower A 2 = M₄(A)`**
(valid over ANY noncommutative ring `A` without adjoining `√(-1)`). -/
def brauerQ1 : ClTower A 2 := mat2 (0 : ClTower A 1) (-1) 1 0
def brauerQ2 : ClTower A 2 := mat2 (quatI (A := A)) 0 0 (-quatI)
def brauerQ3 : ClTower A 2 := mat2 0 (quatI (A := A)) quatI 0

theorem brauer_weyl_quaternion_realization :
    (brauerQ1 (A := A)) * brauerQ1 = -1 ∧
    (brauerQ2 (A := A)) * brauerQ2 = -1 ∧
    (brauerQ3 (A := A)) * brauerQ3 = -1 ∧
    (brauerQ1 (A := A)) * brauerQ2 = brauerQ3 ∧
    (brauerQ2 (A := A)) * (brauerQ1 (A := A)) = -(brauerQ3 (A := A)) ∧
    ⁅(brauerQ1 (A := A)), (brauerQ2 (A := A))⁆ = 2 • (brauerQ3 (A := A)) := by
  have hqi : (quatI (A := A)) * quatI = -1 := by
    apply ext_fin2 <;> simp [quatI, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [brauerQ1, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  · apply ext_fin2 <;> simp [brauerQ2, mat2, Matrix.mul_apply, Fin.sum_univ_two, hqi]
  · apply ext_fin2 <;> simp [brauerQ3, mat2, Matrix.mul_apply, Fin.sum_univ_two, hqi]
  · apply ext_fin2 <;> simp [brauerQ1, brauerQ2, brauerQ3, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  · apply ext_fin2 <;> simp [brauerQ1, brauerQ2, brauerQ3, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Ring.lie_def]
    apply ext_fin2 <;>
      simp [brauerQ1, brauerQ2, brauerQ3, mat2, Matrix.mul_apply, Fin.sum_univ_two, two_smul]

/-- Division-free quaternion Frobenius operator
`F = a • 1 + b • brauerQ1 + c • brauerQ2 + d • brauerQ3 ∈ ClTower A 2 = M₂(M₂(A))`. -/
def brauerFourSquareFrobenius (a b c d : ℕ) : ClTower A 2 :=
  a • (1 : ClTower A 2) + b • brauerQ1 + c • brauerQ2 + d • brauerQ3

/-- **Two-Scale Brauer–Weyl Four-Square Purity & Hasse–Weil Quadratic ($\mathcal{W}_2 \to \mathcal{W}_3$)**:
Over *any* `StarRing A` (without commutativity), `F = brauerFourSquareFrobenius a b c d` satisfies:
1. `star F * F = (a^2 + b^2 + c^2 + d^2) • 1`,
2. `F^2 - (2 * a) • F + (a^2 + b^2 + c^2 + d^2) • 1 = 0`. -/
theorem brauer_four_square_frobenius_purity_and_hasse_weil [StarRing A] (a b c d : ℕ) :
    let F := brauerFourSquareFrobenius (A := A) a b c d
    let q := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
    @Star.star _ (instStarRingClTower 2).toStar F * F = q • (1 : ClTower A 2) ∧
    F * F - (2 * a) • F + q • (1 : ClTower A 2) = 0 := by
  let _ : StarRing (ClTower A 1) := instStarRingClTower 1
  let _ : StarRing (ClTower A 2) := instStarRingClTower 2
  have h_quat := brauer_weyl_quaternion_realization (A := A)
  rcases h_quat with ⟨hq1, hq2, hq3, h12, h21, _⟩
  have hqi : (quatI (A := A)) * quatI = -1 := by
    apply ext_fin2 <;> simp [quatI, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  have h13 : (brauerQ1 (A := A)) * brauerQ3 = -brauerQ2 := by
    apply ext_fin2 <;> simp [brauerQ1, brauerQ2, brauerQ3, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  have h31 : (brauerQ3 (A := A)) * brauerQ1 = brauerQ2 := by
    apply ext_fin2 <;> simp [brauerQ1, brauerQ2, brauerQ3, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  have h23 : (brauerQ2 (A := A)) * brauerQ3 = brauerQ1 := by
    apply ext_fin2 <;> simp [brauerQ1, brauerQ2, brauerQ3, mat2, Matrix.mul_apply, Fin.sum_univ_two, hqi]
  have h32 : (brauerQ3 (A := A)) * brauerQ2 = -brauerQ1 := by
    apply ext_fin2 <;> simp [brauerQ1, brauerQ2, brauerQ3, mat2, Matrix.mul_apply, Fin.sum_univ_two, hqi]
  have hqi_star : star (quatI (A := A)) = -quatI := by
    apply ext_fin2 <;> simp [quatI, mat2]
  have hs1 : star (brauerQ1 (A := A)) = -brauerQ1 := by
    apply ext_fin2 <;> simp [brauerQ1, mat2]
  have hs2 : star (brauerQ2 (A := A)) = -brauerQ2 := by
    apply ext_fin2 <;> simp [brauerQ2, mat2, hqi_star]
  have hs3 : star (brauerQ3 (A := A)) = -brauerQ3 := by
    apply ext_fin2 <;> simp [brauerQ3, mat2, hqi_star]
  have hF_star :
      star (brauerFourSquareFrobenius (A := A) a b c d) =
        a • (1 : ClTower A 2) + -(b • brauerQ1) + -(c • brauerQ2) + -(d • brauerQ3) := by
    simp only [brauerFourSquareFrobenius, star_add, star_nsmul, star_one, hs1, hs2, hs3, smul_neg]
  refine ⟨?_, ?_⟩
  · rw [hF_star]
    dsimp only [brauerFourSquareFrobenius]
    simp only [add_mul, mul_add, neg_mul, neg_neg,
      smul_mul_assoc, mul_smul_comm, smul_add, smul_neg, smul_smul, one_mul, mul_one,
      hq1, hq2, hq3, h12, h21, h13, h31, h23, h32, sq, add_smul]
    try simp only [Nat.mul_comm b a, Nat.mul_comm c a, Nat.mul_comm d a,
      Nat.mul_comm c b, Nat.mul_comm d b, Nat.mul_comm d c]
    abel
  · dsimp only [brauerFourSquareFrobenius]
    simp only [sub_eq_add_neg, add_mul, mul_add,
      smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
      hq1, hq2, hq3, h12, h21, h13, h31, h23, h32, smul_neg, sq, two_mul, add_smul, smul_add]
    simp only [Nat.mul_comm b a, Nat.mul_comm c a, Nat.mul_comm d a,
      Nat.mul_comm c b, Nat.mul_comm d b, Nat.mul_comm d c]
    abel

/-- **Lagrange Four-Square Universal Frobenius Realization**:
For *every* `q : ℕ` (in particular every prime power `q = p^r`) and *every* `StarRing A`,
there exists a division-free operator `F ∈ ClTower A 2 = M₂(M₂(A))` and `a : ℕ` satisfying
`star F * F = q • 1` and `F^2 - (2 * a) • F + q • 1 = 0`. -/
theorem lagrange_arbitrary_q_frobenius_exists [StarRing A] (q : ℕ) :
    ∃ F : ClTower A 2, @Star.star _ (instStarRingClTower 2).toStar F * F = q • (1 : ClTower A 2) ∧
      ∃ a : ℕ, F * F - (2 * a) • F + q • (1 : ClTower A 2) = 0 := by
  rcases Nat.sum_four_squares q with ⟨a, b, c, d, hq⟩
  refine ⟨brauerFourSquareFrobenius a b c d, ?_, a, ?_⟩
  · simpa [hq] using (brauer_four_square_frobenius_purity_and_hasse_weil (A := A) a b c d).1
  · simpa [hq] using (brauer_four_square_frobenius_purity_and_hasse_weil (A := A) a b c d).2

end ArchetypeW2_SupersingularQuaternionSplitting

/-!
## Archetype $\mathcal{W}_3$: Rotor Polynomial Obstruction & Iterated Cayley Identities
-/

section ArchetypeW3_HasseWeilPoincareAndKunnethPurity

variable {A : Type u} [Ring A] [StarRing A]

/-- Rotor-shaped operator `mat2 a (-b) b a` in `ClTower A 1 = M₂(A)`. -/
def weilFrobenius (a b : A) : ClTower A 1 :=
  mat2 a (-b) b a

/-- Division-free Cayley operator `1 + omegaOp` in `ClTower A 1`. -/
def cayleyFrobenius : ClTower A 1 :=
  1 + omegaOp

/-- Algebraic duality operation `F ↦ -omegaOp * star F * omegaOp` in `ClTower A 1`. -/
def poincareDual (F : ClTower A 1) : ClTower A 1 :=
  -omegaOp * @Star.star _ (instStarRingClTower 1).toStar F * omegaOp

/-- **Poincaré Symplectic Similitude Theorem**:
If `star F * omegaOp * F = q • omegaOp`, then `poincareDual F * F = q • 1`. -/
theorem poincare_symplectic_similitude (F : ClTower A 1) (q : ℕ)
    (h_sim : @Star.star _ (instStarRingClTower 1).toStar F * omegaOp * F = q • omegaOp) :
    poincareDual F * F = q • (1 : ClTower A 1) := by
  let _ : StarRing (ClTower A 1) := instStarRingClTower 1
  calc poincareDual F * F
    _ = -omegaOp * (star F * omegaOp * F) := by dsimp [poincareDual]; noncomm_ring
    _ = -omegaOp * (q • omegaOp) := by rw [h_sim]
    _ = -(q • (omegaOp * omegaOp)) := by rw [mul_smul_comm, neg_mul, smul_neg]
    _ = -(q • (-1 : ClTower A 1)) := by rw [omegaOp_sq]
    _ = q • (1 : ClTower A 1) := by simp

/-- $n$-fold Kronecker–Cayley–Walsh Frobenius operator `𝒰_n ∈ ClTower A n`. -/
def cayleyTowerOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cayleyTowerOp n) (-cayleyTowerOp n) (cayleyTowerOp n) (cayleyTowerOp n)

/-- **Rotor Polynomial Defect & Iterated Cayley Identities ($\mathcal{W}_3$):
1. The rotor-shaped matrix polynomial has exact commutator defect `mat2 0 ⁅a, b⁆ (-⁅a, b⁆) 0`,
2. The fixed Cayley operator satisfies a quadratic identity and a symplectic similitude,
3. The recursive Cayley operator has the stated tower trace and star-norm identities.
These algebraic identities do not assert a geometric or spectral theorem. -/
theorem hasse_weil_poincare_and_kunneth_purity (a b : A) (n : ℕ) :
    let F_ab := weilFrobenius a b
    let F_2  := (cayleyFrobenius : ClTower A 1)
    F_ab * F_ab - mat2 (2 • a) 0 0 (2 • a) * F_ab +
      mat2 (a * a + b * b) 0 0 (a * a + b * b) = mat2 0 ⁅a, b⁆ (-⁅a, b⁆) 0 ∧
    F_2 * F_2 - 2 • F_2 + 2 • (1 : ClTower A 1) = 0 ∧
    @Star.star _ (instStarRingClTower 1).toStar F_2 * omegaOp * F_2 = 2 • (omegaOp : ClTower A 1) ∧
    towerTrace (cayleyTowerOp n : ClTower A n) = (2 ^ n) • (1 : A) ∧
    @Star.star _ (instStarRingClTower n).toStar (cayleyTowerOp n : ClTower A n) *
      cayleyTowerOp n = (2 ^ n) • (1 : ClTower A n) := by
  let _ : StarRing (ClTower A 1) := instStarRingClTower 1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ring.lie_def]
    apply ext_fin2 <;>
      simp [weilFrobenius, mat2, Matrix.mul_apply, Fin.sum_univ_two, two_smul] <;>
      noncomm_ring
  · apply ext_fin2 <;>
      simp [cayleyFrobenius, omegaOp, mat2, Matrix.mul_apply, Fin.sum_univ_two, two_smul]
  · have hs : star (cayleyFrobenius : ClTower A 1) = mat2 1 1 (-1) 1 := by
      apply ext_fin2 <;> simp [cayleyFrobenius, omegaOp, mat2]
    rw [hs]
    apply ext_fin2 <;>
      simp [cayleyFrobenius, omegaOp, mat2, Matrix.mul_apply, Fin.sum_univ_two, two_smul]
  · induction n with
    | zero => simp [towerTrace, cayleyTowerOp]
    | succ k ih =>
        rw [cayleyTowerOp, towerTrace, mat2_00, mat2_11, ih, pow_succ', two_mul, add_nsmul]
  · induction n with
    | zero =>
        change star (1 : A) * (1 : A) = (1 : ℕ) • (1 : A)
        simp
    | succ k ih =>
        let _ : StarRing (ClTower A k) := instStarRingClTower k
        let _ : StarRing (ClTower A (k + 1)) := instStarRingClTower (k + 1)
        have hs : star (cayleyTowerOp (A := A) (k + 1)) =
            mat2 (star (cayleyTowerOp k)) (star (cayleyTowerOp k))
                 (-star (cayleyTowerOp k)) (star (cayleyTowerOp k)) := by
          apply ext_fin2 <;> simp [cayleyTowerOp, mat2]
        rw [hs]
        dsimp only [cayleyTowerOp]
        apply ext_fin2
        · simp [mat2, Matrix.mul_apply, Fin.sum_univ_two, ih, pow_succ', two_mul]
        · simp [mat2, Matrix.mul_apply, Fin.sum_univ_two, ih]
        · simp [mat2, Matrix.mul_apply, Fin.sum_univ_two, ih]
        · simp [mat2, Matrix.mul_apply, Fin.sum_univ_two, ih, pow_succ', two_mul]

/-- The rotor polynomial defect vanishes exactly when its two coefficients commute.
The equivalence is read from the off-diagonal entries in the same noncommutative matrix algebra. -/
theorem rotorPolynomial_defect_eq_zero_iff (a b : A) :
    (weilFrobenius a b) * weilFrobenius a b -
      mat2 (2 • a) 0 0 (2 • a) * weilFrobenius a b +
      mat2 (a * a + b * b) 0 0 (a * a + b * b) = 0 ↔ ⁅a, b⁆ = 0 := by
  have hpoly := (hasse_weil_poincare_and_kunneth_purity a b 0).1
  dsimp only at hpoly
  rw [hpoly]
  constructor
  · intro h
    have hentry := congrArg (fun M : ClTower A 1 => M 0 1) h
    simpa [mat2] using hentry
  · intro h
    rw [h]
    apply ext_fin2 <;> simp [mat2]

/-- For every even index `2 * m`, the tower star-norm identity rewrites as the square
`((2 ^ m : ℕ) • 1) ^ 2`. This is an algebraic square identity, not an order-positivity claim. -/
theorem cayleyTowerOp_even_power_square (m : ℕ) :
    @Star.star _ (instStarRingClTower (2 * m)).toStar (cayleyTowerOp (A := A) (2 * m)) *
      cayleyTowerOp (2 * m) = ((2 ^ m : ℕ) • (1 : ClTower A (2 * m))) ^ 2 := by
  have h := (hasse_weil_poincare_and_kunneth_purity (0 : A) 0 (2 * m)).2.2.2.2
  rw [h, sq, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, pow_mul, sq, mul_pow]

end ArchetypeW3_HasseWeilPoincareAndKunnethPurity

/-!
## Archetype $\mathcal{W}_4$: Hodge–Parabolic Symplectic Matrix Monodromy
-/

section ArchetypeW4_PicardLefschetzSymplecticMonodromy

variable {A : Type u} [Ring A] [StarRing A]

/-- Full symplectic cup-product pairing `mat2 0 (-1) 1 0` in `ClTower A (n + 1)`. -/
def cupForm (n : ℕ) : ClTower A (n + 1) :=
  mat2 0 (-1) 1 0

/-- Active Hodge-subspace symplectic cup-product pairing `mat2 0 (-Π_n) Π_n 0` in `ClTower A (n + 1)`. -/
def activeSymplecticForm (n : ℕ) : ClTower A (n + 1) :=
  mat2 0 (-cantorProj n) (cantorProj n) 0

lemma star_hodgeNilpotent (n : ℕ) :
    @Star.star _ (instStarRingClTower (n + 1)).toStar (hodgeNilpotent (A := A) n) =
      mat2 (-cantorProj (A := A) n) (cantorProj n) (-cantorProj n) (cantorProj n) := by
  let _ : StarRing (ClTower A n) := instStarRingClTower n
  let _ : StarRing (ClTower A (n + 1)) := instStarRingClTower (n + 1)
  have hP_star : star (cantorProj (A := A) n) = cantorProj n := cantorProj_selfAdjoint n
  rw [hodgeNilpotent_explicit]
  apply ext_fin2 <;> simp [mat2, hP_star]

/-- **All-Scales Hodge–Parabolic Symplectic Matrix Theorem ($\mathcal{W}_4$)**:
At every scale `n : ℕ` and winding power `k : ℕ`, the canonical Hodge–Parabolic nilpotent
`N_n := hodgeNilpotent (A := A) n` and monodromy `T_n := hodgeMonodromy (A := A) n`
strictly satisfy:
1. `N_n ∈ sp(cupForm n)` (`star N_n * cupForm n + cupForm n * N_n = 0`),
2. Quadratic isotropy (`star N_n * cupForm n * N_n = 0`),
3. Exact symplectic invariance of all windings on `cupForm n`:
   `star (T_n ^ k) * cupForm n * (T_n ^ k) = cupForm n`,
4. Exact symplectic invariance of all windings on `activeSymplecticForm n`:
   `star (T_n ^ k) * activeSymplecticForm n * (T_n ^ k) = activeSymplecticForm n`. -/
theorem all_scales_picard_lefschetz_symplectic_monodromy (n k : ℕ) :
    let Ω_n := cupForm (A := A) n
    let Ω_act := activeSymplecticForm (A := A) n
    let N_n := hodgeNilpotent (A := A) n
    let T_n := hodgeMonodromy (A := A) n
    @Star.star _ (instStarRingClTower (n + 1)).toStar N_n * Ω_n + Ω_n * N_n = 0 ∧
    @Star.star _ (instStarRingClTower (n + 1)).toStar N_n * Ω_n * N_n = 0 ∧
    @Star.star _ (instStarRingClTower (n + 1)).toStar (T_n ^ k) * Ω_n * (T_n ^ k) = Ω_n ∧
    @Star.star _ (instStarRingClTower (n + 1)).toStar (T_n ^ k) * Ω_act * (T_n ^ k) = Ω_act := by
  let _ : StarRing (ClTower A (n + 1)) := instStarRingClTower (n + 1)
  intro Ω_n Ω_act N_n T_n
  have hP := cantorProj_idempotent (A := A) n
  have h_lie : star N_n * Ω_n + Ω_n * N_n = 0 := by
    dsimp [N_n, Ω_n]
    rw [star_hodgeNilpotent, hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [cupForm, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  have h_iso : star N_n * Ω_n * N_n = 0 := by
    dsimp [N_n, Ω_n]
    rw [star_hodgeNilpotent, hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [cupForm, mat2, Matrix.mul_apply, Fin.sum_univ_two, hP]
  have h_lie_act : star N_n * Ω_act + Ω_act * N_n = 0 := by
    dsimp [N_n, Ω_act]
    rw [star_hodgeNilpotent, hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [activeSymplecticForm, mat2, Matrix.mul_apply, Fin.sum_univ_two, hP]
  have h_iso_act : star N_n * Ω_act * N_n = 0 := by
    dsimp [N_n, Ω_act]
    rw [star_hodgeNilpotent, hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [activeSymplecticForm, mat2, Matrix.mul_apply, Fin.sum_univ_two, hP]
  have h_pow : T_n ^ k = 1 + k • N_n := hodgeMonodromy_pow n k
  refine ⟨h_lie, h_iso, ?_, ?_⟩
  · rw [h_pow, star_add, star_one, star_nsmul]
    calc (1 + k • star N_n) * Ω_n * (1 + k • N_n)
      _ = Ω_n + k • (star N_n * Ω_n + Ω_n * N_n) +
          (k * k) • (star N_n * Ω_n * N_n) := by
          simp only [add_mul, mul_add, one_mul, mul_one, mul_smul_comm, smul_mul_assoc,
            smul_smul, smul_add, add_assoc]
      _ = Ω_n := by rw [h_lie, h_iso, smul_zero, smul_zero, add_zero, add_zero]
  · rw [h_pow, star_add, star_one, star_nsmul]
    calc (1 + k • star N_n) * Ω_act * (1 + k • N_n)
      _ = Ω_act + k • (star N_n * Ω_act + Ω_act * N_n) +
          (k * k) • (star N_n * Ω_act * N_n) := by
          simp only [add_mul, mul_add, one_mul, mul_one, mul_smul_comm, smul_mul_assoc,
            smul_smul, smul_add, add_assoc]
      _ = Ω_act := by rw [h_lie_act, h_iso_act, smul_zero, smul_zero, add_zero, add_zero]

private theorem weilCohomology_noncomm_witness {A : Type u} [Ring A] [Nontrivial A] :
    ∃ x y : ClTower A 1, x * y ≠ y * x := by
  refine ⟨gradedFrobenius 1 0, omegaOp, ?_⟩
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [gradedFrobenius, omegaOp, mat2, Matrix.mul_apply, Fin.sum_univ_two] at h01

end ArchetypeW4_PicardLefschetzSymplecticMonodromy

end InfoGeometry.Algebra.NoncommutativeWeilCohomologyAndPicardLefschetzSynthesis
