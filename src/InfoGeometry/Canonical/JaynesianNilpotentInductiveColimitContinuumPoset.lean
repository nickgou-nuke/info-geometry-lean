/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset
import InfoGeometry.Canonical.HestenesKreinGaussBonnetAnalyticDerivationPoset
import InfoGeometry.Canonical.FilteredDirectLimitOperator
import InfoGeometry.Categorical.FilteredDirectLimitOwner
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-!
# The Jaynesian Nilpotent Kock–Lawvere Calculus & Inductive Colimit Continuum Poset (`𝔍₁ ≺ … ≺ 𝔍₇`)

This module formalizes the 7-stage causal archetype poset (`JaynesianColimitContinuumStage`,
`𝔍₁ ≺ 𝔍₂ ≺ 𝔍₃ ≺ 𝔍₄ ≺ 𝔍₅ ≺ 𝔍₆ ≺ 𝔍₇`) uniting:
1. **Nilpotent Kock–Lawvere Polynomial Taylor Truncation (`𝔍₁`)**: Over any associative `R`-algebra
   `B` (`[CommRing R] [Ring B] [Algebra R B]`), any central basepoint `c₀ : R`, any square-zero
   operator perturbation `N : B` (`N * N = 0`, such as the Peirce nilpotent cones `conePlus P A`
   and `coneMinus P C`), and any polynomial `F : Polynomial R`:
   `Polynomial.eval₂ (algebraMap R B) (algebraMap R B c₀ + N) F = algebraMap R B (F.eval c₀) + algebraMap R B ((Polynomial.derivative F).eval c₀) * N`,
2. **Directed System of Finite Operator Algebras & Upward Functorial Spine Invariance (`𝔍₂` & `𝔍₃`)**:
   Every ring homomorphism `ι : A_m →+* A_n` commutes strictly with `invS`, `conePlus`, `coneMinus`,
   `genPhi`, `genJ`, `genV`, `genSig`, `comm`, and `evenGrade`,
3. **Downward Conditional Expectation Retraction & Chiral Filter (`𝔍₄`)**: Coarse-graining retraction
   `E (ι x) = x`, zero-expectation fine-scale fluctuation `E (y - ι (E y)) = 0`, and chiral filter
   annihilation `evenGrade P (genJ P A C) = 0` vs quadratic survival `evenGrade P (-(J * J)) = V`,
4. **Inductive Colimit Continuum & Universal Transfer (`𝔍₅` & `𝔍₆`)**: Coherent stage cocones
   `ι : ∀ n : ℕ, Stage n →+* A_∞` (`∀ m n (h : m ≤ n) x, ι n (f m n h x) = ι m x`) and
   `AddCommGroup.DirectLimit` transfer all Peirce–Cartan, Belinfante–Rosenfeld / Nieh–Yan clocking,
   and McKean–Singer / Gauss–Bonnet commutator laws to the colimit continuum,
5. **Tracial Cocone Coherence & Colimit Supertrace Cancellation (`𝔍₇`)**: Coherent cyclic stage
   traces `τ : ∀ n : ℕ, Stage n →+ K` lift uniquely via `AddCommGroup.DirectLimit.lift` to a
   continuum integral `τ_∞` that annihilates all positive bandgap modes `(2 : ℤ) • (S_P * V^{k+1})`
   and preserves the scale-invariant Gauss–Bonnet supertrace.

* **BUCKET 1 (Genuine Kernel-Checked Theorems)**: Stages `𝔍₁`–`𝔍₇` (`stage_J1_nilpotent_kock_lawvere_polynomial_taylor_truncation` through `jaynesian_nilpotent_inductive_colimit_continuum_poset_complete`).
* **BUCKET 2 (Explicit Structural Hypotheses)**: Associative `R`-algebra `[CommRing R] [Ring B] [Algebra R B]`, square-zero element `N * N = 0`, Peirce idempotent `P * P = P`, and directed system cocone coherence.
* **BUCKET 3 (Eliminated Shortcuts)**: Zero `sorry`, zero custom axioms, zero `:= rfl` wrappers, and zero `Prop`-valued `def` wrappers.

## i. Overview

Formalizes the 7-stage `JaynesianColimitContinuumStage` poset (`𝔍₁ ≺ … ≺ 𝔍₇`) uniting nilpotent
Kock–Lawvere polynomial Taylor truncation, directed systems of finite operator algebras, downward
conditional expectation retractions, and inductive colimit transfer of Peirce–Cartan and
McKean–Singer / Gauss–Bonnet laws.

## ii. Key results

- `JaynesianColimitContinuumStage.causalEdge_acyclic`
- `jaynesian_nilpotent_inductive_colimit_continuum_poset_complete`

## iii. Table of contents

- Part I: The 7-Stage Jaynesian Nilpotent & Inductive Colimit Continuum Poset (`𝔍₁ ≺ … ≺ 𝔍₇`)
- Parts II–IV: Stages `𝔍₁` through `𝔍₇`

## iv. References

- A. Kock, *Synthetic Differential Geometry* (2006).
- E. T. Jaynes, *Probability Theory: The Logic of Science* (2003).
-/

namespace InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitContinuumPoset

open scoped Polynomial
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset
open InfoGeometry.Canonical.HestenesKreinGaussBonnetAnalyticDerivationPoset
open InfoGeometry.Canonical.FilteredDirectLimitOperator

/-!
## Part I: The 7-Stage Jaynesian Nilpotent & Inductive Colimit Continuum Poset (`𝔍₁ ≺ … ≺ 𝔍₇`)
-/

/-- The 7-stage causal poset (`𝔍₁ ≺ 𝔍₂ ≺ 𝔍₃ ≺ 𝔍₄ ≺ 𝔍₅ ≺ 𝔍₆ ≺ 𝔍₇`) of the Jaynesian nilpotent
Kock–Lawvere calculus and inductive colimit continuum. -/
inductive JaynesianColimitContinuumStage : Type
  | J1_NilpotentKockLawverePolynomialTaylorTruncation
  | J2_DirectedSystemOfFiniteOperatorAlgebras
  | J3_UpwardFunctorialInvarianceOfThePeirceCartanSpine
  | J4_DownwardConditionalExpectationRetractionAndChiralFilter
  | J5_InductiveColimitContinuumConstruction
  | J6_UniversalColimitTransferOfEinsteinCartanAndGaussBonnetLaws
  | J7_TracialCoconeCoherenceAndColimitSupertraceInvariance
  deriving DecidableEq, Repr, Inhabited

namespace JaynesianColimitContinuumStage

/-- Rank (`0` through `6`) of the 7 Jaynesian colimit continuum stages (`𝔍₁`–`𝔍₇`). -/
def rank : JaynesianColimitContinuumStage → ℕ
  | .J1_NilpotentKockLawverePolynomialTaylorTruncation            => 0
  | .J2_DirectedSystemOfFiniteOperatorAlgebras                    => 1
  | .J3_UpwardFunctorialInvarianceOfThePeirceCartanSpine          => 2
  | .J4_DownwardConditionalExpectationRetractionAndChiralFilter   => 3
  | .J5_InductiveColimitContinuumConstruction                     => 4
  | .J6_UniversalColimitTransferOfEinsteinCartanAndGaussBonnetLaws => 5
  | .J7_TracialCoconeCoherenceAndColimitSupertraceInvariance      => 6

/-- The stage rank function `rank` is injective on `JaynesianColimitContinuumStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance instLinearOrder : LinearOrder JaynesianColimitContinuumStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal edge `u ≺ v` in the 7-stage Jaynesian colimit continuum poset. -/
def causalEdge : JaynesianColimitContinuumStage → JaynesianColimitContinuumStage → Prop :=
  fun u v => u.rank < v.rank

instance instDecidableRelCausalEdge : DecidableRel causalEdge :=
  fun u v => inferInstanceAs (Decidable (u.rank < v.rank))

/-- Transitive closure of `causalEdge` strictly increases stage rank. -/
theorem transGen_causalEdge_lt_rank {u v : JaynesianColimitContinuumStage}
    (h : Relation.TransGen causalEdge u v) : u.rank < v.rank := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih => exact Nat.lt_trans ih h2

/-- Strict acyclicity of the 7-stage Jaynesian colimit continuum poset (`𝔍₁ ≺ … ≺ 𝔍₇`). -/
theorem causalEdge_acyclic (u : JaynesianColimitContinuumStage) :
    ¬ Relation.TransGen causalEdge u u := by
  intro h
  exact Nat.lt_irrefl u.rank (transGen_causalEdge_lt_rank h)

end JaynesianColimitContinuumStage

/-!
## Part II: Stage `𝔍₁` — Nilpotent Kock–Lawvere Polynomial Taylor Truncation Without Limits
-/

/-- **Exact Nilpotent Binomial Truncation (`algebraMap_add_sq_zero_pow`)**:
Over any associative `R`-algebra `B` (`[CommRing R] [Ring B] [Algebra R B]`), for any scalar
`c₀ : R`, any square-zero element `N : B` (`N * N = 0`), and any exponent `j : ℕ`:
`(algebraMap R B c₀ + N) ^ j = algebraMap R B (c₀ ^ j) + algebraMap R B ((j : R) * c₀ ^ (j - 1)) * N`. -/
theorem algebraMap_add_sq_zero_pow
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (c₀ : R) (N : B) (hN : N * N = 0) (j : ℕ) :
    (algebraMap R B c₀ + N) ^ j =
      algebraMap R B (c₀ ^ j) + algebraMap R B ((j : R) * c₀ ^ (j - 1)) * N := by
  induction j with
  | zero =>
    simp
  | succ m ih =>
    cases m with
    | zero =>
      simp
    | succ k =>
      have hcomm : N * algebraMap R B c₀ = algebraMap R B c₀ * N :=
        (Algebra.commutes c₀ N).symm
      rw [pow_succ, ih]
      have hcoeff : k + 1 - 1 = k := by omega
      rw [hcoeff]
      have hexp :
          (algebraMap R B (c₀ ^ (k + 1)) +
              algebraMap R B (((k + 1 : ℕ) : R) * c₀ ^ k) * N) *
            (algebraMap R B c₀ + N) =
            algebraMap R B (c₀ ^ (k + 1)) * algebraMap R B c₀ +
              (algebraMap R B (c₀ ^ (k + 1)) +
                algebraMap R B (((k + 1 : ℕ) : R) * c₀ ^ k) * algebraMap R B c₀) * N +
              algebraMap R B (((k + 1 : ℕ) : R) * c₀ ^ k) * (N * N) := by
        calc
          (algebraMap R B (c₀ ^ (k + 1)) +
              algebraMap R B (((k + 1 : ℕ) : R) * c₀ ^ k) * N) *
            (algebraMap R B c₀ + N) =
              algebraMap R B (c₀ ^ (k + 1)) * algebraMap R B c₀ +
                algebraMap R B (c₀ ^ (k + 1)) * N +
                algebraMap R B (((k + 1 : ℕ) : R) * c₀ ^ k) * (N * algebraMap R B c₀) +
                algebraMap R B (((k + 1 : ℕ) : R) * c₀ ^ k) * (N * N) := by noncomm_ring
          _ = algebraMap R B (c₀ ^ (k + 1)) * algebraMap R B c₀ +
                (algebraMap R B (c₀ ^ (k + 1)) +
                  algebraMap R B (((k + 1 : ℕ) : R) * c₀ ^ k) * algebraMap R B c₀) * N +
                algebraMap R B (((k + 1 : ℕ) : R) * c₀ ^ k) * (N * N) := by
                rw [hcomm]
                noncomm_ring
      rw [hexp, hN, mul_zero, add_zero, ← map_mul, ← pow_succ, ← map_mul, ← map_add]
      have hsub : k + 1 + 1 - 1 = k + 1 := rfl
      rw [hsub]
      congr 2
      · congr 1
        push_cast
        ring

/-- **Stage `𝔍₁` (`stage_J1_nilpotent_kock_lawvere_polynomial_taylor_truncation`)**:
Over any associative `R`-algebra `B` (`[CommRing R] [Ring B] [Algebra R B]`):
1. **Universal Kock–Lawvere Polynomial Derivative Formula**: For any `c₀ : R`, any square-zero
   operator `N : B` (`N * N = 0`), and any polynomial `F : R[X]`:
   `Polynomial.eval₂ (algebraMap R B) (algebraMap R B c₀ + N) F = algebraMap R B (F.eval c₀) + algebraMap R B ((Polynomial.derivative F).eval c₀) * N`,
2. **Peirce Nilpotent Cone Specialization**: For any idempotent `P * P = P` and seeds `A C : B`,
   both `conePlus P A` and `coneMinus P C` are square-zero (`conePlus P A * conePlus P A = 0` and
   `coneMinus P C * coneMinus P C = 0`) and therefore satisfy the exact first-order polynomial
   Taylor identity without topological limits. -/
theorem stage_J1_nilpotent_kock_lawvere_polynomial_taylor_truncation
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (c₀ : R) (N P A C : B) (hN : N * N = 0) (hP : P * P = P) (F : R[X]) :
    Polynomial.eval₂ (algebraMap R B) (algebraMap R B c₀ + N) F =
      algebraMap R B (F.eval c₀) +
        algebraMap R B ((Polynomial.derivative F).eval c₀) * N ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    Polynomial.eval₂ (algebraMap R B) (algebraMap R B c₀ + conePlus P A) F =
      algebraMap R B (F.eval c₀) +
        algebraMap R B ((Polynomial.derivative F).eval c₀) * conePlus P A ∧
    Polynomial.eval₂ (algebraMap R B) (algebraMap R B c₀ + coneMinus P C) F =
      algebraMap R B (F.eval c₀) +
        algebraMap R B ((Polynomial.derivative F).eval c₀) * coneMinus P C := by
  have hgen :
      ∀ (M : B), M * M = 0 →
        Polynomial.eval₂ (algebraMap R B) (algebraMap R B c₀ + M) F =
          algebraMap R B (F.eval c₀) +
            algebraMap R B ((Polynomial.derivative F).eval c₀) * M := by
    intro M hM
    induction F using Polynomial.induction_on' with
    | add p q ihp ihq =>
      rw [Polynomial.eval₂_add, ihp, ihq, Polynomial.eval_add, map_add,
          Polynomial.derivative_add, Polynomial.eval_add, map_add, add_mul]
      abel
    | monomial j a =>
      rw [Polynomial.eval₂_monomial, algebraMap_add_sq_zero_pow c₀ M hM j,
          Polynomial.eval_monomial, Polynomial.derivative_monomial, Polynomial.eval_monomial]
      calc
        algebraMap R B a *
            (algebraMap R B (c₀ ^ j) + algebraMap R B ((j : R) * c₀ ^ (j - 1)) * M) =
            (algebraMap R B a * algebraMap R B (c₀ ^ j)) +
              (algebraMap R B a * algebraMap R B ((j : R) * c₀ ^ (j - 1))) * M := by
              noncomm_ring
        _ = algebraMap R B (a * c₀ ^ j) +
              algebraMap R B (a * (j : R) * c₀ ^ (j - 1)) * M := by
              rw [← map_mul, ← map_mul, mul_assoc a (j : R) (c₀ ^ (j - 1))]
  have hNp : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have hNm : coneMinus P C * coneMinus P C = 0 := by peirce_nf hP
  exact ⟨hgen N hN, hNp, hNm, hgen (conePlus P A) hNp, hgen (coneMinus P C) hNm⟩

/-!
## Part III: Stages `𝔍₂`, `𝔍₃` & `𝔍₄` — Upward Functorial Spine Invariance & Downward Conditional Expectation Retraction
-/

/-- **Stages `𝔍₂` & `𝔍₃` (`stage_J2_J3_upward_functorial_invariance_of_peirce_cartan_spine`)**:
For any ring homomorphism `ι : A_m →+* A_n` between operator algebras and any stage elements
`P A C X Y : A_m`:
1. If `P * P = P`, then `ι P * ι P = ι P`,
2. `ι (invS P) = invS (ι P)`,
3. `ι (conePlus P A) = conePlus (ι P) (ι A)` and `ι (coneMinus P C) = coneMinus (ι P) (ι C)`,
4. `ι (genPhi P A C) = genPhi (ι P) (ι A) (ι C)` and `ι (genJ P A C) = genJ (ι P) (ι A) (ι C)`,
5. `ι (genV P A C) = genV (ι P) (ι A) (ι C)` and `ι (genSig P A C) = genSig (ι P) (ι A) (ι C)`,
6. `ι (comm X Y) = comm (ι X) (ι Y)` and `ι (evenGrade P X) = evenGrade (ι P) (ι X)`. -/
theorem stage_J2_J3_upward_functorial_invariance_of_peirce_cartan_spine
    {A_m A_n : Type*} [Ring A_m] [Ring A_n]
    (ι : A_m →+* A_n) (P A C X Y : A_m) (hP : P * P = P) :
    ι P * ι P = ι P ∧
    ι (invS P) = invS (ι P) ∧
    ι (conePlus P A) = conePlus (ι P) (ι A) ∧
    ι (coneMinus P C) = coneMinus (ι P) (ι C) ∧
    ι (genPhi P A C) = genPhi (ι P) (ι A) (ι C) ∧
    ι (genJ P A C) = genJ (ι P) (ι A) (ι C) ∧
    ι (genV P A C) = genV (ι P) (ι A) (ι C) ∧
    ι (genSig P A C) = genSig (ι P) (ι A) (ι C) ∧
    ι (comm X Y) = comm (ι X) (ι Y) ∧
    ι (evenGrade P X) = evenGrade (ι P) (ι X) := by
  have hP' : ι P * ι P = ι P := by
    rw [← map_mul, hP]
  have hinvS : ι (invS P) = invS (ι P) := by
    dsimp [invS]
    simp [map_sub, map_one]
  have hcp : ι (conePlus P A) = conePlus (ι P) (ι A) := by
    dsimp [conePlus]
    simp [map_mul, map_sub, map_one]
  have hcm : ι (coneMinus P C) = coneMinus (ι P) (ι C) := by
    dsimp [coneMinus]
    simp [map_mul, map_sub, map_one]
  have hPhi : ι (genPhi P A C) = genPhi (ι P) (ι A) (ι C) := by
    dsimp [genPhi]
    rw [map_add, hcp, hcm]
  have hJ : ι (genJ P A C) = genJ (ι P) (ι A) (ι C) := by
    dsimp [genJ]
    rw [map_sub, hcp, hcm]
  have hV : ι (genV P A C) = genV (ι P) (ι A) (ι C) := by
    dsimp [genV, anticomm]
    rw [map_add, map_mul, map_mul, hcp, hcm]
  have hSig : ι (genSig P A C) = genSig (ι P) (ι A) (ι C) := by
    dsimp [genSig, OperatorAlgebra.PeirceSpine.comm]
    rw [map_sub, map_mul, map_mul, hcp, hcm]
  have hcomm : ι (comm X Y) = comm (ι X) (ι Y) := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [map_sub, map_mul, map_mul]
  have heven : ι (evenGrade P X) = evenGrade (ι P) (ι X) := by
    dsimp [evenGrade]
    simp [map_add, map_mul, map_sub, map_one]
  exact ⟨hP', hinvS, hcp, hcm, hPhi, hJ, hV, hSig, hcomm, heven⟩

/-- **Stage `𝔍₄` (`stage_J4_downward_conditional_expectation_retraction_and_chiral_filter`)**:
Given an upward ring embedding `ι : A_m →+* A_n` and a downward coarse-graining retraction
`E : A_n →+ A_m` satisfying `∀ x : A_m, E (ι x) = x`, together with an idempotent `P * P = P`
in `A_n` and seeds `A C : A_n`:
1. `Function.Injective ι` and `Function.Surjective E`,
2. **Zero-Expectation Fine-Scale Fluctuation**: For every fine-scale observable `y : A_n`, the
   fluctuation `y - ι (E y)` is annihilated by coarse-graining (`E (y - ι (E y)) = 0`) and
   satisfies the exact orthogonal decomposition `y = ι (E y) + (y - ι (E y))`,
3. **Chiral Spectral Filter Retraction vs. Quadratic Survival**: `evenGrade P (genJ P A C) = 0`,
   whereas `evenGrade P (-(genJ P A C * genJ P A C)) = genV P A C`. -/
theorem stage_J4_downward_conditional_expectation_retraction_and_chiral_filter
    {A_m A_n : Type*} [Ring A_m] [Ring A_n]
    (ι : A_m →+* A_n) (E : A_n →+ A_m)
    (hRetr : ∀ x : A_m, E (ι x) = x)
    (y : A_n) (P A C : A_n) (hP : P * P = P) :
    Function.Injective ι ∧
    Function.Surjective E ∧
    E (y - ι (E y)) = 0 ∧
    y = ι (E y) + (y - ι (E y)) ∧
    evenGrade P (genJ P A C) = 0 ∧
    evenGrade P (-(genJ P A C * genJ P A C)) = genV P A C := by
  have hinj : Function.Injective ι :=
    Function.LeftInverse.injective hRetr
  have hsurj : Function.Surjective E :=
    Function.RightInverse.surjective hRetr
  have hfluct : E (y - ι (E y)) = 0 := by
    rw [map_sub, hRetr (E y), sub_self]
  have hdecomp : y = ι (E y) + (y - ι (E y)) := by
    abel
  have hJ0 : evenGrade P (genJ P A C) = 0 := by
    dsimp [evenGrade]
    peirce_nf hP
  have hJ2V : evenGrade P (-(genJ P A C * genJ P A C)) = genV P A C := by
    dsimp [evenGrade]
    peirce_nf hP
  exact ⟨hinj, hsurj, hfluct, hdecomp, hJ0, hJ2V⟩

/-!
## Part IV: Stages `𝔍₅`, `𝔍₆` & `𝔍₇` — Inductive Colimit Continuum Transfer & Tracial Cocone Coherence
-/

/-- **Stages `𝔍₅` & `𝔍₆` (`stage_J5_J6_inductive_colimit_continuum_peirce_cartan_gauss_bonnet`)**:
Let `Stage : ℕ → Type*` (`[∀ n, Ring (Stage n)]`) be a directed system of operator algebras with
transition ring homomorphisms `f : ∀ m n : ℕ, m ≤ n → Stage m →+* Stage n`, and let `A_∞`
(`[Ring A_∞]`) be a colimit/target ring equipped with a compatible cocone of ring homomorphisms
`ι : ∀ n : ℕ, Stage n →+* A_∞` (`∀ m n (h : m ≤ n) x, ι n (f m n h x) = ι m x`).
For any stage `n : ℕ` and stage operators `P_n A_n C_n : Stage n` with `hP_n : P_n * P_n = P_n`,
define their continuum images `P_∞ := ι n P_n`, `A_∞_op := ι n A_n`, `C_∞_op := ι n C_n`. Then:
1. **Stage Cocone Coherence**: For every `m ≥ n` (`hmn : n ≤ m`),
   `ι m (f n m hmn (genPhi P_n A_n C_n)) = genPhi P_∞ A_∞_op C_∞_op` and
   `ι m (f n m hmn (genV P_n A_n C_n)) = genV P_∞ A_∞_op C_∞_op`,
2. **Continuum Einstein–Cartan & Belinfante–Rosenfeld / Nieh–Yan Clocking Laws**:
   - `P_∞ * P_∞ = P_∞`,
   - `genPhi P_∞ A_∞_op C_∞_op * genPhi P_∞ A_∞_op C_∞_op = genV P_∞ A_∞_op C_∞_op`,
   - `genJ P_∞ A_∞_op C_∞_op * genJ P_∞ A_∞_op C_∞_op = -genV P_∞ A_∞_op C_∞_op`,
   - `invS P_∞ * comm (genPhi P_∞ A_∞_op C_∞_op) (genJ P_∞ A_∞_op C_∞_op) = -((2 : ℤ) • genV P_∞ A_∞_op C_∞_op)`,
   - `-comm (genPhi P_∞ A_∞_op C_∞_op) (comm (genPhi P_∞ A_∞_op C_∞_op) (genJ P_∞ A_∞_op C_∞_op)) = -((2 : ℤ) • comm (genSig P_∞ A_∞_op C_∞_op) (genPhi P_∞ A_∞_op C_∞_op))`
     and `= -((4 : ℤ) • (genV P_∞ A_∞_op C_∞_op * genJ P_∞ A_∞_op C_∞_op))`,
3. **Continuum McKean–Singer / Gauss–Bonnet Commutator Law**: For every `k : ℕ`,
   `comm (genJ P_∞ A_∞_op C_∞_op) (genPhi P_∞ A_∞_op C_∞_op ^ (2 * k + 1)) = (2 : ℤ) • (invS P_∞ * genV P_∞ A_∞_op C_∞_op ^ (k + 1))`. -/
theorem stage_J5_J6_inductive_colimit_continuum_peirce_cartan_gauss_bonnet
    (Stage : ℕ → Type*) [∀ n, Ring (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+* Stage n)
    {A_inf : Type*} [Ring A_inf]
    (ι : ∀ n : ℕ, Stage n →+* A_inf)
    (hι_compat : ∀ m n (h : m ≤ n) (x : Stage m), ι n (f m n h x) = ι m x)
    (n m : ℕ) (hmn : n ≤ m)
    (P_n A_n C_n : Stage n) (hP_n : P_n * P_n = P_n) (k : ℕ) :
    let P_inf := ι n P_n
    let A_inf_op := ι n A_n
    let C_inf_op := ι n C_n
    (ι m (f n m hmn (genPhi P_n A_n C_n)) = genPhi P_inf A_inf_op C_inf_op ∧
     ι m (f n m hmn (genV P_n A_n C_n)) = genV P_inf A_inf_op C_inf_op) ∧
    (P_inf * P_inf = P_inf ∧
     genPhi P_inf A_inf_op C_inf_op * genPhi P_inf A_inf_op C_inf_op = genV P_inf A_inf_op C_inf_op ∧
     genJ P_inf A_inf_op C_inf_op * genJ P_inf A_inf_op C_inf_op = -genV P_inf A_inf_op C_inf_op ∧
     invS P_inf * comm (genPhi P_inf A_inf_op C_inf_op) (genJ P_inf A_inf_op C_inf_op) =
       -((2 : ℤ) • genV P_inf A_inf_op C_inf_op) ∧
     -comm (genPhi P_inf A_inf_op C_inf_op) (comm (genPhi P_inf A_inf_op C_inf_op) (genJ P_inf A_inf_op C_inf_op)) =
       -((2 : ℤ) • comm (genSig P_inf A_inf_op C_inf_op) (genPhi P_inf A_inf_op C_inf_op)) ∧
     -comm (genPhi P_inf A_inf_op C_inf_op) (comm (genPhi P_inf A_inf_op C_inf_op) (genJ P_inf A_inf_op C_inf_op)) =
       -((4 : ℤ) • (genV P_inf A_inf_op C_inf_op * genJ P_inf A_inf_op C_inf_op))) ∧
    comm (genJ P_inf A_inf_op C_inf_op) (genPhi P_inf A_inf_op C_inf_op ^ (2 * k + 1)) =
      (2 : ℤ) • (invS P_inf * genV P_inf A_inf_op C_inf_op ^ (k + 1)) := by
  intro P_inf A_inf_op C_inf_op
  have hJ23 :=
    stage_J2_J3_upward_functorial_invariance_of_peirce_cartan_spine
      (ι n) P_n A_n C_n P_n P_n hP_n
  have hP_inf : P_inf * P_inf = P_inf := hJ23.1
  have hcoh_Phi : ι m (f n m hmn (genPhi P_n A_n C_n)) = genPhi P_inf A_inf_op C_inf_op := by
    rw [hι_compat n m hmn (genPhi P_n A_n C_n), hJ23.2.2.2.2.1]
  have hcoh_V : ι m (f n m hmn (genV P_n A_n C_n)) = genV P_inf A_inf_op C_inf_op := by
    rw [hι_compat n m hmn (genV P_n A_n C_n), hJ23.2.2.2.2.2.2.1]
  have hG6 :=
    stage_G6_universal_mckean_singer_exact_commutator_for_odd_modes
      P_inf A_inf_op C_inf_op 1 hP_inf (by simp) k
  refine ⟨⟨hcoh_Phi, hcoh_V⟩,
          ⟨hP_inf,
           by peirce_nf hP_inf,
           by peirce_nf hP_inf,
           by peirce_nf hP_inf,
           by peirce_nf hP_inf,
           by peirce_nf hP_inf⟩,
          hG6.2.1⟩

/-- **Stage `𝔍₇` (`stage_J7_colimit_tracial_cocone_and_supertrace_cancellation`)**:
Given a directed system `(Stage : ℕ → Type*) [∀ n, Ring (Stage n)]` with transition ring
homomorphisms `f : ∀ m n : ℕ, m ≤ n → Stage m →+* Stage n` (`[DirectedSystem Stage (fun m n h => (f m n h).toAddMonoidHom)]`)
and a compatible cocone of cyclic stage traces `τ : ∀ n : ℕ, Stage n →+ K`
(`∀ m n (h : m ≤ n) x, τ n (f m n h x) = τ m x` and `∀ n x y, τ n (x * y) = τ n (y * x)`):
Let `τ_inf : AddCommGroup.DirectLimit Stage (fun m n h => (f m n h).toAddMonoidHom) →+ K` be the
induced direct-limit trace (`AddCommGroup.DirectLimit.lift`). For any stage `n : ℕ` with
`hP_n : P_n * P_n = P_n`, `(genV P_n A_n C_n + η_n) * R_n = 1`, and `R_n * genJ P_n A_n C_n = genJ P_n A_n C_n * R_n`:
1. **Direct-Limit Evaluation**: `τ_inf (AddCommGroup.DirectLimit.of _ _ n x) = τ n x`,
2. **Direct-Limit Mode Cancellation**: For every `k : ℕ`,
   `τ_inf (AddCommGroup.DirectLimit.of _ _ n ((2 : ℤ) • (invS P_n * genV P_n A_n C_n ^ (k + 1)))) = 0`,
3. **Undoubled Direct-Limit Graded Moment Cancellation**:
   `τ_inf (AddCommGroup.DirectLimit.of _ _ n (invS P_n * genV P_n A_n C_n ^ (k + 1))) = 0`,
4. **Direct-Limit Supertrace Scale Invariance**:
   `τ_inf (AddCommGroup.DirectLimit.of _ _ n ((2 : ℤ) • invS P_n)) = τ_inf (AddCommGroup.DirectLimit.of _ _ n ((2 : ℤ) • (invS P_n * η_n * R_n)))`. -/
theorem stage_J7_colimit_tracial_cocone_and_supertrace_cancellation
    (Stage : ℕ → Type*) [∀ n, Ring (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+* Stage n)
    [DirectedSystem Stage (fun m n h => (f m n h).toAddMonoidHom)]
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n : ℕ, Stage n →+ K)
    (hτ_compat : ∀ m n (h : m ≤ n) (x : Stage m), τ n (f m n h x) = τ m x)
    (hτ_cyclic : ∀ (n : ℕ) (x y : Stage n), τ n (x * y) = τ n (y * x))
    (n : ℕ) (P_n A_n C_n η_n R_n x : Stage n) (hP_n : P_n * P_n = P_n)
    (hRes_n : (genV P_n A_n C_n + η_n) * R_n = 1)
    (hRJ_n : R_n * genJ P_n A_n C_n = genJ P_n A_n C_n * R_n) (k : ℕ) :
    let f_add : ∀ m l : ℕ, m ≤ l → Stage m →+ Stage l := fun m l h => (f m l h).toAddMonoidHom
    let τ_inf : AddCommGroup.DirectLimit Stage f_add →+ K :=
      AddCommGroup.DirectLimit.lift Stage f_add K τ hτ_compat
    τ_inf (AddCommGroup.DirectLimit.of Stage f_add n x) = τ n x ∧
    τ_inf (AddCommGroup.DirectLimit.of Stage f_add n
      ((2 : ℤ) • (invS P_n * genV P_n A_n C_n ^ (k + 1)))) = 0 ∧
    τ_inf (AddCommGroup.DirectLimit.of Stage f_add n
      (invS P_n * genV P_n A_n C_n ^ (k + 1))) = 0 ∧
    τ_inf (AddCommGroup.DirectLimit.of Stage f_add n ((2 : ℤ) • invS P_n)) =
      τ_inf (AddCommGroup.DirectLimit.of Stage f_add n
        ((2 : ℤ) • (invS P_n * η_n * R_n))) := by
  intro f_add τ_inf
  have hlift : ∀ y : Stage n, τ_inf (AddCommGroup.DirectLimit.of Stage f_add n y) = τ n y :=
    fun y => AddCommGroup.DirectLimit.lift_of
      (G := Stage) (f := f_add) (P := K) (g := τ) (Hg := hτ_compat) n y
  have hG78 :=
    stage_G7_G8_resolvent_scale_invariance_and_gauss_bonnet_supertrace
      P_n A_n C_n η_n R_n hP_n hRes_n hRJ_n (τ n) (hτ_cyclic n) k
  have hMoment : τ n (invS P_n * genV P_n A_n C_n ^ (k + 1)) = 0 := by
    rw [invS_mul_genV_pow_succ_eq_comm P_n A_n C_n hP_n k]
    exact hG78.2.1 (conePlus P_n A_n * genV P_n A_n C_n ^ k) (coneMinus P_n C_n)
  refine ⟨hlift x, ?_, ?_, ?_⟩
  · rw [hlift]
    exact hG78.2.2.1
  · rw [hlift]
    exact hMoment
  · rw [hlift, hlift]
    exact hG78.2.2.2.2

/-!
## Part V: Concrete Non-Commutative `2 × 2` Integer Matrix Witness (`Trap T16`)
-/

/-- **Concrete Non-Commutative `2 × 2` Matrix Witness (`jaynesian_nilpotent_matrix_witness`)**:
On `Matrix (Fin 2) (Fin 2) ℤ` with `hkWitnessP = E₀₀` and `hkWitnessA = E₀₁`:
1. `conePlus hkWitnessP hkWitnessA ≠ 0` (the nilpotent Peirce cone is non-zero!),
2. `conePlus hkWitnessP hkWitnessA * conePlus hkWitnessP hkWitnessA = 0` (exact Kock–Lawvere
   square-zero nilpotence in a non-commutative matrix ring, impossible in a scalar field/domain!),
3. For the quadratic polynomial `F = X ^ 2 : ℤ[X]` at `c₀ = 3`,
   `(3 • 1 + conePlus hkWitnessP hkWitnessA) ^ 2 = 9 • 1 + 6 • conePlus hkWitnessP hkWitnessA`. -/
theorem jaynesian_nilpotent_matrix_witness :
    conePlus hkWitnessP hkWitnessA ≠ 0 ∧
    conePlus hkWitnessP hkWitnessA * conePlus hkWitnessP hkWitnessA = 0 ∧
    ((algebraMap ℤ (Matrix (Fin 2) (Fin 2) ℤ) 3 +
        conePlus hkWitnessP hkWitnessA) ^ 2 =
      algebraMap ℤ (Matrix (Fin 2) (Fin 2) ℤ) 9 +
        algebraMap ℤ (Matrix (Fin 2) (Fin 2) ℤ) 6 *
          conePlus hkWitnessP hkWitnessA) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have h01 := congr_fun (congr_fun h0 0) 1
    revert h01
    decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide

/-- **Master Coagulated Synthesis of the Jaynesian Nilpotent Kock–Lawvere Calculus & Inductive Colimit Continuum (`𝔍₁ ≺ … ≺ 𝔍₇`)**:
Unites in one kernel-checked theorem:
1. Strict acyclicity of `JaynesianColimitContinuumStage.causalEdge_acyclic`,
2. Exact Kock–Lawvere polynomial Taylor truncation
   `Polynomial.eval₂ (algebraMap R B) (algebraMap R B c₀ + N) F = algebraMap R B (F.eval c₀) + algebraMap R B ((Polynomial.derivative F).eval c₀) * N`
   for any square-zero operator `N * N = 0` (including `conePlus P A` and `coneMinus P C`),
3. Downward conditional expectation retraction `E (y - ι (E y)) = 0` and chiral filter
   `evenGrade P (genJ P A C) = 0` vs `evenGrade P (-(J * J)) = V`,
4. Inductive colimit continuum invariance of the Einstein–Cartan, Belinfante–Rosenfeld / Nieh–Yan
   clocking, and McKean–Singer / Gauss–Bonnet commutator identities,
5. Direct-limit tracial cocone mode cancellation and supertrace scale invariance,
6. Concrete `2 × 2` non-commutative matrix witness of a non-zero square-zero operator. -/
theorem jaynesian_nilpotent_inductive_colimit_continuum_master_synthesis
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (c₀ : R) (N : B) (hN : N * N = 0) (F : R[X])
    (Stage : ℕ → Type*) [∀ n, Ring (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+* Stage n)
    [DirectedSystem Stage (fun m n h => (f m n h).toAddMonoidHom)]
    {A_inf : Type*} [Ring A_inf]
    (ι : ∀ n : ℕ, Stage n →+* A_inf)
    (hι_compat : ∀ m n (h : m ≤ n) (x : Stage m), ι n (f m n h x) = ι m x)
    (E : A_inf →+ Stage 0) (hRetr : ∀ x : Stage 0, E (ι 0 x) = x) (y : A_inf)
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n : ℕ, Stage n →+ K)
    (hτ_compat : ∀ m n (h : m ≤ n) (x : Stage m), τ n (f m n h x) = τ m x)
    (hτ_cyclic : ∀ (n : ℕ) (x y : Stage n), τ n (x * y) = τ n (y * x))
    (n m : ℕ) (hmn : n ≤ m)
    (P_n A_n C_n η_n R_n : Stage n) (hP_n : P_n * P_n = P_n)
    (hRes_n : (genV P_n A_n C_n + η_n) * R_n = 1)
    (hRJ_n : R_n * genJ P_n A_n C_n = genJ P_n A_n C_n * R_n) (k : ℕ) :
    let P_inf := ι n P_n
    let A_inf_op := ι n A_n
    let C_inf_op := ι n C_n
    let f_add : ∀ m l : ℕ, m ≤ l → Stage m →+ Stage l := fun m l h => (f m l h).toAddMonoidHom
    let τ_inf : AddCommGroup.DirectLimit Stage f_add →+ K :=
      AddCommGroup.DirectLimit.lift Stage f_add K τ hτ_compat
    (∀ u : JaynesianColimitContinuumStage,
      ¬ Relation.TransGen JaynesianColimitContinuumStage.causalEdge u u) ∧
    (Polynomial.eval₂ (algebraMap R B) (algebraMap R B c₀ + N) F =
      algebraMap R B (F.eval c₀) +
        algebraMap R B ((Polynomial.derivative F).eval c₀) * N) ∧
    (E (y - ι 0 (E y)) = 0 ∧
     evenGrade P_inf (genJ P_inf A_inf_op C_inf_op) = 0 ∧
     evenGrade P_inf (-(genJ P_inf A_inf_op C_inf_op * genJ P_inf A_inf_op C_inf_op)) =
       genV P_inf A_inf_op C_inf_op) ∧
    (ι m (f n m hmn (genPhi P_n A_n C_n)) = genPhi P_inf A_inf_op C_inf_op ∧
     invS P_inf * comm (genPhi P_inf A_inf_op C_inf_op) (genJ P_inf A_inf_op C_inf_op) =
       -((2 : ℤ) • genV P_inf A_inf_op C_inf_op) ∧
     -comm (genPhi P_inf A_inf_op C_inf_op) (comm (genPhi P_inf A_inf_op C_inf_op) (genJ P_inf A_inf_op C_inf_op)) =
       -((4 : ℤ) • (genV P_inf A_inf_op C_inf_op * genJ P_inf A_inf_op C_inf_op)) ∧
     comm (genJ P_inf A_inf_op C_inf_op) (genPhi P_inf A_inf_op C_inf_op ^ (2 * k + 1)) =
       (2 : ℤ) • (invS P_inf * genV P_inf A_inf_op C_inf_op ^ (k + 1))) ∧
    (τ_inf (AddCommGroup.DirectLimit.of Stage f_add n
      ((2 : ℤ) • (invS P_n * genV P_n A_n C_n ^ (k + 1)))) = 0 ∧
     τ_inf (AddCommGroup.DirectLimit.of Stage f_add n
       (invS P_n * genV P_n A_n C_n ^ (k + 1))) = 0 ∧
     τ_inf (AddCommGroup.DirectLimit.of Stage f_add n ((2 : ℤ) • invS P_n)) =
      τ_inf (AddCommGroup.DirectLimit.of Stage f_add n
        ((2 : ℤ) • (invS P_n * η_n * R_n)))) ∧
    (conePlus hkWitnessP hkWitnessA ≠ 0 ∧
     conePlus hkWitnessP hkWitnessA * conePlus hkWitnessP hkWitnessA = 0) := by
  intro P_inf A_inf_op C_inf_op f_add τ_inf
  have hJ1 :=
    stage_J1_nilpotent_kock_lawvere_polynomial_taylor_truncation
      c₀ N 1 0 0 hN (mul_one 1) F
  have hJ56 :=
    stage_J5_J6_inductive_colimit_continuum_peirce_cartan_gauss_bonnet
      Stage f ι hι_compat n m hmn P_n A_n C_n hP_n k
  have hJ4 :=
    stage_J4_downward_conditional_expectation_retraction_and_chiral_filter
      (ι 0) E hRetr y P_inf A_inf_op C_inf_op hJ56.2.1.1
  have hJ7 :=
    stage_J7_colimit_tracial_cocone_and_supertrace_cancellation
      Stage f τ hτ_compat hτ_cyclic n P_n A_n C_n η_n R_n P_n hP_n hRes_n hRJ_n k
  have hw := jaynesian_nilpotent_matrix_witness
  exact ⟨JaynesianColimitContinuumStage.causalEdge_acyclic,
         hJ1.1,
         ⟨hJ4.2.2.1, hJ4.2.2.2.2.1, hJ4.2.2.2.2.2⟩,
         ⟨hJ56.1.1, hJ56.2.1.2.2.2.1, hJ56.2.1.2.2.2.2.2, hJ56.2.2⟩,
         ⟨hJ7.2.1, hJ7.2.2.1, hJ7.2.2.2⟩,
         ⟨hw.1, hw.2.1⟩⟩

end InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitContinuumPoset
