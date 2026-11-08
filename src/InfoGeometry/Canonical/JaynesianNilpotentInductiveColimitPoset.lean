/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesKreinGaussBonnetMonogenicPoset
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit
import InfoGeometry.Canonical.FilteredDirectLimitOperator
import InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset
import InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The Jaynesian Binary Cut, Exact Nilpotent First-Order Taylor Calculus, Directed Scale-Refinement Poset, Retraction Hypothesis, Eventual-Equality Quotient Carrier, Conditional Ring-Cone Transfer, and Cocone-Valued Function (`𝔍₁ → 𝔍₇`)

This module formalizes in native Mathlib (Lean 4) the 7-stage acyclic causal poset
(`𝔍₁ ≺ 𝔍₂ ≺ 𝔍₃ ≺ 𝔍₄ ≺ 𝔍₅ ≺ 𝔍₆ ≺ 𝔍₇`) governing the **Jaynesian Finite-Stage
Inductive Colimit & Nilpotent Calculus** across arbitrary non-commutative associative rings
`[Ring B]` equipped with `[Algebra R B]`, directed star-ring systems `(𝒜_n, ι_{m,n})_{m ≤ n}`,
the explicit categorical colimit quotient `JaynesianColimitCarrier Sys := Quotient (colimitSetoid Sys)`,
`InductiveStarColimitCone`, and concrete non-commutative matrix / Zorn octonion witnesses:

* **Phase I (The Fundamental Binary Cut `T ↔ S`)**:
  The Cantorian scalar-infinitesimal myth (`dx ≠ 0 ∧ dx² = 0`, which is contradictory in any
  commutative domain) vs. the Jaynesian off-diagonal Peirce nilpotent reality (`N_+ ≠ 0 ∧ N_+² = 0`)
  and an eventual-equality quotient carrier for the directed system. The quotient construction in
  this file is not itself the categorical ring colimit and does not remove analytic-limit
  obligations.
* **Phase II (The Fourfold Relational Anatomy)**:
  1. *Internal Consistency*: Finite-stage non-commutative ring `𝒜_n` with idempotent `P_n² = P_n`,
     nilpotent cones `N_{±,n}² = 0`, and exact first-order polynomial Taylor truncation
     `F(c₀ I_n + N_{+,n}) = F(c₀) I_n + F'(c₀) N_{+,n}`.
  2. *Outward Projection*: Functorial scale-refinement star-ring homomorphisms
     `ι_{m,n} : 𝒜_m →⋆+* 𝒜_n` (`m ≤ n`) preserving all Peirce–Cartan invariants
     `(S_{P_m}, N_{±,m}, Φ_m, J_m, V_m, Σ_m)`.
  3. *Inward Shadow-Intrusion*: A hypothesized downward function `E_n : 𝒜_{n+1} → 𝒜_n`
     satisfying only the retraction law `E_n ∘ ι_{n,n+1} = id`, plus the chiral grade-0 filter `evenGrade P`.
     No conditional-expectation structure or strict inequality for `ι ∘ E_n` is proved here.
     The grade filter annihilates linear odd jumps `Φ, J` while preserving the quadratic Casimir metric `V = Φ²`.
  4. *Autonomous Ground*: The quotient carrier `JaynesianColimitCarrier Sys` constructed
     by quotienting `Σ n : ℕ, 𝒜_n` by the directed equivalence relation
     `(m, X_m) ~ (n, Y_n) ↔ ∃ k ≥ max(m, n), ι_{m,k}(X_m) = ι_{n,k}(Y_n)`. This file proves
     setoid and cocone facts for this carrier; it does not define quotient ring operations or
     establish a categorical ring-colimit universal property.
* **Phase III & Phase IV (Socratic Aporia, Rung 0–Rung 4, & Universal Cocone Lifting)**:
  Rung 0 proves that in any domain `[Ring K] [IsDomain K]`, `dx * dx = 0 ↔ dx = 0`, whereas
  `rnMatrixPlus ≠ 0 ∧ rnMatrixPlus * rnMatrixPlus = 0`; and proves that unnormalized unit-trace
  sums grow strictly with `N` whereas dyadic cocone-normalized traces `(2⁻¹)^(n+1) * (2 * t) = (2⁻¹)^n * t`
  are strictly scale-invariant.
* **Phase V (The 7-Stage Acyclic Causal Poset `𝔍₁ ≺ 𝔍₂ ≺ ⋯ ≺ 𝔍₇`, Lemma 1, Theorems 1–4,
  and Master Synthesis)**.
-/

noncomputable section

namespace InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitPoset

open scoped Matrix BigOperators
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset
open InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume
open InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset
open InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
open InfoGeometry.Canonical.HestenesKreinGaussBonnetMonogenicPoset
open InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty
open CanonicalTwoSheetedInductiveColimit

universe u v

/-!
## 1. The 7-Stage Acyclic Causal Poset (`𝔍₁ ≺ 𝔍₂ ≺ ⋯ ≺ 𝔍₇`)
-/

/-- The 7-stage causal poset governing the Jaynesian Nilpotent Replacement of Infinitesimals,
Directed Scale-Refinement Poset, Upward Algebraic Preservation, Downward Conditional Expectation,
Inductive Colimit Continuum Quotient, Universal Colimit Differential/Curvature Transfer, and
Cocone Tracial Integration & Gauss–Bonnet Closure. -/
inductive JaynesianColimitStage : Type
  | J1_NilpotentReplacementOfInfinitesimals
  | J2_DirectedPosetOfFiniteOperatorAlgebras
  | J3_UpwardAlgebraicPreservation
  | J4_DownwardConditionalExpectation
  | J5_InductiveColimitContinuumQuotient
  | J6_UniversalColimitDifferentialCurvatureTransfer
  | J7_ColimitTracialIntegrationGaussBonnetClosure
  deriving DecidableEq, Repr, Inhabited

namespace JaynesianColimitStage

/-- Strictly monotone integer rank `0..6` witnessing the topological ordering of the 7 stages. -/
def rank : JaynesianColimitStage → ℕ
  | .J1_NilpotentReplacementOfInfinitesimals => 0
  | .J2_DirectedPosetOfFiniteOperatorAlgebras => 1
  | .J3_UpwardAlgebraicPreservation => 2
  | .J4_DownwardConditionalExpectation => 3
  | .J5_InductiveColimitContinuumQuotient => 4
  | .J6_UniversalColimitDifferentialCurvatureTransfer => 5
  | .J7_ColimitTracialIntegrationGaussBonnetClosure => 6

theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> revert h <;> decide

instance instLinearOrderJaynesianColimitStage : LinearOrder JaynesianColimitStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed edges of the 7-stage Jaynesian Colimit DAG:
`𝔍₁ → 𝔍₂`, the upward/downward scale-refinement diamond `𝔍₂ → 𝔍₃ → 𝔍₅` and `𝔍₂ → 𝔍₄ → 𝔍₅`,
and the colimit transfer chain `𝔍₅ → 𝔍₆ → 𝔍₇`. -/
def causalEdge : JaynesianColimitStage → JaynesianColimitStage → Prop
  | .J1_NilpotentReplacementOfInfinitesimals, .J2_DirectedPosetOfFiniteOperatorAlgebras => True
  | .J2_DirectedPosetOfFiniteOperatorAlgebras, .J3_UpwardAlgebraicPreservation => True
  | .J2_DirectedPosetOfFiniteOperatorAlgebras, .J4_DownwardConditionalExpectation => True
  | .J3_UpwardAlgebraicPreservation, .J4_DownwardConditionalExpectation => True
  | .J3_UpwardAlgebraicPreservation, .J5_InductiveColimitContinuumQuotient => True
  | .J4_DownwardConditionalExpectation, .J5_InductiveColimitContinuumQuotient => True
  | .J5_InductiveColimitContinuumQuotient, .J6_UniversalColimitDifferentialCurvatureTransfer => True
  | .J6_UniversalColimitDifferentialCurvatureTransfer,
    .J7_ColimitTracialIntegrationGaussBonnetClosure => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_strict_rank_mono {a b : JaynesianColimitStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem causalEdge_irrefl (a : JaynesianColimitStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

theorem transGen_causalEdge_strict_rank_mono {a b : JaynesianColimitStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hbc)

theorem causalEdge_acyclic (a : JaynesianColimitStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

theorem causalEdge_chain_and_diamond :
    causalEdge .J1_NilpotentReplacementOfInfinitesimals .J2_DirectedPosetOfFiniteOperatorAlgebras ∧
    causalEdge .J2_DirectedPosetOfFiniteOperatorAlgebras .J3_UpwardAlgebraicPreservation ∧
    causalEdge .J2_DirectedPosetOfFiniteOperatorAlgebras .J4_DownwardConditionalExpectation ∧
    causalEdge .J3_UpwardAlgebraicPreservation .J4_DownwardConditionalExpectation ∧
    causalEdge .J3_UpwardAlgebraicPreservation .J5_InductiveColimitContinuumQuotient ∧
    causalEdge .J4_DownwardConditionalExpectation .J5_InductiveColimitContinuumQuotient ∧
    causalEdge .J5_InductiveColimitContinuumQuotient
      .J6_UniversalColimitDifferentialCurvatureTransfer ∧
    causalEdge .J6_UniversalColimitDifferentialCurvatureTransfer
      .J7_ColimitTracialIntegrationGaussBonnetClosure := by
  decide

end JaynesianColimitStage

/-!
## 2. Phase IV / Rung 0: The Dual Aporia of Scalar Infinitesimals & Unnormalized Infinite Traces
-/

/-- **Rung 0 (The Dual Aporia of Scalar Infinitesimals & Unnormalized Infinite Traces)**:
1. *Scalar Infinitesimal Aporia*: In any domain `[Ring K] [IsDomain K]` (such as `ℝ` or `ℂ`),
   `dx * dx = 0 ↔ dx = 0`, so no non-zero scalar infinitesimal `dx ≠ 0 ∧ dx * dx = 0` exists.
2. *Non-Commutative Peirce Nilpotent Resolution*: In the non-commutative matrix ring
   `Matrix (Fin 2) (Fin 2) ℤ`, the off-diagonal Peirce cone `rnMatrixPlus` is strictly non-zero
   (`rnMatrixPlus ≠ 0`) while its square is identically zero (`rnMatrixPlus * rnMatrixPlus = 0`).
3. *Unnormalized vs. Cocone-Normalized Trace Scaling*: The unnormalized trace sum of `N` units
   equals `(N : ℝ)` and grows strictly (`(N : ℝ) < ((N + 1 : ℕ) : ℝ)`), whereas the dyadic
   cocone-normalized trace `(2 : ℝ)⁻¹ ^ (n + 1) * (2 * t) = (2 : ℝ)⁻¹ ^ n * t` is strictly
   scale-invariant across all `n : ℕ`. -/
theorem rung0_scalar_infinitesimal_and_unnormalized_trace_aporia
    {K : Type*} [Ring K] [IsDomain K] (dx : K) (N n : ℕ) (t : ℝ) :
    (dx * dx = 0 ↔ dx = 0) ∧
    ¬ (dx ≠ 0 ∧ dx * dx = 0) ∧
    (rnMatrixPlus ≠ 0 ∧ rnMatrixPlus * rnMatrixPlus = 0) ∧
    ((∑ _i ∈ Finset.range N, (1 : ℝ)) = (N : ℝ) ∧ (N : ℝ) < ((N + 1 : ℕ) : ℝ)) ∧
    ((2 : ℝ)⁻¹ ^ (n + 1) * (2 * t) = (2 : ℝ)⁻¹ ^ n * t) := by
  refine ⟨mul_self_eq_zero, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨hNe, hSq⟩
    exact hNe (mul_self_eq_zero.mp hSq)
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    norm_num [rnMatrixPlus] at h01
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rnMatrixPlus, Matrix.mul_apply]
  · simp
  · exact_mod_cast Nat.lt_succ_self N
  · rw [pow_succ]
    ring

/-- Explicit non-commutativity witness (`T16`) for the concrete `2 × 2` Peirce nilpotent matrices
`rnMatrixPlus` and `rnMatrixMinus`. -/
theorem jaynesian_matrix_noncommutative_witness :
    rnMatrixPlus * rnMatrixMinus ≠ rnMatrixMinus * rnMatrixPlus :=
  rnMatrix_noncommutative_and_schwarz_defect_ne_zero.1

/-!
## 3. Stage `𝔍₁` (Theorem 1): Exact First-Order Taylor Truncation Without Limits
-/

/-- Formal monomial derivative coefficient `j * c₀ ^ (j - 1)` for `t ^ j` at `c₀`. -/
def monomialDerivCoeff {R : Type*} [CommRing R] (c₀ : R) : ℕ → R
  | 0 => 0
  | j + 1 => ((j + 1 : ℕ) : R) * (c₀ ^ j)

/-- Product-rule recurrence for `monomialDerivCoeff`:
`monomialDerivCoeff c₀ (j + 1) = c₀ ^ j + monomialDerivCoeff c₀ j * c₀`. -/
theorem monomialDerivCoeff_succ {R : Type*} [CommRing R] (c₀ : R) (j : ℕ) :
    monomialDerivCoeff c₀ (j + 1) = c₀ ^ j + monomialDerivCoeff c₀ j * c₀ := by
  cases j with
  | zero =>
    simp [monomialDerivCoeff]
  | succ k =>
    simp only [monomialDerivCoeff, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- Exact first-order binomial expansion along any square-zero operator `N * N = 0`:
`(c₀ • 1 + N) ^ j = c₀ ^ j • 1 + (j * c₀ ^ (j - 1)) • N`. -/
theorem nilpotent_binomial_first_order
    {R : Type*} [CommRing R] {B : Type*} [Ring B] [Algebra R B]
    (c₀ : R) (N : B) (hN : N * N = 0) (j : ℕ) :
    (algebraMap R B c₀ + N) ^ j =
      algebraMap R B (c₀ ^ j) + algebraMap R B (monomialDerivCoeff c₀ j) * N := by
  induction j with
  | zero =>
    simp [monomialDerivCoeff]
  | succ j ih =>
    rw [pow_succ, ih, monomialDerivCoeff_succ, pow_succ, map_add, map_mul, map_mul]
    have hcN : N * algebraMap R B c₀ = algebraMap R B c₀ * N :=
      (Algebra.commutes c₀ N).symm
    calc
      (algebraMap R B (c₀ ^ j) + algebraMap R B (monomialDerivCoeff c₀ j) * N) *
          (algebraMap R B c₀ + N)
          = algebraMap R B (c₀ ^ j) * algebraMap R B c₀ +
            algebraMap R B (c₀ ^ j) * N +
            algebraMap R B (monomialDerivCoeff c₀ j) * (N * algebraMap R B c₀) +
            algebraMap R B (monomialDerivCoeff c₀ j) * (N * N) := by noncomm_ring
      _ = algebraMap R B (c₀ ^ j) * algebraMap R B c₀ +
            (algebraMap R B (c₀ ^ j) +
              algebraMap R B (monomialDerivCoeff c₀ j) * algebraMap R B c₀) * N := by
            rw [hcN, hN, mul_zero, add_zero]
            noncomm_ring

/-- Scalar evaluation `F(c₀) = ∑_{j=0}^d c_j c₀^j` of a degree-`d` polynomial with coefficients `c`. -/
def polyEvalScalar {R : Type*} [CommRing R] (c : ℕ → R) (d : ℕ) (c₀ : R) : R :=
  ∑ j ∈ Finset.range (d + 1), c j * (c₀ ^ j)

/-- Formal scalar derivative `F'(c₀) = ∑_{j=0}^d c_j j c₀^{j-1}` of a degree-`d` polynomial. -/
def polyDerivScalar {R : Type*} [CommRing R] (c : ℕ → R) (d : ℕ) (c₀ : R) : R :=
  ∑ j ∈ Finset.range (d + 1), c j * monomialDerivCoeff c₀ j

/-- Operator evaluation `F(X) = ∑_{j=0}^d c_j X^j` in an `R`-algebra `B`. -/
def polyEvalOp {R : Type*} [CommRing R] {B : Type*} [Ring B] [Algebra R B]
    (c : ℕ → R) (d : ℕ) (X : B) : B :=
  ∑ j ∈ Finset.range (d + 1), algebraMap R B (c j) * (X ^ j)

/-- **Theorem 1 (Exact First-Order Taylor Truncation Without Limits, Stage `𝔍₁`)**:
For any idempotent `P * P = P` in an `R`-algebra `[Ring B] [Algebra R B]`, the off-diagonal
Peirce nilpotents `N_+ = conePlus P A` and `N_- = coneMinus P C` satisfy:
1. `N_+ * N_+ = 0` and `N_- * N_- = 0`;
2. Every monomial `(c₀ • 1 + N_+) ^ j` truncates identically at first order:
   `(algebraMap R B c₀ + N_+) ^ j = algebraMap R B (c₀ ^ j) + algebraMap R B (monomialDerivCoeff c₀ j) * N_+`;
3. Every polynomial `F(t) = ∑_{j=0}^d c_j t^j` evaluated at `c₀ • 1 + N_+` truncates
   identically at first order with zero remainder and zero limits:
   `F(c₀ • 1 + N_+) = F(c₀) • 1 + F'(c₀) • N_+`;
4. Simultaneously exciting both chiral nilpotents `Φ = N_+ + N_-` generates the exact second-order
   Casimir metric `Φ * Φ = V` (`(1 + Φ)² = 1 + 2 • Φ + V`). -/
theorem theorem1_exact_first_order_taylor_truncation
    {R : Type*} [CommRing R] {B : Type*} [Ring B] [Algebra R B]
    (P A C : B) (hP : P * P = P) (c : ℕ → R) (d j : ℕ) (c₀ : R) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    (algebraMap R B c₀ + conePlus P A) ^ j =
      algebraMap R B (c₀ ^ j) + algebraMap R B (monomialDerivCoeff c₀ j) * conePlus P A ∧
    polyEvalOp c d (algebraMap R B c₀ + conePlus P A) =
      algebraMap R B (polyEvalScalar c d c₀) +
        algebraMap R B (polyDerivScalar c d c₀) * conePlus P A ∧
    (1 + genPhi P A C) * (1 + genPhi P A C) =
      1 + (2 : ℤ) • genPhi P A C + genV P A C := by
  have hNplus : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have hNminus : coneMinus P C * coneMinus P C = 0 := by peirce_nf hP
  refine ⟨hNplus, hNminus, nilpotent_binomial_first_order c₀ (conePlus P A) hNplus j, ?_, ?_⟩
  · unfold polyEvalOp polyEvalScalar polyDerivScalar
    rw [map_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nilpotent_binomial_first_order c₀ (conePlus P A) hNplus m, map_mul, map_mul]
    noncomm_ring
  · have hPhiSq : genPhi P A C * genPhi P A C = genV P A C :=
      (peirce_dirac_krein_identities P A C hP).2.2.1
    calc
      (1 + genPhi P A C) * (1 + genPhi P A C)
          = 1 + (genPhi P A C + genPhi P A C) + genPhi P A C * genPhi P A C := by noncomm_ring
      _ = 1 + (2 : ℤ) • genPhi P A C + genV P A C := by rw [← two_zsmul, hPhiSq]

/-!
## 4. Stages `𝔍₂`, `𝔍₃`, `𝔍₄` (Lemma 1): Directed Scale-Refinement System, Functorial Spine Invariance, & Retraction Hypothesis
-/

/-- A directed system of unital star-ring homomorphisms `ι_{m,n} : A m →⋆+* A n` (`m ≤ n`)
over `(ℕ, ≤)`. -/
structure DirectedStarRingSystem (A : ℕ → Type u) [∀ n, Ring (A n)] [∀ n, StarRing (A n)] where
  hom : ∀ m n : ℕ, m ≤ n → StarRingHom (A m) (A n)
  hom_refl : ∀ n (x : A n), (hom n n (le_refl n)).toFun x = x
  hom_trans : ∀ l m n (hlm : l ≤ m) (hmn : m ≤ n) (x : A l),
    (hom m n hmn).toFun ((hom l m hlm).toFun x) =
      (hom l n (le_trans hlm hmn)).toFun x

/-- Forgetting the star structure turns the transition maps of a directed star-ring system into
Mathlib's `DirectedSystem` data. -/
instance instMathlibDirectedSystem
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) :
    DirectedSystem A (fun m n h => (Sys.hom m n h).toRingHom) where
  map_self := fun {n} x => Sys.hom_refl n x
  map_map := fun {k j i} hij hjk x => Sys.hom_trans i j k hij hjk x

/-- Canonical constant-fiber inhabitant of `DirectedStarRingSystem` for any star-ring `B`. -/
def constantDirectedStarRingSystem (B : Type u) [Ring B] [StarRing B] :
    DirectedStarRingSystem (fun _ : ℕ => B) where
  hom _ _ _ := StarRingHom.id B
  hom_refl _ _ := rfl
  hom_trans _ _ _ _ _ _ := rfl

instance instInhabitedDirectedStarRingSystem (B : Type u) [Ring B] [StarRing B] :
    Inhabited (DirectedStarRingSystem (fun _ : ℕ => B)) :=
  ⟨constantDirectedStarRingSystem B⟩

/-- **Lemma 1 (Functorial Invariance of the Peirce–Cartan Spine & Downward Chiral Filter
Asymmetry, Stages `𝔍₂ → 𝔍₃, 𝔍₄`)**:
Let `Sys : DirectedStarRingSystem A` and `m ≤ n` (`hmn : m ≤ n`), and let
`ι := (Sys.hom m n hmn).toRingHom`:
1. If `P_m * P_m = P_m`, then `(ι P_m) * (ι P_m) = ι P_m`.
2. `ι` commutes identically with the Peirce involution `invS`, the nilpotent cones
   `conePlus`/`coneMinus`, the Dirac/Krein generators `genPhi`/`genJ`, the Casimir metric `genV`,
   and the symplectic spin curvature `genSig`.
3. Given any function `E_n : A (n + 1) → A n` satisfying the retraction equation
   (`∀ x, E_n ((Sys.hom n (n + 1) (Nat.le_succ n)).toFun x) = x`), it recovers embedded coarse operators.
   No conditional-expectation axioms are assumed. Independently, at stage `m` the chiral grade-0 projection
   `evenGrade P_m` kills the odd generators `genPhi` and `genJ` (`evenGrade P_m Φ_m = 0`,
   `evenGrade P_m J_m = 0`) yet preserves the quadratic Casimir metric (`evenGrade P_m V_m = V_m`). -/
theorem lemma1_functorial_invariance_and_chiral_expectation
    {A : ℕ → Type u} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    (Sys : DirectedStarRingSystem A) {m n : ℕ} (hmn : m ≤ n)
    (P_m A_m C_m X_m : A m) (hP_m : P_m * P_m = P_m)
    (E_n : A (n + 1) → A n)
    (hRetract : ∀ y : A n, E_n ((Sys.hom n (n + 1) (Nat.le_succ n)).toFun y) = y) (y_n : A n) :
    let ι := (Sys.hom m n hmn).toRingHom
    (ι P_m) * (ι P_m) = ι P_m ∧
    ι (invS P_m) = invS (ι P_m) ∧
    ι (conePlus P_m A_m) = conePlus (ι P_m) (ι A_m) ∧
    ι (coneMinus P_m C_m) = coneMinus (ι P_m) (ι C_m) ∧
    ι (genPhi P_m A_m C_m) = genPhi (ι P_m) (ι A_m) (ι C_m) ∧
    ι (genJ P_m A_m C_m) = genJ (ι P_m) (ι A_m) (ι C_m) ∧
    ι (genV P_m A_m C_m) = genV (ι P_m) (ι A_m) (ι C_m) ∧
    ι (genSig P_m A_m C_m) = genSig (ι P_m) (ι A_m) (ι C_m) ∧
    E_n ((Sys.hom n (n + 1) (Nat.le_succ n)).toFun y_n) = y_n ∧
    evenGrade P_m (genPhi P_m A_m C_m) = 0 ∧
    evenGrade P_m (genJ P_m A_m C_m) = 0 ∧
    evenGrade P_m (genV P_m A_m C_m) = genV P_m A_m C_m := by
  intro ι
  have hInter :=
    starRingHom_intertwines_two_sheeted_tower
      (Sys.hom m n hmn).toRingHom (Sys.hom m n hmn).map_star' P_m A_m C_m X_m
  rcases hInter with ⟨hBit, hZig, hZag, hElec, hAxial, hMass, hSpin, _, _⟩
  have hP_n : (ι P_m) * (ι P_m) = ι P_m := by
    rw [← map_mul, hP_m]
  refine ⟨hP_n, hBit, hZig, hZag, hElec, hAxial, hMass, hSpin, hRetract y_n, ?_, ?_, ?_⟩
  · peirce_nf hP_m
  · peirce_nf hP_m
  · peirce_nf hP_m

/-!
## 5. Stage `𝔍₅` (Theorem 2): The Inductive Colimit Quotient (`ColimitRel` & `JaynesianColimitCarrier`)
-/

/-- The Jaynesian directed colimit equivalence relation on the disjoint union `Σ n : ℕ, A n`:
`(m, X_m) ~ (n, Y_n)` iff there exists a common refinement stage `k ≥ m, n` at which
`ι_{m,k}(X_m) = ι_{n,k}(Y_n)`. -/
def ColimitRel {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) (x y : Σ n : ℕ, A n) : Prop :=
  ∃ (k : ℕ) (hx : x.1 ≤ k) (hy : y.1 ≤ k),
    (Sys.hom x.1 k hx).toFun x.2 = (Sys.hom y.1 k hy).toFun y.2

theorem colimitRel_refl {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) (x : Σ n : ℕ, A n) :
    ColimitRel Sys x x :=
  ⟨x.1, le_refl x.1, le_refl x.1, rfl⟩

theorem colimitRel_symm {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) {x y : Σ n : ℕ, A n}
    (h : ColimitRel Sys x y) : ColimitRel Sys y x := by
  rcases h with ⟨k, hx, hy, hEq⟩
  exact ⟨k, hy, hx, hEq.symm⟩

theorem colimitRel_trans {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) {x y z : Σ n : ℕ, A n}
    (hxy : ColimitRel Sys x y) (hyz : ColimitRel Sys y z) :
    ColimitRel Sys x z := by
  rcases hxy with ⟨k₁, hx₁, hy₁, hEq₁⟩
  rcases hyz with ⟨k₂, hy₂, hz₂, hEq₂⟩
  refine ⟨max k₁ k₂, le_trans hx₁ (le_max_left k₁ k₂), le_trans hz₂ (le_max_right k₁ k₂), ?_⟩
  have hk₁ : k₁ ≤ max k₁ k₂ := le_max_left k₁ k₂
  have hk₂ : k₂ ≤ max k₁ k₂ := le_max_right k₁ k₂
  calc
    (Sys.hom x.1 (max k₁ k₂) (le_trans hx₁ hk₁)).toFun x.2
        = (Sys.hom k₁ (max k₁ k₂) hk₁).toFun ((Sys.hom x.1 k₁ hx₁).toFun x.2) :=
          (Sys.hom_trans x.1 k₁ (max k₁ k₂) hx₁ hk₁ x.2).symm
    _ = (Sys.hom k₁ (max k₁ k₂) hk₁).toFun ((Sys.hom y.1 k₁ hy₁).toFun y.2) := by rw [hEq₁]
    _ = (Sys.hom y.1 (max k₁ k₂) (le_trans hy₁ hk₁)).toFun y.2 :=
          Sys.hom_trans y.1 k₁ (max k₁ k₂) hy₁ hk₁ y.2
    _ = (Sys.hom k₂ (max k₁ k₂) hk₂).toFun ((Sys.hom y.1 k₂ hy₂).toFun y.2) :=
          (Sys.hom_trans y.1 k₂ (max k₁ k₂) hy₂ hk₂ y.2).symm
    _ = (Sys.hom k₂ (max k₁ k₂) hk₂).toFun ((Sys.hom z.1 k₂ hz₂).toFun z.2) := by rw [hEq₂]
    _ = (Sys.hom z.1 (max k₁ k₂) (le_trans hz₂ hk₂)).toFun z.2 :=
          Sys.hom_trans z.1 k₂ (max k₁ k₂) hz₂ hk₂ z.2

/-- The setoid on `Σ n : ℕ, A n` induced by `ColimitRel Sys`. -/
def colimitSetoid {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) : Setoid (Σ n : ℕ, A n) where
  r := ColimitRel Sys
  iseqv := ⟨colimitRel_refl Sys, colimitRel_symm Sys, colimitRel_trans Sys⟩

/-- A quotient carrier on representatives modulo eventual equality. This definition alone does
not equip the quotient with ring operations or establish a colimit universal property. -/
def JaynesianColimitCarrier {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) : Type u :=
  Quotient (colimitSetoid Sys)

/-- Canonical stage injection `of_n : A n → JaynesianColimitCarrier Sys`. -/
def colimitOf {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) (n : ℕ) (x : A n) :
    JaynesianColimitCarrier Sys :=
  Quotient.mk (colimitSetoid Sys) ⟨n, x⟩

/-- The eventual-equality quotient carrier is equivalent to Mathlib's directed `DirectLimit`
for the same system. This identifies the set-level quotient with Mathlib's carrier, which has
the ring structure and universal maps; those structures are not defined on
`JaynesianColimitCarrier` itself. -/
noncomputable def jaynesianCarrierEquivMathlibDirectLimit
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) :
    JaynesianColimitCarrier Sys ≃
      DirectLimit A (fun m n h => (Sys.hom m n h).toRingHom) := by
  let f : ∀ m n, m ≤ n → A m →+* A n := fun m n h => (Sys.hom m n h).toRingHom
  refine
    { toFun := Quotient.lift
        (fun z : Σ n : ℕ, A n => DirectLimit.Ring.of A f z.1 z.2) ?_
      invFun := DirectLimit.lift f (fun n x => colimitOf Sys n x) ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro x y hxy
    rcases hxy with ⟨k, hx, hy, hEq⟩
    have hEq' : f x.1 k hx x.2 = f y.1 k hy y.2 := hEq
    calc
      DirectLimit.Ring.of A f x.1 x.2 =
          DirectLimit.Ring.of A f k (f x.1 k hx x.2) :=
            (DirectLimit.Ring.of_f hx x.2).symm
      _ = DirectLimit.Ring.of A f k (f y.1 k hy y.2) := by rw [hEq']
      _ = DirectLimit.Ring.of A f y.1 y.2 := DirectLimit.Ring.of_f hy y.2
  · intro m n hmn x
    apply Eq.symm
    apply Quotient.sound
    exact ⟨n, le_refl n, hmn, Sys.hom_refl n ((Sys.hom m n hmn).toFun x)⟩
  · intro q
    induction q using Quotient.inductionOn with
    | _ z => rfl
  · intro z
    induction z using DirectLimit.induction with
    | _ n x => rfl

/-- The quotient-to-direct-limit equivalence sends each finite-stage representative to the
canonical Mathlib direct-limit injection. -/
@[simp] theorem jaynesianCarrierEquivMathlibDirectLimit_of
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) (n : ℕ) (x : A n) :
    jaynesianCarrierEquivMathlibDirectLimit Sys (colimitOf Sys n x) =
      DirectLimit.Ring.of A (fun m k h => (Sys.hom m k h).toRingHom) n x := rfl

/-- The inverse equivalence sends each Mathlib direct-limit injection back to the corresponding
quotient representative. -/
@[simp] theorem jaynesianCarrierEquivMathlibDirectLimit_symm_of
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) (n : ℕ) (x : A n) :
    (jaynesianCarrierEquivMathlibDirectLimit Sys).symm
      (DirectLimit.Ring.of A (fun m k h => (Sys.hom m k h).toRingHom) n x) =
        colimitOf Sys n x := rfl

/-- **Theorem 2 (Equivalence Relation & Cocone Invariance of the Quotient Carrier,
Stage `𝔍₅`)**:
1. `ColimitRel Sys` is reflexive, symmetric, and transitive;
2. The canonical stage maps `colimitOf Sys n` form a compatible cocone over `Sys`:
   for every `m ≤ n` (`hmn : m ≤ n`) and `x : A m`,
   `colimitOf Sys n (Sys.hom m n hmn x) = colimitOf Sys m x`;
3. Pushing the Peirce–Cartan invariants `(invS, genPhi, genJ, genV, genSig)` from stage `m` to
   stage `n` represents the exact same element in the colimit quotient `JaynesianColimitCarrier Sys`. -/
theorem theorem2_colimitRel_equivalence_and_cocone_invariance
    {A : ℕ → Type u} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    (Sys : DirectedStarRingSystem A) {m n : ℕ} (hmn : m ≤ n)
    (P_m A_m C_m x_m : A m) :
    let ι := (Sys.hom m n hmn).toRingHom
    Equivalence (ColimitRel Sys) ∧
    colimitOf Sys n ((Sys.hom m n hmn).toFun x_m) = colimitOf Sys m x_m ∧
    colimitOf Sys n (genPhi (ι P_m) (ι A_m) (ι C_m)) =
      colimitOf Sys m (genPhi P_m A_m C_m) ∧
    colimitOf Sys n (genV (ι P_m) (ι A_m) (ι C_m)) =
      colimitOf Sys m (genV P_m A_m C_m) ∧
    colimitOf Sys n (genSig (ι P_m) (ι A_m) (ι C_m)) =
      colimitOf Sys m (genSig P_m A_m C_m) := by
  intro ι
  have hCocone : ∀ y : A m, colimitOf Sys n ((Sys.hom m n hmn).toFun y) = colimitOf Sys m y := by
    intro y
    apply Quotient.sound
    refine ⟨n, le_refl n, hmn, ?_⟩
    exact Sys.hom_refl n ((Sys.hom m n hmn).toFun y)
  have hInter :=
    starRingHom_intertwines_two_sheeted_tower
      (Sys.hom m n hmn).toRingHom (Sys.hom m n hmn).map_star' P_m A_m C_m x_m
  rcases hInter with ⟨_, _, _, hElec, _, hMass, hSpin, _, _⟩
  have hPhi : ι (genPhi P_m A_m C_m) = genPhi (ι P_m) (ι A_m) (ι C_m) := by
    simpa [opElectron] using hElec
  have hV : ι (genV P_m A_m C_m) = genV (ι P_m) (ι A_m) (ι C_m) := by
    simpa [opQuadraticCoupling] using hMass
  have hSig : ι (genSig P_m A_m C_m) = genSig (ι P_m) (ι A_m) (ι C_m) := by
    simpa [opSpinDipole] using hSpin
  refine ⟨⟨colimitRel_refl Sys, colimitRel_symm Sys, colimitRel_trans Sys⟩,
    hCocone x_m, ?_, ?_, ?_⟩
  · rw [← hPhi]
    exact hCocone (genPhi P_m A_m C_m)
  · rw [← hV]
    exact hCocone (genV P_m A_m C_m)
  · rw [← hSig]
    exact hCocone (genSig P_m A_m C_m)

/-!
## 6. Stages `𝔍₆` & `𝔍₇` (Theorems 3 & 4): Conditional Ring-Cone Transfer & a Cocone-Valued Function
-/

/-- **Theorem 3 (Conditional Transfer to a Supplied Ring-Valued Cone,
Stage `𝔍₆`)**:
For any `InductiveStarColimitCone A A_inf` (`Cone`), any finite resolution stage `n : ℕ`, any
`m : ℕ` refinement steps, and any idempotent `P_n * P_n = P_n` in `A n`:
let `ι_n := (Cone.toColimit n).toRingHom`, `P_inf := ι_n P_n`, `A_inf_el := ι_n A_n`,
`C_inf_el := ι_n C_n`, `Φ_inf := genPhi P_inf A_inf_el C_inf_el`,
`J_inf := genJ P_inf A_inf_el C_inf_el`, `V_inf := genV P_inf A_inf_el C_inf_el`,
`Sig_inf := genSig P_inf A_inf_el C_inf_el`, and `S_inf := invS P_inf`:
1. *Multi-step scale-refinement invariance (`n → n + m → ∞`)*:
   `(Cone.toColimit (n + m)).toRingHom (genV (ψ_m P_n) (ψ_m A_n) (ψ_m C_n)) = V_inf` and
   `(Cone.toColimit (n + m)).toRingHom (genSig (ψ_m P_n) (ψ_m A_n) (ψ_m C_n)) = Sig_inf`;
2. *Continuum Split-Clifford & Curvature Identities*:
   `Φ_inf * Φ_inf = V_inf`, `J_inf * J_inf = -V_inf`, `comm Φ_inf J_inf = -(2 : ℤ) • Sig_inf`,
   and `S_inf * comm Φ_inf J_inf = -(2 : ℤ) • V_inf`;
3. *Continuum Master `1 : (-2)` Modular Clocking Lock*:
   `-comm Φ_inf (comm Φ_inf J_inf) = -(2 : ℤ) • comm Sig_inf Φ_inf` and
   `-(2 : ℤ) • comm Sig_inf Φ_inf = -(4 : ℤ) • (V_inf * J_inf)`;
4. *Continuum Universal McKean–Singer Commutator Identity*:
   `comm J_inf (Φ_inf ^ (2 * k + 1)) = (2 : ℤ) • (S_inf * (V_inf ^ (k + 1)))`.
The cone and its target ring are inputs; this theorem does not prove that the target is a
categorical colimit, and the algebraic commutator statement is not a Gauss–Bonnet theorem. -/
theorem theorem3_colimit_einstein_cartan_clocking_gauss_bonnet_transfer
    {A : ℕ → Type u} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type v} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (n m k : ℕ) (P_n A_n C_n : A n) (hP_n : P_n * P_n = P_n) :
    let ψ_m := (stepHomIter Cone n m).toRingHom
    let ι_nm := (Cone.toColimit (n + m)).toRingHom
    let ι_n := (Cone.toColimit n).toRingHom
    let P_inf := ι_n P_n
    let A_inf_el := ι_n A_n
    let C_inf_el := ι_n C_n
    let Φ_inf := genPhi P_inf A_inf_el C_inf_el
    let J_inf := genJ P_inf A_inf_el C_inf_el
    let V_inf := genV P_inf A_inf_el C_inf_el
    let Sig_inf := genSig P_inf A_inf_el C_inf_el
    let S_inf := invS P_inf
    ι_nm (genV (ψ_m P_n) (ψ_m A_n) (ψ_m C_n)) = V_inf ∧
    ι_nm (genSig (ψ_m P_n) (ψ_m A_n) (ψ_m C_n)) = Sig_inf ∧
    Φ_inf * Φ_inf = V_inf ∧
    J_inf * J_inf = -V_inf ∧
    OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf = -(2 : ℤ) • Sig_inf ∧
    S_inf * OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf = -(2 : ℤ) • V_inf ∧
    -OperatorAlgebra.PeirceSpine.comm Φ_inf (OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf) =
      -(2 : ℤ) • OperatorAlgebra.PeirceSpine.comm Sig_inf Φ_inf ∧
    -(2 : ℤ) • OperatorAlgebra.PeirceSpine.comm Sig_inf Φ_inf = -(4 : ℤ) • (V_inf * J_inf) ∧
    OperatorAlgebra.PeirceSpine.comm J_inf (Φ_inf ^ (2 * k + 1)) =
      (2 : ℤ) • (S_inf * (V_inf ^ (k + 1))) := by
  intro ψ_m ι_nm ι_n P_inf A_inf_el C_inf_el Φ_inf J_inf V_inf Sig_inf S_inf
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf, ι_n]; rw [← map_mul, hP_n]
  have hRG := colimit_renormalization_scale_invariance Cone n m P_n A_n C_n 0
  rcases hRG with ⟨_, hRG_V, hRG_Sig, _, _, _, _, _, _, _⟩
  have hIds := peirce_dirac_krein_identities P_inf A_inf_el C_inf_el hP_inf
  have hMcKean :=
    (theorem4_universal_mckean_singer_commutator_identity
      P_inf A_inf_el C_inf_el 1 hP_inf k (by noncomm_ring) (by noncomm_ring)).1
  dsimp [Φ_inf, J_inf, V_inf, Sig_inf, S_inf] at hIds hMcKean ⊢
  refine ⟨hRG_V, hRG_Sig, hIds.2.2.1, hIds.2.2.2.1, hIds.2.2.2.2.1, ?_, ?_, ?_, hMcKean⟩
  · peirce_nf hP_inf
  · peirce_nf hP_inf
  · peirce_nf hP_inf

/-- The well-defined function `JaynesianColimitCarrier Sys → K` induced by a compatible family
`τ : ∀ n, A n → K` (`τ n (ι_{m,n} x) = τ m x`). Additivity, cyclicity, positivity, and any
interpretation as an integral require additional hypotheses and are not part of this definition. -/
def colimitTraceLift
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    {K : Type v}
    (Sys : DirectedStarRingSystem A)
    (τ : ∀ n, A n → K)
    (hcompat : ∀ m n (hmn : m ≤ n) (x : A m), τ n ((Sys.hom m n hmn).toFun x) = τ m x) :
    JaynesianColimitCarrier Sys → K :=
  Quotient.lift (fun s : Σ n : ℕ, A n => τ s.1 s.2) (by
    intro x y hxy
    rcases hxy with ⟨k, hx, hy, hEq⟩
    calc
      τ x.1 x.2 = τ k ((Sys.hom x.1 k hx).toFun x.2) := (hcompat x.1 k hx x.2).symm
      _ = τ k ((Sys.hom y.1 k hy).toFun y.2) := by rw [hEq]
      _ = τ y.1 y.2 := hcompat y.1 k hy y.2)

/-- **Theorem 4 (Cocone-Valued Function, Separate Cyclic-Trace Cancellation, &
Metriplectic Cramér–Rao Closure, Stage `𝔍₇`)**:
1. The function `colimitTraceLift Sys τ hcompat` agrees identically with `τ n` on every
   finite stage representative (`colimitTraceLift Sys τ hcompat (colimitOf Sys n x) = τ n x`)
   and is invariant under scale refinement (`m ≤ n`). The construction assumes only a
   type-valued compatible family; it establishes no additivity, cyclicity, positivity, or
   integration properties;
2. Separately, for any ring `A_inf` (`[Ring A_inf] [Algebra ℝ A_inf]`) equipped with a
   cyclic trace `tr_inf : A_inf →ₗ[ℝ] ℝ` (`∀ X Y, tr_inf (X * Y) = tr_inf (Y * X)`), the continuum
   chiral supertrace of every positive Casimir power vanishes:
   `chiralSupertrace tr_inf P_inf (V_inf ^ (k + 1)) = 0`. This trace is separately supplied on
   the target ring and is not descended from `τ` by this theorem;
3. For any normalized state `ψ` and bounded observables `X_op, Y_op`, the Metriplectic Cramér–Rao
   bound holds identically:
   `g(X_op, X_op) * g(Y_op, Y_op) ≥ g(X_op, Y_op)² + (1 / 4) * Ω(X_op, Y_op)²`. -/
theorem theorem4_colimit_tracial_cocone_and_gauss_bonnet_supertrace
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    {K : Type v}
    (Sys : DirectedStarRingSystem A)
    (τ : ∀ n, A n → K)
    (hcompat : ∀ m n (hmn : m ≤ n) (x : A m), τ n ((Sys.hom m n hmn).toFun x) = τ m x)
    {m n : ℕ} (hmn : m ≤ n) (x_m : A m) (x_n : A n)
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf] [Algebra ℝ A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (tr_inf : A_inf →ₗ[ℝ] ℝ) (htr_inf : ∀ X Y : A_inf, tr_inf (X * Y) = tr_inf (Y * X))
    (P_n A_n C_n : A n) (hP_n : P_n * P_n = P_n) (k : ℕ)
    {H_hilb : Type*} [NormedAddCommGroup H_hilb] [InnerProductSpace ℂ H_hilb]
    [CompleteSpace H_hilb]
    (ψ : InfoGeometry.QuantumGeometry.Projective.NormalizedState H_hilb)
    (X_op Y_op : H_hilb →L[ℂ] H_hilb) :
    let ι_n := (Cone.toColimit n).toRingHom
    let P_inf := ι_n P_n
    let V_inf := genV P_inf (ι_n A_n) (ι_n C_n)
    colimitTraceLift Sys τ hcompat (colimitOf Sys n x_n) = τ n x_n ∧
    colimitTraceLift Sys τ hcompat (colimitOf Sys n ((Sys.hom m n hmn).toFun x_m)) = τ m x_m ∧
    chiralSupertrace tr_inf P_inf (V_inf ^ (k + 1)) = 0 ∧
    onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
      (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
        (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 := by
  intro ι_n P_inf V_inf
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf, ι_n]; rw [← map_mul, hP_n]
  refine ⟨rfl, hcompat m n hmn x_m,
    chiralSupertrace_genV_pow_succ_eq_zero tr_inf htr_inf P_inf (ι_n A_n) (ι_n C_n) hP_inf k,
    cramerRao_metriplectic_full_bound ψ X_op Y_op⟩

/-!
## 7. Master Structural Synthesis (`𝔍₁ ≺ 𝔍₂ ≺ ⋯ ≺ 𝔍₇`)
-/

/-- **Master Jaynesian Nilpotent Calculus & Quotient-Carrier Synthesis
(`𝔍₁ ≺ 𝔍₂ ≺ ⋯ ≺ 𝔍₇`)**:
Unifies the 7-stage Jaynesian DAG ordering, the scalar infinitesimal aporia vs. non-commutative
nilpotent resolution, the exact first-order polynomial Taylor truncation without limits
`F(c₀ • 1 + N_+) = F(c₀) • 1 + F'(c₀) • N_+`, the eventual-equality quotient relation and
cocone invariance, conditional transfer of the Master `1 : (-2)` Clocking Lock and
McKean–Singer commutator identity to a supplied ring-valued cone, a separately supplied cyclic
trace cancellation, and the independent Metriplectic Cramér–Rao bound. This synthesis proves no
analytic continuum construction or Gauss–Bonnet theorem. -/
theorem master_jaynesian_nilpotent_inductive_colimit_synthesis
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    {K : Type v}
    (Sys : DirectedStarRingSystem A)
    (τ : ∀ n, A n → K)
    (hcompat : ∀ m n (hmn : m ≤ n) (x : A m), τ n ((Sys.hom m n hmn).toFun x) = τ m x)
    {m n : ℕ} (hmn : m ≤ n) (x_m : A m) (x_n : A n)
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf] [Algebra ℝ A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (tr_inf : A_inf →ₗ[ℝ] ℝ) (htr_inf : ∀ X Y : A_inf, tr_inf (X * Y) = tr_inf (Y * X))
    (P_n A_n C_n : A n) (hP_n : P_n * P_n = P_n)
    (c : ℕ → ℝ) (d k : ℕ) (c₀ : ℝ)
    {H_hilb : Type*} [NormedAddCommGroup H_hilb] [InnerProductSpace ℂ H_hilb]
    [CompleteSpace H_hilb]
    (ψ : InfoGeometry.QuantumGeometry.Projective.NormalizedState H_hilb)
    (X_op Y_op : H_hilb →L[ℂ] H_hilb) :
    let ι_n := (Cone.toColimit n).toRingHom
    let P_inf := ι_n P_n
    let A_inf_el := ι_n A_n
    let C_inf_el := ι_n C_n
    let Φ_inf := genPhi P_inf A_inf_el C_inf_el
    let J_inf := genJ P_inf A_inf_el C_inf_el
    let V_inf := genV P_inf A_inf_el C_inf_el
    let Sig_inf := genSig P_inf A_inf_el C_inf_el
    let S_inf := invS P_inf
    (∀ s : JaynesianColimitStage, ¬ Relation.TransGen JaynesianColimitStage.causalEdge s s) ∧
    (rnMatrixPlus ≠ 0 ∧ rnMatrixPlus * rnMatrixPlus = 0) ∧
    polyEvalOp c d (algebraMap ℝ A_inf c₀ + conePlus P_inf A_inf_el) =
      algebraMap ℝ A_inf (polyEvalScalar c d c₀) +
        algebraMap ℝ A_inf (polyDerivScalar c d c₀) * conePlus P_inf A_inf_el ∧
    colimitOf Sys n ((Sys.hom m n hmn).toFun x_m) = colimitOf Sys m x_m ∧
    -OperatorAlgebra.PeirceSpine.comm Φ_inf (OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf) =
      -(2 : ℤ) • OperatorAlgebra.PeirceSpine.comm Sig_inf Φ_inf ∧
    -(2 : ℤ) • OperatorAlgebra.PeirceSpine.comm Sig_inf Φ_inf = -(4 : ℤ) • (V_inf * J_inf) ∧
    OperatorAlgebra.PeirceSpine.comm J_inf (Φ_inf ^ (2 * k + 1)) =
      (2 : ℤ) • (S_inf * (V_inf ^ (k + 1))) ∧
    colimitTraceLift Sys τ hcompat (colimitOf Sys n x_n) = τ n x_n ∧
    chiralSupertrace tr_inf P_inf (V_inf ^ (k + 1)) = 0 ∧
    onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
      (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
        (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 := by
  intro ι_n P_inf A_inf_el C_inf_el Φ_inf J_inf V_inf Sig_inf S_inf
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf, ι_n]; rw [← map_mul, hP_n]
  have hRung0 := rung0_scalar_infinitesimal_and_unnormalized_trace_aporia (0 : ℝ) 0 0 0
  have hTaylor := theorem1_exact_first_order_taylor_truncation P_inf A_inf_el C_inf_el hP_inf
    c d 0 c₀
  have hCocone := theorem2_colimitRel_equivalence_and_cocone_invariance Sys hmn x_m x_m x_m x_m
  have hTrans := theorem3_colimit_einstein_cartan_clocking_gauss_bonnet_transfer
    Cone n 0 k P_n A_n C_n hP_n
  have hTr := theorem4_colimit_tracial_cocone_and_gauss_bonnet_supertrace
    Sys τ hcompat hmn x_m x_n Cone tr_inf htr_inf P_n A_n C_n hP_n k ψ X_op Y_op
  exact ⟨JaynesianColimitStage.causalEdge_acyclic,
    hRung0.2.2.1, hTaylor.2.2.2.1, hCocone.2.1,
    hTrans.2.2.2.2.2.2.1, hTrans.2.2.2.2.2.2.2.1, hTrans.2.2.2.2.2.2.2.2,
    hTr.1, hTr.2.2.1, hTr.2.2.2⟩

end InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitPoset
