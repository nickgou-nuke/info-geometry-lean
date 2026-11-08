/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Module
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments
import InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
import InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
import InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset
import InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitPoset
import InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitContinuumPoset

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.JaynesInductiveColimitNilpotentPoset
Role: Canonical native-Mathlib formalization of the 7-stage Acyclic Causal Poset
  (𝔍₁ ≺ 𝔍₂ ≺ 𝔍₃, 𝔍₄ ≺ 𝔍₅ ≺ 𝔍₆ ≺ 𝔍₇) of the Jaynesian Inductive Colimit &
  Nilpotent Reality (Solve et Coagula):
  (𝔍₁) Nilpotent Replacement of "Infinitely Small" & Exact First-Order Jet,
  (𝔍₂) Directed Poset of Finite Operator Algebras & Scale-Refinement System,
  (𝔍₃) Upward Functorial Preservation of the Peirce-Cartan-Clocking Spine,
  (𝔍₄) Downward Linear Readout Retraction, Chiral Filter & Asymmetry,
  (𝔍₅) Algebraic Direct-Limit Construction (ColimitRel & DirectLimit),
  (𝔍₆) Transfer of Polynomial Peirce/Clocking Identities to the Ring Direct Limit,
  (𝔍₇) Trace-Valued Cocone Cancellation and the Separate Cramér-Rao Bound.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.JaynesInductiveColimitNilpotentPoset

open Matrix BigOperators
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
open InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset
open InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty
open scoped Matrix InnerProductSpace

/-! ===========================================================================
    Section 0: The 7-Stage Acyclic Causal Poset (𝔍₁ ≺ 𝔍₂ ≺ ⋯ ≺ 𝔍₇)
    =========================================================================== -/

/-- The 7-stage epistemic compilation poset (`𝔍₁ ≺ 𝔍₂ ≺ ⋯ ≺ 𝔍₇`) of the Jaynesian
Inductive Colimit & Nilpotent Reality. -/
inductive JaynesColimitNilpotentStage : Type
  | J1_NilpotentReplacementOfInfinitesimals
  | J2_DirectedPosetOfFiniteOperatorAlgebras
  | J3_UpwardAlgebraicScalePreservation
  | J4_DownwardLinearReadoutRetraction
  | J5_AlgebraicDirectLimitConstruction
  | J6_DirectLimitTransferOfPolynomialIdentities
  | J7_TraceCoconeCancellationAndCramerRaoBound
  deriving DecidableEq, Repr, Inhabited

namespace JaynesColimitNilpotentStage

/-- Strictly monotone integer rank `0..6` for `JaynesColimitNilpotentStage`. -/
def rank : JaynesColimitNilpotentStage → ℕ
  | .J1_NilpotentReplacementOfInfinitesimals        => 0
  | .J2_DirectedPosetOfFiniteOperatorAlgebras       => 1
  | .J3_UpwardAlgebraicScalePreservation            => 2
  | .J4_DownwardLinearReadoutRetraction             => 3
  | .J5_AlgebraicDirectLimitConstruction            => 4
  | .J6_DirectLimitTransferOfPolynomialIdentities    => 5
  | .J7_TraceCoconeCancellationAndCramerRaoBound    => 6

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrderJaynesColimitNilpotentStage : LinearOrder JaynesColimitNilpotentStage :=
  LinearOrder.lift' rank rank_injective

/-- Direct covering edges of the 7-stage Jaynesian Colimit & Nilpotent poset (`𝔍₁ → ⋯ → 𝔍₇`),
with the diamond split `𝔍₂ → 𝔍₃`, `𝔍₂ → 𝔍₄` and join `𝔍₃ → 𝔍₅`, `𝔍₄ → 𝔍₅`. -/
def causalEdge : JaynesColimitNilpotentStage → JaynesColimitNilpotentStage → Prop
  | .J1_NilpotentReplacementOfInfinitesimals,       .J2_DirectedPosetOfFiniteOperatorAlgebras      => True
  | .J2_DirectedPosetOfFiniteOperatorAlgebras,      .J3_UpwardAlgebraicScalePreservation           => True
  | .J2_DirectedPosetOfFiniteOperatorAlgebras,      .J4_DownwardLinearReadoutRetraction            => True
  | .J3_UpwardAlgebraicScalePreservation,           .J5_AlgebraicDirectLimitConstruction            => True
  | .J4_DownwardLinearReadoutRetraction,            .J5_AlgebraicDirectLimitConstruction            => True
  | .J5_AlgebraicDirectLimitConstruction,           .J6_DirectLimitTransferOfPolynomialIdentities    => True
  | .J6_DirectLimitTransferOfPolynomialIdentities,   .J7_TraceCoconeCancellationAndCramerRaoBound    => True
  | _, _ => False

theorem causalEdge_strict_rank_mono {a b : JaynesColimitNilpotentStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

theorem causalEdge_irrefl (a : JaynesColimitNilpotentStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

theorem transGen_causalEdge_strict_rank_mono {a b : JaynesColimitNilpotentStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hbc)

theorem causalEdge_acyclic (a : JaynesColimitNilpotentStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

theorem causalEdge_chain_and_diamond :
    causalEdge .J1_NilpotentReplacementOfInfinitesimals .J2_DirectedPosetOfFiniteOperatorAlgebras ∧
    causalEdge .J2_DirectedPosetOfFiniteOperatorAlgebras .J3_UpwardAlgebraicScalePreservation ∧
    causalEdge .J2_DirectedPosetOfFiniteOperatorAlgebras .J4_DownwardLinearReadoutRetraction ∧
    causalEdge .J3_UpwardAlgebraicScalePreservation .J5_AlgebraicDirectLimitConstruction ∧
    causalEdge .J4_DownwardLinearReadoutRetraction .J5_AlgebraicDirectLimitConstruction ∧
    causalEdge .J5_AlgebraicDirectLimitConstruction .J6_DirectLimitTransferOfPolynomialIdentities ∧
    causalEdge .J6_DirectLimitTransferOfPolynomialIdentities .J7_TraceCoconeCancellationAndCramerRaoBound := by
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end JaynesColimitNilpotentStage

/-! ===========================================================================
    Section 1: Phase I, Rung 0–1 & Stage 𝔍₁ — The Jaynesian Binary Cut,
    Scalar Infinitesimal Aporia, and Theorem 1 (Exact First-Order Taylor Jet)
    =========================================================================== -/

section StageJ1

/-- **Rung 0 (The Scalar Infinitesimal Self-Destruction Aporia)**:
In any commutative ring without zero divisors (`[CommRing K] [NoZeroDivisors K]`, e.g. `ℝ` or `ℂ`),
requiring a scalar `dx` to satisfy `dx * dx = 0` forces `dx = 0`. Thus commutative scalars cannot
support non-zero first-order nilpotent jets. -/
theorem rung0_scalar_infinitesimal_self_destructs
    {K : Type*} [CommRing K] [NoZeroDivisors K] (dx : K) (h_sq : dx * dx = 0) :
    dx = 0 :=
  mul_self_eq_zero.mp h_sq

/-- First-order algebraic exponential `exp₁(N) = 1 + N` of a nilpotent operator. -/
def nilpotentExp {B : Type*} [Ring B] (N : B) : B := 1 + N

/-- In any associative ring `B`, if `N * N = 0`, then `nilpotentExp N = 1 + N` has exact two-sided
inverse `nilpotentExp (-N) = 1 - N` with zero higher-order remainder. -/
theorem nilpotentExp_mul_neg {B : Type*} [Ring B] {N : B} (hN : N * N = 0) :
    nilpotentExp N * nilpotentExp (-N) = 1 ∧
    nilpotentExp (-N) * nilpotentExp N = 1 := by
  unfold nilpotentExp
  constructor <;> noncomm_ring [hN]

/-- **Exact Binomial First-Order Jet (`nilpotent_binomial_first_order_jet`)**:
Over any commutative ring `R` and `R`-algebra `B`, if `N : B` satisfies `N * N = 0`, then for
every exponent `m : ℕ` and every scalar `c₀ : R`:
`(algebraMap R B c₀ + N) ^ m = algebraMap R B (c₀ ^ m) + algebraMap R B ((m : R) * c₀ ^ (m - 1)) * N`.
All terms of order `O(N²)` vanish identically without limits. -/
theorem nilpotent_binomial_first_order_jet
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (c₀ : R) {N : B} (hN : N * N = 0) (m : ℕ) :
    (algebraMap R B c₀ + N) ^ m =
      algebraMap R B (c₀ ^ m) + algebraMap R B ((m : R) * c₀ ^ (m - 1)) * N := by
  induction m with
  | zero =>
    simp
  | succ d ih =>
    cases d with
    | zero =>
      simp
    | succ d =>
      rw [pow_succ, ih]
      have hcomm : N * algebraMap R B c₀ = algebraMap R B c₀ * N :=
        (Algebra.commutes c₀ N).symm
      have hpow1 :
          algebraMap R B (c₀ ^ (d + 1 + 1)) =
            algebraMap R B (c₀ ^ (d + 1)) * algebraMap R B c₀ := by
        rw [pow_succ c₀ (d + 1), map_mul]
      have hpow2 :
          algebraMap R B (((d + 1 + 1 : ℕ) : R) * c₀ ^ (d + 1)) =
            algebraMap R B (((d + 1 : ℕ) : R) * c₀ ^ d) * algebraMap R B c₀ +
              algebraMap R B (c₀ ^ (d + 1)) := by
        have h_scalar :
            ((d + 1 + 1 : ℕ) : R) * c₀ ^ (d + 1) =
              (((d + 1 : ℕ) : R) * c₀ ^ d) * c₀ + c₀ ^ (d + 1) := by
          rw [pow_succ c₀ d]
          push_cast
          ring
        rw [h_scalar, map_add, map_mul]
      simp only [Nat.add_sub_cancel]
      rw [hpow1, hpow2]
      noncomm_ring [hN, hcomm]

/-- Polynomial evaluation of degree `< d` with coefficients `c : ℕ → R` at `x : B`. -/
def polyJetEval {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (c : ℕ → R) (d : ℕ) (x : B) : B :=
  ∑ j ∈ Finset.range d, algebraMap R B (c j) * x ^ j

/-- Scalar polynomial value `F(c₀) = ∑_{j < d} c_j c₀^j`. -/
def polyScalarVal {R : Type*} [CommRing R] (c : ℕ → R) (d : ℕ) (c₀ : R) : R :=
  ∑ j ∈ Finset.range d, c j * c₀ ^ j

/-- Scalar formal derivative value `F'(c₀) = ∑_{j < d} c_j · j · c₀^{j-1}`. -/
def polyScalarDeriv {R : Type*} [CommRing R] (c : ℕ → R) (d : ℕ) (c₀ : R) : R :=
  ∑ j ∈ Finset.range d, c j * ((j : R) * c₀ ^ (j - 1))

/-- **Axiom I / Theorem 1 / Stage `𝔍₁` (`theorem1_exact_first_order_taylor_truncation`)**:
For any associative `R`-algebra `B`, any idempotent `P * P = P`, any operator `X : B`, any
polynomial coefficient sequence `c : ℕ → R`, any degree bound `d : ℕ`, and any central point `c₀ : R`:
1. The off-diagonal Peirce blocks `N₊ = conePlus P X` and `N₋ = coneMinus P X` are nilpotent
   (`N₊ * N₊ = 0` and `N₋ * N₋ = 0`),
2. `nilpotentExp N₊ * nilpotentExp (-N₊) = 1`,
3. Evaluating any polynomial `F` at `c₀ • 1 + N₊` truncates **identically at first order**:
   `polyJetEval c d (algebraMap R B c₀ + N₊) = algebraMap R B (polyScalarVal c d c₀) + algebraMap R B (polyScalarDeriv c d c₀) * N₊`. -/
theorem theorem1_exact_first_order_taylor_truncation
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    {P : B} (hP : P * P = P) (X : B) (c : ℕ → R) (d : ℕ) (c₀ : R) :
    let N_plus := conePlus P X
    let N_minus := coneMinus P X
    N_plus * N_plus = 0 ∧
    N_minus * N_minus = 0 ∧
    nilpotentExp N_plus * nilpotentExp (-N_plus) = 1 ∧
    polyJetEval c d (algebraMap R B c₀ + N_plus) =
      algebraMap R B (polyScalarVal c d c₀) +
        algebraMap R B (polyScalarDeriv c d c₀) * N_plus := by
  have hNp : conePlus P X * conePlus P X = 0 := conePlus_mul_conePlus hP X X
  have hNm : coneMinus P X * coneMinus P X = 0 := coneMinus_mul_coneMinus hP X X
  refine ⟨hNp, hNm, (nilpotentExp_mul_neg hNp).1, ?_⟩
  unfold polyJetEval polyScalarVal polyScalarDeriv
  rw [map_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [nilpotent_binomial_first_order_jet c₀ hNp j, mul_add, ← map_mul, ← mul_assoc, ← map_mul]

end StageJ1

/-! ===========================================================================
    Section 2: Phase II, Rung 2 & Stages 𝔍₂, 𝔍₃ — Directed System of Scale
    Refinements & Lemma 1 (Functorial Invariance of the Peirce–Cartan Spine)
    =========================================================================== -/

section StageJ2J3

/-- **Axiom II / Stage `𝔍₂` (`archetype_J2_directed_system_coherence`)**:
In any directed system of rings `(A_n, ι_{m,n})_{m ≤ n}`, the transition homomorphisms satisfy
reflexivity `ι_{n,n}(x) = x` and transitivity `ι_{n,k}(ι_{m,n}(x)) = ι_{m,k}(x)` for `m ≤ n ≤ k`,
and preserve ring units, sums, products, and commutators. -/
theorem archetype_J2_directed_system_coherence
    {A : ℕ → Type*} [∀ n, Ring (A n)]
    (ι : ∀ m n, m ≤ n → A m →+* A n)
    [DirectedSystem A (fun m n h => ι m n h)]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (X Y : A m) :
    ι m m (le_refl m) X = X ∧
    ι n k hnk (ι m n hmn X) = ι m k (le_trans hmn hnk) X ∧
    ι m n hmn (OperatorAlgebra.PeirceSpine.comm X Y) =
      OperatorAlgebra.PeirceSpine.comm (ι m n hmn X) (ι m n hmn Y) ∧
    ι m n hmn (anticomm X Y) = anticomm (ι m n hmn X) (ι m n hmn Y) := by
  refine ⟨DirectedSystem.map_self (f := fun m n h => ι m n h) X,
          DirectedSystem.map_map (f := fun m n h => ι m n h) hmn hnk X, ?_, ?_⟩
  · simp [OperatorAlgebra.PeirceSpine.comm]
  · simp [anticomm]

/-- **Lemma 1 / Stage `𝔍₃` (`lemma1_functorial_invariance_peirce_cartan_spine`)**:
Any unital ring homomorphism `φ : B₁ →+* B₂` (and in particular every scale-refinement map
`ι_{m,n} : A_m →+* A_n`) preserves idempotence, the chiral involution `S_P`, the nilpotent blocks
`N_±`, the solder form `Φ`, the Maurer–Cartan current `J`, the Fisher metric `V`, and the spin
curvature `Σ`. -/
theorem lemma1_functorial_invariance_peirce_cartan_spine
    {B₁ B₂ : Type*} [Ring B₁] [Ring B₂] (φ : B₁ →+* B₂)
    {P : B₁} (hP : P * P = P) (A C : B₁) :
    let P' := φ P
    let A' := φ A
    let C' := φ C
    P' * P' = P' ∧
    φ (invS P) = invS P' ∧
    φ (conePlus P A) = conePlus P' A' ∧
    φ (coneMinus P C) = coneMinus P' C' ∧
    φ (genPhi P A C) = genPhi P' A' C' ∧
    φ (genJ P A C) = genJ P' A' C' ∧
    φ (genV P A C) = genV P' A' C' ∧
    φ (genSig P A C) = genSig P' A' C' := by
  refine ⟨by rw [← map_mul, hP], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [invS]
  · simp [conePlus]
  · simp [coneMinus]
  · simp [genPhi, conePlus, coneMinus]
  · simp [genJ, conePlus, coneMinus]
  · simp [genV, anticomm, conePlus, coneMinus]
  · simp [genSig, OperatorAlgebra.PeirceSpine.comm, conePlus, coneMinus]

end StageJ2J3

/-! ===========================================================================
    Section 3: Phase II–III & Stage 𝔍₄ — Downward Linear Readout,
    Chiral Filter 𝓚_γ₅, and Directional Tension (Retraction vs. Irreversibility)
    =========================================================================== -/

section StageJ4

/-- Twice the chiral even-grade projection `2 𝓚_γ₅(Y) = Y + S_P Y S_P` in any associative ring. -/
def chiralEvenFilter2 {B : Type*} [Ring B] (P Y : B) : B :=
  Y + invS P * Y * invS P

/-- Unital block-diagonal scale-refinement homomorphism `ι_scale : ℤ →+* Matrix (Fin 2) (Fin 2) ℤ`
embedding a coarse scalar `x` as `x • I₂ = !![x, 0; 0, x]`. -/
def scaleRefine2 : ℤ →+* Matrix (Fin 2) (Fin 2) ℤ where
  toFun x := !![x, 0; 0, x]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- A linear coarse readout `Matrix (Fin 2) (Fin 2) ℤ → ℤ` extracting the upper-left entry.
This is not a conditional expectation: it is not multiplicative and is not a bimodule
expectation onto the scalar-matrix subalgebra. -/
def coarseReadout2 (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := M 0 0

/-- The upper-left readout is not multiplicative, so it is not an algebra conditional
expectation onto the scalar-matrix image of `scaleRefine2`. -/
theorem coarseReadout2_not_multiplicative :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℤ,
      coarseReadout2 (M * N) ≠ coarseReadout2 M * coarseReadout2 N := by
  refine ⟨!![(0 : ℤ), 1; 0, 0], !![(0 : ℤ), 0; 1, 0], ?_⟩
  norm_num [coarseReadout2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Fine-scale fluctuation defect `Δ(M) = M - ι_scale(coarseReadout2 M)` lost under
readout followed by re-embedding. -/
def fineScaleDefect2 (M : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  M - scaleRefine2 (coarseReadout2 M)

/-- Concrete diagonal idempotent `P = !![1, 0; 0, 0]` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def witnessNilpotentProj : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Concrete off-diagonal nilpotent `N_+ = !![0, 1; 0, 0]` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def witnessNilpotentPlus : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- **Trap T16 Non-Commutativity Witness (`witnessNilpotentProj_witnessNilpotentPlus_noncomm`)**:
In `Matrix (Fin 2) (Fin 2) ℤ`, the idempotent sheet projector `witnessNilpotentProj` and the
off-diagonal Peirce nilpotent `witnessNilpotentPlus` do not commute. -/
theorem witnessNilpotentProj_witnessNilpotentPlus_noncomm :
    (witnessNilpotentProj : Matrix (Fin 2) (Fin 2) ℤ) *
        (witnessNilpotentPlus : Matrix (Fin 2) (Fin 2) ℤ) ≠
      (witnessNilpotentPlus : Matrix (Fin 2) (Fin 2) ℤ) *
        (witnessNilpotentProj : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [witnessNilpotentProj, witnessNilpotentPlus, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- **Stage `𝔍₄` (`archetype_J4_downward_readout_chiral_filter_and_directional_tension`)**:
1. **Chiral Filter Kills Odd Noise**: `chiralEvenFilter2 P (genJ P A C) = 0`,
2. **Quadratic Collision Survives in Even Subalgebra**: `-genJ P A C * genJ P A C = genV P A C`
   and `chiralEvenFilter2 P (genV P A C) = (2 : ℤ) • genV P A C`,
3. **Readout Retraction** (not a conditional expectation):
   `coarseReadout2 (scaleRefine2 x) = x` and
   `coarseReadout2 (fineScaleDefect2 M) = 0`,
4. **Directional Tension**: For the fine-scale nilpotent `witnessNilpotentPlus`,
   `scaleRefine2 (coarseReadout2 witnessNilpotentPlus) = 0 ≠ witnessNilpotentPlus` and
   `fineScaleDefect2 witnessNilpotentPlus = witnessNilpotentPlus ≠ 0`. -/
theorem archetype_J4_downward_readout_chiral_filter_and_directional_tension
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
    (x : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    chiralEvenFilter2 P (genJ P A C) = 0 ∧
    -genJ P A C * genJ P A C = genV P A C ∧
    chiralEvenFilter2 P (genV P A C) = (2 : ℤ) • genV P A C ∧
    coarseReadout2 (scaleRefine2 x) = x ∧
    coarseReadout2 (fineScaleDefect2 M) = 0 ∧
    scaleRefine2 (coarseReadout2 witnessNilpotentPlus) = 0 ∧
    fineScaleDefect2 witnessNilpotentPlus = witnessNilpotentPlus ∧
    witnessNilpotentPlus ≠ 0 := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · unfold chiralEvenFilter2
    peirce_nf hP
  · peirce_nf hP
  · unfold chiralEvenFilter2
    peirce_nf hP
  · change M 0 0 - M 0 0 = 0
    exact sub_self (M 0 0)
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [witnessNilpotentPlus] at h01

end StageJ4

/-! ===========================================================================
    Section 4: Phase II & Deduction 1 / Stage 𝔍₅ — Algebraic Direct-Limit
    Construction (`ColimitRel` Equivalence & `DirectLimit A ι`)
    =========================================================================== -/

section StageJ5

variable {A : ℕ → Type*} [∀ n, Ring (A n)]
variable (ι : ∀ m n, m ≤ n → A m →+* A n)
variable [DirectedSystem A (fun m n h => ι m n h)]

/-- The explicit Jaynesian directed colimit equivalence relation on `(n : ℕ) × A n`:
`(m, X_m) ~ (n, Y_n) ↔ ∃ k ≥ max(m, n), ι_{m,k}(X_m) = ι_{n,k}(Y_n)`. -/
def ColimitRel (p q : Σ n : ℕ, A n) : Prop :=
  ∃ k : ℕ, ∃ hmk : p.1 ≤ k, ∃ hnk : q.1 ≤ k,
    ι p.1 k hmk p.2 = ι q.1 k hnk q.2

omit [DirectedSystem A (fun m n h => ι m n h)] in
theorem colimitRel_refl (p : Σ n : ℕ, A n) : ColimitRel ι p p :=
  ⟨p.1, le_refl p.1, le_refl p.1, rfl⟩

omit [DirectedSystem A (fun m n h => ι m n h)] in
theorem colimitRel_symm {p q : Σ n : ℕ, A n} (h : ColimitRel ι p q) :
    ColimitRel ι q p := by
  rcases h with ⟨k, hmk, hnk, heq⟩
  exact ⟨k, hnk, hmk, heq.symm⟩

theorem colimitRel_trans {p q r : Σ n : ℕ, A n}
    (hpq : ColimitRel ι p q) (hqr : ColimitRel ι q r) :
    ColimitRel ι p r := by
  rcases hpq with ⟨k₁, hpk₁, hqk₁, heq₁⟩
  rcases hqr with ⟨k₂, hqk₂, hrk₂, heq₂⟩
  refine ⟨max k₁ k₂, le_trans hpk₁ (le_max_left k₁ k₂),
          le_trans hrk₂ (le_max_right k₁ k₂), ?_⟩
  have h1 := DirectedSystem.map_map (f := fun m n h => ι m n h) hpk₁ (le_max_left k₁ k₂) p.2
  have h2 := DirectedSystem.map_map (f := fun m n h => ι m n h) hqk₁ (le_max_left k₁ k₂) q.2
  have h3 := DirectedSystem.map_map (f := fun m n h => ι m n h) hqk₂ (le_max_right k₁ k₂) q.2
  have h4 := DirectedSystem.map_map (f := fun m n h => ι m n h) hrk₂ (le_max_right k₁ k₂) r.2
  calc
    ι p.1 (max k₁ k₂) (le_trans hpk₁ (le_max_left k₁ k₂)) p.2
      = ι k₁ (max k₁ k₂) (le_max_left k₁ k₂) (ι p.1 k₁ hpk₁ p.2) := h1.symm
    _ = ι k₁ (max k₁ k₂) (le_max_left k₁ k₂) (ι q.1 k₁ hqk₁ q.2) := by rw [heq₁]
    _ = ι q.1 (max k₁ k₂) (le_trans hqk₁ (le_max_left k₁ k₂)) q.2 := h2
    _ = ι k₂ (max k₁ k₂) (le_max_right k₁ k₂) (ι q.1 k₂ hqk₂ q.2) := h3.symm
    _ = ι k₂ (max k₁ k₂) (le_max_right k₁ k₂) (ι r.1 k₂ hrk₂ r.2) := by rw [heq₂]
    _ = ι r.1 (max k₁ k₂) (le_trans hrk₂ (le_max_right k₁ k₂)) r.2 := h4

/-- **Deduction 1 / Theorem 2 / Stage `𝔍₅` (`theorem2_colimitRel_equivalence_and_directLimit_cocone`)**:
1. `ColimitRel ι` is an equivalence relation on `Σ n : ℕ, A n`,
2. For any `m ≤ n` and `X_m : A m`, the canonical colimit ring homomorphism
   `DirectLimit.Ring.of A ι` satisfies `of_n (ι_{m,n}(X_m)) = of_m(X_m)`,
3. Whenever `ColimitRel ι ⟨m, X_m⟩ ⟨n, Y_n⟩` holds, their classes in `DirectLimit A ι`
   coincide: `DirectLimit.Ring.of A ι m X_m = DirectLimit.Ring.of A ι n Y_n`. -/
theorem theorem2_colimitRel_equivalence_and_directLimit_cocone
    {m n : ℕ} (hmn : m ≤ n) (X_m : A m)
    {p q : Σ l : ℕ, A l} (hpq : ColimitRel ι p q) :
    Equivalence (ColimitRel ι) ∧
    DirectLimit.Ring.of A ι n (ι m n hmn X_m) = DirectLimit.Ring.of A ι m X_m ∧
    DirectLimit.Ring.of A ι p.1 p.2 = DirectLimit.Ring.of A ι q.1 q.2 := by
  refine ⟨⟨colimitRel_refl ι, colimitRel_symm ι, colimitRel_trans ι⟩,
          DirectLimit.Ring.of_f hmn X_m, ?_⟩
  rcases hpq with ⟨k, hpk, hqk, heq⟩
  calc
    DirectLimit.Ring.of A ι p.1 p.2
      = DirectLimit.Ring.of A ι k (ι p.1 k hpk p.2) := (DirectLimit.Ring.of_f hpk p.2).symm
    _ = DirectLimit.Ring.of A ι k (ι q.1 k hqk q.2) := by rw [heq]
    _ = DirectLimit.Ring.of A ι q.1 q.2 := DirectLimit.Ring.of_f hqk q.2

end StageJ5

/-! ===========================================================================
    Section 5: Deduction 2 / Stage 𝔍₆ — All-Order Chiral Commutator Identity
    & Theorem 3 (Direct-Limit Transfer of Polynomial Peirce/Clocking Laws)
    =========================================================================== -/

section StageJ6

/-- Odd powers of the solder form factor through powers of the Fisher metric:
`Φ^(2k + 1) = Φ * V^k` in any associative ring with idempotent `P * P = P`. -/
theorem genPhi_odd_pow_eq_mul_genV_pow
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    genPhi P A C ^ (2 * k + 1) = genPhi P A C * genV P A C ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
    have hExp : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
    rw [hExp, pow_succ, pow_succ, ih, mul_assoc, mul_assoc, hPhiSq, ← pow_succ]

/-- The Maurer–Cartan current `J` commutes with every power `V^k` of the Fisher metric. -/
theorem genJ_comm_genV_pow
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    genJ P A C * genV P A C ^ k = genV P A C ^ k * genJ P A C := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hJV : genJ P A C * genV P A C = genV P A C * genJ P A C := by peirce_nf hP
    calc
      genJ P A C * genV P A C ^ (k + 1)
        = (genJ P A C * genV P A C ^ k) * genV P A C := by rw [pow_succ, mul_assoc]
      _ = genV P A C ^ k * (genJ P A C * genV P A C) := by rw [ih, mul_assoc]
      _ = genV P A C ^ k * (genV P A C * genJ P A C) := by rw [hJV]
      _ = genV P A C ^ (k + 1) * genJ P A C := by rw [← mul_assoc, ← pow_succ]

/-- **All-Order Chiral Trace-Density Commutator Identity**:
At every ring stage and for every order `k : ℕ`, twice the chiral trace density
`2 • (S_P * V^(k+1))` is an exact commutator `[J, Φ^(2k+1)]`:
`(2 : ℤ) • (invS P * genV P A C ^ (k + 1)) = comm (genJ P A C) (genPhi P A C ^ (2 * k + 1))`. -/
theorem chiral_trace_density_is_commutator_all_orders
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    (2 : ℤ) • (invS P * genV P A C ^ (k + 1)) =
      OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C ^ (2 * k + 1)) := by
  rw [genPhi_odd_pow_eq_mul_genV_pow hP A C k]
  have hBase :
      OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C) =
        (2 : ℤ) • (invS P * genV P A C) := by
    peirce_nf hP
  have hJV : genJ P A C * genV P A C ^ k = genV P A C ^ k * genJ P A C :=
    genJ_comm_genV_pow hP A C k
  calc
    (2 : ℤ) • (invS P * genV P A C ^ (k + 1))
      = ((2 : ℤ) • (invS P * genV P A C)) * genV P A C ^ k := by
          rw [pow_succ']
          noncomm_ring
    _ = OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C) * genV P A C ^ k := by
          rw [hBase]
    _ = OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C * genV P A C ^ k) := by
          unfold OperatorAlgebra.PeirceSpine.comm
          noncomm_ring [hJV]

/-- In any associative ring `B`, an idempotent `P * P = P` and generators `A, C : B`
satisfy the complete Peirce–Cartan–Clocking and all-order chiral commutator identities. -/
theorem peirce_clocking_spine_identities
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    P * P = P ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) =
      -((2 : ℤ) • genSig P A C) ∧
    invS P * OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) =
      -((2 : ℤ) • genV P A C) ∧
    -OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
      -((2 : ℤ) • OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) ∧
    -OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
      -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    (2 : ℤ) • (invS P * genV P A C ^ (k + 1)) =
      OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C ^ (2 * k + 1)) := by
  refine ⟨hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP,
          chiral_trace_density_is_commutator_all_orders hP A C k⟩

/-- **Theorem 3 / Stage `𝔍₆` (`theorem3_direct_limit_transfer_peirce_clocking_identities`)**:
For any directed system `(A_n, ι_{m,n})` of associative rings and any stage-`n` idempotent
`P_n * P_n = P_n` with generators `A_n, C_n : A n`, let `P_∞, A_∞, C_∞` be their canonical images
under `of_n := DirectLimit.Ring.of A ι n` in the algebraic direct-limit ring `A_∞ := DirectLimit A ι`.
Then the induced solder form `Φ_∞ = genPhi P_∞ A_∞ C_∞`, current `J_∞ = genJ P_∞ A_∞ C_∞`,
Fisher metric `V_∞ = genV P_∞ A_∞ C_∞`, and spin curvature `Sig_inf = genSig P_∞ A_∞ C_∞` satisfy
identically in the ring `A_∞`; this theorem asserts algebraic transfer only and equips `A_∞` with
no topology, measure, or analytic-continuum structure:
1. `P_∞ * P_∞ = P_∞` and `Φ_∞ * Φ_∞ = V_∞`,
2. `comm Φ_∞ J_∞ = -((2 : ℤ) • Sig_inf)` and `invS P_∞ * comm Φ_∞ J_∞ = -((2 : ℤ) • V_∞)`,
3. `-comm Φ_∞ (comm Φ_∞ J_∞) = -((2 : ℤ) • comm Sig_inf Φ_∞)` and
   `-comm Φ_∞ (comm Φ_∞ J_∞) = -((4 : ℤ) • (V_inf * J_inf))`,
4. `(2 : ℤ) • (invS P_∞ * V_∞ ^ (k + 1)) = comm J_∞ (Φ_∞ ^ (2 * k + 1))` for all `k : ℕ`. -/
theorem theorem3_direct_limit_transfer_peirce_clocking_identities
    {A : ℕ → Type*} [∀ n, Ring (A n)]
    (ι : ∀ m n, m ≤ n → A m →+* A n)
    [DirectedSystem A (fun m n h => ι m n h)]
    (n : ℕ) {P_n : A n} (hP_n : P_n * P_n = P_n) (X_n Y_n : A n) (k : ℕ) :
    let of_n := DirectLimit.Ring.of A ι n
    let P_inf := of_n P_n
    let A_inf := of_n X_n
    let C_inf := of_n Y_n
    let Φ_inf := genPhi P_inf A_inf C_inf
    let J_inf := genJ P_inf A_inf C_inf
    let V_inf := genV P_inf A_inf C_inf
    let Sig_inf := genSig P_inf A_inf C_inf
    P_inf * P_inf = P_inf ∧
    Φ_inf * Φ_inf = V_inf ∧
    OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf = -((2 : ℤ) • Sig_inf) ∧
    invS P_inf * OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf = -((2 : ℤ) • V_inf) ∧
    -OperatorAlgebra.PeirceSpine.comm Φ_inf (OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf) =
      -((2 : ℤ) • OperatorAlgebra.PeirceSpine.comm Sig_inf Φ_inf) ∧
    -OperatorAlgebra.PeirceSpine.comm Φ_inf (OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf) =
      -((4 : ℤ) • (V_inf * J_inf)) ∧
    (2 : ℤ) • (invS P_inf * V_inf ^ (k + 1)) =
      OperatorAlgebra.PeirceSpine.comm J_inf (Φ_inf ^ (2 * k + 1)) := by
  intro of_n P_inf A_inf C_inf Φ_inf J_inf V_inf Sig_inf
  have hP_inf : P_inf * P_inf = P_inf :=
    (lemma1_functorial_invariance_peirce_cartan_spine of_n hP_n X_n Y_n).1
  exact peirce_clocking_spine_identities hP_inf A_inf C_inf k

end StageJ6

/-! ===========================================================================
    Section 6: Stage 𝔍₇ — Theorem 4 (Trace-Valued Cocone Cancellation
    & the Separate Metriplectic Cramér–Rao Bound)
    =========================================================================== -/

section StageJ7

/-- Canonical additive functional `τ_∞ : DirectLimit A ι →+ K` descended directly
to the ring direct limit `DirectLimit A ι` from a compatible cocone `τ : ∀ n, A n →+ K`. -/
def directLimitTraceLift
    {A : ℕ → Type*} [∀ n, Ring (A n)]
    (ι : ∀ m n, m ≤ n → A m →+* A n)
    [DirectedSystem A (fun m n h => ι m n h)]
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n, A n →+ K)
    (h_cocone : ∀ m n (h : m ≤ n) (x : A m), τ n (ι m n h x) = τ m x) :
    DirectLimit A ι →+ K where
  toFun := DirectLimit.lift
    (fun m n h => ι m n h)
    (fun n x => τ n x)
    (fun m n h x => (h_cocone m n h x).symm)
  map_zero' := by
    rw [DirectLimit.zero_def 0]
    change τ 0 0 = 0
    exact map_zero (τ 0)
  map_add' x y := by
    induction x, y using DirectLimit.induction₂ with
    | _ i a b =>
      simp only [DirectLimit.add_def, DirectLimit.lift_def, map_add]

@[simp] theorem directLimitTraceLift_of
    {A : ℕ → Type*} [∀ n, Ring (A n)]
    (ι : ∀ m n, m ≤ n → A m →+* A n)
    [DirectedSystem A (fun m n h => ι m n h)]
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n, A n →+ K)
    (h_cocone : ∀ m n (h : m ≤ n) (x : A m), τ n (ι m n h x) = τ m x)
    (n : ℕ) (x : A n) :
    directLimitTraceLift ι τ h_cocone (DirectLimit.Ring.of A ι n x) = τ n x :=
  rfl

/-- If each finite-stage functional `τ n` is tracial (`τ n (X * Y) = τ n (Y * X)`), then the
induced direct-limit functional `directLimitTraceLift ι τ h_cocone` is cyclic on the entire
ring direct limit `DirectLimit A ι`. -/
theorem directLimitTraceLift_cyclic
    {A : ℕ → Type*} [∀ n, Ring (A n)]
    (ι : ∀ m n, m ≤ n → A m →+* A n)
    [DirectedSystem A (fun m n h => ι m n h)]
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n, A n →+ K)
    (h_cocone : ∀ m n (h : m ≤ n) (x : A m), τ n (ι m n h x) = τ m x)
    (h_tracial : ∀ n (X Y : A n), τ n (X * Y) = τ n (Y * X))
    (X Y : DirectLimit A ι) :
    directLimitTraceLift ι τ h_cocone (X * Y) =
      directLimitTraceLift ι τ h_cocone (Y * X) := by
  induction X, Y using DirectLimit.induction₂ with
  | _ n a b =>
    change directLimitTraceLift ι τ h_cocone (⟦⟨n, a⟩⟧ * ⟦⟨n, b⟩⟧) =
      directLimitTraceLift ι τ h_cocone (⟦⟨n, b⟩⟧ * ⟦⟨n, a⟩⟧)
    rw [DirectLimit.mul_def, DirectLimit.mul_def]
    exact h_tracial n a b

/-- **Theorem 4 / Stage `𝔍₇` (`theorem4_trace_cocone_chiral_cancellation_and_cramer_rao`)**:
Let `(A_n, ι_{m,n})` be a directed system of associative rings and let `τ : ∀ n, A n →+ K` be a
compatible cocone of tracial additive functionals into an additive commutative group `K`
(`∀ m ≤ n, τ_n ∘ ι_{m,n} = τ_m` and `∀ n X Y, τ_n(X * Y) = τ_n(Y * X)`):
1. **Cocone Invariance**: Whenever `ColimitRel ι ⟨m, X_m⟩ ⟨n, Y_n⟩` holds,
   `τ m X_m = τ n Y_n`,
2. **Induced Additive Readout**: `τ_∞ := directLimitTraceLift ι τ h_cocone` satisfies
   `τ_∞ (DirectLimit.Ring.of A ι n X_n) = τ n X_n`,
3. **All-Order Algebraic Trace Cancellation**:
   For every stage `n : ℕ` and every order `k : ℕ`, the induced additive readout of
   `2 • (S_{P_∞} * V_∞^{k+1})` vanishes by cyclicity. This is not a Gauss–Bonnet theorem,
   analytic index formula, or topological limit:
   `τ_∞ ((2 : ℤ) • (invS P_∞ * V_∞ ^ (k + 1))) = 0`,
4. **Metriplectic Cramér–Rao Closure**:
   `onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥ (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 + (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2`. -/
theorem theorem4_trace_cocone_chiral_cancellation_and_cramer_rao
    {A : ℕ → Type*} [∀ n, Ring (A n)]
    (ι : ∀ m n, m ≤ n → A m →+* A n)
    [DirectedSystem A (fun m n h => ι m n h)]
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n, A n →+ K)
    (h_cocone : ∀ m n (h : m ≤ n) (x : A m), τ n (ι m n h x) = τ m x)
    (h_tracial : ∀ n (X Y : A n), τ n (X * Y) = τ n (Y * X))
    {p q : Σ l : ℕ, A l} (hpq : ColimitRel ι p q)
    (n : ℕ) {P_n : A n} (hP_n : P_n * P_n = P_n) (X_n Y_n : A n) (k : ℕ)
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (ψ : InfoGeometry.QuantumGeometry.Projective.NormalizedState ℋ)
    (X_op Y_op : ℋ →L[ℂ] ℋ) :
    let τ_inf : DirectLimit A ι →+ K := directLimitTraceLift ι τ h_cocone
    let of_n := DirectLimit.Ring.of A ι n
    let P_inf := of_n P_n
    let V_inf := genV P_inf (of_n X_n) (of_n Y_n)
    τ p.1 p.2 = τ q.1 q.2 ∧
    τ_inf (of_n X_n) = τ n X_n ∧
    τ_inf ((2 : ℤ) • (invS P_inf * V_inf ^ (k + 1))) = 0 ∧
    onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
      (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
        (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 := by
  intro τ_inf of_n P_inf V_inf
  have h_rel_eq : τ p.1 p.2 = τ q.1 q.2 := by
    rcases hpq with ⟨k₀, hpk₀, hqk₀, heq⟩
    calc
      τ p.1 p.2 = τ k₀ (ι p.1 k₀ hpk₀ p.2) := (h_cocone p.1 k₀ hpk₀ p.2).symm
      _ = τ k₀ (ι q.1 k₀ hqk₀ q.2) := by rw [heq]
      _ = τ q.1 q.2 := h_cocone q.1 k₀ hqk₀ q.2
  have h_gb_n :
      (2 : ℤ) • (invS P_n * genV P_n X_n Y_n ^ (k + 1)) =
        OperatorAlgebra.PeirceSpine.comm (genJ P_n X_n Y_n) (genPhi P_n X_n Y_n ^ (2 * k + 1)) :=
    chiral_trace_density_is_commutator_all_orders hP_n X_n Y_n k
  have h_map_gb :
      of_n ((2 : ℤ) • (invS P_n * genV P_n X_n Y_n ^ (k + 1))) =
        (2 : ℤ) • (invS P_inf * V_inf ^ (k + 1)) := by
    have hL := lemma1_functorial_invariance_peirce_cartan_spine of_n hP_n X_n Y_n
    rw [map_zsmul, map_mul, map_pow, hL.2.1, hL.2.2.2.2.2.2.1]
  have h_str_zero : τ_inf ((2 : ℤ) • (invS P_inf * V_inf ^ (k + 1))) = 0 := by
    rw [← h_map_gb, directLimitTraceLift_of, h_gb_n]
    unfold OperatorAlgebra.PeirceSpine.comm
    rw [map_sub, h_tracial n, sub_self]
  exact ⟨h_rel_eq, rfl, h_str_zero,
         cramerRao_metriplectic_full_bound ψ X_op Y_op⟩

/-- The undoubled positive graded metric moment has zero trace in the ring
colimit, with no assumption that the additive trace target has no 2-torsion.
This strengthens the doubled identity above by using the Peirce corner
commutator factorization directly in the ring colimit via `directLimitTraceLift_cyclic`.
It asserts algebraic trace cancellation only; it does not
identify the trace with an analytic index or Euler characteristic. -/
theorem theorem4_colimit_graded_metric_moment_trace_zero
    {A : ℕ → Type*} [∀ n, Ring (A n)]
    (ι : ∀ m n, m ≤ n → A m →+* A n)
    [DirectedSystem A (fun m n h => ι m n h)]
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n, A n →+ K)
    (h_cocone : ∀ m n (h : m ≤ n) (x : A m), τ n (ι m n h x) = τ m x)
    (h_tracial : ∀ n (X Y : A n), τ n (X * Y) = τ n (Y * X))
    (n : ℕ) {P_n : A n} (hP_n : P_n * P_n = P_n)
    (X_n Y_n : A n) (k : ℕ) :
    let τ_inf : DirectLimit A ι →+ K := directLimitTraceLift ι τ h_cocone
    let of_n := DirectLimit.Ring.of A ι n
    let P_inf := of_n P_n
    let V_inf := genV P_inf (of_n X_n) (of_n Y_n)
    τ_inf (invS P_inf * V_inf ^ (k + 1)) = 0 := by
  intro τ_inf of_n P_inf V_inf
  have hP_inf : P_inf * P_inf = P_inf :=
    (lemma1_functorial_invariance_peirce_cartan_spine of_n hP_n X_n Y_n).1
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments.cyclic_grading_metric_power_zero
    τ_inf
    (directLimitTraceLift_cyclic ι τ h_cocone h_tracial)
    hP_inf (of_n X_n) (of_n Y_n) k

end StageJ7

/-! ==========================================================================
    Section 6b: Concrete `2^n × 2^n` complex matrix tower specialization
    ========================================================================== -/

/-- In the repository's concrete matrix direct limit, the normalized cyclic
matrix trace annihilates every positive graded Peirce metric moment. Here the
finite stages are `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`, the successor is the
Kronecker embedding `A ↦ A ⊗ I₂`, and `traceFunctional` is the trace already
descended to that algebraic ring colimit. This is a noncommutative operator
matrix result; it does not assert a C*-completion or identify the value at
degree zero with a topological index. -/
theorem concrete_cuntz_matrix_tower_graded_moment_trace_zero
    (P A C : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier)
    (hP : P * P = P) (k : ℕ) :
    InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional.traceFunctional
      (invS P * genV P A C ^ (k + 1)) = 0 := by
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments.cyclic_grading_metric_power_zero
      InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional.traceFunctional.toAddMonoidHom
      InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional.traceFunctional_cyclic
      hP A C k

/-- The same cancellation holds for every finite integer polynomial in the
positive Peirce metric moments of the concrete matrix direct limit. This is an
algebraic trace identity in the matrix direct-limit carrier, not an
analytic-series or topological-index statement. -/
theorem concrete_cuntz_matrix_tower_graded_metric_polynomial_trace_zero
    (P A C : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier)
    (hP : P * P = P) (s : Finset ℕ) (coeff : ℕ → ℤ) :
    InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional.traceFunctional
      (invS P * ∑ k ∈ s, (coeff k) • (genV P A C) ^ (k + 1)) = 0 := by
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments.cyclic_grading_metric_polynomial_zero
    InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional.traceFunctional.toAddMonoidHom
    InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional.traceFunctional_cyclic
    hP A C s coeff

/-! ===========================================================================
    Section 7: Master Structural Synthesis & Concrete Non-Commutative Matrix
    Witnesses (`T16` & `T17`)
    =========================================================================== -/

/-- **Master Structural Synthesis (`jaynes_inductive_colimit_nilpotent_master_synthesis`)**:
Coagulates the entire 7-stage Jaynesian Inductive Colimit & Nilpotent Reality poset
(`𝔍₁ ≺ 𝔍₂ ≺ ⋯ ≺ 𝔍₇`) into a single self-verifying theorem chain. -/
theorem jaynes_inductive_colimit_nilpotent_master_synthesis
    {K_field : Type*} [CommRing K_field] [NoZeroDivisors K_field]
    (dx : K_field) (h_dx_sq : dx * dx = 0)
    {R : Type*} [CommRing R]
    {A : ℕ → Type*} [∀ n, Ring (A n)] [∀ n, Algebra R (A n)]
    (ι : ∀ m n, m ≤ n → A m →+* A n)
    [DirectedSystem A (fun m n h => ι m n h)]
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n, A n →+ K)
    (h_cocone : ∀ m n (h : m ≤ n) (x : A m), τ n (ι m n h x) = τ m x)
    (h_tracial : ∀ n (X Y : A n), τ n (X * Y) = τ n (Y * X))
    (n : ℕ) {P_n : A n} (hP_n : P_n * P_n = P_n) (X_n Y_n : A n)
    (c : ℕ → R) (d : ℕ) (c₀ : R) (k : ℕ)
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (ψ : InfoGeometry.QuantumGeometry.Projective.NormalizedState ℋ)
    (X_op Y_op : ℋ →L[ℂ] ℋ) :
    let of_n := DirectLimit.Ring.of A ι n
    let P_inf := of_n P_n
    let Φ_inf := genPhi P_inf (of_n X_n) (of_n Y_n)
    let J_inf := genJ P_inf (of_n X_n) (of_n Y_n)
    let V_inf := genV P_inf (of_n X_n) (of_n Y_n)
    let Sig_inf := genSig P_inf (of_n X_n) (of_n Y_n)
    let τ_inf : DirectLimit A ι →+ K := directLimitTraceLift ι τ h_cocone
    -- (0) Acyclic 7-stage causal poset & Rung 0 scalar infinitesimal aporia
    ((∀ s : JaynesColimitNilpotentStage, ¬ Relation.TransGen JaynesColimitNilpotentStage.causalEdge s s) ∧
     dx = 0) ∧
    -- (1) Stage 𝔍₁: Nilpotent first-order polynomial Taylor truncation without limits
    (conePlus P_n X_n * conePlus P_n X_n = 0 ∧
     polyJetEval c d (algebraMap R (A n) c₀ + conePlus P_n X_n) =
       algebraMap R (A n) (polyScalarVal c d c₀) +
         algebraMap R (A n) (polyScalarDeriv c d c₀) * conePlus P_n X_n) ∧
    -- (2) Stage 𝔍₄: Chiral filter kills odd jump while preserving even metric & directional tension
    (chiralEvenFilter2 P_n (genJ P_n X_n Y_n) = 0 ∧
     chiralEvenFilter2 P_n (genV P_n X_n Y_n) = (2 : ℤ) • genV P_n X_n Y_n ∧
     scaleRefine2 (coarseReadout2 witnessNilpotentPlus) = 0 ∧
     witnessNilpotentPlus ≠ 0) ∧
    -- (3) Stages 𝔍₅–𝔍₆: Algebraic DirectLimit Peirce/Clocking identities and trace cancellation
    (Equivalence (ColimitRel ι) ∧
     Φ_inf * Φ_inf = V_inf ∧
     OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf = -((2 : ℤ) • Sig_inf) ∧
     -OperatorAlgebra.PeirceSpine.comm Φ_inf (OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf) =
       -((2 : ℤ) • OperatorAlgebra.PeirceSpine.comm Sig_inf Φ_inf) ∧
     -OperatorAlgebra.PeirceSpine.comm Φ_inf (OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf) =
       -((4 : ℤ) • (V_inf * J_inf)) ∧
     (2 : ℤ) • (invS P_inf * V_inf ^ (k + 1)) =
       OperatorAlgebra.PeirceSpine.comm J_inf (Φ_inf ^ (2 * k + 1))) ∧
    -- (4) Stage 𝔍₇: Additive trace-cocone cancellation and the separate Cramér-Rao bound
    (τ_inf (invS P_inf * V_inf ^ (k + 1)) = 0 ∧
     τ_inf ((2 : ℤ) • (invS P_inf * V_inf ^ (k + 1))) = 0 ∧
     onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
       (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
         (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2) := by
  have hJ1 := theorem1_exact_first_order_taylor_truncation hP_n X_n c d c₀
  have hJ4 :=
    archetype_J4_downward_readout_chiral_filter_and_directional_tension
      hP_n X_n Y_n 0 witnessNilpotentPlus
  have hJ6 :=
    theorem3_direct_limit_transfer_peirce_clocking_identities
      ι n hP_n X_n Y_n k
  have hJ7 :=
    theorem4_trace_cocone_chiral_cancellation_and_cramer_rao
      ι τ h_cocone h_tracial (colimitRel_refl ι ⟨n, X_n⟩) n hP_n X_n Y_n k ψ X_op Y_op
  have hJ7_graded :=
    theorem4_colimit_graded_metric_moment_trace_zero
      ι τ h_cocone h_tracial n hP_n X_n Y_n k
  exact ⟨⟨JaynesColimitNilpotentStage.causalEdge_acyclic,
          rung0_scalar_infinitesimal_self_destructs dx h_dx_sq⟩,
         ⟨hJ1.1, hJ1.2.2.2⟩,
         ⟨hJ4.1, hJ4.2.2.1, hJ4.2.2.2.2.2.1, hJ4.2.2.2.2.2.2.2⟩,
         ⟨⟨colimitRel_refl ι, colimitRel_symm ι, colimitRel_trans ι⟩,
          hJ6.2.1, hJ6.2.2.1, hJ6.2.2.2.2.1, hJ6.2.2.2.2.2.1, hJ6.2.2.2.2.2.2⟩,
         ⟨hJ7_graded, ⟨hJ7.2.2.1, hJ7.2.2.2⟩⟩⟩

/-- **Concrete Non-Commutative `2 × 2` Matrix Witness (`jaynes_colimit_nilpotent_matrix_witness`)**:
Certifies Traps `T16` (non-commutativity) and `T17` (non-zero nilpotent & exact first-order jet)
on `Matrix (Fin 2) (Fin 2) ℤ`:
1. `witnessNilpotentPlus ≠ 0` while `witnessNilpotentPlus * witnessNilpotentPlus = 0`,
2. `witnessProj2 * witnessNilpotentPlus ≠ witnessNilpotentPlus * witnessProj2` (`T16`),
3. `(1 + witnessNilpotentPlus) ^ 3 = !![1, 3; 0, 1]` (exact first-order binomial jet `1 + 3 N_+`),
4. `scaleRefine2 (coarseReadout2 witnessNilpotentPlus) = 0 ≠ witnessNilpotentPlus` (irreversible
   coarse-graining defect). -/
theorem jaynes_colimit_nilpotent_matrix_witness :
    witnessNilpotentPlus ≠ 0 ∧
    witnessNilpotentPlus * witnessNilpotentPlus = 0 ∧
    witnessNilpotentProj * witnessNilpotentPlus ≠ witnessNilpotentPlus * witnessNilpotentProj ∧
    (1 + witnessNilpotentPlus) ^ 3 = !![(1 : ℤ), 3; 0, 1] ∧
    scaleRefine2 (coarseReadout2 witnessNilpotentPlus) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [witnessNilpotentPlus] at h01
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [witnessNilpotentPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [witnessNilpotentProj, witnessNilpotentPlus, Matrix.mul_apply, Fin.sum_univ_two] at h01
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, witnessNilpotentPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-! ===========================================================================
    Section 8: Cross-Module Unification of the Three Jaynesian Colimit Posets
    (`JaynesColimitNilpotentStage` ≃o `JaynesianColimitStage` ≃o
     `JaynesianColimitContinuumStage`)
    =========================================================================== -/

section ThreeLaneUnification

open scoped Polynomial
open InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitPoset
open InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitContinuumPoset

/-- Canonical bijection from `JaynesColimitNilpotentStage` to `JaynesianColimitStage`. -/
def toJaynesianColimitStage : JaynesColimitNilpotentStage → JaynesianColimitStage
  | .J1_NilpotentReplacementOfInfinitesimals        => .J1_NilpotentReplacementOfInfinitesimals
  | .J2_DirectedPosetOfFiniteOperatorAlgebras       => .J2_DirectedPosetOfFiniteOperatorAlgebras
  | .J3_UpwardAlgebraicScalePreservation            => .J3_UpwardAlgebraicPreservation
  | .J4_DownwardLinearReadoutRetraction             => .J4_DownwardConditionalExpectation
  | .J5_AlgebraicDirectLimitConstruction            => .J5_InductiveColimitContinuumQuotient
  | .J6_DirectLimitTransferOfPolynomialIdentities    => .J6_UniversalColimitDifferentialCurvatureTransfer
  | .J7_TraceCoconeCancellationAndCramerRaoBound    => .J7_ColimitTracialIntegrationGaussBonnetClosure

/-- Canonical inverse bijection from `JaynesianColimitStage` to `JaynesColimitNilpotentStage`. -/
def ofJaynesianColimitStage : JaynesianColimitStage → JaynesColimitNilpotentStage
  | .J1_NilpotentReplacementOfInfinitesimals          => .J1_NilpotentReplacementOfInfinitesimals
  | .J2_DirectedPosetOfFiniteOperatorAlgebras         => .J2_DirectedPosetOfFiniteOperatorAlgebras
  | .J3_UpwardAlgebraicPreservation                   => .J3_UpwardAlgebraicScalePreservation
  | .J4_DownwardConditionalExpectation                => .J4_DownwardLinearReadoutRetraction
  | .J5_InductiveColimitContinuumQuotient             => .J5_AlgebraicDirectLimitConstruction
  | .J6_UniversalColimitDifferentialCurvatureTransfer => .J6_DirectLimitTransferOfPolynomialIdentities
  | .J7_ColimitTracialIntegrationGaussBonnetClosure   => .J7_TraceCoconeCancellationAndCramerRaoBound

theorem toJaynesianColimitStage_rank (s : JaynesColimitNilpotentStage) :
    JaynesianColimitStage.rank (toJaynesianColimitStage s) =
      JaynesColimitNilpotentStage.rank s := by
  cases s <;> rfl

/-- Order isomorphism `JaynesColimitNilpotentStage ≃o JaynesianColimitStage` preserving the
7-stage topological rank `0..6`. -/
def jaynesStageOrderIsoPoset :
    JaynesColimitNilpotentStage ≃o JaynesianColimitStage where
  toFun := toJaynesianColimitStage
  invFun := ofJaynesianColimitStage
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;> decide

/-- Every covering edge of `JaynesColimitNilpotentStage` maps to a covering edge of
`JaynesianColimitStage`. -/
theorem causalEdge_imp_poset_causalEdge
    {a b : JaynesColimitNilpotentStage}
    (h : JaynesColimitNilpotentStage.causalEdge a b) :
    JaynesianColimitStage.causalEdge
      (toJaynesianColimitStage a) (toJaynesianColimitStage b) := by
  cases a <;> cases b <;> simp [JaynesColimitNilpotentStage.causalEdge] at h ⊢ <;>
    exact trivial

/-- Canonical bijection from `JaynesColimitNilpotentStage` to `JaynesianColimitContinuumStage`. -/
def toJaynesianColimitContinuumStage :
    JaynesColimitNilpotentStage → JaynesianColimitContinuumStage
  | .J1_NilpotentReplacementOfInfinitesimals        => .J1_NilpotentKockLawverePolynomialTaylorTruncation
  | .J2_DirectedPosetOfFiniteOperatorAlgebras       => .J2_DirectedSystemOfFiniteOperatorAlgebras
  | .J3_UpwardAlgebraicScalePreservation            => .J3_UpwardFunctorialInvarianceOfThePeirceCartanSpine
  | .J4_DownwardLinearReadoutRetraction             => .J4_DownwardConditionalExpectationRetractionAndChiralFilter
  | .J5_AlgebraicDirectLimitConstruction            => .J5_InductiveColimitContinuumConstruction
  | .J6_DirectLimitTransferOfPolynomialIdentities    => .J6_UniversalColimitTransferOfEinsteinCartanAndGaussBonnetLaws
  | .J7_TraceCoconeCancellationAndCramerRaoBound    => .J7_TracialCoconeCoherenceAndColimitSupertraceInvariance

/-- Canonical inverse bijection from `JaynesianColimitContinuumStage` to
`JaynesColimitNilpotentStage`. -/
def ofJaynesianColimitContinuumStage :
    JaynesianColimitContinuumStage → JaynesColimitNilpotentStage
  | .J1_NilpotentKockLawverePolynomialTaylorTruncation            => .J1_NilpotentReplacementOfInfinitesimals
  | .J2_DirectedSystemOfFiniteOperatorAlgebras                    => .J2_DirectedPosetOfFiniteOperatorAlgebras
  | .J3_UpwardFunctorialInvarianceOfThePeirceCartanSpine          => .J3_UpwardAlgebraicScalePreservation
  | .J4_DownwardConditionalExpectationRetractionAndChiralFilter   => .J4_DownwardLinearReadoutRetraction
  | .J5_InductiveColimitContinuumConstruction                     => .J5_AlgebraicDirectLimitConstruction
  | .J6_UniversalColimitTransferOfEinsteinCartanAndGaussBonnetLaws => .J6_DirectLimitTransferOfPolynomialIdentities
  | .J7_TracialCoconeCoherenceAndColimitSupertraceInvariance      => .J7_TraceCoconeCancellationAndCramerRaoBound

theorem toJaynesianColimitContinuumStage_rank (s : JaynesColimitNilpotentStage) :
    JaynesianColimitContinuumStage.rank (toJaynesianColimitContinuumStage s) =
      JaynesColimitNilpotentStage.rank s := by
  cases s <;> rfl

/-- Order isomorphism `JaynesColimitNilpotentStage ≃o JaynesianColimitContinuumStage` preserving
the 7-stage topological rank `0..6`. -/
def jaynesStageOrderIsoContinuum :
    JaynesColimitNilpotentStage ≃o JaynesianColimitContinuumStage where
  toFun := toJaynesianColimitContinuumStage
  invFun := ofJaynesianColimitContinuumStage
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;> decide

/-- Every covering edge of `JaynesColimitNilpotentStage` maps to a strict causal edge of
`JaynesianColimitContinuumStage`. -/
theorem causalEdge_imp_continuum_causalEdge
    {a b : JaynesColimitNilpotentStage}
    (h : JaynesColimitNilpotentStage.causalEdge a b) :
    JaynesianColimitContinuumStage.causalEdge
      (toJaynesianColimitContinuumStage a) (toJaynesianColimitContinuumStage b) := by
  unfold JaynesianColimitContinuumStage.causalEdge
  rw [toJaynesianColimitContinuumStage_rank, toJaynesianColimitContinuumStage_rank]
  exact JaynesColimitNilpotentStage.causalEdge_strict_rank_mono h

/-- **Three-Lane Jaynesian Colimit Unification Bridge (`jaynes_three_lane_colimit_unification_synthesis`)**:
Unifies the three sibling Jaynesian Inductive Colimit & Nilpotent Reality formalizations:
1. **Poset Isomorphism**: Rank-preserving order equivalences across `JaynesColimitNilpotentStage`,
   `JaynesianColimitStage`, and `JaynesianColimitContinuumStage`,
2. **Stage `𝔍₁` Dual Polynomial Jet**: Unites the `Finset.range d` jet `polyJetEval` with the
   `Polynomial R` Kock–Lawvere jet `Polynomial.eval₂` at `algebraMap R (A n) c₀ + conePlus P_n X_n`,
3. **Stages `𝔍₅`–`𝔍₇` Ring DirectLimit ↔ Additive DirectLimit Trace Agreement**:
   The ring-colimit trace lift `directLimitTraceLift ι τ h_cocone (DirectLimit.Ring.of A ι n z)`
   and the additive-colimit trace lift
   `AddCommGroup.DirectLimit.lift A ι_add K τ h_cocone (AddCommGroup.DirectLimit.of A ι_add n z)`
   both evaluate identically to `τ n z`, and both annihilate `(2 : ℤ) • (invS P * V^(k+1))` and
   `invS P * V^(k+1)`,
4. **Concrete `2^n × 2^n` Cuntz Matrix Tower & Cramér–Rao Closure**:
   `traceFunctional (invS P_cuntz * genV P_cuntz A_cuntz C_cuntz ^ (k + 1)) = 0` and
   `g(X_op, X_op) * g(Y_op, Y_op) ≥ g(X_op, Y_op)^2 + (1 / 4) * Ω(X_op, Y_op)^2`. -/
theorem jaynes_three_lane_colimit_unification_synthesis
    {R : Type*} [CommRing R]
    {A : ℕ → Type*} [∀ n, Ring (A n)] [∀ n, Algebra R (A n)]
    (ι : ∀ m n, m ≤ n → A m →+* A n)
    [DirectedSystem A (fun m n h => ι m n h)]
    [DirectedSystem A (fun m n h => (ι m n h).toAddMonoidHom)]
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n, A n →+ K)
    (h_cocone : ∀ m n (h : m ≤ n) (x : A m), τ n (ι m n h x) = τ m x)
    (h_tracial : ∀ n (X Y : A n), τ n (X * Y) = τ n (Y * X))
    (n : ℕ) {P_n : A n} (hP_n : P_n * P_n = P_n) (X_n Y_n : A n)
    (c : ℕ → R) (d : ℕ) (c₀ : R) (F : R[X]) (k : ℕ)
    (P_cuntz A_cuntz C_cuntz : InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier)
    (hP_cuntz : P_cuntz * P_cuntz = P_cuntz)
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (ψ : InfoGeometry.QuantumGeometry.Projective.NormalizedState ℋ)
    (X_op Y_op : ℋ →L[ℂ] ℋ) :
    let of_n := DirectLimit.Ring.of A ι n
    let P_inf := of_n P_n
    let V_inf := genV P_inf (of_n X_n) (of_n Y_n)
    let τ_ring : DirectLimit A ι →+ K := directLimitTraceLift ι τ h_cocone
    let ι_add : ∀ m l, m ≤ l → A m →+ A l := fun m l h => (ι m l h).toAddMonoidHom
    let τ_add : AddCommGroup.DirectLimit A ι_add →+ K :=
      AddCommGroup.DirectLimit.lift A ι_add K τ h_cocone
    -- (1) Poset rank-preserving equivalences across all 3 Jaynesian colimit posets
    ((∀ s : JaynesColimitNilpotentStage,
        JaynesianColimitStage.rank (jaynesStageOrderIsoPoset s) = s.rank ∧
        JaynesianColimitContinuumStage.rank (jaynesStageOrderIsoContinuum s) = s.rank) ∧
     (∀ a b : JaynesColimitNilpotentStage,
        JaynesColimitNilpotentStage.causalEdge a b →
          JaynesianColimitStage.causalEdge (toJaynesianColimitStage a) (toJaynesianColimitStage b) ∧
          JaynesianColimitContinuumStage.causalEdge
            (toJaynesianColimitContinuumStage a) (toJaynesianColimitContinuumStage b))) ∧
    -- (2) Both Finset polynomial jet and R[X] Kock-Lawvere polynomial jet truncate at 1st order
    (polyJetEval c d (algebraMap R (A n) c₀ + conePlus P_n X_n) =
       algebraMap R (A n) (polyScalarVal c d c₀) +
         algebraMap R (A n) (polyScalarDeriv c d c₀) * conePlus P_n X_n ∧
     Polynomial.eval₂ (algebraMap R (A n)) (algebraMap R (A n) c₀ + conePlus P_n X_n) F =
       algebraMap R (A n) (F.eval c₀) +
         algebraMap R (A n) ((Polynomial.derivative F).eval c₀) * conePlus P_n X_n) ∧
    -- (3) Ring DirectLimit trace lift and AddCommGroup DirectLimit trace lift agree on every stage
    (τ_ring (of_n X_n) = τ_add (AddCommGroup.DirectLimit.of A ι_add n X_n) ∧
     τ_ring (invS P_inf * V_inf ^ (k + 1)) = 0 ∧
     τ_add (AddCommGroup.DirectLimit.of A ι_add n
       (invS P_n * genV P_n X_n Y_n ^ (k + 1))) = 0) ∧
    -- (4) Concrete Cuntz matrix tower trace cancellation & Metriplectic Cramér-Rao closure
    (InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional.traceFunctional
       (invS P_cuntz * genV P_cuntz A_cuntz C_cuntz ^ (k + 1)) = 0 ∧
     onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
       (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
         (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2) := by
  intro of_n P_inf V_inf τ_ring ι_add τ_add
  have hNp : conePlus P_n X_n * conePlus P_n X_n = 0 := conePlus_mul_conePlus hP_n X_n X_n
  have hJ1 := theorem1_exact_first_order_taylor_truncation hP_n X_n c d c₀
  have hKL :=
    (stage_J1_nilpotent_kock_lawvere_polynomial_taylor_truncation
      c₀ (conePlus P_n X_n) P_n X_n Y_n hNp hP_n F).1
  have hRingGraded :=
    theorem4_colimit_graded_metric_moment_trace_zero
      ι τ h_cocone h_tracial n hP_n X_n Y_n k
  have hAddLift :
      τ_add (AddCommGroup.DirectLimit.of A ι_add n X_n) = τ n X_n :=
    AddCommGroup.DirectLimit.lift_of
      (G := A) (f := ι_add) (P := K) (g := τ) (Hg := h_cocone) n X_n
  have hAddGraded :
      τ_add (AddCommGroup.DirectLimit.of A ι_add n
        (invS P_n * genV P_n X_n Y_n ^ (k + 1))) = 0 := by
    rw [AddCommGroup.DirectLimit.lift_of
      (G := A) (f := ι_add) (P := K) (g := τ) (Hg := h_cocone)
      n (invS P_n * genV P_n X_n Y_n ^ (k + 1))]
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments.cyclic_grading_metric_power_zero
      (τ n) (h_tracial n) hP_n X_n Y_n k
  refine ⟨⟨fun s => ⟨toJaynesianColimitStage_rank s, toJaynesianColimitContinuumStage_rank s⟩,
           fun a b hab => ⟨causalEdge_imp_poset_causalEdge hab,
                           causalEdge_imp_continuum_causalEdge hab⟩⟩,
          ⟨hJ1.2.2.2, hKL⟩,
          ⟨hAddLift.symm, hRingGraded, hAddGraded⟩,
          ⟨concrete_cuntz_matrix_tower_graded_moment_trace_zero P_cuntz A_cuntz C_cuntz hP_cuntz k,
           cramerRao_metriplectic_full_bound ψ X_op Y_op⟩⟩

end ThreeLaneUnification

end InfoGeometry.Canonical.JaynesInductiveColimitNilpotentPoset
