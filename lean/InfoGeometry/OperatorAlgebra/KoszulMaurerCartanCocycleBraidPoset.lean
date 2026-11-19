/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.UniversalArtinBraidRepresentation
import InfoGeometry.Causal.FiniteDependencyCompiler
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Meta.MetaEpistemicCompiler
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset

Noncommutative epistemic-compiler formalization ("solve et coagula") uniting:
- **$\mathcal{A}_1$ (Associative Jet Obstruction)**: Degree-2 BCH commutator obstruction and
  additive vs multiplicative exponential failure in arbitrary noncommutative rings `B`, plus a
  concrete `Matrix (Fin 2) (Fin 2) B` noncommutativity witness.
- **$\mathcal{A}_2$ (Brauer–Weyl $(1,1)$-Periodicity & Quaternions)**: Clifford $\mathrm{Cl}(1,1)$
  and CAR operators in `M₂(B)`, Brauer–Weyl Klein-twist recursion, and embedded quaternion Lie
  triple `qE₁, qE₂, qE₃ ∈ NestedMat B := M₂(M₂(B))`.
- **$\mathcal{A}_3$ (Noncommutative Ring Derivations)**: Leibniz identity, unit-inverse
  differentiation `d (u⁻¹) = -u⁻¹ * d u * u⁻¹`, inner commutator derivations `innerDeriv K`
  (commuting whenever `⁅K₁, K₂⁆ = 0`), and `Mₙ`-matrix lifting `liftMatrixDeriv`.
- **$\mathcal{A}_4$ (Koszul Curvature & Bianchi Identity)**: Koszul covariant operator `covOp`,
  Maurer–Cartan curvature `mcCurvature`, gauge dressing `dressConn`, adjoint covariant derivative
  `adjDeriv`, conjugation covariance, logarithmic flatness, differential Bianchi identity, and
  nontrivial commuting inner-derivation realization on `NestedMat B`.
- **$\mathcal{A}_5$ (Twisted Group 1-Cocycle)**: `Z * X = Q * X * Z` braiding iteration via
  `twistedCocycle X Q n`, multiplicative 1-cocycle additivity, involutive phase inversion, and
  torsion obstruction `X ^ N = 1 → twistedCocycle X Q N = 1`.
- **$\mathcal{A}_6$ (Parabolic Witt-Link Monodromy)**: Nilpotent split `1 + nilpPar` (`nilpPar² = 0`),
  noncommuting integer `2 × 2` block matrices `blkX, blkZ, blkQ : BlockMatZ` embedding into
  `(BlockMatZ)ˣ`, discharging the `A5` braiding laws and proving infinite parabolic order
  `blkQ ^ n ≠ 1` for all `n > 0`.
- **$\mathcal{A}_7$ (Artin Braid Group $B_3$ Representation & Master Synthesis)**: Genuine
  monoid homomorphism `quaternionicBraidGroup3Hom : Braid.braid_group 3 →* (NestedMat ℂ)ˣ`
  built via `InfoGeometry.Categorical.UniversalArtinBraidRepresentation.ArtinBraidSystem`,
  proving nonabelian image (`σ₀ σ₁ ≠ σ₁ σ₀`), exact braid-commutator Maurer–Cartan identity
  `⁅qR₁₂, qR₂₃⁆ = mcCurvature 0 0 qE₁ qE₂ = 2 * qE₃`, and executable certified compilation of
  the 7-node diamond causal poset `KoszulCocycleBraidArchetype`.

## Three-Bucket Audit Map

* **BUCKET 1 (Reused upstream owners)**:
  - `InfoGeometry.Categorical.UniversalArtinBraidRepresentation`:
    `ArtinBraidSystem`, `ArtinBraidSystem.toGroupHom`, `ArtinBraidSystem.toGroupHom_generator`.
  - `InfoGeometry.Algebra.FiniteSpin`: `Mat2Z`.
  - `InfoGeometry.MetaCompiler`: `TypedArchetype`, `Phase`, `executable_certified_compilation`,
    `#register_archetype`, `#audit_archetype`.
  - `InfoGeometry.Causal.FiniteDependencyCompiler` & `ProofCarryingSchedule`:
    `compile`, `ValidSchedule`, `ProofRules`.
  - Mathlib: `Ring.lie_def`, `Matrix`, `Units`, `noncomm_ring`.
* **BUCKET 2 (New native theorems)**:
  - Commuting inner-derivation curvature/Bianchi realization `nested_inner_deriv_curvature_and_bianchi`.
  - Full noncommutative ring/group proofs for `expJet2`, Brauer–Weyl periodicity, Koszul
    Maurer–Cartan/Bianchi identities, `twistedCocycle` torsion obstruction, and algebraic block
    proofs of `blkQ_infinite_order` (avoiding scalar diagonal toys).
  - Genuine invertible units `qR12Unit, qR23Unit : (NestedMat ℂ)ˣ`, nonabelian `ArtinBraidSystem`
    homomorphism `quaternionicBraidGroup3Hom : Braid.braid_group 3 →* (NestedMat ℂ)ˣ`, and
    certified diamond poset `koszul_cocycle_braid_executable_certified_compilation`.
* **BUCKET 3 (Explicit hypotheses / scope)**:
  - General noncommutative ring `[Ring B]` results carry explicit commuting-derivation and
    matrix-size hypotheses; infinite-dimensional Lie-algebra exponentials (all-order BCH series)
    are truncated cleanly to the associative 2-jet `expJet2`.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset

open InfoGeometry.Categorical.UniversalArtinBraidRepresentation
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.MetaCompiler

section ScalarHelpers

private theorem q0Mat_step_00 (n : ℕ) :
    (1 - (n : ℤ)) * 0 + (-(n : ℤ)) * 1 = 1 - ((n + 1 : ℕ) : ℤ) := by
  push_cast
  ring

private theorem q0Mat_step_01 (n : ℕ) :
    (1 - (n : ℤ)) * (-1) + (-(n : ℤ)) * 2 = -((n + 1 : ℕ) : ℤ) := by
  push_cast
  ring

private theorem q0Mat_step_10 (n : ℕ) :
    (n : ℤ) * 0 + (1 + (n : ℤ)) * 1 = ((n + 1 : ℕ) : ℤ) := by
  push_cast
  ring

private theorem q0Mat_step_11 (n : ℕ) :
    (n : ℤ) * (-1) + (1 + (n : ℤ)) * 2 = 1 + ((n + 1 : ℕ) : ℤ) := by
  push_cast
  ring

end ScalarHelpers

/-!
## Archetype $\mathcal{A}_1$: Associative 2-Jet Obstruction & Matrix Noncommutativity
-/

section ArchetypeA1_AssociativeJetObstruction

variable {B : Type*} [Ring B]

/-- Rescaled degree-2 associative exponential jet `2 + 2X + X²` requiring no rational division. -/
def expJet2 (X : B) : B := 2 + 2 * X + X * X

/-- Exact noncommutative BCH degree-2 commutator obstruction for `expJet2`. -/
theorem bch_jet2_commutator_obstruction (X Y : B) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X =
      4 * ⁅X, Y⁆ +
      2 * (X * X * Y - Y * (X * X) + X * (Y * Y) - Y * Y * X) +
      (X * X * (Y * Y) - Y * Y * (X * X)) := by
  dsimp [expJet2]
  rw [Ring.lie_def]
  noncomm_ring

/-- On square-zero elements, the commutator obstruction of `expJet2` reduces strictly to `4 * ⁅X, Y⁆`. -/
theorem bch_jet2_nilpotent_commutator {X Y : B} (hX : X * X = 0) (hY : Y * Y = 0) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X = 4 * ⁅X, Y⁆ := by
  rw [bch_jet2_commutator_obstruction, hX, hY]
  noncomm_ring

/-- Exact defect separating the multiplicative product `expJet2 X * expJet2 Y` from the additive
lift `2 * expJet2 (X + Y)`. -/
theorem bch_jet2_product_expansion (X Y : B) :
    expJet2 X * expJet2 Y - 2 * expJet2 (X + Y) =
      2 * ⁅X, Y⁆ + 2 * (X * X * Y + X * (Y * Y)) + X * X * (Y * Y) := by
  dsimp [expJet2]
  rw [Ring.lie_def]
  noncomm_ring

/-- On square-zero elements, even the naive additive product law fails by `2 * ⁅X, Y⁆`. -/
theorem bch_jet2_product_of_sq_zero {X Y : B} (hX : X * X = 0) (hY : Y * Y = 0) :
    expJet2 X * expJet2 Y - 2 * expJet2 (X + Y) = 2 * ⁅X, Y⁆ := by
  rw [bch_jet2_product_expansion, hX, hY]
  noncomm_ring

/-- Strict noncommutativity witness for `Matrix (Fin 2) (Fin 2) B` over any nontrivial ring `B`. -/
theorem matrix_fin2_noncommutative [Nontrivial B] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) B, X * Y ≠ Y * X := by
  let swapMat : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![0, 1], ![1, 0]]
  let projMat : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![1, 0], ![0, 0]]
  refine ⟨swapMat, projMat, ?_⟩
  intro hMul
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 1 0) hMul
  simp [Matrix.mul_apply, Fin.sum_univ_two, swapMat, projMat] at h10

end ArchetypeA1_AssociativeJetObstruction

/-!
## Archetype $\mathcal{A}_2$: Brauer–Weyl $(1,1)$-Periodicity & Quaternion Triple in $M_2(M_2(B))$
-/

section ArchetypeA2_BrauerWeylQuaternionChain

private theorem ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Infrastructure
variable {B : Type*} [Ring B]

/-- Noncommutative anticommutator `X * Y + Y * X`. -/
def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

/-- Spacelike reflection / Pauli `σ₁` operator in `M₂(B)`. -/
def sigmaOp : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![0, 1], ![1, 0]]

/-- Timelike reflection / skew-symmetric `iσ₂` operator in `M₂(B)`. -/
def omegaOp : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![0, -1], ![1, 0]]

/-- Grading involution `σ₃` operator in `M₂(B)`. -/
def gammaOneOp : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![1, 0], ![0, -1]]

/-- Fermionic raising Witt nilpotent in `M₂(B)`. -/
def fPlus : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![0, 1], ![0, 0]]

/-- Fermionic lowering Witt nilpotent in `M₂(B)`. -/
def fMinus : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![0, 0], ![1, 0]]

/-- Untwisted block-diagonal fiber embedding `x ↦ diag(x, x)` in `M₂(B)`. -/
def fiberEmbed (x : B) : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![x, 0], ![0, x]]

/-- Graded Brauer–Weyl Klein twist `x ↦ diag(x, -x)` in `M₂(B)`. -/
def kleinTwist (x : B) : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![x, 0], ![0, -x]]

/-- Canonical `Cl(1,1)` Clifford relations and Witt CAR relations inside `M₂(B)`. -/
theorem cl11_and_witt_car_relations :
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) * sigmaOp = 1 ∧
    (omegaOp : Matrix (Fin 2) (Fin 2) B) * omegaOp = -1 ∧
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) * omegaOp = gammaOneOp ∧
    (gammaOneOp : Matrix (Fin 2) (Fin 2) B) * gammaOneOp = 1 ∧
    anticomm (sigmaOp : Matrix (Fin 2) (Fin 2) B) omegaOp = 0 ∧
    (fPlus : Matrix (Fin 2) (Fin 2) B) * fPlus = 0 ∧
    (fMinus : Matrix (Fin 2) (Fin 2) B) * fMinus = 0 ∧
    anticomm (fPlus : Matrix (Fin 2) (Fin 2) B) fMinus = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply ext_fin2 <;>
        simp [sigmaOp, omegaOp, gammaOneOp, fPlus, fMinus, anticomm,
          Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]

/-- Brauer–Weyl `(1,1)`-periodicity doubling step via Klein-twisted tensor generators. -/
theorem brauer_weyl_periodicity_step {e₁ e₂ s₁ s₂ : B}
    (he₁ : e₁ * e₁ = s₁) (he₂ : e₂ * e₂ = s₂) (hAnti : anticomm e₁ e₂ = 0) :
    kleinTwist e₁ * kleinTwist e₁ = fiberEmbed s₁ ∧
    kleinTwist e₂ * kleinTwist e₂ = fiberEmbed s₂ ∧
    anticomm (kleinTwist e₁) (sigmaOp : Matrix (Fin 2) (Fin 2) B) = 0 ∧
    anticomm (kleinTwist e₂) (sigmaOp : Matrix (Fin 2) (Fin 2) B) = 0 ∧
    anticomm (kleinTwist e₁) (omegaOp : Matrix (Fin 2) (Fin 2) B) = 0 ∧
    anticomm (kleinTwist e₂) (omegaOp : Matrix (Fin 2) (Fin 2) B) = 0 ∧
    anticomm (kleinTwist e₁) (kleinTwist e₂) = 0 := by
  have hProd : ∀ x y : B, kleinTwist x * kleinTwist y = fiberEmbed (x * y) := by
    intro x y
    apply ext_fin2 <;>
      simp [kleinTwist, fiberEmbed, Matrix.mul_apply, Fin.sum_univ_two]
  have hAntiLift : anticomm (kleinTwist e₁) (kleinTwist e₂) = fiberEmbed (anticomm e₁ e₂) := by
    apply ext_fin2 <;>
      simp [anticomm, kleinTwist, fiberEmbed]
  refine ⟨by rw [hProd, he₁], by rw [hProd, he₂], ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [anticomm, kleinTwist, sigmaOp]
  · apply ext_fin2 <;> simp [anticomm, kleinTwist, sigmaOp]
  · apply ext_fin2 <;> simp [anticomm, kleinTwist, omegaOp]
  · apply ext_fin2 <;> simp [anticomm, kleinTwist, omegaOp]
  · rw [hAntiLift, hAnti]
    apply ext_fin2 <;> simp [fiberEmbed]

end Matrix2Infrastructure

/-- Nested `2 × 2` block matrices `M₂(M₂(B))`. -/
abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- First embedded quaternion generator `qE₁ ∈ M₂(M₂(B))`. -/
def qE1 {B : Type*} [Ring B] : NestedMat B := omegaOp

/-- Second embedded quaternion generator `qE₂ ∈ M₂(M₂(B))` constructed via Brauer–Weyl twist. -/
def qE2 {B : Type*} [Ring B] : NestedMat B := kleinTwist omegaOp

/-- Third embedded quaternion generator `qE₃ := qE₁ * qE₂ ∈ M₂(M₂(B))`. -/
def qE3 {B : Type*} [Ring B] : NestedMat B := (qE1 : NestedMat B) * qE2

/-- Embedded quaternion Clifford and `sp(1)` Lie bracket relations in `NestedMat B`. -/
theorem nested_quaternion_lie_relations {B : Type*} [Ring B] :
    (qE1 : NestedMat B) * qE1 = -1 ∧
    (qE2 : NestedMat B) * qE2 = -1 ∧
    (qE3 : NestedMat B) * qE3 = -1 ∧
    anticomm (qE1 : NestedMat B) qE2 = 0 ∧
    ⁅(qE1 : NestedMat B), qE2⁆ = (2 : NestedMat B) * qE3 ∧
    ⁅(qE2 : NestedMat B), qE3⁆ = (2 : NestedMat B) * qE1 ∧
    ⁅(qE3 : NestedMat B), qE1⁆ = (2 : NestedMat B) * qE2 := by
  have h1 : (qE1 : NestedMat B) * qE1 = -1 :=
    (cl11_and_witt_car_relations (B := Matrix (Fin 2) (Fin 2) B)).2.1
  have hStep := brauer_weyl_periodicity_step (B := Matrix (Fin 2) (Fin 2) B)
    (cl11_and_witt_car_relations (B := B)).1
    (cl11_and_witt_car_relations (B := B)).2.1
    (cl11_and_witt_car_relations (B := B)).2.2.2.2.1
  have h2 : (qE2 : NestedMat B) * qE2 = -1 := by
    dsimp [qE2]
    rw [hStep.2.1]
    apply ext_fin2 <;>
      simp [fiberEmbed, Matrix.neg_apply]
  have h12Anti : anticomm (qE1 : NestedMat B) qE2 = 0 := by
    dsimp [anticomm, qE1, qE2]
    have ha := hStep.2.2.2.2.2.1
    dsimp [anticomm] at ha
    calc (omegaOp : NestedMat B) * kleinTwist omegaOp + kleinTwist omegaOp * omegaOp
      _ = kleinTwist omegaOp * omegaOp + omegaOp * kleinTwist omegaOp := by abel
      _ = 0 := ha
  have h21 : (qE2 : NestedMat B) * qE1 = -((qE1 : NestedMat B) * qE2) := by
    dsimp [anticomm] at h12Anti
    calc (qE2 : NestedMat B) * qE1
      _ = (qE1 * qE2 + qE2 * qE1) - qE1 * qE2 := by abel
      _ = 0 - qE1 * qE2 := by rw [h12Anti]
      _ = -(qE1 * qE2) := zero_sub _
  have h3 : (qE3 : NestedMat B) * qE3 = -1 := by
    calc (qE3 : NestedMat B) * qE3
      _ = qE1 * (qE2 * qE1) * qE2 := by dsimp [qE3]; noncomm_ring
      _ = qE1 * (-(qE1 * qE2)) * qE2 := by rw [h21]
      _ = -((qE1 * qE1) * (qE2 * qE2)) := by noncomm_ring
      _ = -((-1) * (-1)) := by rw [h1, h2]
      _ = -1 := by noncomm_ring
  refine ⟨h1, h2, h3, h12Anti, ?_, ?_, ?_⟩
  · rw [Ring.lie_def, h21]
    dsimp [qE3]
    noncomm_ring
  · rw [Ring.lie_def]
    dsimp [qE3]
    calc (qE2 : NestedMat B) * ((qE1 : NestedMat B) * (qE2 : NestedMat B)) -
          (qE1 : NestedMat B) * (qE2 : NestedMat B) * (qE2 : NestedMat B)
      _ = ((qE2 : NestedMat B) * qE1) * qE2 - (qE1 : NestedMat B) * (qE2 * qE2) := by noncomm_ring
      _ = (-((qE1 : NestedMat B) * qE2)) * qE2 - (qE1 : NestedMat B) * (-1) := by rw [h21, h2]
      _ = -((qE1 : NestedMat B) * (qE2 * qE2)) + qE1 := by noncomm_ring
      _ = -((qE1 : NestedMat B) * (-1)) + qE1 := by rw [h2]
      _ = (2 : NestedMat B) * qE1 := by noncomm_ring
  · rw [Ring.lie_def]
    dsimp [qE3]
    calc (qE1 : NestedMat B) * (qE2 : NestedMat B) * (qE1 : NestedMat B) -
          (qE1 : NestedMat B) * ((qE1 : NestedMat B) * (qE2 : NestedMat B))
      _ = (qE1 : NestedMat B) * (qE2 * qE1) - ((qE1 : NestedMat B) * qE1) * qE2 := by noncomm_ring
      _ = (qE1 : NestedMat B) * (-(qE1 * qE2)) - (-1) * qE2 := by rw [h21, h1]
      _ = -(((qE1 : NestedMat B) * qE1) * qE2) + qE2 := by noncomm_ring
      _ = -((-1 : NestedMat B) * qE2) + qE2 := by rw [h1]
      _ = (2 : NestedMat B) * qE2 := by noncomm_ring

/-- Strict noncommutativity of the quaternion generators `qE1` and `qE2` whenever `(2 : B) ≠ 0`. -/
theorem nested_quaternion_noncommutative {B : Type*} [Ring B] (h2 : (2 : B) ≠ 0) :
    (qE1 : NestedMat B) * qE2 ≠ qE2 * qE1 := by
  intro hComm
  have hBracket : ⁅(qE1 : NestedMat B), (qE2 : NestedMat B)⁆ = (0 : NestedMat B) := by
    rw [Ring.lie_def, hComm, sub_self]
  rw [(nested_quaternion_lie_relations (B := B)).2.2.2.2.1, two_mul] at hBracket
  have hEntry := congrArg (fun M : NestedMat B => M 0 1 1 0) hBracket
  simp [qE3, qE1, qE2, omegaOp, kleinTwist] at hEntry
  have hTwo : (2 : B) = 0 := one_add_one_eq_two.symm.trans hEntry
  exact h2 hTwo

end ArchetypeA2_BrauerWeylQuaternionChain

/-!
## Archetype $\mathcal{A}_3$: Noncommutative Ring Derivations, Inner Derivations & Matrix Lifting
-/

section ArchetypeA3_NoncommutativeDerivations

/-- Noncommutative additive derivation predicate `d (a * b) = d a * b + a * d b`. -/
def IsRingDeriv {B : Type*} [Ring B] (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

/-- Every ring derivation annihilates the multiplicative identity `1`. -/
theorem IsRingDeriv.map_one {B : Type*} [Ring B] {d : B →+ B} (hd : IsRingDeriv d) :
    d 1 = 0 := by
  have h : d (1 * 1) = d 1 * 1 + 1 * d 1 := hd 1 1
  simp only [mul_one, one_mul] at h
  calc d 1
    _ = d 1 + d 1 - d 1 := by abel
    _ = d 1 - d 1 := by rw [← h]
    _ = 0 := sub_self (d 1)

/-- Noncommutative unit-inverse derivation law `d (u⁻¹) = -u⁻¹ * d u * u⁻¹`. -/
theorem IsRingDeriv.map_units_inv {B : Type*} [Ring B] {d : B →+ B}
    (hd : IsRingDeriv d) (u : Bˣ) :
    d (↑u⁻¹ : B) = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by
  have h1 : d ((u : B) * (↑u⁻¹ : B)) = d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B) :=
    hd (u : B) (↑u⁻¹ : B)
  rw [Units.mul_inv, hd.map_one] at h1
  have h2 : (↑u⁻¹ : B) * (d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑u⁻¹ : B) * (u : B) * d (↑u⁻¹ : B) = d (↑u⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc d (↑u⁻¹ : B)
    _ = (↑u⁻¹ : B) * (u : B) * d (↑u⁻¹ : B) -
        (↑u⁻¹ : B) * (d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by noncomm_ring

/-- Inner commutator derivation `x ↦ ⁅K, x⁆` generated by an element `K : B`. -/
def innerDeriv {B : Type*} [Ring B] (K : B) : B →+ B where
  toFun x := ⁅K, x⁆
  map_zero' := by
    rw [Ring.lie_def]
    noncomm_ring
  map_add' x y := by
    rw [Ring.lie_def, Ring.lie_def, Ring.lie_def]
    noncomm_ring

/-- Every inner commutator operator satisfies the noncommutative Leibniz derivation identity. -/
theorem innerDeriv_isRingDeriv {B : Type*} [Ring B] (K : B) :
    IsRingDeriv (innerDeriv K) := by
  intro a b
  dsimp [innerDeriv]
  simp only [Ring.lie_def]
  noncomm_ring

/-- Inner derivations generated by commuting elements `⁅K₁, K₂⁆ = 0` commute pointwise
by the Jacobi identity. -/
theorem innerDeriv_commute_of_commute {B : Type*} [Ring B] {K₁ K₂ : B}
    (hK : ⁅K₁, K₂⁆ = 0) (x : B) :
    innerDeriv K₁ (innerDeriv K₂ x) = innerDeriv K₂ (innerDeriv K₁ x) := by
  have hMul : K₁ * K₂ = K₂ * K₁ := sub_eq_zero.mp (by simpa [Ring.lie_def] using hK)
  dsimp [innerDeriv]
  simp only [Ring.lie_def]
  calc K₁ * (K₂ * x - x * K₂) - (K₂ * x - x * K₂) * K₁
    _ = (K₁ * K₂) * x - K₁ * x * K₂ - K₂ * x * K₁ + x * (K₂ * K₁) := by noncomm_ring
    _ = (K₂ * K₁) * x - K₁ * x * K₂ - K₂ * x * K₁ + x * (K₁ * K₂) := by rw [hMul]
    _ = K₂ * (K₁ * x - x * K₁) - (K₁ * x - x * K₁) * K₂ := by noncomm_ring

/-- Entrywise lifting of a base-ring derivation to `Matrix n n S`. -/
def liftMatrixDeriv {S : Type*} [Ring S] {n : Type*} [Fintype n] [DecidableEq n]
    (d : S →+ S) : Matrix n n S →+ Matrix n n S where
  toFun M i j := d (M i j)
  map_zero' := by
    ext i j
    exact map_zero d
  map_add' M N := by
    ext i j
    exact map_add d (M i j) (N i j)

/-- Entrywise lifting preserves the noncommutative Leibniz derivation law on `Matrix n n S`. -/
theorem IsRingDeriv.liftMatrix {S : Type*} [Ring S] {n : Type*} [Fintype n] [DecidableEq n]
    {d : S →+ S} (hd : IsRingDeriv d) :
    IsRingDeriv (liftMatrixDeriv (n := n) d) := by
  intro M N
  ext i k
  change d ((M * N) i k) =
    (liftMatrixDeriv (n := n) d M * N + M * liftMatrixDeriv (n := n) d N) i k
  rw [Matrix.mul_apply, map_sum, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => hd (M i j) (N j k))

end ArchetypeA3_NoncommutativeDerivations

/-!
## Archetype $\mathcal{A}_4$: Koszul Covariant Operators, Maurer–Cartan Curvature & Bianchi Law
-/

section ArchetypeA4_KoszulMaurerCartanCurvature

variable {B : Type*} [Ring B]

/-- Noncommutative Koszul covariant connection operator `ψ ↦ d ψ + A * ψ`. -/
def covOp (d : B →+ B) (A ψ : B) : B := d ψ + A * ψ

/-- Noncommutative Maurer–Cartan curvature `d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆`. -/
def mcCurvature (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B := d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆

/-- Gauge-dressed connection `u * A * u⁻¹ - d u * u⁻¹` under a unit `u : Bˣ`. -/
def dressConn (d : B →+ B) (u : Bˣ) (A : B) : B :=
  (u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)

/-- Adjoint covariant derivative `X ↦ d X + ⁅A, X⁆`. -/
def adjDeriv (d : B →+ B) (A X : B) : B := d X + ⁅A, X⁆

/-- Commutator of two Koszul covariant operators acts as left multiplication by `mcCurvature`. -/
theorem koszul_curvature_multiplication
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (hComm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (A₁ A₂ ψ : B) :
    covOp d₁ A₁ (covOp d₂ A₂ ψ) - covOp d₂ A₂ (covOp d₁ A₁ ψ) =
      mcCurvature d₁ d₂ A₁ A₂ * ψ := by
  dsimp [covOp, mcCurvature]
  rw [Ring.lie_def, map_add, map_add, hd₁ A₂ ψ, hd₂ A₁ ψ, hComm ψ]
  noncomm_ring

/-- Gauge dressing intertwines `covOp` covariantly under left unit multiplication. -/
theorem koszul_dressing_intertwining
    {d : B →+ B} (hd : IsRingDeriv d) (u : Bˣ) (A ψ : B) :
    covOp d (dressConn d u A) ((u : B) * ψ) = (u : B) * covOp d A ψ := by
  dsimp [covOp, dressConn]
  rw [hd (u : B) ψ]
  have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  calc d (u : B) * ψ + (u : B) * d ψ +
        ((u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)) * ((u : B) * ψ)
    _ = d (u : B) * ψ + (u : B) * d ψ +
        (u : B) * A * ((↑u⁻¹ : B) * (u : B)) * ψ -
        d (u : B) * ((↑u⁻¹ : B) * (u : B)) * ψ := by noncomm_ring
    _ = d (u : B) * ψ + (u : B) * d ψ + (u : B) * A * 1 * ψ - d (u : B) * 1 * ψ := by rw [hu]
    _ = (u : B) * (d ψ + A * ψ) := by noncomm_ring

/-- Noncommutative Maurer–Cartan curvature transforms purely adjointly (`u * F * u⁻¹`). -/
theorem maurer_cartan_conjugation_covariance
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (hComm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) (A₁ A₂ : B) :
    mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) =
      (u : B) * mcCurvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by
  have hLhs := koszul_curvature_multiplication hd₁ hd₂ hComm
    (dressConn d₁ u A₁) (dressConn d₂ u A₂) ((u : B) * 1)
  rw [koszul_dressing_intertwining hd₂ u A₂ 1,
      koszul_dressing_intertwining hd₁ u A₁ (covOp d₂ A₂ 1),
      koszul_dressing_intertwining hd₁ u A₁ 1,
      koszul_dressing_intertwining hd₂ u A₂ (covOp d₁ A₁ 1)] at hLhs
  have hRhs := koszul_curvature_multiplication hd₁ hd₂ hComm A₁ A₂ 1
  have hComb : mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * (u : B) =
      (u : B) * mcCurvature d₁ d₂ A₁ A₂ := by
    calc mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * (u : B)
      _ = mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * ((u : B) * 1) := by
          rw [mul_one]
      _ = (u : B) * covOp d₁ A₁ (covOp d₂ A₂ 1) -
          (u : B) * covOp d₂ A₂ (covOp d₁ A₁ 1) := hLhs.symm
      _ = (u : B) * (covOp d₁ A₁ (covOp d₂ A₂ 1) - covOp d₂ A₂ (covOp d₁ A₁ 1)) := by
          noncomm_ring
      _ = (u : B) * (mcCurvature d₁ d₂ A₁ A₂ * 1) := by rw [hRhs]
      _ = (u : B) * mcCurvature d₁ d₂ A₁ A₂ := by rw [mul_one]
  calc mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂)
    _ = mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * ((u : B) * (↑u⁻¹ : B)) := by
        rw [Units.mul_inv, mul_one]
    _ = (mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * (u : B)) * (↑u⁻¹ : B) := by
        noncomm_ring
    _ = (u : B) * mcCurvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by rw [hComb]

/-- Pure-gauge logarithmic Maurer–Cartan connections `-d u * u⁻¹` have zero curvature. -/
theorem logarithmic_coboundary_flatness
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (hComm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) :
    mcCurvature d₁ d₂ (-d₁ (u : B) * (↑u⁻¹ : B)) (-d₂ (u : B) * (↑u⁻¹ : B)) = 0 := by
  have h1 : -d₁ (u : B) * (↑u⁻¹ : B) = dressConn d₁ u 0 := by
    dsimp [dressConn]
    noncomm_ring
  have h2 : -d₂ (u : B) * (↑u⁻¹ : B) = dressConn d₂ u 0 := by
    dsimp [dressConn]
    noncomm_ring
  rw [h1, h2, maurer_cartan_conjugation_covariance hd₁ hd₂ hComm u 0 0]
  dsimp [mcCurvature]
  rw [Ring.lie_def, map_zero, map_zero]
  noncomm_ring

/-- Noncommutative cyclic differential Bianchi identity for three commuting ring derivations. -/
theorem differential_bianchi_identity
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    adjDeriv d₁ A₁ (mcCurvature d₂ d₃ A₂ A₃) +
    adjDeriv d₂ A₂ (mcCurvature d₃ d₁ A₃ A₁) +
    adjDeriv d₃ A₃ (mcCurvature d₁ d₂ A₁ A₂) = 0 := by
  dsimp [adjDeriv, mcCurvature]
  simp only [Ring.lie_def, map_add, map_sub]
  rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
      h12 A₃, h13 A₂, h23 A₁, ← h12 A₃, ← h13 A₂, ← h23 A₁]
  noncomm_ring

/-- Uncovariantized exterior cyclic sum leaves the exact adjoint commutator remainder. -/
theorem uncovariantized_exterior_remainder
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    d₁ (mcCurvature d₂ d₃ A₂ A₃) + d₂ (mcCurvature d₃ d₁ A₃ A₁) + d₃ (mcCurvature d₁ d₂ A₁ A₂) =
      ⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ +
      ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
      ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆ := by
  have h := differential_bianchi_identity hd₁ hd₂ hd₃ h12 h23 h13 A₁ A₂ A₃
  calc d₁ (mcCurvature d₂ d₃ A₂ A₃) + d₂ (mcCurvature d₃ d₁ A₃ A₁) + d₃ (mcCurvature d₁ d₂ A₁ A₂)
    _ = (adjDeriv d₁ A₁ (mcCurvature d₂ d₃ A₂ A₃) +
         adjDeriv d₂ A₂ (mcCurvature d₃ d₁ A₃ A₁) +
         adjDeriv d₃ A₃ (mcCurvature d₁ d₂ A₁ A₂)) +
        (⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ +
         ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
         ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆) := by
          dsimp [adjDeriv]
          simp only [Ring.lie_def]
          noncomm_ring
    _ = 0 + (⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ +
             ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
             ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆) := by rw [h]
    _ = ⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ +
        ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
        ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆ := zero_add _

/-- Concrete non-zero first commuting inner derivation on `NestedMat B` generated by
`fiberEmbed omegaOp`. -/
def nestedInnerD1 (B : Type*) [Ring B] : NestedMat B →+ NestedMat B :=
  innerDeriv (fiberEmbed (omegaOp : Matrix (Fin 2) (Fin 2) B))

/-- Concrete non-zero second commuting inner derivation on `NestedMat B` generated by
`kleinTwist 1`. -/
def nestedInnerD2 (B : Type*) [Ring B] : NestedMat B →+ NestedMat B :=
  innerDeriv (kleinTwist (1 : Matrix (Fin 2) (Fin 2) B))

/-- Trivial third commuting inner derivation on `NestedMat B` completing the Bianchi triple. -/
def nestedInnerD3 (B : Type*) [Ring B] : NestedMat B →+ NestedMat B :=
  innerDeriv (1 : NestedMat B)

/-- The concrete commuting inner derivations `nestedInnerD1, nestedInnerD2, nestedInnerD3`
on `NestedMat B` satisfy Maurer–Cartan conjugation covariance, logarithmic flatness, and the
differential Bianchi identity. -/
theorem nested_inner_deriv_curvature_and_bianchi (u : (NestedMat B)ˣ) (A₁ A₂ A₃ : NestedMat B) :
    mcCurvature (nestedInnerD1 B) (nestedInnerD2 B)
      (dressConn (nestedInnerD1 B) u A₁) (dressConn (nestedInnerD2 B) u A₂) =
      (u : NestedMat B) * mcCurvature (nestedInnerD1 B) (nestedInnerD2 B) A₁ A₂ * (↑u⁻¹ : NestedMat B) ∧
    mcCurvature (nestedInnerD1 B) (nestedInnerD2 B)
      (-(nestedInnerD1 B) (u : NestedMat B) * (↑u⁻¹ : NestedMat B))
      (-(nestedInnerD2 B) (u : NestedMat B) * (↑u⁻¹ : NestedMat B)) = 0 ∧
    adjDeriv (nestedInnerD1 B) A₁ (mcCurvature (nestedInnerD2 B) (nestedInnerD3 B) A₂ A₃) +
    adjDeriv (nestedInnerD2 B) A₂ (mcCurvature (nestedInnerD3 B) (nestedInnerD1 B) A₃ A₁) +
    adjDeriv (nestedInnerD3 B) A₃ (mcCurvature (nestedInnerD1 B) (nestedInnerD2 B) A₁ A₂) = 0 := by
  let K₁ : NestedMat B := fiberEmbed (omegaOp : Matrix (Fin 2) (Fin 2) B)
  let K₂ : NestedMat B := kleinTwist (1 : Matrix (Fin 2) (Fin 2) B)
  let K₃ : NestedMat B := 1
  have h12K : ⁅K₁, K₂⁆ = 0 := by
    rw [Ring.lie_def, sub_eq_zero]
    apply ext_fin2 <;>
      simp [K₁, K₂, fiberEmbed, kleinTwist]
  have h23K : ⁅K₂, K₃⁆ = 0 := by
    rw [Ring.lie_def]
    dsimp [K₃]
    noncomm_ring
  have h13K : ⁅K₁, K₃⁆ = 0 := by
    rw [Ring.lie_def]
    dsimp [K₃]
    noncomm_ring
  have h12 : ∀ x : NestedMat B,
      nestedInnerD1 B (nestedInnerD2 B x) = nestedInnerD2 B (nestedInnerD1 B x) :=
    innerDeriv_commute_of_commute h12K
  have h23 : ∀ x : NestedMat B,
      nestedInnerD2 B (nestedInnerD3 B x) = nestedInnerD3 B (nestedInnerD2 B x) :=
    innerDeriv_commute_of_commute h23K
  have h13 : ∀ x : NestedMat B,
      nestedInnerD1 B (nestedInnerD3 B x) = nestedInnerD3 B (nestedInnerD1 B x) :=
    innerDeriv_commute_of_commute h13K
  refine ⟨?_, ?_, ?_⟩
  · exact maurer_cartan_conjugation_covariance
      (innerDeriv_isRingDeriv K₁) (innerDeriv_isRingDeriv K₂) h12 u A₁ A₂
  · exact logarithmic_coboundary_flatness
      (innerDeriv_isRingDeriv K₁) (innerDeriv_isRingDeriv K₂) h12 u
  · exact differential_bianchi_identity
      (innerDeriv_isRingDeriv K₁) (innerDeriv_isRingDeriv K₂) (innerDeriv_isRingDeriv K₃)
      h12 h23 h13 A₁ A₂ A₃

end ArchetypeA4_KoszulMaurerCartanCurvature

/-!
## Archetype $\mathcal{A}_5$: Twisted Group Braiding $Z X = Q X Z$ & 1-Cocycle Cohomology
-/

section ArchetypeA5_TwistedGroupCocycle

variable {G : Type*} [Group G]

/-- Group conjugation `x * q * x⁻¹`. -/
def conjBy (x q : G) : G := x * q * x⁻¹

/-- Group-valued twisted 1-cocycle associated to the braiding defect `Q`. -/
def twistedCocycle (X Q : G) : ℕ → G
  | 0 => 1
  | n + 1 => Q * conjBy X (twistedCocycle X Q n)

/-- Iterated braiding cocycle theorem: `Z * X ^ n = twistedCocycle X Q n * X ^ n * Z`. -/
theorem braided_pow_cocycle {X Z Q : G} (hBraid : Z * X = Q * X * Z) (n : ℕ) :
    Z * X ^ n = twistedCocycle X Q n * X ^ n * Z := by
  induction' n with n ih
  · simp [twistedCocycle]
  · calc Z * X ^ (n + 1)
      _ = (Z * X) * X ^ n := by rw [pow_succ', mul_assoc]
      _ = (Q * X * Z) * X ^ n := by rw [hBraid]
      _ = Q * X * (Z * X ^ n) := by group
      _ = Q * X * (twistedCocycle X Q n * X ^ n * Z) := by rw [ih]
      _ = (Q * (X * twistedCocycle X Q n * X⁻¹)) * (X * X ^ n) * Z := by group
      _ = twistedCocycle X Q (n + 1) * X ^ (n + 1) * Z := by
          rw [twistedCocycle, conjBy, ← pow_succ']

/-- Multiplicative crossed-homomorphism / 1-cocycle additivity identity over `ℕ`. -/
theorem twistedCocycle_add (X Q : G) (m n : ℕ) :
    twistedCocycle X Q (m + n) =
      twistedCocycle X Q m * conjBy (X ^ m) (twistedCocycle X Q n) := by
  induction' m with m ih
  · simp [twistedCocycle, conjBy]
  · have hAdd : m + 1 + n = (m + n) + 1 := by omega
    rw [hAdd, twistedCocycle, ih, twistedCocycle]
    dsimp [conjBy]
    rw [pow_succ']
    group

/-- Torsion obstruction: any order relation `X ^ N = 1` kills the `N`-th twisted cocycle. -/
theorem twistedCocycle_torsion_obstruction {X Z Q : G}
    (hBraid : Z * X = Q * X * Z) {N : ℕ} (hXN : X ^ N = 1) :
    twistedCocycle X Q N = 1 := by
  have h := braided_pow_cocycle hBraid N
  rw [hXN, mul_one, mul_one] at h
  calc twistedCocycle X Q N
    _ = (twistedCocycle X Q N * Z) * Z⁻¹ := by group
    _ = Z * Z⁻¹ := by rw [← h]
    _ = 1 := by group

/-- Involutive braid phase inversion: if `Z * X = Q * X * Z` and `X * X = 1`, then
`Q * (X * Q * X) = 1`. -/
theorem involutive_braid_phase_inversion {X Z Q : G}
    (hBraid : Z * X = Q * X * Z) (hX2 : X * X = 1) :
    Q * (X * Q * X) = 1 := by
  have hXsq : X ^ 2 = 1 := by
    rw [sq]
    exact hX2
  have hXinv : X⁻¹ = X := inv_eq_of_mul_eq_one_right hX2
  have h1 : conjBy X (1 : G) = 1 := by
    dsimp [conjBy]
    group
  have hTor := twistedCocycle_torsion_obstruction hBraid hXsq
  dsimp [twistedCocycle] at hTor
  rw [h1, mul_one] at hTor
  dsimp [conjBy] at hTor
  rw [hXinv] at hTor
  exact hTor

end ArchetypeA5_TwistedGroupCocycle

/-!
## Archetype $\mathcal{A}_6$: Repaired Unipotent Witt-Link Block Monodromy & Infinite Order
-/

section ArchetypeA6_ParabolicBlockMonodromy

/-- Parabolic nilpotent block `![![-1, -1], ![1, 1]]` satisfying `nilpPar² = 0`. -/
def nilpPar {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of ![![-1, -1], ![1, 1]]

/-- Nilpotent splitting of the Witt-link block monodromy over any ring `B`. -/
theorem witt_link_monodromy_nilpotent_split {B : Type*} [Ring B] :
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) * (1 - fPlus) * gammaOneOp * (1 + fPlus) =
      1 + nilpPar ∧
    (nilpPar : Matrix (Fin 2) (Fin 2) B) * nilpPar = 0 := by
  have hSF : (sigmaOp : Matrix (Fin 2) (Fin 2) B) * fPlus = Matrix.of ![![0, 0], ![0, 1]] := by
    apply ext_fin2 <;>
      simp [sigmaOp, fPlus, Matrix.mul_apply, Fin.sum_univ_two]
  have hLeft : (sigmaOp : Matrix (Fin 2) (Fin 2) B) * (1 - fPlus) =
      Matrix.of ![![0, 1], ![1, -1]] := by
    rw [mul_sub, mul_one, hSF]
    apply ext_fin2 <;>
      simp [sigmaOp, sub_eq_add_neg]
  have hGF : (gammaOneOp : Matrix (Fin 2) (Fin 2) B) * fPlus = fPlus := by
    apply ext_fin2 <;>
      simp [gammaOneOp, fPlus, Matrix.mul_apply, Fin.sum_univ_two]
  have hRight : (gammaOneOp : Matrix (Fin 2) (Fin 2) B) * (1 + fPlus) =
      Matrix.of ![![1, 1], ![0, -1]] := by
    rw [mul_add, mul_one, hGF]
    apply ext_fin2 <;>
      simp [gammaOneOp, fPlus]
  constructor
  · calc (sigmaOp : Matrix (Fin 2) (Fin 2) B) * (1 - fPlus) * gammaOneOp * (1 + fPlus)
      _ = ((sigmaOp : Matrix (Fin 2) (Fin 2) B) * (1 - fPlus)) * (gammaOneOp * (1 + fPlus)) := by
          noncomm_ring
      _ = Matrix.of ![![0, 1], ![1, -1]] * Matrix.of ![![1, 1], ![0, -1]] := by
          rw [hLeft, hRight]
      _ = 1 + nilpPar := by
          apply ext_fin2 <;>
            simp [nilpPar, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  · apply ext_fin2 <;>
      simp [nilpPar, Matrix.mul_apply, Fin.sum_univ_two]

/-- `2 × 2` block matrices over `Mat2Z`. -/
abbrev BlockMatZ := Matrix (Fin 2) (Fin 2) Mat2Z

/-- Unipotent shear link `1 + fPlus` in `Mat2Z`. -/
def gLink : Mat2Z := 1 + fPlus

/-- Inverse unipotent shear link `1 - fPlus` in `Mat2Z`. -/
def giLink : Mat2Z := 1 - fPlus

/-- Repaired cross-link orientation `![![0, 1 - fPlus], ![1 + fPlus, 0]]` in `BlockMatZ`. -/
def blkX : BlockMatZ := Matrix.of ![![0, giLink], ![gLink, 0]]

/-- Reflection block involution `![![sigmaOp, 0], ![0, gammaOneOp]]` in `BlockMatZ`. -/
def blkZ : BlockMatZ := Matrix.of ![![sigmaOp, 0], ![0, gammaOneOp]]

/-- Parabolic monodromy element `(blkZ * blkX) ^ 2` in `BlockMatZ`. -/
def blkQ : BlockMatZ := (blkZ * blkX) * (blkZ * blkX)

/-- Upper-left `2 × 2` parabolic Jordan shear `![![0, -1], ![1, 2]]`. -/
def q0Mat : Mat2Z := Matrix.of ![![0, -1], ![1, 2]]

/-- Lower-right `2 × 2` parabolic Jordan shear `![![1, 0], ![-1, 1]]`. -/
def q1Mat : Mat2Z := Matrix.of ![![1, 0], ![-1, 1]]

private theorem blkQ_block_form :
    blkQ = Matrix.of ![![q0Mat, 0], ![0, q1Mat]] := by
  have hZX01 : (sigmaOp : Mat2Z) * giLink = Matrix.of ![![0, 1], ![1, -1]] := by
    apply ext_fin2 <;> decide
  have hZX10 : (gammaOneOp : Mat2Z) * gLink = Matrix.of ![![1, 1], ![0, -1]] := by
    apply ext_fin2 <;> decide
  have hZX : blkZ * blkX =
      Matrix.of ![![0, Matrix.of ![![0, 1], ![1, -1]]], ![Matrix.of ![![1, 1], ![0, -1]], 0]] := by
    apply ext_fin2 <;>
      simp [blkZ, blkX, Matrix.mul_apply, Fin.sum_univ_two, hZX01, hZX10]
  have hMul00 : Matrix.of ![![0, (1 : ℤ)], ![1, -1]] * Matrix.of ![![1, 1], ![0, -1]] = q0Mat := by
    apply ext_fin2 <;> decide
  have hMul11 : Matrix.of ![![1, (1 : ℤ)], ![0, -1]] * Matrix.of ![![0, 1], ![1, -1]] = q1Mat := by
    apply ext_fin2 <;> decide
  dsimp [blkQ]
  rw [hZX]
  apply ext_fin2 <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hMul00, hMul11]

/-- Unipotent link pair `gLink` and `giLink` are mutual two-sided inverses in `Mat2Z`. -/
theorem gLink_giLink_inverse_pair :
    gLink * giLink = 1 ∧ giLink * gLink = 1 := by
  have hf : (fPlus : Mat2Z) * fPlus = 0 := cl11_and_witt_car_relations.2.2.2.2.2.1
  constructor
  · calc gLink * giLink
      _ = (1 + fPlus) * (1 - fPlus) := by dsimp [gLink, giLink]
      _ = 1 - fPlus * fPlus := by noncomm_ring
      _ = 1 := by rw [hf, sub_zero]
  · calc giLink * gLink
      _ = (1 - fPlus) * (1 + fPlus) := by dsimp [gLink, giLink]
      _ = 1 - fPlus * fPlus := by noncomm_ring
      _ = 1 := by rw [hf, sub_zero]

/-- Explicit block monodromy braiding, noncommutativity, and involutive phase inversion
in `BlockMatZ`. -/
theorem block_monodromy_braiding_and_cocycle :
    blkX * blkX = 1 ∧
    blkZ * blkZ = 1 ∧
    blkZ * blkX = blkQ * blkX * blkZ ∧
    blkQ * blkX ≠ blkX * blkQ ∧
    blkQ * blkZ ≠ blkZ * blkQ ∧
    blkQ * (blkX * blkQ * blkX) = 1 := by
  have hX2 : blkX * blkX = 1 := by
    have hInv := gLink_giLink_inverse_pair
    apply ext_fin2 <;>
      simp [blkX, Matrix.mul_apply, Fin.sum_univ_two, hInv.1, hInv.2]
  have hZ2 : blkZ * blkZ = 1 := by
    have hS : (sigmaOp : Mat2Z) * sigmaOp = 1 := cl11_and_witt_car_relations.1
    have hG : (gammaOneOp : Mat2Z) * gammaOneOp = 1 := cl11_and_witt_car_relations.2.2.2.1
    apply ext_fin2 <;>
      simp [blkZ, Matrix.mul_apply, Fin.sum_univ_two, hS, hG]
  have hBraid : blkZ * blkX = blkQ * blkX * blkZ := by
    calc blkZ * blkX
      _ = blkZ * blkX * (blkZ * blkZ) := by rw [hZ2, mul_one]
      _ = blkZ * blkX * blkZ * (blkX * blkX) * blkZ := by rw [hX2]; noncomm_ring
      _ = blkQ * blkX * blkZ := by dsimp [blkQ]; noncomm_ring
  have hQX : blkQ * blkX ≠ blkX * blkQ := by
    intro hEq
    rw [blkQ_block_form] at hEq
    have hBlock := congrArg (fun M : BlockMatZ => M 0 1) hEq
    simp only [blkX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero, zero_add] at hBlock
    have hNe : (q0Mat * giLink : Mat2Z) ≠ giLink * q1Mat := by decide
    exact hNe hBlock
  have hQZ : blkQ * blkZ ≠ blkZ * blkQ := by
    intro hEq
    rw [blkQ_block_form] at hEq
    have hEntry := congrArg (fun M : BlockMatZ => M 0 0 0 0) hEq
    simp [blkZ, sigmaOp, gammaOneOp, q0Mat, q1Mat, Matrix.mul_apply, Fin.sum_univ_two] at hEntry
  have hInvPhase : blkQ * (blkX * blkQ * blkX) = 1 := by
    calc blkQ * (blkX * blkQ * blkX)
      _ = blkZ * blkX * blkZ * (blkX * blkX) * blkZ * blkX * blkZ * (blkX * blkX) := by
          dsimp [blkQ]; noncomm_ring
      _ = blkZ * blkX * (blkZ * blkZ) * blkX * blkZ := by
          rw [hX2]; noncomm_ring
      _ = blkZ * (blkX * blkX) * blkZ := by
          rw [hZ2]; noncomm_ring
      _ = blkZ * blkZ := by rw [hX2, mul_one]
      _ = 1 := hZ2
  exact ⟨hX2, hZ2, hBraid, hQX, hQZ, hInvPhase⟩

/-- Closed-form Jordan power formula `q0Mat ^ n = ![![1 - n, -n], ![n, 1 + n]]`. -/
theorem q0Mat_pow (n : ℕ) :
    q0Mat ^ n = Matrix.of ![![1 - (n : ℤ), -(n : ℤ)], ![(n : ℤ), 1 + (n : ℤ)]] := by
  induction' n with n ih
  · apply ext_fin2 <;>
      simp
  · rw [pow_succ, ih]
    apply ext_fin2 <;>
      simp only [q0Mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact q0Mat_step_00 n
    · exact q0Mat_step_01 n
    · exact q0Mat_step_10 n
    · exact q0Mat_step_11 n

/-- Upper block invariants of `blkQ ^ n` for all `n : ℕ`. -/
theorem blkQ_pow_00 (n : ℕ) :
    (blkQ ^ n) 0 0 = q0Mat ^ n ∧ (blkQ ^ n) 0 1 = 0 := by
  have hQ00 : blkQ 0 0 = q0Mat := by
    rw [blkQ_block_form]
    simp [Matrix.of_apply]
  have hQ01 : blkQ 0 1 = 0 := by
    rw [blkQ_block_form]
    simp [Matrix.of_apply]
  have hQ10 : blkQ 1 0 = 0 := by
    rw [blkQ_block_form]
    simp [Matrix.of_apply]
  induction' n with n ih
  · constructor
    · apply ext_fin2 <;> simp
    · apply ext_fin2 <;> simp
  · rcases ih with ⟨ih00, ih01⟩
    constructor
    · rw [pow_succ, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        ih00, ih01, hQ00, hQ10, zero_mul, add_zero]
    · rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
        ih00, ih01, hQ01, mul_zero, zero_mul, add_zero]

/-- Infinite parabolic order of `blkQ` in `BlockMatZ`: `blkQ ^ n ≠ 1` for every `n > 0`. -/
theorem blkQ_infinite_order (n : ℕ) (hn : 0 < n) : blkQ ^ n ≠ 1 := by
  intro hEq
  have hBlock : (blkQ ^ n) 0 0 = (1 : BlockMatZ) 0 0 := by rw [hEq]
  rw [(blkQ_pow_00 n).1, q0Mat_pow n] at hBlock
  have hEntry :
      (Matrix.of ![![1 - (n : ℤ), -(n : ℤ)], ![(n : ℤ), 1 + (n : ℤ)]] : Mat2Z) 1 0 =
        ((1 : BlockMatZ) 0 0) 1 0 := by
    rw [hBlock]
  simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.one_apply] at hEntry
  exact Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn) hEntry

/-- Unit embedding `blkXUnit` in `(BlockMatZ)ˣ`. -/
def blkXUnit : BlockMatZˣ where
  val := blkX
  inv := blkX
  val_inv := block_monodromy_braiding_and_cocycle.1
  inv_val := block_monodromy_braiding_and_cocycle.1

/-- Unit embedding `blkZUnit` in `(BlockMatZ)ˣ`. -/
def blkZUnit : BlockMatZˣ where
  val := blkZ
  inv := blkZ
  val_inv := block_monodromy_braiding_and_cocycle.2.1
  inv_val := block_monodromy_braiding_and_cocycle.2.1

/-- Unit embedding `blkQUnit` in `(BlockMatZ)ˣ`. -/
def blkQUnit : BlockMatZˣ := (blkZUnit * blkXUnit) * (blkZUnit * blkXUnit)

/-- Applying the abstract `A5` group cocycle laws to the concrete integer block units
`blkXUnit, blkZUnit, blkQUnit` confirms both `twistedCocycle` torsion closure at `N = 2`
and infinite parabolic order of `blkQUnit`. -/
theorem blkQ_unit_cocycle_and_infinite_order (n : ℕ) (hn : 0 < n) :
    blkZUnit * blkXUnit = blkQUnit * blkXUnit * blkZUnit ∧
    blkQUnit * (blkXUnit * blkQUnit * blkXUnit) = 1 ∧
    twistedCocycle blkXUnit blkQUnit 2 = 1 ∧
    blkQUnit ^ n ≠ 1 := by
  have hBraid : blkZUnit * blkXUnit = blkQUnit * blkXUnit * blkZUnit := by
    apply Units.ext
    change blkZ * blkX = blkQ * blkX * blkZ
    exact block_monodromy_braiding_and_cocycle.2.2.1
  have hX2 : blkXUnit * blkXUnit = 1 := by
    apply Units.ext
    exact block_monodromy_braiding_and_cocycle.1
  have hXsq : blkXUnit ^ 2 = 1 := by
    rw [sq]
    exact hX2
  have hInv := involutive_braid_phase_inversion hBraid hX2
  have hTor := twistedCocycle_torsion_obstruction hBraid hXsq
  have hInf : blkQUnit ^ n ≠ 1 := by
    intro hPow
    apply blkQ_infinite_order n hn
    exact congrArg Units.val hPow
  exact ⟨hBraid, hInv, hTor, hInf⟩

end ArchetypeA6_ParabolicBlockMonodromy

/-!
## Archetype $\mathcal{A}_7$: Master Artin Braid Group $B_3$ Representation & Curvature Synthesis
-/

section ArchetypeA7_MasterSynthesis

/-- Triple-product Clifford bivector identity `(1 + E₁₂)(1 + E₂₃)(1 + E₁₂) = 2(E₁₂ + E₂₃)`
over any noncommutative ring `B`. -/
theorem clifford_bivector_triple_product {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (hAnti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = 2 * (E₁₂ + E₂₃) := by
  have h12' : E₁₂ * E₁₂ + 1 = 0 := by
    rw [h12]
    abel
  calc (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂)
    _ = 2 * (E₁₂ + E₂₃) + (E₁₂ * E₁₂ + 1) * (1 - E₂₃) +
        (1 + E₁₂) * (E₁₂ * E₂₃ + E₂₃ * E₁₂) := by noncomm_ring
    _ = 2 * (E₁₂ + E₂₃) + 0 * (1 - E₂₃) + (1 + E₁₂) * 0 := by rw [h12', hAnti]
    _ = 2 * (E₁₂ + E₂₃) := by noncomm_ring

/-- Artin braid relation `(1 + E₁₂)(1 + E₂₃)(1 + E₁₂) = (1 + E₂₃)(1 + E₁₂)(1 + E₂₃)`
for anticommuting square-`-1` elements. -/
theorem clifford_artin_braid_relation {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h23 : E₂₃ * E₂₃ = -1)
    (hAnti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = (1 + E₂₃) * (1 + E₁₂) * (1 + E₂₃) := by
  have hAnti' : E₂₃ * E₁₂ + E₁₂ * E₂₃ = 0 := by
    rw [add_comm, hAnti]
  rw [clifford_bivector_triple_product h12 hAnti,
      clifford_bivector_triple_product h23 hAnti']
  noncomm_ring

/-- First Clifford–Baxter braid generator `1 + qE₁` in `NestedMat B`. -/
def qR12 {B : Type*} [Ring B] : NestedMat B := 1 + qE1

/-- Second Clifford–Baxter braid generator `1 + qE₂` in `NestedMat B`. -/
def qR23 {B : Type*} [Ring B] : NestedMat B := 1 + qE2

/-- Noncommutativity of the braid generators `qR12` and `qR23` whenever `(2 : B) ≠ 0`. -/
theorem qR12_qR23_noncommutative {B : Type*} [Ring B] (h2 : (2 : B) ≠ 0) :
    (qR12 : NestedMat B) * qR23 ≠ qR23 * qR12 := by
  intro hEq
  apply nested_quaternion_noncommutative h2
  have hDiff : (qR12 : NestedMat B) * qR23 - qR23 * qR12 =
      (qE1 : NestedMat B) * qE2 - qE2 * qE1 := by
    dsimp [qR12, qR23]
    noncomm_ring
  have hZero : (qE1 : NestedMat B) * qE2 - qE2 * qE1 = 0 := by
    rw [← hDiff, hEq, sub_self]
  exact sub_eq_zero.mp hZero

private noncomputable def nestedUnitOfSqNegOne {B : Type*} [Ring B] [Algebra ℂ B]
    (E : B) (hE : E * E = -1) : Bˣ where
  val := 1 + E
  inv := (1 / 2 : ℂ) • (1 - E)
  val_inv := by
    have hHalf : (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by norm_num
    have hSub : (1 + E) * (1 - E) = (1 : B) + 1 := by
      calc (1 + E) * (1 - E)
        _ = 1 - E * E := by noncomm_ring
        _ = 1 - (-1) := by rw [hE]
        _ = (1 : B) + 1 := by noncomm_ring
    rw [mul_smul_comm, hSub, smul_add, ← add_smul, hHalf, one_smul]
  inv_val := by
    have hHalf : (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by norm_num
    have hSub : (1 - E) * (1 + E) = (1 : B) + 1 := by
      calc (1 - E) * (1 + E)
        _ = 1 - E * E := by noncomm_ring
        _ = 1 - (-1) := by rw [hE]
        _ = (1 : B) + 1 := by noncomm_ring
    rw [smul_mul_assoc, hSub, smul_add, ← add_smul, hHalf, one_smul]

/-- First invertible Clifford–Baxter braid generator `qR12Unit : (NestedMat ℂ)ˣ`. -/
noncomputable def qR12Unit : (NestedMat ℂ)ˣ :=
  nestedUnitOfSqNegOne (qE1 : NestedMat ℂ) nested_quaternion_lie_relations.1

/-- Second invertible Clifford–Baxter braid generator `qR23Unit : (NestedMat ℂ)ˣ`. -/
noncomputable def qR23Unit : (NestedMat ℂ)ˣ :=
  nestedUnitOfSqNegOne (qE2 : NestedMat ℂ) nested_quaternion_lie_relations.2.1

/-- Canonical `ArtinBraidSystem (NestedMat ℂ)ˣ 2` realized inside nested `2 × 2` complex
block matrices `NestedMat ℂ`. -/
noncomputable def quaternionicArtinBraidSystem : ArtinBraidSystem (NestedMat ℂ)ˣ 2 where
  gen := ![qR12Unit, qR23Unit]
  adjacent := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · dsimp at hij; omega
    · apply Units.ext
      rcases nested_quaternion_lie_relations (B := ℂ) with ⟨hE1, hE2, _, hAnti, _, _, _⟩
      exact clifford_artin_braid_relation hE1 hE2 hAnti
    · dsimp at hij; omega
    · dsimp at hij; omega
  farCommute := by
    intro i j hij
    rcases i with ⟨iv, hi⟩
    rcases j with ⟨jv, hj⟩
    dsimp at hij
    omega

/-- Genuine nonabelian Artin braid group `B₃` representation valued in `(NestedMat ℂ)ˣ`. -/
noncomputable def quaternionicBraidGroup3Hom :
    Braid.braid_group 3 →* (NestedMat ℂ)ˣ :=
  quaternionicArtinBraidSystem.toGroupHom

/-- Explicit evaluation of `quaternionicBraidGroup3Hom` on the Artin generators `σ₀, σ₁ ∈ B₃`. -/
theorem quaternionicBraidGroup3Hom_generators :
    quaternionicBraidGroup3Hom (Braid.σ' 2 0) = qR12Unit ∧
    quaternionicBraidGroup3Hom (Braid.σ' 2 1) = qR23Unit := by
  constructor
  · exact ArtinBraidSystem.toGroupHom_generator quaternionicArtinBraidSystem 0
  · exact ArtinBraidSystem.toGroupHom_generator quaternionicArtinBraidSystem 1

/-- `quaternionicBraidGroup3Hom` has strictly nonabelian image in `(NestedMat ℂ)ˣ`. -/
theorem quaternionicBraidGroup3Hom_nonabelian :
    ∃ x y : Braid.braid_group 3,
      quaternionicBraidGroup3Hom (x * y) ≠ quaternionicBraidGroup3Hom (y * x) := by
  refine ⟨Braid.σ' 2 0, Braid.σ' 2 1, ?_⟩
  intro hEq
  rw [map_mul, map_mul,
    quaternionicBraidGroup3Hom_generators.1,
    quaternionicBraidGroup3Hom_generators.2] at hEq
  have hVal := congrArg Units.val hEq
  exact qR12_qR23_noncommutative (two_ne_zero : (2 : ℂ) ≠ 0) hVal

/-- **Master Noncommutative Curvature & Artin Braid Synthesis Theorem**:
Unifies over arbitrary `[Ring B]` the Artin braid relation `qR12 * qR23 * qR12 = qR23 * qR12 * qR23`,
the exact braid-commutator Maurer–Cartan equality `⁅qR12, qR23⁆ = mcCurvature 0 0 qE1 qE2 = 2 * qE3`,
the commuting inner-derivation Bianchi identity, and the concrete nonabelian realizations in
`NestedMat ℂ` (`Braid.braid_group 3 →* (NestedMat ℂ)ˣ`) and `BlockMatZ` (`blkQ ^ n ≠ 1`). -/
theorem master_braid_curvature_synthesis {B : Type*} [Ring B]
    (u : (NestedMat B)ˣ) (A₁ A₂ A₃ : NestedMat B) (n : ℕ) (hn : 0 < n) :
    ((qR12 : NestedMat B) * qR23 * qR12 = qR23 * qR12 * qR23 ∧
     ⁅(qR12 : NestedMat B), qR23⁆ =
       mcCurvature (0 : NestedMat B →+ NestedMat B) 0 qE1 qE2 ∧
     mcCurvature (0 : NestedMat B →+ NestedMat B) 0 (qE1 : NestedMat B) qE2 =
       (2 : NestedMat B) * qE3 ∧
     mcCurvature (nestedInnerD1 B) (nestedInnerD2 B)
       (dressConn (nestedInnerD1 B) u A₁) (dressConn (nestedInnerD2 B) u A₂) =
       (u : NestedMat B) * mcCurvature (nestedInnerD1 B) (nestedInnerD2 B) A₁ A₂ * (↑u⁻¹ : NestedMat B) ∧
     adjDeriv (nestedInnerD1 B) A₁ (mcCurvature (nestedInnerD2 B) (nestedInnerD3 B) A₂ A₃) +
     adjDeriv (nestedInnerD2 B) A₂ (mcCurvature (nestedInnerD3 B) (nestedInnerD1 B) A₃ A₁) +
     adjDeriv (nestedInnerD3 B) A₃ (mcCurvature (nestedInnerD1 B) (nestedInnerD2 B) A₁ A₂) = 0) ∧
    (quaternionicBraidGroup3Hom (Braid.σ' 2 0) * quaternionicBraidGroup3Hom (Braid.σ' 2 1) ≠
       quaternionicBraidGroup3Hom (Braid.σ' 2 1) * quaternionicBraidGroup3Hom (Braid.σ' 2 0) ∧
     (qR12 : NestedMat ℂ) ^ 4 = (-4 : ℂ) • (1 : NestedMat ℂ) ∧
     blkQ ^ n ≠ 1) := by
  rcases nested_quaternion_lie_relations (B := B) with ⟨hE1, hE2, _, hAnti, hL12, _, _⟩
  have hInner := nested_inner_deriv_curvature_and_bianchi u A₁ A₂ A₃
  have hBraidC : (qR12 : NestedMat ℂ) ^ 4 = (-4 : ℂ) • (1 : NestedMat ℂ) := by
    have hE1C : (qE1 : NestedMat ℂ) * qE1 = -1 := nested_quaternion_lie_relations.1
    have hSq : (qR12 : NestedMat ℂ) * qR12 = (2 : NestedMat ℂ) * qE1 := by
      calc (1 + (qE1 : NestedMat ℂ)) * (1 + qE1)
        _ = 1 + (2 : NestedMat ℂ) * qE1 + qE1 * qE1 := by noncomm_ring
        _ = 1 + (2 : NestedMat ℂ) * qE1 + (-1) := by rw [hE1C]
        _ = (2 : NestedMat ℂ) * qE1 := by noncomm_ring
    calc (qR12 : NestedMat ℂ) ^ 4
      _ = (qR12 * qR12) * (qR12 * qR12) := by noncomm_ring
      _ = ((2 : NestedMat ℂ) * qE1) * ((2 : NestedMat ℂ) * qE1) := by rw [hSq]
      _ = (4 : NestedMat ℂ) * (qE1 * qE1) := by noncomm_ring
      _ = (4 : NestedMat ℂ) * (-1 : NestedMat ℂ) := by rw [hE1C]
      _ = -(4 : NestedMat ℂ) := by rw [mul_neg_one]
      _ = (-4 : ℂ) • (1 : NestedMat ℂ) := by
          rw [Algebra.smul_def, mul_one, map_neg, map_ofNat]
  have hNonAb : quaternionicBraidGroup3Hom (Braid.σ' 2 0) *
        quaternionicBraidGroup3Hom (Braid.σ' 2 1) ≠
      quaternionicBraidGroup3Hom (Braid.σ' 2 1) *
        quaternionicBraidGroup3Hom (Braid.σ' 2 0) := by
    rw [quaternionicBraidGroup3Hom_generators.1, quaternionicBraidGroup3Hom_generators.2]
    intro hMul
    exact qR12_qR23_noncommutative (two_ne_zero : (2 : ℂ) ≠ 0) (congrArg Units.val hMul)
  refine ⟨⟨?_, ?_, ?_, hInner.1, hInner.2.2⟩, ⟨hNonAb, hBraidC, blkQ_infinite_order n hn⟩⟩
  · exact clifford_artin_braid_relation hE1 hE2 hAnti
  · dsimp [qR12, qR23, mcCurvature]
    simp only [Ring.lie_def]
    noncomm_ring
  · dsimp [mcCurvature]
    simp only [sub_self, zero_add]
    exact hL12

end ArchetypeA7_MasterSynthesis

/-!
## Stage 8: 7-Node Diamond Causal Poset & Certified QMS `TypedArchetype` Audit
-/

section CausalPosetCoagulation

/-- The 7-node diamond causal poset of noncommutative archetypes `A1` through `A7`:
- Root: `A1_associativeJet`
- Branch A (Derivation / Gauge): `A1 → A3_ringDerivMatrixLift → A4_koszulMaurerCartan`
- Branch B (Clifford / Cocycle / Monodromy): `A1 → A2_brauerWeylQuaternion → A5_twistedGroupCocycle → A6_parabolicWittMonodromy`
- Apex: `A7_masterArtinBraidCurvature` uniting both branches. -/
inductive KoszulCocycleBraidArchetype
  | A1_associativeJet
  | A2_brauerWeylQuaternion
  | A3_ringDerivMatrixLift
  | A4_koszulMaurerCartan
  | A5_twistedGroupCocycle
  | A6_parabolicWittMonodromy
  | A7_masterArtinBraidCurvature
  deriving DecidableEq, Repr

private def archetypeEquivFin : KoszulCocycleBraidArchetype ≃ Fin 7 where
  toFun
    | .A1_associativeJet => 0
    | .A2_brauerWeylQuaternion => 1
    | .A3_ringDerivMatrixLift => 2
    | .A4_koszulMaurerCartan => 3
    | .A5_twistedGroupCocycle => 4
    | .A6_parabolicWittMonodromy => 5
    | .A7_masterArtinBraidCurvature => 6
  invFun
    | 0 => .A1_associativeJet
    | 1 => .A2_brauerWeylQuaternion
    | 2 => .A3_ringDerivMatrixLift
    | 3 => .A4_koszulMaurerCartan
    | 4 => .A5_twistedGroupCocycle
    | 5 => .A6_parabolicWittMonodromy
    | _ => .A7_masterArtinBraidCurvature
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype KoszulCocycleBraidArchetype :=
  Fintype.ofEquiv (Fin 7) archetypeEquivFin.symm

namespace KoszulCocycleBraidArchetype

/-- Reflexive-transitive prerequisite closure defining the diamond causal partial order. -/
def prerequisites : KoszulCocycleBraidArchetype → Finset KoszulCocycleBraidArchetype
  | .A1_associativeJet => {.A1_associativeJet}
  | .A2_brauerWeylQuaternion => {.A1_associativeJet, .A2_brauerWeylQuaternion}
  | .A3_ringDerivMatrixLift => {.A1_associativeJet, .A3_ringDerivMatrixLift}
  | .A4_koszulMaurerCartan =>
      {.A1_associativeJet, .A3_ringDerivMatrixLift, .A4_koszulMaurerCartan}
  | .A5_twistedGroupCocycle =>
      {.A1_associativeJet, .A2_brauerWeylQuaternion, .A5_twistedGroupCocycle}
  | .A6_parabolicWittMonodromy =>
      {.A1_associativeJet, .A2_brauerWeylQuaternion,
       .A5_twistedGroupCocycle, .A6_parabolicWittMonodromy}
  | .A7_masterArtinBraidCurvature =>
      {.A1_associativeJet, .A2_brauerWeylQuaternion, .A3_ringDerivMatrixLift,
       .A4_koszulMaurerCartan, .A5_twistedGroupCocycle,
       .A6_parabolicWittMonodromy, .A7_masterArtinBraidCurvature}

instance : PartialOrder KoszulCocycleBraidArchetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE KoszulCocycleBraidArchetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

instance : DecidableLT KoszulCocycleBraidArchetype := fun earlier later =>
  decidable_of_iff (earlier ≤ later ∧ ¬ later ≤ earlier) lt_iff_le_not_ge.symm

/-- Unordered worklist of all 7 archetypes presented to the topological dependency compiler. -/
def canonicalPending : List KoszulCocycleBraidArchetype :=
  [.A7_masterArtinBraidCurvature, .A6_parabolicWittMonodromy, .A4_koszulMaurerCartan,
   .A5_twistedGroupCocycle, .A3_ringDerivMatrixLift, .A2_brauerWeylQuaternion,
   .A1_associativeJet]

theorem canonicalPending_nodup : canonicalPending.Nodup := by
  dsimp [canonicalPending]
  decide

theorem canonicalPending_univ : canonicalPending.toFinset = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro a
  cases a <;> decide

theorem incomparable_gauge_and_monodromy_branches :
    ¬ A4_koszulMaurerCartan ≤ A6_parabolicWittMonodromy ∧
    ¬ A6_parabolicWittMonodromy ≤ A4_koszulMaurerCartan := by
  constructor
  · change ¬ prerequisites A4_koszulMaurerCartan ⊆ prerequisites A6_parabolicWittMonodromy
    decide
  · change ¬ prerequisites A6_parabolicWittMonodromy ⊆ prerequisites A4_koszulMaurerCartan
    decide

end KoszulCocycleBraidArchetype

/-- `A1` proved `TypedArchetype` on `NestedMat ℂ`: BCH degree-2 commutator and product failure. -/
noncomputable def archA1AssociativeJet :
    TypedArchetype (NestedMat ℂ × NestedMat ℂ) .proved where
  name := `InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset.archA1AssociativeJet
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun xy =>
    expJet2 xy.1 * expJet2 xy.2 - expJet2 xy.2 * expJet2 xy.1 =
      (4 : NestedMat ℂ) * ⁅xy.1, xy.2⁆ +
      (2 : NestedMat ℂ) * (xy.1 * xy.1 * xy.2 - xy.2 * (xy.1 * xy.1) +
        xy.1 * (xy.2 * xy.2) - xy.2 * xy.2 * xy.1) +
      (xy.1 * xy.1 * (xy.2 * xy.2) - xy.2 * xy.2 * (xy.1 * xy.1)) ∧
    expJet2 xy.1 * expJet2 xy.2 - (2 : NestedMat ℂ) * expJet2 (xy.1 + xy.2) =
      (2 : NestedMat ℂ) * ⁅xy.1, xy.2⁆ +
      (2 : NestedMat ℂ) * (xy.1 * xy.1 * xy.2 + xy.1 * (xy.2 * xy.2)) +
      xy.1 * xy.1 * (xy.2 * xy.2)
  evidence := fun xy =>
    ⟨bch_jet2_commutator_obstruction xy.1 xy.2, bch_jet2_product_expansion xy.1 xy.2⟩

/-- `A2` proved `TypedArchetype` over `NestedMat ℂ`: embedded quaternion Clifford and Lie triple. -/
noncomputable def archA2BrauerWeylQuaternion : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset.archA2BrauerWeylQuaternion
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (qE1 : NestedMat ℂ) * qE1 = -1 ∧
    (qE2 : NestedMat ℂ) * qE2 = -1 ∧
    (qE3 : NestedMat ℂ) * qE3 = -1 ∧
    anticomm (qE1 : NestedMat ℂ) qE2 = 0 ∧
    ⁅(qE1 : NestedMat ℂ), qE2⁆ = (2 : NestedMat ℂ) * qE3 ∧
    (qE1 : NestedMat ℂ) * qE2 ≠ qE2 * qE1
  evidence := fun _ => by
    rcases nested_quaternion_lie_relations (B := ℂ) with ⟨h1, h2, h3, hAnti, hL, _, _⟩
    exact ⟨h1, h2, h3, hAnti, hL, nested_quaternion_noncommutative (two_ne_zero : (2 : ℂ) ≠ 0)⟩

/-- `A3` proved `TypedArchetype` on `NestedMat ℂ`: inner commutator derivations and matrix lift. -/
noncomputable def archA3RingDerivMatrixLift :
    TypedArchetype (NestedMat ℂ × NestedMat ℂ × NestedMat ℂ) .proved where
  name := `InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset.archA3RingDerivMatrixLift
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun kab =>
    IsRingDeriv (innerDeriv kab.1) ∧
    IsRingDeriv (liftMatrixDeriv (n := Fin 2) (innerDeriv (sigmaOp : Mat2Z))) ∧
    innerDeriv kab.1 (kab.2.1 * kab.2.2) =
      innerDeriv kab.1 kab.2.1 * kab.2.2 + kab.2.1 * innerDeriv kab.1 kab.2.2
  evidence := fun kab =>
    ⟨innerDeriv_isRingDeriv kab.1,
     (innerDeriv_isRingDeriv (sigmaOp : Mat2Z)).liftMatrix,
     innerDeriv_isRingDeriv kab.1 kab.2.1 kab.2.2⟩

/-- `A4` proved `TypedArchetype` on `(NestedMat ℂ)ˣ`: Koszul covariance, flatness, and Bianchi
on commuting nonzero inner derivations. -/
noncomputable def archA4KoszulMaurerCartan :
    TypedArchetype ((NestedMat ℂ)ˣ × NestedMat ℂ × NestedMat ℂ × NestedMat ℂ) .proved where
  name := `InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset.archA4KoszulMaurerCartan
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun p =>
    let u := p.1
    let A₁ := p.2.1
    let A₂ := p.2.2.1
    let A₃ := p.2.2.2
    mcCurvature (nestedInnerD1 ℂ) (nestedInnerD2 ℂ)
      (dressConn (nestedInnerD1 ℂ) u A₁) (dressConn (nestedInnerD2 ℂ) u A₂) =
      (u : NestedMat ℂ) * mcCurvature (nestedInnerD1 ℂ) (nestedInnerD2 ℂ) A₁ A₂ * (↑u⁻¹ : NestedMat ℂ) ∧
    mcCurvature (nestedInnerD1 ℂ) (nestedInnerD2 ℂ)
      (-(nestedInnerD1 ℂ) (u : NestedMat ℂ) * (↑u⁻¹ : NestedMat ℂ))
      (-(nestedInnerD2 ℂ) (u : NestedMat ℂ) * (↑u⁻¹ : NestedMat ℂ)) = 0 ∧
    adjDeriv (nestedInnerD1 ℂ) A₁ (mcCurvature (nestedInnerD2 ℂ) (nestedInnerD3 ℂ) A₂ A₃) +
    adjDeriv (nestedInnerD2 ℂ) A₂ (mcCurvature (nestedInnerD3 ℂ) (nestedInnerD1 ℂ) A₃ A₁) +
    adjDeriv (nestedInnerD3 ℂ) A₃ (mcCurvature (nestedInnerD1 ℂ) (nestedInnerD2 ℂ) A₁ A₂) = 0
  evidence := fun p =>
    nested_inner_deriv_curvature_and_bianchi p.1 p.2.1 p.2.2.1 p.2.2.2

/-- `A5` proved `TypedArchetype` on `(NestedMat ℂ)ˣ`: general group 1-cocycle additivity. -/
noncomputable def archA5TwistedGroupCocycle :
    TypedArchetype ((NestedMat ℂ)ˣ × (NestedMat ℂ)ˣ × ℕ × ℕ) .proved where
  name := `InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset.archA5TwistedGroupCocycle
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun p =>
    twistedCocycle p.1 p.2.1 (p.2.2.1 + p.2.2.2) =
      twistedCocycle p.1 p.2.1 p.2.2.1 * conjBy (p.1 ^ p.2.2.1) (twistedCocycle p.1 p.2.1 p.2.2.2)
  evidence := fun p => twistedCocycle_add p.1 p.2.1 p.2.2.1 p.2.2.2

/-- `A6` proved `TypedArchetype` on `BlockMatZˣ`: parabolic Witt-link monodromy of infinite
order with torsion cocycle vanishing at `N = 2`. -/
def archA6ParabolicWittMonodromy : TypedArchetype {n : ℕ // 0 < n} .proved where
  name := `InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset.archA6ParabolicWittMonodromy
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun nh =>
    blkZUnit * blkXUnit = blkQUnit * blkXUnit * blkZUnit ∧
    blkQUnit * (blkXUnit * blkQUnit * blkXUnit) = 1 ∧
    twistedCocycle blkXUnit blkQUnit 2 = 1 ∧
    blkQUnit ^ nh.1 ≠ 1
  evidence := fun nh => blkQ_unit_cocycle_and_infinite_order nh.1 nh.2

/-- `A7` proved `TypedArchetype`: master Artin `B₃` representation, Maurer–Cartan curvature, and
parabolic monodromy synthesis. -/
noncomputable def archA7MasterArtinBraidCurvature :
    TypedArchetype ((NestedMat ℂ)ˣ × NestedMat ℂ × NestedMat ℂ × NestedMat ℂ × {n : ℕ // 0 < n}) .proved where
  name := `InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset.archA7MasterArtinBraidCurvature
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun p =>
    ((qR12 : NestedMat ℂ) * qR23 * qR12 = qR23 * qR12 * qR23 ∧
     ⁅(qR12 : NestedMat ℂ), qR23⁆ =
       mcCurvature (0 : NestedMat ℂ →+ NestedMat ℂ) 0 qE1 qE2 ∧
     mcCurvature (0 : NestedMat ℂ →+ NestedMat ℂ) 0 (qE1 : NestedMat ℂ) qE2 =
       (2 : NestedMat ℂ) * qE3 ∧
     mcCurvature (nestedInnerD1 ℂ) (nestedInnerD2 ℂ)
       (dressConn (nestedInnerD1 ℂ) p.1 p.2.1) (dressConn (nestedInnerD2 ℂ) p.1 p.2.2.1) =
       (p.1 : NestedMat ℂ) * mcCurvature (nestedInnerD1 ℂ) (nestedInnerD2 ℂ) p.2.1 p.2.2.1 * (↑p.1⁻¹ : NestedMat ℂ) ∧
     adjDeriv (nestedInnerD1 ℂ) p.2.1 (mcCurvature (nestedInnerD2 ℂ) (nestedInnerD3 ℂ) p.2.2.1 p.2.2.2.1) +
     adjDeriv (nestedInnerD2 ℂ) p.2.2.1 (mcCurvature (nestedInnerD3 ℂ) (nestedInnerD1 ℂ) p.2.2.2.1 p.2.1) +
     adjDeriv (nestedInnerD3 ℂ) p.2.2.2.1 (mcCurvature (nestedInnerD1 ℂ) (nestedInnerD2 ℂ) p.2.1 p.2.2.1) = 0) ∧
    (quaternionicBraidGroup3Hom (Braid.σ' 2 0) * quaternionicBraidGroup3Hom (Braid.σ' 2 1) ≠
       quaternionicBraidGroup3Hom (Braid.σ' 2 1) * quaternionicBraidGroup3Hom (Braid.σ' 2 0) ∧
     (qR12 : NestedMat ℂ) ^ 4 = (-4 : ℂ) • (1 : NestedMat ℂ) ∧
     blkQ ^ p.2.2.2.2.1 ≠ 1)
  evidence := fun p =>
    master_braid_curvature_synthesis p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2

/-- Parametric `TypedArchetype` bundling the full generic synthesis theorem over arbitrary rings. -/
noncomputable def koszulCocycleBraidPosetArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset.koszulCocycleBraidPosetArchetype
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (∀ (B : Type) [Ring B] (u : (NestedMat B)ˣ) (A₁ A₂ A₃ : NestedMat B) (n : ℕ), 0 < n →
      ((qR12 : NestedMat B) * qR23 * qR12 = qR23 * qR12 * qR23 ∧
       ⁅(qR12 : NestedMat B), qR23⁆ =
         mcCurvature (0 : NestedMat B →+ NestedMat B) 0 qE1 qE2 ∧
       mcCurvature (0 : NestedMat B →+ NestedMat B) 0 (qE1 : NestedMat B) qE2 =
         (2 : NestedMat B) * qE3 ∧
       mcCurvature (nestedInnerD1 B) (nestedInnerD2 B)
         (dressConn (nestedInnerD1 B) u A₁) (dressConn (nestedInnerD2 B) u A₂) =
         (u : NestedMat B) * mcCurvature (nestedInnerD1 B) (nestedInnerD2 B) A₁ A₂ * (↑u⁻¹ : NestedMat B) ∧
       adjDeriv (nestedInnerD1 B) A₁ (mcCurvature (nestedInnerD2 B) (nestedInnerD3 B) A₂ A₃) +
       adjDeriv (nestedInnerD2 B) A₂ (mcCurvature (nestedInnerD3 B) (nestedInnerD1 B) A₃ A₁) +
       adjDeriv (nestedInnerD3 B) A₃ (mcCurvature (nestedInnerD1 B) (nestedInnerD2 B) A₁ A₂) = 0) ∧
      (quaternionicBraidGroup3Hom (Braid.σ' 2 0) * quaternionicBraidGroup3Hom (Braid.σ' 2 1) ≠
         quaternionicBraidGroup3Hom (Braid.σ' 2 1) * quaternionicBraidGroup3Hom (Braid.σ' 2 0) ∧
       (qR12 : NestedMat ℂ) ^ 4 = (-4 : ℂ) • (1 : NestedMat ℂ) ∧
       blkQ ^ n ≠ 1)) ∧
    (∃ x y : Braid.braid_group 3,
      quaternionicBraidGroup3Hom (x * y) ≠ quaternionicBraidGroup3Hom (y * x))
  evidence := fun _ =>
    ⟨fun _ _ u A₁ A₂ A₃ n hn => master_braid_curvature_synthesis u A₁ A₂ A₃ n hn,
     quaternionicBraidGroup3Hom_nonabelian⟩

#register_archetype archA1AssociativeJet
#register_archetype archA2BrauerWeylQuaternion
#register_archetype archA3RingDerivMatrixLift
#register_archetype archA4KoszulMaurerCartan
#register_archetype archA5TwistedGroupCocycle
#register_archetype archA6ParabolicWittMonodromy
#register_archetype archA7MasterArtinBraidCurvature
#register_archetype koszulCocycleBraidPosetArchetype
#audit_archetype koszulCocycleBraidPosetArchetype

/-- Target proposition map for the 7-node diamond poset `KoszulCocycleBraidArchetype`. -/
noncomputable def koszulStatement : KoszulCocycleBraidArchetype → Prop
  | .A1_associativeJet => ∀ xy, archA1AssociativeJet.claim xy
  | .A2_brauerWeylQuaternion => archA2BrauerWeylQuaternion.claim ()
  | .A3_ringDerivMatrixLift => ∀ kab, archA3RingDerivMatrixLift.claim kab
  | .A4_koszulMaurerCartan => ∀ p, archA4KoszulMaurerCartan.claim p
  | .A5_twistedGroupCocycle => ∀ p, archA5TwistedGroupCocycle.claim p
  | .A6_parabolicWittMonodromy => ∀ nh, archA6ParabolicWittMonodromy.claim nh
  | .A7_masterArtinBraidCurvature => ∀ p, archA7MasterArtinBraidCurvature.claim p

private lemma koszulPosetRules : ProofRules koszulStatement := by
  intro target prereqs
  cases target with
  | A1_associativeJet => exact fun xy => archA1AssociativeJet.discharge xy
  | A2_brauerWeylQuaternion =>
    have _ := prereqs .A1_associativeJet (by decide)
    exact archA2BrauerWeylQuaternion.discharge ()
  | A3_ringDerivMatrixLift =>
    have _ := prereqs .A1_associativeJet (by decide)
    exact fun kab => archA3RingDerivMatrixLift.discharge kab
  | A4_koszulMaurerCartan =>
    have _ := prereqs .A3_ringDerivMatrixLift (by decide)
    exact fun p => archA4KoszulMaurerCartan.discharge p
  | A5_twistedGroupCocycle =>
    have _ := prereqs .A2_brauerWeylQuaternion (by decide)
    exact fun p => archA5TwistedGroupCocycle.discharge p
  | A6_parabolicWittMonodromy =>
    have _ := prereqs .A5_twistedGroupCocycle (by decide)
    exact fun nh => archA6ParabolicWittMonodromy.discharge nh
  | A7_masterArtinBraidCurvature =>
    have _ := prereqs .A4_koszulMaurerCartan (by decide)
    have _ := prereqs .A6_parabolicWittMonodromy (by decide)
    exact fun p => archA7MasterArtinBraidCurvature.discharge p

/-- **Certified Execution of `MetaEpistemicCompiler` on `KoszulCocycleBraidArchetype`**:
Compiles the reversed 7-node worklist `canonicalPending` into a valid topological schedule
preserving the diamond partial order and discharging every theorem in `NestedMat ℂ`, `BlockMatZ`,
and `Braid.braid_group 3 →* (NestedMat ℂ)ˣ`. -/
theorem koszul_cocycle_braid_executable_certified_compilation :
    ∃ schedule : List KoszulCocycleBraidArchetype,
      compile ∅ KoszulCocycleBraidArchetype.canonicalPending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card KoszulCocycleBraidArchetype ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, koszulStatement target :=
  executable_certified_compilation
    koszulStatement
    koszulPosetRules
    KoszulCocycleBraidArchetype.canonicalPending
    KoszulCocycleBraidArchetype.canonicalPending_nodup
    KoszulCocycleBraidArchetype.canonicalPending_univ

end CausalPosetCoagulation

end InfoGeometry.OperatorAlgebra.KoszulMaurerCartanCocycleBraidPoset
