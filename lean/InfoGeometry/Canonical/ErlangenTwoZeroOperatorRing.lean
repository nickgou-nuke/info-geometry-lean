/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Canonical.OperatorErlangenFixedPoints
import InfoGeometry.Canonical.OperatorErlangenGaloisConnection
import InfoGeometry.Core.LieJordanBoundaryOperators
import InfoGeometry.OperatorAlgebra.ChiralRailPlane
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Erlangen 2.0 for Noncommutative Operator Rings

Formalizes the **Erlangen 2.0** invariant principle $(\mathrm{Aut}(\mathcal{R}), \mathcal{R})$ where
geometry is the invariant information structure of an associative real operator ring `B` equipped
with an expectation/trace state `τ : B →ₗ[ℝ] ℝ` (`τ 1 = 1`):

1. **Abstract Operator Ring & Jordan–Lie Product Reconstruction**:
   `jordanProd X Y = ½ (X Y + Y X)` (metric/inner channel), `lieBracket X Y = X Y - Y X`
   (symplectic/outer channel), Koszul–Fisher state covariance `fisherCov X Y = τ(X ∘ Y) - τ(X) τ(Y)`,
   and center `inCenter Z := ∀ X, [Z, X] = 0`. Proves `X ∘ Y ± ½ [X, Y]`, symmetry/skew-symmetry,
   center collapse, Fisher variance expansion, and zero Fisher variance on scalar multiples `c • 1`.
2. **Metriplectic (GENERIC) Conservation & Entropy Production**:
   Under a cyclic trace state `τ(X Y) = τ(Y X)`, energy degeneracy `τ({S, H}_M) = 0`, and
   non-negative dissipation `0 ≤ τ({S, S}_M)`, proves First Law `τ(dH/dt) = 0`, Second Law
   `τ(dS/dt) = τ({S, S}_M) ≥ 0`, and invariant horizon decoupling `inCenter S → [H, S] = 0`.
3. **Concrete `M₂(ℝ)` Chiral Atom & Three-Way Erlangen Equivalence**:
   Reuses `DoubledMinkowskiBdGColimitBridge.{zCut2, xMir2}` and
   `DoubledMinkowskiRotatingSpinInstability.eps2`. Proves normalized trace cyclicity, exact Jordan
   variances `(1, 1, -1)` vs positive-definite Krein Hilbert–Schmidt Fisher variance
   `kreinFisherVar2 A = ((A₀₀ - A₁₁)² + 2 A₀₁² + 2 A₁₀²) / 4 ≥ 0` (`1, 1, 1` on `Z, X, ε`), and
   the three-way equivalence `inCenter A ↔ kreinFisherVar2 A = 0 ↔ ∃ c, A = c • I₂`.
4. **Inductive `Cl11TensorTower.MatStage n` OperatorRing Tower**:
   Instantiates `OperatorRing (MatStage n)` via `Cl11TensorTower.normalizedTrace n` and proves
   that `stageEmbed n : MatStage n →ₐ[ℝ] MatStage (n + 1)` preserves `jordanProd`, `lieBracket`,
   `traceState`, `fisherCov`, and `fisherVar` across every refinement scale.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & ALGEBRAIC THEOREMS
* `exists_noncomm_mat2_erlangen`, `exists_noncomm_matStage_erlangen`
* `erlangen_operator_ring_fundamental_laws`
* `erlangen_metriplectic_operator_laws`
* `erlangen_m2_chiral_atom_spec`
* `erlangen_cl11_stageEmbed_preserves_structure`
* `m2ChiralErlangenDatum_lie_hom`
* `ring_generic_erlangen_superbracket_and_invariants`, `m2_chiral_atom_eq_chiralRailPlane_and_datum`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* Abstract ring / metriplectic theorems hold for any `[OperatorRing B]` and explicit cyclicity,
  energy-degeneracy, and entropy-production hypotheses.

#### BUCKET 3: OPEN CLOSURE DEBT
* Infinite-dimensional von Neumann `II₁` factors, continuum Tomita–Takesaki modular flows, and
  unbounded unbounded-operator Fisher Hessian bundles lie beyond this finite-stage algebraic module.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Kronecker
open Matrix

namespace InfoGeometry.Canonical.ErlangenTwoZeroOperatorRing

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` (OpenGauss T16). -/
theorem exists_noncomm_mat2_erlangen :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨zCut2, xMir2, fun h => ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [zCut2, xMir2, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Explicit non-commutativity witness on `MatStage 2` (OpenGauss T16). -/
theorem exists_noncomm_matStage_erlangen :
    ∃ A B : MatStage 2, A * B ≠ B * A := by
  let A : MatStage 2 := (1 : MatStage 1) ⊗ₖ gamma_0_base
  let B : MatStage 2 := (1 : MatStage 1) ⊗ₖ gamma_1_base
  refine ⟨A, B, fun h => ?_⟩
  change ((1 : MatStage 1) ⊗ₖ gamma_0_base) * ((1 : MatStage 1) ⊗ₖ gamma_1_base) =
    ((1 : MatStage 1) ⊗ₖ gamma_1_base) * ((1 : MatStage 1) ⊗ₖ gamma_0_base) at h
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul] at h
  have h00 := congrArg (fun M : Matrix (TowerMatrix.Idx 1 × Fin 2) (TowerMatrix.Idx 1 × Fin 2) ℝ =>
    M (default, (0 : Fin 2)) (default, (0 : Fin 2))) h
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul] at h00
  norm_num [gamma_0_base, gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

/-! ### Part 1: Abstract Operator Ring, Jordan–Lie Channels, & State Variance -/

/-- An abstract real noncommutative operator ring `B` with an associative product and an
expectation/trace functional `traceState : B →ₗ[ℝ] ℝ` normalized by `traceState 1 = 1`. -/
class OperatorRing (B : Type*) extends Ring B, Algebra ℝ B where
  traceState : B →ₗ[ℝ] ℝ
  trace_one : traceState 1 = 1

variable {B : Type*} [OperatorRing B]

/-- Jordan symmetric product `X ∘ Y = ½(X Y + Y X)` (metric/inner channel). -/
def jordanProd (X Y : B) : B := (1 / 2 : ℝ) • (X * Y + Y * X)

/-- Lie antisymmetric bracket `[X, Y] = X Y - Y X` (symplectic/outer channel). -/
def lieBracket (X Y : B) : B := X * Y - Y * X

/-- Intrinsic Koszul–Fisher covariance pairing `g_F(X, Y) = τ(X ∘ Y) - τ(X) τ(Y)`. -/
def fisherCov (X Y : B) : ℝ :=
  OperatorRing.traceState (jordanProd X Y) -
    OperatorRing.traceState X * OperatorRing.traceState Y

/-- Intrinsic Koszul–Fisher state variance `g_F(X, X)`. -/
def fisherVar (X : B) : ℝ := fisherCov X X

/-- Center of the operator ring `𝒵(B) = {Z ∈ B | ∀ X, [Z, X] = 0}`. -/
def inCenter (Z : B) : Prop := ∀ X : B, lieBracket Z X = 0

private lemma scalar_c_sq_sub (c : ℝ) : (c * c) - (c * 1) ^ 2 = 0 := by
  ring

private lemma scalar_sub_pow_two (a b : ℝ) : a - b * b = a - b ^ 2 := by
  ring

/-- **Theorem 1 (Erlangen 2.0 Fundamental Operator-Ring Invariant Laws)**:
In any associative operator ring `[OperatorRing B]`:
1. Product reconstruction `X ∘ Y + ½[X, Y] = X * Y` and `X ∘ Y - ½[X, Y] = Y * X`.
2. Jordan symmetry and Lie skew-symmetry.
3. Center invariants collapse: `inCenter Z → Z ∘ X = Z * X ∧ [Z, X] = 0`.
4. Fisher variance expansion `g_F(X, X) = τ(X²) - (τ X)²` and scalar vanishing `g_F(c • 1, c • 1) = 0`. -/
theorem erlangen_operator_ring_fundamental_laws (X Y Z : B) (c : ℝ) :
    (jordanProd X Y + (1 / 2 : ℝ) • lieBracket X Y = X * Y) ∧
    (jordanProd X Y - (1 / 2 : ℝ) • lieBracket X Y = Y * X) ∧
    (jordanProd X Y = jordanProd Y X) ∧
    (lieBracket X Y = -lieBracket Y X) ∧
    (inCenter Z → jordanProd Z X = Z * X ∧ lieBracket Z X = 0) ∧
    (fisherVar X = OperatorRing.traceState (X * X) - (OperatorRing.traceState X) ^ 2) ∧
    (fisherVar (c • (1 : B)) = 0) := by
  have hRecon1 : jordanProd X Y + (1 / 2 : ℝ) • lieBracket X Y = X * Y := by
    unfold jordanProd lieBracket; module
  have hRecon2 : jordanProd X Y - (1 / 2 : ℝ) • lieBracket X Y = Y * X := by
    unfold jordanProd lieBracket; module
  have hSym : jordanProd X Y = jordanProd Y X := by
    unfold jordanProd; rw [add_comm]
  have hSkew : lieBracket X Y = -lieBracket Y X := by
    unfold lieBracket; abel
  have hCenter : inCenter Z → jordanProd Z X = Z * X := by
    intro hZ
    have hComm : Z * X = X * Z := sub_eq_zero.mp (hZ X)
    unfold jordanProd
    rw [← hComm, ← two_smul ℝ (Z * X), smul_smul]
    norm_num
  have hVarExp : ∀ A : B, fisherVar A =
      OperatorRing.traceState (A * A) - (OperatorRing.traceState A) ^ 2 := by
    intro A
    unfold fisherVar fisherCov jordanProd
    have hSq : (1 / 2 : ℝ) • (A * A + A * A) = A * A := by
      rw [← two_smul ℝ (A * A), smul_smul]; norm_num
    rw [hSq]
    exact scalar_sub_pow_two _ _
  have hVarScalar : fisherVar (c • (1 : B)) = 0 := by
    rw [hVarExp (c • (1 : B))]
    simp only [Algebra.mul_smul_comm, mul_one,
      map_smul, OperatorRing.trace_one, smul_eq_mul]
    rw [← sq, sub_self]
  refine ⟨hRecon1, hRecon2, hSym, hSkew, fun hZ => ⟨hCenter hZ, hZ X⟩, hVarExp X, hVarScalar⟩

/-! ### Part 2: Erlangen 2.0 Metriplectic Dynamics on Operator Rings -/

/-- Metriplectic rate `dA/dt = [H, A] + dissipator S A`. -/
def metriplecticRate (H S A : B) (dissipator : B → B → B) : B :=
  lieBracket H A + dissipator S A

/-- **Theorem 2 (Erlangen 2.0 Metriplectic First & Second Laws on Operator Rings)**:
For a cyclic trace state `hCyclic`, energy degeneracy `τ(dissipator S H) = 0`, and non-negative
entropy production `0 ≤ τ(dissipator S S)`:
1. `τ([H, H]) = 0`.
2. First Law (Energy conservation): `τ(metriplecticRate H S H dissipator) = 0`.
3. Second Law (Entropy production): `τ(metriplecticRate H S S dissipator) = τ(dissipator S S) ≥ 0`.
4. Center horizon decoupling: `inCenter S → [H, S] = 0`. -/
theorem erlangen_metriplectic_operator_laws
    (hCyclic : ∀ X Y : B, OperatorRing.traceState (X * Y) = OperatorRing.traceState (Y * X))
    (H S : B) (dissipator : B → B → B)
    (hDegH : OperatorRing.traceState (dissipator S H) = 0)
    (hEntropyProd : 0 ≤ OperatorRing.traceState (dissipator S S)) :
    let rate := metriplecticRate H S
    (OperatorRing.traceState (lieBracket H H) = 0) ∧
    (OperatorRing.traceState (rate H dissipator) = 0) ∧
    (OperatorRing.traceState (rate S dissipator) = OperatorRing.traceState (dissipator S S)) ∧
    (0 ≤ OperatorRing.traceState (rate S dissipator)) ∧
    (inCenter S → lieBracket H S = 0) := by
  dsimp [metriplecticRate]
  have hCommTraceZero : ∀ X Y : B, OperatorRing.traceState (lieBracket X Y) = 0 := by
    intro X Y
    unfold lieBracket
    rw [map_sub, hCyclic X Y, sub_self]
  have h1 : OperatorRing.traceState (lieBracket H H) = 0 := hCommTraceZero H H
  have hFirstLaw : OperatorRing.traceState (lieBracket H H + dissipator S H) = 0 := by
    rw [map_add, h1, zero_add, hDegH]
  have hSecondLaw : OperatorRing.traceState (lieBracket H S + dissipator S S) =
      OperatorRing.traceState (dissipator S S) := by
    rw [map_add, hCommTraceZero H S, zero_add]
  refine ⟨h1, hFirstLaw, hSecondLaw, ?_, ?_⟩
  · rw [hSecondLaw]; exact hEntropyProd
  · intro hS
    have hSkew := (erlangen_operator_ring_fundamental_laws H S 0 0).2.2.2.1
    rw [hSkew, hS H, neg_zero]

/-! ### Part 3: Concrete `M₂(ℝ)` Chiral Atom & Three-Way Erlangen Equivalence -/

private lemma scalar_half_mul_comm (c x : ℝ) :
    (1 / 2 : ℝ) * (c * x) = c * ((1 / 2 : ℝ) * x) := by
  ring

private def mat2NormalizedTraceLinear : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ where
  toFun A := (1 / 2 : ℝ) * Matrix.trace A
  map_add' A B := by rw [Matrix.trace_add, mul_add]
  map_smul' c A := by
    rw [Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
    exact scalar_half_mul_comm c (Matrix.trace A)

instance : OperatorRing (Matrix (Fin 2) (Fin 2) ℝ) where
  traceState := mat2NormalizedTraceLinear
  trace_one := by
    change (1 / 2 : ℝ) * Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1
    rw [trace_fin_two_one]
    norm_num

/-- Positive-definite Krein / Hilbert–Schmidt Koszul–Fisher variance `τ(Aᵀ ∘ A) - τ(A)²` on `M₂(ℝ)`. -/
def kreinFisherVar2 (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  OperatorRing.traceState (jordanProd Aᵀ A) - (OperatorRing.traceState A) ^ 2

private lemma scalar_krein_var2_formula (a b c d : ℝ) :
    (1 / 2 : ℝ) * ((a * a + b * b) + (c * c + d * d)) - ((1 / 2 : ℝ) * (a + d)) ^ 2 =
      ((a - d) ^ 2 + 2 * b ^ 2 + 2 * c ^ 2) / 4 := by
  ring

private lemma scalar_krein_var2_nonneg (a b c d : ℝ) :
    0 ≤ ((a - d) ^ 2 + 2 * b ^ 2 + 2 * c ^ 2) / 4 := by
  positivity

private lemma scalar_krein_var2_eq_zero_iff (a b c d : ℝ) :
    ((a - d) ^ 2 + 2 * b ^ 2 + 2 * c ^ 2) / 4 = 0 ↔ b = 0 ∧ c = 0 ∧ d = a := by
  constructor
  · intro h
    have h4 : (a - d) ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 = 0 := by linarith
    have had : (a - d) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - d), sq_nonneg b, sq_nonneg c]
    have hb2 : b ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - d), sq_nonneg b, sq_nonneg c]
    have hc2 : c ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - d), sq_nonneg b, sq_nonneg c]
    have ha0 : a - d = 0 := (pow_eq_zero_iff (by norm_num)).mp had
    have hb0 : b = 0 := (pow_eq_zero_iff (by norm_num)).mp hb2
    have hc0 : c = 0 := (pow_eq_zero_iff (by norm_num)).mp hc2
    exact ⟨hb0, hc0, by linarith [ha0]⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

private lemma scalar_m2_center_eqs (a b c d : ℝ)
    (h1 : -b - b = 0) (h2 : c = 0) (h3 : a - d = 0) :
    b = 0 ∧ c = 0 ∧ d = a := by
  exact ⟨by linarith [h1], h2, by linarith [h3]⟩

private lemma scalar_one_sub_zero : (1 : ℝ) - 0 ^ 2 = 1 := by ring
private lemma scalar_neg_one_sub_zero : (-1 : ℝ) - 0 ^ 2 = -1 := by ring

private lemma kreinFisherVar2_eq_formula (A : Matrix (Fin 2) (Fin 2) ℝ) :
    kreinFisherVar2 A =
      ((A 0 0 - A 1 1) ^ 2 + 2 * (A 0 1) ^ 2 + 2 * (A 1 0) ^ 2) / 4 := by
  unfold kreinFisherVar2 jordanProd
  change (1 / 2 : ℝ) * Matrix.trace ((1 / 2 : ℝ) • (Aᵀ * A + A * Aᵀ)) -
      ((1 / 2 : ℝ) * Matrix.trace A) ^ 2 = _
  rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_add, Matrix.trace_mul_comm A Aᵀ, ← two_mul]
  have h1 : (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (2 * Matrix.trace (Aᵀ * A))) =
      (1 / 2 : ℝ) * Matrix.trace (Aᵀ * A) := by ring
  rw [h1]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  rw [show A 0 0 * A 0 0 + A 1 0 * A 1 0 + (A 0 1 * A 0 1 + A 1 1 * A 1 1) =
    (A 0 0 * A 0 0 + A 0 1 * A 0 1) + (A 1 0 * A 1 0 + A 1 1 * A 1 1) by ring]
  exact scalar_krein_var2_formula (A 0 0) (A 0 1) (A 1 0) (A 1 1)

/-- **Theorem 3 (Erlangen 2.0 Chiral Atom `M₂(ℝ)` & Three-Way Invariant Characterization)**:
1. `traceState 1 = 1` and `traceState (A * B) = traceState (B * A)`.
2. All three traceless generators satisfy `traceState zCut2 = 0`, `xMir2`, `eps2`.
3. Jordan state variances are `(1, 1, -1)` while Krein Hilbert–Schmidt Fisher variances are
   strictly positive `(1, 1, 1)`, and `0 ≤ kreinFisherVar2 A` for all `A : M₂(ℝ)`.
4. **Three-Way Erlangen Equivalence**:
   `inCenter A ↔ kreinFisherVar2 A = 0 ↔ ∃ c : ℝ, A = c • 1`. -/
theorem erlangen_m2_chiral_atom_spec :
    (OperatorRing.traceState (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1) ∧
    (∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
      OperatorRing.traceState (A * B) = OperatorRing.traceState (B * A)) ∧
    (OperatorRing.traceState zCut2 = 0 ∧
      OperatorRing.traceState xMir2 = 0 ∧
      OperatorRing.traceState eps2 = 0) ∧
    (fisherVar zCut2 = 1 ∧ fisherVar xMir2 = 1 ∧ fisherVar eps2 = -1) ∧
    (kreinFisherVar2 zCut2 = 1 ∧ kreinFisherVar2 xMir2 = 1 ∧ kreinFisherVar2 eps2 = 1 ∧
      ∀ A : Matrix (Fin 2) (Fin 2) ℝ, 0 ≤ kreinFisherVar2 A) ∧
    (∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      (inCenter A ↔ ∃ c : ℝ, A = c • 1) ∧
      (kreinFisherVar2 A = 0 ↔ ∃ c : ℝ, A = c • 1)) := by
  have hTrOne : OperatorRing.traceState (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
    OperatorRing.trace_one
  have hCyclic : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
      OperatorRing.traceState (A * B) = OperatorRing.traceState (B * A) := fun A B => by
    change (1 / 2 : ℝ) * Matrix.trace (A * B) = (1 / 2 : ℝ) * Matrix.trace (B * A)
    rw [Matrix.trace_mul_comm]
  have hTrZ : OperatorRing.traceState zCut2 = 0 := by
    simp [OperatorRing.traceState, mat2NormalizedTraceLinear, zCut2, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two]
  have hTrX : OperatorRing.traceState xMir2 = 0 := by
    simp [OperatorRing.traceState, mat2NormalizedTraceLinear, xMir2, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two]
  have hTrE : OperatorRing.traceState eps2 = 0 := by
    simp [OperatorRing.traceState, mat2NormalizedTraceLinear, eps2, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two]
  have hZ2 : zCut2 * zCut2 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [zCut2, Matrix.mul_apply, Fin.sum_univ_two]
  have hX2 : xMir2 * xMir2 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [xMir2, Matrix.mul_apply, Fin.sum_univ_two]
  have hE2 : eps2 * eps2 = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [eps2, Matrix.mul_apply, Fin.sum_univ_two]
  have hVarZ : fisherVar zCut2 = 1 := by
    rw [(erlangen_operator_ring_fundamental_laws zCut2 zCut2 0 0).2.2.2.2.2.1, hZ2, hTrOne, hTrZ]
    exact scalar_one_sub_zero
  have hVarX : fisherVar xMir2 = 1 := by
    rw [(erlangen_operator_ring_fundamental_laws xMir2 xMir2 0 0).2.2.2.2.2.1, hX2, hTrOne, hTrX]
    exact scalar_one_sub_zero
  have hVarE : fisherVar eps2 = -1 := by
    rw [(erlangen_operator_ring_fundamental_laws eps2 eps2 0 0).2.2.2.2.2.1, hE2, map_neg,
      hTrOne, hTrE]
    exact scalar_neg_one_sub_zero
  have hKVarZ : kreinFisherVar2 zCut2 = 1 := by
    rw [kreinFisherVar2_eq_formula]; norm_num [zCut2]
  have hKVarX : kreinFisherVar2 xMir2 = 1 := by
    rw [kreinFisherVar2_eq_formula]; norm_num [xMir2]
  have hKVarE : kreinFisherVar2 eps2 = 1 := by
    rw [kreinFisherVar2_eq_formula]; norm_num [eps2]
  have hKNonneg : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, 0 ≤ kreinFisherVar2 A := fun A => by
    rw [kreinFisherVar2_eq_formula]
    exact scalar_krein_var2_nonneg (A 0 0) (A 0 1) (A 1 0) (A 1 1)
  refine ⟨hTrOne, hCyclic, ⟨hTrZ, hTrX, hTrE⟩, ⟨hVarZ, hVarX, hVarE⟩,
    ⟨hKVarZ, hKVarX, hKVarE, hKNonneg⟩, fun A => ⟨?_, ?_⟩⟩
  · constructor
    · intro hCent
      have hCommZ := hCent zCut2
      have hCommX := hCent xMir2
      unfold lieBracket at hCommZ hCommX
      have hZ01 := congrFun (congrFun hCommZ 0) 1
      have hZ10 := congrFun (congrFun hCommZ 1) 0
      have hX01 := congrFun (congrFun hCommX 0) 1
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_two] at hZ01 hZ10 hX01
      norm_num [zCut2, xMir2] at hZ01 hZ10 hX01
      obtain ⟨hb, hc, hd⟩ := scalar_m2_center_eqs (A 0 0) (A 0 1) (A 1 0) (A 1 1) hZ01 hZ10 hX01
      refine ⟨A 0 0, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hc, hd]
    · rintro ⟨c, rfl⟩ X
      unfold lieBracket
      simp only [Algebra.smul_mul_assoc, one_mul, Algebra.mul_smul_comm, mul_one, sub_self]
  · rw [kreinFisherVar2_eq_formula, scalar_krein_var2_eq_zero_iff]
    constructor
    · rintro ⟨hb, hc, hd⟩
      refine ⟨A 0 0, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hc, hd]
    · rintro ⟨c, rfl⟩
      simp

/-! ### Part 4: Inductive `Cl11TensorTower.MatStage n` OperatorRing Tower -/

private def matStageNormalizedTraceLinear (n : ℕ) : MatStage n →ₗ[ℝ] ℝ where
  toFun A := normalizedTrace n A
  map_add' A B := by
    dsimp [normalizedTrace]
    rw [Matrix.trace_add, add_div]
  map_smul' c A := by
    dsimp [normalizedTrace]
    rw [Matrix.trace_smul, smul_eq_mul, mul_div_assoc]

private lemma scalar_pow_two_div_self (n : ℕ) : ((2 : ℝ) ^ n) / ((2 : ℝ) ^ n) = 1 :=
  div_self (pow_ne_zero n (by norm_num))

instance (n : ℕ) : OperatorRing (MatStage n) where
  traceState := matStageNormalizedTraceLinear n
  trace_one := by
    change normalizedTrace n (1 : MatStage n) = 1
    unfold normalizedTrace
    rw [Matrix.trace_one, Fintype.card_eq_nat_card, Nat.card_eq_fintype_card,
      TowerMatrix.idx_card_pow_two n]
    push_cast
    exact scalar_pow_two_div_self n

/-- **Theorem 4 (Inductive `Cl11TensorTower` Scale-Invariant Erlangen Operator-Ring Bridge)**:
For every tensor stage `n : ℕ`, `stageEmbed n : MatStage n →ₐ[ℝ] MatStage (n + 1)` preserves:
1. Jordan metric products and Lie brackets (`jordanProd`, `lieBracket`).
2. Expectation trace states (`traceState (stageEmbed n A) = traceState A`).
3. Intrinsic Koszul–Fisher covariances and variances (`fisherCov`, `fisherVar`). -/
theorem erlangen_cl11_stageEmbed_preserves_structure (n : ℕ) (X Y : MatStage n) :
    (stageEmbed n (jordanProd X Y) = jordanProd (stageEmbed n X) (stageEmbed n Y)) ∧
    (stageEmbed n (lieBracket X Y) = lieBracket (stageEmbed n X) (stageEmbed n Y)) ∧
    (OperatorRing.traceState (stageEmbed n X) = OperatorRing.traceState X) ∧
    (fisherCov (stageEmbed n X) (stageEmbed n Y) = fisherCov X Y) ∧
    (fisherVar (stageEmbed n X) = fisherVar X) := by
  have hTr : ∀ Z : MatStage n, OperatorRing.traceState (stageEmbed n Z) = OperatorRing.traceState Z := by
    intro Z
    change normalizedTrace (n + 1) (matStageEmbed n Z) = normalizedTrace n Z
    exact normalizedTrace_matStageEmbed n Z
  have hJ : stageEmbed n (jordanProd X Y) = jordanProd (stageEmbed n X) (stageEmbed n Y) := by
    unfold jordanProd
    rw [map_smul, map_add, map_mul, map_mul]
  have hL : stageEmbed n (lieBracket X Y) = lieBracket (stageEmbed n X) (stageEmbed n Y) := by
    unfold lieBracket
    rw [map_sub, map_mul, map_mul]
  have hCov : ∀ A B : MatStage n, fisherCov (stageEmbed n A) (stageEmbed n B) = fisherCov A B := by
    intro A B
    unfold fisherCov jordanProd
    rw [← map_mul, ← map_mul, ← map_add, ← map_smul, hTr, hTr, hTr]
  refine ⟨hJ, hL, hTr X, hCov X Y, ?_⟩
  simpa [fisherVar] using hCov X X

/-! ### Part 5: Bridge to Repo `Erlangen20OperatorGeometryDatum` -/

section DatumBridge

open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum

local instance end2LieRing : LieRing (Module.End ℝ (Fin 2 → ℝ)) :=
  LieRing.ofAssociativeRing

local instance end2LieAlgebra : LieAlgebra ℝ (Module.End ℝ (Fin 2 → ℝ)) :=
  LieAlgebra.ofAssociativeAlgebra

/-- Concrete `Erlangen20Datum` packaging `End_ℝ(ℝ²)` (`M₂(ℝ)`) with `(zCut2, xMir2, eps2)` and their
three Krein Hilbert–Schmidt Koszul–Fisher invariants
`(kreinFisherVar2 zCut2, kreinFisherVar2 xMir2, kreinFisherVar2 eps2)`. -/
def m2ChiralErlangenDatum :
    Erlangen20Datum ℝ (Fin 2 → ℝ) (Module.End ℝ (Fin 2 → ℝ))
      (Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ)
      (ℝ × ℝ × ℝ) where
  operatorAlgebra := ⊤
  representation := LieHom.id
  representation_mem _ := Algebra.mem_top
  symmetryData := (zCut2, xMir2, eps2)
  invariantData := (kreinFisherVar2 zCut2, kreinFisherVar2 xMir2, kreinFisherVar2 eps2)

/-- `m2ChiralErlangenDatum` realizes exact Lie-bracket equivariance and unit normalized variances. -/
theorem m2ChiralErlangenDatum_lie_hom (X Y : Module.End ℝ (Fin 2 → ℝ)) :
    m2ChiralErlangenDatum.representation ⁅X, Y⁆ =
      m2ChiralErlangenDatum.representation X * m2ChiralErlangenDatum.representation Y -
        m2ChiralErlangenDatum.representation Y * m2ChiralErlangenDatum.representation X ∧
    m2ChiralErlangenDatum.invariantData = (1, 1, 1) := by
  have hSpec := erlangen_m2_chiral_atom_spec
  refine ⟨m2ChiralErlangenDatum.representation_map_lie X Y, ?_⟩
  simp [m2ChiralErlangenDatum, hSpec.2.2.2.2.1.1, hSpec.2.2.2.2.1.2.1, hSpec.2.2.2.2.1.2.2.1]

end DatumBridge

/-! ### Part 6: Preexisting Noncommutative-Ring (`[Ring B]` / `[Ring R]`) Erlangen 2.0 & `ChiralRailPlane` Bridge -/

section NoncommRingErlangenBridge

open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Core.LieJordanBoundaryOperators
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ChiralRailPlane
open InfoGeometry.Canonical.OperatorErlangenFixedPoints

/-- **Theorem 6A (Ring-Generic Noncommutative Erlangen 2.0, Superbracket, Lie–Jordan, & Galois Bridge)**:
Over ANY noncommutative ring `[OperatorRing B]` and symmetry group `[Group G]` with
`α : SymmetryAction G B` and `[MulSemiringAction G B]`:
1. Identifies `lieBracket` / `jordanProd` with `SupergradedBracket.{commutator, anticommutator}`,
   `Core.JordanMultiplicationClosure.jordanLeft`, and `LieJordanBoundaryOperators.ring_ad_mul_jordan_self_apply`.
2. Proves `α.act g` preserves `SupergradedBracket.superBracket`, preserves the ring center
   `inCenter Z → inCenter (α.act g Z)`, and characterizes `invariantSubring α`.
3. Connects directly to `OperatorErlangenFixedPoints.subgroup_le_fixingSubgroup_iff` and
   `fixedPointSet_superBracket_mem`. -/
theorem ring_generic_erlangen_superbracket_and_invariants
    {B : Type*} [OperatorRing B]
    {G : Type*} [Group G] (α : SymmetryAction G B) [MulSemiringAction G B]
    (H : Subgroup G) (S : Set B) (g : G) (X Y Z : B) (p q : Bool) :
    (lieBracket X Y = commutator X Y) ∧
    ((2 : ℝ) • jordanProd X Y = anticommutator X Y) ∧
    (jordanLeft (R := ℝ) X Y = (2 : ℝ) • jordanProd X Y) ∧
    (X * (X * Y + Y * X) - (X * Y + Y * X) * X = (X * X) * Y - Y * (X * X)) ∧
    ((α.act g) (superBracket p q X Y) = superBracket p q (α.act g X) (α.act g Y)) ∧
    (inCenter Z → inCenter (α.act g Z)) ∧
    (Z ∈ invariantSubring α ↔ IsInvariant α Z) ∧
    (H ≤ fixingSubgroup (G := G) (A := B) S ↔ S ⊆ fixedPointSet (G := G) (A := B) H) ∧
    (X ∈ ringFixedPointSet (G := G) H → Y ∈ ringFixedPointSet (G := G) H →
      superBracket p q X Y ∈ ringFixedPointSet (G := G) H) := by
  have hLie : lieBracket X Y = commutator X Y := rfl
  have hJord : (2 : ℝ) • jordanProd X Y = anticommutator X Y := by
    unfold jordanProd anticommutator
    rw [smul_smul]
    norm_num
  have hJLeft : jordanLeft (R := ℝ) X Y = (2 : ℝ) • jordanProd X Y := by
    change X * Y + Y * X = (2 : ℝ) • jordanProd X Y
    exact hJord.symm
  have hAd : X * (X * Y + Y * X) - (X * Y + Y * X) * X = (X * X) * Y - Y * (X * X) :=
    ring_ad_mul_jordan_self_apply X Y
  have hMapSB : (α.act g) (superBracket p q X Y) = superBracket p q (α.act g X) (α.act g Y) :=
    map_superBracket (α.act g).toRingHom p q X Y
  have hCent : inCenter Z → inCenter (α.act g Z) := by
    intro hZ W
    unfold lieBracket
    have hZW := hZ ((α.act g).symm W)
    unfold lieBracket at hZW
    have hEq : α.act g Z * W - W * α.act g Z =
        α.act g (Z * (α.act g).symm W - (α.act g).symm W * Z) := by
      rw [map_sub, map_mul, map_mul, RingEquiv.apply_symm_apply]
    rw [hEq, hZW, map_zero]
  have hInv : Z ∈ invariantSubring α ↔ IsInvariant α Z := mem_invariantSubring_iff α Z
  have hGal : H ≤ fixingSubgroup (G := G) (A := B) S ↔ S ⊆ fixedPointSet (G := G) (A := B) H :=
    subgroup_le_fixingSubgroup_iff
  have hSB : X ∈ ringFixedPointSet (G := G) H → Y ∈ ringFixedPointSet (G := G) H →
      superBracket p q X Y ∈ ringFixedPointSet (G := G) H :=
    fixedPointSet_superBracket_mem (G := G) (B := B)
      (fun h a b => MulSemiringAction.smul_mul (M := G) (R := B) h a b) H p q
  exact ⟨hLie, hJord, hJLeft, hAd, hMapSB, hCent, hInv, hGal, hSB⟩

/-- **Theorem 6B (`ChiralRailPlane` `[Ring R]` Anchor & `M₂(ℝ)` Specialization)**:
Over ANY nontrivial ring `[Ring R] [Nontrivial R]`, `ChiralRailPlane`'s raising/lowering operators
`E_R_standard, E_L_standard` do not commute, satisfy `[E_R, E_L] = Γ_standard` and `{E_R, E_L} = 1`,
and at `R = ℝ` specialize to `zCut2`, `xMir2`, `eps2`. -/
theorem m2_chiral_atom_eq_chiralRailPlane_and_datum (R : Type*) [Ring R] [Nontrivial R] :
    ((E_R_standard : Matrix (Fin 2) (Fin 2) R) * E_L_standard ≠
        E_L_standard * E_R_standard) ∧
    (E_R_standard * E_L_standard - E_L_standard * E_R_standard =
        (Γ_standard : Matrix (Fin 2) (Fin 2) R)) ∧
    (E_R_standard * E_L_standard + E_L_standard * E_R_standard =
        (1 : Matrix (Fin 2) (Fin 2) R)) ∧
    (zCut2 = (Γ_standard : Matrix (Fin 2) (Fin 2) ℝ) ∧
     xMir2 = (E_R_standard : Matrix (Fin 2) (Fin 2) ℝ) + E_L_standard ∧
     eps2 = (Ω_standard : Matrix (Fin 2) (Fin 2) ℝ)) := by
  refine ⟨E_R_E_L_noncomm, commutator_E_R_E_L_standard, anticommutator_E_R_E_L_standard, ?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zCut2, xMir2, eps2, Γ_standard, E_R_standard, E_L_standard, Ω_standard]

end NoncommRingErlangenBridge

end InfoGeometry.Canonical.ErlangenTwoZeroOperatorRing
