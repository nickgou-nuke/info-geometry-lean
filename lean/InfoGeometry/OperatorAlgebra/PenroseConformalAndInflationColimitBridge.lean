/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ConformalCyclicCosmology
import InfoGeometry.Lie.Pin55NondegenerateKreinBridge
import InfoGeometry.Lie.SO55GlobalConformalPrecursors
import InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
import InfoGeometry.Algebra.FibonacciGrothendieckRing
import InfoGeometry.Canonical.PeircePolygonKreinBottMasterSynthesis

/-!
# Constructive Bridge: `SO(5,5)` Dirac Conformal Cyclic Crossover and `FibonacciK0`--Penrose Kite/Dart Colimits

Connects two further Penrose operator-algebraic lanes to concrete carriers and colimits:

1. **Concrete `(5,5)` Dirac Null-Cone Realization of `AeonConformalCrossover`**:
   Embeds `(1,3)` Minkowski spacetime `Minkowski13` into the nondegenerate `(5,5)` Krein null
   quadric `NullQuadric ⊆ Fin 10 → ℝ` via `diracNullConeEmbed`, constructs the ambient
   reflection-inversion datum `so55MobiusInversionDatum : MobiusInversionDatum (Fin 10 → ℝ)`,
   proves that nonlinear conformal inversion `p ↦ (Q55 (minkowskiSlice p))⁻¹ • p` lifts to the
   projective Krein inversion `(Q55 (minkowskiSlice p))⁻¹ • kreinConformalInversion55 (diracNullConeEmbed p)`,
   constructs a concrete nontrivial `AeonConformalCrossover Minkowski13 Minkowski13 (Fin 10 → ℝ)`
   together with a nontrivial scale-invariant `CrossoverLightlikeGrammar`, and proves preservation
   of the conformal null cone under `so55Boost ξ : SO(5,5)`.
2. **`FibonacciK0` Grothendieck Fusion Ring $\leftrightarrow$ Noncommutative Penrose Kite/Dart
   Operator Tower & `Cl(5,5)` Bott Colimit**:
   For any idempotent `P` in any associative ring `[Ring B]` with unit Penrose Dart horizon
   `penroseDartOp P A C = 1`, constructs the additive evaluation map
   `evalFibonacciK0OnPenroseKite P A C : FibonacciK0 →+ B` and proves it is a multiplicative
   ring homomorphism sending `k0Mul` to ring multiplication, specializes `polygonFibSeq P A C m`
   to `(Nat.fib m : B)`, supplies an explicit noncommuting `2 × 2` matrix witness (`A * C ≠ C * A`),
   and transports the Fibonacci--Lucas Penrose Kite/Dart inflation law across `cl55ToBottStage k`
   into `Cl11TensorTowerLimit.Limit`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ConformalCyclicCosmology
open InfoGeometry.Lie.Pin55NondegenerateKreinBridge
open InfoGeometry.Lie.SO55GlobalConformalPrecursors
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Algebra.FibonacciGrothendieckRing
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.PeircePolygonKreinBottMasterSynthesis
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Clifford55

/-! ## 1. Dirac `(5,5)` Conformal Null-Cone Realization of `AeonConformalCrossover` -/

/-- Ambient `O(5,5)` conformal reflection-inversion on `Fin 10 → ℝ`, flipping the negative-weight
compactification coordinate `v 4` while preserving `v 9` and `(t, x₁, x₂, x₃)`. -/
def kreinConformalInversion55 : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ) where
  toFun v i := if i = 4 then -v 4 else v i
  map_add' u v := by
    ext i
    by_cases hi : i = 4 <;> simp [hi, Pi.add_apply]
    ring
  map_smul' c v := by
    ext i
    by_cases hi : i = 4 <;> simp [hi, Pi.smul_apply]

theorem kreinConformalInversion55_sq (v : Fin 10 → ℝ) :
    kreinConformalInversion55 (kreinConformalInversion55 v) = v := by
  ext i
  fin_cases i <;> simp [kreinConformalInversion55]

theorem kreinConformalInversion55_isometry (x y : Fin 10 → ℝ) :
    kreinForm55 (kreinConformalInversion55 x) (kreinConformalInversion55 y) =
      kreinForm55 x y := by
  rw [kreinForm55_apply, kreinForm55_apply]
  congr 1
  ext i
  fin_cases i <;> simp [kreinConformalInversion55]

/-- Concrete `(5,5)` Krein Möbius inversion datum on `Fin 10 → ℝ`. -/
def so55MobiusInversionDatum :
    InfoGeometry.OperatorAlgebra.MobiusInversionDatum (Fin 10 → ℝ) where
  inv := kreinConformalInversion55
  inv_sq := kreinConformalInversion55_sq
  nullCone := { v : Fin 10 → ℝ | kreinForm55 v v = 0 }
  preserves_null := by
    intro v hv
    change kreinForm55 (kreinConformalInversion55 v) (kreinConformalInversion55 v) = 0
    rw [kreinConformalInversion55_isometry]
    exact hv

theorem mem_nullQuadric_iff (v : Fin 10 → ℝ) :
    v ∈ NullQuadric ↔ v ≠ 0 ∧ v ∈ so55MobiusInversionDatum.nullCone :=
  Iff.rfl

/-- Every `so55Boost ξ` preserves the Möbius null cone `{v | kreinForm55 v v = 0}`. -/
theorem so55Boost_preserves_nullCone (ξ : ℝ) {v : Fin 10 → ℝ}
    (hv : v ∈ so55MobiusInversionDatum.nullCone) :
    (so55Boost ξ).mulVec v ∈ so55MobiusInversionDatum.nullCone := by
  change kreinForm55 ((so55Boost ξ).mulVec v) ((so55Boost ξ).mulVec v) = 0
  rw [isSO55_isometry (so55Boost ξ) (so55Boost_isSO55 ξ) v v]
  exact hv

/-- Dirac projective null-cone embedding of `(1,3)` Minkowski spacetime into `(5,5)` Krein space:
`diracNullConeEmbed (t, x₁, x₂, x₃)` places `(t, x₁, x₂, x₃)` in indices `(0; 5, 6, 7)` and
lightcone coordinates `((1 - q)/2, (1 + q)/2)` in indices `(4, 9)`, where `q = Q55 (minkowskiSlice p)`. -/
def diracNullConeEmbed (p : Minkowski13) : Fin 10 → ℝ :=
  let q := InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p)
  fun i =>
    if i = 0 then p.1
    else if i = 4 then (1 - q) / 2
    else if i = 5 then p.2 0
    else if i = 6 then p.2 1
    else if i = 7 then p.2 2
    else if i = 9 then (1 + q) / 2
    else 0

/-- Every Dirac null-cone image lies on the `(5,5)` Krein null cone. -/
theorem diracNullConeEmbed_mem_nullCone (p : Minkowski13) :
    diracNullConeEmbed p ∈ so55MobiusInversionDatum.nullCone := by
  change kreinForm55 (diracNullConeEmbed p) (diracNullConeEmbed p) = 0
  rw [kreinForm55_apply, sum_fin10]
  have hq : InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p) =
      p.1 ^ 2 - (p.2 0 ^ 2 + p.2 1 ^ 2 + p.2 2 ^ 2) := by
    rw [Q55_minkowskiSlice, Fin.sum_univ_three]
  simp [diracNullConeEmbed, hq]
  ring

/-- Every Dirac null-cone image is nonzero because `v 4 + v 9 = 1`, so it lies in `NullQuadric`. -/
theorem diracNullConeEmbed_mem_nullQuadric (p : Minkowski13) :
    diracNullConeEmbed p ∈ NullQuadric := by
  refine ⟨?_, diracNullConeEmbed_mem_nullCone p⟩
  intro h0
  have h4 := congrFun h0 4
  have h9 := congrFun h0 9
  simp only [diracNullConeEmbed, Fin.reduceEq, ↓reduceIte, Pi.zero_apply] at h4 h9
  linarith

/-- Nonlinear Minkowski conformal inversion `p ↦ p / Q55(p)`. -/
def minkowskiConformalInvert (p : Minkowski13) : Minkowski13 :=
  let q := InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p)
  (q⁻¹ * p.1, q⁻¹ • p.2)

theorem Q55_minkowskiConformalInvert {p : Minkowski13}
    (hq : InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p) ≠ 0) :
    InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice (minkowskiConformalInvert p)) =
      (InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p))⁻¹ := by
  have hq_def : InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p) =
      p.1 ^ 2 - (p.2 0 ^ 2 + p.2 1 ^ 2 + p.2 2 ^ 2) := by
    rw [Q55_minkowskiSlice, Fin.sum_univ_three]
  let q := InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p)
  unfold minkowskiConformalInvert
  rw [Q55_minkowskiSlice, Fin.sum_univ_three]
  dsimp [Pi.smul_apply, smul_eq_mul]
  change (q⁻¹ * p.1) ^ 2 - ((q⁻¹ * p.2 0) ^ 2 + (q⁻¹ * p.2 1) ^ 2 + (q⁻¹ * p.2 2) ^ 2) = q⁻¹
  calc
    (q⁻¹ * p.1) ^ 2 - ((q⁻¹ * p.2 0) ^ 2 + (q⁻¹ * p.2 1) ^ 2 + (q⁻¹ * p.2 2) ^ 2)
        = (q⁻¹) ^ 2 * (p.1 ^ 2 - (p.2 0 ^ 2 + p.2 1 ^ 2 + p.2 2 ^ 2)) := by ring
    _ = (q⁻¹) ^ 2 * q := by rw [← hq_def]
    _ = q⁻¹ * (q⁻¹ * q) := by ring
    _ = q⁻¹ := by rw [inv_mul_cancel₀ hq, mul_one]

/-- **Dirac Conformal Linearization Theorem**: nonlinear Minkowski inversion corresponds under
`diracNullConeEmbed` to the projective scaling `q⁻¹ • kreinConformalInversion55 (diracNullConeEmbed p)`. -/
theorem diracNullConeEmbed_conformalInvert {p : Minkowski13}
    (hq : InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p) ≠ 0) :
    diracNullConeEmbed (minkowskiConformalInvert p) =
      (InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p))⁻¹ •
        kreinConformalInversion55 (diracNullConeEmbed p) := by
  have hq_inv := Q55_minkowskiConformalInvert hq
  ext i
  fin_cases i
  · simp [diracNullConeEmbed, minkowskiConformalInvert, kreinConformalInversion55]
  · simp [diracNullConeEmbed, kreinConformalInversion55]
  · simp [diracNullConeEmbed, kreinConformalInversion55]
  · simp [diracNullConeEmbed, kreinConformalInversion55]
  · simp only [diracNullConeEmbed, kreinConformalInversion55, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, smul_eq_mul, Fin.reduceEq, ↓reduceIte, Fin.isValue]
    change (1 - InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice (minkowskiConformalInvert p))) / 2 =
        (InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p))⁻¹ *
          -((1 - InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p)) / 2)
    rw [hq_inv]
    field_simp [hq]
    ring
  · simp [diracNullConeEmbed, minkowskiConformalInvert, kreinConformalInversion55]
  · simp [diracNullConeEmbed, minkowskiConformalInvert, kreinConformalInversion55]
  · simp [diracNullConeEmbed, minkowskiConformalInvert, kreinConformalInversion55]
  · simp [diracNullConeEmbed, kreinConformalInversion55]
  · simp only [diracNullConeEmbed, kreinConformalInversion55, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, smul_eq_mul, Fin.reduceEq, ↓reduceIte, Fin.isValue]
    change (1 + InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice (minkowskiConformalInvert p))) / 2 =
        (InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p))⁻¹ *
          ((1 + InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p)) / 2)
    rw [hq_inv]
    field_simp [hq]
    ring

/-- Concrete `(5,5)` realization of `AeonConformalCrossover` connecting old and new Minkowski
aeon charts by conformal inversion on the Dirac null cone. -/
def minkowskiSO55AeonCrossover :
    AeonConformalCrossover Minkowski13 Minkowski13 (Fin 10 → ℝ) where
  inversion := so55MobiusInversionDatum
  oldCarrier := diracNullConeEmbed
  newCarrier := diracNullConeEmbed
  old_null := diracNullConeEmbed_mem_nullCone
  new_null := diracNullConeEmbed_mem_nullCone
  crossoverRel o n :=
    InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice o) ≠ 0 ∧ n = minkowskiConformalInvert o
  crossover_projective := by
    rintro o n ⟨hq, rfl⟩
    refine ⟨(InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice o))⁻¹, inv_ne_zero hq, ?_⟩
    exact diracNullConeEmbed_conformalInvert hq

/-- Nontrivial projective lightlike grammar measuring the transverse-to-time boost ratio `x₁ / t`,
invariant under both nonzero scalar rescaling and the conformal inversion `i = 4` flip. -/
def spatialRatioConformalGrammar :
    CrossoverLightlikeGrammar minkowskiSO55AeonCrossover ℝ where
  grammar v := if v 0 = 0 then 0 else v 5 / v 0
  projective := by
    intro c v hc
    dsimp [Pi.smul_apply, smul_eq_mul]
    by_cases hv : v 0 = 0
    · simp [hv]
    · have hcv : c * v 0 ≠ 0 := mul_ne_zero hc hv
      simp only [hv, hcv, ↓reduceIte]
      field_simp [hc, hv]
  inversion_invariant := by
    intro v _
    rfl

/-- Explicit non-unit-scale crossover witness: `p₀ = (2, ![1, 0, 0])` transforms from affine
interval `3` to `1/3`, while `spatialRatioConformalGrammar` stays strictly invariant at `1 / 2`. -/
theorem spatialRatioConformalGrammar_nontrivial_crossover_witness :
    let p₀ : Minkowski13 := (2, ![1, 0, 0])
    let p₁ : Minkowski13 := (2, ![0, 0, 0])
    InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p₀) = 3 ∧
      InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice (minkowskiConformalInvert p₀)) = 1 / 3 ∧
      spatialRatioConformalGrammar.grammar (diracNullConeEmbed (minkowskiConformalInvert p₀)) = 1 / 2 ∧
      spatialRatioConformalGrammar.grammar (diracNullConeEmbed p₀) = 1 / 2 ∧
      spatialRatioConformalGrammar.grammar (diracNullConeEmbed p₁) = 0 := by
  intro p₀ p₁
  have hq0 : InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p₀) = 3 := by
    rw [Q55_minkowskiSlice, Fin.sum_univ_three]
    norm_num [p₀]
  have hqinv :
      InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice (minkowskiConformalInvert p₀)) = 1 / 3 := by
    rw [Q55_minkowskiConformalInvert (by rw [hq0]; norm_num), hq0]
    norm_num
  have hgram0 : spatialRatioConformalGrammar.grammar (diracNullConeEmbed p₀) = 1 / 2 := by
    simp [spatialRatioConformalGrammar, diracNullConeEmbed, p₀]
  have hgram_cross :
      spatialRatioConformalGrammar.grammar (diracNullConeEmbed (minkowskiConformalInvert p₀)) = 1 / 2 := by
    change spatialRatioConformalGrammar.grammar
        (minkowskiSO55AeonCrossover.newCarrier (minkowskiConformalInvert p₀)) = 1 / 2
    rw [spatialRatioConformalGrammar.grammar_eq_on_crossover
      (o := p₀) (n := minkowskiConformalInvert p₀) ⟨by rw [hq0]; norm_num, rfl⟩]
    exact hgram0
  have hgram1 : spatialRatioConformalGrammar.grammar (diracNullConeEmbed p₁) = 0 := by
    simp [spatialRatioConformalGrammar, diracNullConeEmbed, p₁]
  exact ⟨hq0, hqinv, hgram_cross, hgram0, hgram1⟩

/-! ## 2. `FibonacciK0` Grothendieck Fusion Ring $\leftrightarrow$ Penrose Kite/Dart & `Cl(5,5)` Bott Colimit -/

/-- Additive homomorphism evaluating elements of the Grothendieck Fibonacci fusion ring `FibonacciK0`
at the noncommutative Penrose Kite operator `penroseKiteOp P A C` in an arbitrary associative ring `B`. -/
def evalFibonacciK0OnPenroseKite {B : Type*} [Ring B] (P A C : B) :
    FibonacciK0 →+ B where
  toFun x :=
    (fibonacciK0AddEquiv x).1 • (1 : B) + (fibonacciK0AddEquiv x).2 • penroseKiteOp P A C
  map_zero' := by
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero, zero_zsmul, add_zero]
  map_add' x y := by
    simp only [map_add, Prod.fst_add, Prod.snd_add, add_zsmul]
    abel

theorem evalFibonacciK0OnPenroseKite_one {B : Type*} [Ring B] (P A C : B) :
    evalFibonacciK0OnPenroseKite P A C fibOneK0 = 1 := by
  simp [evalFibonacciK0OnPenroseKite, fibonacciK0AddEquiv_apply, k0ToModel_one,
    FibonacciRingModel.one]

theorem evalFibonacciK0OnPenroseKite_tau {B : Type*} [Ring B] (P A C : B) :
    evalFibonacciK0OnPenroseKite P A C fibTauK0 = penroseKiteOp P A C := by
  simp [evalFibonacciK0OnPenroseKite, fibonacciK0AddEquiv_apply, k0ToModel_tau,
    FibonacciRingModel.tau]

/-- Multiplicative Penrose Kite quadratic identity `K^2 = K + V` from `P^2 = P`. -/
theorem penroseKiteOp_sq_eq_add_penroseDartOp {B : Type*} [Ring B]
    {P : B} (hP : P * P = P) (A C : B) :
    penroseKiteOp P A C * penroseKiteOp P A C =
      penroseKiteOp P A C + penroseDartOp P A C := by
  unfold penroseKiteOp penroseDartOp peirceTransfer
  peirce_nf hP

/-- When the Penrose Dart horizon equals `1` (`genV P A C = 1`), `evalFibonacciK0OnPenroseKite`
intertwines the Grothendieck fusion product `k0Mul` with noncommutative ring multiplication in `B`. -/
theorem evalFibonacciK0OnPenroseKite_k0Mul {B : Type*} [Ring B]
    {P A C : B} (hP : P * P = P) (hDart : penroseDartOp P A C = 1)
    (x y : FibonacciK0) :
    evalFibonacciK0OnPenroseKite P A C (k0Mul x y) =
      evalFibonacciK0OnPenroseKite P A C x * evalFibonacciK0OnPenroseKite P A C y := by
  have hK2 : penroseKiteOp P A C * penroseKiteOp P A C = penroseKiteOp P A C + 1 := by
    rw [penroseKiteOp_sq_eq_add_penroseDartOp hP A C, hDart]
  change (k0ToModel (k0Mul x y)).1 • (1 : B) +
      (k0ToModel (k0Mul x y)).2 • penroseKiteOp P A C =
    ((k0ToModel x).1 • (1 : B) + (k0ToModel x).2 • penroseKiteOp P A C) *
      ((k0ToModel y).1 • (1 : B) + (k0ToModel y).2 • penroseKiteOp P A C)
  rw [k0ToModel_k0Mul, FibonacciRingModel.mul_fst, FibonacciRingModel.mul_snd]
  set a₁ : ℤ := (k0ToModel x).1
  set b₁ : ℤ := (k0ToModel x).2
  set a₂ : ℤ := (k0ToModel y).1
  set b₂ : ℤ := (k0ToModel y).2
  set K : B := penroseKiteOp P A C
  calc
    (a₁ * a₂ + b₁ * b₂) • (1 : B) + (a₁ * b₂ + b₁ * a₂ + b₁ * b₂) • K
        = ((a₁ * a₂) • (1 : B) + (a₁ * b₂) • K + (b₁ * a₂) • K) + (b₁ * b₂) • (K + 1) := by
          simp only [add_zsmul, zsmul_add]
          abel
    _ = ((a₁ * a₂) • (1 : B) + (a₁ * b₂) • K + (b₁ * a₂) • K) + (b₁ * b₂) • (K * K) := by
          rw [← hK2]
    _ = (a₁ • (1 : B) + b₁ • K) * (a₂ • (1 : B) + b₂ • K) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
            one_mul, mul_one, smul_add, smul_smul]
          rw [mul_comm a₂ a₁, mul_comm a₂ b₁, mul_comm b₂ a₁, mul_comm b₂ b₁]
          abel

/-- Whenever the Penrose Dart horizon equals `1`, the operator sequence `polygonFibSeq P A C m`
reduces exactly to `(Nat.fib m : B)`. -/
theorem polygonFibSeq_eq_natCast_fib {B : Type*} [Ring B]
    {P A C : B} (hDart : penroseDartOp P A C = 1) :
    ∀ m : ℕ, polygonFibSeq P A C m = (Nat.fib m : B)
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
      have hV : genV P A C = 1 := hDart
      rw [polygonFibSeq_succ_succ, polygonFibSeq_eq_natCast_fib hDart (m + 1),
        polygonFibSeq_eq_natCast_fib hDart m, hV, one_mul, Nat.fib_add_two]
      push_cast
      abel

/-- Concrete noncommutative `2 × 2` matrix realization of unit-Dart Penrose Kite/Dart inflation
with `A * C ≠ C * A` (OpenGauss Trap T16 noncommutativity witness). -/
theorem concrete_matrix_penroseKite_unit_dart_witness :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    P * P = P ∧
      A * C ≠ C * A ∧
      penroseDartOp P A C = 1 ∧
      penroseKiteOp P A C = !![1, 1; 1, 0] ∧
      (∀ x y : FibonacciK0,
        evalFibonacciK0OnPenroseKite P A C (k0Mul x y) =
          evalFibonacciK0OnPenroseKite P A C x * evalFibonacciK0OnPenroseKite P A C y) ∧
      (∀ m : ℕ, (penroseKiteOp P A C) ^ (m + 1) =
        (Nat.fib (m + 1) : Matrix (Fin 2) (Fin 2) ℝ) * penroseKiteOp P A C +
          (Nat.fib m : Matrix (Fin 2) (Fin 2) ℝ)) := by
  intro P A C
  have hP : P * P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  have hAC : A * C ≠ C * A := by
    intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    simp [A, C, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hDart : penroseDartOp P A C = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [penroseDartOp, genV, anticomm, conePlus, coneMinus, P, A, C,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hKite : penroseKiteOp P A C = !![1, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [penroseKiteOp, peirceTransfer, genPhi, conePlus, coneMinus, P, A, C,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  refine ⟨hP, hAC, hDart, hKite, fun x y => evalFibonacciK0OnPenroseKite_k0Mul hP hDart x y, ?_⟩
  intro m
  have hInfl := (all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence hP A C m).1
  change (peirceTransfer P A C) ^ (m + 1) = _
  rw [hInfl, polygonFibSeq_eq_natCast_fib hDart (m + 1), polygonFibSeq_eq_natCast_fib hDart m,
    show genV P A C = 1 from hDart, one_mul]
  rfl

/-- Unifying colimit theorem lifting `FibonacciK0` Kite evaluation (under unit Dart horizon)
across the multi-period `Cl(5,5)` Bott tower `cl55ToBottStage k` into `Cl11TensorTowerLimit.Limit`. -/
theorem cl55_bott_penrose_fibonacciK0_colimit_bridge
    {ω : Cl55} (hω : ω * ω = ω) (k m : ℕ) (A_cl C_cl : Cl55) :
    let P_lim := ofStage 5 (cl55ToStage5 ω)
    let A_lim := ofStage 5 (cl55ToStage5 A_cl)
    let C_lim := ofStage 5 (cl55ToStage5 C_cl)
    (evalFibonacciK0OnPenroseKite P_lim A_lim C_lim fibTauK0 =
      ofStage (5 + 8 * k) (cl55ToBottStage k (penroseKiteOp ω A_cl C_cl))) ∧
    ((penroseKiteOp P_lim A_lim C_lim) ^ (m + 1) =
      polygonFibSeq P_lim A_lim C_lim (m + 1) * penroseKiteOp P_lim A_lim C_lim +
        penroseDartOp P_lim A_lim C_lim * polygonFibSeq P_lim A_lim C_lim m) ∧
    (penroseDartOp P_lim A_lim C_lim = 1 →
      ∀ x y : FibonacciK0,
        evalFibonacciK0OnPenroseKite P_lim A_lim C_lim (k0Mul x y) =
          evalFibonacciK0OnPenroseKite P_lim A_lim C_lim x *
            evalFibonacciK0OnPenroseKite P_lim A_lim C_lim y) := by
  intro P_lim A_lim C_lim
  have hP5 : cl55ToStage5 ω * cl55ToStage5 ω = cl55ToStage5 ω :=
    map_idempotent cl55ToStage5 hω
  have hPlim : P_lim * P_lim = P_lim :=
    map_idempotent (ofStage 5) hP5
  have hCoherent : ∀ y : Cl55,
      ofStage (5 + 8 * k) (cl55ToBottStage k y) = ofStage 5 (cl55ToStage5 y) := by
    intro y
    unfold cl55ToBottStage
    exact directLimitOf_bondMap stageBond 5 (5 + 8 * k) (Nat.le_add_right 5 (8 * k))
      (cl55ToStage5 y)
  have hKiteMap :
      ofStage (5 + 8 * k) (cl55ToBottStage k (penroseKiteOp ω A_cl C_cl)) =
        penroseKiteOp P_lim A_lim C_lim := by
    rw [hCoherent]
    unfold penroseKiteOp peirceTransfer
    rw [map_add, map_genPhi, map_add, map_genPhi]
  have hBott := cl55_multi_period_bott_intertwiner_of_idempotent hω k m 0 A_cl C_cl ω
  refine ⟨?_, ?_, ?_⟩
  · rw [evalFibonacciK0OnPenroseKite_tau, hKiteMap]
  · exact hBott.2.2.2.2.2.2
  · intro hDart x y
    exact evalFibonacciK0OnPenroseKite_k0Mul hPlim hDart x y

end InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge
