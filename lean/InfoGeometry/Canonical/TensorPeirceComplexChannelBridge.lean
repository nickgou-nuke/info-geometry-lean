/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorPeirceStateTransport
import InfoGeometry.Canonical.Cl11ComplexStageBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingOrthogonality

/-! # Complexification and the finite Peirce channel

The existing real tower embeds into the complex finite matrix algebras.
The embedding intertwines the actual Peirce map with its Kraus realization.
-/

noncomputable section
open scoped MatrixOrder ComplexOrder

namespace InfoGeometry.Canonical.TensorPeirceComplexChannelBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl11ComplexStageBridge
open InfoGeometry.Canonical.TensorPeirceStateTransport
open InfoGeometry.Canonical.TensorPeirceDensityWitness
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Examples.RealMatrixModeWitness
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingOrthogonality

/-- Complexification respects the involution on every full matrix stage. -/
theorem complexifyStage_star (n : ℕ) (A : Stage n) :
    complexifyStage n (star A) = star (complexifyStage n A) := by
  ext i j
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    complexifyStage_apply]

/-- Complexification sends a real positive semidefinite matrix to a complex
positive semidefinite matrix, using its finite Gram factorization. -/
theorem complexifyStage_posSemidef (n : ℕ) (A : Stage n) (hA : A.PosSemidef) :
    (complexifyStage n A).PosSemidef := by
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hY, map_mul, complexifyStage_star]
  exact Matrix.posSemidef_conjTranspose_mul_self (complexifyStage n Y)

/-- The existing complex Kraus map is the complexification of the real
Peirce projection, for the same full matrix input and cut. -/
theorem complexifyStage_pinching (n : ℕ) (P X : Stage n) (hPs : star P = P) :
    InfoGeometry.Quantum.Choi.krausMap (pinchingKraus (complexifyStage n P))
        (complexifyStage n X) = complexifyStage n (evenGrade P X) := by
  have hp : star (complexifyStage n P) = complexifyStage n P := by
    rw [← complexifyStage_star, hPs]
  rw [pinchingKraus_eq_even _ _ hp]
  simp only [evenGrade, map_add, map_mul, map_sub, map_one]

/-- Positivity, normalized trace, and the Kraus output are witnessed on
all complexified finite stages. The normalization is the tower's normalized
trace; the channel itself preserves ordinary matrix trace. -/
theorem complexified_pinching_state (n : ℕ) (P X : Stage n)
    (hP : P * P = P) (hPs : star P = P) (hX : X.PosSemidef)
    (htrace : normalizedTrace n X = 1) :
    (complexifyStage n X).PosSemidef ∧
    complexNormalizedTrace n (complexifyStage n X) = 1 ∧
    (InfoGeometry.Quantum.Choi.krausMap (pinchingKraus (complexifyStage n P))
      (complexifyStage n X)).PosSemidef ∧
    complexNormalizedTrace n
      (InfoGeometry.Quantum.Choi.krausMap (pinchingKraus (complexifyStage n P))
        (complexifyStage n X)) = 1 := by
  refine ⟨complexifyStage_posSemidef n X hX, ?_, ?_, ?_⟩
  · rw [complexNormalizedTrace_complexify, htrace, Complex.ofReal_one]
  · rw [complexifyStage_pinching n P X hPs]
    exact complexifyStage_posSemidef n _ (stage_pinching_posSemidef n P X hPs hX)
  · rw [complexifyStage_pinching n P X hPs, complexNormalizedTrace_complexify,
      stage_pinching_normalizedTrace n P X hP, htrace, Complex.ofReal_one]

/-- The complex matrix with ordinary trace normalization corresponding to a
real matrix normalized by the tower trace. -/
def quantumDensity (n : ℕ) (X : Stage n) : ComplexMatStage n :=
  complexifyStage n (((2 : ℝ) ^ n)⁻¹ • X)

/-- The actual finite complex density is positive and has ordinary trace one. -/
theorem quantumDensity_is_density (n : ℕ) (X : Stage n)
    (hX : X.PosSemidef) (htrace : normalizedTrace n X = 1) :
    (quantumDensity n X).PosSemidef ∧ Matrix.trace (quantumDensity n X) = 1 := by
  constructor
  · exact complexifyStage_posSemidef n _
      (hX.smul (inv_nonneg.mpr (pow_nonneg (by norm_num) n)))
  · have hcomplex : Matrix.trace (complexifyStage n X) = (2 : ℂ) ^ n := by
      have hn := complexNormalizedTrace_complexify n X
      rw [htrace, Complex.ofReal_one, complexNormalizedTrace_apply] at hn
      have hp : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      exact ((inv_mul_eq_one₀ hp).mp hn).symm
    have hscale : quantumDensity n X = ((2 : ℂ) ^ n)⁻¹ • complexifyStage n X := by
      ext i j
      simp [quantumDensity, complexifyStage_apply]
    rw [hscale, Matrix.trace_smul, hcomplex]
    exact inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))

/-- The trace-one density remains a trace-one density after the existing
completely positive trace-preserving pinching channel. -/
theorem quantumDensity_pinching (n : ℕ) (P X : Stage n)
    (hP : P * P = P) (hPs : star P = P) (hX : X.PosSemidef)
    (htrace : normalizedTrace n X = 1) :
    let Q := complexifyStage n P
    let ρ := quantumDensity n X
    (InfoGeometry.Quantum.Choi.krausMap (pinchingKraus Q) ρ).PosSemidef ∧
    Matrix.trace (InfoGeometry.Quantum.Choi.krausMap (pinchingKraus Q) ρ) = 1 := by
  dsimp only
  have hp : complexifyStage n P * complexifyStage n P = complexifyStage n P := by
    rw [← map_mul, hP]
  have hps : star (complexifyStage n P) = complexifyStage n P := by
    rw [← complexifyStage_star, hPs]
  obtain ⟨hρ, ht⟩ := quantumDensity_is_density n X hX htrace
  rw [pinchingKraus_eq_even _ _ hps]
  exact pinching_is_density _ _ hp hps hρ ht

/-- Entrywise complexification is injective on every full real matrix stage. -/
theorem complexifyStage_injective (n : ℕ) : Function.Injective (complexifyStage n) := by
  intro A B h
  ext i j
  apply Complex.ofReal_injective
  exact congrArg (fun M : ComplexMatStage n => M i j) h

/-- Trace normalization and complexification preserve noncommutation. -/
theorem quantumDensity_not_commute (n : ℕ) (P X : Stage n)
    (h : ¬ Commute P X) : ¬ Commute (complexifyStage n P) (quantumDensity n X) := by
  intro hc
  apply h
  have hm : P * (((2 : ℝ) ^ n)⁻¹ • X) = (((2 : ℝ) ^ n)⁻¹ • X) * P := by
    apply complexifyStage_injective n
    simpa only [map_mul, quantumDensity] using hc.eq
  simp only [mul_smul_comm, smul_mul_assoc] at hm
  have ht := congrArg (fun A : Stage n => ((2 : ℝ) ^ n) • A) hm
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  change P * X = X * P
  simpa [smul_smul, hp] using ht

/-- At every refinement the trace-one complex density remains genuinely
noncommuting with the represented Peirce cut. -/
theorem dense_quantumDensity_noncommuting (m : ℕ) (h : 2 ≤ m) :
    ¬ Commute (complexifyStage m (bondMap stageBond 2 m h p))
      (quantumDensity m (bondMap stageBond 2 m h denseDensity)) := by
  apply quantumDensity_not_commute
  intro hc
  have hleft : ofStage m (bondMap stageBond 2 m h p) = ofStage 2 p :=
    directLimitOf_bondMap stageBond 2 m h p
  have hright : ofStage m (bondMap stageBond 2 m h denseDensity) = ofStage 2 denseDensity :=
    directLimitOf_bondMap stageBond 2 m h denseDensity
  have hcol : Commute (ofStage 2 p) (ofStage 2 denseDensity) := by
    change ofStage 2 p * ofStage 2 denseDensity = ofStage 2 denseDensity * ofStage 2 p
    simpa only [map_mul, hleft, hright] using congrArg (ofStage m) hc.eq
  exact denseDensity_colimit_strict_trace_loss.2.2.1 hcol

/-- At every stage, the actual complex Kraus output has strictly smaller
quadratic trace than the noncommuting trace-one input. -/
theorem dense_quantumDensity_strict_purity_loss (m : ℕ) (h : 2 ≤ m) :
    let Q := complexifyStage m (bondMap stageBond 2 m h p)
    let ρ := quantumDensity m (bondMap stageBond 2 m h denseDensity)
    let Φρ := InfoGeometry.Quantum.Choi.krausMap (pinchingKraus Q) ρ
    (Matrix.trace (Φρ * Φρ)).re < (Matrix.trace (ρ * ρ)).re := by
  dsimp only
  let P := bondMap stageBond 2 m h p
  let X := bondMap stageBond 2 m h denseDensity
  let Q := complexifyStage m P
  let ρ := quantumDensity m X
  have hp : Q * Q = Q := by
    dsimp [Q, P]
    rw [← map_mul, ← map_mul, p_isIdempotentElem.eq]
  have hps : star Q = Q := by
    dsimp [Q, P]
    rw [← complexifyStage_star, ← bondMap_star, p_isSelfAdjoint.star_eq]
  have hstate := denseDensity_all_refinements m h
  have hρ : ρ.PosSemidef ∧ Matrix.trace ρ = 1 :=
    quantumDensity_is_density m X hstate.1 hstate.2.1
  have hn : ¬ Commute Q ρ := dense_quantumDensity_noncommuting m h
  have hpur := pinching_density_purity Q ρ hp hps hρ.1 hρ.2
  have hneq : evenGrade Q ρ ≠ ρ := by
    intro he
    apply hn
    change Q * ρ = ρ * Q
    rw [← he]
    unfold evenGrade
    peirce_nf hp
  have hlt : (Matrix.trace (evenGrade Q ρ * evenGrade Q ρ)).re <
      (Matrix.trace (ρ * ρ)).re := lt_of_le_of_ne hpur.2.2.1 (by
        intro heq
        exact hneq (hpur.2.2.2.mp heq))
  change (Matrix.trace
    (InfoGeometry.Quantum.Choi.krausMap (pinchingKraus Q) ρ *
      InfoGeometry.Quantum.Choi.krausMap (pinchingKraus Q) ρ)).re < _
  rw [pinchingKraus_eq_even Q ρ hps]
  exact hlt

/-- At every finite refinement the channel output is the unique closest
Peirce-even density in squared Hilbert--Schmidt distance. -/
theorem dense_quantumDensity_unique_best_even (m : ℕ) (h : 2 ≤ m) :
    let Q := complexifyStage m (bondMap stageBond 2 m h p)
    let ρ := quantumDensity m (bondMap stageBond 2 m h denseDensity)
    ∀ σ : ComplexMatStage m, σ.PosSemidef → Matrix.trace σ = 1 → evenGrade Q σ = σ →
      InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq
          (ρ - evenGrade Q ρ) ≤
        InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq (ρ - σ) ∧
      (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq
          (ρ - evenGrade Q ρ) =
        InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq (ρ - σ) ↔
          σ = evenGrade Q ρ) := by
  dsimp only
  let P := bondMap stageBond 2 m h p
  let X := bondMap stageBond 2 m h denseDensity
  let Q := complexifyStage m P
  have hp : Q * Q = Q := by
    dsimp [Q, P]
    rw [← map_mul, ← map_mul, p_isIdempotentElem.eq]
  have hps : star Q = Q := by
    dsimp [Q, P]
    rw [← complexifyStage_star, ← bondMap_star, p_isSelfAdjoint.star_eq]
  have hs := denseDensity_all_refinements m h
  have hρ := quantumDensity_is_density m X hs.1 hs.2.1
  exact (pinching_density_unique_best_approximation Q (quantumDensity m X)
    hp hps hρ.1 hρ.2).2.2

end InfoGeometry.Canonical.TensorPeirceComplexChannelBridge

end
