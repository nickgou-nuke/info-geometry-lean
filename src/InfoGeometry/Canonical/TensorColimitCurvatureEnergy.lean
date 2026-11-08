/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorExactCurvatureTrace

/-!
# Finite-frame curvature energy on the algebraic tensor colimit

A finite family of real-linear Leibniz directions determines a positive
quadratic trace functional of the actual CE curvature. Its zero set and
unitary gauge invariance follow from faithfulness and cyclicity of the
existing normalized colimit trace. No topology on the colimit is imposed.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorColimitCurvatureEnergy

open scoped BigOperators
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.TensorStageExactConnection
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorExactCurvatureTrace
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Examples.RealMatrixModeWitness
open InfoGeometry.Canonical.TensorExactCurvatureNonzero
open InfoGeometry.Canonical.RealStarColimitUniversal

variable {ι : Type*} [Fintype ι]

/-- Squared curvature readout over a finite family of Leibniz directions. -/
def curvatureEnergy (frame : ι → limitDerivationsLane.L)
    (Γ : OneForm limitDerivationsLane) : ℝ :=
  ∑ i, ∑ j,
    normalizedTraceLimit
      (star (connectionCurvature limitDerivationsLane Γ (frame i) (frame j)) *
        connectionCurvature limitDerivationsLane Γ (frame i) (frame j))

/-- The finite matrix-stage counterpart, evaluated on inner directions. -/
def stageCurvatureEnergy (n : ℕ) (P : Stage n) (frame : ι → Stage n) : ℝ :=
  ∑ i, ∑ j, normalizedTrace n
    (star (exactCutCurvature n P (frame i) (frame j)) *
      exactCutCurvature n P (frame i) (frame j))

/-- The colimit readout is exactly the normalized full-matrix stage readout. -/
theorem curvatureEnergy_ofStage (n : ℕ) (P : Stage n) (frame : ι → Stage n) :
    curvatureEnergy (fun i => limitInnerLieHom (ofStage n (frame i)))
      (exteriorDerivativeZero limitDerivationsLane (ofStage n P)) =
      stageCurvatureEnergy n P frame := by
  unfold curvatureEnergy stageCurvatureEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change normalizedTraceLimit
    (star (limitExactCurvature (ofStage n P) (ofStage n (frame i)) (ofStage n (frame j))) *
      limitExactCurvature (ofStage n P) (ofStage n (frame i)) (ofStage n (frame j))) = _
  rw [← ofStage_exactCurvature, ← ofStage_star, ← map_mul]
  rfl

/-- Refinement does not change the finite curvature energy. -/
theorem stageCurvatureEnergy_bondMap {n m : ℕ} (h : n ≤ m)
    (P : Stage n) (frame : ι → Stage n) :
    stageCurvatureEnergy m (bondMap stageBond n m h P)
        (fun i => bondMap stageBond n m h (frame i)) = stageCurvatureEnergy n P frame := by
  rw [← curvatureEnergy_ofStage, ← curvatureEnergy_ofStage]
  congr 1
  · funext i
    congr 1
    exact directLimitOf_bondMap stageBond n m h (frame i)
  · congr 1
    exact directLimitOf_bondMap stageBond n m h P

/-- Every term is a genuine adjoint square, so the energy is nonnegative. -/
theorem curvatureEnergy_nonneg (frame : ι → limitDerivationsLane.L)
    (Γ : OneForm limitDerivationsLane) : 0 ≤ curvatureEnergy frame Γ := by
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg fun j _ => normalizedTraceLimit_star_mul_self_nonneg _

/-- Faithfulness detects all curvature components tested by the family. -/
theorem curvatureEnergy_eq_zero_iff (frame : ι → limitDerivationsLane.L)
    (Γ : OneForm limitDerivationsLane) :
    curvatureEnergy frame Γ = 0 ↔
      ∀ i j, connectionCurvature limitDerivationsLane Γ (frame i) (frame j) = 0 := by
  unfold curvatureEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => normalizedTraceLimit_star_mul_self_nonneg _))]
  simp only [Finset.mem_univ, forall_const]
  simp_rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => normalizedTraceLimit_star_mul_self_nonneg _)]
  simp only [Finset.mem_univ, forall_const, normalizedTraceLimit_star_mul_self_eq_zero_iff]

/-- The full-matrix stage energy is nonnegative. -/
theorem stageCurvatureEnergy_nonneg (n : ℕ) (P : Stage n) (frame : ι → Stage n) :
    0 ≤ stageCurvatureEnergy n P frame := by
  rw [← curvatureEnergy_ofStage]
  exact curvatureEnergy_nonneg _ _

/-- The finite-stage energy detects precisely the curvature components of
its chosen matrix directions. -/
theorem stageCurvatureEnergy_eq_zero_iff (n : ℕ) (P : Stage n) (frame : ι → Stage n) :
    stageCurvatureEnergy n P frame = 0 ↔
      ∀ i j, exactCutCurvature n P (frame i) (frame j) = 0 := by
  rw [← curvatureEnergy_ofStage, curvatureEnergy_eq_zero_iff]
  change (∀ i j, limitExactCurvature (ofStage n P) (ofStage n (frame i))
    (ofStage n (frame j)) = 0) ↔ _
  simp only [← ofStage_exactCurvature, ofStage_eq_zero_iff]

/-- Positive colimit energy is equivalent to a genuinely nonzero curvature
component among the selected Leibniz directions. -/
theorem curvatureEnergy_pos_iff (frame : ι → limitDerivationsLane.L)
    (Γ : OneForm limitDerivationsLane) :
    0 < curvatureEnergy frame Γ ↔
      ∃ i j, connectionCurvature limitDerivationsLane Γ (frame i) (frame j) ≠ 0 := by
  classical
  constructor
  · intro hp
    by_contra h
    push Not at h
    exact (ne_of_gt hp) ((curvatureEnergy_eq_zero_iff frame Γ).2 h)
  · rintro ⟨i, j, h⟩
    apply lt_of_le_of_ne (curvatureEnergy_nonneg frame Γ)
    intro hz
    exact h ((curvatureEnergy_eq_zero_iff frame Γ).1 hz.symm i j)

/-- The analogous criterion holds on each full noncommutative matrix stage. -/
theorem stageCurvatureEnergy_pos_iff (n : ℕ) (P : Stage n) (frame : ι → Stage n) :
    0 < stageCurvatureEnergy n P frame ↔
      ∃ i j, exactCutCurvature n P (frame i) (frame j) ≠ 0 := by
  classical
  constructor
  · intro hp
    by_contra h
    push Not at h
    exact (ne_of_gt hp) ((stageCurvatureEnergy_eq_zero_iff n P frame).2 h)
  · rintro ⟨i, j, h⟩
    apply lt_of_le_of_ne (stageCurvatureEnergy_nonneg n P frame)
    intro hz
    exact h ((stageCurvatureEnergy_eq_zero_iff n P frame).1 hz.symm i j)

/-- Unitary changes of gauge preserve the full finite-frame energy. -/
theorem curvatureEnergy_gauge (frame : ι → limitDerivationsLane.L)
    (Γ : OneForm limitDerivationsLane) (u : unitary Limit) :
    curvatureEnergy frame (gaugeOneForm limitDerivationsLane Γ (Unitary.toUnits u)) =
      curvatureEnergy frame Γ := by
  unfold curvatureEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact normalizedTraceLimit_gauge_curvature_square Γ u (frame i) (frame j)

/-- The existing dense noncommutative mode supplies an actual finite family
with strictly positive energy for an exact colimit connection. -/
theorem exists_positive_exactCurvatureEnergy :
    ∃ frame : Fin 2 → limitDerivationsLane.L,
      0 < curvatureEnergy frame
        (exteriorDerivativeZero limitDerivationsLane (ofStage 2 p)) := by
  let frame : Fin 2 → limitDerivationsLane.L :=
    ![limitInnerLieHom (ofStage 2 x), limitInnerLieHom (ofStage 2 (star x))]
  refine ⟨frame, lt_of_le_of_ne (curvatureEnergy_nonneg frame _) ?_⟩
  intro hz
  have hF := (curvatureEnergy_eq_zero_iff frame _).mp hz.symm 0 1
  apply denseMode_limitExactCurvature_ne_zero
  simpa [frame, limitExactCurvature] using hF

/-- The dense stage-two frame has strictly positive normalized curvature
energy, and every subsequent tensor refinement has the same positive value. -/
theorem denseMode_stageCurvatureEnergy_positive (m : ℕ) (h : 2 ≤ m) :
    0 < stageCurvatureEnergy m (bondMap stageBond 2 m h p)
      (fun i : Fin 2 => bondMap stageBond 2 m h (![x, star x] i)) := by
  rw [stageCurvatureEnergy_bondMap, ← curvatureEnergy_ofStage]
  let frame : Fin 2 → limitDerivationsLane.L :=
    fun i => limitInnerLieHom (ofStage 2 (![x, star x] i))
  change 0 < curvatureEnergy frame
    (exteriorDerivativeZero limitDerivationsLane (ofStage 2 p))
  refine lt_of_le_of_ne (curvatureEnergy_nonneg frame _) ?_
  intro hz
  have hF := (curvatureEnergy_eq_zero_iff frame _).mp hz.symm 0 1
  apply denseMode_limitExactCurvature_ne_zero
  simpa [frame, limitExactCurvature] using hF

end InfoGeometry.Canonical.TensorColimitCurvatureEnergy

end
