/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorColimitCurvatureEnergy
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-! # Peirce coherence energy on the tensor colimit

The faithful normalized trace measures the noncommuting Peirce component
on the actual algebraic colimit. The energy is represented exactly at every
finite matrix stage and is invariant under the tower's bonding maps.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorPeirceTraceLoss

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.Canonical.TensorExactCurvatureTrace
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Examples.RealMatrixModeWitness

/-- The squared norm of the off-diagonal component is the squared norm of
the commutator, as an identity in every involutive ring. -/
theorem peirce_residual_gram {B : Type*} [Ring B] [StarRing B]
    (P X : B) (hP : P * P = P) (hPs : star P = P) :
    star (X - evenGrade P X) * (X - evenGrade P X) =
      star (comm P X) * comm P X := by
  unfold evenGrade InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  simp only [star_sub, star_add, star_mul, star_one, hPs]
  peirce_nf hP

/-- Faithful quadratic readout of the actual cut commutator. -/
def coherenceEnergy (P X : Limit) : ℝ :=
  normalizedTraceLimit (star (comm P X) * comm P X)

/-- The same readout on a finite full matrix stage. -/
def stageCoherenceEnergy (n : ℕ) (P X : Stage n) : ℝ :=
  normalizedTrace n (star (comm P X) * comm P X)

theorem coherenceEnergy_eq_residual (P X : Limit) (hP : P * P = P)
    (hPs : star P = P) :
    coherenceEnergy P X = normalizedTraceLimit
      (star (X - evenGrade P X) * (X - evenGrade P X)) := by
  unfold coherenceEnergy
  rw [peirce_residual_gram P X hP hPs]

theorem coherenceEnergy_nonneg_and_faithful (P X : Limit) :
    0 ≤ coherenceEnergy P X ∧ (coherenceEnergy P X = 0 ↔ Commute P X) := by
  constructor
  · exact normalizedTraceLimit_star_mul_self_nonneg _
  · rw [coherenceEnergy, normalizedTraceLimit_star_mul_self_eq_zero_iff]
    change P * X - X * P = 0 ↔ P * X = X * P
    exact sub_eq_zero

/-- Cyclicity kills both off-diagonal Peirce corners on the colimit. -/
theorem normalizedTraceLimit_oddGrade (P X : Limit) (hP : P * P = P) :
    normalizedTraceLimit (oddGrade P X) = 0 := by
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have h₁ : normalizedTraceLimit (P * X * (1 - P)) = 0 := by
    rw [normalizedTraceLimit_cyclic (P * X) (1 - P), ← mul_assoc, hQP, zero_mul, map_zero]
  have h₂ : normalizedTraceLimit ((1 - P) * X * P) = 0 := by
    rw [normalizedTraceLimit_cyclic ((1 - P) * X) P, ← mul_assoc, hPQ, zero_mul, map_zero]
  simp only [oddGrade, map_add, h₁, h₂, add_zero]

/-- For a self-adjoint colimit element the loss of quadratic trace under
Peirce pinching is exactly the faithful commutator energy. -/
theorem normalizedTraceLimit_pinching_defect (P X : Limit) (hP : P * P = P)
    (hPs : star P = P) (hX : star X = X) :
    normalizedTraceLimit (X * X) =
      normalizedTraceLimit (evenGrade P X * evenGrade P X) + coherenceEnergy P X := by
  let E := evenGrade P X
  let R := X - E
  have hERodd : E * R = oddGrade P (E * R) := by
    dsimp [E, R]
    unfold evenGrade oddGrade
    peirce_nf hP
  have hER : normalizedTraceLimit (E * R) = 0 := by
    rw [hERodd]
    exact normalizedTraceLimit_oddGrade P (E * R) hP
  have hRE : normalizedTraceLimit (R * E) = 0 := by
    rw [normalizedTraceLimit_cyclic R E, hER]
  have hRstar : star R = R := by
    dsimp [R, E]
    simp only [star_sub, evenGrade, star_add, star_mul, star_one, hPs, hX, mul_assoc]
  have hsplit : X = E + R := by dsimp [R]; abel
  have hexp : normalizedTraceLimit (X * X) =
      normalizedTraceLimit (E * E) + normalizedTraceLimit (R * R) := by
    conv_lhs => rw [hsplit]
    simp only [add_mul, mul_add, map_add, hER, hRE, add_zero, zero_add]
  have henergy : coherenceEnergy P X = normalizedTraceLimit (R * R) := by
    rw [coherenceEnergy_eq_residual P X hP hPs]
    change normalizedTraceLimit (star R * R) = normalizedTraceLimit (R * R)
    rw [hRstar]
  exact hexp.trans (by rw [henergy])

/-- For self-adjoint colimit elements, the quadratic trace is preserved
exactly when the element commutes with the cut. -/
theorem normalizedTraceLimit_pinching_eq_iff_commute (P X : Limit)
    (hP : P * P = P) (hPs : star P = P) (hX : star X = X) :
    normalizedTraceLimit (X * X) = normalizedTraceLimit (evenGrade P X * evenGrade P X) ↔
      Commute P X := by
  have hdefect := normalizedTraceLimit_pinching_defect P X hP hPs hX
  have hfaith := (coherenceEnergy_nonneg_and_faithful P X).2
  constructor
  · intro heq
    apply hfaith.mp
    linarith
  · intro hc
    rw [hfaith.mpr hc, add_zero] at hdefect
    exact hdefect

/-- No limiting procedure is invoked: the colimit trace reduces exactly to
the normalized trace of the representing finite matrix. -/
theorem coherenceEnergy_ofStage (n : ℕ) (P X : Stage n) :
    coherenceEnergy (ofStage n P) (ofStage n X) = stageCoherenceEnergy n P X := by
  unfold coherenceEnergy stageCoherenceEnergy
  have hc : comm (ofStage n P) (ofStage n X) = ofStage n (comm P X) := by
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, map_sub, map_mul]
  rw [hc, ← ofStage_star, ← map_mul]
  rfl

theorem stageCoherenceEnergy_bondMap {n m : ℕ} (h : n ≤ m) (P X : Stage n) :
    stageCoherenceEnergy m (bondMap stageBond n m h P) (bondMap stageBond n m h X) =
      stageCoherenceEnergy n P X := by
  rw [← coherenceEnergy_ofStage, ← coherenceEnergy_ofStage]
  congr 1
  · exact directLimitOf_bondMap stageBond n m h P
  · exact directLimitOf_bondMap stageBond n m h X

/-- A full dense matrix mode gives a strictly positive noncommutative value. -/
theorem dense_coherenceEnergy_pos : 0 < coherenceEnergy (ofStage 2 p) (ofStage 2 x) := by
  apply lt_of_le_of_ne (coherenceEnergy_nonneg_and_faithful _ _).1
  intro hz
  have hc := (coherenceEnergy_nonneg_and_faithful (ofStage 2 p) (ofStage 2 x)).2.mp hz.symm
  have he : ofStage 2 x = 0 := by
    have h := hc.eq
    rw [← map_mul, ← map_mul, p_mul_x, x_mul_p, map_zero] at h
    exact h
  have hx : x = 0 := (ofStage_eq_zero_iff 2 x).mp he
  exact x_entry_ne_zero (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0) (by rw [hx]; rfl)

/-- The self-adjoint sum of the dense mode and its adjoint still does not
commute with the dense projection. -/
theorem dense_hermitian_mode_not_commute : ¬ Commute p (x + star x) := by
  have hpstar : star p = p := p_isSelfAdjoint.star_eq
  have hpxs : p * star x = 0 := by
    have h := congrArg star x_mul_p
    simpa only [star_mul, hpstar, star_zero] using h
  have hxsp : star x * p = star x := by
    have h := congrArg star p_mul_x
    simpa only [star_mul, hpstar] using h
  intro hc
  have h := hc.eq
  rw [mul_add, add_mul, p_mul_x, hpxs, x_mul_p, hxsp, add_zero, zero_add] at h
  have he := congrArg (fun A : Stage 2 => A (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 1)) h
  norm_num [x, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.transpose_apply] at he
  change (-(1 / 4) : ℝ) = (1 / 4 : ℝ) at he
  norm_num at he

/-- The exact quadratic trace loss is strictly positive for the represented
self-adjoint dense mode on the actual colimit. -/
theorem dense_hermitian_strict_trace_loss :
    normalizedTraceLimit
        (evenGrade (ofStage 2 p) (ofStage 2 (x + star x)) *
          evenGrade (ofStage 2 p) (ofStage 2 (x + star x))) <
      normalizedTraceLimit (ofStage 2 (x + star x) * ofStage 2 (x + star x)) := by
  have hp : ofStage 2 p * ofStage 2 p = ofStage 2 p := by
    rw [← map_mul, p_isIdempotentElem.eq]
  have hps : star (ofStage 2 p) = ofStage 2 p := by
    rw [← ofStage_star, p_isSelfAdjoint.star_eq]
  have hxs : star (ofStage 2 (x + star x)) = ofStage 2 (x + star x) := by
    rw [← ofStage_star, star_add, star_star, add_comm]
  have hnc : ¬ Commute (ofStage 2 p) (ofStage 2 (x + star x)) := by
    intro hc
    apply dense_hermitian_mode_not_commute
    apply (ofStage_injective 2)
    simpa only [map_mul] using hc.eq
  have hdefect := normalizedTraceLimit_pinching_defect (ofStage 2 p)
    (ofStage 2 (x + star x)) hp hps hxs
  have hpositive : 0 < coherenceEnergy (ofStage 2 p) (ofStage 2 (x + star x)) := by
    apply lt_of_le_of_ne (coherenceEnergy_nonneg_and_faithful _ _).1
    intro hz
    exact hnc ((coherenceEnergy_nonneg_and_faithful _ _).2.mp hz.symm)
  linarith

/-- Every refinement of the dense witness retains exactly the same strictly
positive finite-matrix coherence energy. -/
theorem dense_stage_coherenceEnergy_pos (m : ℕ) (h : 2 ≤ m) :
    0 < stageCoherenceEnergy m (bondMap stageBond 2 m h p) (bondMap stageBond 2 m h x) := by
  rw [stageCoherenceEnergy_bondMap, ← coherenceEnergy_ofStage]
  exact dense_coherenceEnergy_pos

end InfoGeometry.Canonical.TensorPeirceTraceLoss

end
