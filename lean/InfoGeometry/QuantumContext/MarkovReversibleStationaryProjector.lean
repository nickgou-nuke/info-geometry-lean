/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Canonical.DrazinCommutant
import InfoGeometry.QuantumContext.MarkovGroupInverseStationaryReadout
import InfoGeometry.QuantumContext.MarkovMetriplecticReversibleRotation
import InfoGeometry.QuantumContext.MarkovMetriplecticGroupInverseLift

/-!
# Reversible actions on the stationary sector of a Markov operator

This module connects the stationary projector of a strictly positive finite
Markov transition to weighted-skew matrix actions on the full matrix carrier.
The compatibility equation with the transition is an explicit hypothesis;
no such equation is inferred for a Clifford or Majorana generator.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Canonical.DrazinCommutant
open InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weighted-skew matrix commuting with a strictly positive Markov
transition annihilates the constant observable. -/
theorem weightedSkew_mulVec_one_eq_zero
    [Nonempty ι]
    (P A : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hA : ∀ i j, π i * A i j = -(π j * A j i))
    (hcomm : A * P = P * A) :
    A.mulVec (fun _ => (1 : ℝ)) = 0 := by
  let one : ι → ℝ := fun _ => 1
  have hPone : P.mulVec one = one := (Matrix.mem_rowStochastic.mp hP).2
  have hmul := congrArg (fun M : Matrix ι ι ℝ => M.mulVec one) hcomm
  rw [← Matrix.mulVec_mulVec] at hmul
  rw [hPone] at hmul
  rw [← Matrix.mulVec_mulVec] at hmul
  have hfixed : P.mulVec (A.mulVec one) = A.mulVec one := by
    exact hmul.symm
  obtain ⟨c, hc⟩ :=
    (positive_rowStochastic_mulVec_fixed_iff_const P hP hPpos
      (A.mulVec one)).mp hfixed
  have hpair := weightedMarkovPairing_leftAction_skew π A hA one one
  have hpair_comm : weightedMarkovPairing π one (A.mulVec one) =
      weightedMarkovPairing π (A.mulVec one) one := by
    unfold weightedMarkovPairing
    apply Finset.sum_congr rfl
    intro i hi
    simp [one]
  rw [hpair_comm] at hpair
  have hmean : weightedMarkovPairing π one (A.mulVec one) = c := by
    simp only [weightedMarkovPairing]
    simp_rw [hc]
    simp only [one, mul_one]
    change (∑ i, π i * c) = c
    calc
      (∑ i, π i * c) = (∑ i, π i) * c := (Finset.sum_mul ..).symm
      _ = c := by simp [hπsum]
  rw [← hpair_comm, hmean] at hpair
  have hc_zero : c = 0 := by linarith
  funext i
  rw [hc i, hc_zero]
  simp

omit [DecidableEq ι] in
/-- Weighted-skewness and annihilation of constants force every output to
have zero stationary weighted mean. -/
theorem weightedMeanMap_mulVec_eq_zero_of_weightedSkew
    (A : Matrix ι ι ℝ) (π : ι → ℝ)
    (hA : ∀ i j, π i * A i j = -(π j * A j i))
    (hone : A.mulVec (fun _ => (1 : ℝ)) = 0)
    (x : ι → ℝ) :
    weightedMeanMap π (A.mulVec x) = 0 := by
  have hskew := weightedMarkovPairing_leftAction_skew π A hA
    (fun _ => 1) x
  rw [hone] at hskew
  simpa [weightedMeanMap, weightedMarkovPairing] using hskew

/-- On the full matrix carrier, a weighted-skew action commuting with a
strictly positive Markov transition annihilates the group-inverse stationary
projector in both composition orders. -/
theorem weightedSkew_leftAction_annihilates_stationaryProjector
    [Nonempty ι]
    (P A G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (hA : ∀ i j, π i * A i j = -(π j * A j i))
    (hcomm : A * P = P * A)
    (hG : IsGroupInverse (1 - P) G) :
    mulLeftLinearMap ι ℝ A *
        mulLeftLinearMap ι ℝ (markovStationaryProjector P G) = 0 ∧
      mulLeftLinearMap ι ℝ (markovStationaryProjector P G) *
        mulLeftLinearMap ι ℝ A = 0 := by
  let one : ι → ℝ := fun _ => 1
  let F : Matrix ι ι ℝ := markovStationaryProjector P G
  have hone : A.mulVec one = 0 :=
    weightedSkew_mulVec_one_eq_zero P A π hP hPpos hπsum hA hcomm
  have hAF : A * stationaryMeanMatrix π = 0 := by
    ext i j
    simp only [Matrix.mul_apply, stationaryMeanMatrix]
    calc
      (∑ k, A i k * π j) = (∑ k, A i k) * π j :=
        (Finset.sum_mul ..).symm
      _ = (A.mulVec one) i * π j := by
        simp [Matrix.mulVec, dotProduct, one]
      _ = 0 := by rw [hone]; simp
  have hFA : stationaryMeanMatrix π * A = 0 := by
    ext i j
    simp only [Matrix.mul_apply, stationaryMeanMatrix]
    calc
      (∑ k, π k * A k j) = -π j * (∑ k, A j k) := by
        calc
          (∑ k, π k * A k j) = ∑ k, -(π j * A j k) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hA k j
          _ = -(π j * (∑ k, A j k)) := by
            calc
              (∑ k, -(π j * A j k)) = -(∑ k, π j * A j k) := by
                rw [Finset.sum_neg_distrib]
              _ = -(π j * (∑ k, A j k)) := by rw [Finset.mul_sum]
          _ = -π j * (∑ k, A j k) := by ring
      _ = 0 := by
        have hj : (A.mulVec one) j = 0 := congrFun hone j
        have hrow : (∑ k, A j k) = 0 := by
          simpa [Matrix.mulVec, dotProduct, one] using hj
        rw [hrow]
        ring
  have hF : F = stationaryMeanMatrix π :=
    markovStationaryProjector_eq_stationaryMeanMatrix
      P π hP hPpos hπsum hstat G hG
  constructor
  · change mulLeftLinearMap ι ℝ A * mulLeftLinearMap ι ℝ F = 0
    rw [hF]
    have h := congrArg (fun M : Matrix ι ι ℝ => mulLeftLinearMap ι ℝ M) hAF
    simpa [mulLeftLinearMap_mul, Module.End.mul_eq_comp] using h
  · change mulLeftLinearMap ι ℝ F * mulLeftLinearMap ι ℝ A = 0
    rw [hF]
    have h := congrArg (fun M : Matrix ι ι ℝ => mulLeftLinearMap ι ℝ M) hFA
    simpa [mulLeftLinearMap_mul, Module.End.mul_eq_comp] using h

/-- The same compatibility forces the reversible left action to commute
with the lifted group inverse on the full matrix module. -/
theorem leftAction_commutes_markovGroupInverse
    (P A G : Matrix ι ι ℝ)
    (hcomm : A * P = P * A)
    (hG : IsGroupInverse (1 - P) G) :
    mulLeftLinearMap ι ℝ A * mulLeftLinearMap ι ℝ G =
      mulLeftLinearMap ι ℝ G * mulLeftLinearMap ι ℝ A := by
  have hAL : A * (1 - P) = (1 - P) * A := by
    calc
      A * (1 - P) = A - A * P := by noncomm_ring
      _ = A - P * A := by rw [hcomm]
      _ = (1 - P) * A := by noncomm_ring
  have hGA : G * A = A * G :=
    inverse_commutes_of_commutes hG.toDrazin A hAL.symm
  simpa [mulLeftLinearMap_mul, Module.End.mul_eq_comp] using
    (congrArg (fun X : Matrix ι ι ℝ => mulLeftLinearMap ι ℝ X) hGA).symm

/-! ### A concrete noncommutative Fin 3 witness -/

/-- A strictly positive, non-diagonal Markov transition on three states. -/
def uniformPositiveTransition : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(2 : ℝ) / 3, 1 / 6, 1 / 6;
     1 / 6, 2 / 3, 1 / 6;
     1 / 6, 1 / 6, 2 / 3]

/-- The cyclic skew action on the three-state fluctuation plane. -/
def cyclicSkewAction : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, -1;
     -1, 0, 1;
     1, -1, 0]

/-- The normalized uniform stationary row weight. -/
def uniformStationaryWeight : Fin 3 → ℝ := fun _ => 1 / 3

theorem uniformPositiveTransition_rowStochastic :
    uniformPositiveTransition ∈ Matrix.rowStochastic ℝ (Fin 3) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [uniformPositiveTransition]
  · intro i
    fin_cases i <;>
      norm_num [uniformPositiveTransition, Fin.sum_univ_succ]

theorem uniformPositiveTransition_entrywise_positive (i j : Fin 3) :
    0 < uniformPositiveTransition i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [uniformPositiveTransition]

theorem uniformStationaryWeight_normalized :
    ∑ i : Fin 3, uniformStationaryWeight i = 1 := by
  norm_num [uniformStationaryWeight, Fin.sum_univ_succ]

theorem uniformStationaryWeight_stationary :
    ∀ j : Fin 3, ∑ i : Fin 3,
      uniformStationaryWeight i * uniformPositiveTransition i j =
        uniformStationaryWeight j := by
  intro j
  fin_cases j <;>
    norm_num [uniformStationaryWeight, uniformPositiveTransition,
      Fin.sum_univ_succ]

theorem cyclicSkewAction_weighted_skew :
    ∀ i j : Fin 3,
      uniformStationaryWeight i * cyclicSkewAction i j =
        -(uniformStationaryWeight j * cyclicSkewAction j i) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [uniformStationaryWeight, cyclicSkewAction]

theorem cyclicSkewAction_commutes_uniformPositiveTransition :
    cyclicSkewAction * uniformPositiveTransition =
      uniformPositiveTransition * cyclicSkewAction := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, cyclicSkewAction,
      uniformPositiveTransition, Fin.sum_univ_succ]

theorem cyclicSkewAction_ne_zero : cyclicSkewAction ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  norm_num [cyclicSkewAction] at h01

/-- The compatible skew action is nonzero as an endomorphism of the full
matrix module, witnessed by its value on the identity matrix. -/
theorem cyclicSkewAction_leftAction_ne_zero :
    mulLeftLinearMap (Fin 3) ℝ cyclicSkewAction ≠ 0 := by
  intro h
  have hval := congrArg (fun f : Module.End ℝ (Matrix (Fin 3) (Fin 3) ℝ) =>
    f (1 : Matrix (Fin 3) (Fin 3) ℝ)) h
  have hmat : cyclicSkewAction * (1 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
    simpa [mulLeftLinearMap] using hval
  exact cyclicSkewAction_ne_zero (by simpa using hmat)

/- The coefficient carrier is explicitly witnessed as a noncommutative
three-state matrix algebra; see `fullMatrixCarrier_noncommutative_witness`. -/
def matrixUnit01 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.single 0 1 1

def matrixUnit10 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.single 1 0 1

/-- The actual coefficient algebra used here is noncommutative: these two
matrix units have distinct products. -/
theorem fullMatrixCarrier_noncommutative_witness :
    matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
  intro h
  have hdiag := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  have hleft : matrixUnit01 * matrixUnit10 = Matrix.single 0 0 (1 : ℝ) := by
    simp [matrixUnit01, matrixUnit10]
  have hright : matrixUnit10 * matrixUnit01 = Matrix.single 1 1 (1 : ℝ) := by
    simp [matrixUnit01, matrixUnit10]
  rw [hleft, hright] at hdiag
  norm_num [Matrix.single_apply] at hdiag

/-- Concrete non-vacuity instance: the nonzero cyclic skew action on the
full matrix module annihilates the stationary projector on both sides for a
strictly positive non-diagonal transition. -/
theorem exists_uniformMarkov_stationary_annihilation :
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ,
      IsGroupInverse (1 - uniformPositiveTransition) G ∧
        cyclicSkewAction ≠ 0 ∧
        mulLeftLinearMap (Fin 3) ℝ cyclicSkewAction ≠ 0 ∧
        (mulLeftLinearMap (Fin 3) ℝ cyclicSkewAction *
            mulLeftLinearMap (Fin 3) ℝ
              (markovStationaryProjector uniformPositiveTransition G) = 0 ∧
          mulLeftLinearMap (Fin 3) ℝ
              (markovStationaryProjector uniformPositiveTransition G) *
            mulLeftLinearMap (Fin 3) ℝ cyclicSkewAction = 0) := by
  obtain ⟨G, hG, _⟩ := exists_stochastic_markovLeft_groupInverse
    uniformPositiveTransition uniformPositiveTransition_rowStochastic
  refine ⟨G, hG, cyclicSkewAction_ne_zero,
    cyclicSkewAction_leftAction_ne_zero, ?_⟩
  exact weightedSkew_leftAction_annihilates_stationaryProjector
    uniformPositiveTransition cyclicSkewAction G uniformStationaryWeight
    uniformPositiveTransition_rowStochastic
    uniformPositiveTransition_entrywise_positive
    uniformStationaryWeight_normalized uniformStationaryWeight_stationary
    cyclicSkewAction_weighted_skew
    cyclicSkewAction_commutes_uniformPositiveTransition hG

end InfoGeometry.QuantumContext.MarkovDrazin
