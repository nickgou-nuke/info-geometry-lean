import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge

/-!
# Native infinity/origin Witt readout in `Cl(5,5)`

The affine gauge `u + v` and its complementary coordinate `u - v` are read
by the normalized native null pair `(n_bar_vec / 2, n_vec / 2)`.  This file
only transports the existing `Clifford55` data; it does not introduce a
second Clifford, projective, or operator carrier.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55InfinityWittBoundary

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge
open ProjectiveAffineConformalClosure55

def infinityVector55 : V55 := (1 / 2 : ℝ) • n_bar_vec

def originVector55 : V55 := (1 / 2 : ℝ) • n_vec

def affineGaugeCoord (X : PACSplit55) : ℝ := X.u + X.v

def complementaryGaugeCoord (X : PACSplit55) : ℝ := X.u - X.v

def infinityClifford55 : Cl55 := ι55 infinityVector55

def originClifford55 : Cl55 := ι55 originVector55

def infinityProjector55 : Cl55 := infinityClifford55 * originClifford55

def originProjector55 : Cl55 := originClifford55 * infinityClifford55

def infinityGrading55 : Cl55 := infinityProjector55 - originProjector55

theorem infinityVector55_null : Q55 infinityVector55 = 0 := by
  unfold infinityVector55
  rw [QuadraticMap.map_smul, n_bar_vec_null]
  norm_num

theorem originVector55_null : Q55 originVector55 = 0 := by
  unfold originVector55
  rw [QuadraticMap.map_smul, n_vec_null]
  norm_num

private theorem nbar_pair_anticomm_coordinate (X : V55) :
    ι55 (nbar_pair 4) * ι55 X + ι55 X * ι55 (nbar_pair 4) =
      2 • (algebraMap ℝ Cl55 (X.1 4) +
        algebraMap ℝ Cl55 (X.2 4)) := by
  rcases X with ⟨x, y⟩
  rw [CliffordAlgebra.ι_mul_ι_add_swap, QuadraticMap.polar]
  rw [InfoGeometry.Clifford.Clifford55.Q55_apply,
    InfoGeometry.Clifford.Clifford55.Q55_apply,
    InfoGeometry.Clifford.Clifford55.Q55_apply]
  simp [nbar_pair, e_pos, f_neg, Fin.sum_univ_succ]
  noncomm_ring

private theorem n_pair_anticomm_coordinate (X : V55) :
    ι55 (n_pair 4) * ι55 X + ι55 X * ι55 (n_pair 4) =
      2 • (algebraMap ℝ Cl55 (X.1 4) -
        algebraMap ℝ Cl55 (X.2 4)) := by
  rcases X with ⟨x, y⟩
  rw [CliffordAlgebra.ι_mul_ι_add_swap, QuadraticMap.polar]
  rw [InfoGeometry.Clifford.Clifford55.Q55_apply,
    InfoGeometry.Clifford.Clifford55.Q55_apply,
    InfoGeometry.Clifford.Clifford55.Q55_apply]
  simp [n_pair, e_pos, f_neg, Fin.sum_univ_succ]
  noncomm_ring

theorem infinity_origin_CAR :
    ι55 infinityVector55 * ι55 originVector55 +
        ι55 originVector55 * ι55 infinityVector55 = 1 := by
  unfold infinityVector55 originVector55
  rw [map_smul, map_smul]
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
  have h : ι55 n_bar_vec * ι55 n_vec +
      ι55 n_vec * ι55 n_bar_vec = (4 : Cl55) := by
    simpa [n_vec, n_bar_vec, add_comm] using n_dot_nbar_clifford 4
  calc
    (1 / 2 : ℝ) • (1 / 2 : ℝ) • (ι55 n_bar_vec * ι55 n_vec) +
        (1 / 2 : ℝ) • (1 / 2 : ℝ) • (ι55 n_vec * ι55 n_bar_vec) =
        (1 / 4 : ℝ) •
          (ι55 n_bar_vec * ι55 n_vec + ι55 n_vec * ι55 n_bar_vec) := by
            module
    _ = (1 / 4 : ℝ) • (4 : Cl55) := by rw [h]
    _ = 1 := by
      rw [Algebra.smul_def]
      change algebraMap ℝ Cl55 (1 / 4 : ℝ) *
        algebraMap ℝ Cl55 (4 : ℝ) = 1
      rw [← map_mul]
      norm_num

theorem infinity_reads_affineGauge (X : PACSplit55) :
    ι55 infinityVector55 * ι55 (pacSplit55ToV55 X) +
        ι55 (pacSplit55ToV55 X) * ι55 infinityVector55 =
      algebraMap ℝ Cl55 (affineGaugeCoord X) := by
  unfold infinityVector55 affineGaugeCoord n_bar_vec
  rw [map_smul, smul_mul_assoc, mul_smul_comm]
  rw [← smul_add]
  rw [nbar_pair_anticomm_coordinate]
  rw [map_add]
  change (1 / 2 : ℝ) •
      (2 • (algebraMap ℝ Cl55 X.u + algebraMap ℝ Cl55 X.v)) = _
  module

theorem origin_reads_complementaryGauge (X : PACSplit55) :
    ι55 originVector55 * ι55 (pacSplit55ToV55 X) +
        ι55 (pacSplit55ToV55 X) * ι55 originVector55 =
      algebraMap ℝ Cl55 (complementaryGaugeCoord X) := by
  unfold originVector55 complementaryGaugeCoord n_vec
  rw [map_smul, smul_mul_assoc, mul_smul_comm]
  rw [← smul_add]
  rw [n_pair_anticomm_coordinate]
  rw [map_sub]
  change (1 / 2 : ℝ) •
      (2 • (algebraMap ℝ Cl55 X.u - algebraMap ℝ Cl55 X.v)) = _
  module

theorem infinity_orthogonal_iff_affineGauge_zero (X : PACSplit55) :
    (ι55 infinityVector55 * ι55 (pacSplit55ToV55 X) +
        ι55 (pacSplit55ToV55 X) * ι55 infinityVector55 = 0) ↔
      affineGaugeCoord X = 0 := by
  rw [infinity_reads_affineGauge]
  constructor
  · intro h
    apply (algebraMap ℝ Cl55).injective
    simpa using h
  · intro h
    rw [h]
    simp

theorem conformalEmbed44to55_affineGaugeCoord (x : PACSplit44) :
    affineGaugeCoord (conformalEmbed44to55 x) = 1 := by
  change chartCoordinate55
      (pacSplit55ToV55 (conformalEmbed44to55 x)) = 1
  exact conformalEmbed44to55_chartCoordinate x

theorem conformalEmbed44to55_complementaryGaugeCoord (x : PACSplit44) :
    complementaryGaugeCoord (conformalEmbed44to55 x) =
      -ProjectiveAffineConformalClosure55.Q44 x := by
  unfold complementaryGaugeCoord
    ProjectiveAffineConformalClosure55.conformalEmbed44to55
  ring

theorem conformalEmbed44to55_infinity_CAR (x : PACSplit44) :
    ι55 infinityVector55 *
          ι55 (pacSplit55ToV55 (conformalEmbed44to55 x)) +
        ι55 (pacSplit55ToV55 (conformalEmbed44to55 x)) *
          ι55 infinityVector55 =
      algebraMap ℝ Cl55 1 := by
  rw [infinity_reads_affineGauge,
    conformalEmbed44to55_affineGaugeCoord]

theorem conformalEmbed44to55_origin_CAR (x : PACSplit44) :
    ι55 originVector55 *
          ι55 (pacSplit55ToV55 (conformalEmbed44to55 x)) +
        ι55 (pacSplit55ToV55 (conformalEmbed44to55 x)) *
          ι55 originVector55 =
      algebraMap ℝ Cl55
        (-ProjectiveAffineConformalClosure55.Q44 x) := by
  rw [origin_reads_complementaryGauge,
    conformalEmbed44to55_complementaryGaugeCoord]

theorem infinityClifford55_sq_zero : infinityClifford55 * infinityClifford55 = 0 := by
  unfold infinityClifford55
  rw [CliffordAlgebra.ι_sq_scalar, infinityVector55_null]
  simp

theorem originClifford55_sq_zero : originClifford55 * originClifford55 = 0 := by
  unfold originClifford55
  rw [CliffordAlgebra.ι_sq_scalar, originVector55_null]
  simp

theorem infinity_origin_CAR_clifford :
    infinityClifford55 * originClifford55 +
        originClifford55 * infinityClifford55 = 1 := by
  exact infinity_origin_CAR

theorem infinity_origin_projector_packet :
    infinityProjector55 * infinityProjector55 = infinityProjector55 ∧
      originProjector55 * originProjector55 = originProjector55 ∧
      infinityProjector55 * originProjector55 = 0 ∧
      originProjector55 * infinityProjector55 = 0 ∧
      infinityProjector55 + originProjector55 = 1 := by
  have hI : infinityClifford55 * infinityClifford55 = 0 :=
    infinityClifford55_sq_zero
  have hO : originClifford55 * originClifford55 = 0 :=
    originClifford55_sq_zero
  have hCAR :
      infinityClifford55 * originClifford55 +
          originClifford55 * infinityClifford55 = 1 :=
    infinity_origin_CAR_clifford
  have hIO :
      infinityClifford55 * originClifford55 =
        1 - originClifford55 * infinityClifford55 := by
    calc
      infinityClifford55 * originClifford55 =
          (infinityClifford55 * originClifford55 +
            originClifford55 * infinityClifford55) -
            originClifford55 * infinityClifford55 := by abel
      _ = 1 - originClifford55 * infinityClifford55 := by rw [hCAR]
  have hOI :
      originClifford55 * infinityClifford55 =
        1 - infinityClifford55 * originClifford55 := by
    calc
      originClifford55 * infinityClifford55 =
          (originClifford55 * infinityClifford55 +
            infinityClifford55 * originClifford55) -
            infinityClifford55 * originClifford55 := by abel
      _ = 1 - infinityClifford55 * originClifford55 := by
        have hcomm : originClifford55 * infinityClifford55 +
            infinityClifford55 * originClifford55 =
            infinityClifford55 * originClifford55 +
              originClifford55 * infinityClifford55 := add_comm _ _
        rw [hcomm, hCAR]
  unfold infinityProjector55 originProjector55
  constructor
  · calc
      (infinityClifford55 * originClifford55) *
          (infinityClifford55 * originClifford55) =
          infinityClifford55 * (originClifford55 * infinityClifford55) *
            originClifford55 := by simp [mul_assoc]
      _ = infinityClifford55 *
          (1 - infinityClifford55 * originClifford55) * originClifford55 := by
        rw [hOI]
      _ = infinityClifford55 * originClifford55 -
          (infinityClifford55 * infinityClifford55) *
            (originClifford55 * originClifford55) := by
        noncomm_ring
      _ = infinityClifford55 * originClifford55 := by simp [hI, hO]
  constructor
  · calc
      (originClifford55 * infinityClifford55) *
          (originClifford55 * infinityClifford55) =
          originClifford55 * (infinityClifford55 * originClifford55) *
            infinityClifford55 := by simp [mul_assoc]
      _ = originClifford55 *
          (1 - originClifford55 * infinityClifford55) * infinityClifford55 := by
        rw [hIO]
      _ = originClifford55 * infinityClifford55 -
          (originClifford55 * originClifford55) *
            (infinityClifford55 * infinityClifford55) := by
        noncomm_ring
      _ = originClifford55 * infinityClifford55 := by simp [hI, hO]
  constructor
  · calc
      (infinityClifford55 * originClifford55) *
          (originClifford55 * infinityClifford55) =
          infinityClifford55 * (originClifford55 * originClifford55) *
            infinityClifford55 := by simp [mul_assoc]
      _ = 0 := by rw [hO, mul_zero, zero_mul]
  constructor
  · calc
      (originClifford55 * infinityClifford55) *
          (infinityClifford55 * originClifford55) =
          originClifford55 * (infinityClifford55 * infinityClifford55) *
            originClifford55 := by simp [mul_assoc]
      _ = 0 := by rw [hI, mul_zero, zero_mul]
  · exact hCAR

theorem infinityGrading55_sq : infinityGrading55 * infinityGrading55 = 1 := by
  have hP := infinity_origin_projector_packet
  unfold infinityGrading55
  rcases hP with ⟨hPInf, hPOrg, hInfOrg, hOrgInf, hsum⟩
  calc
    (infinityProjector55 - originProjector55) *
        (infinityProjector55 - originProjector55) =
        infinityProjector55 * infinityProjector55 -
          infinityProjector55 * originProjector55 -
          originProjector55 * infinityProjector55 +
          originProjector55 * originProjector55 := by noncomm_ring
    _ = infinityProjector55 + originProjector55 := by
      rw [hPInf, hInfOrg, hOrgInf, hPOrg]
      abel
    _ = 1 := hsum

private theorem infinityClifford55_mul_originClifford55_eq_one_sub :
    infinityClifford55 * originClifford55 =
      1 - originClifford55 * infinityClifford55 := by
  calc
    infinityClifford55 * originClifford55 =
        (infinityClifford55 * originClifford55 +
          originClifford55 * infinityClifford55) -
          originClifford55 * infinityClifford55 := by abel
    _ = 1 - originClifford55 * infinityClifford55 := by
      rw [infinity_origin_CAR_clifford]

private theorem originClifford55_mul_infinityClifford55_eq_one_sub :
    originClifford55 * infinityClifford55 =
      1 - infinityClifford55 * originClifford55 := by
  calc
    originClifford55 * infinityClifford55 =
        (originClifford55 * infinityClifford55 +
          infinityClifford55 * originClifford55) -
          infinityClifford55 * originClifford55 := by abel
    _ = 1 - infinityClifford55 * originClifford55 := by
      rw [add_comm, infinity_origin_CAR_clifford]

theorem infinityGrading55_mul_infinityClifford55 :
    infinityGrading55 * infinityClifford55 = infinityClifford55 := by
  have hI := infinityClifford55_sq_zero
  have hOI := originClifford55_mul_infinityClifford55_eq_one_sub
  unfold infinityGrading55 infinityProjector55 originProjector55
  calc
    (infinityClifford55 * originClifford55 -
        originClifford55 * infinityClifford55) * infinityClifford55 =
        infinityClifford55 * (originClifford55 * infinityClifford55) -
          originClifford55 * (infinityClifford55 * infinityClifford55) := by
            noncomm_ring
    _ = infinityClifford55 *
        (1 - infinityClifford55 * originClifford55) - originClifford55 * 0 := by
          rw [hOI, hI]
    _ = infinityClifford55 := by
      rw [mul_sub, mul_one, ← mul_assoc, hI, zero_mul]
      simp

theorem infinityGrading55_mul_originClifford55 :
    infinityGrading55 * originClifford55 = -originClifford55 := by
  have hO := originClifford55_sq_zero
  have hIO := infinityClifford55_mul_originClifford55_eq_one_sub
  unfold infinityGrading55 infinityProjector55 originProjector55
  calc
    (infinityClifford55 * originClifford55 -
        originClifford55 * infinityClifford55) * originClifford55 =
        infinityClifford55 * (originClifford55 * originClifford55) -
          originClifford55 * (infinityClifford55 * originClifford55) := by
            noncomm_ring
    _ = infinityClifford55 * 0 - originClifford55 *
        (1 - originClifford55 * infinityClifford55) := by
          rw [hO, hIO]
    _ = -originClifford55 := by
      rw [mul_zero, mul_sub, mul_one, ← mul_assoc, hO, zero_mul]
      simp

theorem infinityClifford55_mul_infinityGrading55 :
    infinityClifford55 * infinityGrading55 = -infinityClifford55 := by
  have hI := infinityClifford55_sq_zero
  have hOI := originClifford55_mul_infinityClifford55_eq_one_sub
  unfold infinityGrading55 infinityProjector55 originProjector55
  calc
    infinityClifford55 *
        (infinityClifford55 * originClifford55 -
          originClifford55 * infinityClifford55) =
        (infinityClifford55 * infinityClifford55) * originClifford55 -
          infinityClifford55 * (originClifford55 * infinityClifford55) := by
            noncomm_ring
    _ = 0 * originClifford55 - infinityClifford55 *
        (1 - infinityClifford55 * originClifford55) := by
          rw [hI, hOI]
    _ = -infinityClifford55 := by
      rw [zero_mul, mul_sub, mul_one, ← mul_assoc, hI, zero_mul]
      simp

theorem originClifford55_mul_infinityGrading55 :
    originClifford55 * infinityGrading55 = originClifford55 := by
  have hO := originClifford55_sq_zero
  have hIO := infinityClifford55_mul_originClifford55_eq_one_sub
  unfold infinityGrading55 infinityProjector55 originProjector55
  calc
    originClifford55 *
        (infinityClifford55 * originClifford55 -
          originClifford55 * infinityClifford55) =
        originClifford55 * (infinityClifford55 * originClifford55) -
          (originClifford55 * originClifford55) * infinityClifford55 := by
            noncomm_ring
    _ = originClifford55 *
        (1 - originClifford55 * infinityClifford55) - 0 := by
          rw [hIO, hO]
          simp
    _ = originClifford55 := by
      rw [sub_zero, mul_sub, mul_one, ← mul_assoc, hO, zero_mul]
      simp

theorem infinityGrading55_anticomm_infinityClifford55 :
    infinityGrading55 * infinityClifford55 +
        infinityClifford55 * infinityGrading55 = 0 := by
  rw [infinityGrading55_mul_infinityClifford55,
    infinityClifford55_mul_infinityGrading55]
  exact add_neg_cancel _

theorem infinityGrading55_anticomm_originClifford55 :
    infinityGrading55 * originClifford55 +
        originClifford55 * infinityGrading55 = 0 := by
  rw [infinityGrading55_mul_originClifford55,
    originClifford55_mul_infinityGrading55]
  exact neg_add_cancel _

theorem infinityProjector55_eq_half_add_grading :
    infinityProjector55 =
      (1 / 2 : ℝ) • (1 + infinityGrading55) := by
  have hP := infinity_origin_projector_packet
  rcases hP with ⟨_, _, _, _, hsum⟩
  unfold infinityProjector55 originProjector55 at hsum
  unfold infinityProjector55 infinityGrading55 originProjector55
  calc
    infinityClifford55 * originClifford55 =
        (1 / 2 : ℝ) •
          (infinityClifford55 * originClifford55 +
            infinityClifford55 * originClifford55) := by
              calc
                infinityClifford55 * originClifford55 =
                    (1 : ℝ) • (infinityClifford55 * originClifford55) := by
                      rw [one_smul]
                _ = ((1 / 2 : ℝ) * 2) •
                    (infinityClifford55 * originClifford55) := by norm_num
                _ = (1 / 2 : ℝ) •
                    ((2 : ℝ) • (infinityClifford55 * originClifford55)) := by
                      rw [smul_smul]
                _ = (1 / 2 : ℝ) •
                    (infinityClifford55 * originClifford55 +
                      infinityClifford55 * originClifford55) := by
                      rw [two_smul]
    _ = (1 / 2 : ℝ) •
        ((infinityClifford55 * originClifford55 +
          originClifford55 * infinityClifford55) +
          (infinityClifford55 * originClifford55 -
            originClifford55 * infinityClifford55)) := by
          congr 1
          abel
    _ = (1 / 2 : ℝ) •
        (1 + (infinityClifford55 * originClifford55 -
          originClifford55 * infinityClifford55)) := by rw [hsum]

theorem originProjector55_eq_half_sub_grading :
    originProjector55 =
      (1 / 2 : ℝ) • (1 - infinityGrading55) := by
  have hP := infinity_origin_projector_packet
  rcases hP with ⟨_, _, _, _, hsum⟩
  unfold originProjector55 infinityProjector55 at hsum
  unfold originProjector55 infinityGrading55 infinityProjector55
  calc
    originClifford55 * infinityClifford55 =
        (1 / 2 : ℝ) •
          (originClifford55 * infinityClifford55 +
            originClifford55 * infinityClifford55) := by
              calc
                originClifford55 * infinityClifford55 =
                    (1 : ℝ) • (originClifford55 * infinityClifford55) := by
                      rw [one_smul]
                _ = ((1 / 2 : ℝ) * 2) •
                    (originClifford55 * infinityClifford55) := by norm_num
                _ = (1 / 2 : ℝ) •
                    ((2 : ℝ) • (originClifford55 * infinityClifford55)) := by
                      rw [smul_smul]
                _ = (1 / 2 : ℝ) •
                    (originClifford55 * infinityClifford55 +
                      originClifford55 * infinityClifford55) := by
                      rw [two_smul]
    _ = (1 / 2 : ℝ) •
        ((infinityClifford55 * originClifford55 +
          originClifford55 * infinityClifford55) -
          (infinityClifford55 * originClifford55 -
            originClifford55 * infinityClifford55)) := by
          congr 1
          abel
    _ = (1 / 2 : ℝ) •
        (1 - (infinityClifford55 * originClifford55 -
          originClifford55 * infinityClifford55)) := by rw [hsum]

/-! ### A scalar deformation of the normalized Witt generator -/

def deformedInfinityClifford55 (κ : ℝ) : Cl55 :=
  infinityClifford55 + κ • originClifford55

theorem deformedInfinityClifford55_sq (κ : ℝ) :
    deformedInfinityClifford55 κ * deformedInfinityClifford55 κ =
      algebraMap ℝ Cl55 κ := by
  have hI : infinityClifford55 * infinityClifford55 = 0 :=
    infinityClifford55_sq_zero
  have hO : originClifford55 * originClifford55 = 0 :=
    originClifford55_sq_zero
  have hCAR :
      infinityClifford55 * originClifford55 +
          originClifford55 * infinityClifford55 = 1 :=
    infinity_origin_CAR_clifford
  unfold deformedInfinityClifford55
  calc
    (infinityClifford55 + κ • originClifford55) *
        (infinityClifford55 + κ • originClifford55) =
        infinityClifford55 * infinityClifford55 +
          κ • (infinityClifford55 * originClifford55) +
          κ • (originClifford55 * infinityClifford55) +
          (κ * κ) • (originClifford55 * originClifford55) := by
            simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
              smul_add, smul_smul]
            abel
    _ = κ •
        (infinityClifford55 * originClifford55 +
          originClifford55 * infinityClifford55) := by
      rw [hI, hO]
      module
    _ = κ • (1 : Cl55) := by rw [hCAR]
    _ = algebraMap ℝ Cl55 κ := by
      rw [Algebra.smul_def]
      simp

end InfoGeometry.Canonical.Cl55InfinityWittBoundary
