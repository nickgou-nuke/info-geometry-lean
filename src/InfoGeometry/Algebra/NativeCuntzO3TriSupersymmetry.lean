import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Native O₃ root operators

The Cuntz O₃ relations are supplied by the tensor-algebra quotient itself.
This owner therefore uses `CuntzAlg 3` directly instead of a record carrying
copies of the six generators and their relation proofs.
-/

noncomputable section

namespace InfoGeometry.Algebra.NativeCuntzO3TriSupersymmetry

open InfoGeometry.Algebra.CuntzTensorQuotient

abbrev Carrier := CuntzAlg 3

def rangeProjection (i : Fin 3) : Carrier :=
  cuntzS 3 i * star (cuntzS 3 i)

def Q12 : Carrier := cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3))
def Q21 : Carrier := cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (0 : Fin 3))
def Q23 : Carrier := cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (2 : Fin 3))
def Q32 : Carrier := cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (1 : Fin 3))
def Q31 : Carrier := cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (0 : Fin 3))
def Q13 : Carrier := cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (2 : Fin 3))

def Lambda3 : Carrier := rangeProjection (0 : Fin 3) - rangeProjection (1 : Fin 3)

def Lambda8 : Carrier :=
  rangeProjection (0 : Fin 3) + rangeProjection (1 : Fin 3) - 2 * rangeProjection (2 : Fin 3)

def lieBracket (x y : Carrier) : Carrier := x * y - y * x

theorem q12_nilpotent : Q12 * Q12 = 0 := by
  dsimp [Q12]
  have h : cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3)) *
      (cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3))) =
      cuntzS 3 (0 : Fin 3) * (star (cuntzS 3 (1 : Fin 3)) * cuntzS 3 (0 : Fin 3)) *
        star (cuntzS 3 (1 : Fin 3)) := by noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q23_nilpotent : Q23 * Q23 = 0 := by
  dsimp [Q23]
  have h : cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (2 : Fin 3)) *
      (cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (2 : Fin 3))) =
      cuntzS 3 (1 : Fin 3) * (star (cuntzS 3 (2 : Fin 3)) * cuntzS 3 (1 : Fin 3)) *
        star (cuntzS 3 (2 : Fin 3)) := by noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q31_nilpotent : Q31 * Q31 = 0 := by
  dsimp [Q31]
  have h : cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (0 : Fin 3)) *
      (cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (0 : Fin 3))) =
      cuntzS 3 (2 : Fin 3) * (star (cuntzS 3 (0 : Fin 3)) * cuntzS 3 (2 : Fin 3)) *
        star (cuntzS 3 (0 : Fin 3)) := by noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q12_q21_product : Q12 * Q21 = rangeProjection (0 : Fin 3) := by
  dsimp [Q12, Q21, rangeProjection]
  have h : cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3)) *
      (cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (0 : Fin 3))) =
      cuntzS 3 (0 : Fin 3) * (star (cuntzS 3 (1 : Fin 3)) * cuntzS 3 (1 : Fin 3)) *
        star (cuntzS 3 (0 : Fin 3)) := by noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q23_q32_product : Q23 * Q32 = rangeProjection (1 : Fin 3) := by
  dsimp [Q23, Q32, rangeProjection]
  have h : cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (2 : Fin 3)) *
      (cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (1 : Fin 3))) =
      cuntzS 3 (1 : Fin 3) * (star (cuntzS 3 (2 : Fin 3)) * cuntzS 3 (2 : Fin 3)) *
        star (cuntzS 3 (1 : Fin 3)) := by noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q31_q13_product : Q31 * Q13 = rangeProjection (2 : Fin 3) := by
  dsimp [Q31, Q13, rangeProjection]
  have h : cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (0 : Fin 3)) *
      (cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (2 : Fin 3))) =
      cuntzS 3 (2 : Fin 3) * (star (cuntzS 3 (0 : Fin 3)) * cuntzS 3 (0 : Fin 3)) *
        star (cuntzS 3 (2 : Fin 3)) := by noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q21_q12_product : Q21 * Q12 = rangeProjection (1 : Fin 3) := by
  dsimp [Q21, Q12, rangeProjection]
  have h : cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (0 : Fin 3)) *
      (cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3))) =
      cuntzS 3 (1 : Fin 3) * (star (cuntzS 3 (0 : Fin 3)) *
        cuntzS 3 (0 : Fin 3)) * star (cuntzS 3 (1 : Fin 3)) := by
    noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q32_q23_product : Q32 * Q23 = rangeProjection (2 : Fin 3) := by
  dsimp [Q32, Q23, rangeProjection]
  have h : cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (1 : Fin 3)) *
      (cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (2 : Fin 3))) =
      cuntzS 3 (2 : Fin 3) * (star (cuntzS 3 (1 : Fin 3)) *
        cuntzS 3 (1 : Fin 3)) * star (cuntzS 3 (2 : Fin 3)) := by
    noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q13_q31_product : Q13 * Q31 = rangeProjection (0 : Fin 3) := by
  dsimp [Q13, Q31, rangeProjection]
  have h : cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (2 : Fin 3)) *
      (cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (0 : Fin 3))) =
      cuntzS 3 (0 : Fin 3) * (star (cuntzS 3 (2 : Fin 3)) *
        cuntzS 3 (2 : Fin 3)) * star (cuntzS 3 (0 : Fin 3)) := by
    noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem lambda3_squared : Lambda3 * Lambda3 =
    rangeProjection (0 : Fin 3) + rangeProjection (1 : Fin 3) := by
  dsimp [Lambda3]
  have h00 : rangeProjection (0 : Fin 3) * rangeProjection 0 =
      rangeProjection 0 := by
    simpa only [rangeProjection, star_cuntzS] using cuntz_range_projector 3 (0 : Fin 3)
  have h11 : rangeProjection (1 : Fin 3) * rangeProjection 1 =
      rangeProjection 1 := by
    simpa only [rangeProjection, star_cuntzS] using cuntz_range_projector 3 (1 : Fin 3)
  have h01 : rangeProjection (0 : Fin 3) * rangeProjection 1 = 0 := by
    simpa only [rangeProjection, star_cuntzS] using
      cuntz_range_projectors_orthogonal 3 (i := (0 : Fin 3))
        (j := (1 : Fin 3)) (by decide)
  have h10 : rangeProjection (1 : Fin 3) * rangeProjection 0 = 0 := by
    simpa only [rangeProjection, star_cuntzS] using
      cuntz_range_projectors_orthogonal 3 (i := (1 : Fin 3))
        (j := (0 : Fin 3)) (by decide)
  calc
    (rangeProjection 0 - rangeProjection 1) *
        (rangeProjection 0 - rangeProjection 1) =
        (rangeProjection 0 - rangeProjection 1) * rangeProjection 0 -
          (rangeProjection 0 - rangeProjection 1) * rangeProjection 1 := by
            rw [mul_sub]
    _ = (rangeProjection 0 * rangeProjection 0 -
          rangeProjection 1 * rangeProjection 0) -
        (rangeProjection 0 * rangeProjection 1 -
          rangeProjection 1 * rangeProjection 1) := by
            rw [sub_mul, sub_mul]
    _ = rangeProjection 0 * rangeProjection 0 - rangeProjection 0 * rangeProjection 1 -
          rangeProjection 1 * rangeProjection 0 + rangeProjection 1 * rangeProjection 1 := by
            noncomm_ring
    _ = rangeProjection 0 + rangeProjection 1 := by
      rw [h00, h01, h10, h11]
      noncomm_ring

theorem lambda8_squared : Lambda8 * Lambda8 =
    rangeProjection (0 : Fin 3) + rangeProjection (1 : Fin 3) +
      4 * rangeProjection (2 : Fin 3) := by
  dsimp [Lambda8]
  have h00 := cuntz_range_projector 3 (0 : Fin 3)
  have h11 := cuntz_range_projector 3 (1 : Fin 3)
  have h22 := cuntz_range_projector 3 (2 : Fin 3)
  have h01 := cuntz_range_projectors_orthogonal 3 (i := (0 : Fin 3))
    (j := (1 : Fin 3)) (by decide)
  have h10 := cuntz_range_projectors_orthogonal 3 (i := (1 : Fin 3))
    (j := (0 : Fin 3)) (by decide)
  have h02 := cuntz_range_projectors_orthogonal 3 (i := (0 : Fin 3))
    (j := (2 : Fin 3)) (by decide)
  have h20 := cuntz_range_projectors_orthogonal 3 (i := (2 : Fin 3))
    (j := (0 : Fin 3)) (by decide)
  have h12 := cuntz_range_projectors_orthogonal 3 (i := (1 : Fin 3))
    (j := (2 : Fin 3)) (by decide)
  have h21 := cuntz_range_projectors_orthogonal 3 (i := (2 : Fin 3))
    (j := (1 : Fin 3)) (by decide)
  have h00' : rangeProjection (0 : Fin 3) * rangeProjection 0 =
      rangeProjection 0 := by simpa only [rangeProjection, star_cuntzS] using h00
  have h11' : rangeProjection (1 : Fin 3) * rangeProjection 1 =
      rangeProjection 1 := by simpa only [rangeProjection, star_cuntzS] using h11
  have h22' : rangeProjection (2 : Fin 3) * rangeProjection 2 =
      rangeProjection 2 := by simpa only [rangeProjection, star_cuntzS] using h22
  have h01' : rangeProjection (0 : Fin 3) * rangeProjection 1 = 0 := by
    simpa only [rangeProjection, star_cuntzS] using h01
  have h10' : rangeProjection (1 : Fin 3) * rangeProjection 0 = 0 := by
    simpa only [rangeProjection, star_cuntzS] using h10
  have h02' : rangeProjection (0 : Fin 3) * rangeProjection 2 = 0 := by
    simpa only [rangeProjection, star_cuntzS] using h02
  have h20' : rangeProjection (2 : Fin 3) * rangeProjection 0 = 0 := by
    simpa only [rangeProjection, star_cuntzS] using h20
  have h12' : rangeProjection (1 : Fin 3) * rangeProjection 2 = 0 := by
    simpa only [rangeProjection, star_cuntzS] using h12
  have h21' : rangeProjection (2 : Fin 3) * rangeProjection 1 = 0 := by
    simpa only [rangeProjection, star_cuntzS] using h21
  rw [two_mul]
  calc
    (rangeProjection 0 + rangeProjection 1 -
        (rangeProjection 2 + rangeProjection 2)) *
        (rangeProjection 0 + rangeProjection 1 -
          (rangeProjection 2 + rangeProjection 2)) =
      rangeProjection 0 * rangeProjection 0 +
        rangeProjection 0 * rangeProjection 1 -
        (rangeProjection 0 * rangeProjection 2 +
          rangeProjection 0 * rangeProjection 2) +
        rangeProjection 1 * rangeProjection 0 +
        rangeProjection 1 * rangeProjection 1 -
        (rangeProjection 1 * rangeProjection 2 +
          rangeProjection 1 * rangeProjection 2) -
        (rangeProjection 2 * rangeProjection 0 +
          rangeProjection 2 * rangeProjection 0) -
        (rangeProjection 2 * rangeProjection 1 +
          rangeProjection 2 * rangeProjection 1) +
        ((rangeProjection 2 * rangeProjection 2 +
          rangeProjection 2 * rangeProjection 2) +
          (rangeProjection 2 * rangeProjection 2 +
            rangeProjection 2 * rangeProjection 2)) := by
          simp only [sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
          noncomm_ring
    _ = rangeProjection 0 + rangeProjection 1 +
        4 * rangeProjection 2 := by
      rw [h00', h01', h02', h10', h11', h12', h20', h21', h22']
      noncomm_ring

theorem tri_susy_hamiltonian_completeness :
    Q12 * Q21 + Q23 * Q32 + Q31 * Q13 = 1 := by
  rw [q12_q21_product, q23_q32_product, q31_q13_product]
  calc
    rangeProjection (0 : Fin 3) + rangeProjection (1 : Fin 3) +
        rangeProjection (2 : Fin 3) =
        rangeProjection (0 : Fin 3) +
        (rangeProjection (1 : Fin 3) + rangeProjection (2 : Fin 3)) := by
          abel
    _ = 1 := by
      simpa [rangeProjection, star_cuntzS, Fin.sum_univ_succ] using
        cuntz_ranges_sum_one 3

theorem q12_q23_product : Q12 * Q23 = Q13 := by
  dsimp [Q12, Q23, Q13]
  have h : cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3)) *
      (cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (2 : Fin 3))) =
      cuntzS 3 (0 : Fin 3) * (star (cuntzS 3 (1 : Fin 3)) * cuntzS 3 (1 : Fin 3)) *
        star (cuntzS 3 (2 : Fin 3)) := by noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q23_q12_product : Q23 * Q12 = 0 := by
  dsimp [Q23, Q12]
  have h : cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (2 : Fin 3)) *
      (cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3))) =
      cuntzS 3 (1 : Fin 3) * (star (cuntzS 3 (2 : Fin 3)) * cuntzS 3 (0 : Fin 3)) *
        star (cuntzS 3 (1 : Fin 3)) := by noncomm_ring
  simp only [star_cuntzS] at h ⊢
  rw [h, cuntz_orthogonality]; simp

theorem q12_q23_commutator : lieBracket Q12 Q23 = Q13 := by
  dsimp [lieBracket]
  rw [q12_q23_product, q23_q12_product, sub_zero]

theorem q12_q21_commutator : lieBracket Q12 Q21 = Lambda3 := by
  dsimp [lieBracket, Lambda3]
  rw [q12_q21_product]
  have h : Q21 * Q12 = rangeProjection (1 : Fin 3) := by
    dsimp [Q21, Q12, rangeProjection]
    have h' : cuntzS 3 (1 : Fin 3) * star (cuntzS 3 (0 : Fin 3)) *
        (cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3))) =
        cuntzS 3 (1 : Fin 3) * (star (cuntzS 3 (0 : Fin 3)) * cuntzS 3 (0 : Fin 3)) *
          star (cuntzS 3 (1 : Fin 3)) := by noncomm_ring
    simp only [star_cuntzS] at h' ⊢
    rw [h', cuntz_orthogonality]; simp
  rw [h]

end InfoGeometry.Algebra.NativeCuntzO3TriSupersymmetry
