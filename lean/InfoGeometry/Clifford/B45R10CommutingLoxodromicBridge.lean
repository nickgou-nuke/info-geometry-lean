import InfoGeometry.Clifford.BivectorPairConditionalClosure
import InfoGeometry.Clifford.Cl55ConcreteBivectorSignature

/-!
# Concrete commuting closure of the `B45` and `R10` bivectors

The two bivectors use disjoint Clifford basis directions. Moving one
grade-two word past the other contributes four sign changes, so the concrete
axes commute. This is the finite Cartan/loxodromic lane; it makes no
matrix-exponential or BCH claim.
-/

namespace InfoGeometry.Clifford.B45R10CommutingLoxodromicBridge

open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.Cl55ConcreteBivectorSignature
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.CliffordTower

noncomputable section

private theorem gammaBasis55_anticomm_of_polar_zero (i j : Fin 10)
    (hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis i))
      (vec55SplitEquiv (vec55Basis j)) = 0) :
    gammaBasis55 i * gammaBasis55 j = -(gammaBasis55 j * gammaBasis55 i) := by
  have h := gamma55_anticomm (vec55Basis i) (vec55Basis j)
  rw [hpolar, map_zero] at h
  simpa [gammaBasis55] using (eq_neg_of_add_eq_zero_left h)

private theorem gammaBasis55_41_anticomm :
    gammaBasis55 4 * gammaBasis55 1 = -(gammaBasis55 1 * gammaBasis55 4) := by
  apply gammaBasis55_anticomm_of_polar_zero
  rw [QuadraticMap.polar]
  change (Qsplit 5) (vec55SplitEquiv (vec55Basis 4 + vec55Basis 1)) -
    (Qsplit 5) (vec55SplitEquiv (vec55Basis 4)) -
    (Qsplit 5) (vec55SplitEquiv (vec55Basis 1)) = 0
  rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
  simp [vec55Basis, q55Real]

private theorem gammaBasis55_51_anticomm :
    gammaBasis55 5 * gammaBasis55 1 = -(gammaBasis55 1 * gammaBasis55 5) := by
  apply gammaBasis55_anticomm_of_polar_zero
  rw [QuadraticMap.polar]
  change (Qsplit 5) (vec55SplitEquiv (vec55Basis 5 + vec55Basis 1)) -
    (Qsplit 5) (vec55SplitEquiv (vec55Basis 5)) -
    (Qsplit 5) (vec55SplitEquiv (vec55Basis 1)) = 0
  rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
  simp [vec55Basis, q55Real]

private theorem gammaBasis55_40_anticomm :
    gammaBasis55 4 * gammaBasis55 0 = -(gammaBasis55 0 * gammaBasis55 4) := by
  apply gammaBasis55_anticomm_of_polar_zero
  rw [QuadraticMap.polar]
  change (Qsplit 5) (vec55SplitEquiv (vec55Basis 4 + vec55Basis 0)) -
    (Qsplit 5) (vec55SplitEquiv (vec55Basis 4)) -
    (Qsplit 5) (vec55SplitEquiv (vec55Basis 0)) = 0
  rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
  simp [vec55Basis, q55Real]

private theorem gammaBasis55_50_anticomm :
    gammaBasis55 5 * gammaBasis55 0 = -(gammaBasis55 0 * gammaBasis55 5) := by
  apply gammaBasis55_anticomm_of_polar_zero
  rw [QuadraticMap.polar]
  change (Qsplit 5) (vec55SplitEquiv (vec55Basis 5 + vec55Basis 0)) -
    (Qsplit 5) (vec55SplitEquiv (vec55Basis 5)) -
    (Qsplit 5) (vec55SplitEquiv (vec55Basis 0)) = 0
  rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
  simp [vec55Basis, q55Real]

/-- The concrete disjoint bivectors commute after four Clifford sign swaps. -/
theorem mixedBivector45_rotationBivector10_commute :
    mixedBivector45 * rotationBivector10 =
      rotationBivector10 * mixedBivector45 := by
  unfold mixedBivector45 rotationBivector10
  calc
    (gammaBasis55 5 * gammaBasis55 4) *
        (gammaBasis55 1 * gammaBasis55 0) =
      gammaBasis55 5 * (gammaBasis55 4 * gammaBasis55 1) *
        gammaBasis55 0 := by simp only [mul_assoc]
    _ = gammaBasis55 5 * (-(gammaBasis55 1 * gammaBasis55 4)) *
        gammaBasis55 0 := by rw [gammaBasis55_41_anticomm]
    _ = -(gammaBasis55 5 * gammaBasis55 1) *
        (gammaBasis55 4 * gammaBasis55 0) := by noncomm_ring
    _ = (gammaBasis55 1 * gammaBasis55 5) *
        (gammaBasis55 4 * gammaBasis55 0) := by
          rw [gammaBasis55_51_anticomm]
          simp
    _ = (gammaBasis55 1 * gammaBasis55 5) *
        (-(gammaBasis55 0 * gammaBasis55 4)) := by
          rw [gammaBasis55_40_anticomm]
    _ = gammaBasis55 1 * (-(gammaBasis55 5 * gammaBasis55 0)) *
        gammaBasis55 4 := by noncomm_ring
    _ = (gammaBasis55 1 * gammaBasis55 0) *
        (gammaBasis55 5 * gammaBasis55 4) := by
          rw [gammaBasis55_50_anticomm]
          noncomm_ring

/-- The associative-algebra commutator of the two concrete axes vanishes. -/
theorem mixedBivector45_rotationBivector10_commutator_zero :
    mixedBivector45 * rotationBivector10 -
      rotationBivector10 * mixedBivector45 = 0 := by
  rw [mixedBivector45_rotationBivector10_commute, sub_self]

/-- The commuting product is another square-`-1` direction. -/
theorem mixedBivector45_rotationBivector10_product_square :
    (mixedBivector45 * rotationBivector10) *
        (mixedBivector45 * rotationBivector10) =
      (-1 : SpinorMatrix 5) := by
  calc
    (mixedBivector45 * rotationBivector10) *
        (mixedBivector45 * rotationBivector10) =
      (mixedBivector45 * mixedBivector45) *
        (rotationBivector10 * rotationBivector10) :=
          BivectorPairConditionalClosure.commuting_pair_product
            mixedBivector45_rotationBivector10_commute
    _ = (-1 : SpinorMatrix 5) := by
      rw [mixedBivector45_square, rotationBivector10_square, one_mul]

/-- The real two-parameter generator in the commuting mixed bivector plane. -/
def loxodromicGenerator (alpha beta : ℝ) : SpinorMatrix 5 :=
  alpha • mixedBivector45 + beta • rotationBivector10

/-- Exact square of the combined generator; the commuting cross term remains. -/
theorem loxodromicGenerator_square (alpha beta : ℝ) :
    loxodromicGenerator alpha beta * loxodromicGenerator alpha beta =
      (alpha ^ 2 - beta ^ 2) • (1 : SpinorMatrix 5) +
        (2 * alpha * beta) •
          (mixedBivector45 * rotationBivector10) := by
  unfold loxodromicGenerator
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    mixedBivector45_square, rotationBivector10_square, smul_neg]
  rw [mixedBivector45_rotationBivector10_commute]
  module

end

end InfoGeometry.Clifford.B45R10CommutingLoxodromicBridge
