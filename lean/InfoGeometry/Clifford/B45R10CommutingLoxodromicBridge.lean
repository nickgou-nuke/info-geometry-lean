import InfoGeometry.Clifford.BivectorPairConditionalClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-! ## Finite factorized loxodromic rotor -/

/-- The commuting boost--rotation product in the concrete spinor carrier. -/
def loxodromicRotor45_10 (a b c d : ℝ) : SpinorMatrix 5 :=
  hyperbolicRotor45 a b * ellipticRotor10 c d

theorem loxodromicRotor45_10_expand (a b c d : ℝ) :
    loxodromicRotor45_10 a b c d =
      (a * c) • (1 : SpinorMatrix 5) +
        (b * c) • mixedBivector45 +
        (a * d) • rotationBivector10 +
        (b * d) • (mixedBivector45 * rotationBivector10) := by
  unfold loxodromicRotor45_10
  rw [hyperbolicRotor45, ellipticRotor10]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  module

/-- Reverse order is part of the finite rotor data; it is not notation for a
commutative product. -/
def loxodromicRotor45_10_reverse (a b c d : ℝ) : SpinorMatrix 5 :=
  ellipticRotor10 c (-d) * hyperbolicRotor45 a (-b)

theorem loxodromicRotor45_10_mul_reverse
    (a b c d : ℝ)
    (hH : a ^ 2 - b ^ 2 = 1)
    (hE : c ^ 2 + d ^ 2 = 1) :
    loxodromicRotor45_10 a b c d *
        loxodromicRotor45_10_reverse a b c d =
      (1 : SpinorMatrix 5) := by
  unfold loxodromicRotor45_10 loxodromicRotor45_10_reverse
  calc
    (hyperbolicRotor45 a b * ellipticRotor10 c d) *
        (ellipticRotor10 c (-d) * hyperbolicRotor45 a (-b)) =
      hyperbolicRotor45 a b *
        (ellipticRotor10 c d * ellipticRotor10 c (-d)) *
          hyperbolicRotor45 a (-b) := by
            simp only [Matrix.mul_assoc]
    _ = hyperbolicRotor45 a b *
        ((c ^ 2 + d ^ 2) • (1 : SpinorMatrix 5)) *
          hyperbolicRotor45 a (-b) := by
            rw [ellipticRotor10_reverse]
    _ = hyperbolicRotor45 a b * hyperbolicRotor45 a (-b) := by
            rw [hE]
            simp
    _ = 1 := by
            rw [hyperbolicRotor45_mul_reverse_of_norm a b hH]

/-! ## Hyperbolic chiral lanes -/

/-- The two spectral projectors of the `B45` hyperbolic bivector. -/
def splitProjector45Plus : SpinorMatrix 5 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix 5) + mixedBivector45)

def splitProjector45Minus : SpinorMatrix 5 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix 5) - mixedBivector45)

theorem splitProjector45Plus_idempotent :
    splitProjector45Plus * splitProjector45Plus = splitProjector45Plus := by
  unfold splitProjector45Plus
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, add_mul, mul_add,
    one_mul, mul_one, mixedBivector45_square]
  module

theorem splitProjector45Minus_idempotent :
    splitProjector45Minus * splitProjector45Minus = splitProjector45Minus := by
  unfold splitProjector45Minus
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub,
    one_mul, mul_one, mixedBivector45_square]
  module

theorem splitProjector45Plus_mul_minus :
    splitProjector45Plus * splitProjector45Minus = 0 := by
  unfold splitProjector45Plus splitProjector45Minus
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, add_mul, mul_sub,
    one_mul, mul_one, mixedBivector45_square]
  module

theorem splitProjector45Minus_mul_plus :
    splitProjector45Minus * splitProjector45Plus = 0 := by
  unfold splitProjector45Plus splitProjector45Minus
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_add,
    one_mul, mul_one, mixedBivector45_square]
  module

theorem splitProjector45_add :
    splitProjector45Plus + splitProjector45Minus =
      (1 : SpinorMatrix 5) := by
  unfold splitProjector45Plus splitProjector45Minus
  module

theorem hyperbolicRotor45_mul_splitProjector45Plus (a b : ℝ) :
    hyperbolicRotor45 a b * splitProjector45Plus =
      (a + b) • splitProjector45Plus := by
  unfold hyperbolicRotor45 splitProjector45Plus
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    one_mul, mul_one, mixedBivector45_square]
  module

theorem hyperbolicRotor45_mul_splitProjector45Minus (a b : ℝ) :
    hyperbolicRotor45 a b * splitProjector45Minus =
      (a - b) • splitProjector45Minus := by
  unfold hyperbolicRotor45 splitProjector45Minus
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
    one_mul, mul_one, mixedBivector45_square]
  module

theorem ellipticRotor10_commutes_mixedBivector45 (c d : ℝ) :
    ellipticRotor10 c d * mixedBivector45 =
      mixedBivector45 * ellipticRotor10 c d := by
  unfold ellipticRotor10
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  rw [mixedBivector45_rotationBivector10_commute]

theorem ellipticRotor10_commutes_splitProjector45Plus (c d : ℝ) :
    ellipticRotor10 c d * splitProjector45Plus =
      splitProjector45Plus * ellipticRotor10 c d := by
  simp only [splitProjector45Plus, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_add, add_mul, ellipticRotor10_commutes_mixedBivector45]
  simp

theorem ellipticRotor10_commutes_splitProjector45Minus (c d : ℝ) :
    ellipticRotor10 c d * splitProjector45Minus =
      splitProjector45Minus * ellipticRotor10 c d := by
  simp only [splitProjector45Minus, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sub, sub_mul, ellipticRotor10_commutes_mixedBivector45]
  simp

theorem loxodromicRotor45_10_mul_splitProjector45Plus
    (a b c d : ℝ) :
    loxodromicRotor45_10 a b c d * splitProjector45Plus =
      (a + b) • (ellipticRotor10 c d * splitProjector45Plus) := by
  unfold loxodromicRotor45_10
  calc
    (hyperbolicRotor45 a b * ellipticRotor10 c d) *
        splitProjector45Plus =
      hyperbolicRotor45 a b *
        (splitProjector45Plus * ellipticRotor10 c d) := by
          rw [Matrix.mul_assoc, ellipticRotor10_commutes_splitProjector45Plus]
    _ = (hyperbolicRotor45 a b * splitProjector45Plus) *
        ellipticRotor10 c d := by rw [Matrix.mul_assoc]
    _ = ((a + b) • splitProjector45Plus) * ellipticRotor10 c d := by
          rw [hyperbolicRotor45_mul_splitProjector45Plus]
    _ = (a + b) • (ellipticRotor10 c d * splitProjector45Plus) := by
          rw [smul_mul_assoc, ellipticRotor10_commutes_splitProjector45Plus]

theorem loxodromicRotor45_10_mul_splitProjector45Minus
    (a b c d : ℝ) :
    loxodromicRotor45_10 a b c d * splitProjector45Minus =
      (a - b) • (ellipticRotor10 c d * splitProjector45Minus) := by
  unfold loxodromicRotor45_10
  calc
    (hyperbolicRotor45 a b * ellipticRotor10 c d) *
        splitProjector45Minus =
      hyperbolicRotor45 a b *
        (splitProjector45Minus * ellipticRotor10 c d) := by
          rw [Matrix.mul_assoc, ellipticRotor10_commutes_splitProjector45Minus]
    _ = (hyperbolicRotor45 a b * splitProjector45Minus) *
        ellipticRotor10 c d := by rw [Matrix.mul_assoc]
    _ = ((a - b) • splitProjector45Minus) * ellipticRotor10 c d := by
          rw [hyperbolicRotor45_mul_splitProjector45Minus]
    _ = (a - b) • (ellipticRotor10 c d * splitProjector45Minus) := by
          rw [smul_mul_assoc, ellipticRotor10_commutes_splitProjector45Minus]

end

end InfoGeometry.Clifford.B45R10CommutingLoxodromicBridge
