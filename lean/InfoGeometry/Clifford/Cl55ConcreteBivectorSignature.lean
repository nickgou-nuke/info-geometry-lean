import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Clifford.LorentzianBivectorSignatureBridge

/-!
# A concrete mixed-signature bivector in the native `Cl(5,5)` carrier

The pair `(4,5)` is one positive and one negative Clifford basis direction.
The generic grade-two signature lemma therefore gives a concrete square-`+1`
hyperbolic bivector, while the anticommutation relation is inherited from the
native split gamma construction.
-/

namespace InfoGeometry.Clifford.Cl55ConcreteBivectorSignature

open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.LorentzianBivectorSignatureBridge
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.CliffordTower

noncomputable section

def mixedBivector45 : SpinorMatrix 5 := gammaBasis55 5 * gammaBasis55 4

def rotationBivector10 : SpinorMatrix 5 := gammaBasis55 1 * gammaBasis55 0

def ellipticRotor10 (a b : ℝ) : SpinorMatrix 5 :=
  a • (1 : SpinorMatrix 5) + b • rotationBivector10

def hyperbolicRotor45 (a b : ℝ) : SpinorMatrix 5 :=
  a • (1 : SpinorMatrix 5) + b • mixedBivector45

def cliffordBivector45 : Cl_split 5 :=
  gammaBasisClifford55 5 * gammaBasisClifford55 4

def cliffordBivector10 : Cl_split 5 :=
  gammaBasisClifford55 1 * gammaBasisClifford55 0

theorem spinorRepresentation_cliffordBivector45 :
    (spinorRepresentation 5) cliffordBivector45 = mixedBivector45 := by
  unfold cliffordBivector45 mixedBivector45 gammaBasisClifford55
  rw [map_mul, spinorRepresentation_ι, spinorRepresentation_ι,
    gammaBasis55, gammaBasis55]
  rfl

theorem spinorRepresentation_cliffordBivector10 :
    (spinorRepresentation 5) cliffordBivector10 = rotationBivector10 := by
  unfold cliffordBivector10 rotationBivector10 gammaBasisClifford55
  rw [map_mul, spinorRepresentation_ι, spinorRepresentation_ι,
    gammaBasis55, gammaBasis55]
  rfl

def cliffordEllipticRotor10 (a b : ℝ) : Cl_split 5 :=
  a • (1 : Cl_split 5) + b • cliffordBivector10

def cliffordHyperbolicRotor45 (a b : ℝ) : Cl_split 5 :=
  a • (1 : Cl_split 5) + b • cliffordBivector45

theorem spinorRepresentation_cliffordEllipticRotor10 (a b : ℝ) :
    (spinorRepresentation 5) (cliffordEllipticRotor10 a b) =
      ellipticRotor10 a b := by
  unfold cliffordEllipticRotor10 ellipticRotor10
  rw [map_add, map_smul, map_smul, map_one,
    spinorRepresentation_cliffordBivector10]

theorem spinorRepresentation_cliffordHyperbolicRotor45 (a b : ℝ) :
    (spinorRepresentation 5) (cliffordHyperbolicRotor45 a b) =
      hyperbolicRotor45 a b := by
  unfold cliffordHyperbolicRotor45 hyperbolicRotor45
  rw [map_add, map_smul, map_smul, map_one,
    spinorRepresentation_cliffordBivector45]

theorem gammaBasis55_45_positive_square :
    gammaBasis55 4 * gammaBasis55 4 = (1 : SpinorMatrix 5) := by
  simpa using gammaBasis55_sq 4

theorem gammaBasis55_45_negative_square :
    gammaBasis55 5 * gammaBasis55 5 = (-1 : SpinorMatrix 5) := by
  simpa using gammaBasis55_sq 5

theorem mixedBivector45_square :
    mixedBivector45 * mixedBivector45 = (1 : SpinorMatrix 5) := by
  apply mixed_bivector_sq_one
  · exact gammaBasis55_45_positive_square
  · exact gammaBasis55_45_negative_square
  · have hpolar : QuadraticMap.polar (Qsplit 5)
        (vec55SplitEquiv (vec55Basis 4))
        (vec55SplitEquiv (vec55Basis 5)) = 0 := by
      rw [vec55SplitEquiv_basis4, vec55SplitEquiv_basis5]
      rw [QuadraticMap.polar]
      change (Qsplit 5) (vec55SplitEquiv (vec55Basis 4 + vec55Basis 5)) -
        (Qsplit 5) (vec55SplitEquiv (vec55Basis 4)) -
        (Qsplit 5) (vec55SplitEquiv (vec55Basis 5)) = 0
      rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv,
        splitQ_vec55SplitEquiv]
      simp [vec55Basis, q55Real]
    have h := gamma55_anticomm (vec55Basis 4) (vec55Basis 5)
    rw [hpolar, map_zero] at h
    simpa [gammaBasis55] using h

theorem gammaBasis55_10_anticomm :
    gammaBasis55 0 * gammaBasis55 1 =
      -(gammaBasis55 1 * gammaBasis55 0) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 0))
      (vec55SplitEquiv (vec55Basis 1)) = 0 := by
    rw [vec55SplitEquiv_basis0, vec55SplitEquiv_basis1]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 0 + vec55Basis 1)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 0)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 1)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv,
      splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  have h := gamma55_anticomm (vec55Basis 0) (vec55Basis 1)
  rw [hpolar, map_zero] at h
  simpa [gammaBasis55] using (eq_neg_of_add_eq_zero_left h)

theorem rotationBivector10_square :
    rotationBivector10 * rotationBivector10 = (-1 : SpinorMatrix 5) := by
  apply positive_bivector_sq_neg_one
  · simpa using gammaBasis55_sq 1
  · simpa using gammaBasis55_sq 0
  · have h := gammaBasis55_10_anticomm
    simpa [add_comm] using (show gammaBasis55 1 * gammaBasis55 0 +
      gammaBasis55 0 * gammaBasis55 1 = 0 by
        rw [h]
        abel)

theorem ellipticRotor10_mul (a b c d : ℝ) :
    ellipticRotor10 a b * ellipticRotor10 c d =
      (a * c - b * d) • (1 : SpinorMatrix 5) +
        (a * d + b * c) • rotationBivector10 := by
  unfold ellipticRotor10
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, rotationBivector10_square, smul_neg]
  module

theorem hyperbolicRotor45_mul (a b c d : ℝ) :
    hyperbolicRotor45 a b * hyperbolicRotor45 c d =
      (a * c + b * d) • (1 : SpinorMatrix 5) +
        (a * d + b * c) • mixedBivector45 := by
  unfold hyperbolicRotor45
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, mixedBivector45_square, smul_add]
  module

theorem ellipticRotor10_reverse (a b : ℝ) :
    ellipticRotor10 a b * ellipticRotor10 a (-b) =
      (a ^ 2 + b ^ 2) • (1 : SpinorMatrix 5) := by
  rw [ellipticRotor10_mul]
  simp only [mul_neg, sub_neg_eq_add]
  module

theorem hyperbolicRotor45_reverse (a b : ℝ) :
    hyperbolicRotor45 a b * hyperbolicRotor45 a (-b) =
      (a ^ 2 - b ^ 2) • (1 : SpinorMatrix 5) := by
  rw [hyperbolicRotor45_mul]
  simp only [mul_neg, sub_neg_eq_add]
  module

theorem ellipticRotor10_reverse_mul (a b : ℝ) :
    ellipticRotor10 a (-b) * ellipticRotor10 a b =
      (a ^ 2 + b ^ 2) • (1 : SpinorMatrix 5) := by
  rw [ellipticRotor10_mul]
  simp only [neg_mul, sub_neg_eq_add]
  module

theorem hyperbolicRotor45_reverse_mul (a b : ℝ) :
    hyperbolicRotor45 a (-b) * hyperbolicRotor45 a b =
      (a ^ 2 - b ^ 2) • (1 : SpinorMatrix 5) := by
  rw [hyperbolicRotor45_mul]
  simp only [neg_mul, sub_neg_eq_add]
  module

theorem ellipticRotor10_commutes_axis (a b : ℝ) :
    ellipticRotor10 a b * rotationBivector10 =
      rotationBivector10 * ellipticRotor10 a b := by
  unfold ellipticRotor10
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]

theorem hyperbolicRotor45_commutes_axis (a b : ℝ) :
    hyperbolicRotor45 a b * mixedBivector45 =
      mixedBivector45 * hyperbolicRotor45 a b := by
  unfold hyperbolicRotor45
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]

theorem ellipticRotor10_conjugate_axis (a b : ℝ) :
    ellipticRotor10 a b * rotationBivector10 *
        ellipticRotor10 a (-b) =
      (a ^ 2 + b ^ 2) • rotationBivector10 := by
  calc
    ellipticRotor10 a b * rotationBivector10 * ellipticRotor10 a (-b) =
        rotationBivector10 * ellipticRotor10 a b *
          ellipticRotor10 a (-b) := by
            rw [ellipticRotor10_commutes_axis]
    _ = rotationBivector10 *
          ((a ^ 2 + b ^ 2) • (1 : SpinorMatrix 5)) := by
            rw [mul_assoc, ellipticRotor10_reverse]
    _ = (a ^ 2 + b ^ 2) • rotationBivector10 := by
            simp [mul_smul_comm]

theorem hyperbolicRotor45_conjugate_axis (a b : ℝ) :
    hyperbolicRotor45 a b * mixedBivector45 *
        hyperbolicRotor45 a (-b) =
      (a ^ 2 - b ^ 2) • mixedBivector45 := by
  calc
    hyperbolicRotor45 a b * mixedBivector45 * hyperbolicRotor45 a (-b) =
        mixedBivector45 * hyperbolicRotor45 a b *
          hyperbolicRotor45 a (-b) := by
            rw [hyperbolicRotor45_commutes_axis]
    _ = mixedBivector45 *
          ((a ^ 2 - b ^ 2) • (1 : SpinorMatrix 5)) := by
            rw [mul_assoc, hyperbolicRotor45_reverse]
    _ = (a ^ 2 - b ^ 2) • mixedBivector45 := by
            simp [mul_smul_comm]

theorem ellipticRotor10_circle_axis_invariant (θ : ℝ) :
    ellipticRotor10 (Real.cos θ) (Real.sin θ) * rotationBivector10 *
        ellipticRotor10 (Real.cos θ) (-Real.sin θ) =
      rotationBivector10 := by
  rw [ellipticRotor10_conjugate_axis, Real.cos_sq_add_sin_sq, one_smul]

theorem hyperbolicRotor45_boost_axis_invariant (η : ℝ) :
    hyperbolicRotor45 (Real.cosh η) (Real.sinh η) * mixedBivector45 *
        hyperbolicRotor45 (Real.cosh η) (-Real.sinh η) =
      mixedBivector45 := by
  rw [hyperbolicRotor45_conjugate_axis, Real.cosh_sq_sub_sinh_sq, one_smul]

theorem ellipticRotor10_mul_reverse_of_norm (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) :
    ellipticRotor10 a b * ellipticRotor10 a (-b) =
      (1 : SpinorMatrix 5) := by
  rw [ellipticRotor10_reverse, h, one_smul]

theorem hyperbolicRotor45_mul_reverse_of_norm (a b : ℝ)
    (h : a ^ 2 - b ^ 2 = 1) :
    hyperbolicRotor45 a b * hyperbolicRotor45 a (-b) =
      (1 : SpinorMatrix 5) := by
  rw [hyperbolicRotor45_reverse, h, one_smul]

theorem ellipticRotor10_circle_unit (θ : ℝ) :
    ellipticRotor10 (Real.cos θ) (Real.sin θ) *
        ellipticRotor10 (Real.cos θ) (-Real.sin θ) =
      (1 : SpinorMatrix 5) := by
  apply ellipticRotor10_mul_reverse_of_norm
  exact Real.cos_sq_add_sin_sq θ

theorem hyperbolicRotor45_boost_unit (η : ℝ) :
    hyperbolicRotor45 (Real.cosh η) (Real.sinh η) *
        hyperbolicRotor45 (Real.cosh η) (-Real.sinh η) =
      (1 : SpinorMatrix 5) := by
  apply hyperbolicRotor45_mul_reverse_of_norm
  exact Real.cosh_sq_sub_sinh_sq η

theorem ellipticRotor10_circle_add (θ φ : ℝ) :
    ellipticRotor10 (Real.cos θ) (Real.sin θ) *
        ellipticRotor10 (Real.cos φ) (Real.sin φ) =
      ellipticRotor10 (Real.cos (θ + φ)) (Real.sin (θ + φ)) := by
  rw [ellipticRotor10_mul, ellipticRotor10]
  rw [Real.cos_add, Real.sin_add]
  module

theorem hyperbolicRotor45_boost_add (η ξ : ℝ) :
    hyperbolicRotor45 (Real.cosh η) (Real.sinh η) *
        hyperbolicRotor45 (Real.cosh ξ) (Real.sinh ξ) =
      hyperbolicRotor45 (Real.cosh (η + ξ)) (Real.sinh (η + ξ)) := by
  rw [hyperbolicRotor45_mul, hyperbolicRotor45]
  rw [Real.cosh_add, Real.sinh_add]
  module

theorem spinorRepresentation_cliffordEllipticRotor10_circle_add (θ φ : ℝ) :
    (spinorRepresentation 5)
        (cliffordEllipticRotor10 (Real.cos θ) (Real.sin θ) *
          cliffordEllipticRotor10 (Real.cos φ) (Real.sin φ)) =
      ellipticRotor10 (Real.cos (θ + φ)) (Real.sin (θ + φ)) := by
  rw [map_mul, spinorRepresentation_cliffordEllipticRotor10,
    spinorRepresentation_cliffordEllipticRotor10,
    ellipticRotor10_circle_add]

theorem spinorRepresentation_cliffordHyperbolicRotor45_boost_add (η ξ : ℝ) :
    (spinorRepresentation 5)
        (cliffordHyperbolicRotor45 (Real.cosh η) (Real.sinh η) *
          cliffordHyperbolicRotor45 (Real.cosh ξ) (Real.sinh ξ)) =
      hyperbolicRotor45 (Real.cosh (η + ξ)) (Real.sinh (η + ξ)) := by
  rw [map_mul, spinorRepresentation_cliffordHyperbolicRotor45,
    spinorRepresentation_cliffordHyperbolicRotor45,
    hyperbolicRotor45_boost_add]

theorem ellipticRotor10_circle_zero :
    ellipticRotor10 (Real.cos 0) (Real.sin 0) =
      (1 : SpinorMatrix 5) := by
  simp [ellipticRotor10]

theorem hyperbolicRotor45_boost_zero :
    hyperbolicRotor45 (Real.cosh 0) (Real.sinh 0) =
      (1 : SpinorMatrix 5) := by
  simp [hyperbolicRotor45]

theorem ellipticRotor10_circle_neg (θ : ℝ) :
    ellipticRotor10 (Real.cos (-θ)) (Real.sin (-θ)) =
      ellipticRotor10 (Real.cos θ) (-Real.sin θ) := by
  simp [Real.cos_neg, Real.sin_neg]

theorem hyperbolicRotor45_boost_neg (η : ℝ) :
    hyperbolicRotor45 (Real.cosh (-η)) (Real.sinh (-η)) =
      hyperbolicRotor45 (Real.cosh η) (-Real.sinh η) := by
  simp [Real.cosh_neg, Real.sinh_neg]

theorem spinorRepresentation_cliffordEllipticRotor10_circle_neg (θ : ℝ) :
    (spinorRepresentation 5)
        (cliffordEllipticRotor10 (Real.cos (-θ)) (Real.sin (-θ))) =
      ellipticRotor10 (Real.cos θ) (-Real.sin θ) := by
  rw [spinorRepresentation_cliffordEllipticRotor10,
    ellipticRotor10_circle_neg]

theorem spinorRepresentation_cliffordHyperbolicRotor45_boost_neg (η : ℝ) :
    (spinorRepresentation 5)
        (cliffordHyperbolicRotor45 (Real.cosh (-η)) (Real.sinh (-η))) =
      hyperbolicRotor45 (Real.cosh η) (-Real.sinh η) := by
  rw [spinorRepresentation_cliffordHyperbolicRotor45,
    hyperbolicRotor45_boost_neg]

end

end InfoGeometry.Clifford.Cl55ConcreteBivectorSignature
