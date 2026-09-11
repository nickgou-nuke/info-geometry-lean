import InfoGeometry.Physics.ConnesDiracOperatorFromBdG
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The operator carrier as a transported `2 × 2` matrix algebra

`OperatorZornMatrix` is a four-entry presentation of an ordinary chiral
block matrix.  All ring operations below are transported from Mathlib's
matrix operations; no separate Zorn multiplication is asserted here.
-/

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

namespace OperatorZornMatrix

abbrev Mat2 (A : Type*) := Matrix (Fin 2) (Fin 2) A

def toMatrix (M : OperatorZornMatrix A) : Mat2 A :=
  !![M.n_plus_op, M.sigma_plus_op; M.sigma_minus_op, M.n_minus_op]

def ofMatrix (M : Mat2 A) : OperatorZornMatrix A where
  n_plus_op := M 0 0
  n_minus_op := M 1 1
  sigma_plus_op := M 0 1
  sigma_minus_op := M 1 0

def equivMatrix : OperatorZornMatrix A ≃ Mat2 A where
  toFun := toMatrix
  invFun := ofMatrix
  left_inv := by
    intro M
    cases M
    rfl
  right_inv := by
    intro M
    funext i j
    fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem equivMatrix_apply (M : OperatorZornMatrix A) :
    equivMatrix M = toMatrix M := rfl

noncomputable instance : Ring (OperatorZornMatrix A) :=
  Equiv.ring (equivMatrix (A := A))

noncomputable def ringEquivMatrix :
    OperatorZornMatrix A ≃+* Mat2 A :=
  Equiv.ringEquiv (equivMatrix (A := A))

@[simp] theorem toMatrix_zero :
    toMatrix (0 : OperatorZornMatrix A) = 0 := by
  exact (ringEquivMatrix (A := A)).map_zero

@[simp] theorem toMatrix_one :
    toMatrix (1 : OperatorZornMatrix A) = 1 := by
  exact (ringEquivMatrix (A := A)).map_one

@[simp] theorem toMatrix_add (M N : OperatorZornMatrix A) :
    toMatrix (M + N) = toMatrix M + toMatrix N := by
  exact (ringEquivMatrix (A := A)).map_add M N

@[simp] theorem toMatrix_neg (M : OperatorZornMatrix A) :
    toMatrix (-M) = -toMatrix M := by
  exact (ringEquivMatrix (A := A)).map_neg M

@[simp] theorem toMatrix_sub (M N : OperatorZornMatrix A) :
    toMatrix (M - N) = toMatrix M - toMatrix N := by
  exact (ringEquivMatrix (A := A)).map_sub M N

@[simp] theorem toMatrix_mul (M N : OperatorZornMatrix A) :
    toMatrix (M * N) = toMatrix M * toMatrix N := by
  exact (ringEquivMatrix (A := A)).map_mul M N

/-! ### Entrywise Nambu--Gorkov/Zorn multiplication

The product is the transported ordinary `2 × 2` matrix product.  These
lemmas expose its four operator-coordinate formulas without introducing a
second multiplication on the carrier.
-/

@[simp] theorem mul_n_plus_op (M N : OperatorZornMatrix A) :
    (M * N).n_plus_op =
      M.n_plus_op * N.n_plus_op + M.sigma_plus_op * N.sigma_minus_op := by
  change (ofMatrix (toMatrix M * toMatrix N)).n_plus_op = _
  simp [ofMatrix, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem mul_sigma_plus_op (M N : OperatorZornMatrix A) :
    (M * N).sigma_plus_op =
      M.n_plus_op * N.sigma_plus_op + M.sigma_plus_op * N.n_minus_op := by
  change (ofMatrix (toMatrix M * toMatrix N)).sigma_plus_op = _
  simp [ofMatrix, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem mul_sigma_minus_op (M N : OperatorZornMatrix A) :
    (M * N).sigma_minus_op =
      M.sigma_minus_op * N.n_plus_op + M.n_minus_op * N.sigma_minus_op := by
  change (ofMatrix (toMatrix M * toMatrix N)).sigma_minus_op = _
  simp [ofMatrix, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem mul_n_minus_op (M N : OperatorZornMatrix A) :
    (M * N).n_minus_op =
      M.sigma_minus_op * N.sigma_plus_op + M.n_minus_op * N.n_minus_op := by
  change (ofMatrix (toMatrix M * toMatrix N)).n_minus_op = _
  simp [ofMatrix, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The concrete Nambu--Gorkov square

The following is an identity in the transported matrix algebra.  It is kept
here, rather than in the non-associative canonical Zorn owner, because the
right-hand side uses the ordinary associative product on the four-entry
carrier.
-/

@[simp] theorem dirac_mul_dirac (Delta : A) :
    InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.diracOperator Delta =
      (⟨Delta * star Delta, star Delta * Delta, 0, 0⟩ :
        OperatorZornMatrix A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (_ * _) = toMatrix
    (⟨Delta * star Delta, star Delta * Delta, 0, 0⟩ :
      OperatorZornMatrix A)
  rw [Equiv.mul_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NCG.diracOperator, toMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, equivMatrix, ofMatrix]

@[simp] theorem dirac_square_n_plus (Delta : A) :
    (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta).n_plus_op =
      Delta * star Delta := by
  simp [dirac_mul_dirac]

@[simp] theorem dirac_square_n_minus (Delta : A) :
    (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta).n_minus_op =
      star Delta * Delta := by
  simp [dirac_mul_dirac]

@[simp] theorem ofMatrix_toMatrix (M : OperatorZornMatrix A) :
    ofMatrix (toMatrix M) = M := (equivMatrix (A := A)).left_inv M

@[simp] theorem toMatrix_ofMatrix (M : Mat2 A) :
    toMatrix (ofMatrix M) = M := (equivMatrix (A := A)).right_inv M

@[simp] theorem equivMatrix_symm_apply (M : Mat2 A) :
    (equivMatrix (A := A)).symm M = ofMatrix M := rfl

def starOp (M : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ofMatrix (star (toMatrix M))

instance : Star (OperatorZornMatrix A) := ⟨starOp⟩

@[simp] theorem star_eq_starOp (M : OperatorZornMatrix A) :
    star M = starOp M := rfl

@[simp] theorem toMatrix_starOp (M : OperatorZornMatrix A) :
    toMatrix (starOp M) = star (toMatrix M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [starOp, ofMatrix, toMatrix, Matrix.star_apply]

/-! The coordinate action of the transported conjugate transpose.  The two
diagonal channels are starred in place, while the off-diagonal channels are
starred and exchanged. -/

@[simp] theorem star_n_plus_op (M : OperatorZornMatrix A) :
    (star M).n_plus_op = star M.n_plus_op := by
  change (starOp M).n_plus_op = star M.n_plus_op
  simp [starOp, ofMatrix, toMatrix, Matrix.star_apply]

@[simp] theorem star_n_minus_op (M : OperatorZornMatrix A) :
    (star M).n_minus_op = star M.n_minus_op := by
  change (starOp M).n_minus_op = star M.n_minus_op
  simp [starOp, ofMatrix, toMatrix, Matrix.star_apply]

@[simp] theorem star_sigma_plus_op (M : OperatorZornMatrix A) :
    (star M).sigma_plus_op = star M.sigma_minus_op := by
  change (starOp M).sigma_plus_op = star M.sigma_minus_op
  simp [starOp, ofMatrix, toMatrix, Matrix.star_apply]

@[simp] theorem star_sigma_minus_op (M : OperatorZornMatrix A) :
    (star M).sigma_minus_op = star M.sigma_plus_op := by
  change (starOp M).sigma_minus_op = star M.sigma_plus_op
  simp [starOp, ofMatrix, toMatrix, Matrix.star_apply]

/-! Coordinate consequences of the Nambu--Gorkov square.  Keeping the
off-diagonal zero laws explicit makes the even/odd block separation
available without reproving the full matrix identity. -/

@[simp] theorem dirac_square_sigma_plus (Delta : A) :
    (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta).sigma_plus_op = 0 := by
  simp [dirac_mul_dirac]

@[simp] theorem dirac_square_sigma_minus (Delta : A) :
    (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta).sigma_minus_op = 0 := by
  simp [dirac_mul_dirac]

instance : StarRing (OperatorZornMatrix A) where
  star_involutive := by
    intro M
    apply (equivMatrix (A := A)).injective
    change toMatrix (starOp (starOp M)) = toMatrix M
    rw [toMatrix_starOp, toMatrix_starOp]
    exact star_star _
  star_mul := by
    intro M N
    apply (equivMatrix (A := A)).injective
    change toMatrix (starOp (M * N)) =
      toMatrix (starOp N * starOp M)
    simpa only [star_eq_starOp, equivMatrix_apply, toMatrix_starOp, Equiv.mul_def,
      equivMatrix_symm_apply, toMatrix_ofMatrix] using
      (Matrix.star_mul (toMatrix M) (toMatrix N))
  star_add := by
    intro M N
    apply (equivMatrix (A := A)).injective
    change toMatrix (starOp (M + N)) =
      toMatrix (starOp M + starOp N)
    simpa only [star_eq_starOp, equivMatrix_apply, toMatrix_starOp, Equiv.add_def,
      equivMatrix_symm_apply, toMatrix_ofMatrix] using
      (StarAddMonoid.star_add (toMatrix M) (toMatrix N))

@[simp] theorem starOp_starOp (M : OperatorZornMatrix A) :
    starOp (starOp M) = M := by
  apply (equivMatrix (A := A)).injective
  simp [starOp]

@[simp] theorem dirac_self_adjoint_native (Delta : A) :
    star (InfoGeometry.Physics.NCG.diracOperator Delta) =
      InfoGeometry.Physics.NCG.diracOperator Delta := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (starOp (InfoGeometry.Physics.NCG.diracOperator Delta)) =
    toMatrix (InfoGeometry.Physics.NCG.diracOperator Delta)
  rw [toMatrix_starOp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NCG.diracOperator, toMatrix, Matrix.star_apply]

/-! The positive block square inherits self-adjointness from the Dirac
operator; this is the finite algebraic input for spectral/Gram readouts. -/

@[simp] theorem dirac_square_self_adjoint_native (Delta : A) :
    star (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta) =
      InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.diracOperator Delta := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (starOp
      (InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.diracOperator Delta)) =
    toMatrix (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta)
  rw [toMatrix_starOp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NCG.diracOperator, toMatrix, starOp,
      Matrix.star_apply, star_mul]

@[simp] theorem dirac_anticommutes_with_chirality_native (Delta : A) :
    InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.chiralGradingOperator +
      InfoGeometry.Physics.NCG.chiralGradingOperator *
        InfoGeometry.Physics.NCG.diracOperator Delta = 0 := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (_ + _) = toMatrix (0 : OperatorZornMatrix A)
  rw [Equiv.add_def, Equiv.mul_def, Equiv.mul_def, Equiv.zero_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NCG.diracOperator,
      InfoGeometry.Physics.NCG.chiralGradingOperator, toMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, equivMatrix, ofMatrix]

@[simp] theorem chiral_grading_sq_native :
    InfoGeometry.Physics.NCG.chiralGradingOperator *
        InfoGeometry.Physics.NCG.chiralGradingOperator =
      (⟨1, 1, 0, 0⟩ : OperatorZornMatrix A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (_ * _) = toMatrix (⟨1, 1, 0, 0⟩ : OperatorZornMatrix A)
  rw [Equiv.mul_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NCG.chiralGradingOperator, toMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, equivMatrix, ofMatrix]

/-- The square of an odd Dirac block is even for the chiral grading. -/
theorem dirac_square_commutes_with_chirality_native (Delta : A) :
    (InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.diracOperator Delta) *
        InfoGeometry.Physics.NCG.chiralGradingOperator =
      InfoGeometry.Physics.NCG.chiralGradingOperator *
        (InfoGeometry.Physics.NCG.diracOperator Delta *
          InfoGeometry.Physics.NCG.diracOperator Delta) := by
  let D : OperatorZornMatrix A :=
    InfoGeometry.Physics.NCG.diracOperator Delta
  let Gamma : OperatorZornMatrix A :=
    InfoGeometry.Physics.NCG.chiralGradingOperator
  have hodd : D * Gamma + Gamma * D = 0 := by
    simpa [D, Gamma] using dirac_anticommutes_with_chirality_native Delta
  have hswap : D * Gamma = -(Gamma * D) := by
    exact eq_neg_of_add_eq_zero_left hodd
  have hsq : D * D * Gamma = Gamma * (D * D) := by
    calc
      D * D * Gamma = D * (D * Gamma) := by rw [mul_assoc]
      _ = D * (-(Gamma * D)) := by rw [hswap]
      _ = -(D * Gamma) * D := by noncomm_ring
      _ = -(-(Gamma * D)) * D := by rw [hswap]
      _ = Gamma * (D * D) := by noncomm_ring
  simpa [D, Gamma] using hsq

/-! ## Hestenes--Krein product of phase and grading -/

/-- Product of a phase operator and a grading involution. -/
def kreinSymmetry (K Gamma : A) : A := K * Gamma

/-- An anticommuting skew phase and self-adjoint grading produce a
self-adjoint Krein fundamental symmetry. -/
theorem kreinSymmetry_star_eq
    (K Gamma : A)
    (hKstar : star K = -K)
    (hGstar : star Gamma = Gamma)
    (hanti : K * Gamma = -(Gamma * K)) :
    star (kreinSymmetry K Gamma) = kreinSymmetry K Gamma := by
  rw [kreinSymmetry, star_mul, hGstar, hKstar]
  calc
    Gamma * -K = -(Gamma * K) := by rw [mul_neg]
    _ = K * Gamma := by rw [hanti]

/-- The square of the Krein fundamental symmetry is the identity. -/
theorem kreinSymmetry_sq
    (K Gamma : A)
    (hKsq : K * K = -1)
    (hGsq : Gamma * Gamma = 1)
    (hanti : K * Gamma = -(Gamma * K)) :
    kreinSymmetry K Gamma * kreinSymmetry K Gamma = 1 := by
  rw [kreinSymmetry]
  have hanti' : Gamma * K = -(K * Gamma) := by
    rw [hanti]
    simp
  calc
    K * Gamma * (K * Gamma) = K * (Gamma * K) * Gamma := by
      noncomm_ring
    _ = K * (-(K * Gamma)) * Gamma := by rw [hanti']
    _ = -(K * K) * (Gamma * Gamma) := by noncomm_ring
    _ = 1 := by rw [hKsq, hGsq]; simp

end OperatorZornMatrix

end InfoGeometry.Physics
