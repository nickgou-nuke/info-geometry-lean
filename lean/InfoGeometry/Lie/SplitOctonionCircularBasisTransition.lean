/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
import InfoGeometry.Lie.SplitOctonionCircularZ3Grading
import InfoGeometry.Lie.SplitOctonionFureyOperatorLift

/-!
# Change of coordinates between the two circular split-octonion bases

Both frames are bases of the same canonical Zorn vector space, but they use
different Peirce idempotents.  This file constructs their actual linear basis
change and records how native multiplication operators transport through it.
The map is not asserted to preserve multiplication: the octonion carrier is
nonassociative, and a basis change alone is only linear.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Lie.SplitOctonionCircularBasisTransition

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

open InfoGeometry.Algebra.FiniteSpin (Vec8R)

/-- The regular split-octonion `J` operator expressed on the legacy
eight-coordinate carrier. -/
def legacyRegularJOperator : Module.End ℝ Vec8R :=
  InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
    (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)

/-- Vec8R of a native Zorn element in the diagonal `zornPlus/zornMinus`
frame. -/
def legacyCoordinates : CZ ≃ₗ[ℝ] Vec8R :=
  InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun

/-- The exact change of coordinates from the Ell `uPlus/uMinus` frame to the
legacy `zornPlus/zornMinus` frame.  This is a linear equivalence of vector
spaces, not an algebra equivalence. -/
def ellToLegacy : Vec8R ≃ₗ[ℝ] Vec8R :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.symm.trans
    legacyCoordinates

/-- Native split-octonion multiplication expressed in Ell coordinates.  The
product is transported from the Zorn carrier; no associative replacement is
introduced. -/
def ellCoordinateProduct (x y : Vec8R) : Vec8R :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.symm x *
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.symm y)

/-- The same native split-octonion multiplication expressed in legacy
`zornPlus/zornMinus` coordinates. -/
def legacyCoordinateProduct (x y : Vec8R) : Vec8R :=
  legacyCoordinates (legacyCoordinates.symm x * legacyCoordinates.symm y)

/-- The explicit Ell-to-legacy transition is an algebra isomorphism between
the two transported coordinate products.  This statement concerns the
products transported from the nonassociative Zorn carrier, not pointwise
coordinate multiplication. -/
theorem ellToLegacy_preserves_native_product (x y : Vec8R) :
    ellToLegacy (ellCoordinateProduct x y) =
      legacyCoordinateProduct (ellToLegacy x) (ellToLegacy y) := by
  let e := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
  change legacyCoordinates (e.symm (e (e.symm x * e.symm y))) =
    legacyCoordinates (legacyCoordinates.symm (ellToLegacy x) *
      legacyCoordinates.symm (ellToLegacy y))
  have hx : legacyCoordinates.symm (ellToLegacy x) = e.symm x := by
    change legacyCoordinates.symm (legacyCoordinates (e.symm x)) = e.symm x
    simp
  have hy : legacyCoordinates.symm (ellToLegacy y) = e.symm y := by
    change legacyCoordinates.symm (legacyCoordinates (e.symm y)) = e.symm y
    simp
  rw [e.symm_apply_apply, hx, hy]

/-- The split-octonion associator in Ell coordinates, formed using the
transported native product. -/
def ellCoordinateAssociator (x y z : Vec8R) : Vec8R :=
  ellCoordinateProduct (ellCoordinateProduct x y) z -
    ellCoordinateProduct x (ellCoordinateProduct y z)

/-- The same associator in legacy circular coordinates. -/
def legacyCoordinateAssociator (x y z : Vec8R) : Vec8R :=
  legacyCoordinateProduct (legacyCoordinateProduct x y) z -
    legacyCoordinateProduct x (legacyCoordinateProduct y z)

/-- Soldering the two coordinate carriers preserves the full associator
defect, so the basis transition cannot turn the native nonassociative product
into an associative one. -/
theorem ellToLegacy_preserves_associator (x y z : Vec8R) :
    ellToLegacy (ellCoordinateAssociator x y z) =
      legacyCoordinateAssociator (ellToLegacy x) (ellToLegacy y)
        (ellToLegacy z) := by
  change ellToLegacy
      (ellCoordinateProduct (ellCoordinateProduct x y) z -
        ellCoordinateProduct x (ellCoordinateProduct y z)) = _
  rw [map_sub,
    ellToLegacy_preserves_native_product (ellCoordinateProduct x y) z,
    ellToLegacy_preserves_native_product x (ellCoordinateProduct y z),
    ellToLegacy_preserves_native_product x y,
    ellToLegacy_preserves_native_product y z]
  rfl

/-- The Ell basis triple `rootPlus 0, rootPlus 1, rootPlus 2` has the
nonzero native split-octonion associator, expressed in Ell coordinates. -/
theorem ellCoordinateAssociator_rootPlus_basis :
    ellCoordinateAssociator
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1))
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2)) =
    InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
      (InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus -
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus) := by
  let e := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
  change ellCoordinateAssociator
      (e (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
      (e (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1))
      (e (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2)) =
    e (InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus -
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus)
  simp [e, ellCoordinateAssociator, ellCoordinateProduct]
  rw [← map_sub]
  exact congrArg e
    InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_associator_zero_one_two

/-- The transported `rootPlus` basis associator remains nonzero in Ell
coordinates, certified by the frame-coordinate values of the complementary
Peirce idempotents. -/
theorem ellCoordinateAssociator_rootPlus_basis_ne_zero :
    ellCoordinateAssociator
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1))
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2)) ≠ 0 := by
  rw [ellCoordinateAssociator_rootPlus_basis]
  intro h
  let e := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
  have huPlus : e InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus =
      (Pi.single 0 (1 : ℝ) : Vec8R) := by
    simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_apply_frame 0
  have huMinus : e InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus =
      (Pi.single 4 (1 : ℝ) : Vec8R) := by
    simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_apply_frame 4
  have h0 := congrFun h 0
  rw [map_sub, huMinus, huPlus] at h0
  norm_num [Pi.single_apply] at h0

/-- The same explicit nonzero associator witness holds after soldering into
legacy circular coordinates. -/
theorem legacyCoordinateAssociator_rootPlus_basis_ne_zero :
    legacyCoordinateAssociator
      (ellToLegacy
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
          (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0)))
      (ellToLegacy
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
          (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1)))
      (ellToLegacy
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
          (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2))) ≠ 0 := by
  intro hzero
  have htransport := ellToLegacy_preserves_associator
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1))
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2))
  have hEllZero : ellCoordinateAssociator
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1))
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2)) = 0 := by
    apply ellToLegacy.injective
    rw [htransport, hzero]
    simp
  exact ellCoordinateAssociator_rootPlus_basis_ne_zero hEllZero

/-- Explicit columns of the Ell-to-legacy transition.  The coefficients are
in the legacy order `(a, x₀, x₁, x₂, b, y₀, y₁, y₂)`. -/
def transitionColumn (j : Fin 8) : Vec8R :=
  match j.val with
  | 0 => fun i => if i.val = 0 ∨ i.val = 1 ∨ i.val = 4 ∨ i.val = 5 then 1 / 2 else 0
  | 1 => fun i => if i.val = 0 ∨ i.val = 5 then -(1 / 2)
      else if i.val = 1 ∨ i.val = 4 then 1 / 2 else 0
  | 2 => fun i => if i.val = 2 ∨ i.val = 3 then 1 / 2
      else if i.val = 6 then -(1 / 2) else if i.val = 7 then 1 / 2 else 0
  | 3 => fun i => if i.val = 2 ∨ i.val = 6 ∨ i.val = 7 then -(1 / 2)
      else if i.val = 3 then 1 / 2 else 0
  | 4 => fun i => if i.val = 1 ∨ i.val = 5 then -(1 / 2)
      else if i.val = 0 ∨ i.val = 4 then 1 / 2 else 0
  | 5 => fun i => if i.val = 0 ∨ i.val = 1 then -(1 / 2)
      else if i.val = 4 ∨ i.val = 5 then 1 / 2 else 0
  | 6 => fun i => if i.val = 2 then -(1 / 2)
      else if i.val = 3 ∨ i.val = 6 ∨ i.val = 7 then 1 / 2 else 0
  | 7 => fun i => if i.val = 2 ∨ i.val = 3 ∨ i.val = 6 then -(1 / 2)
      else if i.val = 7 then 1 / 2 else 0
  | _ => 0

/-- Entrywise computation of the basis-change columns from the canonical
Zorn product.  In particular, the Ell sectors are not coordinatewise the
legacy sectors: these columns exhibit the scalar/vector mixing and the
cyclic permutation of the three root directions. -/
theorem ellToLegacy_single_eq_transitionColumn (j : Fin 8) :
    ellToLegacy (Pi.single j (1 : ℝ)) = transitionColumn j := by
  have hframe : ellToLegacy (Pi.single j (1 : ℝ)) =
      legacyCoordinates
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame j) := by
    simp [ellToLegacy]
  rw [hframe]
  rw [legacyCoordinates,
    ← InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_coordinate_eq_equivFun]
  fin_cases j <;> funext i <;> fin_cases i <;>
    norm_num [transitionColumn,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularCoordinate,
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame,
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus,
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus,
      InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus,
      InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.chiralNull,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.ellBasis,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.quaternionBasis,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.jUnit,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.kQuaternionUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, smul_eq_mul]

/-- Each genuine Ell frame vector expressed in legacy circular coordinates
equals the corresponding explicit `transitionColumn`. -/
theorem ell_frame_transition_column (j : Fin 8) :
    legacyCoordinates
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame j) =
      transitionColumn j := by
  have hframe :
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame j) =
      (Pi.single j (1 : ℝ) : Vec8R) :=
    InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_apply_frame j
  calc legacyCoordinates
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame j)
      = ellToLegacy
          (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
            (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame j)) := by
          change _ = legacyCoordinates
            (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.symm
              (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
                (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame j)))
          rw [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.symm_apply_apply]
    _ = ellToLegacy (Pi.single j (1 : ℝ)) := by rw [hframe]
    _ = transitionColumn j := ellToLegacy_single_eq_transitionColumn j

/-- The concrete `8 × 8` change-of-basis matrix, with columns indexed by the
Ell input frame and rows by the legacy output frame. -/
noncomputable def ellToLegacyMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) ellToLegacy

/-- Every matrix entry is the corresponding explicit transition-column
coefficient computed from the two native Zorn bases. -/
theorem ellToLegacyMatrix_apply (i j : Fin 8) :
    ellToLegacyMatrix i j = transitionColumn j i := by
  rw [ellToLegacyMatrix, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr]
  change ellToLegacy (Pi.single j (1 : ℝ)) i = _
  rw [ellToLegacy_single_eq_transitionColumn]

/-- The explicit transition matrix acts on every legacy-coordinate vector
as the abstract Ell-to-legacy linear equivalence.  This upgrades the column
calculation to an operator-level coordinate transport formula. -/
theorem ellToLegacyMatrix_mulVec (x : Vec8R) :
    Matrix.mulVec ellToLegacyMatrix x = ellToLegacy x := by
  exact LinearMap.toMatrix_mulVec_repr
    (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) ellToLegacy x

/-- The explicit frame change is orthogonal for the standard coordinate inner
product: its eight columns form an orthonormal basis. -/
theorem ellToLegacyMatrix_orthogonal :
    Matrix.transpose ellToLegacyMatrix * ellToLegacyMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, ellToLegacyMatrix_apply,
      transitionColumn] <;> norm_num

/-- Matrix of the reverse transition, from legacy coordinates to Ell
coordinates. -/
noncomputable def legacyToEllMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) ellToLegacy.symm

/-- The two concrete frame-transition matrices are mutual inverses.  This
records invertibility at the coordinate-matrix level, in addition to the
abstract `LinearEquiv` witness. -/
theorem transition_matrices_are_inverses :
    legacyToEllMatrix * ellToLegacyMatrix = 1 ∧
    ellToLegacyMatrix * legacyToEllMatrix = 1 := by
  constructor
  · rw [legacyToEllMatrix, ellToLegacyMatrix, ← LinearMap.toMatrix_comp]
    have hcomp : ellToLegacy.symm.toLinearMap.comp ellToLegacy.toLinearMap = LinearMap.id := by
      ext x
      simp [ellToLegacy]
    rw [hcomp, LinearMap.toMatrix_id]
  · rw [legacyToEllMatrix, ellToLegacyMatrix, ← LinearMap.toMatrix_comp]
    have hcomp : ellToLegacy.toLinearMap.comp ellToLegacy.symm.toLinearMap = LinearMap.id := by
      ext x
      simp [ellToLegacy]
    rw [hcomp, LinearMap.toMatrix_id]

/-- Since the transition columns are orthonormal, the reverse coordinate
matrix is exactly the transpose of the forward matrix. -/
theorem legacyToEllMatrix_eq_transpose :
    legacyToEllMatrix = Matrix.transpose ellToLegacyMatrix := by
  have horth := ellToLegacyMatrix_orthogonal
  have hinv := transition_matrices_are_inverses.2
  calc legacyToEllMatrix =
        (Matrix.transpose ellToLegacyMatrix * ellToLegacyMatrix) * legacyToEllMatrix := by
          rw [horth, one_mul]
    _ = Matrix.transpose ellToLegacyMatrix *
        (ellToLegacyMatrix * legacyToEllMatrix) := by rw [Matrix.mul_assoc]
    _ = Matrix.transpose ellToLegacyMatrix := by rw [hinv, mul_one]

/-- Conversely, each legacy frame vector expressed in Ell coordinates equals the
corresponding Ell coordinate readout of `circularPeirceBasis i` and has explicit
components given by the `i`th row of `transitionColumn`. -/
theorem legacy_frame_transition_column (i : Fin 8) :
    ellToLegacy.symm (Pi.single i (1 : ℝ)) =
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i) ∧
    ∀ j : Fin 8, ellToLegacy.symm (Pi.single i (1 : ℝ)) j = transitionColumn j i := by
  refine ⟨by simp [ellToLegacy, legacyCoordinates], ?_⟩
  intro j
  have hmat : legacyToEllMatrix j i = ellToLegacy.symm (Pi.single i (1 : ℝ)) j := by
    rw [legacyToEllMatrix, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
    rfl
  rw [← hmat, legacyToEllMatrix_eq_transpose, Matrix.transpose_apply, ellToLegacyMatrix_apply]

/-- Soldering theorem for the operator algebras: conjugating any endomorphism
of the native split-octonion carrier directly into legacy coordinates agrees
with first transporting it into Ell coordinates and then applying the basis
transition.  Since conjugation is an algebra equivalence, this one theorem
transports all regular tetrad generators and their commutator superoperators
without assuming the octonion multiplication is associative. -/
theorem ellToLegacy_conjugateEnd
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    ellToLegacy.conjAlgEquiv ℝ
        (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate T) =
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout T := by
  change ellToLegacy.conjAlgEquiv ℝ
      (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate T) =
    legacyCoordinates.conjAlgEquiv ℝ T
  apply LinearMap.ext
  intro x
  change ellToLegacy
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (T (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.symm
          (ellToLegacy.symm x)))) =
    legacyCoordinates (T (legacyCoordinates.symm x))
  dsimp only [ellToLegacy, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm]
  rw [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.symm_apply_apply,
    InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.symm_apply_apply]

/-- Evaluation form of operator soldering: apply a native endomorphism in
legacy coordinates to a transported native vector, then read the result as
the transition of its Ell-coordinate action. -/
theorem ellToLegacy_conjugateEnd_apply
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ)
    (x : CZ) :
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout T
        (ellToLegacy
          (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv x)) =
      ellToLegacy
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv (T x)) := by
  have h := congrArg
    (fun U : Module.End ℝ Vec8R => U
      (ellToLegacy
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv x)))
    (ellToLegacy_conjugateEnd T).symm
  simpa [LinearEquiv.conjAlgEquiv_apply,
    InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate]
    using h

/-- The mixed left/right multiplication commutator in legacy coordinates is
exactly the transported negative associator, for every native split-octonion
triple. This is an operator identity on the soldered coordinate carrier, not
an associativity claim about the octonion product. -/
theorem legacy_mixedRegularCommutator_apply_eq_neg_associator
    (x z y : CZ) :
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x *
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z -
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z *
          InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x)
        (ellToLegacy
          (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv y)) =
      -ellToLegacy
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
          (InfoGeometry.Lie.SplitOctonionFureyOperatorLift.splitAssociator x y z)) := by
  let T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
    InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x *
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z -
    InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z *
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x
  change InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout T
      (ellToLegacy
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv y)) = _
  rw [ellToLegacy_conjugateEnd_apply,
    InfoGeometry.Lie.SplitOctonionFureyOperatorLift.regular_commutator_apply_eq_neg_associator]
  simp only [map_neg]

/-- The legacy coordinate readout of the mixed regular commutator vanishes
exactly when its native split-octonion associator vanishes on every input.
This transports the native operator criterion across both coordinate maps. -/
theorem legacy_mixedRegularCommutator_eq_zero_iff_associator_vanishes
    (x z : CZ) :
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x *
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z -
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z *
          InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x) = 0 ↔
      ∀ y : CZ,
        InfoGeometry.Lie.SplitOctonionFureyOperatorLift.splitAssociator x y z = 0 := by
  let C : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ :=
    InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x *
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z -
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z *
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x
  change InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout C = 0 ↔ _
  constructor
  · intro hC
    have hC' : InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout C =
        InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout 0 := by
      simpa using hC
    have hzero : C = 0 :=
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout.injective hC'
    have hcomm :
        InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x *
            InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z =
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z *
            InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x := by
      exact sub_eq_zero.mp (show
        InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x *
            InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z -
            InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z *
              InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x = 0 from hzero)
    exact
      (InfoGeometry.Lie.SplitOctonionFureyOperatorLift.regular_operators_commute_iff_associator_vanishes
        x z).mp hcomm
  · intro hassoc
    have hcomm :=
      (InfoGeometry.Lie.SplitOctonionFureyOperatorLift.regular_operators_commute_iff_associator_vanishes
        x z).mpr hassoc
    have hzero : C = 0 := by
      change InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x *
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z -
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular z *
            InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x = 0
      exact sub_eq_zero.mpr hcomm
    rw [hzero]
    simp

/-- The mixed left/right regular commutator evaluated on a circular root
basis vector is the transported split Cartan axis in the legacy frame. This
connects the native associator witness to an actual operator action in the
second eight-coordinate basis. -/
theorem legacy_rootBasis_mixedRegularCommutator_action :
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0) *
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) -
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) *
          InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
        (ellToLegacy
          (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1))) =
      ellToLegacy
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
          InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) := by
  let x := InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0
  let y := InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1
  let z := InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2
  have hval :
      -(InfoGeometry.Lie.SplitOctonionFureyOperatorLift.splitAssociator x y z) =
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit := by
    have hcomm :=
      InfoGeometry.Lie.SplitOctonionFureyOperatorLift.root_frame_regular_commutator_is_split_axis
    have hdef :=
      InfoGeometry.Lie.SplitOctonionFureyOperatorLift.regular_commutator_apply_eq_neg_associator
        x z y
    rw [hcomm] at hdef
    exact hdef.symm
  rw [legacy_mixedRegularCommutator_apply_eq_neg_associator]
  change -(ellToLegacy
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionFureyOperatorLift.splitAssociator x y z))) =
    ellToLegacy
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit)
  have htransport := congrArg
    (fun q : CZ => ellToLegacy
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv q)) hval
  simpa only [map_neg] using htransport

/-- Fully explicit basis-column form of the preceding operator action: the
mixed regular commutator sends transition column `2` to column `0` minus
column `4`. -/
theorem legacy_rootBasis_mixedRegularCommutator_transition_columns :
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0) *
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) -
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) *
          InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
        (transitionColumn 2) = transitionColumn 0 - transitionColumn 4 := by
  have hrootCoord :
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1) =
      (Pi.single 2 (1 : ℝ) : Vec8R) := by
    simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_apply_frame 2
  have hroot : ellToLegacy
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1)) =
      transitionColumn 2 := by
    rw [hrootCoord, ellToLegacy_single_eq_transitionColumn]
  have hplus :
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus =
      (Pi.single 0 (1 : ℝ) : Vec8R) := by
    simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_apply_frame 0
  have hminus :
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus =
      (Pi.single 4 (1 : ℝ) : Vec8R) := by
    simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_apply_frame 4
  have haxis : ellToLegacy
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) =
      transitionColumn 0 - transitionColumn 4 := by
    rw [← InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus_sub_uMinus,
      map_sub, hplus, hminus, map_sub,
      ellToLegacy_single_eq_transitionColumn 0,
      ellToLegacy_single_eq_transitionColumn 4]
  rw [← hroot, legacy_rootBasis_mixedRegularCommutator_action, haxis]

/-- The explicit legacy-coordinate mixed regular commutator is nonzero as an
endomorphism; its action on transition column `2` separates columns `0` and
`4` (already at legacy coordinate `1`). -/
theorem legacy_rootBasis_mixedRegularCommutator_ne_zero :
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0) *
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) -
          InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) *
          InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0)) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (fun T : Module.End ℝ Vec8R => T (transitionColumn 2)) hzero
  rw [legacy_rootBasis_mixedRegularCommutator_transition_columns] at heval
  have hcoord := congrFun heval 1
  norm_num [transitionColumn] at hcoord

/-- Matrix-level readout of the same basis action: the standard `8 × 8`
matrix of the legacy mixed commutator sends transition column `2` to column
`0` minus column `4`. -/
def legacyRootBasisMixedRegularCommutator : Module.End ℝ Vec8R :=
  InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
    (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0) *
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) -
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) *
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))

theorem legacy_rootBasis_mixedRegularCommutator_matrix_mulVec :
    Matrix.mulVec
      (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
        legacyRootBasisMixedRegularCommutator)
      (transitionColumn 2) = transitionColumn 0 - transitionColumn 4 := by
  let T := legacyRootBasisMixedRegularCommutator
  change (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8))
      (Pi.basisFun ℝ (Fin 8)) T).mulVec (transitionColumn 2) = _
  calc (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8))
        (Pi.basisFun ℝ (Fin 8)) T).mulVec (transitionColumn 2)
      = (Pi.basisFun ℝ (Fin 8)).repr (T (transitionColumn 2)) := by
          exact LinearMap.toMatrix_mulVec_repr
            (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) T
            (transitionColumn 2)
    _ = T (transitionColumn 2) := by
      funext i
      simp
    _ = transitionColumn 0 - transitionColumn 4 :=
      legacy_rootBasis_mixedRegularCommutator_transition_columns

/-- The matrix readout is nonzero, witnessed by the preceding nonzero
matrix-vector output. -/
theorem legacy_rootBasis_mixedRegularCommutator_matrix_ne_zero :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
      legacyRootBasisMixedRegularCommutator ≠ 0 := by
  intro hzero
  have hmul := congrArg
    (fun M : Matrix (Fin 8) (Fin 8) ℝ =>
      Matrix.mulVec M (transitionColumn 2)) hzero
  rw [legacy_rootBasis_mixedRegularCommutator_matrix_mulVec] at hmul
  simp only [Matrix.zero_mulVec] at hmul
  have hcoord := congrFun hmul 1
  norm_num [transitionColumn] at hcoord

/-- The `8 × 8` legacy-coordinate matrix of left regular multiplication by `rootPlus 0`. -/
noncomputable def legacyLeftRootPlus0Matrix : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
    (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0)))

/-- The `8 × 8` legacy-coordinate matrix of right regular multiplication by `rootPlus 2`. -/
noncomputable def legacyRightRootPlus2Matrix : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
    (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2)))

/-- Explicit `8 × 8` matrix non-commutativity witness: the transported left and
right regular split-octonion multiplication matrices fail to commute because
their matrix commutator is the nonzero associator matrix of
`legacyRootBasisMixedRegularCommutator`. -/
theorem legacyLeftRootPlus0Matrix_legacyRightRootPlus2Matrix_not_commute :
    legacyLeftRootPlus0Matrix * legacyRightRootPlus2Matrix ≠
      legacyRightRootPlus2Matrix * legacyLeftRootPlus0Matrix := by
  intro hcomm
  have hsub :
      legacyLeftRootPlus0Matrix * legacyRightRootPlus2Matrix -
        legacyRightRootPlus2Matrix * legacyLeftRootPlus0Matrix = 0 :=
    sub_eq_zero.mpr hcomm
  have hmat :
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
        legacyRootBasisMixedRegularCommutator =
      legacyLeftRootPlus0Matrix * legacyRightRootPlus2Matrix -
        legacyRightRootPlus2Matrix * legacyLeftRootPlus0Matrix := by
    change LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
        legacyRootBasisMixedRegularCommutator = _
    dsimp only [legacyRootBasisMixedRegularCommutator,
      legacyLeftRootPlus0Matrix, legacyRightRootPlus2Matrix]
    rw [map_sub, map_mul, map_mul, map_sub, map_mul, map_mul]
  rw [← hmat] at hsub
  exact legacy_rootBasis_mixedRegularCommutator_matrix_ne_zero hsub

/-- Full action table of the fixed mixed regular commutator on the genuine
Ell circular Peirce frame.  The three zero columns and the four nonzero
columns are computed using the native split-octonion product. -/
theorem ell_rootBasis_mixedRegularCommutator_frame_action (i : Fin 8) :
    (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0) *
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) -
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) *
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) =
      match i.val with
      | 0 => -InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus 1
      | 2 => InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus -
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus
      | 4 => InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus 1
      | 5 => -InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2
      | 7 => InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0
      | _ => 0 := by
  rw [InfoGeometry.Lie.SplitOctonionFureyOperatorLift.regular_commutator_apply_eq_neg_associator]
  fin_cases i <;>
    ext j <;>
    simp [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame,
      InfoGeometry.Lie.SplitOctonionFureyOperatorLift.splitAssociator,
      InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus,
      InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.chiralNull,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.quaternionBasis,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.ellBasis,
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus,
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.jUnit,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.kQuaternionUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordAddEquiv,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv] <;>
    (try fin_cases j) <;> norm_num

/-- The fixed mixed regular commutator as an endomorphism on the native
split-octonion carrier. -/
def ellRootBasisMixedRegularCommutator : Module.End ℝ CZ :=
  InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0) *
    InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) -
    InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) *
    InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0)

/-- Coordinate expression of the mixed commutator in the Ell circular frame. -/
def ellRootBasisMixedRegularCommutatorFormula : Module.End ℝ CZ :=
  (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 4 -
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 0).smulRight
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 6) +
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 2).smulRight
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 0 -
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 4) -
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 5).smulRight
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 3) +
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 7).smulRight
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 1)

/-- The frame action table determines the mixed commutator on the entire
native split-octonion carrier. -/
theorem ell_rootBasis_mixedRegularCommutator_eq_coordinate_formula :
    ellRootBasisMixedRegularCommutator =
      ellRootBasisMixedRegularCommutatorFormula := by
  let b := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis
  apply LinearMap.ext_on b.span_eq
  rintro x ⟨i, rfl⟩
  change ellRootBasisMixedRegularCommutator (b i) =
    ellRootBasisMixedRegularCommutatorFormula (b i)
  rw [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis_apply]
  change (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0) *
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) -
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) *
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) = _
  rw [ell_rootBasis_mixedRegularCommutator_frame_action i]
  have hc : ∀ j : Fin 8,
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord j
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) =
        if i = j then 1 else 0 := by
    intro j
    rw [← InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis_apply,
      Module.Basis.coord_apply]
    exact InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.repr_self_apply i j
  simp only [ellRootBasisMixedRegularCommutatorFormula, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smulRight_apply]
  simp only [hc]
  fin_cases i <;> ext <;>
    simp [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame]

/-- The Ell circular dual basis reads the Kronecker coordinates of its frame. -/
lemma ellCircularBasis_coord_frame (i j : Fin 8) :
    InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord i
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame j) =
        if j = i then 1 else 0 := by
  rw [← InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis_apply,
    Module.Basis.coord_apply]
  exact InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.repr_self_apply j i

/-- Applying the mixed commutator to any vector is the four-coordinate formula. -/
theorem ellRootBasisMixedRegularCommutator_apply (x : CZ) :
    ellRootBasisMixedRegularCommutator x =
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 4 x -
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 0 x) •
          InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 6 +
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 2 x) •
          (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 0 -
            InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 4) -
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 5 x) •
          InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 3 +
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 7 x) •
          InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 1 := by
  rw [ell_rootBasis_mixedRegularCommutator_eq_coordinate_formula]
  simp only [ellRootBasisMixedRegularCommutatorFormula, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smulRight_apply]

/-- Exact kernel criterion for the mixed regular commutator in Ell coordinates. -/
theorem ellRootBasisMixedRegularCommutator_eq_zero_iff (x : CZ) :
    ellRootBasisMixedRegularCommutator x = 0 ↔
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 4 x =
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 0 x) ∧
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 2 x = 0 ∧
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 5 x = 0 ∧
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 7 x = 0 := by
  rw [ellRootBasisMixedRegularCommutator_apply]
  constructor
  · intro h
    have h6 := congrArg
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 6) h
    have h0 := congrArg
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 0) h
    have h3 := congrArg
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 3) h
    have h1 := congrArg
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 1) h
    simp only [map_add, map_sub, map_smul, ellCircularBasis_coord_frame,
      LinearMap.map_zero] at h6 h0 h3 h1
    norm_num at h6 h0 h3 h1
    change (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 4 x -
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 0 x) = 0 at h6
    change InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 2 x = 0 at h0
    change InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 5 x = 0 at h3
    change InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.coord 7 x = 0 at h1
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith
  · rintro ⟨h40, h2, h5, h7⟩
    rw [h40, h2, h5, h7]
    simp

/-- Four independent output directions singled out by the Ell circular frame. -/
def ellRootBasisMixedRegularCommutatorImageFrame : Fin 4 → CZ
  | 0 => InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 6
  | 1 => InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 0 -
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 4
  | 2 => InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 3
  | 3 => InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 1

/-- Exact range description: the mixed commutator image is the span of the
four frame directions occurring in its coordinate formula. -/
theorem ellRootBasisMixedRegularCommutator_range_eq_span :
    LinearMap.range ellRootBasisMixedRegularCommutator =
      Submodule.span ℝ (Set.range ellRootBasisMixedRegularCommutatorImageFrame) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [ellRootBasisMixedRegularCommutator_apply]
    apply Submodule.add_mem
    · apply Submodule.sub_mem
      · apply Submodule.add_mem
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    fin_cases i
    · change InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 6 ∈
        LinearMap.range ellRootBasisMixedRegularCommutator
      refine ⟨InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 4, ?_⟩
      rw [ellRootBasisMixedRegularCommutator_apply]
      simp only [ellCircularBasis_coord_frame]
      norm_num
    · change InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 0 -
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 4 ∈
        LinearMap.range ellRootBasisMixedRegularCommutator
      refine ⟨InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 2, ?_⟩
      rw [ellRootBasisMixedRegularCommutator_apply]
      simp only [ellCircularBasis_coord_frame]
      norm_num
    · change InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 3 ∈
        LinearMap.range ellRootBasisMixedRegularCommutator
      refine ⟨-InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 5, ?_⟩
      rw [map_neg, ellRootBasisMixedRegularCommutator_apply]
      simp only [ellCircularBasis_coord_frame]
      norm_num
    · change InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 1 ∈
        LinearMap.range ellRootBasisMixedRegularCommutator
      refine ⟨InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 7, ?_⟩
      rw [ellRootBasisMixedRegularCommutator_apply]
      simp only [ellCircularBasis_coord_frame]
      norm_num

/-- The four range generators are independent: their coefficients are recovered
by the Ell basis coordinates `6`, `0`, `3`, and `1`. -/
theorem ellRootBasisMixedRegularCommutatorImageFrame_linearIndependent :
    LinearIndependent ℝ ellRootBasisMixedRegularCommutatorImageFrame := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h i
  let b := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis
  have h_repr_frame (a j : Fin 8) :
      b.repr (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame a) j =
        if a = j then 1 else 0 := by
    rw [← InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis_apply]
    exact b.repr_self_apply a j
  have h_repr_difference (j : Fin 8) :
      b.repr (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 0 -
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame 4) j =
        (if (0 : Fin 8) = j then 1 else 0) - (if (4 : Fin 8) = j then 1 else 0) := by
    rw [← Module.Basis.coord_apply, map_sub,
      ellCircularBasis_coord_frame, ellCircularBasis_coord_frame]
  have h_repr_image (i : Fin 4) (j : Fin 8) :
      b.repr (ellRootBasisMixedRegularCommutatorImageFrame i) j =
        if i = 0 then (if (6 : Fin 8) = j then 1 else 0)
        else if i = 1 then
          (if (0 : Fin 8) = j then 1 else 0) - (if (4 : Fin 8) = j then 1 else 0)
        else if i = 2 then (if (3 : Fin 8) = j then 1 else 0)
        else if i = 3 then (if (1 : Fin 8) = j then 1 else 0) else 0 := by
    fin_cases i
    · exact h_repr_frame 6 j
    · exact h_repr_difference j
    · exact h_repr_frame 3 j
    · exact h_repr_frame 1 j
  fin_cases i
  · have h6 := congrArg (fun x => b.repr x 6) h
    rw [map_sum, map_sum] at h6
    simp [map_smul, Fin.sum_univ_succ, h_repr_image] at h6
    exact h6
  · have h0 := congrArg (fun x => b.repr x 0) h
    rw [map_sum, map_sum] at h0
    simp [map_smul, Fin.sum_univ_succ, h_repr_image] at h0
    exact h0
  · have h3 := congrArg (fun x => b.repr x 3) h
    rw [map_sum, map_sum] at h3
    simp [map_smul, Fin.sum_univ_succ, h_repr_image] at h3
    exact h3
  · have h1 := congrArg (fun x => b.repr x 1) h
    rw [map_sum, map_sum] at h1
    simp [map_smul, Fin.sum_univ_succ, h_repr_image] at h1
    exact h1

/-- The mixed regular commutator has rank four on the native split-octonion
carrier. -/
theorem ellRootBasisMixedRegularCommutator_finrank_range :
    Module.finrank ℝ (LinearMap.range ellRootBasisMixedRegularCommutator) = 4 := by
  rw [ellRootBasisMixedRegularCommutator_range_eq_span]
  simpa [ellRootBasisMixedRegularCommutatorImageFrame] using
    (finrank_span_eq_card ellRootBasisMixedRegularCommutatorImageFrame_linearIndependent)

/-- Entrywise matrix of the native mixed regular commutator in the Ell
circular Peirce basis; rows are output coordinates, columns are inputs. -/
theorem ellRootBasisMixedRegularCommutator_toMatrix_entries (i j : Fin 8) :
    LinearMap.toMatrix
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis
        ellRootBasisMixedRegularCommutator i j =
      (if i = 0 ∧ j = 2 then 1 else 0) +
      (if i = 1 ∧ j = 7 then 1 else 0) -
      (if i = 3 ∧ j = 5 then 1 else 0) -
      (if i = 4 ∧ j = 2 then 1 else 0) +
      (if i = 6 ∧ j = 4 then 1 else 0) -
      (if i = 6 ∧ j = 0 then 1 else 0) := by
  let b := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis
  rw [LinearMap.toMatrix_apply]
  change (b.repr (ellRootBasisMixedRegularCommutator (b j))) i = _
  rw [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis_apply]
  change (b.repr ((InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0) *
    InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) -
    InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) *
    InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame j))) i = _
  rw [ell_rootBasis_mixedRegularCommutator_frame_action j]
  have hrepr (k : Fin 8) :
      b.repr (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame k) =
        Finsupp.single k (1 : ℝ) := by
    rw [← InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis_apply]
    exact b.repr_self k
  have hrm1 : b.repr (InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus 1) =
      Finsupp.single 6 (1 : ℝ) := by simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using hrepr 6
  have hrp2 : b.repr (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 2) =
      Finsupp.single 3 (1 : ℝ) := by simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using hrepr 3
  have hrp0 : b.repr (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0) =
      Finsupp.single 1 (1 : ℝ) := by simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using hrepr 1
  have huplus : b.repr InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus =
      Finsupp.single 0 (1 : ℝ) := by simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using hrepr 0
  have huminus : b.repr InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus =
      Finsupp.single 4 (1 : ℝ) := by simpa [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame] using hrepr 4
  fin_cases j <;>
    simp only [sub_eq_add_neg, map_add, map_neg, hrm1, hrp2,
      hrp0, huplus, huminus, Finsupp.single_apply] <;>
    fin_cases i <;> norm_num

/-- Native regular Tetraktys action on each vector of the genuine Ell circular
Peirce basis.  This is the basis-level form of the coordinate formulas: `Φ`
is identity, `J` distinguishes the two four-dimensional sectors, and `V`
and `Σ` vanish. -/
theorem ellCircular_regularTetraktys_basis_action (i : Fin 8) :
    (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularPhi
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) =
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i ∧
    (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) =
      (if i.val < 4 then (1 : ℝ) else -1) •
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i ∧
    (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularV
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) = 0 ∧
    (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularSig
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) = 0 := by
  have hPhi := InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.regularPhi_uPlus_uMinus_eq_one
  have hVS := InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.regularV_regularSig_uPlus_uMinus_eq_zero
  have hJ :
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) =
      (if i.val < 4 then (1 : ℝ) else -1) •
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i := by
    apply InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.injective
    have hcoordAction :
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
            ((InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
              InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
              InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
              (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i)) =
          InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate
            (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
              InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
              InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
            (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
              (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i)) := by
      simp [InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate,
        LinearEquiv.conjAlgEquiv_apply]
    rw [hcoordAction,
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_apply_frame,
      InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCircular_regularJ_apply]
    simp only [map_smul,
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_apply_frame]
    ext k
    by_cases hi : i.val < 4 <;> by_cases hki : k = i <;>
      simp [hi, hki]
  refine ⟨?_, hJ, ?_, ?_⟩
  · simpa using congrArg
      (fun T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ =>
        T (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i)) hPhi
  · simpa using congrArg
      (fun T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ =>
        T (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i)) hVS.1
  · simpa using congrArg
      (fun T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ =>
        T (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i)) hVS.2

/-- Matrix form of conjugation by a linear equivalence: the coordinate
matrix of the transported operator is obtained by conjugating its matrix by
the frame-transition matrix. -/
theorem toMatrix_conjAlgEquiv
    (e : Vec8R ≃ₗ[ℝ] Vec8R)
    (T : Module.End ℝ Vec8R) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
        (e.conjAlgEquiv ℝ T) =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) e.toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) T *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) e.symm.toLinearMap := by
  let b := Pi.basisFun ℝ (Fin 8)
  change LinearMap.toMatrix b b
      ((e.toLinearMap.comp T).comp e.symm.toLinearMap) = _
  rw [← LinearMap.toMatrix_comp b b b, ← LinearMap.toMatrix_comp b b b]

/-- Concrete operator soldering identity: for every native endomorphism of
the split-octonion carrier, its legacy circular matrix is the conjugate of
its Ell circular matrix by the explicitly computed 8×8 basis-change matrix. -/
theorem ellToLegacy_operatorMatrix_conjugation
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout T) =
      ellToLegacyMatrix *
        LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
          (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate T) *
        legacyToEllMatrix := by
  rw [← ellToLegacy_conjugateEnd T]
  simpa [LinearMap.toMatrixAlgEquiv, ellToLegacyMatrix, legacyToEllMatrix] using
    toMatrix_conjAlgEquiv ellToLegacy
      (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate T)

/-- The native double-commutator superoperator is transported in two stages
without changing its composition order: first to Ell coordinates by the Ell
operator owner, then to the legacy circular coordinates by the basis-change
equivalence. -/
theorem ellToLegacy_doubleComm
    (H T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    ellToLegacy.conjAlgEquiv ℝ
        (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateDoubleComm
          (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate H)
          (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate T)) =
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T) := by
  rw [← InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate_doubleComm]
  exact ellToLegacy_conjugateEnd _

/-- Explicit `8 × 8` matrix soldering for the native Tetraktys
double-commutator.  Its Ell-coordinate matrix and legacy-coordinate matrix
are related by conjugation with the computed basis transition. -/
theorem ellToLegacy_doubleComm_matrix_conjugation
    (H T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T)) =
      ellToLegacyMatrix *
        LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
          (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateDoubleComm
            (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate H)
            (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate T)) *
        legacyToEllMatrix := by
  simpa only [InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate_doubleComm] using
    ellToLegacy_operatorMatrix_conjugation
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T)

/-- In the Ell frame the distinguished regular `J` generator is diagonal,
with eigenvalue `+1` on the first Peirce sector and `-1` on the second. -/
theorem ellRegularJMatrix_eq_sector_diagonal :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
        (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)) =
      Matrix.diagonal (fun i => if i.val < 4 then (1 : ℝ) else -1) := by
  change LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
      (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)) = _
  apply InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.coordinateOperatorMatrix_eq_diagonal
  intro j
  rw [InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCircular_regularJ_apply]
  ext i
  by_cases hj : j.val < 4 <;> by_cases hij : i = j <;>
    simp [hj, hij]

/-- In the legacy circular frame, the same regular split-octonion `J`
operator is the explicit orthogonal conjugate of its Ell-sector diagonal
matrix.  This identifies the actual operator matrix across the two distinct
Peirce bases. -/
theorem legacyRegularJMatrix_eq_transition_conjugate :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)) =
      ellToLegacyMatrix *
        Matrix.diagonal (fun i => if i.val < 4 then (1 : ℝ) else -1) *
        Matrix.transpose ellToLegacyMatrix := by
  rw [ellToLegacy_operatorMatrix_conjugation,
    ellRegularJMatrix_eq_sector_diagonal, legacyToEllMatrix_eq_transpose]

/-- Concrete legacy-coordinate matrix of the regular split-octonion `J`.
Although `J` is diagonal in the Ell Peirce frame, the explicit basis change
turns it into this signed permutation matrix in the legacy frame. -/
theorem legacyRegularJMatrix_explicit :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)) =
      (!![0, 0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0, 1;
         0, 0, 0, 0, 0, 0, -1, 0;
         0, 1, 0, 0, 0, 0, 0, 0;
         1, 0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, -1, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [legacyRegularJMatrix_eq_transition_conjugate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_eight,
      ellToLegacyMatrix_apply, transitionColumn]

/-- In the legacy coordinates the transported regular `J` remains a
symmetric involution.  Thus the basis change preserves its self-adjoint
operator structure, not only its abstract endomorphism action. -/
theorem legacyRegularJMatrix_symmetric_and_involutive :
    let J := LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))
    Matrix.transpose J = J ∧ J * J = 1 := by
  dsimp only
  rw [legacyRegularJMatrix_eq_transition_conjugate]
  let T := ellToLegacyMatrix
  let D := Matrix.diagonal (fun i : Fin 8 => if i.val < 4 then (1 : ℝ) else -1)
  have hD_symm : Matrix.transpose D = D := by
    change Matrix.transpose
        (Matrix.diagonal (fun i : Fin 8 => if i.val < 4 then (1 : ℝ) else -1)) = _
    exact Matrix.diagonal_transpose _
  have hD_sq : D * D = 1 := by
    change Matrix.diagonal (fun i : Fin 8 => if i.val < 4 then (1 : ℝ) else -1) * _ = _
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      by_cases hi : i.val < 4 <;> simp [hi]
    · simp [Matrix.diagonal, h]
  have hTorth : Matrix.transpose T * T = 1 := ellToLegacyMatrix_orthogonal
  have hTorth' : T * Matrix.transpose T = 1 := by
    rw [← legacyToEllMatrix_eq_transpose]
    exact transition_matrices_are_inverses.2
  constructor
  · change Matrix.transpose (T * D * Matrix.transpose T) = T * D * Matrix.transpose T
    calc Matrix.transpose (T * D * Matrix.transpose T) =
          Matrix.transpose (Matrix.transpose T) * Matrix.transpose D *
            Matrix.transpose T := by
              rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
              noncomm_ring
      _ = T * D * Matrix.transpose T := by
            rw [Matrix.transpose_transpose, hD_symm]
  · calc (T * D * Matrix.transpose T) * (T * D * Matrix.transpose T)
        = T * D * (Matrix.transpose T * T) * D * Matrix.transpose T := by
            noncomm_ring
      _ = T * D * D * Matrix.transpose T := by rw [hTorth]; noncomm_ring
      _ = T * (D * D) * Matrix.transpose T := by noncomm_ring
      _ = T * Matrix.transpose T := by rw [hD_sq, mul_one]
      _ = 1 := hTorth'

/-- The legacy-frame regular `J` has trace zero.  Together with its
involution law this records the balanced positive and negative sectors after
transport. -/
theorem legacyRegularJMatrix_trace_zero :
    Matrix.trace
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) = 0 := by
  rw [legacyRegularJMatrix_eq_transition_conjugate]
  let T := ellToLegacyMatrix
  let D := Matrix.diagonal (fun i : Fin 8 => if i.val < 4 then (1 : ℝ) else -1)
  have hTorth : Matrix.transpose T * T = 1 := ellToLegacyMatrix_orthogonal
  calc Matrix.trace (T * D * Matrix.transpose T) =
        Matrix.trace (Matrix.transpose T * (T * D)) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((Matrix.transpose T * T) * D) := by
          congr 1
          noncomm_ring
    _ = Matrix.trace D := by rw [hTorth, one_mul]
    _ = 0 := by
          simp [D, Fin.sum_univ_eight]

/-- Each explicit transition column is an eigenvector of the legacy-frame
regular `J` operator, with the sign determined by its Ell Peirce sector. -/
theorem legacyRegularJ_transitionColumn_eigen (j : Fin 8) :
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
      (transitionColumn j) =
        (if j.val < 4 then (1 : ℝ) else -1) • transitionColumn j := by
  rw [← ellToLegacy_single_eq_transitionColumn]
  have hconj := congrArg
    (fun S : Module.End ℝ Vec8R => S (ellToLegacy (Pi.single j (1 : ℝ))))
    (ellToLegacy_conjugateEnd
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))
  change ellToLegacy
      (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
        (ellToLegacy.symm (ellToLegacy (Pi.single j (1 : ℝ))))) = _ at hconj
  rw [ellToLegacy.symm_apply_apply] at hconj
  have hEll :
      InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
          (Pi.single j (1 : ℝ)) =
        (if j.val < 4 then (1 : ℝ) else -1) • Pi.single j (1 : ℝ) := by
    rw [InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCircular_regularJ_apply]
    ext i
    by_cases hj : j.val < 4 <;> by_cases hij : i = j <;> simp [hj, hij]
  rw [hEll, map_smul] at hconj
  simpa using hconj.symm

/-- The entire distinguished regular Tetraktys in the legacy circular frame:
`Φ` acts as the identity, `J` has the two Ell-sector eigenvalues on the
explicit transition columns, and `V` and `Σ` act as zero.  This records the
four operator actions on one common coordinate carrier. -/
theorem legacy_regularTetraktys_basis_action :
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularPhi
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus) = 1 ∧
    (∀ j : Fin 8,
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
          (transitionColumn j) =
        (if j.val < 4 then (1 : ℝ) else -1) • transitionColumn j) ∧
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularV
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus) = 0 ∧
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularSig
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus) = 0 := by
  have hVS :=
    InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.regularV_regularSig_uPlus_uMinus_eq_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← ellToLegacy_conjugateEnd
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularPhi
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus),
      InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.regularPhi_uPlus_uMinus_eq_one]
    simp [InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate]
  · exact legacyRegularJ_transitionColumn_eigen
  · rw [← ellToLegacy_conjugateEnd
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularV
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus), hVS.1]
    simp [InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate]
  · rw [← ellToLegacy_conjugateEnd
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularSig
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus), hVS.2]
    simp [InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate]

/-- The three degenerate Tetraktys superoperators remain zero after soldering
to legacy coordinates.  This transports the native Ell reduction without
identifying the nonassociative split-octonion carrier with its endomorphism
algebra. -/
theorem legacy_regularTetraktys_doubleComm_zero_channels
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularPhi
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus) T) = 0 ∧
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularV
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus) T) = 0 ∧
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularSig
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus) T) = 0 := by
  rcases InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCircular_regularTetraktys_doubleComm_reduction T with
    ⟨hPhi, hV, hSig⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← ellToLegacy_doubleComm, hPhi]
    simp
  · rw [← ellToLegacy_doubleComm, hV]
    simp
  · rw [← ellToLegacy_doubleComm, hSig]
    simp

/-- Rank-one coordinate endomorphism sending the `j`th coordinate to the
`i`th basis vector. -/
def coordinateMatrixUnit (i j : Fin 8) : Module.End ℝ Vec8R where
  toFun x := x j • Pi.single i (1 : ℝ)
  map_add' x y := by
    simp only [Pi.add_apply]
    rw [add_smul]
  map_smul' c x := by
    ext k
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Pi.single_apply]
    ring

/-- Matrix units form a basis of the full endomorphism space, transported
from the standard matrix basis through the basis-coordinate matrix equivalence. -/
def coordinateEndBasis : Module.Basis (Fin 8 × Fin 8) ℝ
    (Module.End ℝ Vec8R) :=
  (Matrix.stdBasis ℝ (Fin 8) (Fin 8)).map
    (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))).symm.toLinearEquiv

theorem coordinateEndBasis_apply (i j : Fin 8) :
    coordinateEndBasis (i, j) = coordinateMatrixUnit i j := by
  simp only [coordinateEndBasis, Module.Basis.map_apply,
    Matrix.stdBasis_eq_single, LinearMap.toMatrixAlgEquiv_symm]
  apply LinearMap.ext
  intro x
  change Matrix.toLinAlgEquiv (Pi.basisFun ℝ (Fin 8))
    (Matrix.single i j (1 : ℝ)) x = _
  rw [Matrix.toLinAlgEquiv_apply, Matrix.single_mulVec_eq]
  ext k
  rw [Finset.sum_eq_single i]
  · simp [coordinateMatrixUnit]
  · intro a ha hai
    simp [hai]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Every operator on the legacy eight-coordinate carrier is a linear
combination of the 64 coordinate matrix units. -/
theorem coordinateMatrixUnits_span_eq_top :
    Submodule.span ℝ {X : Module.End ℝ Vec8R |
      ∃ i j : Fin 8, X = coordinateMatrixUnit i j} = ⊤ := by
  have hspan := coordinateEndBasis.span_eq
  apply le_antisymm
  · exact le_top
  · rw [← hspan]
    apply Submodule.span_le.mpr
    rintro X ⟨p, rfl⟩
    apply Submodule.subset_span
    exact ⟨p.1, p.2, coordinateEndBasis_apply p.1 p.2⟩

/-- A linear endomorphism that acts by zero or identity on every vector of a
basis is idempotent on the whole carrier. -/
theorem linearEnd_idempotent_of_basis_zero_or_identity
    {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] [Module ℝ M]
    (b : Module.Basis ι ℝ M) (f : Module.End ℝ M)
    (heig : ∀ i, f (b i) = 0 ∨ f (b i) = b i) :
    f * f = f := by
  have hfix : ∀ i, f (f (b i)) = f (b i) := by
    intro i
    rcases heig i with hzero | hone
    · rw [hzero, map_zero]
    · rw [hone, hone]
  apply LinearMap.ext
  intro x
  rw [← b.sum_repr x, map_sum, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  change (b.repr x) i • f (f (b i)) = (b.repr x) i • f (b i)
  rw [hfix i]

@[simp] theorem coordinateMatrixUnit_apply_single (i j k : Fin 8) :
    coordinateMatrixUnit i j (Pi.single k (1 : ℝ)) =
      if k = j then Pi.single i (1 : ℝ) else 0 := by
  ext l
  by_cases hk : k = j <;> by_cases hl : l = i <;>
    simp [coordinateMatrixUnit, hk, hl]

/-- In the Ell frame, the double-commutator by regular `J` acts diagonally
on the 64 matrix units: it vanishes within each Peirce block and has
eigenvalue four between the two blocks. -/
theorem ellRegularJ_doubleComm_coordinateMatrixUnit_eigen (i j : Fin 8) :
    InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateDoubleComm
      (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))
      (coordinateMatrixUnit i j) =
        (if (i.val < 4) = (j.val < 4) then (0 : ℝ) else 4) •
          coordinateMatrixUnit i j := by
  apply (Pi.basisFun ℝ (Fin 8)).ext
  intro k
  rw [Pi.basisFun_apply]
  funext l
  rw [InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCircular_regularJ_doubleComm_matrixUnit
    (coordinateMatrixUnit i j) l k]
  by_cases hsec : (i.val < 4) = (j.val < 4)
  · by_cases hkj : k = j <;> by_cases hli : l = i <;>
      simp [coordinateMatrixUnit, hsec, hkj, hli]
  · by_cases hkj : k = j <;> by_cases hli : l = i <;>
      simp [coordinateMatrixUnit, hsec, hkj, hli]

/-- The Ell matrix unit transported into legacy coordinates.  Its range is
spanned by the corresponding transition column and its coefficient reads
the matching Ell-coordinate functional. -/
def legacyCoordinateMatrixUnit (i j : Fin 8) : Module.End ℝ Vec8R :=
  ellToLegacy.conjAlgEquiv ℝ (coordinateMatrixUnit i j)

/-- Transport of the coordinate endomorphism basis through the actual Ell to
legacy change of frame. -/
def legacyCoordinateEndBasis : Module.Basis (Fin 8 × Fin 8) ℝ
    (Module.End ℝ Vec8R) :=
  coordinateEndBasis.map (ellToLegacy.conjAlgEquiv ℝ).toLinearEquiv

@[simp] theorem legacyCoordinateEndBasis_apply (i j : Fin 8) :
    legacyCoordinateEndBasis (i, j) = legacyCoordinateMatrixUnit i j := by
  simp [legacyCoordinateEndBasis, legacyCoordinateMatrixUnit,
    coordinateEndBasis_apply]

/-- The transported legacy matrix units span the entire operator space. -/
theorem legacyCoordinateMatrixUnits_span_eq_top :
    Submodule.span ℝ {X : Module.End ℝ Vec8R |
      ∃ i j : Fin 8, X = legacyCoordinateMatrixUnit i j} = ⊤ := by
  have hspan := legacyCoordinateEndBasis.span_eq
  apply le_antisymm
  · exact le_top
  · rw [← hspan]
    apply Submodule.span_le.mpr
    rintro X ⟨p, rfl⟩
    apply Submodule.subset_span
    exact ⟨p.1, p.2, legacyCoordinateEndBasis_apply p.1 p.2⟩

/-- The transported matrix unit is the rank-one map determined by the `j`th
Ell coordinate functional and the actual `i`th transition column.  This
identifies its eigenvectors concretely in the legacy basis. -/
@[simp] theorem legacyCoordinateMatrixUnit_apply (i j : Fin 8) (x : Vec8R) :
    legacyCoordinateMatrixUnit i j x = (ellToLegacy.symm x j) • transitionColumn i := by
  change ellToLegacy (coordinateMatrixUnit i j (ellToLegacy.symm x)) = _
  simp [coordinateMatrixUnit]
  rw [ellToLegacy_single_eq_transitionColumn i]

/-- A double commutator on the legacy coordinate endomorphism carrier.
The native `doubleComm` is specialized to `EndCZ`; changing coordinates
requires the corresponding operation on `Module.End ℝ Vec8R`. -/
def legacyCoordinateComm (H X : Module.End ℝ Vec8R) : Module.End ℝ Vec8R :=
  H * X - X * H

def legacyCoordinateDoubleComm (H X : Module.End ℝ Vec8R) :
    Module.End ℝ Vec8R :=
  legacyCoordinateComm H (legacyCoordinateComm H X)

/-- The explicit Ell-to-legacy basis soldering carries the native double
commutator to the legacy-coordinate double commutator.  This holds for every
pair of native endomorphisms; it does not depend on the special Peirce
generators or on an associativity assumption for split-octonion multiplication. -/
theorem legacyCoordinateDoubleComm_soldering
    (H T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    legacyCoordinateDoubleComm
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout H)
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout T) =
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T) := by
  let e := ellToLegacy.conjAlgEquiv ℝ
  let ellReadout := InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate
  let coordComm := fun X Y : Module.End ℝ Vec8R => X * Y - Y * X
  have hcomm (X Y : Module.End ℝ Vec8R) :
      legacyCoordinateComm (e X) (e Y) = e (coordComm X Y) := by
    change e X * e Y - e Y * e X = e (X * Y - Y * X)
    have hmul₁ : e X * e Y = e (X * Y) := (e.map_mul X Y).symm
    have hmul₂ : e Y * e X = e (Y * X) := (e.map_mul Y X).symm
    rw [hmul₁, hmul₂]
    exact (e.map_sub (X * Y) (Y * X)).symm
  have hH :
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout H =
        e (ellReadout H) := (ellToLegacy_conjugateEnd H).symm
  have hT :
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout T =
        e (ellReadout T) := (ellToLegacy_conjugateEnd T).symm
  have hdouble :
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T) =
        e (ellReadout (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T)) :=
    (ellToLegacy_conjugateEnd _).symm
  have hcoord :
      ellReadout (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T) =
        coordComm (ellReadout H) (coordComm (ellReadout H) (ellReadout T)) := by
    simpa [ellReadout, coordComm,
      InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateDoubleComm,
      InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateComm,
      InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm,
      InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.operatorComm] using
      InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate_doubleComm H T
  rw [hH, hT, hdouble]
  change legacyCoordinateDoubleComm (e (ellReadout H)) (e (ellReadout T)) =
    e (ellReadout (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T))
  rw [hcoord]
  change legacyCoordinateComm (e (ellReadout H))
      (legacyCoordinateComm (e (ellReadout H)) (e (ellReadout T))) =
    e (coordComm (ellReadout H) (coordComm (ellReadout H) (ellReadout T)))
  rw [hcomm (ellReadout H) (ellReadout T),
    hcomm (ellReadout H) (coordComm (ellReadout H) (ellReadout T))]

/-- For an involution, the coordinate double commutator is twice the defect
from conjugation by that involution. -/
theorem legacyCoordinateDoubleComm_formula
    (H X : Module.End ℝ Vec8R) (hH : H * H = 1) :
    legacyCoordinateDoubleComm H X = 2 • (X - H * X * H) := by
  unfold legacyCoordinateDoubleComm legacyCoordinateComm
  calc H * (H * X - X * H) - (H * X - X * H) * H
      = H * (H * X) - H * (X * H) - ((H * X) * H - (X * H) * H) := by
        simp only [mul_sub, sub_mul]
    _ = (H * H) * X - (H * X) * H - ((H * X) * H - X * (H * H)) := by
        rw [← mul_assoc H H X, ← mul_assoc H X H, mul_assoc X H H]
    _ = 2 • (X - H * X * H) := by
      rw [hH, one_mul, mul_one, two_smul]
      abel

/-- The involutive double-commutator superoperator has minimal polynomial
dividing `X (X - 4)`: applying it twice multiplies its value by four. -/
theorem legacyCoordinateDoubleComm_quadratic_relation
    (H X : Module.End ℝ Vec8R) (hH : H * H = 1) :
    legacyCoordinateDoubleComm H (legacyCoordinateDoubleComm H X) =
      4 • legacyCoordinateDoubleComm H X := by
  let Y := X - H * X * H
  have hY : H * Y * H = -Y := by
    dsimp [Y]
    have hconj : H * (H * X * H) * H = X := by
      calc H * (H * X * H) * H = (H * H) * X * (H * H) := by noncomm_ring
        _ = X := by rw [hH]; noncomm_ring
    calc H * (X - H * X * H) * H
        = H * X * H - H * (H * X * H) * H := by simp only [mul_sub, sub_mul]
      _ = H * X * H - X := by rw [hconj]
      _ = -(X - H * X * H) := by abel
  rw [legacyCoordinateDoubleComm_formula H _ hH,
    legacyCoordinateDoubleComm_formula H X hH]
  rw [show H * (2 • Y) * H = 2 • (H * Y * H) by
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc], hY]
  module

/-- The double commutator, viewed as a genuine linear endomorphism of the
64-dimensional space of legacy-coordinate operators. -/
private def legacyLeftCompose (H : Module.End ℝ Vec8R) :
    Module.End ℝ (Module.End ℝ Vec8R) where
  toFun X := H * X
  map_add' X Y := by simp [mul_add]
  map_smul' c X := Algebra.mul_smul_comm c H X

private def legacyRightCompose (H : Module.End ℝ Vec8R) :
    Module.End ℝ (Module.End ℝ Vec8R) where
  toFun X := X * H
  map_add' X Y := by simp [add_mul]
  map_smul' c X := Algebra.smul_mul_assoc c X H

private def legacyCoordinateCommAction (H : Module.End ℝ Vec8R) :
    Module.End ℝ (Module.End ℝ Vec8R) :=
  legacyLeftCompose H - legacyRightCompose H

/-- The double commutator is the square of the commutator action on operator
space, so linearity follows from composition in `Module.End`. -/
def legacyCoordinateDoubleCommAction (H : Module.End ℝ Vec8R) :
    Module.End ℝ (Module.End ℝ Vec8R) :=
  legacyCoordinateCommAction H * legacyCoordinateCommAction H

/-- As a linear endomorphism of operator space, the double commutator obeys
the same quadratic relation as its pointwise action. -/
theorem legacyCoordinateDoubleCommAction_quadratic_relation
    (H : Module.End ℝ Vec8R) (hH : H * H = 1) :
    legacyCoordinateDoubleCommAction H * legacyCoordinateDoubleCommAction H =
      4 • legacyCoordinateDoubleCommAction H := by
  apply LinearMap.ext
  intro X
  change legacyCoordinateDoubleComm H (legacyCoordinateDoubleComm H X) = _
  exact legacyCoordinateDoubleComm_quadratic_relation H X hH

/-- One quarter of the involutive double commutator is the projection onto
the cross-sector operator subspace. -/
def legacyCoordinateCrossSectorProjection (H : Module.End ℝ Vec8R) :
    Module.End ℝ (Module.End ℝ Vec8R) :=
  (1 / 4 : ℝ) • legacyCoordinateDoubleCommAction H

/-- For an involution, the normalized double commutator is the antisymmetric
part of the conjugation action `X ↦ H * X * H`. -/
theorem legacyCoordinateCrossSectorProjection_formula
    (H X : Module.End ℝ Vec8R) (hH : H * H = 1) :
    legacyCoordinateCrossSectorProjection H X =
      (1 / 2 : ℝ) • (X - H * X * H) := by
  change (1 / 4 : ℝ) • legacyCoordinateDoubleComm H X = _
  rw [legacyCoordinateDoubleComm_formula H X hH]
  module

/-- The zero eigenspace of the normalized double commutator consists exactly
of operators fixed by conjugation with the involution. -/
theorem legacyCoordinateCrossSectorProjection_eq_zero_iff_conjugation_fixed
    (H X : Module.End ℝ Vec8R) (hH : H * H = 1) :
    legacyCoordinateCrossSectorProjection H X = 0 ↔ H * X * H = X := by
  rw [legacyCoordinateCrossSectorProjection_formula H X hH]
  constructor
  · intro h
    have hdiff : X - H * X * H = 0 := by
      have := smul_eq_zero.mp h
      exact this.resolve_left (by norm_num)
    exact (sub_eq_zero.mp hdiff).symm
  · intro h
    rw [h]
    simp

/-- The one eigenspace of the normalized double commutator consists exactly
of operators negated by conjugation with the involution. -/
theorem legacyCoordinateCrossSectorProjection_eq_self_iff_conjugation_negated
    (H X : Module.End ℝ Vec8R) (hH : H * H = 1) :
    legacyCoordinateCrossSectorProjection H X = X ↔ H * X * H = -X := by
  rw [legacyCoordinateCrossSectorProjection_formula H X hH]
  constructor
  · intro h
    have htwice : X - H * X * H = (2 : ℝ) • X := by
      calc X - H * X * H = (2 : ℝ) • ((1 / 2 : ℝ) • (X - H * X * H)) := by module
        _ = (2 : ℝ) • X := congrArg (fun Y : Module.End ℝ Vec8R =>
          (2 : ℝ) • Y) h
    calc H * X * H = X - (X - H * X * H) := by module
      _ = X - (2 : ℝ) • X := by rw [htwice]
      _ = -X := by module
  · intro h
    rw [h]
    module

/-- The transported regular split-octonion `J` is an involution on the
legacy coordinate carrier. -/
theorem legacyRegularJOperator_involution :
    legacyRegularJOperator * legacyRegularJOperator = 1 := by
  change InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus) *
    InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus) = 1
  rw [← map_mul,
    InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.regularJ_uPlus_uMinus_sq]
  simp

/-- The legacy-frame double commutator generated by the native split-octonion
regular `J` satisfies the same exact quadratic relation on every coordinate
endomorphism. -/
theorem legacyRegularJ_doubleComm_quadratic_relation
    (X : Module.End ℝ Vec8R) :
    let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
    legacyCoordinateDoubleComm J (legacyCoordinateDoubleComm J X) =
      4 • legacyCoordinateDoubleComm J X := by
  let J₀ := InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
    InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
    InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus
  have hJ₀ : J₀ * J₀ = 1 :=
    InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.regularJ_uPlus_uMinus_sq
  have hJ :
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout J₀ *
        InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout J₀ = 1 := by
    rw [← map_mul, hJ₀]
    simp
  dsimp only
  exact legacyCoordinateDoubleComm_quadratic_relation _ X hJ

/-- Conjugation transports the Ell-coordinate double commutator to the
double commutator on the destination endomorphism algebra. -/
theorem conjugate_ellDoubleComm (e : Vec8R ≃ₗ[ℝ] Vec8R)
    (H X : Module.End ℝ Vec8R) :
    e.conjAlgEquiv ℝ
        (InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateDoubleComm H X) =
      legacyCoordinateDoubleComm (e.conjAlgEquiv ℝ H) (e.conjAlgEquiv ℝ X) := by
  simp [InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateDoubleComm,
    InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateComm,
    legacyCoordinateDoubleComm, legacyCoordinateComm, map_sub, map_mul]

/-- In the legacy operator algebra, rank-one maps formed from transition
columns retain the same double-commutator eigenvalue: zero on equal Peirce
sectors and four on cross-sector maps. -/
theorem legacyRegularJ_doubleComm_matrixUnit_eigen (i j : Fin 8) :
    legacyCoordinateDoubleComm
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))
      (legacyCoordinateMatrixUnit i j) =
        (if (i.val < 4) = (j.val < 4) then (0 : ℝ) else 4) •
          legacyCoordinateMatrixUnit i j := by
  let J₀ := InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
    InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
    InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus
  let Jell := InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates.ellCoordinateConjugate J₀
  have hJ : ellToLegacy.conjAlgEquiv ℝ Jell =
      InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout J₀ :=
    ellToLegacy_conjugateEnd J₀
  rw [← hJ]
  change legacyCoordinateDoubleComm
      (ellToLegacy.conjAlgEquiv ℝ Jell)
      (ellToLegacy.conjAlgEquiv ℝ (coordinateMatrixUnit i j)) = _
  rw [← conjugate_ellDoubleComm, ellRegularJ_doubleComm_coordinateMatrixUnit_eigen]
  by_cases hsec : (i.val < 4) = (j.val < 4) <;>
    simp [hsec, legacyCoordinateMatrixUnit]

/-- The normalized regular-`J` double commutator reads the two Peirce sectors
directly on the transported matrix-unit basis: it is zero within a sector and
the identity on cross-sector matrix units. -/
theorem legacyRegularJ_crossSectorProjection_matrixUnit (i j : Fin 8) :
    legacyCoordinateCrossSectorProjection
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))
      (legacyCoordinateMatrixUnit i j) =
        (if (i.val < 4) = (j.val < 4) then (0 : ℝ) else 1) •
          legacyCoordinateMatrixUnit i j := by
  rw [legacyCoordinateCrossSectorProjection]
  change (1 / 4 : ℝ) • legacyCoordinateDoubleComm
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))
      (legacyCoordinateMatrixUnit i j) = _
  rw [legacyRegularJ_doubleComm_matrixUnit_eigen]
  by_cases hsec : (i.val < 4) = (j.val < 4) <;> simp [hsec]

/-- The cross-sector operator subspace in the transported matrix-unit frame. -/
def legacyCrossSectorOperatorSubspace :
    Submodule ℝ (Module.End ℝ Vec8R) :=
  Submodule.span ℝ {X | ∃ i j : Fin 8,
    (i.val < 4) ≠ (j.val < 4) ∧ X = legacyCoordinateMatrixUnit i j}

/-- On the linear span of cross-Peirce matrix units, the normalized regular-`J`
double commutator is exactly the identity. -/
theorem legacyRegularJ_crossSectorProjection_eq_self
    {X : Module.End ℝ Vec8R} (hX : X ∈ legacyCrossSectorOperatorSubspace) :
    legacyCoordinateCrossSectorProjection
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)) X = X := by
  induction hX using Submodule.span_induction with
  | zero =>
      change (1 / 4 : ℝ) • legacyCoordinateDoubleComm
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)) 0 = 0
      simp [legacyCoordinateDoubleComm, legacyCoordinateComm]
  | mem X hX =>
      rcases hX with ⟨i, j, hsec, rfl⟩
      rw [legacyRegularJ_crossSectorProjection_matrixUnit]
      simp [hsec]
  | add X Y hX hY hPX hPY => rw [map_add, hPX, hPY]
  | smul a X hX hPX => rw [map_smul, hPX]

/-- The within-sector operator subspace in the transported matrix-unit frame. -/
def legacyWithinSectorOperatorSubspace :
    Submodule ℝ (Module.End ℝ Vec8R) :=
  Submodule.span ℝ {X | ∃ i j : Fin 8,
    (i.val < 4) = (j.val < 4) ∧ X = legacyCoordinateMatrixUnit i j}

/-- The normalized regular-`J` double commutator annihilates the span of the
two within-sector matrix blocks. -/
theorem legacyRegularJ_crossSectorProjection_eq_zero
    {X : Module.End ℝ Vec8R} (hX : X ∈ legacyWithinSectorOperatorSubspace) :
    legacyCoordinateCrossSectorProjection
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)) X = 0 := by
  induction hX using Submodule.span_induction with
  | zero =>
      change (1 / 4 : ℝ) • legacyCoordinateDoubleComm
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)) 0 = 0
      simp [legacyCoordinateDoubleComm, legacyCoordinateComm]
  | mem X hX =>
      rcases hX with ⟨i, j, hsec, rfl⟩
      rw [legacyRegularJ_crossSectorProjection_matrixUnit]
      simp [hsec]
  | add X Y hX hY hPX hPY => rw [map_add, hPX, hPY, add_zero]
  | smul a X hX hPX => rw [map_smul, hPX, smul_zero]

/-- The normalized regular-`J` double commutator is a genuine projection on
the entire 64-dimensional legacy-coordinate operator space. -/
theorem legacyRegularJ_crossSectorProjection_idempotent :
    let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
    legacyCoordinateCrossSectorProjection J * legacyCoordinateCrossSectorProjection J =
      legacyCoordinateCrossSectorProjection J := by
  let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
    (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
  let P := legacyCoordinateCrossSectorProjection J
  have heig (p : Fin 8 × Fin 8) : P (legacyCoordinateEndBasis p) = 0 ∨
      P (legacyCoordinateEndBasis p) = legacyCoordinateEndBasis p := by
    rcases p with ⟨i, j⟩
    rw [legacyCoordinateEndBasis_apply,
      legacyRegularJ_crossSectorProjection_matrixUnit]
    by_cases hsec : (i.val < 4) = (j.val < 4) <;> simp [hsec]
  have hproj := linearEnd_idempotent_of_basis_zero_or_identity
    legacyCoordinateEndBasis P heig
  simpa [P] using hproj

/-- The within-sector and cross-sector matrix units together span the full
operator space.  This is the concrete two-block decomposition in the
transported split-octonion operator basis. -/
theorem legacyWithin_sup_crossSector_eq_top :
    legacyWithinSectorOperatorSubspace ⊔ legacyCrossSectorOperatorSubspace = ⊤ := by
  apply le_antisymm
  · exact le_top
  · rw [← legacyCoordinateEndBasis.span_eq]
    apply Submodule.span_le.mpr
    intro X hX
    rcases hX with ⟨p, rfl⟩
    rcases p with ⟨i, j⟩
    rw [legacyCoordinateEndBasis_apply]
    by_cases hsec : (i.val < 4) = (j.val < 4)
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, j, hsec, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, j, hsec, rfl⟩)

/-- The within-sector and cross-sector operator blocks intersect trivially.
The projection is zero on the first block and the identity on the second. -/
theorem legacyWithin_inf_crossSector_eq_bot :
    legacyWithinSectorOperatorSubspace ⊓ legacyCrossSectorOperatorSubspace = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro X hX
  have hwithin := legacyRegularJ_crossSectorProjection_eq_zero hX.1
  have hcross := legacyRegularJ_crossSectorProjection_eq_self hX.2
  rw [hwithin] at hcross
  exact hcross.symm

/-- The normalized regular-`J` double commutator has precisely the
cross-sector block as its range and the within-sector blocks as its kernel. -/
theorem legacyRegularJ_projection_range_ker :
    let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
    let P := legacyCoordinateCrossSectorProjection J
    LinearMap.range P = legacyCrossSectorOperatorSubspace ∧
      LinearMap.ker P = legacyWithinSectorOperatorSubspace := by
  dsimp only
  let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
    (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
  let P := legacyCoordinateCrossSectorProjection J
  have hzero : ∀ X : Module.End ℝ Vec8R,
      X ∈ legacyWithinSectorOperatorSubspace → P X = 0 := by
    intro X hX
    simpa [P, J] using legacyRegularJ_crossSectorProjection_eq_zero hX
  have hfix : ∀ X : Module.End ℝ Vec8R,
      X ∈ legacyCrossSectorOperatorSubspace → P X = X := by
    intro X hX
    simpa [P, J] using legacyRegularJ_crossSectorProjection_eq_self hX
  change LinearMap.range P = legacyCrossSectorOperatorSubspace ∧
    LinearMap.ker P = legacyWithinSectorOperatorSubspace
  constructor
  · apply le_antisymm
    · rw [LinearMap.range_le_iff_comap, eq_top_iff]
      intro X hxTop
      have hdecomp : X ∈ legacyWithinSectorOperatorSubspace ⊔
          legacyCrossSectorOperatorSubspace :=
        legacyWithin_sup_crossSector_eq_top ▸ hxTop
      rcases Submodule.mem_sup.mp hdecomp with ⟨Y, hY, Z, hZ, hXZ⟩
      change P X ∈ legacyCrossSectorOperatorSubspace
      rw [← hXZ]
      rw [map_add, hzero Y hY, hfix Z hZ, zero_add]
      exact hZ
    · intro X hX
      exact ⟨X, hfix X hX⟩
  · apply le_antisymm
    · intro X hX
      have hPX : P X = 0 := LinearMap.mem_ker.mp hX
      have hdecomp : X ∈ legacyWithinSectorOperatorSubspace ⊔
          legacyCrossSectorOperatorSubspace := by
        rw [legacyWithin_sup_crossSector_eq_top]
        exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hdecomp with ⟨Y, hY, Z, hZ, hXZ⟩
      have hz : Z = 0 := by
        have hsum : P X = Z := by
          calc P X = P (Y + Z) := congrArg P hXZ.symm
            _ = P Y + P Z := map_add P Y Z
            _ = Z := by rw [hzero Y hY, hfix Z hZ, zero_add]
        rw [hPX] at hsum
        exact hsum.symm
      rw [← hXZ, hz, add_zero]
      exact hY
    · intro X hX
      exact LinearMap.mem_ker.mpr (hzero X hX)

/-- The within-sector block of the transported operator basis is precisely
the fixed algebra of conjugation by the regular split-octonion `J`. -/
theorem legacyRegularJ_withinSector_iff_conjugation_fixed
    (X : Module.End ℝ Vec8R) :
    X ∈ legacyWithinSectorOperatorSubspace ↔
      legacyRegularJOperator * X * legacyRegularJOperator = X := by
  have hker := legacyRegularJ_projection_range_ker.2
  rw [← hker, LinearMap.mem_ker]
  exact legacyCoordinateCrossSectorProjection_eq_zero_iff_conjugation_fixed
    legacyRegularJOperator X legacyRegularJOperator_involution

/-- The cross-sector block of the transported operator basis is precisely
the sign-reversing subspace for conjugation by regular split-octonion `J`. -/
theorem legacyRegularJ_crossSector_iff_conjugation_negated
    (X : Module.End ℝ Vec8R) :
    X ∈ legacyCrossSectorOperatorSubspace ↔
      legacyRegularJOperator * X * legacyRegularJOperator = -X := by
  have hrange := legacyRegularJ_projection_range_ker.1
  change LinearMap.range (legacyCoordinateCrossSectorProjection legacyRegularJOperator) =
    legacyCrossSectorOperatorSubspace at hrange
  rw [← hrange]
  have hproj :
      legacyCoordinateCrossSectorProjection legacyRegularJOperator *
        legacyCoordinateCrossSectorProjection legacyRegularJOperator =
      legacyCoordinateCrossSectorProjection legacyRegularJOperator := by
    simpa [legacyRegularJOperator] using
      legacyRegularJ_crossSectorProjection_idempotent
  have h_range_iff :
      X ∈ LinearMap.range (legacyCoordinateCrossSectorProjection legacyRegularJOperator) ↔
        legacyCoordinateCrossSectorProjection legacyRegularJOperator X = X := by
    constructor
    · rintro ⟨Y, rfl⟩
      have h := congrArg (fun f : Module.End ℝ (Module.End ℝ Vec8R) => f Y) hproj
      simpa only [Module.End.mul_apply] using h
    · intro hX
      exact ⟨X, hX⟩
  rw [h_range_iff]
  exact legacyCoordinateCrossSectorProjection_eq_self_iff_conjugation_negated
    legacyRegularJOperator X legacyRegularJOperator_involution

/-- The two operator sectors form a genuine `ℤ/2`-graded algebra under
composition: conjugation signs multiply, so equal parities compose to the
within-sector block and opposite parities compose to the cross-sector block.
-/
theorem legacyRegularJ_sector_product_rules
    {X Y : Module.End ℝ Vec8R} :
    (X ∈ legacyWithinSectorOperatorSubspace →
      Y ∈ legacyWithinSectorOperatorSubspace →
      X * Y ∈ legacyWithinSectorOperatorSubspace) ∧
    (X ∈ legacyWithinSectorOperatorSubspace →
      Y ∈ legacyCrossSectorOperatorSubspace →
      X * Y ∈ legacyCrossSectorOperatorSubspace) ∧
    (X ∈ legacyCrossSectorOperatorSubspace →
      Y ∈ legacyWithinSectorOperatorSubspace →
      X * Y ∈ legacyCrossSectorOperatorSubspace) ∧
    (X ∈ legacyCrossSectorOperatorSubspace →
      Y ∈ legacyCrossSectorOperatorSubspace →
      X * Y ∈ legacyWithinSectorOperatorSubspace) := by
  have hJ : legacyRegularJOperator * legacyRegularJOperator = 1 :=
    legacyRegularJOperator_involution
  have hconj : ∀ A B : Module.End ℝ Vec8R,
      legacyRegularJOperator * (A * B) * legacyRegularJOperator =
        (legacyRegularJOperator * A * legacyRegularJOperator) *
          (legacyRegularJOperator * B * legacyRegularJOperator) := by
    intro A B
    calc legacyRegularJOperator * (A * B) * legacyRegularJOperator
        = legacyRegularJOperator * A * (1 : Module.End ℝ Vec8R) * B *
            legacyRegularJOperator := by noncomm_ring
      _ = legacyRegularJOperator * A *
            (legacyRegularJOperator * legacyRegularJOperator) * B *
            legacyRegularJOperator := by rw [hJ]
      _ = (legacyRegularJOperator * A * legacyRegularJOperator) *
          (legacyRegularJOperator * B * legacyRegularJOperator) := by
            noncomm_ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hX hY
    rw [legacyRegularJ_withinSector_iff_conjugation_fixed] at hX hY ⊢
    rw [hconj, hX, hY]
  · intro hX hY
    rw [legacyRegularJ_withinSector_iff_conjugation_fixed] at hX
    rw [legacyRegularJ_crossSector_iff_conjugation_negated] at hY ⊢
    rw [hconj, hX, hY]
    exact mul_neg X Y
  · intro hX hY
    rw [legacyRegularJ_crossSector_iff_conjugation_negated] at hX
    rw [legacyRegularJ_withinSector_iff_conjugation_fixed] at hY
    rw [legacyRegularJ_crossSector_iff_conjugation_negated]
    rw [hconj, hX, hY]
    exact neg_mul X Y
  · intro hX hY
    rw [legacyRegularJ_crossSector_iff_conjugation_negated] at hX hY
    rw [legacyRegularJ_withinSector_iff_conjugation_fixed]
    rw [hconj, hX, hY]
    exact neg_mul_neg X Y

/-- Every legacy-coordinate operator has a canonical decomposition into its
within-sector remainder and cross-sector projection.  The projected term is
the cross component, and subtracting it leaves an element of the kernel. -/
theorem legacyRegularJ_canonical_sector_decomposition
    (X : Module.End ℝ Vec8R) :
    let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
    let P := legacyCoordinateCrossSectorProjection J
    X - P X ∈ legacyWithinSectorOperatorSubspace ∧
      P X ∈ legacyCrossSectorOperatorSubspace ∧ X = (X - P X) + P X := by
  dsimp only
  let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
    (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
  let P := legacyCoordinateCrossSectorProjection J
  have hIdem := congrArg (fun f : Module.End ℝ (Module.End ℝ Vec8R) => f X)
    legacyRegularJ_crossSectorProjection_idempotent
  have hP : P (P X) = P X := by
    simpa [P, J, Module.End.mul_apply] using hIdem
  rcases legacyRegularJ_projection_range_ker with ⟨hrange, hker⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← hker]
    apply LinearMap.mem_ker.mpr
    rw [map_sub, hP, sub_self]
  · rw [← hrange]
    exact ⟨X, rfl⟩
  · abel

/-- The within/cross sector decomposition is unique.  Its uniqueness follows
from the zero intersection already established for the two operator blocks. -/
theorem legacyRegularJ_sector_decomposition_unique
    (X : Module.End ℝ Vec8R) :
    ∃! yz : Module.End ℝ Vec8R × Module.End ℝ Vec8R,
      yz.1 ∈ legacyWithinSectorOperatorSubspace ∧
      yz.2 ∈ legacyCrossSectorOperatorSubspace ∧ X = yz.1 + yz.2 := by
  rcases legacyRegularJ_canonical_sector_decomposition X with ⟨hY, hZ, hsum⟩
  refine ⟨(X - (legacyCoordinateCrossSectorProjection
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) X,
    (legacyCoordinateCrossSectorProjection
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) X),
    ⟨hY, hZ, hsum⟩, ?_⟩
  intro yz hyz
  rcases hyz with ⟨hy, hz, hdecomp⟩
  have hdiff : (X - (legacyCoordinateCrossSectorProjection
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) X) - yz.1 =
      yz.2 - (legacyCoordinateCrossSectorProjection
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) X := by
    rw [hsum, hdecomp]
    abel
  have hzero : (X - (legacyCoordinateCrossSectorProjection
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) X) - yz.1 = 0 := by
    have hbot : (X - (legacyCoordinateCrossSectorProjection
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) X) - yz.1 ∈
        (⊥ : Submodule ℝ (Module.End ℝ Vec8R)) := by
      rw [← legacyWithin_inf_crossSector_eq_bot]
      constructor
      · exact sub_mem hY hy
      · rw [hdiff]
        exact sub_mem hz hZ
    simpa using hbot
  have hfirst : X - (legacyCoordinateCrossSectorProjection
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) X = yz.1 :=
    sub_eq_zero.mp hzero
  have hsecond : yz.2 = (legacyCoordinateCrossSectorProjection
      (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
          InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) X := by
    have hzero' : yz.2 - (legacyCoordinateCrossSectorProjection
        (InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
          (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
            InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus))) X = 0 := by
      rw [← hdiff, hzero]
    exact sub_eq_zero.mp hzero'
  exact Prod.ext hfirst.symm hsecond

/-- Exact count of the matrix units in the two regular-`J` sectors.  Each
Peirce eigenspace has four carrier coordinates, so the operator-space
decomposition has 32 within-sector and 32 cross-sector basis elements. -/
theorem legacyRegularJ_operatorSector_matrixUnit_counts :
    (∑ i : Fin 8, ∑ j : Fin 8,
      if (i.val < 4) = (j.val < 4) then 1 else 0) = 32 ∧
    (∑ i : Fin 8, ∑ j : Fin 8,
      if (i.val < 4) ≠ (j.val < 4) then 1 else 0) = 32 := by
  constructor <;>
    simp only [Fin.sum_univ_eight] <;>
    norm_num [Finset.card_filter]

private abbrev WithinSectorIndex :=
  {p : Fin 8 × Fin 8 // (p.1.val < 4) = (p.2.val < 4)}

private abbrev CrossSectorIndex :=
  {p : Fin 8 × Fin 8 // (p.1.val < 4) ≠ (p.2.val < 4)}

private def withinSectorFamily (p : WithinSectorIndex) : Module.End ℝ Vec8R :=
  legacyCoordinateEndBasis p.1

private def crossSectorFamily (p : CrossSectorIndex) : Module.End ℝ Vec8R :=
  legacyCoordinateEndBasis p.1

/-- The two eigenspaces of the normalized double commutator each have
dimension 32.  This upgrades the matrix-unit count to actual `finrank`
statements for the subspaces defined above. -/
theorem legacyRegularJ_operatorSector_finrank :
    Module.finrank ℝ legacyWithinSectorOperatorSubspace = 32 ∧
    Module.finrank ℝ legacyCrossSectorOperatorSubspace = 32 := by
  classical
  have hwithin_ind : LinearIndependent ℝ withinSectorFamily :=
    legacyCoordinateEndBasis.linearIndependent.comp Subtype.val Subtype.val_injective
  have hcross_ind : LinearIndependent ℝ crossSectorFamily :=
    legacyCoordinateEndBasis.linearIndependent.comp Subtype.val Subtype.val_injective
  have hwithin_span : Submodule.span ℝ (Set.range withinSectorFamily) =
      legacyWithinSectorOperatorSubspace := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro X ⟨p, rfl⟩
      exact Submodule.subset_span ⟨p.1.1, p.1.2, p.2, by
        change legacyCoordinateEndBasis (p.1.1, p.1.2) = _
        rw [legacyCoordinateEndBasis_apply]⟩
    · apply Submodule.span_le.mpr
      rintro X ⟨i, j, hsec, rfl⟩
      exact Submodule.subset_span ⟨⟨(i, j), hsec⟩, by
        change legacyCoordinateEndBasis (i, j) = _
        rw [legacyCoordinateEndBasis_apply]⟩
  have hcross_span : Submodule.span ℝ (Set.range crossSectorFamily) =
      legacyCrossSectorOperatorSubspace := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro X ⟨p, rfl⟩
      exact Submodule.subset_span ⟨p.1.1, p.1.2, p.2, by
        change legacyCoordinateEndBasis (p.1.1, p.1.2) = _
        rw [legacyCoordinateEndBasis_apply]⟩
    · apply Submodule.span_le.mpr
      rintro X ⟨i, j, hsec, rfl⟩
      exact Submodule.subset_span ⟨⟨(i, j), hsec⟩, by
        change legacyCoordinateEndBasis (i, j) = _
        rw [legacyCoordinateEndBasis_apply]⟩
  have hwithin_card : Fintype.card WithinSectorIndex = 32 := by
    decide
  have hcross_card : Fintype.card CrossSectorIndex = 32 := by
    decide
  constructor
  · rw [← hwithin_span, finrank_span_eq_card hwithin_ind, hwithin_card]
  · rw [← hcross_span, finrank_span_eq_card hcross_ind, hcross_card]

/-- The normalized regular-`J` double-commutator superoperator has rank and
nullity 32 on the 64-dimensional operator space.  Its image is exactly the
cross-sector block and its kernel exactly the within-sector block. -/
theorem legacyRegularJ_crossSectorProjection_rank_nullity :
    let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
    let P := legacyCoordinateCrossSectorProjection J
    Module.finrank ℝ (LinearMap.range P) = 32 ∧
      Module.finrank ℝ (LinearMap.ker P) = 32 := by
  dsimp only
  rcases legacyRegularJ_projection_range_ker with ⟨hrange, hker⟩
  rw [hrange, hker]
  exact ⟨legacyRegularJ_operatorSector_finrank.2,
    legacyRegularJ_operatorSector_finrank.1⟩

/-- Exact eigenspace description of the unnormalized regular-`J`
double-commutator on the full operator space: its zero eigenspace is the
within-sector block, and its eigenvalue-four eigenspace is the cross-sector
block. -/
theorem legacyRegularJ_doubleComm_eigenspaces
    (X : Module.End ℝ Vec8R) :
    let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
      (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
        InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
    (legacyCoordinateDoubleComm J X = 0 ↔
        X ∈ legacyWithinSectorOperatorSubspace) ∧
      (legacyCoordinateDoubleComm J X = 4 • X ↔
        X ∈ legacyCrossSectorOperatorSubspace) := by
  dsimp only
  let J := InfoGeometry.Lie.SplitOctonionCircularOperatorReadout.circularOperatorReadout
    (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.regularJ
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
      InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus)
  let P := legacyCoordinateCrossSectorProjection J
  have hscale : legacyCoordinateDoubleComm J X = 4 • P X := by
    change legacyCoordinateDoubleComm J X =
      4 • ((1 / 4 : ℝ) • legacyCoordinateDoubleComm J X)
    module
  rcases legacyRegularJ_projection_range_ker with ⟨hrange, hker⟩
  constructor
  · constructor
    · intro hzero
      have hPzero : P X = 0 := by
        have h := hscale.symm.trans hzero
        exact (smul_eq_zero.mp h).resolve_left (by norm_num)
      rw [← hker]
      exact LinearMap.mem_ker.mpr hPzero
    · intro hwithin
      have hPzero : P X = 0 := by
        apply LinearMap.mem_ker.mp
        rw [hker]
        exact hwithin
      rw [hscale, hPzero]
      simp
  · constructor
    · intro heigen
      have hPeq : P X = X := by
        have h := hscale.symm.trans heigen
        calc P X = (1 / 4 : ℝ) • (4 • P X) := by module
          _ = (1 / 4 : ℝ) • (4 • X) := congrArg (fun Y : Module.End ℝ Vec8R =>
            (1 / 4 : ℝ) • Y) h
          _ = X := by module
      rw [← hrange]
      exact ⟨X, hPeq⟩
    · intro hcross
      have hPeq : P X = X := by
        have h := legacyRegularJ_crossSectorProjection_eq_self hcross
        simpa [P, J] using h
      rw [hscale, hPeq]

end InfoGeometry.Lie.SplitOctonionCircularBasisTransition

end
