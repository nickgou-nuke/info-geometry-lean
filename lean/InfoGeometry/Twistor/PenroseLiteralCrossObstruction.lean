import InfoGeometry.Twistor.PenroseSignedCCRGeometry

/-!
# An exact obstruction to the literal CCR cross-product proposal

The source defines `A cross B = [IA, IB, IE]` in (7.105), after deriving the
linear contraction triple from central CCR in (7.89)--(7.90). We test that
literal proposal, not an unspecified corrected cross product.

The scalar term of (7.107) is kept as a free normalization `k`. Both the
printed `k=1` and the norm-normalized `k=1/2` fail left alternativity on the
same explicit coordinate pair. The counterexample does not refute the
existence of a split-octonion product on this quadratic space; it proves
that extra multiplication data are needed beyond this particular triple.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseLiteralCrossObstruction

open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenroseSignedCCRGeometry

/-- A positive unit-normalized real twistor. -/
def chosenUnit : TwistorCarrier := ![1, 0, 0, 0]

/-- Two nonisotropic vectors orthogonal to the chosen complex unit line. -/
def testX : TwistorCarrier := ![0, 1, 0, 0]
def testY : TwistorCarrier := ![0, 0, 1, 0]

@[simp] theorem chosenUnit_metric : metric chosenUnit chosenUnit = 2 := by
    norm_num [chosenUnit, twistorHermitian_apply, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_fin_one]

/-- The source's scalar projection with its stated `E dot E = 2` normalization. -/
def scalarPart (x : TwistorCarrier) : ℝ := metric x chosenUnit / 2

def vectorPart (x : TwistorCarrier) : TwistorCarrier := x - scalarPart x • chosenUnit

/-- The exact expression displayed in equation (7.105). -/
def literalCross (x y : TwistorCarrier) : TwistorCarrier :=
  realTriple (phaseJ x) (phaseJ y) (phaseJ chosenUnit)

/-- The image degenerates to one line on the symplectic-orthogonal hyperplane. -/
theorem literalCross_line_image (x y : TwistorCarrier)
    (hx : symplectic x chosenUnit = 0) (hy : symplectic y chosenUnit = 0) :
    literalCross x y = symplectic x y • phaseJ chosenUnit := by
  unfold literalCross realTriple
  rw [symplectic_phaseJ, symplectic_phaseJ, symplectic_phaseJ,
    symplectic_skew chosenUnit x, hx, hy]
  simp

theorem scalar_vector_reconstruction (x : TwistorCarrier) :
    scalarPart x • chosenUnit + vectorPart x = x := by
  unfold vectorPart
  abel

theorem vectorPart_orthogonal (x : TwistorCarrier) : metric (vectorPart x) chosenUnit = 0 := by
  simp only [vectorPart, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, chosenUnit_metric]
  unfold scalarPart
  ring

/-- Explicit signature and orthogonality data of the test pair. -/
theorem test_pair_geometry :
    metric testX testX = 2 ∧ metric testY testY = -2 ∧
      metric testX testY = 0 ∧ scalarPart testX = 0 ∧ scalarPart testY = 0 := by
  norm_num [testX, testY, scalarPart, chosenUnit, twistorHermitian_apply,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_fin_one]

/-- The proposed cross product vanishes on this independent, nonisotropic pair. -/
theorem literalCross_test_pair : literalCross testX testY = 0 := by
  funext i
  fin_cases i <;>
    norm_num [literalCross, realTriple, symplectic_eq_im, phaseJ, chosenUnit,
      testX, testY, twistorHermitian_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_fin_one]

/-- Source scalar/vector assembly, with the scalar metric coefficient exposed. -/
def candidateProduct (k : ℝ) (x y : TwistorCarrier) : TwistorCarrier :=
  (scalarPart x * scalarPart y - k * metric (vectorPart x) (vectorPart y)) • chosenUnit +
    (scalarPart x • vectorPart y + scalarPart y • vectorPart x +
      literalCross (vectorPart x) (vectorPart y))

@[simp] theorem candidate_zero_right (k : ℝ) (x : TwistorCarrier) :
    candidateProduct k x 0 = 0 := by
  simp [candidateProduct, scalarPart, vectorPart, literalCross, realTriple, symplectic]

/-- The scalar line acts as intended: the obstruction is not a missing unit law. -/
theorem candidate_scalar_left (k a : ℝ) (y : TwistorCarrier) :
    candidateProduct k (a • chosenUnit) y = a • y := by
  have hs : scalarPart (a • chosenUnit) = a := by
    simp only [scalarPart, map_smul, LinearMap.smul_apply, smul_eq_mul, chosenUnit_metric]
    ring
  have hv : vectorPart (a • chosenUnit) = 0 := by simp [vectorPart, hs]
  simp only [candidateProduct, hs, hv]
  simp [literalCross, realTriple, symplectic, vectorPart, smul_sub, smul_smul] <;> abel

/-- Two exact native-coordinate products used in the alternativity counterexample. -/
theorem candidate_test_products (k : ℝ) :
    candidateProduct k testX testY = 0 ∧
      candidateProduct k testX testX = (-2 * k) • chosenUnit := by
  constructor <;> funext i <;> fin_cases i <;> apply Complex.ext <;>
    simp [candidateProduct, scalarPart, vectorPart, literalCross, realTriple,
      symplectic_eq_im, phaseJ, chosenUnit, testX, testY,
      twistorHermitian_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_fin_one] <;> ring

/-- Left alternativity fails for every nonzero scalar normalization. -/
theorem candidate_not_left_alternative (k : ℝ) (hk : k ≠ 0) :
    candidateProduct k testX (candidateProduct k testX testY) ≠
      candidateProduct k (candidateProduct k testX testX) testY := by
  rw [(candidate_test_products k).1, (candidate_test_products k).2,
    candidate_zero_right, candidate_scalar_left]
  intro h
  have h2 := congrArg (fun z : TwistorCarrier => (z 2).re) h
  simp [testY] at h2
  apply hk
  linarith

/-- The printed and norm-normalized readings both have the same obstruction. -/
theorem printed_and_normalized_obstruction :
    (¬ ∀ x y, candidateProduct 1 x (candidateProduct 1 x y) =
      candidateProduct 1 (candidateProduct 1 x x) y) ∧
    (¬ ∀ x y, candidateProduct (1/2) x (candidateProduct (1/2) x y) =
      candidateProduct (1/2) (candidateProduct (1/2) x x) y) := by
  constructor
  · intro h
    exact candidate_not_left_alternative 1 (by norm_num) (h testX testY)
  · intro h
    exact candidate_not_left_alternative (1/2) (by norm_num) (h testX testY)

/-- Composition also fails: the two input norms are +1 and -1, but their product is zero. -/
theorem candidate_not_composition (k : ℝ) :
    twistorRealQuadraticForm (candidateProduct k testX testY) ≠
      twistorRealQuadraticForm testX * twistorRealQuadraticForm testY := by
  rw [(candidate_test_products k).1]
  simp [twistorRealQuadraticForm_apply, helicity, testX, testY,
    twistorHermitian_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_fin_one]

end InfoGeometry.Twistor.PenroseLiteralCrossObstruction
