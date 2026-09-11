import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
import InfoGeometry.Thermo.SouriauOnsagerBKMProbe
import InfoGeometry.Canonical.CuntzMatrixTraceTower

/-!
# Finite operator readout of Cantor cylinders

An `n`-cylinder is a diagonal observable on the finite `BitWord n` stage.
This owner makes that already existing identification explicit as a genuine
finite matrix, before any trace or BKM functional is applied.  It introduces
no completion and no state on the infinite boundary.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCylinderFiniteOperatorReadout

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Thermo.SouriauOnsagerBKMProbe
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

/-- The finite diagonal operator represented by a cylinder observable. -/
def cylinderMatrix (n : ℕ) (f : DiagAlg n) : BitWordMatrixStage n :=
  Matrix.diagonal f

@[simp] theorem cylinderMatrix_apply (n : ℕ) (f : DiagAlg n)
    (u v : BitWord n) :
    cylinderMatrix n f u v = if u = v then f u else 0 := by
  by_cases h : u = v
  · subst v
    simp [cylinderMatrix]
  · simp [cylinderMatrix, h]

/-- The diagonal matrix readout at a boundary point is its cylinder value. -/
theorem cylinderMatrix_boundary_readout
    (n : ℕ) (f : DiagAlg n) (b : ℕ → Bool) :
    cylinderMatrix n f (boundaryPrefix n b) (boundaryPrefix n b) =
      cylinder n f b := by
  simp [cylinderMatrix, cylinder]

/-- The cylinder map factors through the finite diagonal operator readout. -/
theorem cylinder_eq_finite_operator_readout
    (n : ℕ) (f : DiagAlg n) :
    cylinder n f =
      fun b => cylinderMatrix n f (boundaryPrefix n b) (boundaryPrefix n b) := by
  funext b
  exact (cylinderMatrix_boundary_readout n f b).symm

/-- The finite normalized trace/BKM probe reads a cylinder as its dyadic
average.  This is the finite-stage boundary-to-probe square. -/
theorem traceProbe_cylinderMatrix
    (n : ℕ) (f : DiagAlg n) :
    bitWordMatrixTraceProbe n (cylinderMatrix n f) =
      (1 / (2 ^ n : ℂ)) * ∑ w : BitWord n, f w := by
  rw [bitWordMatrixTraceProbe_eq_gaugeReadout]
  unfold bitWordMatrixGaugeReadout cylinderMatrix
  simp_rw [Matrix.diagonal_apply_eq]
  simp_rw [canonicalGaugeState_proj, List.length_ofFn]
  have hpow : (1 / 2 : ℂ) ^ n = 1 / (2 ^ n : ℂ) := by
    simpa only [one_div] using (inv_pow (2 : ℂ) n)
  rw [← Finset.sum_mul, hpow]
  ring

/- The same finite cylinder, now viewed in the genuine bounded-operator
 carrier used by the BKM construction. -/
def cylinderFiniteOperator (n : ℕ) (f : DiagAlg n) :
    FiniteOperatorAlgebra (2 ^ n) :=
  matrixOp
    (bitWordStageStarAlgEquiv n (cylinderMatrix n f))

theorem finiteOperatorTrace_cylinderFiniteOperator_eq_traceProbe
    (n : ℕ) (f : DiagAlg n) :
    finiteOperatorTrace (cylinderFiniteOperator n f) =
      (2 ^ n : ℂ) * bitWordMatrixTraceProbe n (cylinderMatrix n f) := by
  unfold finiteOperatorTrace cylinderFiniteOperator
  simp only [matrixOfOp_matrixOp]
  rw [bitWordMatrixTraceProbe_apply, matrixTraceProbe_apply]
  simp only [matrixTraceState_apply]
  field_simp

/-- The unnormalised operator trace is the finite dyadic sum of the cylinder. -/
theorem finiteOperatorTrace_cylinderFiniteOperator_eq_dyadicAverage
    (n : ℕ) (f : DiagAlg n) :
    finiteOperatorTrace (cylinderFiniteOperator n f) =
      ∑ w : BitWord n, f w := by
  rw [finiteOperatorTrace_cylinderFiniteOperator_eq_traceProbe,
    traceProbe_cylinderMatrix]
  field_simp

/-- The canonical maximally-mixed BKM kernel reads the same dyadic cylinder
probe as the boundary trace, after transporting the diagonal stage operator
to the finite bounded-operator carrier. -/
theorem maximallyMixed_bkm_kernel_cylinderFiniteOperator
    (n : ℕ) (s : ℝ) (f : DiagAlg n) :
    (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ n)) s
        (cylinderFiniteOperator n f) =
      bitWordMatrixTraceProbe n (cylinderMatrix n f) := by
  rw [maximallyMixed_bkm_kernel_eq_normalized_trace]
  rw [finiteOperatorTrace_cylinderFiniteOperator_eq_traceProbe]
  field_simp

/-- The same commuting square written entirely in the finite boundary
coordinates: the BKM kernel is the dyadic average of the cylinder values. -/
theorem maximallyMixed_bkm_kernel_cylinderFiniteOperator_eq_dyadicAverage
    (n : ℕ) (s : ℝ) (f : DiagAlg n) :
    (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ n)) s
        (cylinderFiniteOperator n f) =
      (1 / (2 ^ n : ℂ)) * ∑ w : BitWord n, f w := by
  rw [maximallyMixed_bkm_kernel_cylinderFiniteOperator,
    traceProbe_cylinderMatrix]

/- The finite boundary-to-operator square: the pointwise cylinder pullback
and the maximally-mixed operatorial BKM readout are the two sides of the same
finite-stage construction. -/
theorem boundary_to_operatorial_bkm_square
    (n : ℕ) (s : ℝ) (f : DiagAlg n) (b : ℕ → Bool) :
    cylinder n f b =
        cylinderMatrix n f (boundaryPrefix n b) (boundaryPrefix n b) ∧
      (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
          (1 : FiniteOperatorAlgebra (2 ^ n)) s
          (cylinderFiniteOperator n f) =
        (1 / (2 ^ n : ℂ)) * ∑ w : BitWord n, f w := by
  constructor
  · exact (cylinderMatrix_boundary_readout n f b).symm
  · rw [maximallyMixed_bkm_kernel_cylinderFiniteOperator_eq_dyadicAverage]

end InfoGeometry.Canonical.CantorCylinderFiniteOperatorReadout
