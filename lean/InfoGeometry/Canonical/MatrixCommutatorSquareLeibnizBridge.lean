import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.ChernClassInstantonTopologicalBridge
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
import InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
import InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
import InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.MatrixCommutatorSquareLeibnizBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
open InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Theorem**: Algebraic Matrix Commutator Leibniz Identity [A, F * F] = [A, F] * F + F * [A, F]. -/
theorem matrixCommutator_square_leibniz
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    matrixCommutator A (F * F) = matrixCommutator A F * F + F * matrixCommutator A F := by
  dsimp [matrixCommutator]
  noncomm_ring

/-- **Theorem**: Derived Covariant Derivative Leibniz Rule D_A (F * F) = (D_A F) * F + F * (D_A F) from Exterior Derivative Leibniz. -/
theorem covariantDerivative_square_leibniz_from_exterior_leibniz
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_d_leibniz : matrixExteriorDerivative d (F * F) = matrixExteriorDerivative d F * F + F * matrixExteriorDerivative d F) :
    covariantDerivative A d (F * F) = (covariantDerivative A d F) * F + F * (covariantDerivative A d F) := by
  dsimp [covariantDerivative]
  rw [h_d_leibniz]
  rw [matrixCommutator_square_leibniz]
  noncomm_ring

/-- **Theorem**: Master Matrix Commutator Square Leibniz Synthesis.
    Unifies:
    1. Pure algebraic proof closure of commutator Leibniz product rule [A, F * F] = [A, F] * F + F * [A, F] without extra assumptions.
    2. Derivation of covariant derivative Leibniz rule D_A (F * F) = (D_A F) * F + F * (D_A F) from exterior derivative Leibniz rule.
    3. Removal of the commutator half of the Leibniz assumption in non-Abelian Chern-Weil gauge field theory. -/
theorem master_matrix_commutator_square_leibniz_synthesis
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_d_leibniz : matrixExteriorDerivative d (F * F) = matrixExteriorDerivative d F * F + F * matrixExteriorDerivative d F) :
    (matrixCommutator A (F * F) = matrixCommutator A F * F + F * matrixCommutator A F) ∧
    (covariantDerivative A d (F * F) = (covariantDerivative A d F) * F + F * (covariantDerivative A d F)) := ⟨
  matrixCommutator_square_leibniz A F,
  covariantDerivative_square_leibniz_from_exterior_leibniz A F d h_d_leibniz
⟩

end InfoGeometry.Canonical.MatrixCommutatorSquareLeibnizBridge
