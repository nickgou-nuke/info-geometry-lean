/-
InfoGeometry/OperatorAlgebra/IndividuatedCl44Casimir.lean

Constructive Cl(4,4) Casimir readout.

This module removes the Pfaffian-as-Casimir shortcut.

The primary Casimir candidate is the Clifford trace/readout of the Drazin-core
Dirac-Souriau operator

  P_D D.

The resulting Casimir element is the scalar identity multiple determined by the
scalar and pseudoscalar Clifford readouts.  A Pfaffian interpretation is kept as
a separate calibration, not as the definition of the Casimir.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.VerifiedCasimir
import InfoGeometry.Canonical.DiracSouriauOperator

noncomputable section

namespace InfoGeometry.OperatorAlgebra.IndividuatedCl44Casimir

open Matrix
open InfoGeometry.OperatorAlgebra
open IndividuatedCasimir
open InfoGeometry.Canonical.DiracSouriau

/-! ## 1. The Cl(4,4) Operator Algebra and Symmetry Action -/

/--
The `4 × 4` Dirac-Souriau operator algebra.

The index is the block index used by `DiracSouriauSector.toMatrix`, so the
Drazin-core compression can be formed without an artificial reindexing.
-/
abbrev Op := Matrix (Fin 4) (Fin 4) ℝ

/--
The block-indexed `4 × 4` operator algebra used by the Dirac-Souriau sector.
-/
abbrev DiracSouriauOp :=
  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ

/-! ## 2. The Constructive Casimir Synthesis (Rubedo) -/

/--
A Drazin-core Clifford trace datum for the Dirac-Souriau operator.

`coreProjector` is the Drazin-core projector `P_D`.

The scalar and pseudoscalar readouts are intentionally separate.  In a concrete
Cl(4,4) model they should be the grade-`0` and top-grade Clifford trace
components.  This module only needs their resulting scalar values.
-/
structure DiracSouriauCoreTrace where
  /-- Dirac-Souriau sector whose assembled matrix is the operator `D`. -/
  sector : DiracSouriauSector ℝ

  /-- Drazin-core projector `P_D`. -/
  coreProjector : DiracSouriauOp

  /-- Scalar-grade Clifford trace/readout. -/
  scalarTrace : DiracSouriauOp → ℝ

  /-- Pseudoscalar/top-grade Clifford trace/readout. -/
  pseudoscalarTrace : DiracSouriauOp → ℝ

namespace DiracSouriauCoreTrace

variable (T : DiracSouriauCoreTrace)

/-- The Drazin-compressed Dirac-Souriau operator `P_D D`. -/
def drazinCoreOperator : DiracSouriauOp :=
  T.coreProjector * T.sector.toMatrix

/--
The scalar Casimir candidate obtained from the Clifford scalar and
pseudoscalar readouts of the Drazin core.
-/
def constructCasimirCandidate : ℝ :=
  T.scalarTrace T.drazinCoreOperator + T.pseudoscalarTrace T.drazinCoreOperator

/--
The central operator represented by the Clifford-trace Casimir candidate.
-/
def constructCasimirElement : DiracSouriauOp :=
  T.constructCasimirCandidate • (1 : DiracSouriauOp)

/-- The candidate is exactly the scalar plus pseudoscalar readout of `P_D D`. -/
theorem constructCasimirCandidate_eq_trace_sum :
    T.constructCasimirCandidate =
      T.scalarTrace T.drazinCoreOperator + T.pseudoscalarTrace T.drazinCoreOperator :=
  rfl

end DiracSouriauCoreTrace

/--
CONSTRUCTIVE THEOREM: the Clifford-trace Dirac-Souriau Casimir.

The Casimir element is the identity operator scaled by the Clifford trace
readout of the Drazin-compressed core `P_D D`.
-/
def diracSouriauCasimir
    (T : DiracSouriauCoreTrace)
    : DiracSouriauOp :=
  T.constructCasimirElement

theorem diracSouriauCasimir_invariant
    {G : Type*} [Group G]
    (S : OperatorSymmetryAction G DiracSouriauOp)
    (T : DiracSouriauCoreTrace) :
    IsInvariant (toSymmetryAction S) (diracSouriauCasimir T) := by
    dsimp [diracSouriauCasimir, DiracSouriauCoreTrace.constructCasimirElement,
      toSymmetryAction]
    intro g
    change S.act g (T.constructCasimirCandidate • (1 : DiracSouriauOp)) =
      T.constructCasimirCandidate • (1 : DiracSouriauOp)
    rw [S.act_smul, S.map_one]

theorem diracSouriauCasimir_central
    (T : DiracSouriauCoreTrace) :
    ∀ x : DiracSouriauOp, diracSouriauCasimir T * x = x * diracSouriauCasimir T := by
    intro x
    dsimp [diracSouriauCasimir, DiracSouriauCoreTrace.constructCasimirElement]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

/-
  is_invariant := by
    intro g
    dsimp [DiracSouriauCoreTrace.constructCasimirElement, toSymmetryAction]
    rw [S.act_smul, S.map_one]

  is_central := by
    intro x
    -- Scalar multiples of identity commute with everything.
    dsimp [DiracSouriauCoreTrace.constructCasimirElement]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
-/

/--
The Casimir element is the scalar identity multiple built from the Clifford
trace candidate.
-/
theorem diracSouriauCasimir_eq_trace_identity
    (T : DiracSouriauCoreTrace) :
    diracSouriauCasimir T =
      T.constructCasimirCandidate • (1 : DiracSouriauOp) :=
  rfl

/-! ## 3. Optional Pfaffian calibration -/

/--
Calibration connecting the Clifford-trace Casimir candidate with the Pfaffian
proxy of the topological block.

This is deliberately separate from `constructCasimirCandidate`: evaluating a
Pfaffian is a characteristic-polynomial/topological readout, and it should only
be identified with the Clifford trace candidate after a concrete model proves
the calibration.
-/
structure PfaffianCasimirCalibration
    (T : DiracSouriauCoreTrace) where
  /-- The sector Pfaffian matches the Clifford trace candidate. -/
  pfaffian_eq_constructCasimirCandidate :
    T.sector.pfaffian = T.constructCasimirCandidate

namespace PfaffianCasimirCalibration

variable {T : DiracSouriauCoreTrace}
variable (P : PfaffianCasimirCalibration T)

/-- Re-export the Pfaffian/Casimir calibration law. -/
theorem pfaffian_eq_casimirCandidate
    (P : PfaffianCasimirCalibration T) :
    T.sector.pfaffian = T.constructCasimirCandidate :=
  P.pfaffian_eq_constructCasimirCandidate

/--
Under a Pfaffian calibration, the Clifford-trace Casimir element can be written
as the Pfaffian scalar multiple of the identity.
-/
theorem casimir_eq_pfaffian_identity
    (P : PfaffianCasimirCalibration T) :
    diracSouriauCasimir T =
      T.sector.pfaffian • (1 : DiracSouriauOp) := by
  rw [diracSouriauCasimir_eq_trace_identity]
  rw [P.pfaffian_eq_constructCasimirCandidate]

end PfaffianCasimirCalibration

end InfoGeometry.OperatorAlgebra.IndividuatedCl44Casimir
