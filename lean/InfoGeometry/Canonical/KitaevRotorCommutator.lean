/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevRotorChordalTrace

/-! The rotor commutator in the actual chain boundary algebra, with its
constructed indefinite adjoint. Its Dirac trace square can be negative. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevRotorCommutator
open InfoGeometry.Quantum.KitaevChain
open CARMajoranaFiniteBridge KitaevConcreteBoundary KitaevBoundaryDiracPair KitaevBoundaryAlgebra
open KitaevBoundaryTraceNormalization PeirceRotorAction PeirceRotorChordal
open ReflexiveNilpotentFlows

/-- Commutator with the native boundary occupation. -/
def boundaryCommutator (c s : ℂ) : ChainOp :=
  let d := boundaryAnnihilation (by decide) twoSiteOperators
  let B := boundaryCreation (by decide) twoSiteOperators
  (d*B)*movingPlus c s d B - movingPlus c s d B*(d*B)

theorem boundaryCommutator_matrix (c s : ℂ) :
    boundaryCommutator c s =
      boundaryMatrixHom (by decide) twoSiteOperators !![0, -(c*s); c*s, 0] := by
  unfold boundaryCommutator
  rw [plus_movingPlus_commutator (boundaryAnnihilation_sq (by decide) twoSiteOperators)
    (boundaryCreation_sq (by decide) twoSiteOperators)
    (boundary_reflexive (by decide) twoSiteOperators).1
    (boundary_reflexive (by decide) twoSiteOperators).2]
  change _ = pairMatrixLinear _ _ _
  simp [pairMatrixLinear_apply, pairMatrixUnit, smul_sub, neg_smul]

theorem boundaryCommutator_commutes (c s t : ℂ) :
    Commute (boundaryCommutator c s)
      (sweetSpotHamiltonian twoSiteOperators.toMajoranaOperators
        (algebraMap ℂ ChainOp t)) := by
  rw [boundaryCommutator_matrix]
  exact boundaryMatrixHom_commutes (by decide) twoSiteOperators t _

theorem boundaryCommutator_dirac_trace (c s : ℂ) :
    Matrix.trace (boundaryCommutator c s *
      twoSiteKreinData.diracAdjoint (boundaryCommutator c s)) =
      -4 * (c*s) * star (c*s) := by
  rw [boundaryCommutator_matrix, boundaryMatrixHom_dirac_trace]
  simp [pairDiracMetric, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

theorem circular_commutator_dirac_trace_negative :
    Matrix.trace (boundaryCommutator (3/5) (4/5) *
      twoSiteKreinData.diracAdjoint (boundaryCommutator (3/5) (4/5))) =
      (-576/625 : ℂ) := by
  rw [boundaryCommutator_dirac_trace]
  norm_num

end InfoGeometry.Canonical.KitaevRotorCommutator
