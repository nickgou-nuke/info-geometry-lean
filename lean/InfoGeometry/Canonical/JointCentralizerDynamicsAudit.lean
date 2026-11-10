/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteMatrixNoncommutativity
import InfoGeometry.Canonical.JointCentralizerGeometry
import InfoGeometry.Canonical.JointCentralizerDynamics
import InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Dense real witnesses for the flow boundary

The carrier remains the full algebra of real `3 × 3` matrices. The boost
expressions use the existing completed Peirce block, including its nonzero
harmonic corner. No new flow or diagonal matrix surrogate is defined.
-/

namespace InfoGeometry.Canonical.JointCentralizerDynamicsAudit

open Matrix InfoGeometry.Core.DualSeedPeirce InfoGeometry.Core.PeirceRotor
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Canonical.JointCentralizerGeometry
open InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses

/-- The Cartan centralizer has strictly more elements than the common commutant,
on the existing nonzero dense pair. -/
theorem denseSeed_jointCentralizer_lt_phaseCentralizer :
    Subalgebra.centralizer ℝ
      ({denseSeed, denseSeedᴴ} : Set (Matrix (Fin 3) (Fin 3) ℝ)) <
    Subalgebra.centralizer ℝ
      ({phasePolarization denseSeed denseSeedᴴ} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
  jointCentralizer_lt_phaseCentralizer denseSeed_pair denseSeed_ne_zero

/-- A unit parabolic shear changes the directional centralizer projection. -/
theorem denseSeed_parabolic_projection_ne :
    centralizerProjection ℝ denseSeed denseSeedᴴ
      ((1 + denseSeed) * denseSeedᴴ * (1 - denseSeed)) ≠
    centralizerProjection ℝ denseSeed denseSeedᴴ denseSeedᴴ := by
  have hshear :=
    denseSeed_pair.centralizerProjection_unipotent_partner (R := ℝ) (1 : ℝ)
  simp only [one_smul] at hshear
  rw [hshear, denseSeed_pair.centralizerProjection_partner]
  exact denseSeed_pair.support_ne_zero denseSeed_ne_zero

/-- The actual dense completed boost at reciprocal weights `2, 1/2`
has volume determinant one. This is a finite matrix determinant statement. -/
theorem denseSeed_completed_boost_det :
    Matrix.det (completedBlock denseSeed denseSeedᴴ (2 : ℝ) 0 0 (1 / 2)) = 1 := by
  norm_num [completedBlock, peirceBlock, zeroModeSupport, harmonicSupport,
    polePlus, poleMinus, exactSupport, coexactSupport, denseSeed,
    Matrix.det_fin_three, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMul, dotProduct, Matrix.transpose_apply, Fin.sum_univ_succ]

/-- Despite its determinant-one value, the same dense boost acts nontrivially. -/
theorem denseSeed_completed_boost_moves_seed :
    completedBlock denseSeed denseSeedᴴ (2 : ℝ) 0 0 (1 / 2) * denseSeed *
      completedBlock denseSeed denseSeedᴴ (1 / 2 : ℝ) 0 0 2 ≠ denseSeed := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  norm_num [completedBlock, peirceBlock, zeroModeSupport, harmonicSupport,
    polePlus, poleMinus, exactSupport, coexactSupport, denseSeed,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_succ] at h00

/-- Real hyperbolic similarity does not preserve the Hilbert adjoint.
This refutes identifying this real boost with a star-automorphism flow. -/
theorem denseSeed_completed_boost_star_failure :
    (completedBlock denseSeed denseSeedᴴ (2 : ℝ) 0 0 (1 / 2) * denseSeed *
      completedBlock denseSeed denseSeedᴴ (1 / 2 : ℝ) 0 0 2)ᴴ ≠
    completedBlock denseSeed denseSeedᴴ (2 : ℝ) 0 0 (1 / 2) * denseSeedᴴ *
      completedBlock denseSeed denseSeedᴴ (1 / 2 : ℝ) 0 0 2 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  norm_num [completedBlock, peirceBlock, zeroModeSupport, harmonicSupport,
    polePlus, poleMinus, exactSupport, coexactSupport, denseSeed,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_succ] at h00

#print axioms JointCentralizerDynamics.exp_phasePolarization
#print axioms JointCentralizerDynamics.splitCartanHom_eq_diagonalUnit
#print axioms JointCentralizerDynamics.splitCartan_conjugates_seed
#print axioms JointCentralizerDynamics.splitCartan_conjugates_partner
#print axioms JointCentralizerDynamics.splitCartan_fixes_jointCentralizer
#print axioms JointCentralizerDynamics.centralizerProjection_splitCartan
#print axioms IsDualSeedPair.centralizerProjection_of_anticommute
#print axioms denseSeed_jointCentralizer_lt_phaseCentralizer
#print axioms denseSeed_parabolic_projection_ne
#print axioms denseSeed_completed_boost_det
#print axioms denseSeed_completed_boost_moves_seed
#print axioms denseSeed_completed_boost_star_failure

end InfoGeometry.Canonical.JointCentralizerDynamicsAudit
