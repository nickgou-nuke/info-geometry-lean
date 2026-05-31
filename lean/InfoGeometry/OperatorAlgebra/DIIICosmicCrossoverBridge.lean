/-
InfoGeometry/OperatorAlgebra/DIIICosmicCrossoverBridge.lean

Constructive bridge from the DIII CPT branch to the cosmic Andreev crossover
socket.

This file replaces the crossover swap hypothesis by the concrete DIII
particle-hole/CPT conjugation:

  theta x = C * x * C.

The existing DIII branch theorems prove that this closure swaps the two chiral
half-projectors.  Therefore the diagonal survives and the chiral imbalance is
anti-fixed without an additional reflection witness.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.CosmicAndreevCrossover
import InfoGeometry.OperatorAlgebra.DIIISuperfluidBranch

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DIIISuperfluidBranch

open InfoGeometry.OperatorAlgebra.AndreevBoundary
open InfoGeometry.OperatorAlgebra.ClosureInvolution
open InfoGeometry.OperatorAlgebra.CosmicAndreevCrossover

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

namespace DIIICPTBranchDatum

variable (D : DIIICPTBranchDatum Op)

/-- CPT conjugation by the DIII particle-hole operator. -/
def cptConjugationLinear : Op →ₗ[ℝ] Op where
  toFun := fun x => D.C * x * D.C
  map_add' := by
    intro x y
    rw [mul_add, add_mul]
  map_smul' := by
    intro a x
    calc
      D.C * (a • x) * D.C
          = (a • (D.C * x)) * D.C := by
              rw [mul_smul_comm]
      _ = a • (D.C * x * D.C) := by
              rw [smul_mul_assoc]

/-- CPT conjugation is involutive because `C² = 1`. -/
theorem cptConjugationLinear_involutive
    (x : Op) :
    D.cptConjugationLinear (D.cptConjugationLinear x) = x := by
  calc
    D.cptConjugationLinear (D.cptConjugationLinear x)
        = D.C * (D.C * x * D.C) * D.C := rfl
    _ = (D.C * D.C) * x * (D.C * D.C) := by
          noncomm_ring
    _ = (1 : Op) * x * (1 : Op) := by
          rw [D.C_square]
    _ = x := by
          simp

/-- The DIII CPT conjugation closure involution. -/
def cptClosure : LinearClosureInvolution Op where
  theta := D.cptConjugationLinear
  theta_involutive := D.cptConjugationLinear_involutive

/-- CPT closure sends the left DIII chiral projector to the right one. -/
theorem cptClosure_theta_P_left :
    D.cptClosure.theta D.P_left = D.P_right := by
  exact D.C_conj_P_left

/-- CPT closure sends the right DIII chiral projector to the left one. -/
theorem cptClosure_theta_P_right :
    D.cptClosure.theta D.P_right = D.P_left := by
  exact D.C_conj_P_right

/-- The DIII CPT datum gives an Andreev boundary datum on chiral projectors. -/
def toAndreevBoundaryDatum : AndreevBoundaryDatum Op where
  closure := D.cptClosure
  electron := D.P_left
  hole := D.P_right
  theta_electron := D.cptClosure_theta_P_left

/--
Concrete interpretation law for the DIII/Cosmic bridge: the installed closure
is CPT conjugation and it swaps the two DIII chiral half-projectors.
-/
def cosmicCrossoverInterpretationLaw : Prop :=
  D.cptClosure.theta D.P_left = D.P_right ∧
    D.cptClosure.theta D.P_right = D.P_left

/-- The DIII projector-swap law is constructively supplied by CPT conjugation. -/
theorem cosmicCrossoverInterpretation_holds :
    D.cosmicCrossoverInterpretationLaw :=
  ⟨D.cptClosure_theta_P_left, D.cptClosure_theta_P_right⟩

/--
The DIII CPT branch constructs a cosmic Andreev crossover witness whose old/new
data are the left/right chiral projectors.
-/
def toCosmicCrossoverWitness : CosmicCrossoverWitness Op where
  boundary := D.toAndreevBoundaryDatum
  oldNullData := D.P_left
  newMetricData := D.P_right
  reflection_True := D.cptClosure_theta_P_left
  crossover_interpretation_True := D.cosmicCrossoverInterpretationLaw
  crossover_interpretation_sorryProof := D.cosmicCrossoverInterpretation_holds

/-- The DIII chiral diagonal survives the CPT/crossover closure. -/
theorem cpt_crossover_diagonal_fixed :
    D.P_left + D.P_right ∈ D.cptClosure.Fixed :=
  (D.toCosmicCrossoverWitness).crossover_diagonal_fixed

/-- The DIII chiral imbalance is anti-fixed by the CPT/crossover closure. -/
theorem cpt_chiral_imbalance_anti_fixed :
    D.cptClosure.theta (D.P_left - D.P_right) =
      -(D.P_left - D.P_right) :=
  (D.toCosmicCrossoverWitness).crossover_imbalance_anti_fixed

end DIIICPTBranchDatum

end InfoGeometry.OperatorAlgebra.DIIISuperfluidBranch
