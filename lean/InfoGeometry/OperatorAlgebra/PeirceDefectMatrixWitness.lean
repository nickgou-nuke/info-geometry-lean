/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Noncommuting matrix witnesses for the Peirce defect bridge

The examples live in the full matrix algebra `M₂(ℚ)`.  The cut is a
nontrivial idempotent.  A self-adjoint witness has nonzero entries in both
off-diagonal corners; a one-sided idempotent separately shows why zero
quadratic defect does not imply zero current without additional
star/positivity hypotheses.  That calculation is reproduced by
`scripts/cas/peirce_one_sided_zero_metric_witness.py`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceDefectMatrixWitness

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian

abbrev Op := Matrix (Fin 2) (Fin 2) ℚ

/-- The coordinate cut onto the first summand of the two-site module. -/
def cut : Op := !![1, 0; 0, 0]

/-- A self-adjoint idempotent with coherence across the cut. -/
def state : Op := !![(1 : ℚ) / 2, 1 / 2; 1 / 2, 1 / 2]

/-- A one-sided idempotent whose upper Peirce boundary is nonzero and whose
lower Peirce boundary vanishes.  It is deliberately not self-adjoint. -/
def oneSidedIdempotent : Op := !![1, 1; 0, 0]

/-- The cut is idempotent. -/
theorem cut_idempotent : cut * cut = cut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cut, Matrix.mul_apply, Fin.sum_univ_two]

/-- The full matrix state is idempotent. -/
theorem state_idempotent : state * state = state := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [state, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix state is self-adjoint under the standard matrix star operation. -/
theorem state_selfAdjoint : star state = state := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [state]

/-- The state fails to commute with the cut, witnessed by its `(0,1)` entry. -/
theorem cut_state_noncommute : comm cut state ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Op => M 0 1) h
  norm_num [PeirceSpine.comm, cut, state, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Direct multiplication-order witness for noncommutativity of the cut and
the state operator. -/
theorem cut_state_mul_ne_swap : cut * state ≠ state * cut := by
  intro h
  apply cut_state_noncommute
  unfold PeirceSpine.comm
  rw [h]
  simp

/-- The one-sided witness is an idempotent. -/
theorem oneSidedIdempotent_idempotent :
    oneSidedIdempotent * oneSidedIdempotent = oneSidedIdempotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oneSidedIdempotent, Matrix.mul_apply, Fin.sum_univ_two]

/-- The explicit CAS round-trip product of the cut and one-sided operator. -/
theorem cut_mul_oneSidedIdempotent :
    cut * oneSidedIdempotent = !![1, 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cut, oneSidedIdempotent, Matrix.mul_apply, Fin.sum_univ_two]

/-- The one-sided idempotent is not self-adjoint under the matrix star. -/
theorem oneSidedIdempotent_not_selfAdjoint :
    star oneSidedIdempotent ≠ oneSidedIdempotent := by
  intro h
  have h01 := congrArg (fun M : Op => M 0 1) h
  norm_num [oneSidedIdempotent] at h01

/-- Its outward boundary is nonzero, despite the zero quadratic boundary
metric. -/
theorem oneSidedIdempotent_has_nonzero_current :
    comm cut oneSidedIdempotent ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Op => M 0 1) h
  norm_num [PeirceSpine.comm, cut, oneSidedIdempotent,
    Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- For a non-self-adjoint idempotent, the quadratic boundary metric can
vanish while the commutator current is nonzero.  Thus `genV = 0` does not by
itself characterize zero Peirce boundary or projectability in an arbitrary
ring. -/
theorem oneSidedIdempotent_zero_metric_nonzero_current :
    genV cut oneSidedIdempotent oneSidedIdempotent = 0 ∧
    comm cut oneSidedIdempotent ≠ 0 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [genV, anticomm, conePlus, coneMinus, cut,
        oneSidedIdempotent, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
        Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two]
  · exact oneSidedIdempotent_has_nonzero_current

/-- Pinching this idempotent preserves idempotence although its boundary
current is nonzero.  The self-adjointness hypothesis in state interpretations
cannot be dropped when reading zero quadratic defect as zero boundary. -/
theorem oneSidedIdempotent_pinch_idempotent_nonzero_current :
    idempotencyDefect (evenGrade cut oneSidedIdempotent) = 0 ∧
    comm cut oneSidedIdempotent ≠ 0 := by
  constructor
  · rw [idempotencyDefect_evenGrade_of_idempotent cut oneSidedIdempotent
      cut_idempotent oneSidedIdempotent_idempotent,
      oneSidedIdempotent_zero_metric_nonzero_current.1]
    simp
  · exact oneSidedIdempotent_has_nonzero_current

/-- The quadratic boundary term is one quarter of the identity matrix. -/
theorem boundary_metric_value : genV cut state state = (1 / 4 : ℚ) • (1 : Op) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genV, anticomm, conePlus, coneMinus, cut, state,
      Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two]

/-- The pinched state has nonzero idempotency defect, exactly the negative
of its boundary metric. This is a concrete instance of the general theorem. -/
theorem pinched_state_defect_value :
    idempotencyDefect (evenGrade cut state) = -((1 / 4 : ℚ) • (1 : Op)) := by
  rw [idempotencyDefect_evenGrade_of_idempotent cut state cut_idempotent
    state_idempotent, boundary_metric_value]

/-- The purity defect in the preceding theorem is genuinely nonzero. -/
theorem pinched_state_defect_ne_zero :
    idempotencyDefect (evenGrade cut state) ≠ 0 := by
  rw [pinched_state_defect_value]
  intro h
  have h00 := congrArg (fun M : Op => M 0 0) h
  norm_num at h00

/-- First connection with only an upper-corner component. -/
def connectionUpper : Op := !![0, 1; 0, 0]

/-- Second connection with only a lower-corner component. -/
def connectionLower : Op := !![0, 0; 1, 0]

/-- The mixed Dirac square is `-1` for this pair of noncommuting matrix
connections. -/
theorem mixed_dirac_square_value :
    (genPhi cut connectionUpper 0 + genJ cut 0 connectionLower) *
        (genPhi cut connectionUpper 0 + genJ cut 0 connectionLower) =
      -((1 : Op)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genPhi, genJ, conePlus, coneMinus, cut, connectionUpper,
      connectionLower, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      Fin.sum_univ_two]

/-- The proposed commutator-curvature replacement for that mixed square
returns `diag(-1,1)`, so it is not a valid universal identity. -/
theorem commutator_cross_term_wrong_value :
    genV cut connectionUpper 0 - genV cut 0 connectionLower -
        (genSig cut connectionUpper connectionLower - genSig cut 0 0) =
      !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genV, genSig, anticomm, PeirceSpine.comm, conePlus, coneMinus,
      cut, connectionUpper, connectionLower, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]

/-- The corrected anticommutator cross term agrees with the actual mixed
square on the same witness. -/
theorem mixed_dirac_corrected_formula_value :
    genV cut connectionUpper 0 - genV cut 0 connectionLower -
        (anticomm (conePlus cut connectionUpper) (coneMinus cut connectionLower) -
          anticomm (conePlus cut 0) (coneMinus cut 0)) =
      -((1 : Op)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genV, anticomm, conePlus, coneMinus, cut, connectionUpper,
      connectionLower, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      Fin.sum_univ_two]

/-- Directly certifies the failure of the earlier commutator-based formula. -/
theorem mixed_square_disproves_commutator_formula :
    (genPhi cut connectionUpper 0 + genJ cut 0 connectionLower) *
        (genPhi cut connectionUpper 0 + genJ cut 0 connectionLower) ≠
      genV cut connectionUpper 0 - genV cut 0 connectionLower -
        (genSig cut connectionUpper connectionLower - genSig cut 0 0) := by
  rw [mixed_dirac_square_value, commutator_cross_term_wrong_value]
  intro h
  have h11 := congrArg (fun M : Op => M 1 1) h
  norm_num at h11

end InfoGeometry.OperatorAlgebra.PeirceDefectMatrixWitness
