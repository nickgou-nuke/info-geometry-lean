/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentParity
import InfoGeometry.Physics.NuclearSuperSolovievPeirceBridge
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization

/-!
# Soloviev parity derived from the five adjoint grades

The internal grading is constructed from the tripotent zero-mode projector.
The existing five-grade hypotheses then imply even diagonal and odd
transition coefficients. Combined with external Fock parity this proves
invariance of the full operator block. Applying the five projectors supplies
such blocks from arbitrary operator inputs.
-/

namespace InfoGeometry.Physics.NuclearFiveGradeParity

open InfoGeometry.Physics.Algebra
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization
open InfoGeometry.Physics.NuclearSuperSolovievPeirceBridge

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The existing internal-parity carrier realized by the actual zero-mode
reflection of a tripotent. -/
def zeroModeInternalParity (T : A) (hT : T * T * T = T) : InternalParity A where
  gamma := invS (projZero T)
  gamma_sq := invS_projZero_sq hT

/-- Five-grade membership supplies the internal signs required for total
parity invariance. All four block coefficients remain arbitrary operators. -/
theorem totalParity_invariant_of_fiveGrade
    {T E0 E1 V W : A} (hT : T * T * T = T)
    (hE0 : E0 ∈ fiveGradeRange T .zero)
    (hE1 : E1 ∈ fiveGradeRange T .zero)
    (hV : V ∈ fiveGradeRange T .posOne)
    (hW : W ∈ fiveGradeRange T .negOne) :
    totalParity (zeroModeInternalParity T hT) * blockHamiltonian E0 E1 V W *
        totalParity (zeroModeInternalParity T hT) = blockHamiltonian E0 E1 V W := by
  apply invariant_of_even_diagonal_odd_offDiagonal
  · change parityConj (projZero T) E0 = E0
    simpa using parityConj_projZero_of_mem_fiveGradeRange hT .zero hE0
  · change parityConj (projZero T) E1 = E1
    simpa using parityConj_projZero_of_mem_fiveGradeRange hT .zero hE1
  · change parityConj (projZero T) V = -V
    simpa using parityConj_projZero_of_mem_fiveGradeRange hT .posOne hV
  · change parityConj (projZero T) W = -W
    simpa using parityConj_projZero_of_mem_fiveGradeRange hT .negOne hW

/-- The existing projectors construct parity-invariant blocks from any four
inputs; their grade memberships are proved by the range witnesses. -/
theorem totalParity_invariant_projected_block
    {T : A} (hT : T * T * T = T) (E0 E1 V W : A) :
    totalParity (zeroModeInternalParity T hT) *
        blockHamiltonian (fiveGradeProjector T .zero E0)
          (fiveGradeProjector T .zero E1) (fiveGradeProjector T .posOne V)
          (fiveGradeProjector T .negOne W) *
        totalParity (zeroModeInternalParity T hT) =
      blockHamiltonian (fiveGradeProjector T .zero E0)
        (fiveGradeProjector T .zero E1) (fiveGradeProjector T .posOne V)
        (fiveGradeProjector T .negOne W) := by
  exact totalParity_invariant_of_fiveGrade hT
    ⟨E0, rfl⟩ ⟨E1, rfl⟩ ⟨V, rfl⟩ ⟨W, rfl⟩

/-- The repository's existing compatible block acquires a derived total
parity symmetry, with no new symmetry field added to its data. -/
theorem PeirceCompatibleBlock.totalParity_invariant
    {T : A} (H : PeirceCompatibleBlock T) :
    totalParity (zeroModeInternalParity T H.tripotent) * H.toHamiltonian *
        totalParity (zeroModeInternalParity T H.tripotent) = H.toHamiltonian := by
  exact totalParity_invariant_of_fiveGrade H.tripotent
    H.E0_grade_zero H.E1_grade_zero H.V_grade_posOne H.W_grade_negOne

end InfoGeometry.Physics.NuclearFiveGradeParity
