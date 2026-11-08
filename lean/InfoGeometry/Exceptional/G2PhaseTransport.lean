/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2DiagonalPhaseTable
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.G2ArtinRootPermutationLift

namespace InfoGeometry.Exceptional.G2PhaseTransport

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Exceptional.G2ArtinRootLift

abbrev Root := G2CoordinateRoot

/-- Pull back a root-indexed phase table along a Weyl permutation. -/
def phaseTransport (π : Equiv.Perm Root) (phase : Root → ℂ) : Root → ℂ :=
  phase ∘ π

@[simp] theorem phaseTransport_apply (π : Equiv.Perm Root) (phase : Root → ℂ)
    (r : Root) :
    phaseTransport π phase r = phase (π r) := rfl

theorem phaseTransport_id (phase : Root → ℂ) :
    phaseTransport (1 : Equiv.Perm Root) phase = phase := by
  funext r
  rfl

theorem phaseTransport_comp (π τ : Equiv.Perm Root) (phase : Root → ℂ) :
    phaseTransport π (phaseTransport τ phase) =
      phaseTransport (τ * π) phase := by
  funext r
  rfl

@[simp] theorem permMatrix_mul_diagonal_apply
    (π : Equiv.Perm Root) (phase : Root → ℂ) (i j : Root) :
    (permMatrix π * Matrix.diagonal phase) i j =
      (if π j = i then phase j else 0) := by
  simp [Matrix.mul_diagonal, permMatrix_apply]

@[simp] theorem diagonal_mul_permMatrix_apply
    (π : Equiv.Perm Root) (phase : Root → ℂ) (i j : Root) :
    (Matrix.diagonal phase * permMatrix π) i j =
      (if π j = i then phase i else 0) := by
  simp [Matrix.diagonal_mul, permMatrix_apply]

end InfoGeometry.Exceptional.G2PhaseTransport
