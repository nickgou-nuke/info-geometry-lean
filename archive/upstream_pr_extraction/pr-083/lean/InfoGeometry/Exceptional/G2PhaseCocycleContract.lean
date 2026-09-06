/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2PermutationDiagonalConjugation
import InfoGeometry.Exceptional.G2PhaseTransport

namespace InfoGeometry.Exceptional.G2PhaseCocycleContract

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Exceptional.G2ArtinRootLift
open InfoGeometry.Exceptional.G2PermutationDiagonalConjugation
open InfoGeometry.Exceptional.G2PhaseTransport

abbrev Root := G2CoordinateRoot

/-- Conjugating a diagonal phase table by a Weyl permutation is exactly
    transport of its entries along the inverse permutation.  This is the
    primitive equation used by any later label-dependent phase cocycle. -/
theorem permMatrix_conj_diagonal_eq_phaseTransport
    (π : Equiv.Perm Root) (phase : Root → ℂ) :
    permMatrix π * Matrix.diagonal phase * permMatrix π⁻¹ =
      Matrix.diagonal (phaseTransport (π⁻¹ : Equiv.Perm Root) phase) := by
  simpa [phaseTransport] using permMatrix_conj_diagonal π phase

end InfoGeometry.Exceptional.G2PhaseCocycleContract
