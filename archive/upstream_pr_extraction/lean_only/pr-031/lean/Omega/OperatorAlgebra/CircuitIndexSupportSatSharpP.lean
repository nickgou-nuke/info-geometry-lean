import Mathlib.Data.Fintype.Card
import Omega.OperatorAlgebra.CircuitNoninjectiveNPComplete
import Omega.OperatorAlgebra.IndexSupportSatNpHardIndexCoeffSharpP
import Omega.OperatorAlgebra.NpWatataniIndexSupportCharacterization

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

/-- For a single dummy input, the imported verifier characterization gives the Watatani-index
coefficient as the number of satisfying assignments and identifies support with satisfiability. -/
theorem paper_index_support_sat_np_hard_index_coeff_sharpp
    {n : ℕ} (φ : BitVec n → Bool) :
    let V : Unit → BitVec n → Bool := fun _ w => φ w
    foldWatataniIndexElement (verifierFold V) () =
        Fintype.card {w : BitVec n // φ w = true} ∧
      (verifierProjectorInSupport V () ↔ satisfiable φ) := by
  dsimp
  have h := index_support_sat_np_hard_index_coeff_sharpp_characterization
    (fun _ : Unit => φ)
  constructor
  · simpa [verifierWitnessCount, verifierWitnesses] using h.2 ()
  · simpa [satisfiable] using h.1 ()

end Omega.OperatorAlgebra
