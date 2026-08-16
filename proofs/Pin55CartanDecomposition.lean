import InfoGeometry.Canonical.TKKJordanPairData
import InfoGeometry.Core.SymmetricLie
import proofs.Clifford55AnomalyOSP

/-!
# Pin/TKK compatibility surface

The former file duplicated five-graded carriers, Cartan involutions,
projector packets, root-space sockets, and generic enveloping-algebra labels.
Those structures either already belong to the canonical TKK/SymmetricLie
owners or were only assumptions with no Pin-specific construction.

This file retains the legacy namespace only for the verified split-signature
arithmetic readout used by downstream proof packets.
-/

namespace Pin55CartanDecomposition

abbrev TKKGrade := TKKJordanPairData.TKKGrade

abbrev FiveGradedLieAlgebra (R : Type*) [CommRing R] :=
  TKKJordanPairData.FiveGradedLieAlgebra R

theorem split_signature_index_55_zero :
    Clifford55AnomalyOSP.anomalyIndex 5 5 = 0 :=
  Clifford55AnomalyOSP.anomalyIndex_55_zero

end Pin55CartanDecomposition
