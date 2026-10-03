import InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
import InfoGeometry.GrandUnification.KleinParabolicPeirceTwist
import InfoGeometry.GrandUnification.IwasawaDiracDecomposition
import InfoGeometry.Algebra.SplitCayleyDickson
import InfoGeometry.Canonical.KleinNativeSemidirectProductBridge

/-!
# Iwasawa and Split Algebra Source Index

This module imports several related owners for convenient discovery. The
imports do not themselves prove a map between the structures or unify them
into a causal-chain API.

## The Causal Chain of Archetypes
1. `CoquaternionicDiracDecomposition` contains concrete split-algebra matrices.
2. `KleinParabolicPeirceTwist` proves finite Peirce-projector identities and a
   coordinate-swap conjugation identity for diagonal matrices. It does not
   define a Klein-group representation.
3. `IwasawaDiracDecomposition` proves a basis identity for traceless matrices
   and elementary trace calculations. It does not prove a group-level KAN
   factorization; `trace_iwasawa` has value zero on the displayed
   traceless-generator combination, while `trace_matOne` records the separate
   scalar direction.
4. `SplitCayleyDickson` defines pair operations and proves selected operation
   laws; it does not establish a Cayley–Dickson algebra tower or a functor.
5. `KleinNativeSemidirectProductBridge` defines an abstract semidirect-product
   model. No homomorphism connecting that model to the concrete matrices above
   is defined in this module.
-/

namespace InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary

end InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary
