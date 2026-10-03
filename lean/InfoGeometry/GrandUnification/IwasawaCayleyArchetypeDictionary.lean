import InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
import InfoGeometry.GrandUnification.KleinParabolicPeirceTwist
import InfoGeometry.GrandUnification.IwasawaDiracDecomposition
import InfoGeometry.Algebra.SplitCayleyDickson
import InfoGeometry.Canonical.KleinNativeSemidirectProductBridge

/-!
# Iwasawa Cayley Archetype Causal Chain

This file unifies the algebraic structures mapping the basic matrix algebra
to the Split Cayley-Dickson multiplication rules.

## The Causal Chain of Archetypes
1. **The Core Split Algebra:**
   `CoquaternionicDiracDecomposition` defines the baseline `Cℓ(1,1)` matrix generators (`matI`, `matJ`, `matK`).
2. **The Projector Basis and Klein Representation:**
   `KleinParabolicPeirceTwist` establishes the Peirce projectors (P_+, P_-) as the eigenbasis for the J matrix, and proves that `matK` acts as an outer automorphism swapping P_+ and P_-. It proves the homomorphic matrix representation of the Klein bottle group.
3. **The Matrix Splitting:**
   `IwasawaDiracDecomposition` proves that traceless 2x2 real matrices factor uniquely over the K, A, and N matrix generators, and proves the nilpotent matrix maps across the Peirce projectors. It proves the log-determinant trace functional properties natively on the SL(2, R) KAN matrices.
4. **The Split Multiplication Functor:**
   `SplitCayleyDickson` abstracts the multiplication operator over A × A with γ = +1.
5. **The Parabolic Klein Homomorphism (Semidirect Product):**
   `KleinNativeSemidirectProductBridge` constructs the formal semidirect product of the Klein bottle group and proves its native structure map.
-/

namespace InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary

end InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary
