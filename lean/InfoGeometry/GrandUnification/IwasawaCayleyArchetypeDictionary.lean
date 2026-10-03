import InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
import InfoGeometry.GrandUnification.KleinParabolicPeirceTwist
import InfoGeometry.GrandUnification.IwasawaDiracDecomposition
import InfoGeometry.Algebra.SplitCayleyDickson

/-!
# Iwasawa Cayley Archetype Causal Chain

This file unifies the algebraic structures mapping the KAN matrix algebra
to the Split Cayley-Dickson multiplication rules.

## The Causal Chain of Archetypes
1. **The Core Split Algebra:**
   `CoquaternionicDiracDecomposition` defines the baseline `Cℓ(1,1)` matrix generators (`matI`, `matJ`, `matK`).
2. **The Projector Basis:**
   `KleinParabolicPeirceTwist` establishes the Peirce projectors (P_+, P_-) as the eigenbasis for the J matrix, and proves that `matK` acts as an outer automorphism swapping P_+ and P_-.
3. **The Matrix Splitting (KAN):**
   `IwasawaDiracDecomposition` proves that traceless 2x2 real matrices factor uniquely over the K, A, and N matrix generators, and proves the nilpotent shears bridge the Peirce polarization.
4. **The Split Multiplication Functor:**
   `SplitCayleyDickson` abstracts the multiplication operator over A × A with γ = +1.

-/

namespace InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary

end InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary
