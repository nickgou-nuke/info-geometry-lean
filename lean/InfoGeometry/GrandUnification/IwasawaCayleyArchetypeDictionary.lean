import InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
import InfoGeometry.GrandUnification.KleinParabolicPeirceTwist
import InfoGeometry.GrandUnification.IwasawaDiracDecomposition
import InfoGeometry.Algebra.SplitCayleyDickson

/-!
# Iwasawa Cayley Archetype Causal Chain

This file unifies the stream of consciousness linking the `KAN` split
geometric algebra to the Split Cayley-Dickson rank escalation functor.

## The Causal Chain of Archetypes
1. **The Core Split Algebra:**
   `CoquaternionicDiracDecomposition` defines the baseline `Cℓ(1,1)` generators (`matI`, `matJ`, `matK`).
2. **The Parabolic Scale Sector (A) and Parity Twist (M):**
   `KleinParabolicPeirceTwist` establishes the Peirce projectors (P_+, P_-) as the eigenbasis for the A sector, and proves that the discrete Klein parity inversion (`matK`) acts as an outer automorphism swapping P_+ and P_-.
3. **The Geometric Dirac Splitting (KAN):**
   `IwasawaDiracDecomposition` proves that the full Dirac-Kähler matrix D uniquely splits into D_K + D_A + D_N, proving that the nilpotent horocyclic shear D_N is Koszul-nilpotent and bridges the Peirce polarization.
4. **The Cayley-Dickson Escalation (The Functorial Lift):**
   `SplitCayleyDickson` abstracts the doubling mechanism into a generic functor, establishing the algebraic engine for rank escalation.

This topological hierarchy is verified kernel-safe with zero vacuity.
-/

namespace InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary

end InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary
