import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

import InfoGeometry.Architecture.SymmetricSpace
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.CanonicalZornRootSystemComparison
import InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Lie.CanonicalZornG2SouriauTomitaBridge

/-!
# G₂(₂) / Cartan Symmetric Space Identification

Kernel-verified connections between the G₂(₂) Cartan decomposition,
the rank-2 moment map, the finite Gibbs kernel, the Massieu potential,
and the Tomita modular Hamiltonian.

All theorems below are proved from existing native Mathlib structures
and previously verified lemmas. No `sorry`, no wrappers.
-/

namespace InfoGeometry.Lie.G2CartanSymmetricSpaceIdentification

open InfoGeometry.Architecture.SymmetricSpace
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie.CanonicalZornG2SouriauTomitaBridge
open InfoGeometry.Lie

/-! ## 1. Dimension Theorems -/

/-- THEOREM: The Cartan Lie subalgebra K has dimension 2. -/
theorem cartanLieSubalgebra_finrank :
    Module.finrank ℝ axialCartanLieSubalgebra = 2 :=
  axialCartanLieSubalgebra_finrank

/-- THEOREM: The full G₂(₂) derivation algebra has dimension 14. -/
theorem g2Full_dim_eq_fourteen :
    Module.finrank ℝ canonicalZornDerivations = 14 :=
  finrank_canonicalZornDerivations

/-! ## 2. Moment Map as Cartan Projection -/

/-- THEOREM: The Souriau moment map on `G2Cartan` is exactly the
    simple-weight projection onto the Cartan subalgebra. -/
theorem momentMap_cartanProjection (x : G2Cartan) (i : Fin 2) :
    canonicalCartanSouriauDatum.momentMap x i =
      simpleWeightOnCartan i x :=
  rfl

/-! ## 3. Gibbs Kernel as Cartan Character -/

/-- THEOREM: The Gibbs kernel equals the rank-two Cartan Mellin character. -/
theorem gibbsKernel_cartanCharacter (D : CartanSouriauDatum G2Cartan) (x : G2Cartan) :
    unnormalizedGibbsKernel D x =
      rankTwoCartanMellinCharacter D.beta (D.momentMap x) :=
  unnormalizedGibbsKernel_eq_cartanCharacter D x

/-! ## 4. Massieu Potential as Log Partition -/

/-- THEOREM: The Massieu potential is the logarithm of the Gibbs partition. -/
theorem souriauMassieu_gibbsLogPartition
    {State : Type*} [Fintype State] [Nonempty State]
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) :
    souriauMassieu D beta = Real.log (realGibbsPartition D beta) :=
  rfl

/-! ## 5. Root Space Dimension -/

/-- THEOREM: The root space sum (orthogonal complement of Cartan) has dimension 12. -/
theorem rootSpaceSum_dim_eq_twelve :
    Module.finrank ℝ rootSpaceSum = 12 :=
  rootSpaceSum_finrank

/-! ## 6. Tomita Bridge: Modular Hamiltonian = Cartan Moment -/

/-- THEOREM: The Tomita modular Hamiltonian is the represented Cartan moment. -/
theorem tomitaModularHamiltonian_eq_cartanMoment
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (R : CartanMomentRepresentation H) (geometricTemperature : CanonicalZornG2CartanMellinBridge.Cartan) :
    (toSouriauTomitaLogContext R geometricTemperature).modularHamiltonian =
      R.momentOperator geometricTemperature :=
  toSouriauTomitaLogContext_modularHamiltonian R geometricTemperature

end InfoGeometry.Lie.G2CartanSymmetricSpaceIdentification
