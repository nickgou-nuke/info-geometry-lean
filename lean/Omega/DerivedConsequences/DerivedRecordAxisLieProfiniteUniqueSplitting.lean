import Mathlib.Tactic
import Omega.CircleDimension.FiniteLocalizationSolenoidQuotientEmbeddingRigidity
import Omega.CircleDimension.MinimalRecordAxis
import Omega.CircleDimension.UniversalSolenoidFullPrimeKernel
import Omega.Zeta.PrimeSupportKernelGaloisCorrespondence

namespace Omega.DerivedConsequences

/-- Concrete data used by the derived record-axis / Lie-profinite splitting wrapper. The fields are
existing audited packages together with a chosen finite prime-support inclusion. -/
structure DerivedRecordAxisLieProfiniteUniqueSplittingData where
  kernelData : Omega.Zeta.PrimeSupportKernelGaloisCorrespondenceData
  localization : Omega.CircleDimension.FiniteLocalizationPrimeLedgerData
  supportSubset : kernelData.S ⊆ kernelData.T

namespace DerivedRecordAxisLieProfiniteUniqueSplittingData

/-- The derived splitting package keeps the canonical record axis, the universal-solenoid short
exact sequence, the prime-support kernel decomposition, and the finite-rank additive-ledger
obstruction in one concrete statement. -/
def Holds (D : DerivedRecordAxisLieProfiniteUniqueSplittingData)
    (initialObject uniqueContinuousTransverse orthogonalExternalization : Prop)
    (allPrimeHeightsInfinite dualGroupIsQHat kernelIsFullPadicProduct shortExactSequence : Prop) : Prop :=
  initialObject ∧
    uniqueContinuousTransverse ∧
    orthogonalExternalization ∧
    allPrimeHeightsInfinite ∧
    dualGroupIsQHat ∧
    kernelIsFullPadicProduct ∧
    shortExactSequence ∧
    D.kernelData.openSurjectionWitness ∧
    D.kernelData.shortExactSequenceWitness ∧
    D.kernelData.openKernel = D.kernelData.shortExactKernel ∧
    D.kernelData.shortExactKernel = D.kernelData.T \ D.kernelData.S ∧
    Omega.CircleDimension.finiteLocalizationSolenoidTorusQuotient D.localization ∧
    (Omega.CircleDimension.finiteLocalizationHasNonzeroPrimeLedger D.localization →
      ∀ N, ¬ Omega.CircleDimension.finiteLocalizationSolenoidEmbedsInTorus N D.localization)

end DerivedRecordAxisLieProfiniteUniqueSplittingData

open DerivedRecordAxisLieProfiniteUniqueSplittingData

/-- Paper label: `thm:derived-record-axis-lie-profinite-unique-splitting`. The minimal record
axis gives the canonical continuous direction, the universal-solenoid audit supplies the compact
short exact sequence, prime-support recovery identifies the kernel uniquely as `T \\ S`, and the
finite-rank additive-ledger package obstructs any competing finite-torus splitting. -/
theorem paper_derived_record_axis_lie_profinite_unique_splitting
    (D : DerivedRecordAxisLieProfiniteUniqueSplittingData)
    {initialObject uniqueContinuousTransverse orthogonalExternalization : Prop}
    (hInitial : initialObject)
    (hUnique : uniqueContinuousTransverse)
    (hOrthogonal : orthogonalExternalization)
    {allPrimeHeightsInfinite dualGroupIsQHat kernelIsFullPadicProduct shortExactSequence : Prop}
    (hHeights : allPrimeHeightsInfinite)
    (hDual : dualGroupIsQHat)
    (hKernel : kernelIsFullPadicProduct)
    (hShortExact : shortExactSequence) :
    D.Holds initialObject uniqueContinuousTransverse orthogonalExternalization
      allPrimeHeightsInfinite dualGroupIsQHat kernelIsFullPadicProduct shortExactSequence := by
  rcases Omega.Zeta.paper_xi_time_part56ea_prime_support_kernel_galois_correspondence D.kernelData
      with ⟨hOpenIff, hShortIff⟩
  have hOpen : D.kernelData.openSurjectionWitness := hOpenIff.mp D.supportSubset
  have hShort : D.kernelData.shortExactSequenceWitness := hShortIff.mp D.supportSubset
  have hKernelEq : D.kernelData.openKernel = D.kernelData.shortExactKernel := by
    rw [D.kernelData.openKernel_def, D.kernelData.shortExactKernel_def]
  have hShortExactKernel :
      D.kernelData.shortExactKernel = D.kernelData.T \ D.kernelData.S :=
    D.kernelData.shortExactKernel_def
  rcases Omega.CircleDimension.paper_cdim_finite_localization_solenoid_quotient_embedding_rigidity
      D.localization with ⟨hTorusQuotient, hNoEmbedding, _⟩
  exact ⟨hInitial, hUnique, hOrthogonal, hHeights, hDual, hKernel, hShortExact, hOpen, hShort,
    hKernelEq, hShortExactKernel, hTorusQuotient, hNoEmbedding⟩

end Omega.DerivedConsequences
