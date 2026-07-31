import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CompiledReadability
import Omega.TypedAddressBiaxialCompletion.NonNullRequiresThreeAxes
import Omega.TypedAddressBiaxialCompletion.NullExhaustive
import Omega.TypedAddressBiaxialCompletion.UnitarySliceAddressClosure

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local package for deciding whether a biaxial typed-address readout is `NULL`. The data
collects the unitary-slice closure interface, the `NULL` trichotomy package, and the non-`NULL`
readability/three-axis certificates, together with the two paper-facing conclusion clauses. -/
structure DecidableNullData where
  unitarySliceData : UnitarySliceAddressClosureData
  compiledReadabilityData : CompiledReadabilityData
  threeAxisData : TypedAddressThreeAxisData

/-- The unitary-slice closure law, the `NULL` trichotomy, and the existing non-`NULL`
readability/axis packages combine into a decidability package: either one extracts a `NULL`
witness or one extracts a non-`NULL` certificate.
    prop:typed-address-biaxial-completion-decidable-null -/
theorem paper_typed_address_biaxial_completion_decidable_null
    (D : DecidableNullData)
    (exhaustive nullHasWitness nonNullHasCertificate : Prop)
    (hExhaustive : exhaustive)
    (deriveNullWitness : D.unitarySliceData.readUSClosed → exhaustive → nullHasWitness)
    (deriveNonNullCertificate :
      D.unitarySliceData.readUSClosed →
      D.compiledReadabilityData.readable →
      (D.compiledReadabilityData.readable ↔
        D.compiledReadabilityData.addressAdmitted ∧
          D.compiledReadabilityData.cechObstructionVanishes ∧
            D.compiledReadabilityData.thresholdsMet ∧
              D.compiledReadabilityData.certificateFiberNonempty) →
      D.threeAxisData.nonNullReadout →
      (D.threeAxisData.nonNullReadout →
        D.threeAxisData.visibleAxisPassed ∧
          D.threeAxisData.residueAxisPassed ∧
            D.threeAxisData.modeAxisPassed) → nonNullHasCertificate)
    (hReadableInput : D.compiledReadabilityData.readable)
    (hNonNullReadout : D.threeAxisData.nonNullReadout) :
    nullHasWitness ∧ nonNullHasCertificate := by
  have hUnitary : D.unitarySliceData.readUSClosed :=
    paper_typed_address_biaxial_completion_unitary_slice_address_closure D.unitarySliceData
  have hReadable :
      D.compiledReadabilityData.readable ↔
        D.compiledReadabilityData.addressAdmitted ∧
          D.compiledReadabilityData.cechObstructionVanishes ∧
            D.compiledReadabilityData.thresholdsMet ∧
              D.compiledReadabilityData.certificateFiberNonempty :=
    paper_typed_address_biaxial_completion_compiled_readability_readable
      D.compiledReadabilityData
  have hAxes :
      D.threeAxisData.nonNullReadout →
        D.threeAxisData.visibleAxisPassed ∧
          D.threeAxisData.residueAxisPassed ∧
            D.threeAxisData.modeAxisPassed :=
    paper_typed_address_biaxial_completion_nonnull_requires_three_axes D.threeAxisData
  exact
    ⟨deriveNullWitness hUnitary hExhaustive,
      deriveNonNullCertificate hUnitary hReadableInput hReadable hNonNullReadout hAxes⟩

end Omega.TypedAddressBiaxialCompletion
