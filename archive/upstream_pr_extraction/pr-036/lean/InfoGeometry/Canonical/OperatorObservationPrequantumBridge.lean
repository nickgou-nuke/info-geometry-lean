import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationQuotientCompHaus
import InfoGeometry.Prequantum.Quotient

/-!
# Observational quotient to projective/prequantum data

The observational quotient is not identified with all operators.  It is
identified with the range of the readout, and a prequantum interpretation is
an additional, explicit lift of that range into bundle data.  This owner
records the resulting factorisation without hiding that hypothesis.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorObservationPrequantumBridge

open InfoGeometry.Topology
open InfoGeometry.Prequantum

universe u

variable {X A : Type u} {ι : Type u} {E : Type}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An explicit interpretation of operator readouts as projective prequantum
bundle points.  The map is deliberately supplied by the model owner: the
quotient/range theorem alone cannot manufacture a line bundle or a ray lift. -/
structure ReadoutPrequantumLift
    (S : NoncommutativeObservableSystem X A ι) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  bundleOfReadout : (ι → A) → ProjectivePrequantumBundle E

variable (S : NoncommutativeObservableSystem X A ι)

/-- The prequantum bundle datum induced on the observational quotient. -/
def bundleOnObservationQuotient (L : ReadoutPrequantumLift S E) :
    OperatorObservationalQuotient S → ProjectivePrequantumBundle E :=
  fun q => L.bundleOfReadout (operatorObservationQuotientReadout S q)

@[simp] theorem bundleOnObservationQuotient_mk
    (L : ReadoutPrequantumLift S E) (x : X) :
    bundleOnObservationQuotient S L (operatorObservationQuotientMap S x) =
      L.bundleOfReadout (S.operatorObservationMap x) := by
  simp [bundleOnObservationQuotient, operatorObservationQuotientReadout_mk]

/-- The same lift can be transported to the compact readout range. -/
def bundleOnObservationRange (L : ReadoutPrequantumLift S E) :
    Set.range S.operatorObservationMap → ProjectivePrequantumBundle E :=
  fun r => L.bundleOfReadout r.1

theorem bundleOnObservationQuotient_factorization
    (L : ReadoutPrequantumLift S E) (q : OperatorObservationalQuotient S) :
    bundleOnObservationQuotient S L q =
      bundleOnObservationRange S L
        (operatorObservationQuotientRangeEquiv S q) := by
  change L.bundleOfReadout (operatorObservationQuotientReadout S q) =
    L.bundleOfReadout (operatorObservationQuotientRangeMap S q).1
  rw [operatorObservationQuotientRangeMap_val]

/-- The quotient/range equivalence is the precise one-to-one statement used by
the bridge.  No injectivity of the original operator carrier is assumed. -/
theorem observational_one_to_one_readout_range :
    Function.Bijective (operatorObservationQuotientRangeMap S) := by
  exact (operatorObservationQuotientRangeEquiv S).bijective

end InfoGeometry.Canonical.OperatorObservationPrequantumBridge

end noncomputable section
