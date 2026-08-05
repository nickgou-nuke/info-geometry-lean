import InfoGeometry.Clifford.Cl55WittPinCoverEvidence

namespace InfoGeometry.Clifford.Clifford55

/-!
# Central-kernel evidence for the native Pin action

The scalar `-1` is constructed inside `Pin55` as the square of one negative
Witt reflection vector.  Its action is the identity.  The converse kernel
classification is intentionally not asserted here.
-/

noncomputable def negOnePin : Pin55 := fNegPin 0 * fNegPin 0

theorem negOnePin_coe : (negOnePin : Cl55) = -1 := by
  change (fNegPin 0 : Cl55) * (fNegPin 0 : Cl55) = -1
  rw [fNegPin_coe, ← pow_two, f_neg_sq]

theorem pinTwistedOrthogonalAction_negOnePin :
    pinTwistedOrthogonalAction negOnePin = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change pinTwistedActionEquiv negOnePin v = v
  rw [negOnePin, pinTwistedActionEquiv_mul_all,
    pinTwistedActionEquiv_fNegPin_eq_negativeReflection]
  change negativeReflectionLinearEquiv 0
      (negativeReflectionLinearEquiv 0 v) = v
  simpa only [negativeReflectionLinearEquiv_apply] using
    negativeReflection_involutive 0 v

theorem negOnePin_mem_kernel :
    negOnePin ∈ (pinTwistedOrthogonalAction).ker := by
  change pinTwistedOrthogonalAction negOnePin = 1
  exact pinTwistedOrthogonalAction_negOnePin

end InfoGeometry.Clifford.Clifford55
