import InfoGeometry.Clifford.Cl55RealSplitPinImage

namespace InfoGeometry.Clifford.Clifford55

/-!
# Central-kernel evidence for the corrected split Pin action

This constructs the scalar `-1` inside the corrected normalized-vector
subgroup.  The converse kernel classification remains open.
-/

noncomputable def fNegRealPin (i : Fin 5) : realSplitPin55 :=
  ⟨fNegUnit i, fNegUnit_mem_realSplitPin i⟩

theorem fNegRealPin_unit_eq_pinToUnits (i : Fin 5) :
    (fNegRealPin i : Cl55ˣ) = pinToUnits (fNegPin i) := by
  apply Units.ext
  simpa [fNegRealPin, fNegPin] using
    congrArg (fun u : Cl55ˣ => (u : Cl55)) (pinToUnits_f_neg i).symm

theorem realSplitPinOrthogonalAction_fNegRealPin
    (i : Fin 5) :
    realSplitPinOrthogonalAction (fNegRealPin i) =
      coordinateReflectionGenerator i := by
  exact realSplitPinOrthogonalAction_eq_pinTwistedOrthogonalAction
    (fNegRealPin i) (fNegPin i)
    (fNegRealPin_unit_eq_pinToUnits i) |>.trans
      (pinTwistedOrthogonalAction_fNegPin i)

noncomputable def realSplitNegOne : realSplitPin55 :=
  fNegRealPin 0 * fNegRealPin 0

theorem realSplitNegOne_coe :
    ((realSplitNegOne : Cl55ˣ) : Cl55) = -1 := by
  change ((fNegRealPin 0 : Cl55ˣ) : Cl55) *
      ((fNegRealPin 0 : Cl55ˣ) : Cl55) = -1
  rw [fNegRealPin, fNegUnit_coe, ← pow_two, f_neg_sq]

theorem realSplitPinOrthogonalAction_realSplitNegOne :
    realSplitPinOrthogonalAction realSplitNegOne = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change realSplitPinTwistedActionEquiv realSplitNegOne v = v
  rw [realSplitNegOne, realSplitPinTwistedActionEquiv_mul]
  have h0 : realSplitPinTwistedActionEquiv (fNegRealPin 0) =
      negativeReflectionLinearEquiv 0 := by
    exact realSplitPinTwistedActionEquiv_eq_pinTwistedActionEquiv
      (fNegRealPin 0) (fNegPin 0)
      (fNegRealPin_unit_eq_pinToUnits 0) |>.trans
        (by exact pinTwistedActionEquiv_fNegPin_eq_negativeReflection 0)
  rw [h0]
  rw [LinearEquiv.mul_apply]
  change negativeReflectionLinearEquiv 0
      (negativeReflectionLinearEquiv 0 v) = v
  simpa only [negativeReflectionLinearEquiv_apply] using
    negativeReflection_involutive 0 v

theorem realSplitNegOne_mem_kernel :
    realSplitNegOne ∈ (realSplitPinOrthogonalAction).ker := by
  change realSplitPinOrthogonalAction realSplitNegOne = 1
  exact realSplitPinOrthogonalAction_realSplitNegOne

end InfoGeometry.Clifford.Clifford55
