import InfoGeometry.Clifford.Cl55RealSplitPinKernelEvidence
import InfoGeometry.Clifford.Cl55WittNativeIsometryGroup

namespace InfoGeometry.Clifford.Clifford55

/-!
# Native split-Pin action on the Witt null pair

The corrected real split-Pin lift built from `f_neg` acts by swapping the
native null pair `n_pair`/`nbar_pair`.  This is a concrete action theorem for
the native `Q55` isometry, not an identification with the older positive-
generator Clifford reflection or with an affine Klein glide.
-/

theorem realSplitPinNativeOrthogonalAction_fNegRealPin_n_pair
    (i : Fin 5) :
    realSplitPinNativeOrthogonalAction (fNegRealPin i) (n_pair i) =
      nbar_pair i := by
  rw [realSplitPinNativeOrthogonalAction_apply,
    realSplitPinOrthogonalAction_fNegRealPin]
  change negativeReflectionLinearEquiv i (n_pair i) = nbar_pair i
  rw [negativeReflectionLinearEquiv_apply]
  apply Prod.ext
  · simp [negativeReflection, n_pair, nbar_pair, e_pos, f_neg]
  · funext j
    by_cases h : j = i <;> simp [negativeReflection, n_pair,
      nbar_pair, e_pos, f_neg, h]

theorem realSplitPinNativeOrthogonalAction_fNegRealPin_nbar_pair
    (i : Fin 5) :
    realSplitPinNativeOrthogonalAction (fNegRealPin i) (nbar_pair i) =
      n_pair i := by
  rw [realSplitPinNativeOrthogonalAction_apply,
    realSplitPinOrthogonalAction_fNegRealPin]
  change negativeReflectionLinearEquiv i (nbar_pair i) = n_pair i
  rw [negativeReflectionLinearEquiv_apply]
  apply Prod.ext
  · simp [negativeReflection, n_pair, nbar_pair, e_pos, f_neg]
  · funext j
    by_cases h : j = i <;> simp [negativeReflection, n_pair,
      nbar_pair, e_pos, f_neg, h]

end InfoGeometry.Clifford.Clifford55
