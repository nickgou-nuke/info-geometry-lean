import InfoGeometry.Canonical.SplitOctonionBogoliubovCarrierBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.QuasilatticeDirac

/-!
# Canonical quaternionic split-octonion Dirac transport

This file is only a specialization adapter.  The Dirac transport law is
owned by `QuasilatticeDirac`; this theorem instantiates it with the canonical
8-dimensional quaternionic split-octonion vielbein.
-/

namespace InfoGeometry.Canonical

open BogoliubovVielbein
open QuasilatticeDirac
open InfoGeometry.Krein

theorem canonicalQuaternionicSplitOctonion_quasilatticeDirac_deriv
    (g : Quaternion ℝ)
    (D : DoubledSpace (Quaternion ℝ) →L[ℝ] DoubledSpace (Quaternion ℝ))
    (t : ℝ) :
    deriv
        (fun s =>
          quasilatticeDirac (canonicalQuaternionicSplitOctonionVielbein g) D s)
        t =
      (canonicalQuaternionicSplitOctonionVielbein g).connectionGenerator *
          quasilatticeDirac (canonicalQuaternionicSplitOctonionVielbein g) D t -
        quasilatticeDirac (canonicalQuaternionicSplitOctonionVielbein g) D t *
          (canonicalQuaternionicSplitOctonionVielbein g).connectionGenerator := by
  exact deriv_quasilatticeDirac
    (canonicalQuaternionicSplitOctonionVielbein g) D t

end InfoGeometry.Canonical
