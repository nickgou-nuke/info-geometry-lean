import InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Transport of odd volume anticommutation to the spinor matrix model

The statement is restricted to the native image of the Clifford vector
insertion.  It does not identify an arbitrary matrix with a Clifford vector.
-/

namespace InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep

theorem spinor_chirality_anticommutes_vector (v : V55) :
    cl55SpinorAlgEquiv (ι55 v) * chirality55 =
      -(chirality55 * cl55SpinorAlgEquiv (ι55 v)) := by
  have h := cl55WittVolume_anticommutes v
  have hm := congrArg cl55SpinorAlgEquiv h
  have hv : cl55SpinorAlgEquiv cl55WittVolume = chirality55 := by
    exact spinorWittVolume_eq_chirality55
  have hm' : cl55SpinorAlgEquiv (ι55 v) *
        cl55SpinorAlgEquiv cl55WittVolume =
      -(cl55SpinorAlgEquiv cl55WittVolume *
        cl55SpinorAlgEquiv (ι55 v)) := by
    simpa only [map_mul, map_neg] using hm
  rw [hv] at hm'
  exact hm'

end InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
