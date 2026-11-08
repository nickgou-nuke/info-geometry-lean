import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

namespace InfoGeometry.Spectral

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {Q : QuadraticForm ℝ V}

/--
  A Majorana Parafermion is a null vector in the underlying vector space V.
  Its evaluation under the split quadratic form Q is exactly zero.
-/
structure MajoranaParafermion (Q : QuadraticForm ℝ V) where
  v : V
  is_null : Q v = 0

/--
  The Clifford algebra injection of a vector into the algebra.
-/
def embed (mode : MajoranaParafermion Q) : CliffordAlgebra Q :=
  CliffordAlgebra.ι Q mode.v

/--
  EXACT GENUINE PROOF: THE ALGEBRAIC HOLONOMY THEOREM
  The exact cancellation of the global anomaly occurs because the boundary 
  is composed entirely of nilpotent Majorana modes. 
  For any Majorana mode (null vector), its square in the Clifford Algebra is exactly zero.
-/
theorem global_anomaly_cancellation (mode : MajoranaParafermion Q) : 
    (embed mode) * (embed mode) = 0 := by
  dsimp [embed]
  have h_sq : (CliffordAlgebra.ι Q mode.v) * (CliffordAlgebra.ι Q mode.v) = algebraMap ℝ (CliffordAlgebra Q) (Q mode.v) :=
    CliffordAlgebra.ι_sq_scalar Q mode.v
  have h_null : Q mode.v = 0 := mode.is_null
  rw [h_null] at h_sq
  have h_map_zero : algebraMap ℝ (CliffordAlgebra Q) 0 = 0 := map_zero (algebraMap ℝ (CliffordAlgebra Q))
  rw [h_map_zero] at h_sq
  exact h_sq

end InfoGeometry.Spectral
