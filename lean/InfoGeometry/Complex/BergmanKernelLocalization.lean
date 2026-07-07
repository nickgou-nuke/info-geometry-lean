import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Complex

/-- A simple complex-valued localization kernel built from the standard
Hermitian pairing on `ℂ`. -/
def localizedBergmanKernel (z w : ℂ) : ℂ :=
  z * Complex.conj w

/-- The kernel is conjugate-symmetric on swapped arguments. -/
theorem localizedBergmanKernel_conj_symm (z w : ℂ) :
    Complex.conj (localizedBergmanKernel z w) = localizedBergmanKernel w z := by
  simp [localizedBergmanKernel, mul_comm, mul_left_comm, mul_assoc]

/-- The diagonal localization readout is the squared norm. -/
theorem localizedBergmanKernel_diag (z : ℂ) :
    localizedBergmanKernel z z = ‖z‖ ^ 2 := by
  simp [localizedBergmanKernel, sq]

end InfoGeometry.Complex
