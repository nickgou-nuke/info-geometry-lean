import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Complex

open scoped ComplexConjugate

/-- A simple complex-valued localization kernel built from the standard
Hermitian pairing on `ℂ`. -/
def localizedBergmanKernel (z w : ℂ) : ℂ :=
  z * conj w

/-- The kernel is conjugate-symmetric on swapped arguments. -/
theorem localizedBergmanKernel_conj_symm (z w : ℂ) :
    conj (localizedBergmanKernel z w) = localizedBergmanKernel w z := by
  simp [localizedBergmanKernel, mul_comm, mul_left_comm, mul_assoc]

/-- The diagonal localization readout is the squared norm. -/
theorem localizedBergmanKernel_diag (z : ℂ) :
    localizedBergmanKernel z z = Complex.normSq z := by
  simpa [localizedBergmanKernel] using (Complex.mul_conj z)

end InfoGeometry.Complex
