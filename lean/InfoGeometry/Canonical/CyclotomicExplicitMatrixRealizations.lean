import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge

/-!
# Concrete cyclotomic matrix witnesses

These are finite representation-neutral witnesses.  They do not identify a
matrix with a physical Hamiltonian or a Lie-group action.
-/


namespace InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations

open Matrix

abbrev M3Z := InfoGeometry.Algebra.FiniteSpin.Mat3Z
abbrev M8Z := InfoGeometry.Algebra.FiniteSpin.Mat8Z

def tripotentStage : M3Z :=
  !![1, 0, 0; 0, -1, 0; 0, 0, 0]

theorem tripotentStage_cube : tripotentStage ^ 3 = tripotentStage := by
  decide

def phi24Companion : M8Z :=
  !![0, 0, 0, 0, 0, 0, 0, -1;
     1, 0, 0, 0, 0, 0, 0,  0;
     0, 1, 0, 0, 0, 0, 0,  0;
     0, 0, 1, 0, 0, 0, 0,  0;
     0, 0, 0, 1, 0, 0, 0,  1;
     0, 0, 0, 0, 1, 0, 0,  0;
     0, 0, 0, 0, 0, 1, 0,  0;
     0, 0, 0, 0, 0, 0, 1,  0]

theorem phi24Companion_polynomial :
    phi24Companion ^ 8 - phi24Companion ^ 4 + 1 = 0 := by
  decide

theorem phi24Companion_pow_twenty_four : phi24Companion ^ 24 = 1 := by
  change InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge.phi24Companion ^ 24 = 1
  exact InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge.phi24Companion_order

theorem phi24Companion_master25 : phi24Companion ^ 25 = phi24Companion := by
  rw [show (25 : ℕ) = 24 + 1 by norm_num, pow_add, pow_one,
    phi24Companion_pow_twenty_four]
  simp

end InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations
