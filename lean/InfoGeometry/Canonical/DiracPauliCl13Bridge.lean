import InfoGeometry.Algebra.PseudoEuclideanCliffordSignatureBridge
import InfoGeometry.Clifford.DiracPauliGamma

/-!
# Native Dirac--Pauli realization of the `(1,3)` generator carrier

The abstract `Cl13SpacetimeGenerators` carrier is instantiated by the
repository's existing Dirac--Pauli matrices.  This is a finite matrix bridge:
it fixes the signature and anticommutators without asserting a global
identification with a Hestenes, Pin, or physical state-space construction.
-/

namespace InfoGeometry.Canonical.DiracPauliCl13Bridge

open InfoGeometry.Algebra.PseudoEuclideanCliffordSignatureBridge
open InfoGeometry.Clifford.DiracPauliGamma

noncomputable section

/-- The native complex Dirac matrices as one explicit `(1,3)` Clifford frame. -/
def diracPauliCl13 :
    Cl13SpacetimeGenerators DiracMatrix where
  gamma0 := gamma0
  gamma1 := gamma1
  gamma2 := gamma2
  gamma3 := gamma3
  gamma0_sq := gamma0_mul_self
  gamma1_sq := gamma1_mul_self
  gamma2_sq := gamma2_mul_self
  gamma3_sq := gamma3_mul_self
  anticomm_01 := gamma0_gamma1_anticomm
  anticomm_02 := gamma0_gamma2_anticomm
  anticomm_03 := gamma0_gamma3_anticomm
  anticomm_12 := gamma1_gamma2_anticomm
  anticomm_13 := gamma1_gamma3_anticomm
  anticomm_23 := gamma2_gamma3_anticomm

@[simp] theorem diracPauliCl13_gamma0 :
    diracPauliCl13.gamma0 = gamma0 := rfl

@[simp] theorem diracPauliCl13_gamma1 :
    diracPauliCl13.gamma1 = gamma1 := rfl

@[simp] theorem diracPauliCl13_gamma2 :
    diracPauliCl13.gamma2 = gamma2 := rfl

@[simp] theorem diracPauliCl13_gamma3 :
    diracPauliCl13.gamma3 = gamma3 := rfl

theorem diracPauliCl13_volume_anticommutes_with_time :
    diracPauliCl13.gamma5 * diracPauliCl13.gamma0 +
        diracPauliCl13.gamma0 * diracPauliCl13.gamma5 = 0 := by
  exact diracPauliCl13.gamma5_anticomm_gamma0

theorem diracPauliCl13_signature_packet :
    diracPauliCl13.gamma0 * diracPauliCl13.gamma0 = 1 ∧
    diracPauliCl13.gamma1 * diracPauliCl13.gamma1 = -1 ∧
    diracPauliCl13.gamma2 * diracPauliCl13.gamma2 = -1 ∧
    diracPauliCl13.gamma3 * diracPauliCl13.gamma3 = -1 := by
  exact ⟨diracPauliCl13.gamma0_sq, diracPauliCl13.gamma1_sq,
    diracPauliCl13.gamma2_sq, diracPauliCl13.gamma3_sq⟩

theorem diracPauliCl13_anticommutator (mu nu : Fin 4) :
    gamma mu * gamma nu + gamma nu * gamma mu =
      (2 * eta mu nu) • (1 : DiracMatrix) := by
  exact gamma_anticomm mu nu

end
end InfoGeometry.Canonical.DiracPauliCl13Bridge
