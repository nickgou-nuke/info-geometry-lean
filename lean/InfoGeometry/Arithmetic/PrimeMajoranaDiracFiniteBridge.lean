import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite
import InfoGeometry.Meta.BridgeTarget


noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaDiracFiniteBridge

open InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite

@[bridge_target_tag]
theorem diracCoefficient_sq_eq_log_bridge
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    {p : ℕ}
    (hp : p ∈ L.primes) :
    diracCoefficient L p * diracCoefficient L p = Real.log p := by
  exact diracCoefficient_sq_eq_log L hp

@[bridge_target_tag]
theorem finiteDiracHamiltonian_eq_primeBitEnergy_bridge
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) :
    finiteDiracHamiltonian L ψ =
      InfoGeometry.Arithmetic.primeBitEnergy L ψ.support := by
  exact finiteDiracHamiltonian_eq_primeBitEnergy L ψ

@[bridge_target_tag]
theorem finiteDiracHamiltonian_eq_log_primeBitInteger_bridge
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) :
    finiteDiracHamiltonian L ψ =
      Real.log (InfoGeometry.Arithmetic.primeBitInteger L ψ : ℝ) := by
  exact finiteDiracHamiltonian_eq_log_primeBitInteger L ψ

end InfoGeometry.Arithmetic.PrimeMajoranaDiracFiniteBridge
