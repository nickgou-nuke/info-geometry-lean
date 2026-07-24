import Mathlib
import InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite
import InfoGeometry.Meta.BridgeTarget

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaDiracFiniteBridge

Bridge-target reexports for the finite prime Majorana Dirac layer.

This file does not prove new mathematics. It makes the already-proved finite
Dirac/Hamiltonian identities visible to the graph overlay as bridge targets.

No infinite Euler product.
No analytic continuation.
No Hilbert--Polya claim.
No RH/Mertens socket.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaDiracFiniteBridge

open InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite

/--
Bridge target: the Dirac coefficient square is the logarithmic prime energy.
-/
@[bridge_target_tag]
theorem diracCoefficient_sq_eq_log_bridge
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    {p : ℕ}
    (hp : p ∈ L.primes) :
    diracCoefficient L p * diracCoefficient L p = Real.log p := by
  exact diracCoefficient_sq_eq_log L hp

/--
Bridge target: the finite Dirac Hamiltonian agrees with the finite prime-bit
energy.
-/
@[bridge_target_tag]
theorem finiteDiracHamiltonian_eq_primeBitEnergy_bridge
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) :
    finiteDiracHamiltonian L ψ =
      InfoGeometry.Arithmetic.primeBitEnergy L ψ.support := by
  exact finiteDiracHamiltonian_eq_primeBitEnergy L ψ

/--
Bridge target: the finite Dirac Hamiltonian agrees with the logarithm of the
represented prime-bit integer.
-/
@[bridge_target_tag]
theorem finiteDiracHamiltonian_eq_log_primeBitInteger_bridge
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) :
    finiteDiracHamiltonian L ψ =
      Real.log (InfoGeometry.Arithmetic.primeBitInteger L ψ : ℝ) := by
  exact finiteDiracHamiltonian_eq_log_primeBitInteger L ψ

end InfoGeometry.Arithmetic.PrimeMajoranaDiracFiniteBridge
