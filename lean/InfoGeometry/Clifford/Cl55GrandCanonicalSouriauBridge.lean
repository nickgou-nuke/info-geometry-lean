import InfoGeometry.Clifford.Cl55CARAutomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinOperatorConnection
import InfoGeometry.OperatorAlgebra.OperatorGrandCanonicalChiralGenerator
import InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR

/-!
# Spin transport of the grand-canonical `Cl(5,5)` operator generator

The Souriau/Tomita generator is represented on its own operator carrier by
`SouriauTomitaModularFlowBridge`.  This file does not identify that carrier
with `Cl55` without an explicit representation.  It proves the genuine
transport statement available on the native `Cl55` carrier: every `Spin55`
ring equivalence transports an arbitrary grand-canonical Hamiltonian,
conserved charge, and the CAR relations.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra

def spinTransportedGrandCanonicalGenerator
    (g : Spin55) (H Nplus Nminus μ μχ : Cl55) : Cl55 :=
  grandCanonicalGenerator
    (spinCliffordRingEquiv g H)
    (spinCliffordRingEquiv g Nplus)
    (spinCliffordRingEquiv g Nminus)
    (spinCliffordRingEquiv g μ)
    (spinCliffordRingEquiv g μχ)

theorem spinTransportedGrandCanonicalGenerator_eq_map
    (g : Spin55) (H Nplus Nminus μ μχ : Cl55) :
    spinTransportedGrandCanonicalGenerator g
        H Nplus Nminus μ μχ =
      spinCliffordRingEquiv g
        (grandCanonicalGenerator H Nplus Nminus μ μχ) := by
  symm
  exact RingHom.map_grandCanonicalGenerator
    (spinCliffordRingEquiv g).toRingHom H Nplus Nminus μ μχ

theorem spinTransportedGrandCanonicalConservation
    (g : Spin55) (G Q : Cl55)
    (hGQ : grandCanonicalCommutator G Q = 0) :
    grandCanonicalCommutator
      (spinCliffordRingEquiv g G)
      (spinCliffordRingEquiv g Q) = 0 := by
  exact RingHom.map_grandCanonicalConservation
    (spinCliffordRingEquiv g).toRingHom G Q hGQ

theorem spinTransportedGrandCanonicalGenerator_conserves
    (g : Spin55) (H Nplus Nminus μ μχ Q : Cl55)
    (hGQ : grandCanonicalCommutator
      (grandCanonicalGenerator H Nplus Nminus μ μχ) Q = 0) :
    grandCanonicalCommutator
      (spinTransportedGrandCanonicalGenerator g
        H Nplus Nminus μ μχ)
      (spinCliffordRingEquiv g Q) = 0 := by
  rw [spinTransportedGrandCanonicalGenerator_eq_map]
  exact spinTransportedGrandCanonicalConservation g
    (grandCanonicalGenerator H Nplus Nminus μ μχ) Q hGQ

def spinTransportedModularGrandCanonicalGenerator
    (g : Spin55) (β H Nplus Nminus μ μχ : Cl55) : Cl55 :=
  modularGrandCanonicalGenerator
    (spinCliffordRingEquiv g β)
    (spinCliffordRingEquiv g H)
    (spinCliffordRingEquiv g Nplus)
    (spinCliffordRingEquiv g Nminus)
    (spinCliffordRingEquiv g μ)
    (spinCliffordRingEquiv g μχ)

theorem spinTransportedModularGrandCanonicalGenerator_eq_map
    (g : Spin55) (β H Nplus Nminus μ μχ : Cl55) :
    spinTransportedModularGrandCanonicalGenerator g
        β H Nplus Nminus μ μχ =
      spinCliffordRingEquiv g
        (modularGrandCanonicalGenerator β H Nplus Nminus μ μχ) := by
  symm
  exact RingHom.map_modularGrandCanonicalGenerator
    (spinCliffordRingEquiv g).toRingHom β H Nplus Nminus μ μχ

theorem spinTransportedModularGrandCanonicalConservation
    (g : Spin55) (β H Nplus Nminus μ μχ Q : Cl55)
    (hGQ : grandCanonicalCommutator
      (modularGrandCanonicalGenerator β H Nplus Nminus μ μχ) Q = 0) :
    grandCanonicalCommutator
      (spinTransportedModularGrandCanonicalGenerator g
        β H Nplus Nminus μ μχ)
      (spinCliffordRingEquiv g Q) = 0 := by
  rw [spinTransportedModularGrandCanonicalGenerator_eq_map]
  exact spinTransportedGrandCanonicalConservation g
    (modularGrandCanonicalGenerator β H Nplus Nminus μ μχ) Q hGQ

theorem spin55_transport_preserves_car
    (g : Spin55) (i j : Fin 5) :
    thermalAnticommutator
      (spinCliffordRingEquiv g (annihilation55 i))
      (spinCliffordRingEquiv g (creation55 j)) =
      if i = j then 1 else 0 := by
  simpa only [thermalAnticommutator, spinCARAutomorphism_apply] using
    spinCARAutomorphism_preserves_indexed_car g i j

end InfoGeometry.Clifford.Clifford55
