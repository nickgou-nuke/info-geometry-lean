import InfoGeometry.Canonical.ConnesArakiRadonNikodymCocycleG2

/-!
# Matrix Connes--Araki Radon--Nikodym cocycle bridge

The previous version of this file encoded a cocycle by a scalar exponential.
The maintained owner is the noncommutative `Fin 2` matrix realization in
`ConnesArakiRadonNikodymCocycleG2`: the cocycle is an operator-valued matrix
and its chain law is twisted by the Wiesbrock modular flow.  This file keeps a
small namespace-level bridge to that owner and introduces no commutative
surrogate.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConnesRadonNikodymCocycleChainBridge

open InfoGeometry.Canonical.ConnesArakiRadonNikodymCocycleG2

abbrev MatrixCocycle := Matrix (Fin 2) (Fin 2) ℂ

abbrev modularFlow :=
  InfoGeometry.Canonical.ConnesArakiRadonNikodymCocycleG2.modularFlow

abbrev connesRadonNikodymCocycle :=
  InfoGeometry.Canonical.ConnesArakiRadonNikodymCocycleG2.radonNikodymCocycle

theorem connes_rn_matrix_cocycle_condition (L t s : ℂ) :
    connesRadonNikodymCocycle L (t + s) =
      connesRadonNikodymCocycle L t * modularFlow t
        (connesRadonNikodymCocycle L s) := by
  exact connes_araki_cocycle_condition L t s

theorem modular_flow_translationP (t : ℂ) :
    InfoGeometry.Canonical.ConnesArakiRadonNikodymCocycleG2.modularFlow t
      SL2RToG2Wiesbrock.translationP =
      Complex.exp (Complex.I * t) •
        SL2RToG2Wiesbrock.translationP := by
  exact InfoGeometry.Canonical.ConnesArakiRadonNikodymCocycleG2.modularFlow_translationP t

end InfoGeometry.Canonical.ConnesRadonNikodymCocycleChainBridge
