import InfoGeometry.Canonical.BostConnesModularFlow
import InfoGeometry.Canonical.PauliBostConnesModularFlow

/-!
# Pauli clock / arithmetic Bost--Connes flow bridge

The two existing flow owners have different carriers: the Pauli clock is an
abstract commutative-ring flow, while the arithmetic Bost--Connes flow acts on
the normed algebra carrying the indexed generators.  This file connects them
only after an explicit readout `Op → R` and an explicit intertwining law are
provided.  Thus no unproved identification of the two carriers is hidden in
the bridge.
-/

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.BostConnesModularFlow
open InfoGeometry.Arithmetic.BostConnesSystem

variable {R Op : Type*} [CommRing R]
variable [NormedRing Op] [NormedAlgebra ℂ Op] [StarRing Op]

structure PauliArithmeticModularFlowBridge
    (C : CuntzMultiplicativeIndexing Op) where
  clock : PauliBostConnesClock R
  arithmetic : ArithmeticModularFlow C
  readout : Op → R
  intertwines : ∀ (t : ℝ) (n : ℕ+),
    readout (arithmetic.σ t (C.generator n)) =
      clock.time_flow.flow t (readout (C.generator n))

theorem arithmetic_generator_readout_intertwines
    {C : CuntzMultiplicativeIndexing Op}
    (B : PauliArithmeticModularFlowBridge (R := R) C)
    (t : ℝ) (n : ℕ+) :
    B.readout (B.arithmetic.σ t (C.generator n)) =
      B.clock.time_flow.flow t (B.readout (C.generator n)) :=
  B.intertwines t n

theorem pauli_synchronicity_survives_arithmetic_coupling
    {C : CuntzMultiplicativeIndexing Op}
    (B : PauliArithmeticModularFlowBridge (R := R) C) (t : ℝ) :
    B.clock.time_flow.flow t
        (B.clock.red_wheel.e * B.clock.red_wheel.u) =
      B.clock.time_flow.flow t
        (B.clock.green_wheel.e * B.clock.green_wheel.u) :=
  synchronicity_flow_invariance B.clock t

end InfoGeometry.Canonical
