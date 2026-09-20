import InfoGeometry.Algebra.CyclotomicPhasePolarization
import InfoGeometry.Algebra.CyclotomicPhaseDependencies
import InfoGeometry.Algebra.CyclotomicPeirceMatrix
import InfoGeometry.Algebra.AnyonFiniteSpinBraid.AnyonLocalDefectSteps

namespace InfoGeometry.Algebra.CyclotomicPhasePolarizationTests

open InfoGeometry.Algebra.CyclotomicPhasePolarization
open InfoGeometry.Algebra.CyclotomicPeirceMatrix
open InfoGeometry.Canonical.CyclotomicProjector

example : cyclotomicPhase 3 ^ 3 = 1 := cyclotomicPhase_pow_self 3 (by omega)

example : cyclotomicPhase 3 ^ 2 + cyclotomicPhase 3 + 1 = 0 :=
  triangular_root_identity

example : (∑ index ∈ Finset.range 1, cyclotomicPhase 1 ^ index) ≠ 0 := by
  norm_num

example : phaseWeight 2 0 * phaseWeight 2 0 ≠ phaseWeight 2 0 :=
  phaseWeight_two_zero_not_idempotent

example : phaseOperator 3 ^ 3 = 1 := phaseOperator_periodic 3 (by omega)

example (state : Fin 3 → ℂ) :
    ∑ sector : Fin 3, coordinateProjector sector * state = state :=
  state_reconstruction state

example {Carrier : Type*} [Ring Carrier] [Algebra ℂ Carrier]
    {operator : Carrier} {order : ℕ}
    (readout : FourierCyclotomicReadout (K := ℂ) operator order)
    (state : Carrier) :
    ∑ left, ∑ right, blocks readout state left right = state :=
  sum_blocks readout state

example {Carrier : Type*} [Ring Carrier] [Algebra ℂ Carrier]
    {operator : Carrier} {order : ℕ}
    (readout : FourierCyclotomicReadout (K := ℂ) operator order)
    (state : Carrier) (left right : Fin order) (distinct : left ≠ right) :
    blocks readout state left right * blocks readout state left right = 0 :=
  off_diagonal_block_square_zero readout state left right distinct

example : InfoGeometry.Algebra.FiniteSpin.J_plus *
    InfoGeometry.Algebra.FiniteSpin.J_plus = 0 :=
  InfoGeometry.Algebra.AnyonFiniteSpinBraid.J_plus_nilpotent

example : InfoGeometry.Algebra.FiniteSpin.J_minus *
    InfoGeometry.Algebra.FiniteSpin.J_minus = 0 :=
  InfoGeometry.Algebra.AnyonFiniteSpinBraid.J_minus_nilpotent

#print axioms cyclotomic_sum_vanishing
#print axioms triangular_root_identity
#print axioms coordinateReadout
#print axioms phaseOperator_periodic
#print axioms state_reconstruction

end InfoGeometry.Algebra.CyclotomicPhasePolarizationTests
