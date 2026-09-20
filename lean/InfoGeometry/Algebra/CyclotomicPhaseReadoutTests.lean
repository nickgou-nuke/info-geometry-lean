import InfoGeometry.Algebra.CyclotomicPhaseReadout

namespace InfoGeometry.Algebra.CyclotomicPhaseReadoutTests

open CyclotomicPhaseReadout FourthRootSpectralProjectors

example : phase 3 ^ 3 = 1 := phase_pow_order 3 (by norm_num)

example : phase 3 ≠ 1 := phase_ne_one 3 (by norm_num)

example : phase 3 ^ 2 + phase 3 + 1 = 0 := triangular_phase

example : ∑ exponent ∈ Finset.range 5, phase 5 ^ exponent = 0 :=
  phase_sum 5 (by norm_num)

example : phaseWeight 3 0 * phaseWeight 3 0 ≠ phaseWeight 3 0 :=
  scalar_weight_not_idempotent

theorem identity_has_empty_imaginary_sector :
    projector (1 : Module.End ℂ ℂ) 1 = 0 := by
  ext vector
  have eigen : (1 : Module.End ℂ ℂ) vector = root4 0 • vector := by simp
  simpa using projector_on_eigenvector (1 : Module.End ℂ ℂ) 1 0 vector eigen

example (operator : Module.End ℂ (Fin 4 → ℂ)) (periodic : operator ^ 4 = 1) :
    LinearMap.range (projector operator 2) = Module.End.eigenspace operator (root4 2) :=
  projector_range_eq_eigenspace operator periodic 2

#print axioms phase_primitive
#print axioms phase_pow_order
#print axioms phase_ne_one
#print axioms phase_sum
#print axioms triangular_phase
#print axioms phaseWeight_sum
#print axioms scalar_weight_not_idempotent
#print axioms projector_range_eq_eigenspace
#print axioms projector_idempotent
#print axioms projector_orthogonal
#print axioms projector_sum
#print axioms identity_has_empty_imaginary_sector

end InfoGeometry.Algebra.CyclotomicPhaseReadoutTests
