import InfoGeometry.OptimalTransport.ItakuraSaitoTwinFlow

namespace InfoGeometry.OptimalTransport.ItakuraSaitoTwinFlowTests

open ItakuraSaitoTwinFlow

example : HasDerivAt potential 0 (1 / 2) := by
  convert hasDerivAt_potential (state := 1 / 2) (by constructor <;> norm_num) using 1
  norm_num [gradient]

example : 0 < potential (1 / 4) := by
  exact potential_pos_of_ne_half (by constructor <;> norm_num) (by norm_num)

example : gradient (1 / 4) < 0 := by norm_num [gradient]

example : 0 < gradient (3 / 4) := by norm_num [gradient]

example : perturbedFlow (fun _ => 1) (1 / 2) ≠ 0 := by
  rw [perturbedFlow_half]
  norm_num

example : gradient 0 = 0 ∧ gradient 1 = 0 := by norm_num [gradient]

#print axioms hasDerivAt_potential
#print axioms potential_eq_zero_iff
#print axioms energy_derivative_along_descent
#print axioms half_equilibrium_iff

end InfoGeometry.OptimalTransport.ItakuraSaitoTwinFlowTests
