import InfoGeometry.Quantum.WittenIndexVacuum

namespace InfoGeometry.Canonical.WittenIndexVacuumCapstone

open InfoGeometry.Quantum.WittenIndexVacuum

theorem capstone_witten_index_vacuum_synthesis
    (E β γ p : ℝ) :
    (excitedLevelWittenContribution E β = 0) ∧
    (HasDerivAt (wittenIndexThermal 1 0) 0 β) ∧
    (wittenIndex 1 0 = 1) ∧
    ((Complex.exp (Complex.I * (γ * Real.log p : ℂ))) *
     (Complex.exp (-Complex.I * (γ * Real.log p : ℂ))) = 1) :=
  grand_witten_index_vacuum_synthesis E β γ p

end InfoGeometry.Canonical.WittenIndexVacuumCapstone
