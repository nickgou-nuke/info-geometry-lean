import InfoGeometry.Quantum.SuperPoincareCasimir
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.SuperPoincareCasimirCapstone

open InfoGeometry.Quantum.SuperPoincareCasimir

theorem capstone_super_poincare_casimir_synthesis
    {R : Type*} [CommRing R] (P_u P_v Q Qbar : R)
    (h_susy : anticommutator Q Qbar = 2 * P_u) :
    (commutator (superPoincareCasimir P_u P_v) P_u = 0) ∧
    (commutator (superPoincareCasimir P_u P_v) P_v = 0) ∧
    (anticommutator Q Qbar = 2 * P_u) := by
  exact ⟨casimir_commutes_with_Pu P_u P_v,
    casimir_commutes_with_Pv P_u P_v, h_susy⟩

end InfoGeometry.Canonical.SuperPoincareCasimirCapstone
