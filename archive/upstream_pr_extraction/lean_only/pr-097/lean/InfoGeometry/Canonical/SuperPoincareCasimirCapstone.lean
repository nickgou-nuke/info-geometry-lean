import InfoGeometry.Quantum.SuperPoincareCasimir

namespace InfoGeometry.Canonical.SuperPoincareCasimirCapstone

open InfoGeometry.Quantum.SuperPoincareCasimir

theorem capstone_super_poincare_casimir_synthesis
    {R : Type*} [CommRing R] (P_u P_v Q Qbar : R)
    (h_susy : anticommutator Q Qbar = 2 * P_u) :
    (commutator (superPoincareCasimir P_u P_v) P_u = 0) ∧
    (commutator (superPoincareCasimir P_u P_v) P_v = 0) ∧
    (anticommutator Q Qbar = 2 * P_u) :=
  grand_super_poincare_casimir_synthesis P_u P_v Q Qbar h_susy

end InfoGeometry.Canonical.SuperPoincareCasimirCapstone
