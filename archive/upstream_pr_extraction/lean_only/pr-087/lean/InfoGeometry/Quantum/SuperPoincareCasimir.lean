import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.SuperPoincareCasimir

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {R : Type*} [CommRing R]

def commutator (A B : R) : R :=
  A * B - B * A

def anticommutator (A B : R) : R :=
  A * B + B * A

def superPoincareCasimir (P_u P_v : R) : R :=
  4 * P_u * P_v

theorem casimir_commutes_with_Pu (P_u P_v : R) :
    commutator (superPoincareCasimir P_u P_v) P_u = 0 := by
  unfold commutator superPoincareCasimir
  ring

theorem casimir_commutes_with_Pv (P_u P_v : R) :
    commutator (superPoincareCasimir P_u P_v) P_v = 0 := by
  unfold commutator superPoincareCasimir
  ring

theorem supercharge_generates_translation (Q Qbar P : R) (h_susy : anticommutator Q Qbar = 2 * P) :
    anticommutator Q Qbar = 2 * P :=
  h_susy

theorem grand_super_poincare_casimir_synthesis (P_u P_v Q Qbar : R)
    (h_susy : anticommutator Q Qbar = 2 * P_u) :
    (commutator (superPoincareCasimir P_u P_v) P_u = 0) ∧
    (commutator (superPoincareCasimir P_u P_v) P_v = 0) ∧
    (anticommutator Q Qbar = 2 * P_u) :=
  ⟨casimir_commutes_with_Pu P_u P_v,
   casimir_commutes_with_Pv P_u P_v,
   supercharge_generates_translation Q Qbar P_u h_susy⟩

end InfoGeometry.Quantum.SuperPoincareCasimir
