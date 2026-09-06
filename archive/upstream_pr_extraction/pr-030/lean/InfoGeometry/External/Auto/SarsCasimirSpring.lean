import Mathlib.Tactic

noncomputable section

namespace SarsCasimirSpring

open Real

def poincareCasimirOnShell (m : ℝ) : ℝ := - m^2

def casimirStiffness (C : ℝ) : ℝ := -C

def massStiffness (m : ℝ) : ℝ := m^2

def dilationSpringPotentialFromCasimir (C lam : ℝ) : ℝ := -(C * lam^2) / 2

def dilationSpringPotentialMass (m lam : ℝ) : ℝ := (m^2 * lam^2) / 2

def restoringForceFromCasimir (C lam : ℝ) : ℝ := C * lam

def restoringForceMass (m lam : ℝ) : ℝ := -m^2 * lam

def dilationCasimirBracket (C : ℝ) : ℝ := 2 * C

theorem on_shell_stiffness_eq_mass_sq (m : ℝ) :
    casimirStiffness (poincareCasimirOnShell m) = massStiffness m := by
  unfold casimirStiffness poincareCasimirOnShell massStiffness
  ring

theorem potential_casimir_eq_mass (m lam : ℝ) :
    dilationSpringPotentialFromCasimir (poincareCasimirOnShell m) lam =
      dilationSpringPotentialMass m lam := by
  unfold dilationSpringPotentialFromCasimir poincareCasimirOnShell dilationSpringPotentialMass
  ring

theorem restoring_force_casimir_eq_mass (m lam : ℝ) :
    restoringForceFromCasimir (poincareCasimirOnShell m) lam = restoringForceMass m lam := by
  unfold restoringForceFromCasimir poincareCasimirOnShell restoringForceMass
  ring

theorem massless_spring_loose : massStiffness 0 = 0 := by
  norm_num [massStiffness]

theorem massive_stiffness_nonneg (m : ℝ) : 0 ≤ massStiffness m := by
  unfold massStiffness
  positivity

theorem spring_potential_nonneg (m lam : ℝ) : 0 ≤ dilationSpringPotentialMass m lam := by
  unfold dilationSpringPotentialMass
  positivity

theorem spring_potential_zero_at_vacuum (m : ℝ) : dilationSpringPotentialMass m 0 = 0 := by
  norm_num [dilationSpringPotentialMass]

theorem restoring_force_hooke (m lam : ℝ) : restoringForceMass m lam = - massStiffness m * lam := by
  unfold restoringForceMass massStiffness
  ring

theorem dilation_changes_casimir (C : ℝ) : dilationCasimirBracket C = 2 * C := rfl

structure CasimirLeaf (State : Type*) where
  casimir : State → ℝ
  entropy : State → ℝ
  base : State

namespace CasimirLeaf

def on_leaf (L : CasimirLeaf State) (q : State) : Prop :=
  L.casimir q = L.casimir L.base ∧ L.entropy q = L.entropy L.base

end CasimirLeaf

structure TangentFlow (State : Type*) (L : CasimirLeaf State) where
  flow : State → State
  preserves_leaf : ∀ q, L.on_leaf q → L.on_leaf (flow q)

structure TransverseDilationFlow (State : Type*) (L : CasimirLeaf State) where
  flow : State → State
  entropy_production : ∀ q, 0 ≤ L.entropy (flow q) - L.entropy q

theorem tangent_flow_preserves_casimir_entropy {State : Type*} {L : CasimirLeaf State}
    (F : TangentFlow State L) {q : State} (hq : L.on_leaf q) : L.on_leaf (F.flow q) :=
  F.preserves_leaf q hq

theorem transverse_flow_entropy_nonneg {State : Type*} {L : CasimirLeaf State}
    (F : TransverseDilationFlow State L) (q : State) :
    0 ≤ L.entropy (F.flow q) - L.entropy q := F.entropy_production q

inductive CasimirSpringConcept where
  | Poincare_Casimir_On_Shell
  | Mass_Shell_Coadjoint_Orbit
  | Souriau_Entropic_Leaf
  | Conformal_Dilation_Spring
  | Dilaton_Transverse_Flow
  | Compton_Equilibrium_Scale
  deriving DecidableEq, Repr

inductive CasimirSpringEdge where
  | labels
  | identical_to
  | gives_stiffness
  | resists
  | crosses
  | restores_to
  deriving DecidableEq, Repr

def edgeHolds : CasimirSpringConcept → CasimirSpringEdge → CasimirSpringConcept → Bool
  | CasimirSpringConcept.Poincare_Casimir_On_Shell, CasimirSpringEdge.labels, CasimirSpringConcept.Mass_Shell_Coadjoint_Orbit => true
  | CasimirSpringConcept.Mass_Shell_Coadjoint_Orbit, CasimirSpringEdge.identical_to, CasimirSpringConcept.Souriau_Entropic_Leaf => true
  | CasimirSpringConcept.Poincare_Casimir_On_Shell, CasimirSpringEdge.gives_stiffness, CasimirSpringConcept.Conformal_Dilation_Spring => true
  | CasimirSpringConcept.Conformal_Dilation_Spring, CasimirSpringEdge.resists, CasimirSpringConcept.Dilaton_Transverse_Flow => true
  | CasimirSpringConcept.Dilaton_Transverse_Flow, CasimirSpringEdge.crosses, CasimirSpringConcept.Souriau_Entropic_Leaf => true
  | CasimirSpringConcept.Conformal_Dilation_Spring, CasimirSpringEdge.restores_to, CasimirSpringConcept.Compton_Equilibrium_Scale => true
  | _, _, _ => false

end SarsCasimirSpring

end noncomputable section
