import InfoGeometry.Canonical.ModularSurprisalThermoPacket
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# State Surprisal and Modular Hamiltonian

This compatibility module keeps its historical file name but corrects the
mathematical terminology.  The negative logarithm of a density operator is a
state-surprisal (or modular-log) operator, not a Boltzmann macroentropy
operator.  Genuine finite Boltzmann macroentropy is owned separately by
`FiniteBoltzmannMacroentropy`.
-/

namespace InfoGeometry.Canonical.BoltzmannModularHamiltonianEquivalence

/--
Compatibility name for the repo-owned bounded modular-surprisal context.

Both stored components are continuous linear operators.  The first is the
modular operator and the second is its supplied negative-log owner; concrete
functional-calculus models remain responsible for constructing that owner.
-/
abbrev OperatorStateSurprisal
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] :=
  InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext Op

/-! Historical type name retained as a deprecated compatibility alias. -/
@[deprecated OperatorStateSurprisal (since := "2026-07-27")]
abbrev OperatorBoltzmannEntropy
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] :=
  OperatorStateSurprisal Op

namespace OperatorStateSurprisal

variable {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]

/-- Historical selector name for the modular operator. -/
def densityOperator (B : OperatorStateSurprisal Op) : Op →L[ℝ] Op :=
  B.modularOperator

/--
The logarithm associated with the supplied negative-log owner.

This is derived, rather than stored independently, so negating it recovers the
unique state-surprisal operator.
-/
def logDensityOperator (B : OperatorStateSurprisal Op) : Op →L[ℝ] Op :=
  -B.negativeLogModularOperator

def stateSurprisalOperator (B : OperatorStateSurprisal Op) : Op →L[ℝ] Op :=
  B.negativeLogModularOperator

@[deprecated stateSurprisalOperator (since := "2026-07-27")]
abbrev operatorBoltzmannEntropy
    (B : OperatorStateSurprisal Op) : Op →L[ℝ] Op :=
  B.stateSurprisalOperator

/-! The former record field is retained as a theorem projection.  It is an
operator identity, not an additional scalar or diagonal construction. -/
@[deprecated stateSurprisalOperator
    (since := "2026-07-27")]
theorem entropy_eq_neg_log
    (B : OperatorStateSurprisal Op) :
    B.operatorBoltzmannEntropy = -B.logDensityOperator := by
  simp [operatorBoltzmannEntropy, stateSurprisalOperator, logDensityOperator]

def modularHamiltonian (B : OperatorStateSurprisal Op) : Op →L[ℝ] Op :=
  B.negativeLogModularOperator

@[simp] theorem modularHamiltonian_eq_stateSurprisalOperator
    (B : OperatorStateSurprisal Op) :
    B.modularHamiltonian = B.stateSurprisalOperator := rfl

@[deprecated modularHamiltonian_eq_stateSurprisalOperator
    (since := "2026-07-27")]
theorem modularHamiltonian_eq_operatorBoltzmannEntropy
    (B : OperatorStateSurprisal Op) :
    B.modularHamiltonian = B.operatorBoltzmannEntropy :=
  B.modularHamiltonian_eq_stateSurprisalOperator

@[simp] theorem stateSurprisalOperator_eq_neg_logDensityOperator
    (B : OperatorStateSurprisal Op) :
    B.stateSurprisalOperator = -B.logDensityOperator := by
  simp [stateSurprisalOperator, logDensityOperator]

@[simp] theorem modularHamiltonian_eq_neg_log (B : OperatorStateSurprisal Op) :
    B.modularHamiltonian = -B.logDensityOperator := by
  simp [modularHamiltonian, logDensityOperator]

end OperatorStateSurprisal

/--
The modular generator and state-surprisal operator are the same supplied
negative-log operator.  This is the operatorial content formerly hidden behind
the misleading Boltzmann compatibility names.
-/
theorem modularHamiltonian_eq_stateSurprisal
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (B : OperatorStateSurprisal Op) :
    B.modularHamiltonian = B.stateSurprisalOperator :=
  B.modularHamiltonian_eq_stateSurprisalOperator

/--
Tomita--Takesaki/modular-log generator readback with corrected terminology.

No scalar trace, diagonalization, or Boltzmann macrostate identification is
used: both equalities are identities of continuous linear operators.
-/
theorem tomita_takesaki_state_surprisal_generator_duality
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (B : OperatorStateSurprisal Op) :
    (B.modularHamiltonian = B.stateSurprisalOperator) ∧
      (-B.logDensityOperator = B.modularHamiltonian) :=
  ⟨modularHamiltonian_eq_stateSurprisal B,
    B.modularHamiltonian_eq_neg_log.symm⟩

end InfoGeometry.Canonical.BoltzmannModularHamiltonianEquivalence
