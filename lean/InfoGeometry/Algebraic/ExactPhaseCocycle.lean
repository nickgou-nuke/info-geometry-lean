/- 
InfoGeometry/Algebraic/ExactPhaseCocycle.lean

Exact phase formulation for the modular Berry cocycle.

This file is intentionally contract-first:
- it defines the automorphic factor and the phase rotor carrier;
- it packages the exact phase lift as a cocycle only under an explicit
  compatibility hypothesis;
- it does not claim a branch-cut theorem without hypotheses.
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import InfoGeometry.Canonical.Algebraic.ModularRotorCocycle

noncomputable section

open scoped MatrixGroups Modular
open UpperHalfPlane Complex

namespace InfoGeometry.Algebraic

abbrev ModularGroup := Matrix.SpecialLinearGroup (Fin 2) ℤ

/--
The automorphic factor `j(γ, τ) = c τ + d`.

This is the geometric scalar whose phase is later read by the rotor carrier.
-/
def automorphicFactor (γ : ModularGroup) (τ : UpperHalfPlane) : ℂ :=
  (γ.1 1 0 : ℂ) * (τ : ℂ) + (γ.1 1 1 : ℂ)

/--
Phase rotor carrier for the exact phase formulation.

The file keeps the carrier abstract. The exact phase bridge only needs a
group-valued phase map together with the usual additive/periodic laws.
-/
class PhaseRotorGroup (R : Type*) extends Group R where
  phaseRotor : ℝ → R
  phase_zero : phaseRotor 0 = 1
  phase_add : ∀ a b : ℝ, phaseRotor (a + b) = phaseRotor a * phaseRotor b
  phase_period : ∀ a : ℝ, phaseRotor (a + 2 * Real.pi) = phaseRotor a

/-- The exact Berry phase readout from the automorphic factor. -/
def exactBerryPhase {R : Type*} [PhaseRotorGroup R]
    (k : ℤ) (γ : ModularGroup) (τ : UpperHalfPlane) : R :=
  PhaseRotorGroup.phaseRotor (((k : ℝ) * Complex.arg (automorphicFactor γ τ)))

/--
Compatibility hypothesis for the exact phase lift.

This is the honest Lean boundary: branch-cut and additivity behavior are not
asserted silently; they are packaged as an explicit condition.
-/
structure ExactPhaseCompatibility {R : Type*} [PhaseRotorGroup R] (k : ℤ) : Prop where
  map_one :
    ∀ τ : UpperHalfPlane, exactBerryPhase (R := R) k 1 τ = 1
  map_mul :
    ∀ γ δ : ModularGroup, ∀ τ : UpperHalfPlane,
      exactBerryPhase (R := R) k (γ * δ) τ =
        exactBerryPhase (R := R) k γ (δ • τ) * exactBerryPhase (R := R) k δ τ

/--
Exact phase cocycle packaged as a `MulActionCocycle`.

The cocycle structure is obtained from the explicit compatibility hypothesis.
-/
def exactModularBerryCocycle
    {R : Type*} [PhaseRotorGroup R] {k : ℤ}
    (h : ExactPhaseCompatibility (R := R) k) :
    InfoGeometry.Canonical.Algebraic.MulActionCocycle
      ModularGroup UpperHalfPlane R where
  toFun := exactBerryPhase (R := R) k
  map_one := h.map_one
  map_mul := h.map_mul

namespace MulActionCocycle

variable
    {Γ X R₁ R₂ : Type*}
    [Group Γ] [MulAction Γ X] [Group R₁] [Group R₂]

/--
Push a cocycle forward along a target group homomorphism.

This is the algebraic bridge from the concrete `Circle` phase to an abstract
rotor or spin target.
-/
def mapTarget (C : InfoGeometry.Canonical.Algebraic.MulActionCocycle Γ X R₁)
    (f : R₁ →* R₂) :
    InfoGeometry.Canonical.Algebraic.MulActionCocycle Γ X R₂ where
  toFun γ x := f (C γ x)
  map_one := by
    intro x
    simp [C.map_one x]
  map_mul := by
    intro γ δ x
    rw [C.map_mul γ δ x]
    simpa using f.map_mul (C γ (δ • x)) (C δ x)

@[simp]
theorem mapTarget_apply
    (C : InfoGeometry.Canonical.Algebraic.MulActionCocycle Γ X R₁)
    (f : R₁ →* R₂) (γ : Γ) (x : X) :
    mapTarget C f γ x = f (C γ x) :=
  rfl

end MulActionCocycle

end InfoGeometry.Algebraic
