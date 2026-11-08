import InfoGeometry.SuperMetriplectic.DiscreteMellinHamiltonian
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.WedgeBoostModularBridge

/-!
# Operatorial Lorentz Curvature

Lean-facing bridge for the operatorial Clifford-Fourier / Lorentz / modular
curvature step.

The Pauli-audit boundary is explicit:

* no coordinate-space Lorentz manifold is introduced;
* no Bisognano-Wichmann theorem is reproved here;
* no analytic infinite sum or trace is asserted;
* curvature is represented as a proof-carrying commutator readout of two
  modular/Lorentz operator flows;
* Drazin-core Lorentz protection is represented by explicit generator-killing
  and flow-fixing equations.
-/

namespace InfoGeometry.SuperMetriplectic

set_option linter.unusedSectionVars false

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Operatorial Clifford-Fourier grade split.

This is a readout packet, not a claim that a full analytic Clifford-Fourier
integral has been constructed.  It records the repo-acceptable algebraic
content: one transformed operator decomposes into scalar/vector/bivector/
topological grade lanes.
-/
@[rep_depth operator]
structure OperatorialCliffordFourierGradeSplit where
  transformed : EndH
  scalarGrade : EndH
  vectorGrade : EndH
  bivectorGrade : EndH
  topologicalGrade : EndH
  transformed_eq_grade_sum :
    transformed = scalarGrade + vectorGrade + bivectorGrade + topologicalGrade

namespace OperatorialCliffordFourierGradeSplit

/-- The Clifford-Fourier readout separates into the carried grade lanes. -/
@[rep_depth operator]
theorem transformed_eq_sum
    (G : OperatorialCliffordFourierGradeSplit (E := E)) :
    G.transformed =
      G.scalarGrade + G.vectorGrade + G.bivectorGrade + G.topologicalGrade :=
  G.transformed_eq_grade_sum

end OperatorialCliffordFourierGradeSplit

/--
Bisognano-Wichmann-style compatibility packet.

`modularFlow` is the Tomita-Takesaki flow readout; `lorentzBoostFlow` is the
same operator family viewed as the wedge/Lorentz boost.  The equality is carried
as proof data or obtained from the canonical wedge bridge below.
-/
@[rep_depth operator]
structure BisognanoWichmannModularLorentzPacket where
  modularFlow : ℝ → EndH
  lorentzBoostFlow : ℝ → EndH
  modular_eq_lorentz : ∀ τ : ℝ, modularFlow τ = lorentzBoostFlow τ

namespace BisognanoWichmannModularLorentzPacket

/-- Modular flow and Lorentz boost flow are the same carried operator family. -/
@[rep_depth operator]
theorem modularFlow_eq_lorentzBoost
    (B : BisognanoWichmannModularLorentzPacket (E := E)) (τ : ℝ) :
    B.modularFlow τ = B.lorentzBoostFlow τ :=
  B.modular_eq_lorentz τ

end BisognanoWichmannModularLorentzPacket

/--
Curvature packet from two modular/Lorentz directions.

The "Riemann readout" is deliberately an operator-algebraic readout: it is the
commutator of two modular flows.  This is the strongest Lean statement supported
here without importing a coordinate manifold and its tensor calculus.
-/
@[rep_depth operator]
structure ModularLorentzCommutatorCurvaturePacket where
  modularFlowX : ℝ → EndH
  modularFlowY : ℝ → EndH
  lorentzBoostX : ℝ → EndH
  lorentzBoostY : ℝ → EndH
  curvatureCommutator : ℝ → ℝ → EndH
  riemannReadout : ℝ → ℝ → EndH
  modularX_eq_lorentzX :
    ∀ s : ℝ, modularFlowX s = lorentzBoostX s
  modularY_eq_lorentzY :
    ∀ t : ℝ, modularFlowY t = lorentzBoostY t
  curvatureCommutator_eq :
    ∀ s t : ℝ,
      curvatureCommutator s t =
        modularFlowX s * modularFlowY t - modularFlowY t * modularFlowX s
  riemannReadout_eq_curvature :
    ∀ s t : ℝ, riemannReadout s t = curvatureCommutator s t

namespace ModularLorentzCommutatorCurvaturePacket

/-- The curvature readout is the commutator of two modular flows. -/
@[rep_depth operator]
theorem riemannReadout_eq_modularCommutator
    (C : ModularLorentzCommutatorCurvaturePacket (E := E)) (s t : ℝ) :
    C.riemannReadout s t =
      C.modularFlowX s * C.modularFlowY t
        - C.modularFlowY t * C.modularFlowX s := by
  rw [C.riemannReadout_eq_curvature s t]
  exact C.curvatureCommutator_eq s t

/-- The same curvature readout as a Lorentz-boost commutator. -/
@[rep_depth operator]
theorem riemannReadout_eq_lorentzBoostCommutator
    (C : ModularLorentzCommutatorCurvaturePacket (E := E)) (s t : ℝ) :
    C.riemannReadout s t =
      C.lorentzBoostX s * C.lorentzBoostY t
        - C.lorentzBoostY t * C.lorentzBoostX s := by
  rw [C.riemannReadout_eq_modularCommutator s t]
  rw [C.modularX_eq_lorentzX s, C.modularY_eq_lorentzY t]

end ModularLorentzCommutatorCurvaturePacket

/--
Capstone packet for the operatorial Clifford/Lorentz curvature bridge.

It keeps the four intended layers together:

1. Clifford-Fourier grade separation,
2. modular flow as Lorentz boost in two directions,
3. Drazin-core boost protection,
4. curvature as the commutator of the two modular/Lorentz flows.
-/
@[capstone, rep_depth operator]
structure OperatorLorentzCurvatureCapstone where
  gradeSplit : OperatorialCliffordFourierGradeSplit (E := E)
  boostX : BisognanoWichmannModularLorentzPacket (E := E)
  boostY : BisognanoWichmannModularLorentzPacket (E := E)
  drazinCoreProjector : EndH
  drazinCoreModularGenerator : EndH
  drazinCoreModularFlow : ℝ → EndH
  drazinCore_generator_kills_left :
    drazinCoreModularGenerator * drazinCoreProjector = 0
  drazinCore_generator_kills_right :
    drazinCoreProjector * drazinCoreModularGenerator = 0
  drazinCore_flow_fixes_left :
    ∀ τ : ℝ, drazinCoreModularFlow τ * drazinCoreProjector = drazinCoreProjector
  drazinCore_flow_fixes_right :
    ∀ τ : ℝ, drazinCoreProjector * drazinCoreModularFlow τ = drazinCoreProjector
  curvature : ModularLorentzCommutatorCurvaturePacket (E := E)
  curvature_modularFlowX_matches_boostX :
    curvature.modularFlowX = boostX.modularFlow
  curvature_modularFlowY_matches_boostY :
    curvature.modularFlowY = boostY.modularFlow
  curvature_lorentzBoostX_matches_boostX :
    curvature.lorentzBoostX = boostX.lorentzBoostFlow
  curvature_lorentzBoostY_matches_boostY :
    curvature.lorentzBoostY = boostY.lorentzBoostFlow

namespace OperatorLorentzCurvatureCapstone

/-- The capstone Clifford-Fourier transform readout splits by geometric grade. -/
@[rep_depth operator]
theorem gradeSplit_eq_sum
    (C : OperatorLorentzCurvatureCapstone (E := E)) :
    C.gradeSplit.transformed =
      C.gradeSplit.scalarGrade + C.gradeSplit.vectorGrade
        + C.gradeSplit.bivectorGrade + C.gradeSplit.topologicalGrade :=
  C.gradeSplit.transformed_eq_sum

/-- The capstone Drazin core is killed infinitesimally by the modular generator. -/
@[rep_depth operator]
theorem drazinCore_generator_killed
    (C : OperatorLorentzCurvatureCapstone (E := E)) :
    C.drazinCoreModularGenerator * C.drazinCoreProjector = 0
      ∧ C.drazinCoreProjector * C.drazinCoreModularGenerator = 0 :=
  ⟨C.drazinCore_generator_kills_left, C.drazinCore_generator_kills_right⟩

/-- The capstone Drazin core is fixed by finite modular/Lorentz flow. -/
@[rep_depth operator]
theorem drazinCore_flow_fixed
    (C : OperatorLorentzCurvatureCapstone (E := E)) (τ : ℝ) :
    C.drazinCoreModularFlow τ * C.drazinCoreProjector =
        C.drazinCoreProjector
      ∧ C.drazinCoreProjector * C.drazinCoreModularFlow τ =
        C.drazinCoreProjector :=
  ⟨C.drazinCore_flow_fixes_left τ, C.drazinCore_flow_fixes_right τ⟩

/--
The capstone curvature/Riemann readout is the commutator of the two modular
flows.
-/
@[rep_depth operator]
theorem riemannReadout_eq_modularCommutator
    (C : OperatorLorentzCurvatureCapstone (E := E)) (s t : ℝ) :
    C.curvature.riemannReadout s t =
      C.boostX.modularFlow s * C.boostY.modularFlow t
        - C.boostY.modularFlow t * C.boostX.modularFlow s := by
  rw [C.curvature.riemannReadout_eq_modularCommutator s t]
  rw [C.curvature_modularFlowX_matches_boostX,
    C.curvature_modularFlowY_matches_boostY]

/--
The same capstone curvature/Riemann readout is the commutator of the two
Lorentz-boost flows.
-/
@[rep_depth operator]
theorem riemannReadout_eq_lorentzBoostCommutator
    (C : OperatorLorentzCurvatureCapstone (E := E)) (s t : ℝ) :
    C.curvature.riemannReadout s t =
      C.boostX.lorentzBoostFlow s * C.boostY.lorentzBoostFlow t
        - C.boostY.lorentzBoostFlow t * C.boostX.lorentzBoostFlow s := by
  rw [C.curvature.riemannReadout_eq_lorentzBoostCommutator s t]
  rw [C.curvature_lorentzBoostX_matches_boostX,
    C.curvature_lorentzBoostY_matches_boostY]

/--
Combined operatorial Lorentz-curvature theorem.

It returns the grade split, Drazin-core Lorentz protection, and the curvature
readout as both modular and Lorentz commutators.
-/
@[capstone, rep_depth operator]
theorem operator_lorentz_curvature_theorem
    (C : OperatorLorentzCurvatureCapstone (E := E)) (s t τ : ℝ) :
    C.gradeSplit.transformed =
        C.gradeSplit.scalarGrade + C.gradeSplit.vectorGrade
          + C.gradeSplit.bivectorGrade + C.gradeSplit.topologicalGrade
      ∧ C.drazinCoreModularGenerator * C.drazinCoreProjector = 0
      ∧ C.drazinCoreProjector * C.drazinCoreModularGenerator = 0
      ∧ C.drazinCoreModularFlow τ * C.drazinCoreProjector =
          C.drazinCoreProjector
      ∧ C.drazinCoreProjector * C.drazinCoreModularFlow τ =
          C.drazinCoreProjector
      ∧ C.curvature.riemannReadout s t =
          C.boostX.modularFlow s * C.boostY.modularFlow t
            - C.boostY.modularFlow t * C.boostX.modularFlow s
      ∧ C.curvature.riemannReadout s t =
          C.boostX.lorentzBoostFlow s * C.boostY.lorentzBoostFlow t
            - C.boostY.lorentzBoostFlow t * C.boostX.lorentzBoostFlow s := by
  exact ⟨C.gradeSplit_eq_sum,
    C.drazinCore_generator_killed.1,
    C.drazinCore_generator_killed.2,
    (C.drazinCore_flow_fixed τ).1,
    (C.drazinCore_flow_fixed τ).2,
    C.riemannReadout_eq_modularCommutator s t,
    C.riemannReadout_eq_lorentzBoostCommutator s t⟩

end OperatorLorentzCurvatureCapstone

/--
Owner alias: the canonical wedge bridge identifies modular transport at
wedge-normalized modular time with the Unruh/Lorentz boost flow.
-/
@[rep_depth operator]
theorem wedgeBoost_modularTransport_eq_unruhBoost
    (W :
      InfoGeometry.Canonical.WedgeBoostModularBridge.WedgeBoostModularCompatibility
        (E := E))
    (τwedge : ℝ) :
    InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow
        (E := E) W.modularSeed
        (InfoGeometry.Canonical.RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      =
    InfoGeometry.Dynamics.unruhFlow (E := E) τwedge :=
  W.flow_at_wedgeParameter τwedge

end InfoGeometry.SuperMetriplectic
