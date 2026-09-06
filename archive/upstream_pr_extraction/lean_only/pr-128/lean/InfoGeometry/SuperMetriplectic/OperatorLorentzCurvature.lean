import InfoGeometry.SuperMetriplectic.DiscreteMellinHamiltonian
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
structure OperatorialCliffordFourierGradeData where
  transformed : EndH
  scalarGrade : EndH
  vectorGrade : EndH
  bivectorGrade : EndH
  topologicalGrade : EndH

namespace OperatorialCliffordFourierGradeData

/-- The Clifford-Fourier readout separates into the carried grade lanes. -/
@[rep_depth operator]
theorem transformed_eq_sum
    (G : OperatorialCliffordFourierGradeData (E := E))
    (hSplit : G.transformed =
      G.scalarGrade + G.vectorGrade + G.bivectorGrade + G.topologicalGrade) :
    G.transformed =
      G.scalarGrade + G.vectorGrade + G.bivectorGrade + G.topologicalGrade :=
  hSplit

end OperatorialCliffordFourierGradeData

/--
Bisognano-Wichmann-style compatibility packet.

`modularFlow` is the Tomita-Takesaki flow readout; `lorentzBoostFlow` is the
same operator family viewed as the wedge/Lorentz boost.  The equality is carried
as proof data or obtained from the canonical wedge bridge below.
-/
@[rep_depth operator]
structure BisognanoWichmannModularLorentzData where
  modularFlow : ℝ → EndH
  lorentzBoostFlow : ℝ → EndH

namespace BisognanoWichmannModularLorentzData

/-- Modular flow and Lorentz boost flow are the same carried operator family. -/
@[rep_depth operator]
theorem modularFlow_eq_lorentzBoost
    (B : BisognanoWichmannModularLorentzData (E := E)) (τ : ℝ)
    (hFlow : ∀ τ : ℝ, B.modularFlow τ = B.lorentzBoostFlow τ) :
    B.modularFlow τ = B.lorentzBoostFlow τ :=
  hFlow τ

end BisognanoWichmannModularLorentzData

/--
Curvature packet from two modular/Lorentz directions.

The "Riemann readout" is deliberately an operator-algebraic readout: it is the
commutator of two modular flows.  This is the strongest Lean statement supported
here without importing a coordinate manifold and its tensor calculus.
-/
@[rep_depth operator]
structure ModularLorentzCommutatorCurvatureData where
  modularFlowX : ℝ → EndH
  modularFlowY : ℝ → EndH
  lorentzBoostX : ℝ → EndH
  lorentzBoostY : ℝ → EndH
  curvatureCommutator : ℝ → ℝ → EndH
  riemannReadout : ℝ → ℝ → EndH

namespace ModularLorentzCommutatorCurvatureData

/-- The curvature readout is the commutator of two modular flows. -/
@[rep_depth operator]
theorem riemannReadout_eq_modularCommutator
    (C : ModularLorentzCommutatorCurvatureData (E := E)) (s t : ℝ)
    (hReadout : C.riemannReadout s t = C.curvatureCommutator s t)
    (hCommutator : C.curvatureCommutator s t =
      C.modularFlowX s * C.modularFlowY t - C.modularFlowY t * C.modularFlowX s) :
    C.riemannReadout s t =
      C.modularFlowX s * C.modularFlowY t
        - C.modularFlowY t * C.modularFlowX s := by
  rw [hReadout, hCommutator]

/-- The same curvature readout as a Lorentz-boost commutator. -/
@[rep_depth operator]
theorem riemannReadout_eq_lorentzBoostCommutator
    (C : ModularLorentzCommutatorCurvatureData (E := E)) (s t : ℝ)
    (hReadout : C.riemannReadout s t = C.curvatureCommutator s t)
    (hCommutator : C.curvatureCommutator s t =
      C.modularFlowX s * C.modularFlowY t - C.modularFlowY t * C.modularFlowX s)
    (hModX : C.modularFlowX s = C.lorentzBoostX s)
    (hModY : C.modularFlowY t = C.lorentzBoostY t) :
    C.riemannReadout s t =
      C.lorentzBoostX s * C.lorentzBoostY t
        - C.lorentzBoostY t * C.lorentzBoostX s := by
  rw [hReadout, hCommutator, hModX, hModY]

end ModularLorentzCommutatorCurvatureData

/--
Capstone packet for the operatorial Clifford/Lorentz curvature bridge.

It keeps the four intended layers together:

1. Clifford-Fourier grade separation,
2. modular flow as Lorentz boost in two directions,
3. Drazin-core boost protection,
4. curvature as the commutator of the two modular/Lorentz flows.
-/
@[capstone, rep_depth operator]
structure OperatorLorentzCurvatureData where
  gradeSplit : OperatorialCliffordFourierGradeData (E := E)
  boostX : BisognanoWichmannModularLorentzData (E := E)
  boostY : BisognanoWichmannModularLorentzData (E := E)
  drazinCoreProjector : EndH
  drazinCoreModularGenerator : EndH
  drazinCoreModularFlow : ℝ → EndH
  curvature : ModularLorentzCommutatorCurvatureData (E := E)

namespace OperatorLorentzCurvatureData

/-- The capstone Clifford-Fourier transform readout splits by geometric grade. -/
@[rep_depth operator]
theorem gradeSplit_eq_sum
    (C : OperatorLorentzCurvatureData (E := E))
    (hSplit : C.gradeSplit.transformed =
      C.gradeSplit.scalarGrade + C.gradeSplit.vectorGrade
        + C.gradeSplit.bivectorGrade + C.gradeSplit.topologicalGrade) :
    C.gradeSplit.transformed =
      C.gradeSplit.scalarGrade + C.gradeSplit.vectorGrade
        + C.gradeSplit.bivectorGrade + C.gradeSplit.topologicalGrade :=
  hSplit

/-- The capstone Drazin core is killed infinitesimally by the modular generator. -/
@[rep_depth operator]
theorem drazinCore_generator_killed
    (C : OperatorLorentzCurvatureData (E := E))
    (hLeft : C.drazinCoreModularGenerator * C.drazinCoreProjector = 0)
    (hRight : C.drazinCoreProjector * C.drazinCoreModularGenerator = 0) :
    C.drazinCoreModularGenerator * C.drazinCoreProjector = 0
      ∧ C.drazinCoreProjector * C.drazinCoreModularGenerator = 0 :=
  ⟨hLeft, hRight⟩

/-- The capstone Drazin core is fixed by finite modular/Lorentz flow. -/
@[rep_depth operator]
theorem drazinCore_flow_fixed
    (C : OperatorLorentzCurvatureData (E := E)) (τ : ℝ)
    (hLeft : ∀ τ : ℝ,
      C.drazinCoreModularFlow τ * C.drazinCoreProjector = C.drazinCoreProjector)
    (hRight : ∀ τ : ℝ,
      C.drazinCoreProjector * C.drazinCoreModularFlow τ = C.drazinCoreProjector) :
    C.drazinCoreModularFlow τ * C.drazinCoreProjector =
        C.drazinCoreProjector
      ∧ C.drazinCoreProjector * C.drazinCoreModularFlow τ =
        C.drazinCoreProjector :=
  ⟨hLeft τ, hRight τ⟩

/--
The capstone curvature/Riemann readout is the commutator of the two modular
flows.
-/
@[rep_depth operator]
theorem riemannReadout_eq_modularCommutator
    (C : OperatorLorentzCurvatureData (E := E)) (s t : ℝ)
    (hReadout : C.curvature.riemannReadout s t = C.curvature.curvatureCommutator s t)
    (hCommutator : C.curvature.curvatureCommutator s t =
      C.curvature.modularFlowX s * C.curvature.modularFlowY t
        - C.curvature.modularFlowY t * C.curvature.modularFlowX s)
    (hMatchX : C.curvature.modularFlowX = C.boostX.modularFlow)
    (hMatchY : C.curvature.modularFlowY = C.boostY.modularFlow) :
    C.curvature.riemannReadout s t =
      C.boostX.modularFlow s * C.boostY.modularFlow t
        - C.boostY.modularFlow t * C.boostX.modularFlow s := by
  rw [hReadout, hCommutator, hMatchX, hMatchY]

/--
The same capstone curvature/Riemann readout is the commutator of the two
Lorentz-boost flows.
-/
@[rep_depth operator]
theorem riemannReadout_eq_lorentzBoostCommutator
    (C : OperatorLorentzCurvatureData (E := E)) (s t : ℝ)
    (hReadout : C.curvature.riemannReadout s t = C.curvature.curvatureCommutator s t)
    (hCommutator : C.curvature.curvatureCommutator s t =
      C.curvature.modularFlowX s * C.curvature.modularFlowY t
        - C.curvature.modularFlowY t * C.curvature.modularFlowX s)
    (hMatchX : C.curvature.lorentzBoostX = C.boostX.lorentzBoostFlow)
    (hMatchY : C.curvature.lorentzBoostY = C.boostY.lorentzBoostFlow)
    (hModX : C.curvature.modularFlowX s = C.curvature.lorentzBoostX s)
    (hModY : C.curvature.modularFlowY t = C.curvature.lorentzBoostY t) :
    C.curvature.riemannReadout s t =
      C.boostX.lorentzBoostFlow s * C.boostY.lorentzBoostFlow t
        - C.boostY.lorentzBoostFlow t * C.boostX.lorentzBoostFlow s := by
  rw [hReadout, hCommutator, hModX, hModY, hMatchX, hMatchY]

/--
Combined operatorial Lorentz-curvature theorem.

It returns the grade split, Drazin-core Lorentz protection, and the curvature
readout as both modular and Lorentz commutators.
-/
@[capstone, rep_depth operator]
theorem operator_lorentz_curvature_theorem
    (C : OperatorLorentzCurvatureData (E := E)) (s t τ : ℝ)
    (hSplit : C.gradeSplit.transformed =
      C.gradeSplit.scalarGrade + C.gradeSplit.vectorGrade
        + C.gradeSplit.bivectorGrade + C.gradeSplit.topologicalGrade)
    (hGenLeft : C.drazinCoreModularGenerator * C.drazinCoreProjector = 0)
    (hGenRight : C.drazinCoreProjector * C.drazinCoreModularGenerator = 0)
    (hFlowLeft : ∀ τ : ℝ,
      C.drazinCoreModularFlow τ * C.drazinCoreProjector = C.drazinCoreProjector)
    (hFlowRight : ∀ τ : ℝ,
      C.drazinCoreProjector * C.drazinCoreModularFlow τ = C.drazinCoreProjector)
    (hReadout : C.curvature.riemannReadout s t = C.curvature.curvatureCommutator s t)
    (hCommutator : C.curvature.curvatureCommutator s t =
      C.curvature.modularFlowX s * C.curvature.modularFlowY t
        - C.curvature.modularFlowY t * C.curvature.modularFlowX s)
    (hMatchModX : C.curvature.modularFlowX = C.boostX.modularFlow)
    (hMatchModY : C.curvature.modularFlowY = C.boostY.modularFlow)
    (hMatchLorX : C.curvature.lorentzBoostX = C.boostX.lorentzBoostFlow)
    (hMatchLorY : C.curvature.lorentzBoostY = C.boostY.lorentzBoostFlow)
    (hModX : C.curvature.modularFlowX s = C.curvature.lorentzBoostX s)
    (hModY : C.curvature.modularFlowY t = C.curvature.lorentzBoostY t) :
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
  exact ⟨hSplit, hGenLeft, hGenRight, hFlowLeft τ, hFlowRight τ,
    C.riemannReadout_eq_modularCommutator s t hReadout hCommutator
      hMatchModX hMatchModY,
    C.riemannReadout_eq_lorentzBoostCommutator s t hReadout hCommutator
      hMatchLorX hMatchLorY hModX hModY⟩

end OperatorLorentzCurvatureData

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
