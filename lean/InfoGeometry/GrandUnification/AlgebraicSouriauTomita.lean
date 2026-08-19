import InfoGeometry.Canonical.BoundaryMatrixUnitWick
import InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal
import InfoGeometry.Thermodynamics.FiniteConnesCocycle
import InfoGeometry.Thermodynamics.FiniteGibbsRelative
import InfoGeometry.Volume.ConnesCocycle

/-!
# Algebraic Souriau--Tomita roadmap, theorem-stack version

This module is intentionally not a grand data packet.

It records the Lean-safe separation of the four finite theorem surfaces:

* `H¹` determinant/exponential trace controls finite volume transport;
* `log Tr(exp θ)` controls the finite Massieu/Fisher layer;
* finite commuting Connes phases control scalar Cartan modular transport;
* normal-ordered CAR matrix units control the `H²` Wick/Schwinger anomaly.

The intended dictionary is deliberately non-identifying:

* volume cocycle: `det(exp A)`, the finite Weyl/Jacobian readout;
* log-volume generator: `trace A`, the additive `H¹` cocycle;
* partition function: `Tr(exp (-βQ))`, the thermodynamic normalization;
* Massieu potential: `log Tr(exp (-βQ))`, the Fisher/Souriau potential;
* finite Connes phase: `exp (-I * t * (Kψ - Kφ))`, the unitary relative-time
  transporter;
* positive density ratio: `exp (-(Kψ - Kφ))`, the finite Radon--Nikodym
  density shadow.

Thus determinant/trace mechanics is only the finite `H¹` log-Jacobian
component.  It is not the statistical partition function, it does not produce
the Fisher metric, and it does not by itself prove fluctuation theorems.
Duistermaat--Heckman localization and general Tomita--Takesaki/Connes theory
belong to separate theorem surfaces with their own hypotheses.

The module contains no assumed data fields.  Its target theorem is a conjunction
of propositions already proved in the owner modules.
-/

noncomputable section

namespace InfoGeometry.GrandUnification

open scoped Matrix

/-- H¹ finite volume-cocycle theorem surface, restricted to a concrete finite chart. -/
def H1VolumeCocycleSurface : Prop :=
  ∀ v : Fin 2 → ℂ,
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v))

/--
Finite Massieu/Fisher firewall: even at the symmetric two-point Cartan chart,
the statistical Massieu potential and determinant log-volume readout differ.
-/
def MassieuVolumeSeparationSurface : Prop :=
  _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.massieuPotential
      (ι := Fin 2) (fun _ => (0 : ℝ)) ≠
    _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.volumeCocycleLog
      (ι := Fin 2) (fun _ => (0 : ℝ))

/-! Genuine operator-valued Connes cocycle surface on the doubled carrier. -/
def OperatorialConnesTransportSurface
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Prop :=
  ∀
      (K : _root_.InfoGeometry.Volume.ConnesCocycle.AlgebraEnd E) (s t : ℝ),
    _root_.InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (_root_.InfoGeometry.Volume.ConnesCocycle.additiveModularFlowOfGenerator K) (s + t) =
      _root_.InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (_root_.InfoGeometry.Volume.ConnesCocycle.additiveModularFlowOfGenerator K) s *
        (_root_.InfoGeometry.Volume.ConnesCocycle.additiveModularFlowOfGenerator K) s
          (_root_.InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
            (_root_.InfoGeometry.Volume.ConnesCocycle.additiveModularFlowOfGenerator K) t)

/-- H² Wick/Schwinger owner theorem surface, stated as the raw-CAR implication. -/
def BoundaryWickAnomalySurface : Prop :=
  ∀ (A : Type) [Ring A] (psiPlus psiMinus : Int → A)
      (_car_minus_plus :
        ∀ b c : Int,
          psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
            if b = c then 1 else 0)
      (_car_plus_plus :
        ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
      (_car_minus_minus :
        ∀ b d : Int,
          psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
      (a b c d : Int),
    _root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.comm
        (_root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.matrixUnit psiPlus psiMinus a b)
        (_root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.matrixUnit psiPlus psiMinus c d) =
      (if b = c then
          _root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.matrixUnit psiPlus psiMinus a d
        else 0) -
        (if a = d then
          _root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.matrixUnit psiPlus psiMinus c b
        else 0) +
        (if b = c ∧ a = d then
          (_root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ a -
            _root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ c) • (1 : A)
        else 0)


/-- The concrete H¹ diagonal volume-cocycle surface is available. -/
theorem h1VolumeCocycleSurface :
    H1VolumeCocycleSurface := by
  intro v
  exact _root_.InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal.det_exp_diagonal v

/-- The finite Massieu potential is not the determinant log-volume readout. -/
theorem massieuVolumeSeparationSurface :
    MassieuVolumeSeparationSurface :=
  _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.massieuPotential_zero_fin_two_ne_volumeCocycleLog_zero

/-- The native operator-valued modular flow satisfies the Connes cocycle law. -/
theorem operatorialConnesTransportSurface :
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      OperatorialConnesTransportSurface E := by
  intro E _ _ _ K s t
  exact
    _root_.InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_cocycle
      (_root_.InfoGeometry.Volume.ConnesCocycle.additiveModularFlowOfGenerator K) s t

/-- The boundary Wick/Schwinger commutator follows from raw CAR. -/
theorem boundaryWickAnomalySurface :
    BoundaryWickAnomalySurface := by
  intro A _inst psiPlus psiMinus car_minus_plus car_plus_plus car_minus_minus a b c d
  exact
    _root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.normalOrdered_matrixUnit_commutator_from_rawCAR
      psiPlus psiMinus car_minus_plus car_plus_plus car_minus_minus a b c d

/--
Constructor for the corrected roadmap target.

No external data are accepted: each component is discharged by its owner theorem.
-/
theorem algebraicSouriauTomita_properties :
    (H1VolumeCocycleSurface ∧ MassieuVolumeSeparationSurface ∧ OperatorialConnesTransportSurface ℝ ∧ BoundaryWickAnomalySurface) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h1VolumeCocycleSurface
  · exact massieuVolumeSeparationSurface
  · exact operatorialConnesTransportSurface ℝ
  · exact boundaryWickAnomalySurface

end InfoGeometry.GrandUnification
