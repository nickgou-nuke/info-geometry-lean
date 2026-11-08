/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BoundaryMatrixUnitWick
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal
import InfoGeometry.Thermodynamics.FiniteConnesCocycle
import InfoGeometry.Thermodynamics.FiniteGibbsRelative

/-!
# Algebraic Souriau–Tomita Four-Pillar Synthesis

This module records the wrapper-free separation and conjunction of the four
finite thermodynamic and operator-algebraic pillars:

* `H¹` determinant/exponential trace controls finite diagonal volume transport:
  $\det(\exp(\mathrm{diag}(v))) = \exp(\operatorname{Tr}(\mathrm{diag}(v)))$;
* $\log\operatorname{Tr}(\exp\theta)$ controls the finite Massieu/Fisher layer,
  strictly separated from the determinant log-volume readout at $\theta = 0$;
* finite commuting Connes phases satisfy the scalar relative-time cocycle law;
* normal-ordered CAR matrix units satisfy the `H²` Wick/Schwinger commutator
  with occupation-number central anomaly.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal`: `det_exp_diagonal`.
  * `InfoGeometry.Thermodynamics.FiniteGibbsRelative`:
    `massieuPotential_zero_fin_two_ne_volumeCocycleLog_zero`.
  * `InfoGeometry.Thermodynamics.FiniteConnesCocycle`:
    `finite_commuting_connes_cocycle_satisfies_cocycle`.
  * `InfoGeometry.Canonical.BoundaryMatrixUnitWick`:
    `normalOrdered_matrixUnit_commutator_from_rawCAR`.
- BUCKET 2 (Deconfabulation):
  * Replaced the five `Prop`-valued `def` wrappers (`H1VolumeCocycleSurface`,
    `MassieuVolumeSeparationSurface`, `FiniteConnesTransportSurface`,
    `BoundaryWickAnomalySurface`, `AlgebraicSouriauTomitaTarget`) with direct,
    wrapper-free theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `h1_diagonal_volume_cocycle_det_exp`
  * `massieu_potential_zero_ne_volume_cocycle_log`
  * `finite_commuting_connes_phase_cocycle_law`
  * `normal_ordered_car_matrix_unit_wick_commutator`
  * `algebraic_souriau_tomita_four_pillar_synthesis`
-/

noncomputable section

namespace InfoGeometry.GrandUnification

open scoped Matrix

/-- Concrete `H¹` diagonal volume-cocycle identity: for any $v : \mathrm{Fin}\,2 \to \mathbb{C}$,
$\det(\exp(\mathrm{diag}(v))) = \exp(\operatorname{Tr}(\mathrm{diag}(v)))$, and subtracting the
right-hand side yields zero. -/
theorem h1_diagonal_volume_cocycle_det_exp (v : Fin 2 → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) ∧
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) -
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) = 0 := by
  have hdet := _root_.InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal.det_exp_diagonal v
  refine ⟨hdet, ?_⟩
  rw [hdet, sub_self]

/-- Finite Massieu/Fisher separation law on $\mathrm{Fin}\,2$: at the symmetric zero chart
$\theta = 0$, the statistical Massieu potential $\log\operatorname{Tr}(\exp\theta)$ and the
determinant log-volume readout $\operatorname{Tr}(\theta)$ are strictly distinct. -/
theorem massieu_potential_zero_ne_volume_cocycle_log :
    _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.massieuPotential
        (ι := Fin 2) (fun _ => (0 : ℝ)) ≠
      _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.volumeCocycleLog
        (ι := Fin 2) (fun _ => (0 : ℝ)) ∧
    _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.volumeCocycleLog
        (ι := Fin 2) (fun _ => (0 : ℝ)) ≠
      _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.massieuPotential
        (ι := Fin 2) (fun _ => (0 : ℝ)) := by
  have hne :=
    _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.massieuPotential_zero_fin_two_ne_volumeCocycleLog_zero
  exact ⟨hne, Ne.symm hne⟩

/-- Finite commuting Connes phase cocycle law on $\mathrm{Fin}\,2$ with explicit scalar
reference modular action. -/
theorem finite_commuting_connes_phase_cocycle_law
    (φ ψ : _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.FiniteTemperature (Fin 2))
    (s t : ℝ) :
    (fun i =>
        _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
          φ ψ (s + t) i) =
      fun i =>
        _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
          φ ψ s i *
          _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteScalarReferenceModularAction
            φ s
              (fun j =>
                _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
                  φ ψ t j) i := by
  have hcocycle :=
    _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finite_commuting_connes_cocycle_satisfies_cocycle
      φ ψ s t
  rw [hcocycle]

/-- Boundary Wick/Schwinger commutator identity for normal-ordered CAR matrix units
from raw canonical anticommutation relations. -/
theorem normal_ordered_car_matrix_unit_wick_commutator
    (A : Type) [Ring A] (psiPlus psiMinus : Int → A)
    (car_minus_plus :
      ∀ b c : Int,
        psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
          if b = c then 1 else 0)
    (car_plus_plus :
      ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
    (car_minus_minus :
      ∀ b d : Int,
        psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
    (a b c d : Int) :
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
        else 0) := by
  have hwick :=
    _root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.normalOrdered_matrixUnit_commutator_from_rawCAR
      psiPlus psiMinus car_minus_plus car_plus_plus car_minus_minus a b c d
  rw [hwick]

/-- **Algebraic Souriau–Tomita Four-Pillar Synthesis (`algebraic_souriau_tomita_four_pillar_synthesis`):**
Unifies in one wrapper-free theorem:
1. `H¹` diagonal volume-cocycle identity $\det(\exp(\mathrm{diag}(v))) = \exp(\operatorname{Tr}(\mathrm{diag}(v)))$;
2. Finite Massieu/Fisher separation $\Phi_{\mathrm{Massieu}}(0) \ne \log\det(\exp(0))$ on $\mathrm{Fin}\,2$;
3. Finite commuting Connes phase cocycle law $u_{\psi|\varphi}(s+t) = u_{\psi|\varphi}(s)\,\sigma^\varphi_s(u_{\psi|\varphi}(t))$;
4. Normal-ordered CAR matrix-unit Wick commutator with occupation-number central anomaly. -/
theorem algebraic_souriau_tomita_four_pillar_synthesis
    (v : Fin 2 → ℂ)
    (φ ψ : _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.FiniteTemperature (Fin 2))
    (s t : ℝ)
    (A : Type) [Ring A] (psiPlus psiMinus : Int → A)
    (car_minus_plus :
      ∀ b c : Int,
        psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
          if b = c then 1 else 0)
    (car_plus_plus :
      ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
    (car_minus_minus :
      ∀ b d : Int,
        psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
    (a b c d : Int) :
    (Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v))) ∧
    (_root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.massieuPotential
        (ι := Fin 2) (fun _ => (0 : ℝ)) ≠
      _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.volumeCocycleLog
        (ι := Fin 2) (fun _ => (0 : ℝ))) ∧
    ((fun i =>
        _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
          φ ψ (s + t) i) =
      fun i =>
        _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
          φ ψ s i *
          _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteScalarReferenceModularAction
            φ s
              (fun j =>
                _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
                  φ ψ t j) i) ∧
    (_root_.InfoGeometry.Canonical.BoundaryMatrixUnitWick.comm
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
        else 0)) := by
  have h1 := (h1_diagonal_volume_cocycle_det_exp v).1
  have h2 := massieu_potential_zero_ne_volume_cocycle_log.1
  have h3 := finite_commuting_connes_phase_cocycle_law φ ψ s t
  have h4 := normal_ordered_car_matrix_unit_wick_commutator
    A psiPlus psiMinus car_minus_plus car_plus_plus car_minus_minus a b c d
  exact ⟨h1, h2, h3, h4⟩

end InfoGeometry.GrandUnification

end
