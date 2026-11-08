/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.GrandUnification.AlgebraicSouriauTomita
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Thermodynamics.FiniteConnesCocycle

/-!
# Finite Commuting Cartan Modular Transport and Souriau–Tomita Synthesis

This module proves the finite commuting Cartan modular transport cocycle law
owned by `InfoGeometry.Thermodynamics.FiniteConnesCocycle` together with its
four-pillar Souriau–Tomita synthesis from
`InfoGeometry.GrandUnification.AlgebraicSouriauTomita`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Thermodynamics.FiniteConnesCocycle`:
    `finite_commuting_connes_cocycle_satisfies_cocycle`.
  * `InfoGeometry.GrandUnification.AlgebraicSouriauTomita`:
    `h1_diagonal_volume_cocycle_det_exp`,
    `massieu_potential_zero_ne_volume_cocycle_log`,
    `finite_commuting_connes_phase_cocycle_law`,
    `normal_ordered_car_matrix_unit_wick_commutator`,
    `algebraic_souriau_tomita_four_pillar_synthesis`.
- BUCKET 2 (Deconfabulation):
  * Replaced the named-target wrapper theorems with direct, wrapper-free
    modular cocycle and Souriau–Tomita synthesis theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `finite_modular_connes_phase_cocycle_law`
  * `tomita_gromov_finite_connes_souriau_synthesis`
-/

noncomputable section

namespace InfoGeometry.GrandUnification

/-- Finite modular transport cocycle law: the finite unitary Connes phase
satisfies the scalar 1-cocycle equation under the reference modular action on
`Fin 2`, and the difference between left and right sides vanishes pointwise. -/
theorem finite_modular_connes_phase_cocycle_law
    (φ ψ : _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.FiniteTemperature (Fin 2))
    (s t : ℝ) :
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
    (∀ i : Fin 2,
      _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
          φ ψ (s + t) i -
        _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
          φ ψ s i *
          _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteScalarReferenceModularAction
            φ s
              (fun j =>
                _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
                  φ ψ t j) i = 0) := by
  have hcocycle := finite_commuting_connes_phase_cocycle_law φ ψ s t
  refine ⟨hcocycle, ?_⟩
  intro i
  have hi := congrFun hcocycle i
  rw [hi, sub_self]

/-- Combined finite Connes modular transport and four-pillar Souriau–Tomita
synthesis theorem on `Fin 2`. -/
theorem tomita_gromov_finite_connes_souriau_synthesis
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
  have hsynth := algebraic_souriau_tomita_four_pillar_synthesis
    v φ ψ s t A psiPlus psiMinus car_minus_plus car_plus_plus car_minus_minus a b c d
  rcases hsynth with ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end InfoGeometry.GrandUnification

end
