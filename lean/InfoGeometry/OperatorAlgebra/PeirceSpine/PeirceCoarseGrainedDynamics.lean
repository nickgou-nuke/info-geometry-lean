/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePositiveCollision

/-! # Coarse-grained Peirce dynamics

A grading-covariant channel cannot restore distinctions erased by pinching,
even when an arbitrary number of channel steps precedes the measurement.
The obstruction is witnessed by two distinct normalized positive matrices.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePositiveCollision
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- Iteration of the residual-completed corner channel on an arbitrary input. -/
def evolve (P A W : Mat) : ℕ → Mat → Mat
  | 0, X => X
  | k + 1, X => InfoGeometry.Quantum.Choi.krausMap
      (cornerKrausWithResidual P A W) (evolve P A W k X)

/-- Every finite iterate intertwines the Peirce pinching projection. -/
theorem evolve_pinching (P A W X : Mat) (hP : P * P = P)
    (hPs : star P = P) (hW : evenGrade P W = W) (k : ℕ) :
    evenGrade P (evolve P A W k X) = evolve P A W k (evenGrade P X) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change evenGrade P (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual P A W) (evolve P A W k X)) = _
      rw [corner_channel_pinching_covariant P A W _ hP hPs hW, ih]
      rfl

/-- A nontrivial Peirce cut gives two different density matrices whose
coarse-grained outputs agree after every finite channel iterate. -/
theorem exists_densities_colliding_after_evolution
    (P A W : Mat) (hP : P * P = P) (hPs : star P = P)
    (hW : evenGrade P W = W) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ ρ σ : Mat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      ∀ k, evenGrade P (evolve P A W k ρ) = evenGrade P (evolve P A W k σ) := by
  have hQ : 1 - P ≠ 0 := by
    intro h
    exact hP1 (sub_eq_zero.mp h).symm
  obtain ⟨Z, hZ⟩ := exists_nonzero_matrix_sandwich P (1 - P) hP0 hQ
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    exists_indistinguishable_densities P Z hP hPs hZ
  refine ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, ?_⟩
  intro k
  rw [evolve_pinching P A W ρ hP hPs hW, evolve_pinching P A W σ hP hPs hW, heq]

/-- No decoder, including a quantum channel, can recover every input density
matrix from the pinched output after any fixed number of channel steps. -/
theorem no_density_recovery_after_evolution
    (P A W : Mat) (hP : P * P = P) (hPs : star P = P)
    (hW : evenGrade P W = W) (hP0 : P ≠ 0) (hP1 : P ≠ 1) (k : ℕ) :
    ¬ ∃ recovery : Mat → Mat, ∀ ρ : Mat, ρ.PosSemidef → Matrix.trace ρ = 1 →
      recovery (evenGrade P (evolve P A W k ρ)) = ρ := by
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    exists_densities_colliding_after_evolution P A W hP hPs hW hP0 hP1
  rintro ⟨recovery, hr⟩
  have hρ' := hr ρ hρ htρ
  have hσ' := hr σ hσ htσ
  rw [heq k] at hρ'
  exact hne (hρ'.symm.trans hσ')

/-- A positive residual bound constructs a grading-covariant CPTP channel
whose coarse-grained output admits no universal density-matrix decoder,
for any finite number of channel steps. -/
theorem exists_cptp_coarse_grained_no_recovery
    (P A : Mat) (hP : P * P = P) (hPs : star P = P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (hBound : (1 - genV P A (star A)).PosSemidef) :
    ∃ W : Mat, evenGrade P W = W ∧
      (∀ X : Mat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual P A W) X) = Matrix.trace X) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (X : Matrix (r × n) (r × n) ℂ), X.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
          (InfoGeometry.Modular.Choi.krausChannel (cornerKrausWithResidual P A W)) X).PosSemidef) ∧
      ∀ k, ¬ ∃ recovery : Mat → Mat, ∀ ρ : Mat,
        ρ.PosSemidef → Matrix.trace ρ = 1 →
        recovery (evenGrade P (evolve P A W k ρ)) = ρ := by
  obtain ⟨W, hEven, hResidual⟩ := exists_even_residual P A hP hBound
  refine ⟨W, hEven, ?_, ?_, ?_⟩
  · intro X
    exact cornerKrausWithResidual_trace P A W X hPs hResidual
  · intro r _ _ X hX
    exact cornerKrausWithResidual_completely_positive P A W X hX
  · intro k
    exact no_density_recovery_after_evolution P A W hP hPs hEven hP0 hP1 k

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics

end
