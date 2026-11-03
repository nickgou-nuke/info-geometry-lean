/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceEvenObservables
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornCoarseGrainedRecovery

/-! # Even observables for matrix-valued Zorn evolution -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornEvenObservables

open Matrix InfoGeometry.Physics.NCG InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceEvenObservables
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornCoarseGrainedRecovery
open scoped ComplexOrder MatrixOrder

variable {d : ℕ} [NeZero d]
local notation "Flat" => Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ

/-- A contractive Zorn operator coefficient defines an even-residual channel
and two distinct states indistinguishable by all even matrix observables at
every finite step. -/
theorem zorn_even_observable_collision (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ))
    (hUpper : (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef) :
    ∃ W ρ σ : Flat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      (∀ Z : Flat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (BlackHoleFiniteQuantum.cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z) =
        Matrix.trace Z) ∧
      ∀ (k : ℕ) (O : Flat), evenGrade zornFlatSheet O = O →
        Matrix.trace (O * evolve zornFlatSheet (zornFlatSlice i X) W k ρ) =
          Matrix.trace (O * evolve zornFlatSheet (zornFlatSlice i X) W k σ) := by
  have hLower := (matrix_ordered_gram_bounds_iff (X.sigma_plus i)).mp hUpper
  have hBound := zornFlatSlice_bound_of_compressions i X hUpper hLower
  obtain ⟨W, hEven, hResidual⟩ := exists_even_residual zornFlatSheet (zornFlatSlice i X)
    zornFlatSheet_idem hBound
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, hexp⟩ :=
    exists_density_pair_same_even_expectations zornFlatSheet (zornFlatSlice i X) W
      zornFlatSheet_idem zornFlatSheet_star hEven zornFlatSheet_nontrivial.1
      zornFlatSheet_nontrivial.2
  refine ⟨W, ρ, σ, hρ, hσ, htρ, htσ, hne, ?_, hexp⟩
  intro Z
  exact BlackHoleFiniteQuantum.cornerKrausWithResidual_trace _ _ _ Z zornFlatSheet_star hResidual

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornEvenObservables

end
