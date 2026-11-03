/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornCoarseGrainedRecovery

/-! # Coarse-grained histories of operator-valued Zorn channels

Equality of all finite-time observations gives equality of the entire
sequence. This is an obstruction to universal decoding from that sequence,
including decoders that do not themselves satisfy a channel condition.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornReducedHistory

open Matrix InfoGeometry.Physics.NCG InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornCoarseGrainedRecovery
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open scoped ComplexOrder MatrixOrder

variable {d : ℕ} [NeZero d]
local notation "Flat" => Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ
local notation "Sheet" => Matrix (Fin 2) (Fin 2) ℂ

/-- The entire sequence of reduced, pinched finite-time observations. -/
def reducedHistory (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ)) (W ρ : Flat) : ℕ → Sheet :=
  fun k => partialTraceSecondOp
    (evenGrade zornFlatSheet (evolve zornFlatSheet (zornFlatSlice i X) W k ρ))

/-- Even residual Kraus operators force one fixed pair of distinct density
matrices to have identical complete observation histories. -/
theorem reducedHistory_collision (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ)) (W : Flat)
    (hEven : evenGrade zornFlatSheet W = W) :
    ∃ ρ σ : Flat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      reducedHistory i X W ρ = reducedHistory i X W σ := by
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    exists_densities_colliding_after_evolution zornFlatSheet (zornFlatSlice i X) W
      zornFlatSheet_idem zornFlatSheet_star hEven zornFlatSheet_nontrivial.1
      zornFlatSheet_nontrivial.2
  refine ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, ?_⟩
  funext k
  exact congrArg partialTraceSecondOp (heq k)

/-- Access to all finite-time reduced observations still cannot universally
recover arbitrary initial density matrices. -/
theorem no_universal_recovery_from_reduced_history (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ)) (W : Flat)
    (hEven : evenGrade zornFlatSheet W = W) :
    ¬ ∃ recover : (ℕ → Sheet) → Flat, ∀ ρ : Flat,
      ρ.PosSemidef → Matrix.trace ρ = 1 → recover (reducedHistory i X W ρ) = ρ := by
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ := reducedHistory_collision i X W hEven
  rintro ⟨recover, hr⟩
  have hρ' := hr ρ hρ htρ
  have hσ' := hr σ hσ htσ
  rw [heq] at hρ'
  exact hne (hρ'.symm.trans hσ')

/-- Every contractive operator-valued Zorn coefficient supplies a genuine
CPTP channel with a non-recoverable complete reduced observation history. -/
theorem exists_cptp_no_history_recovery (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ))
    (hUpper : (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef) :
    ∃ W : Flat, evenGrade zornFlatSheet W = W ∧
      (∀ Z : Flat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z) = Matrix.trace Z) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (Z : Matrix (r × (Fin 2 × Fin d)) (r × (Fin 2 × Fin d)) ℂ), Z.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
          (InfoGeometry.Modular.Choi.krausChannel
            (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)) Z).PosSemidef) ∧
      ¬ ∃ recover : (ℕ → Sheet) → Flat, ∀ ρ : Flat,
        ρ.PosSemidef → Matrix.trace ρ = 1 → recover (reducedHistory i X W ρ) = ρ := by
  obtain ⟨W, hEven, hTrace, hCP, _⟩ := zorn_cptp_coarse_grained_collision i X hUpper
  exact ⟨W, hEven, hTrace, hCP, no_universal_recovery_from_reduced_history i X W hEven⟩

/-- Each observation in the reduced history is itself a density matrix
whenever the residual Kraus operator satisfies completeness. -/
theorem reducedHistory_is_density (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ)) (W ρ : Flat)
    (hResidual : star W * W = 1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X)))
    (hPos : ρ.PosSemidef) (hTrace : Matrix.trace ρ = 1) (k : ℕ) :
    (reducedHistory i X W ρ k).PosSemidef ∧ Matrix.trace (reducedHistory i X W ρ k) = 1 := by
  have hE := zorn_evolve_density i X W ρ hResidual hPos hTrace k
  have hP := pinching_is_density zornFlatSheet _ zornFlatSheet_idem zornFlatSheet_star hE.1 hE.2
  exact ⟨partialTraceSecond_posSemidef _ hP.1, (partialTraceSecondOp_trace _).trans hP.2⟩

/-- A matrix-valued contraction gives a CPTP channel whose entire observable
history consists of density matrices but does not determine the initial state. -/
theorem exists_cptp_density_history_no_recovery (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ))
    (hUpper : (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef) :
    ∃ W : Flat,
      (∀ Z : Flat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z) = Matrix.trace Z) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (Z : Matrix (r × (Fin 2 × Fin d)) (r × (Fin 2 × Fin d)) ℂ), Z.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
          (InfoGeometry.Modular.Choi.krausChannel
            (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)) Z).PosSemidef) ∧
      (∀ ρ : Flat, ρ.PosSemidef → Matrix.trace ρ = 1 → ∀ k,
        (reducedHistory i X W ρ k).PosSemidef ∧
          Matrix.trace (reducedHistory i X W ρ k) = 1) ∧
      ¬ ∃ recover : (ℕ → Sheet) → Flat, ∀ ρ : Flat,
        ρ.PosSemidef → Matrix.trace ρ = 1 → recover (reducedHistory i X W ρ) = ρ := by
  have hLower := (matrix_ordered_gram_bounds_iff (X.sigma_plus i)).mp hUpper
  have hBound := zornFlatSlice_bound_of_compressions i X hUpper hLower
  obtain ⟨W, hEven, hResidual⟩ := exists_even_residual zornFlatSheet (zornFlatSlice i X)
    zornFlatSheet_idem hBound
  refine ⟨W, ?_, ?_, ?_, no_universal_recovery_from_reduced_history i X W hEven⟩
  · intro Z
    exact cornerKrausWithResidual_trace _ _ _ Z zornFlatSheet_star hResidual
  · intro r _ _ Z hZ
    exact cornerKrausWithResidual_completely_positive _ _ _ Z hZ
  · intro ρ hPos hTrace k
    exact reducedHistory_is_density i X W ρ hResidual hPos hTrace k

/-- The directed Kraus operator retains every nonzero operator coefficient;
this is a statement in the full flattened matrix algebra. -/
theorem zorn_upper_kraus_ne_zero (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ))
    (hX : X.sigma_plus i ≠ 0) (W : Flat) :
    cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W 0 ≠ 0 := by
  change conePlus zornFlatSheet (zornFlatSlice i X) ≠ 0
  intro h
  rw [zornFlatSlice_conePlus] at h
  have hblocks : (!![0, X.sigma_plus i; 0, 0] :
      Matrix (Fin 2) (Fin 2) (Matrix (Fin d) (Fin d) ℂ)) = 0 := by
    have hh : Matrix.compRingEquiv (Fin 2) (Fin d) ℂ
        (!![0, X.sigma_plus i; 0, 0] : Matrix (Fin 2) (Fin 2) (Matrix (Fin d) (Fin d) ℂ)) =
        Matrix.compRingEquiv (Fin 2) (Fin d) ℂ 0 := by
      rw [map_zero]
      exact h
    exact (Matrix.compRingEquiv (Fin 2) (Fin d) ℂ).injective hh
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Matrix (Fin d) (Fin d) ℂ) => M 0 1) hblocks
  apply hX
  simpa using he

/-- A nonzero contractive Zorn coefficient gives a CPTP channel with a
nonzero directed Kraus operator and nonrecoverable reduced histories. -/
theorem exists_nonzero_cptp_no_history_recovery (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ))
    (hX : X.sigma_plus i ≠ 0)
    (hUpper : (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef) :
    ∃ W : Flat,
      cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W 0 ≠ 0 ∧
      (∀ Z : Flat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z) = Matrix.trace Z) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (Z : Matrix (r × (Fin 2 × Fin d)) (r × (Fin 2 × Fin d)) ℂ), Z.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
          (InfoGeometry.Modular.Choi.krausChannel
            (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)) Z).PosSemidef) ∧
      (∀ ρ : Flat, ρ.PosSemidef → Matrix.trace ρ = 1 → ∀ k,
        (reducedHistory i X W ρ k).PosSemidef ∧
          Matrix.trace (reducedHistory i X W ρ k) = 1) ∧
      ¬ ∃ recover : (ℕ → Sheet) → Flat, ∀ ρ : Flat,
        ρ.PosSemidef → Matrix.trace ρ = 1 → recover (reducedHistory i X W ρ) = ρ := by
  obtain ⟨W, hTrace, hCP, hDensity, hNoRecovery⟩ :=
    exists_cptp_density_history_no_recovery i X hUpper
  exact ⟨W, zorn_upper_kraus_ne_zero i X hX W, hTrace, hCP, hDensity, hNoRecovery⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornReducedHistory

end
