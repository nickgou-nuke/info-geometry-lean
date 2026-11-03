/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumMarginal
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics

/-! # Coarse-grained recovery for operator-valued Zorn slices

The cut acts on the actual flattened two-sheet matrix carrier. An operator
contraction supplies a completely positive trace-preserving channel. A pair
of distinct density matrices remains indistinguishable at all finite times
after the even Peirce projection.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornCoarseGrainedRecovery

open Matrix InfoGeometry.Physics.NCG InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumBridge
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open scoped ComplexOrder MatrixOrder

variable {d : ℕ} [NeZero d]
local notation "Flat" => Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ

/-- Both complementary sheets of the flattened operator space are nonzero. -/
theorem zornFlatSheet_nontrivial : (zornFlatSheet : Flat) ≠ 0 ∧ (zornFlatSheet : Flat) ≠ 1 := by
  let a : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  constructor
  · intro h
    have he := congrArg (fun M : Flat => M (0, a) (0, a)) h
    simpa [zornFlatSheet, peirceSheetProj, Matrix.comp_apply, Matrix.one_apply] using he
  · intro h
    have he := congrArg (fun M : Flat => M (1, a) (1, a)) h
    simpa [zornFlatSheet, peirceSheetProj, Matrix.comp_apply, Matrix.one_apply] using he

/-- A contractive matrix-valued Zorn coefficient has a genuine CPTP corner
channel for which one pair of distinct density matrices remains invisible
to all finite-time even-block readouts. -/
theorem zorn_cptp_coarse_grained_collision (i : Fin 3)
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
      ∃ ρ σ : Flat, ρ.PosSemidef ∧ σ.PosSemidef ∧
        Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
        ∀ k, evenGrade zornFlatSheet (evolve zornFlatSheet (zornFlatSlice i X) W k ρ) =
          evenGrade zornFlatSheet (evolve zornFlatSheet (zornFlatSlice i X) W k σ) := by
  have hLower := (matrix_ordered_gram_bounds_iff (X.sigma_plus i)).mp hUpper
  have hBound := zornFlatSlice_bound_of_compressions i X hUpper hLower
  obtain ⟨W, hEven, hTrace, hCP, _⟩ :=
    exists_cptp_coarse_grained_no_recovery zornFlatSheet (zornFlatSlice i X)
      zornFlatSheet_idem zornFlatSheet_star zornFlatSheet_nontrivial.1
      zornFlatSheet_nontrivial.2 hBound
  refine ⟨W, hEven, hTrace, hCP, ?_⟩
  exact exists_densities_colliding_after_evolution zornFlatSheet (zornFlatSlice i X) W
    zornFlatSheet_idem zornFlatSheet_star hEven zornFlatSheet_nontrivial.1
    zornFlatSheet_nontrivial.2

/-- Every iterate of the completed corner channel maps density matrices to
    density matrices on the full matrix carrier. -/
theorem zorn_evolve_density (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ)) (W ρ : Flat)
    (hResidual : star W * W = 1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X)))
    (hPos : ρ.PosSemidef) (hTrace : Matrix.trace ρ = 1) (k : ℕ) :
    (evolve zornFlatSheet (zornFlatSlice i X) W k ρ).PosSemidef ∧
      Matrix.trace (evolve zornFlatSheet (zornFlatSlice i X) W k ρ) = 1 := by
  induction k with
  | zero => exact ⟨hPos, hTrace⟩
  | succ k ih =>
      change (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)
        (evolve zornFlatSheet (zornFlatSlice i X) W k ρ)).PosSemidef ∧ _
      exact ⟨cornerKrausWithResidual_positive _ _ _ _ ih.1,
        (cornerKrausWithResidual_trace _ _ _ _ zornFlatSheet_star hResidual).trans ih.2⟩

/-- After pinching, the reduced output states are positive, normalized and
    indistinguishable at every finite time for two distinct initial states. -/
theorem zorn_reduced_collision (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ))
    (hUpper : (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef) :
    ∃ W ρ σ : Flat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      ∀ k : ℕ,
        (partialTraceSecondOp (evenGrade zornFlatSheet
          (evolve zornFlatSheet (zornFlatSlice i X) W k ρ))).PosSemidef ∧
        Matrix.trace (partialTraceSecondOp (evenGrade zornFlatSheet
          (evolve zornFlatSheet (zornFlatSlice i X) W k ρ))) = 1 ∧
        partialTraceSecondOp (evenGrade zornFlatSheet
          (evolve zornFlatSheet (zornFlatSlice i X) W k ρ)) =
        partialTraceSecondOp (evenGrade zornFlatSheet
          (evolve zornFlatSheet (zornFlatSlice i X) W k σ)) := by
  have hLower := (matrix_ordered_gram_bounds_iff (X.sigma_plus i)).mp hUpper
  have hBound := zornFlatSlice_bound_of_compressions i X hUpper hLower
  obtain ⟨W, hEven, hResidual⟩ := exists_even_residual zornFlatSheet (zornFlatSlice i X)
    zornFlatSheet_idem hBound
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    exists_densities_colliding_after_evolution zornFlatSheet (zornFlatSlice i X) W
      zornFlatSheet_idem zornFlatSheet_star hEven zornFlatSheet_nontrivial.1
      zornFlatSheet_nontrivial.2
  refine ⟨W, ρ, σ, hρ, hσ, htρ, htσ, hne, ?_⟩
  intro k
  have hE := zorn_evolve_density i X W ρ hResidual hρ htρ k
  have hPinch := pinching_is_density zornFlatSheet _ zornFlatSheet_idem
    zornFlatSheet_star hE.1 hE.2
  exact ⟨partialTraceSecond_posSemidef _ hPinch.1,
    (partialTraceSecondOp_trace _).trans hPinch.2,
    congrArg partialTraceSecondOp (heq k)⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornCoarseGrainedRecovery

end
