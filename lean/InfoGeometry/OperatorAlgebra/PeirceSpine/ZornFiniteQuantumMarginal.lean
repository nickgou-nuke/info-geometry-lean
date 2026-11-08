/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal

/-! # Reduced states for a matrix-valued Zorn slice -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumMarginal

open Matrix InfoGeometry.Physics.NCG InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumBridge
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open scoped ComplexOrder

variable {d : ℕ} [NeZero d]

/-- Under the contractivity bound, an operator-valued Zorn slice admits
a trace-preserving corner channel whose global and sheet-reduced states are
positive and normalized at every discrete time. -/
theorem zorn_channel_and_reduced_state_evolution (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ))
    (hUpper : (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef) :
    ∃ W : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ,
      (∀ Z : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ,
        Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
          (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z) = Matrix.trace Z) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (Z : Matrix (r × (Fin 2 × Fin d)) (r × (Fin 2 × Fin d)) ℂ), Z.PosSemidef →
          (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
            (InfoGeometry.Modular.Choi.krausChannel
              (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)) Z).PosSemidef) ∧
      (∀ k, (zornStateEvolution i X W k).PosSemidef ∧
        Matrix.trace (zornStateEvolution i X W k) = 1 ∧
        (partialTraceSecondOp (zornStateEvolution i X W k)).PosSemidef ∧
        Matrix.trace (partialTraceSecondOp (zornStateEvolution i X W k)) = 1) := by
  have hLower := (matrix_ordered_gram_bounds_iff (X.sigma_plus i)).mp hUpper
  have hBound := zornFlatSlice_bound_of_compressions i X hUpper hLower
  obtain ⟨W, hW⟩ := exists_residual_kraus zornFlatSheet (zornFlatSlice i X) hBound
  refine ⟨W, ?_, ?_, ?_⟩
  · intro Z
    exact cornerKrausWithResidual_trace _ _ W Z zornFlatSheet_star hW
  · intro r _ _ Z hZ
    exact cornerKrausWithResidual_completely_positive _ _ W Z hZ
  · intro k
    rcases zornStateEvolution_is_density i X W hBound hW k with ⟨hPos, hTrace⟩
    exact ⟨hPos, hTrace, partialTraceSecond_posSemidef _ hPos,
      (partialTraceSecondOp_trace _).trans hTrace⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumMarginal

end
