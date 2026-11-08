/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
import InfoGeometry.Quantum.FiniteAttentionCanonicalBridges

/-! # Reduced states of the Peirce corner channel -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open scoped ComplexOrder

/-- Partial trace is a sum of positive diagonal compressions. -/
theorem partialTraceSecond_posSemidef {m r : ℕ}
    (X : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ) (hX : X.PosSemidef) :
    (partialTraceSecondOp X).PosSemidef := by
  let blocks : Fin r → Matrix (Fin m) (Fin m) ℂ :=
    fun j => X.submatrix (fun i => (i, j)) (fun i => (i, j))
  have hsum : ∀ s : Finset (Fin r), (∑ j ∈ s, blocks j).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin m) (Fin m) ℂ).PosSemidef)
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (hX.submatrix (fun i => (i, a))).add ih
  have heq : partialTraceSecondOp X = ∑ j, blocks j := by
    ext i k
    simp [partialTraceSecondOp, blocks, Matrix.submatrix, Matrix.sum_apply]
  rw [heq]
  exact hsum Finset.univ

/-- Every reduced state in the discrete Peirce-channel evolution is positive
and normalized. -/
theorem reduced_cornerEvolution_is_density {m r : ℕ}
    (P A W : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ)
    (hP : P * P = P) (hPs : star P = P) (hTrace : Matrix.trace P = 1)
    (hBound : (1 - genV P A (star A)).PosSemidef)
    (hResidual : star W * W = 1 - genV P A (star A)) (k : ℕ) :
    (partialTraceSecondOp (cornerEvolution P A W k)).PosSemidef ∧
      Matrix.trace (partialTraceSecondOp (cornerEvolution P A W k)) = 1 := by
  rcases cornerEvolution_is_density P A W hP hPs hTrace hBound hResidual k with ⟨hPos, hTr⟩
  exact ⟨partialTraceSecond_posSemidef _ hPos,
    (partialTraceSecondOp_trace _).trans hTr⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal

end
