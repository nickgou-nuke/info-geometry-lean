/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKrein
import InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence

/-!
# Existing graph Dirac and paravector null-shell incidence

The soldering matrix of a real spacetime paravector is used as the incidence
matrix in the repository's existing rectangular graph Hodge--Dirac operator.
The theorem identifies null paravectors with nonzero zero modes supported on
the vertex summand. No second graph operator is introduced.
-/

namespace InfoGeometry.Twistor.GraphDiracParavectorShellBridge

open InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKrein
open InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence

/-- The graph Dirac action on a vertex state with zero edge component. -/
theorem graphDirac_mulVec_vertex (B : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : InfoGeometry.Twistor.PenroseIncidence.Spinor2) :
    (graphDirac B).mulVec (Sum.elim ψ (fun _ : Fin 2 => 0)) =
      Sum.elim (fun _ : Fin 2 => 0) (B.mulVec ψ) := by
  rw [graphDirac, Matrix.fromBlocks_mulVec]
  ext i
  cases i with
  | inl i => fin_cases i <;> simp
  | inr i => simp

/-- The spacetime null condition is equivalent to a nonzero graph-Dirac
zero mode lying in the vertex summand, for the existing paravector incidence
matrix. -/
theorem paravector_null_iff_vertex_supported_graphDirac_zero
    (p : InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice.Minkowski13) :
    InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence.paravectorQuadratic p = 0 ↔
      ∃ ψ : InfoGeometry.Twistor.PenroseIncidence.Spinor2, ψ ≠ 0 ∧
        (graphDirac
          (InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence.paravectorToSolderingMatrix p)).mulVec
          (Sum.elim ψ (fun _ : Fin 2 => 0)) = 0 := by
  rw [InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence.null_paravector_iff_nontrivial_kernel]
  constructor
  · rintro ⟨ψ, hψ, hker⟩
    refine ⟨ψ, hψ, ?_⟩
    rw [graphDirac_mulVec_vertex]
    funext i
    cases i with
    | inl i => rfl
    | inr i => simpa [hker]
  · rintro ⟨ψ, hψ, hD⟩
    refine ⟨ψ, hψ, ?_⟩
    rw [graphDirac_mulVec_vertex] at hD
    funext i
    have hi := congrFun hD (Sum.inr i)
    simpa using hi

end InfoGeometry.Twistor.GraphDiracParavectorShellBridge
