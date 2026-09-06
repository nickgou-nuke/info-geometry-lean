import InfoGeometry.Topological.VerlindeDefectFusion

namespace InfoGeometry.Canonical.VerlindeDefectFusionCapstone

open InfoGeometry.Topological.VerlindeDefectFusion

theorem verlinde_defect_fusion_canonical_capstone
    (p q γ : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (verlindeSMatrix2 * verlindeSMatrix2.transpose = 1) ∧
    (totalQuantumDimensionSq = 2) ∧
    (‖primeDefectLineAction p γ‖ = 1) ∧
    (primeDefectFusion p q γ = primeDefectLineAction (p * q) γ) ∧
    (primeDefectLineAction p γ * primeDefectLineAction q γ -
      primeDefectLineAction q γ * primeDefectLineAction p γ = 0) := by
  exact ⟨verlinde_S_matrix_unitary, total_quantum_dimension_eval,
    prime_defect_line_unitary p γ, prime_defect_fusion_match p q γ hp hq,
    prime_defect_commutation p q γ⟩

end InfoGeometry.Canonical.VerlindeDefectFusionCapstone
