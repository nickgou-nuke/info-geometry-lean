import InfoGeometry.External.Automath.Omega.Conclusion.ScalekernelTreeFourthOrderSynchronization

namespace Omega.Conclusion

/-- Numerical acceleration changes coefficients, windows, or costs, represented by the explicit
scale-kernel formulas from the synchronization theorem. -/
def conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_data.numericalAccelerationChangesOnlyMagnitude
    (_D : conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_data) : Prop :=
  (∀ Δ : ℝ,
      conclusion_scalekernel_tree_fourth_order_synchronization_kernel Δ =
        Δ / (2 * Real.sinh (Δ / 2))) ∧
    ∀ ρ : ℝ,
      conclusion_scalekernel_tree_fourth_order_synchronization_local_loop_defect ρ =
        -Real.log (1 - ρ ^ 2)

/-- The synchronized scalar and geometric structural orders remain fixed at four. -/
def conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_data.structuralOrderRemainsFour
    (_D : conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_data) : Prop :=
  conclusion_scalekernel_tree_fourth_order_synchronization_scalar_order = 4 ∧
    conclusion_scalekernel_tree_fourth_order_synchronization_geometric_order = 4 ∧
    conclusion_scalekernel_tree_fourth_order_synchronization_scalar_order =
      conclusion_scalekernel_tree_fourth_order_synchronization_geometric_order

/-- Concrete arithmetic witness for the orthogonality wrapper. -/
def conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_certificate : Prop :=
  conclusion_scalekernel_tree_fourth_order_synchronization_scalar_order = 4 ∧
    conclusion_scalekernel_tree_fourth_order_synchronization_geometric_order = 4 ∧
    conclusion_scalekernel_tree_fourth_order_synchronization_scalar_order =
      conclusion_scalekernel_tree_fourth_order_synchronization_geometric_order

/-- Concrete singleton data for the conclusion-level orthogonality wrapper. -/
structure conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_data where
  marker : conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_certificate := by
    rcases paper_conclusion_scalekernel_tree_fourth_order_synchronization with
      ⟨hScalar, hGeometric, hSync, _, _⟩
    exact ⟨hScalar, hGeometric, hSync⟩

/-- Paper label: `cor:conclusion-scalekernel-tree-numerics-vs-structure-orthogonality`. -/
theorem paper_conclusion_scalekernel_tree_numerics_vs_structure_orthogonality
    (D : conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_data) :
    (conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_data.numericalAccelerationChangesOnlyMagnitude D) ∧
    (conclusion_scalekernel_tree_numerics_vs_structure_orthogonality_data.structuralOrderRemainsFour D) := by
  rcases paper_conclusion_scalekernel_tree_fourth_order_synchronization with
    ⟨hScalar, hGeometric, hSync, hKernel, hLoop⟩
  exact ⟨⟨hKernel, hLoop⟩, hScalar, hGeometric, hSync⟩

end Omega.Conclusion
