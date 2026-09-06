import InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

namespace InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

noncomputable section

universe u

variable {A : Type u} [TopologicalSpace A]

/-!
# Recursive topology of the native inverse-limit boundary

The inverse-limit owner already supplies the head/tail decomposition of an
infinite word.  This bridge upgrades that algebraic decomposition to the
native `Homeomorph` API: the boundary is homeomorphic to one alphabet symbol
followed by another boundary.
-/

noncomputable def boundaryConsHomeomorph :
    A × Boundary (A := A) ≃ₜ Boundary (A := A) where
  toFun p := boundaryCons p.1 p.2
  invFun x := (boundaryHead x, boundaryTail x)
  left_inv p := by
    ext <;> simp [boundaryHead, boundaryTail, boundaryCons]
  right_inv x := boundary_recursive_decomposition x
  continuous_toFun := by
    apply continuous_pi
    intro n
    cases n with
    | zero => exact continuous_fst
    | succ n => exact (continuous_apply n).comp continuous_snd
  continuous_invFun := continuous_boundaryHead.prodMk continuous_boundaryTail

theorem boundaryConsHomeomorph_apply
    (p : A × Boundary (A := A)) :
    boundaryConsHomeomorph p = boundaryCons p.1 p.2 := by
  change boundaryCons p.1 p.2 = boundaryCons p.1 p.2
  rfl

theorem boundaryConsHomeomorph_symm_apply
    (x : Boundary (A := A)) :
    boundaryConsHomeomorph.symm x = (boundaryHead x, boundaryTail x) := by
  change (boundaryHead x, boundaryTail x) = (boundaryHead x, boundaryTail x)
  rfl

end

end InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
