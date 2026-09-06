import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosureTopCat
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowComposition
import InfoGeometry.Topology.TripotentFiveGradeCoordinateModularFlow

namespace InfoGeometry.Topology.TripotentFiveGradeCoordinateOrbitClosure

open InfoGeometry.Topology
open InfoGeometry.Physics.Algebra
open InfoGeometry.Topology.TripotentFiveGradeMirrorTopological
open InfoGeometry.Topology.TripotentFiveGradeCoordinateModularFlow
open CategoryTheory

noncomputable section

abbrev coordinateOrbitClosure (f : FiveGrade → ℝ) :=
  closure (fiveGradeCoordinateModularFlow.orbit f)

theorem mem_coordinateMirrorFixedPointSet_iff (f : FiveGrade → ℝ) :
    f ∈ symbolicLatentInvolutionFixedPointSet
        fiveGradeCoordinateMirrorInvolution ↔
      coordinateMirror f = f :=
  Iff.rfl

theorem coordinateMirror_fixedPoint_iff (f : FiveGrade → ℝ) :
    coordinateMirror f = f ↔
      ∀ k : FiveGrade, f (fiveGradeMirror k) = f k := by
  constructor
  · intro h k
    exact congrFun h k
  · intro h
    funext k
    exact h k

noncomputable def coordinateFixedOrbitClosureMirrorTopCatHom
    (f : FiveGrade → ℝ)
    (hf : coordinateMirror f = f) :
    TopCat.of (coordinateOrbitClosure f) ⟶
      TopCat.of (coordinateOrbitClosure f) :=
  fiveGradeCoordinateModularReversal.fixedPointOrbitClosureTopCatHom f hf

theorem coordinateFixedOrbitClosureMirrorTopCatHom_forget_apply
    (f : FiveGrade → ℝ)
    (hf : coordinateMirror f = f)
    (z : coordinateOrbitClosure f) :
    (coordinateFixedOrbitClosureMirrorTopCatHom f hf).hom z =
      ⟨coordinateMirror z.1, by
        change coordinateMirror z.1 ∈ closure
          (fiveGradeCoordinateModularFlow.orbit f)
        let hInv :=
          fiveGradeCoordinateModularReversal.fixedPoint_orbitClosure_invariant
            f hf
        have hz : coordinateMirror z.1 ∈
            coordinateMirror '' closure
              (fiveGradeCoordinateModularFlow.orbit f) :=
          ⟨z.1, z.2, rfl⟩
        have hInv' : coordinateMirror '' closure
              (fiveGradeCoordinateModularFlow.orbit f) =
            closure (fiveGradeCoordinateModularFlow.orbit f) := by
          simpa [fiveGradeCoordinateMirrorInvolution] using hInv
        rw [hInv'] at hz
        exact hz⟩ := by
  rfl

theorem coordinateOrbitClosureFlow_zero_apply
    (f : FiveGrade → ℝ) (z : coordinateOrbitClosure f) :
    (fiveGradeCoordinateModularFlow.orbitClosureFlowTopCatHom
      0 f z).1 = z.1 := by
  exact fiveGradeCoordinateModularFlow.orbitClosureFlowTopCatHom_zero_apply f z

theorem coordinateOrbitClosureFlow_trans_apply
    (f : FiveGrade → ℝ) (t s : ℝ)
    (z : coordinateOrbitClosure f) :
    (fiveGradeCoordinateModularFlow.orbitClosureFlowTopCatHom
      (t + s) f z).1 =
      ((fiveGradeCoordinateModularFlow.orbitClosureFlowTopCatHom t f ≫
        fiveGradeCoordinateModularFlow.orbitClosureFlowTopCatHom s
          (fiveGradeCoordinateModularFlow.act t f)) z).1 := by
  exact fiveGradeCoordinateModularFlow.orbitClosureFlowTopCatHom_trans_apply
    f t s z

end
end InfoGeometry.Topology.TripotentFiveGradeCoordinateOrbitClosure
