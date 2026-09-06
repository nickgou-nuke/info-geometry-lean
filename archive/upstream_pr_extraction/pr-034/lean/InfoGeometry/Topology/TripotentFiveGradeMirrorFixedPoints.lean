import InfoGeometry.Topology.TripotentFiveGradeMirrorTopological
import InfoGeometry.Topology.SymbolicLatentInvolutionFixedPointsCompHaus

/-!
# Fixed points of the five-grade mirror

The finite mirror fixes exactly the zero grade.  This owner connects that
finite symbolic fact to the generic closed-fixed-point and `CompHaus`
packaging owners.
-/

namespace InfoGeometry.Topology.TripotentFiveGradeMirrorFixedPoints

open InfoGeometry.Physics.Algebra
open InfoGeometry.Topology
open InfoGeometry.Topology.TripotentFiveGradeMirrorTopological

noncomputable section

local instance : TopologicalSpace FiveGrade := ⊥
local instance : DiscreteTopology FiveGrade := discreteTopology_bot FiveGrade
local instance : CompactSpace FiveGrade := by infer_instance

def fiveGradeMirrorInvolution : SymbolicLatentInvolution FiveGrade where
  toFun := fiveGradeMirror
  continuous_toFun := continuous_of_discreteTopology
  involutive := fiveGradeMirror_involutive

@[simp] theorem fiveGradeMirrorInvolution_apply (k : FiveGrade) :
    fiveGradeMirrorInvolution k = fiveGradeMirror k := rfl

theorem fiveGradeMirror_fixed_iff (k : FiveGrade) :
    fiveGradeMirrorInvolution k = k ↔ k = FiveGrade.zero := by
  cases k <;> simp [fiveGradeMirrorInvolution, fiveGradeMirror] <;> decide

theorem fiveGradeMirror_fixedPointSet_eq :
    symbolicLatentInvolutionFixedPointSet fiveGradeMirrorInvolution =
      ({FiveGrade.zero} : Set FiveGrade) := by
  ext k
  rw [mem_symbolicLatentInvolutionFixedPointSet]
  simpa only [Set.mem_singleton_iff] using fiveGradeMirror_fixed_iff k

noncomputable def fiveGradeMirrorFixedPointCompHaus : CompHaus :=
  symbolicLatentInvolutionFixedPointCompHaus fiveGradeMirrorInvolution

theorem fiveGradeMirrorFixedPointCompHaus_carrier_eq_singleton :
    (fiveGradeMirrorFixedPointCompHaus : Type) =
      symbolicLatentInvolutionFixedPointSet fiveGradeMirrorInvolution := rfl

end
end InfoGeometry.Topology.TripotentFiveGradeMirrorFixedPoints
