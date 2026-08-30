import InfoGeometry.Canonical.RealSplitOctonionAutAmbient
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Induced topology for the canonical real split-octonion automorphism carrier

The algebraic automorphism subtype is given the topology induced by its
faithful continuous Cartesian action. The ambient continuous linear
equivalence carrier is itself given the topology transported from the units
of its continuous-linear endomorphism algebra. This file records the
resulting topological group structure without asserting a manifold or Lie
group structure.
-/

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

/- The analytic carrier is induced from the existing Cartesian equivalence;
   the native algebraic operations on CZ are left unchanged. -/
noncomputable instance instTopologicalSpaceCanonicalZorn : TopologicalSpace CZ :=
  TopologicalSpace.induced cartesianZornLinearEquiv.symm.toFun inferInstance

theorem continuous_canonicalZorn_coordinates :
    Continuous (cartesianZornLinearEquiv.symm : CZ → CartesianCoordinates) :=
  continuous_induced_dom

/-- The native monoid hom from continuous linear equivalences to endomorphism
units. It supplies the ambient topology and topological-group structure. -/
noncomputable def continuousLinearEquivToUnitHom :
    (CartesianCoordinates ≃L[ℝ] CartesianCoordinates) →*
      (CartesianCoordinates →L[ℝ] CartesianCoordinates)ˣ :=
  (ContinuousLinearEquiv.unitsEquiv ℝ CartesianCoordinates).symm.toMonoidHom

noncomputable instance instTopologicalSpaceCartesianCoordinatesContinuousLinearEquiv :
    TopologicalSpace (CartesianCoordinates ≃L[ℝ] CartesianCoordinates) :=
  TopologicalSpace.induced continuousLinearEquivToUnitHom inferInstance

noncomputable instance instIsTopologicalGroupCartesianCoordinatesContinuousLinearEquiv :
    IsTopologicalGroup (CartesianCoordinates ≃L[ℝ] CartesianCoordinates) :=
  topologicalGroup_induced continuousLinearEquivToUnitHom

noncomputable instance instTopologicalSpaceRealSplitOctonionAut :
    TopologicalSpace RealSplitOctonionAut :=
  TopologicalSpace.induced realSplitOctonionAutCartesianContinuousHom inferInstance

noncomputable instance instIsTopologicalGroupRealSplitOctonionAut :
    IsTopologicalGroup RealSplitOctonionAut :=
  topologicalGroup_induced realSplitOctonionAutCartesianContinuousHom

theorem continuous_realSplitOctonionAutCartesianContinuous :
    Continuous (realSplitOctonionAutCartesianContinuous :
      RealSplitOctonionAut →
        CartesianCoordinates ≃L[ℝ] CartesianCoordinates) := by
  exact continuous_induced_dom

theorem inducing_realSplitOctonionAutCartesianContinuous :
    @Topology.IsInducing RealSplitOctonionAut
      (CartesianCoordinates ≃L[ℝ] CartesianCoordinates)
      instTopologicalSpaceRealSplitOctonionAut
      instTopologicalSpaceCartesianCoordinatesContinuousLinearEquiv
      realSplitOctonionAutCartesianContinuous := by
  exact ⟨rfl⟩

end
end InfoGeometry.Canonical
