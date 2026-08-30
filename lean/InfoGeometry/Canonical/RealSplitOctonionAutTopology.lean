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

theorem continuous_canonicalZorn_a : Continuous (fun X : CZ => X.a) := by
  have hq₀ : Continuous (fun X : CZ => (cartesianZornLinearEquiv.symm X).1.1) :=
    continuous_fst.comp (continuous_fst.comp continuous_canonicalZorn_coordinates)
  have hr₀ : Continuous (fun X : CZ => (cartesianZornLinearEquiv.symm X).2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_canonicalZorn_coordinates)
  rw [show (fun X : CZ => X.a) =
      (fun X => (cartesianZornLinearEquiv.symm X).1.1 +
        (cartesianZornLinearEquiv.symm X).2.1) by
    funext X
    simp [cartesianZornLinearEquiv_symm_apply]
    ring]
  exact hq₀.add hr₀

theorem continuous_canonicalZorn_b : Continuous (fun X : CZ => X.b) := by
  have hq₀ : Continuous (fun X : CZ => (cartesianZornLinearEquiv.symm X).1.1) :=
    continuous_fst.comp (continuous_fst.comp continuous_canonicalZorn_coordinates)
  have hr₀ : Continuous (fun X : CZ => (cartesianZornLinearEquiv.symm X).2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_canonicalZorn_coordinates)
  rw [show (fun X : CZ => X.b) =
      (fun X => (cartesianZornLinearEquiv.symm X).1.1 -
        (cartesianZornLinearEquiv.symm X).2.1) by
    funext X
    simp [cartesianZornLinearEquiv_symm_apply]
    ring]
  exact hq₀.sub hr₀

theorem continuous_canonicalZorn_x :
    Continuous (fun X : CZ => X.x) := by
  have hq : Continuous (fun X : CZ => (cartesianZornLinearEquiv.symm X).1.2) :=
    continuous_snd.comp (continuous_fst.comp continuous_canonicalZorn_coordinates)
  have hr : Continuous (fun X : CZ => (cartesianZornLinearEquiv.symm X).2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_canonicalZorn_coordinates)
  rw [show (fun X : CZ => X.x) =
      (fun X => (cartesianZornLinearEquiv.symm X).1.2 +
        (cartesianZornLinearEquiv.symm X).2.2) by
    funext X
    simp only [cartesianZornLinearEquiv_symm_apply]
    ext i
    change X.x i = (X.x i - X.y i) / 2 + (X.x i + X.y i) / 2
    ring]
  exact continuous_pi fun i => (continuous_apply i).comp (hq.add hr)

theorem continuous_canonicalZorn_y :
    Continuous (fun X : CZ => X.y) := by
  have hq : Continuous (fun X : CZ => (cartesianZornLinearEquiv.symm X).1.2) :=
    continuous_snd.comp (continuous_fst.comp continuous_canonicalZorn_coordinates)
  have hr : Continuous (fun X : CZ => (cartesianZornLinearEquiv.symm X).2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_canonicalZorn_coordinates)
  rw [show (fun X : CZ => X.y) =
      (fun X => (cartesianZornLinearEquiv.symm X).2.2 -
        (cartesianZornLinearEquiv.symm X).1.2) by
    funext X
    simp only [cartesianZornLinearEquiv_symm_apply]
    ext i
    change X.y i = (X.x i + X.y i) / 2 - (X.x i - X.y i) / 2
    ring]
  exact continuous_pi fun i => (continuous_apply i).comp (hr.sub hq)

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
