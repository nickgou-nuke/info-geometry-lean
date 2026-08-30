import InfoGeometry.Canonical.RealSplitOctonionAutAmbient
import InfoGeometry.Algebra.Zorn.G2TrifactorSU3
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
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

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

private theorem continuous_canonicalZorn_dot :
    Continuous (fun p : CZ × CZ =>
      InfoGeometry.Canonical.ZornMatrix.dot p.1.x p.2.y) := by
  have hx : Continuous (fun p : CZ × CZ => p.1.x) :=
    continuous_canonicalZorn_x.comp continuous_fst
  have hy : Continuous (fun p : CZ × CZ => p.2.y) :=
    continuous_canonicalZorn_y.comp continuous_snd
  change Continuous (fun p : CZ × CZ =>
    p.1.x 0 * p.2.y 0 + p.1.x 1 * p.2.y 1 + p.1.x 2 * p.2.y 2)
  simpa [Function.comp_apply, Pi.add_apply, Pi.mul_apply] using
    ((((continuous_apply 0).comp hx).mul ((continuous_apply 0).comp hy)).add
      (((continuous_apply 1).comp hx).mul ((continuous_apply 1).comp hy))).add
      (((continuous_apply 2).comp hx).mul ((continuous_apply 2).comp hy))

private theorem continuous_canonicalZorn_dot' :
    Continuous (fun p : CZ × CZ =>
      InfoGeometry.Canonical.ZornMatrix.dot p.1.y p.2.x) := by
  have hy : Continuous (fun p : CZ × CZ => p.1.y) :=
    continuous_canonicalZorn_y.comp continuous_fst
  have hx : Continuous (fun p : CZ × CZ => p.2.x) :=
    continuous_canonicalZorn_x.comp continuous_snd
  change Continuous (fun p : CZ × CZ =>
    p.1.y 0 * p.2.x 0 + p.1.y 1 * p.2.x 1 + p.1.y 2 * p.2.x 2)
  simpa [Function.comp_apply, Pi.add_apply, Pi.mul_apply] using
    ((((continuous_apply 0).comp hy).mul ((continuous_apply 0).comp hx)).add
      (((continuous_apply 1).comp hy).mul ((continuous_apply 1).comp hx))).add
      (((continuous_apply 2).comp hy).mul ((continuous_apply 2).comp hx))

private theorem continuous_canonicalZorn_cross :
    Continuous (fun p : CZ × CZ =>
      InfoGeometry.Canonical.ZornMatrix.cross p.1.y p.2.y) := by
  apply continuous_pi
  intro i
  have hy : Continuous (fun p : CZ × CZ => p.1.y) :=
    continuous_canonicalZorn_y.comp continuous_fst
  have hz : Continuous (fun p : CZ × CZ => p.2.y) :=
    continuous_canonicalZorn_y.comp continuous_snd
  fin_cases i
  · change Continuous (fun p : CZ × CZ =>
      p.1.y 1 * p.2.y 2 - p.1.y 2 * p.2.y 1)
    exact ((continuous_apply 1).comp hy).mul ((continuous_apply 2).comp hz) |>.sub
      (((continuous_apply 2).comp hy).mul ((continuous_apply 1).comp hz))
  · change Continuous (fun p : CZ × CZ =>
      p.1.y 2 * p.2.y 0 - p.1.y 0 * p.2.y 2)
    exact ((continuous_apply 2).comp hy).mul ((continuous_apply 0).comp hz) |>.sub
      (((continuous_apply 0).comp hy).mul ((continuous_apply 2).comp hz))
  · change Continuous (fun p : CZ × CZ =>
      p.1.y 0 * p.2.y 1 - p.1.y 1 * p.2.y 0)
    exact ((continuous_apply 0).comp hy).mul ((continuous_apply 1).comp hz) |>.sub
      (((continuous_apply 1).comp hy).mul ((continuous_apply 0).comp hz))

private theorem continuous_canonicalZorn_cross' :
    Continuous (fun p : CZ × CZ =>
      InfoGeometry.Canonical.ZornMatrix.cross p.1.x p.2.x) := by
  apply continuous_pi
  intro i
  have hx : Continuous (fun p : CZ × CZ => p.1.x) :=
    continuous_canonicalZorn_x.comp continuous_fst
  have hz : Continuous (fun p : CZ × CZ => p.2.x) :=
    continuous_canonicalZorn_x.comp continuous_snd
  fin_cases i
  · change Continuous (fun p : CZ × CZ =>
      p.1.x 1 * p.2.x 2 - p.1.x 2 * p.2.x 1)
    exact ((continuous_apply 1).comp hx).mul ((continuous_apply 2).comp hz) |>.sub
      (((continuous_apply 2).comp hx).mul ((continuous_apply 1).comp hz))
  · change Continuous (fun p : CZ × CZ =>
      p.1.x 2 * p.2.x 0 - p.1.x 0 * p.2.x 2)
    exact ((continuous_apply 2).comp hx).mul ((continuous_apply 0).comp hz) |>.sub
      (((continuous_apply 0).comp hx).mul ((continuous_apply 2).comp hz))
  · change Continuous (fun p : CZ × CZ =>
      p.1.x 0 * p.2.x 1 - p.1.x 1 * p.2.x 0)
    exact ((continuous_apply 0).comp hx).mul ((continuous_apply 1).comp hz) |>.sub
      (((continuous_apply 1).comp hx).mul ((continuous_apply 0).comp hz))

theorem continuous_zMul_a :
    Continuous (fun p : CZ × CZ => (zMul p.1 p.2).a) := by
  change Continuous (fun p : CZ × CZ =>
    p.1.a * p.2.a +
      InfoGeometry.Canonical.ZornMatrix.dot p.1.x p.2.y)
  exact (continuous_canonicalZorn_a.comp continuous_fst).mul
      (continuous_canonicalZorn_a.comp continuous_snd) |>.add
    continuous_canonicalZorn_dot

theorem continuous_zMul_b :
    Continuous (fun p : CZ × CZ => (zMul p.1 p.2).b) := by
  change Continuous (fun p : CZ × CZ =>
    p.1.b * p.2.b +
      InfoGeometry.Canonical.ZornMatrix.dot p.1.y p.2.x)
  exact (continuous_canonicalZorn_b.comp continuous_fst).mul
      (continuous_canonicalZorn_b.comp continuous_snd) |>.add
    continuous_canonicalZorn_dot'

theorem continuous_zMul_x :
    Continuous (fun p : CZ × CZ => (zMul p.1 p.2).x) := by
  have h₁ : Continuous (fun p : CZ × CZ => p.1.a • p.2.x) :=
    (continuous_canonicalZorn_a.comp continuous_fst).smul
      (continuous_canonicalZorn_x.comp continuous_snd)
  have h₂ : Continuous (fun p : CZ × CZ => p.2.b • p.1.x) :=
    (continuous_canonicalZorn_b.comp continuous_snd).smul
      (continuous_canonicalZorn_x.comp continuous_fst)
  change Continuous (fun p : CZ × CZ =>
    p.1.a • p.2.x + p.2.b • p.1.x -
      InfoGeometry.Canonical.ZornMatrix.cross p.1.y p.2.y)
  exact (h₁.add h₂).sub continuous_canonicalZorn_cross

theorem continuous_zMul_y :
    Continuous (fun p : CZ × CZ => (zMul p.1 p.2).y) := by
  have h₁ : Continuous (fun p : CZ × CZ => p.1.b • p.2.y) :=
    (continuous_canonicalZorn_b.comp continuous_fst).smul
      (continuous_canonicalZorn_y.comp continuous_snd)
  have h₂ : Continuous (fun p : CZ × CZ => p.2.a • p.1.y) :=
    (continuous_canonicalZorn_a.comp continuous_snd).smul
      (continuous_canonicalZorn_y.comp continuous_fst)
  change Continuous (fun p : CZ × CZ =>
    p.1.b • p.2.y + p.2.a • p.1.y +
      InfoGeometry.Canonical.ZornMatrix.cross p.1.x p.2.x)
  exact (h₁.add h₂).add continuous_canonicalZorn_cross'

theorem continuous_zMul :
    Continuous (fun p : CZ × CZ => zMul p.1 p.2) := by
  apply continuous_induced_rng.mpr
  have ha : Continuous (fun p : CZ × CZ => (zMul p.1 p.2).a) :=
    continuous_zMul_a
  have hb : Continuous (fun p : CZ × CZ => (zMul p.1 p.2).b) :=
    continuous_zMul_b
  have hx : Continuous (fun p : CZ × CZ => (zMul p.1 p.2).x) :=
    continuous_zMul_x
  have hy : Continuous (fun p : CZ × CZ => (zMul p.1 p.2).y) :=
    continuous_zMul_y
  have hq₀ : Continuous (fun p : CZ × CZ =>
      ((zMul p.1 p.2).a + (zMul p.1 p.2).b) / (2 : ℝ)) :=
    (ha.add hb).div_const 2
  have hr₀ : Continuous (fun p : CZ × CZ =>
      ((zMul p.1 p.2).a - (zMul p.1 p.2).b) / (2 : ℝ)) :=
    (ha.sub hb).div_const 2
  have hq : Continuous (fun p : CZ × CZ =>
      fun i => ((zMul p.1 p.2).x i - (zMul p.1 p.2).y i) / (2 : ℝ)) := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp (hx.sub hy)).div_const (2 : ℝ)
  have hr : Continuous (fun p : CZ × CZ =>
      fun i => ((zMul p.1 p.2).x i + (zMul p.1 p.2).y i) / (2 : ℝ)) := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp (hx.add hy)).div_const (2 : ℝ)
  change Continuous (fun p : CZ × CZ =>
    ((((zMul p.1 p.2).a + (zMul p.1 p.2).b) / (2 : ℝ),
        fun i => ((zMul p.1 p.2).x i - (zMul p.1 p.2).y i) / (2 : ℝ)),
      (((zMul p.1 p.2).a - (zMul p.1 p.2).b) / (2 : ℝ),
        fun i => ((zMul p.1 p.2).x i + (zMul p.1 p.2).y i) / (2 : ℝ))))
  exact (hq₀.prodMk hq).prodMk (hr₀.prodMk hr)

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
