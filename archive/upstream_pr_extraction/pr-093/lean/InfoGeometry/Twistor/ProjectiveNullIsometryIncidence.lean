import InfoGeometry.Twistor.ProjectiveNullPolarIncidence
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Quadratic isometries on projective null incidence geometry

A native Mathlib `QuadraticMap.IsometryEquiv Q₁ Q₂` induces an equivalence
between the corresponding projective null spaces.  This owner proves that the
induced equivalence preserves the polar-incidence relation exactly.

This is the generic orthogonal/projective-null symmetry layer.  No particular
Spin, Pin, conformal, or Clifford realization is asserted here.
-/

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.ProjectiveNullIsometryIncidence

open InfoGeometry.Twistor
open InfoGeometry.Twistor.ProjectiveNullPolarIncidence

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- A quadratic isometry preserves the associated polar form. -/
theorem isometryEquiv_polar
    {Q : QuadraticForm K V} {R : QuadraticForm K W}
    (f : Q.IsometryEquiv R) (x y : V) :
    QuadraticMap.polar R (f x) (f y) =
      QuadraticMap.polar Q x y := by
  unfold QuadraticMap.polar
  rw [← map_add f, f.map_app, f.map_app, f.map_app]

/-- Projectivization of a native quadratic isometry. -/
def projectiveIsometryMap
    {Q : QuadraticForm K V} {R : QuadraticForm K W}
    (f : Q.IsometryEquiv R) : ℙ K V → ℙ K W :=
  Projectivization.map f.toLinearEquiv.toLinearMap
    f.toLinearEquiv.injective

@[simp] theorem projectiveIsometryMap_mk
    {Q : QuadraticForm K V} {R : QuadraticForm K W}
    (f : Q.IsometryEquiv R) (x : V) (hx : x ≠ 0) :
    projectiveIsometryMap f (Projectivization.mk K x hx) =
      Projectivization.mk K (f x) (by
        simpa using f.toLinearEquiv.injective.ne hx) := by
  rw [projectiveIsometryMap, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff K _ _ _ _).2
  exact ⟨1, by simp⟩

/-- The projectivized isometry sends null rays to null rays. -/
theorem projectiveIsometryMap_preserves_null
    {Q : QuadraticForm K V} {R : QuadraticForm K W}
    (f : Q.IsometryEquiv R) (p : ℙ K V) :
    IsNull Q p → IsNull R (projectiveIsometryMap f p) := by
  refine Projectivization.ind (p := p) ?_
  intro x hx hp
  rw [projectiveIsometryMap_mk, isNull_mk_iff]
  rw [f.map_app]
  exact (isNull_mk_iff Q x hx).mp hp

/-- Restriction of a projectivized quadratic isometry to projective null
rays. -/
def nullIsometryMap
    {Q : QuadraticForm K V} {R : QuadraticForm K W}
    (f : Q.IsometryEquiv R) : TwistorSpace Q → TwistorSpace R :=
  fun p => ⟨projectiveIsometryMap f p.1,
    projectiveIsometryMap_preserves_null f p.1 p.2⟩

/-- The projective image of a quadratic isometry preserves polar incidence
exactly, before restricting to either null locus. -/
theorem projectiveIsometryMap_preserves_polarIncident
    {Q : QuadraticForm K V} {R : QuadraticForm K W}
    (f : Q.IsometryEquiv R) (p q : ℙ K V) :
    PolarIncident R (projectiveIsometryMap f p)
        (projectiveIsometryMap f q) ↔
      PolarIncident Q p q := by
  refine Projectivization.ind (p := p) ?_
  intro x hx
  refine Projectivization.ind (p := q) ?_
  intro y hy
  rw [projectiveIsometryMap_mk, projectiveIsometryMap_mk,
    polarIncident_mk_iff, polarIncident_mk_iff]
  rw [isometryEquiv_polar]

/-- A native quadratic isometry induces an actual equivalence of its two
projective null spaces. -/
def nullIsometryEquiv
    {Q : QuadraticForm K V} {R : QuadraticForm K W}
    (f : Q.IsometryEquiv R) : TwistorSpace Q ≃ TwistorSpace R where
  toFun := nullIsometryMap f
  invFun := nullIsometryMap f.symm
  left_inv p := by
    apply Subtype.ext
    change projectiveIsometryMap f.symm
        (projectiveIsometryMap f p.1) = p.1
    refine Projectivization.ind (p := p.1) ?_
    intro x hx
    rw [projectiveIsometryMap_mk, projectiveIsometryMap_mk]
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).2
    refine ⟨1, ?_⟩
    simpa only [one_smul] using
      (f.toLinearEquiv.symm_apply_apply x).symm
  right_inv p := by
    apply Subtype.ext
    change projectiveIsometryMap f
        (projectiveIsometryMap f.symm p.1) = p.1
    refine Projectivization.ind (p := p.1) ?_
    intro x hx
    rw [projectiveIsometryMap_mk, projectiveIsometryMap_mk]
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).2
    refine ⟨1, ?_⟩
    simpa only [one_smul] using
      (f.toLinearEquiv.apply_symm_apply x).symm

/-- The induced equivalence of projective null spaces preserves their native
polar-incidence relation. -/
theorem nullIsometryEquiv_preserves_incidence
    {Q : QuadraticForm K V} {R : QuadraticForm K W}
    (f : Q.IsometryEquiv R) (p q : TwistorSpace Q) :
    NullPolarIncident R (nullIsometryEquiv f p)
        (nullIsometryEquiv f q) ↔
      NullPolarIncident Q p q := by
  exact projectiveIsometryMap_preserves_polarIncident f p.1 q.1

end InfoGeometry.Twistor.ProjectiveNullIsometryIncidence
