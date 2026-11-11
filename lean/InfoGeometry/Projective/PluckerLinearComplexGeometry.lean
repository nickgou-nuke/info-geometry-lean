/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.PluckerLinearComplex
import InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Linear complexes on the existing real projective line space

The complex form is transported to the repository's `Vec4`. Its restriction
to an actual rank-two submodule defines complex membership independently of
an ordered frame. For a simple nonzero polar representative, this membership
is exactly projective incidence with the directrix. The entire radical of
the associated form is the directrix plane.
-/

noncomputable section

namespace InfoGeometry.Projective.PluckerLinearComplexGeometry

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Projective.ExteriorKleinFrameSurjection
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
open InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence
open InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
open PluckerLinearComplex

/-- Read the existing `I4`-indexed vectors in their fixed `t,x,y,z` order. -/
def nativeCoordinates : Vec4 →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x i := x (finFourIndex i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The complex form on the existing native real four-space. -/
def nativeComplexForm (C : KleinQuadric.Plucker6 ℝ) :
    LinearMap.BilinForm ℝ Vec4 :=
  ((complexForm C).compl₂ nativeCoordinates).comp nativeCoordinates

/-- Compatibility with the existing six-coordinate Plücker incidence owner. -/
theorem nativeComplexForm_apply (C : KleinQuadric.Plucker6 ℝ) (x y : Vec4) :
    nativeComplexForm C x y =
      KleinQuadricIncidence.Plucker6.incidenceForm C (linePlucker x y) := by
  simp [nativeComplexForm, nativeCoordinates, complexForm,
    complexMatrix, InfoGeometry.Canonical.Pfaffian.skew4,
    Matrix.toBilin'_apply, Fin.sum_univ_four, finFourIndex,
    linePlucker, KleinQuadricIncidence.Plucker6.incidenceForm]
  ring

theorem nativeComplexForm_isAlt (C : KleinQuadric.Plucker6 ℝ) :
    (nativeComplexForm C).IsAlt := by
  intro x
  exact (complexForm_isAlt C).self_eq_zero (nativeCoordinates x)

/-- A complex is a set of actual two-planes, defined by restriction of the
bilinear form, rather than a chosen coordinate representative for each line. -/
def lineComplex (C : KleinQuadric.Plucker6 ℝ) : Set RealTwoPlane :=
  {P | ∀ x ∈ P.1, ∀ y ∈ P.1, nativeComplexForm C x y = 0}

/-- Testing an alternating form on the ordered basis pair tests its entire
restriction to the two-plane. -/
theorem mem_lineComplex_frameSpan_iff (C : KleinQuadric.Plucker6 ℝ)
    (uv : NondegenerateExteriorFrame) :
    frameSpan uv ∈ lineComplex C ↔
      nativeComplexForm C (uv.1 0) (uv.1 1) = 0 := by
  constructor
  · intro h
    exact h _ (Submodule.subset_span (Set.mem_range_self 0))
      _ (Submodule.subset_span (Set.mem_range_self 1))
  · intro h x hx y hy
    have hrange : Set.range uv.1 = {uv.1 0, uv.1 1} := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    change x ∈ Submodule.span ℝ (Set.range uv.1) at hx
    change y ∈ Submodule.span ℝ (Set.range uv.1) at hy
    rw [hrange, Submodule.mem_span_pair] at hx hy
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    have hswap := (nativeComplexForm_isAlt C).eq_iff.mp h
    simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      (nativeComplexForm_isAlt C).self_eq_zero, h, hswap]

/-- A special complex consists exactly of lines meeting its directrix. -/
theorem mem_lineComplex_linePlucker_iff (uv : NondegenerateExteriorFrame)
    (P : RealTwoPlane) :
    P ∈ lineComplex (linePlucker (uv.1 0) (uv.1 1)) ↔
      PlanesIncident (frameSpan uv) P := by
  obtain ⟨st, rfl⟩ := frameSpan_surjective P
  rw [mem_lineComplex_frameSpan_iff, nativeComplexForm_apply,
    ← det_rows_eq_incidence, ← top_wedge_eq_zero_iff_det_eq_zero]
  rw [← combinedFrame_eq_vec]
  exact combinedFrame_wedge_eq_zero_iff_incident uv st

/-- The determinant functional in the last argument vanishes identically
exactly for points on the directrix. -/
theorem forall_det_rows_eq_zero_iff_mem_frameSpan
    (uv : NondegenerateExteriorFrame) (x : Vec4) :
    (∀ y : Vec4, (rowsMatrix (uv.1 0) (uv.1 1) x y).det = 0) ↔
      x ∈ (frameSpan uv).1 := by
  have htuple (y : Vec4) :
      Fin.snoc (Fin.snoc uv.1 x) y = ![uv.1 0, uv.1 1, x, y] := by
    funext i
    fin_cases i <;> simp [Fin.snoc]
  constructor
  · intro hzero
    by_contra hx
    have hli3 : LinearIndependent ℝ (Fin.snoc uv.1 x) :=
      (nondegenerateExteriorFrame_linearIndependent uv).finSnoc hx
    have hdim : 3 < Module.finrank ℝ Vec4 := by
      rw [Module.finrank_pi]
      decide
    obtain ⟨y, hli4⟩ := exists_linearIndependent_snoc_of_lt_finrank hli3 hdim
    rw [htuple y] at hli4
    have hw := (top_wedge_eq_zero_iff_det_eq_zero _ _ _ _).2 (hzero y)
    exact (InfoGeometry.Canonical.exteriorPower_ιMulti_ne_zero_of_linearIndependent
      _ hli4) hw
  · intro hx y
    apply (top_wedge_eq_zero_iff_det_eq_zero _ _ _ _).1
    have hdep : ¬ LinearIndependent ℝ (Fin.snoc (Fin.snoc uv.1 x) y) := by
      intro hli4
      have hli3 := (linearIndependent_finSnoc.mp hli4).1
      exact (linearIndependent_finSnoc.mp hli3).2 hx
    have hw := (exteriorPower.ιMulti ℝ 4).map_linearDependent
      (Fin.snoc (Fin.snoc uv.1 x) y) hdep
    simpa only [htuple y] using hw

/-- The whole radical, not merely a subspace of it, is the directrix plane. -/
theorem ker_nativeComplexForm_linePlucker (uv : NondegenerateExteriorFrame) :
    LinearMap.ker (nativeComplexForm (linePlucker (uv.1 0) (uv.1 1))) =
      (frameSpan uv).1 := by
  ext x
  rw [← forall_det_rows_eq_zero_iff_mem_frameSpan]
  constructor
  · intro hx y
    rw [det_rows_eq_incidence, ← nativeComplexForm_apply]
    exact LinearMap.congr_fun hx y
  · intro hx
    apply LinearMap.ext
    intro y
    change nativeComplexForm (linePlucker (uv.1 0) (uv.1 1)) x y = 0
    rw [nativeComplexForm_apply, ← det_rows_eq_incidence]
    exact hx y

/-- A special complex has a two-dimensional radical. -/
theorem finrank_ker_nativeComplexForm_linePlucker (uv : NondegenerateExteriorFrame) :
    Module.finrank ℝ
      (LinearMap.ker (nativeComplexForm (linePlucker (uv.1 0) (uv.1 1)))) = 2 := by
  rw [ker_nativeComplexForm_linePlucker]
  exact (frameSpan uv).2

/-- On the directrix the polar covector is zero, so its kernel is the whole
four-space. This is the exceptional case in Plücker's point-plane relation. -/
theorem polar_ker_eq_top_iff_mem_directrix (uv : NondegenerateExteriorFrame) (x : Vec4) :
    LinearMap.ker (nativeComplexForm (linePlucker (uv.1 0) (uv.1 1)) x) = ⊤ ↔
      x ∈ (frameSpan uv).1 := by
  rw [LinearMap.ker_eq_top, ← ker_nativeComplexForm_linePlucker]
  rfl

/-- Every nonzero special polar representative is realized by a genuine
nondegenerate exterior frame, using the existing full Plücker converse. -/
theorem exists_frame_of_special (C : KleinQuadric.Plucker6 ℝ)
    (hC : complexMatrix C ≠ 0) (hQ : KleinQuadric.Plucker6.kleinQ C = 0) :
    ∃ uv : NondegenerateExteriorFrame, linePlucker (uv.1 0) (uv.1 1) = C := by
  let P : Bivector4 := ⟨C.p01, C.p02, C.p03, C.p12, C.p13, C.p23⟩
  have hP : kleinForm P = 0 := hQ
  obtain ⟨u, v, huv⟩ := (kleinForm_eq_zero_iff_exists_wedge P).1 hP
  have hline : linePlucker u v = C := by
    apply KleinQuadric.Plucker6.ext
    · exact congrArg Bivector4.p01 huv
    · exact congrArg Bivector4.p02 huv
    · exact congrArg Bivector4.p03 huv
    · exact congrArg Bivector4.p12 huv
    · exact congrArg Bivector4.p13 huv
    · exact congrArg Bivector4.p23 huv
  have hnonzero : exteriorPower.ιMulti ℝ 2 ![u, v] ≠ 0 := by
    intro hz
    have hpz := congrArg exteriorBivectorLinearEquiv hz
    rw [exteriorBivectorLinearEquiv_ιMulti, map_zero, huv] at hpz
    have h01 : C.p01 = 0 := congrArg Bivector4.p01 hpz
    have h02 : C.p02 = 0 := congrArg Bivector4.p02 hpz
    have h03 : C.p03 = 0 := congrArg Bivector4.p03 hpz
    have h12 : C.p12 = 0 := congrArg Bivector4.p12 hpz
    have h13 : C.p13 = 0 := congrArg Bivector4.p13 hpz
    have h23 : C.p23 = 0 := congrArg Bivector4.p23 hpz
    apply hC
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [complexMatrix, InfoGeometry.Canonical.Pfaffian.skew4,
        h01, h02, h03, h12, h13, h23]
  exact ⟨⟨![u, v], hnonzero⟩, hline⟩

/-- General special-complex classification: the nonzero discriminant-zero
case has a directrix whose plane is precisely the radical, and consists of
all lines meeting that directrix. -/
theorem special_complex_exists_directrix (C : KleinQuadric.Plucker6 ℝ)
    (hC : complexMatrix C ≠ 0) (hQ : KleinQuadric.Plucker6.kleinQ C = 0) :
    ∃ D : RealTwoPlane,
      LinearMap.ker (nativeComplexForm C) = D.1 ∧
      ∀ P : RealTwoPlane, P ∈ lineComplex C ↔ PlanesIncident D P := by
  obtain ⟨uv, hframe⟩ := exists_frame_of_special C hC hQ
  refine ⟨frameSpan uv, ?_, ?_⟩
  · rw [← hframe]
    exact ker_nativeComplexForm_linePlucker uv
  · intro P
    rw [← hframe]
    exact mem_lineComplex_linePlucker_iff uv P

/-- The radical has dimension exactly two for every nonzero special complex. -/
theorem finrank_ker_of_special (C : KleinQuadric.Plucker6 ℝ)
    (hC : complexMatrix C ≠ 0) (hQ : KleinQuadric.Plucker6.kleinQ C = 0) :
    Module.finrank ℝ (LinearMap.ker (nativeComplexForm C)) = 2 := by
  obtain ⟨D, hker, _⟩ := special_complex_exists_directrix C hC hQ
  rw [hker]
  exact D.2

end InfoGeometry.Projective.PluckerLinearComplexGeometry
