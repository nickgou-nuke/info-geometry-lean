import InfoGeometry.Lie.SplitOctonionAxialKleinBridge
import InfoGeometry.Projective.ExteriorKleinProjective

/-!
# Projective active-Zorn/Klein bridge

The native active-sector/exterior linear equivalence descends through
Mathlib's projectivization.  Its null readout is exactly the native Zorn
determinant equation.  No Grassmannian equivalence is asserted here.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitOctonionAxialKleinProjective

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Lie.SplitOctonionAxialKleinBridge
open InfoGeometry.Lie.SplitOctonionAxialWittReduction
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

abbrev ActiveProjective := ℙ ℝ ActiveSector
abbrev ExteriorProjective := ℙ ℝ ExteriorSquare

/-- Projectivization of the concrete active-Zorn/exterior linear equivalence. -/
def activeExteriorProjectiveMap : ActiveProjective → ExteriorProjective :=
  Projectivization.map activeExteriorLinearEquiv.toLinearMap
    activeExteriorLinearEquiv.injective

/-- The inverse projective map induced by the inverse linear equivalence. -/
def exteriorActiveProjectiveMap : ExteriorProjective → ActiveProjective :=
  Projectivization.map activeExteriorLinearEquiv.symm.toLinearMap
    activeExteriorLinearEquiv.symm.injective

@[simp] theorem exteriorActiveProjectiveMap_activeExteriorProjectiveMap
    (p : ActiveProjective) :
    exteriorActiveProjectiveMap (activeExteriorProjectiveMap p) = p := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  rw [activeExteriorProjectiveMap, exteriorActiveProjectiveMap,
    Projectivization.map_mk, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨1, by simp⟩

@[simp] theorem activeExteriorProjectiveMap_exteriorActiveProjectiveMap
    (p : ExteriorProjective) :
    activeExteriorProjectiveMap (exteriorActiveProjectiveMap p) = p := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  rw [activeExteriorProjectiveMap, exteriorActiveProjectiveMap,
    Projectivization.map_mk, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨1, by simp⟩

/-- The affine linear equivalence induces an actual equivalence of projective
spaces, before restricting to either null locus. -/
def activeExteriorProjectiveEquiv : ActiveProjective ≃ ExteriorProjective where
  toFun := activeExteriorProjectiveMap
  invFun := exteriorActiveProjectiveMap
  left_inv := exteriorActiveProjectiveMap_activeExteriorProjectiveMap
  right_inv := activeExteriorProjectiveMap_exteriorActiveProjectiveMap

abbrev ActiveKleinNullProjective :=
  {p : ActiveProjective //
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
      (activeExteriorProjectiveMap p)}

abbrev ExteriorKleinNullProjective :=
  {p : ExteriorProjective //
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein p}

/-- The projective equivalence restricts to an equivalence of the two Klein
null loci.  This is the projectivized active-Zorn null-cone theorem; no
Grassmannian quotient is added here. -/
def activeExteriorProjectiveNullEquiv :
    ActiveKleinNullProjective ≃ ExteriorKleinNullProjective where
  toFun p := ⟨activeExteriorProjectiveMap p.1, p.2⟩
  invFun q := ⟨exteriorActiveProjectiveMap q.1, by
    simpa using q.2⟩
  left_inv p := by
    apply Subtype.ext
    exact exteriorActiveProjectiveMap_activeExteriorProjectiveMap p.1
  right_inv q := by
    apply Subtype.ext
    exact activeExteriorProjectiveMap_exteriorActiveProjectiveMap q.1

theorem activeExteriorProjectiveNullEquiv_target_isDecomposable
    (p : ActiveKleinNullProjective) :
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsDecomposable
      (activeExteriorProjectiveNullEquiv p).1 := by
  rw [← _root_.InfoGeometry.Projective.ExteriorKleinProjective.isKlein_iff_isDecomposable]
  exact p.2

/-- A nonzero active Zorn representative lands on the projective Klein locus
exactly when its native Zorn determinant vanishes. -/
theorem isKlein_activeExteriorProjectiveMap_mk_iff
    (X : ActiveSector) (hX : X ≠ 0) :
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
        (activeExteriorProjectiveMap
          (Projectivization.mk ℝ X hX)) ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 = 0 := by
  rw [activeExteriorProjectiveMap, Projectivization.map_mk,
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.isKlein_mk_iff]
  change exteriorKleinForm (activeExteriorLinearEquiv X) = 0 ↔ _
  rw [exteriorKleinForm_activeExterior]

/-- The same active projective ray is Klein-null exactly when its exterior
representative is projectively decomposable. -/
theorem isDecomposable_activeExteriorProjectiveMap_mk_iff
    (X : ActiveSector) (hX : X ≠ 0) :
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsDecomposable
        (activeExteriorProjectiveMap
          (Projectivization.mk ℝ X hX)) ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 = 0 := by
  rw [← _root_.InfoGeometry.Projective.ExteriorKleinProjective.isKlein_iff_isDecomposable]
  exact isKlein_activeExteriorProjectiveMap_mk_iff X hX

end InfoGeometry.Lie.SplitOctonionAxialKleinProjective
