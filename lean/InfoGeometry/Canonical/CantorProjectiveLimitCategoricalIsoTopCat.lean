import InfoGeometry.Canonical.CantorProjectiveLimitTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorProjectiveLimitFiniteReadoutTopCat
import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

/-!
# Identifying the two native prefix-limit carriers

The repository contains both a concrete coherent-family carrier and the
categorical `TopCat` limit of the finite-prefix diagram.  They are related by
the same Cantor boundary; this owner records the resulting canonical
topological isomorphism and its projection law.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimitTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitFiniteReadoutTopCat
open InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
open InfoGeometry.Canonical.CantorCylinderTopology
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

def projectiveToCategoricalLimitTopCatIso :
    TopCat.of PrefixProjectiveLimit ≅
      TopCat.of (↑(limit prefixDiagram)) :=
  cantorProjectiveLimitTopCatIso.symm.trans prefixBoundaryLimitIso

def categoricalLimitFinitePrefixReadoutTopCatHom (n : ℕ) :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of ℝ :=
    limit.π prefixDiagram (Opposite.op n) ≫
    finitePrefixReadoutTopCatHom n

def projectivePrefixExtendTopCatHom {n : ℕ} (w : BitWord n) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of PrefixProjectiveLimit :=
  cantorProjectiveLimitTopCatIso.inv ≫
    prefixExtendTopCatHom w ≫ cantorProjectiveLimitTopCatIso.hom

def projectiveReadoutTopCatHom :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of ℝ :=
  cantorProjectiveLimitTopCatIso.inv ≫ readoutTopCatHom

def projectivePrefixProjectionTopCatHom {n : ℕ} (w : BitWord n) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of (BitWord n) :=
  TopCat.ofHom
    { toFun := fun _ => w
      continuous_toFun := continuous_const }

def categoricalLimitPrefixExtendTopCatHom {n : ℕ} (w : BitWord n) :
    TopCat.of (↑(limit prefixDiagram)) ⟶
      TopCat.of (↑(limit prefixDiagram)) :=
  projectiveToCategoricalLimitTopCatIso.inv ≫
    projectivePrefixExtendTopCatHom w ≫
      projectiveToCategoricalLimitTopCatIso.hom

def categoricalLimitReadoutTopCatHom :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of ℝ :=
  projectiveToCategoricalLimitTopCatIso.inv ≫ projectiveReadoutTopCatHom

def categoricalLimitPrefixProjectionTopCatHom {n : ℕ} (w : BitWord n) :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of (BitWord n) :=
  projectiveToCategoricalLimitTopCatIso.inv ≫
    projectivePrefixProjectionTopCatHom w

theorem projectiveToCategoricalLimit_projection (n : ℕ) :
    projectiveToCategoricalLimitTopCatIso.hom ≫
        limit.π prefixDiagram (Opposite.op n) =
      projectiveProjectionTopCatHom n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  change (limit.π prefixDiagram (Opposite.op n)).hom
      (prefixBoundaryLimitIso.hom (toCantor p)) = π n p
  apply funext
  intro i
  have hproj := prefixBoundaryLimitIso_hom_apply n (toCantor p) i
  have hword := congrFun (boundaryPrefix_toCantor_eq_word p n) i
  simpa [boundaryPrefix] using hproj.trans hword

theorem projectiveToCategoricalLimit_projection_apply
    (n : ℕ) (p : PrefixProjectiveLimit) (i : Fin n) :
    (limit.π prefixDiagram (Opposite.op n)).hom
        (projectiveToCategoricalLimitTopCatIso.hom p) i =
      p.word n i := by
  have h := congrArg (fun f => f p)
    (projectiveToCategoricalLimit_projection n)
  have hi := congrFun h i
  exact hi

theorem categoricalLimitFinitePrefixReadout_projective_iso (n : ℕ) :
    projectiveToCategoricalLimitTopCatIso.hom ≫
        categoricalLimitFinitePrefixReadoutTopCatHom n =
      projectiveFinitePrefixReadoutTopCatHom n := by
  rw [categoricalLimitFinitePrefixReadoutTopCatHom,
    ← Category.assoc, projectiveToCategoricalLimit_projection]
  rfl

theorem projectivePrefixExtend_readoutTopCat_square {n : ℕ}
    (w : BitWord n) :
    projectivePrefixExtendTopCatHom w ≫ projectiveReadoutTopCatHom =
      projectiveReadoutTopCatHom ≫ finitePrefixAffineTopCatHom n w := by
  simp only [projectivePrefixExtendTopCatHom, projectiveReadoutTopCatHom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [prefixExtend_readoutTopCat_square]

theorem categoricalLimitPrefixExtend_readoutTopCat_square {n : ℕ}
    (w : BitWord n) :
    categoricalLimitPrefixExtendTopCatHom w ≫
        categoricalLimitReadoutTopCatHom =
      categoricalLimitReadoutTopCatHom ≫ finitePrefixAffineTopCatHom n w := by
  simp only [categoricalLimitPrefixExtendTopCatHom,
    categoricalLimitReadoutTopCatHom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [projectivePrefixExtend_readoutTopCat_square]

theorem projectivePrefixExtend_projectionTopCat_square {n : ℕ}
    (w : BitWord n) :
    projectivePrefixExtendTopCatHom w ≫ projectiveProjectionTopCatHom n =
      projectivePrefixProjectionTopCatHom w := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [projectivePrefixExtendTopCatHom, TopCat.comp_app,
    TopCat.comp_app]
  change projectiveProjectionTopCatHom n
      (cantorProjectiveLimitTopCatIso.hom
        (prefixExtend w (cantorProjectiveLimitTopCatIso.inv p))) = w
  rw [cantorProjectiveLimit_projection_readout]
  exact prefixExtend_mem_prefixCylinder w _

theorem categoricalLimitPrefixExtend_projectionTopCat_square {n : ℕ}
    (w : BitWord n) :
    categoricalLimitPrefixExtendTopCatHom w ≫
        limit.π prefixDiagram (Opposite.op n) =
      categoricalLimitPrefixProjectionTopCatHom w := by
  rw [categoricalLimitPrefixExtendTopCatHom,
    categoricalLimitPrefixProjectionTopCatHom]
  simp only [Category.assoc, projectiveToCategoricalLimit_projection]
  rw [projectivePrefixExtend_projectionTopCat_square]

end InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
