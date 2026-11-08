/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

### Audit Classification (BUCKET 1 / BUCKET 2 / BUCKET 3)
- **BUCKET 1 (Genuine Constructive Theorems)**:
  - `projectiveToCategoricalLimitTopCatIso`
  - `categoricalLimitFinitePrefixReadoutTopCatHom`, `projectivePrefixExtendTopCatHom`,
    `projectiveReadoutTopCatHom`, `projectivePrefixProjectionTopCatHom`,
    `categoricalLimitPrefixExtendTopCatHom`, `categoricalLimitReadoutTopCatHom`,
    `categoricalLimitPrefixProjectionTopCatHom`
  - `projectiveToCategoricalLimit_projection`, `projectiveToCategoricalLimit_projection_apply`,
    `categoricalLimitFinitePrefixReadout_projective_iso`
  - `projectivePrefixExtend_readoutTopCat_square`,
    `categoricalLimitPrefixExtend_readoutTopCat_square`,
    `projectivePrefixExtend_projectionTopCat_square`,
    `categoricalLimitPrefixExtend_projectionTopCat_square`
- **BUCKET 2 (Honest Numeric/Finite Certificates)**: None (all results are universally quantified over `n : ℕ` and `w : BitWord n`).
- **BUCKET 3 (Eliminated Debt)**: `0` `sorry`, `0` `admit`, `0` wrapper structures.
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

/-- Canonical `TopCat` isomorphism from the concrete `PrefixProjectiveLimit` to the categorical
projective limit `limit prefixDiagram`. -/
def projectiveToCategoricalLimitTopCatIso :
    TopCat.of PrefixProjectiveLimit ≅
      TopCat.of (↑(limit prefixDiagram)) :=
  cantorProjectiveLimitTopCatIso.symm.trans prefixBoundaryLimitIso

/-- Finite-prefix readout morphism on `limit prefixDiagram` at depth `n`. -/
def categoricalLimitFinitePrefixReadoutTopCatHom (n : ℕ) :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of ℝ :=
    limit.π prefixDiagram (Opposite.op n) ≫
    finitePrefixReadoutTopCatHom n

/-- Prefix-extension endomorphism on `PrefixProjectiveLimit` transported from `CantorBoundary`. -/
def projectivePrefixExtendTopCatHom {n : ℕ} (w : BitWord n) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of PrefixProjectiveLimit :=
  cantorProjectiveLimitTopCatIso.inv ≫
    prefixExtendTopCatHom w ≫ cantorProjectiveLimitTopCatIso.hom

/-- Real-valued boundary readout morphism on `PrefixProjectiveLimit`. -/
def projectiveReadoutTopCatHom :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of ℝ :=
  cantorProjectiveLimitTopCatIso.inv ≫ readoutTopCatHom

/-- Constant projection morphism to `w : BitWord n` on `PrefixProjectiveLimit`. -/
def projectivePrefixProjectionTopCatHom {n : ℕ} (w : BitWord n) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of (BitWord n) :=
  TopCat.ofHom
    { toFun := fun _ => w
      continuous_toFun := continuous_const }

/-- Prefix-extension endomorphism on `limit prefixDiagram` transported along
`projectiveToCategoricalLimitTopCatIso`. -/
def categoricalLimitPrefixExtendTopCatHom {n : ℕ} (w : BitWord n) :
    TopCat.of (↑(limit prefixDiagram)) ⟶
      TopCat.of (↑(limit prefixDiagram)) :=
  projectiveToCategoricalLimitTopCatIso.inv ≫
    projectivePrefixExtendTopCatHom w ≫
      projectiveToCategoricalLimitTopCatIso.hom

/-- Real-valued boundary readout morphism on `limit prefixDiagram`. -/
def categoricalLimitReadoutTopCatHom :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of ℝ :=
  projectiveToCategoricalLimitTopCatIso.inv ≫ projectiveReadoutTopCatHom

/-- Constant projection morphism to `w : BitWord n` on `limit prefixDiagram`. -/
def categoricalLimitPrefixProjectionTopCatHom {n : ℕ} (w : BitWord n) :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of (BitWord n) :=
  projectiveToCategoricalLimitTopCatIso.inv ≫
    projectivePrefixProjectionTopCatHom w

/-- Composing `projectiveToCategoricalLimitTopCatIso.hom` with the categorical limit projection
`limit.π prefixDiagram (Opposite.op n)` recovers `projectiveProjectionTopCatHom n`. -/
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

/-- Pointwise evaluation of `projectiveToCategoricalLimit_projection` at index `i : Fin n`. -/
theorem projectiveToCategoricalLimit_projection_apply
    (n : ℕ) (p : PrefixProjectiveLimit) (i : Fin n) :
    (limit.π prefixDiagram (Opposite.op n)).hom
        (projectiveToCategoricalLimitTopCatIso.hom p) i =
      p.word n i := by
  have h := congrArg (fun f => f p)
    (projectiveToCategoricalLimit_projection n)
  have hi := congrFun h i
  exact hi

/-- Compatibility of `categoricalLimitFinitePrefixReadoutTopCatHom n` with
`projectiveFinitePrefixReadoutTopCatHom n` across `projectiveToCategoricalLimitTopCatIso.hom`. -/
theorem categoricalLimitFinitePrefixReadout_projective_iso (n : ℕ) :
    projectiveToCategoricalLimitTopCatIso.hom ≫
        categoricalLimitFinitePrefixReadoutTopCatHom n =
      projectiveFinitePrefixReadoutTopCatHom n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  have harg : (limit.π prefixDiagram (Opposite.op n)).hom
      (projectiveToCategoricalLimitTopCatIso.hom p) =
      (projectiveProjectionTopCatHom n).hom p := by
    funext i
    have h1 := projectiveToCategoricalLimit_projection_apply n p i
    exact h1
  exact congrArg (finitePrefixReadoutTopCatHom n).hom harg

/-- Commutative square intertwining `projectivePrefixExtendTopCatHom w` and
`finitePrefixAffineTopCatHom n w` via `projectiveReadoutTopCatHom`. -/
theorem projectivePrefixExtend_readoutTopCat_square {n : ℕ}
    (w : BitWord n) :
    projectivePrefixExtendTopCatHom w ≫ projectiveReadoutTopCatHom =
      projectiveReadoutTopCatHom ≫ finitePrefixAffineTopCatHom n w := by
  simp only [projectivePrefixExtendTopCatHom, projectiveReadoutTopCatHom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [prefixExtend_readoutTopCat_square]

/-- Commutative square intertwining `categoricalLimitPrefixExtendTopCatHom w` and
`finitePrefixAffineTopCatHom n w` via `categoricalLimitReadoutTopCatHom`. -/
theorem categoricalLimitPrefixExtend_readoutTopCat_square {n : ℕ}
    (w : BitWord n) :
    categoricalLimitPrefixExtendTopCatHom w ≫
        categoricalLimitReadoutTopCatHom =
      categoricalLimitReadoutTopCatHom ≫ finitePrefixAffineTopCatHom n w := by
  simp only [categoricalLimitPrefixExtendTopCatHom,
    categoricalLimitReadoutTopCatHom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [projectivePrefixExtend_readoutTopCat_square]

/-- Composing `projectivePrefixExtendTopCatHom w` with `projectiveProjectionTopCatHom n` yields
`projectivePrefixProjectionTopCatHom w`. -/
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

/-- Composing `categoricalLimitPrefixExtendTopCatHom w` with `limit.π prefixDiagram (Opposite.op n)`
yields `categoricalLimitPrefixProjectionTopCatHom w`. -/
theorem categoricalLimitPrefixExtend_projectionTopCat_square {n : ℕ}
    (w : BitWord n) :
    categoricalLimitPrefixExtendTopCatHom w ≫
        limit.π prefixDiagram (Opposite.op n) =
      categoricalLimitPrefixProjectionTopCatHom w := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  funext i
  have h1 := projectiveToCategoricalLimit_projection_apply n
    (projectivePrefixExtendTopCatHom w (projectiveToCategoricalLimitTopCatIso.inv x)) i
  have h2 := congrArg (fun f => f (projectiveToCategoricalLimitTopCatIso.inv x))
    (projectivePrefixExtend_projectionTopCat_square w)
  have h2i := congrFun (congrArg (fun f => f) h2) i
  exact h1.trans h2i

end InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
