import InfoGeometry.Canonical.CantorProjectiveLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic

/-!
# `TopCat` interface for the finite-prefix projective limit

The concrete coherent-prefix carrier already has a homeomorphism with the
Cantor boundary.  This owner exposes that equivalence and the finite-prefix
projections as categorical topological maps, including their bonding
coherence.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit

def cantorProjectiveLimitTopCatIso :
    TopCat.of CantorBoundary ≅ TopCat.of PrefixProjectiveLimit where
  hom := TopCat.ofHom
    { toFun := cantorHomeomorphPrefixProjectiveLimit
      continuous_toFun := cantorHomeomorphPrefixProjectiveLimit.continuous }
  inv := TopCat.ofHom
    { toFun := cantorHomeomorphPrefixProjectiveLimit.symm
      continuous_toFun := cantorHomeomorphPrefixProjectiveLimit.symm.continuous }
  hom_inv_id := by
    apply TopCat.hom_ext
    ext x
    simp [TopCat.ofHom]
  inv_hom_id := by
    apply TopCat.hom_ext
    ext x
    simp [TopCat.ofHom]

def projectiveProjectionTopCatHom (n : ℕ) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of (BitWord n) :=
  TopCat.ofHom
    { toFun := π n
      continuous_toFun := continuous_π n }

def prefixSuccTopCatHom (n : ℕ) :
    TopCat.of (BitWord (n + 1)) ⟶ TopCat.of (BitWord n) :=
  TopCat.ofHom
    { toFun := prefixSucc n
      continuous_toFun := by fun_prop }

@[simp] theorem projectiveProjectionTopCatHom_apply
    (n : ℕ) (p : PrefixProjectiveLimit) :
    projectiveProjectionTopCatHom n p = π n p := rfl

@[simp] theorem prefixSuccTopCatHom_apply
    (n : ℕ) (w : BitWord (n + 1)) :
    prefixSuccTopCatHom n w = prefixSucc n w := rfl

theorem projectiveProjection_bonding_square (n : ℕ) :
    projectiveProjectionTopCatHom (n + 1) ≫ prefixSuccTopCatHom n =
      projectiveProjectionTopCatHom n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  change prefixSucc n (π (n + 1) p) = π n p
  exact projection_coherent p n

theorem cantorProjectiveLimit_projection_readout (n : ℕ) (x : CantorBoundary) :
    projectiveProjectionTopCatHom n
        (cantorProjectiveLimitTopCatIso.hom x) =
      boundaryPrefix n x := by
  exact cantorHomeomorph_projection x n

end InfoGeometry.Canonical.CantorProjectiveLimitTopCat
