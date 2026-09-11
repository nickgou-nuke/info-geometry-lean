import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topology of finite Sinkhorn scaling

The algebraic Sinkhorn owner requires positive row or column sums.  This file
packages the corresponding normalization maps as continuous maps on those
open positive-sum carriers.  It does not assert convergence of an iteration.
-/

noncomputable section

namespace InfoGeometry.Topology.SinkhornScalingTopological

open InfoGeometry.Canonical.MoE

abbrev SinkhornMatrix (n : Nat) := Matrix (Fin n) (Fin n) ℝ
abbrev PositiveRowSumMatrix (n : Nat) :=
  {M : SinkhornMatrix n // HasPositiveRowSums n M}
abbrev PositiveColSumMatrix (n : Nat) :=
  {M : SinkhornMatrix n // HasPositiveColSums n M}

noncomputable def rowNormalizeContinuousMap (n : Nat) :
    C(PositiveRowSumMatrix n, SinkhornMatrix n) :=
  ContinuousMap.mk
    (fun M => rowNormalize n M.1 M.2)
    (by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      unfold rowNormalize rowSum
      have hnum : Continuous (fun M : PositiveRowSumMatrix n => M.1 i j) := by
        exact (continuous_apply j).comp
          ((continuous_apply i).comp continuous_subtype_val)
      have hden : Continuous (fun M : PositiveRowSumMatrix n =>
          ∑ k : Fin n, M.1 i k) := by
        refine continuous_finset_sum Finset.univ ?_
        intro k hk
        exact (continuous_apply k).comp
          ((continuous_apply i).comp continuous_subtype_val)
      apply hnum.div₀ hden
      intro M
      exact (M.2 i).ne')

@[simp] theorem rowNormalizeContinuousMap_apply
    (n : Nat) (M : PositiveRowSumMatrix n) :
    rowNormalizeContinuousMap n M = rowNormalize n M.1 M.2 :=
  rfl

noncomputable def colNormalizeContinuousMap (n : Nat) :
    C(PositiveColSumMatrix n, SinkhornMatrix n) :=
  ContinuousMap.mk
    (fun M => colNormalize n M.1 M.2)
    (by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      unfold colNormalize colSum
      have hnum : Continuous (fun M : PositiveColSumMatrix n => M.1 i j) := by
        exact (continuous_apply j).comp
          ((continuous_apply i).comp continuous_subtype_val)
      have hden : Continuous (fun M : PositiveColSumMatrix n =>
          ∑ k : Fin n, M.1 k j) := by
        refine continuous_finset_sum Finset.univ ?_
        intro k hk
        exact (continuous_apply j).comp
          ((continuous_apply k).comp continuous_subtype_val)
      apply hnum.div₀ hden
      intro M
      exact (M.2 j).ne')

@[simp] theorem colNormalizeContinuousMap_apply
    (n : Nat) (M : PositiveColSumMatrix n) :
    colNormalizeContinuousMap n M = colNormalize n M.1 M.2 :=
  rfl

def rowNormalizeTopCatHom (n : Nat) :
    TopCat.of (PositiveRowSumMatrix n) ⟶ TopCat.of (SinkhornMatrix n) :=
  TopCat.ofHom (rowNormalizeContinuousMap n)

@[simp] theorem rowNormalizeTopCatHom_apply
    (n : Nat) (M : PositiveRowSumMatrix n) :
    rowNormalizeTopCatHom n M = rowNormalize n M.1 M.2 :=
  rfl

def colNormalizeTopCatHom (n : Nat) :
    TopCat.of (PositiveColSumMatrix n) ⟶ TopCat.of (SinkhornMatrix n) :=
  TopCat.ofHom (colNormalizeContinuousMap n)

@[simp] theorem colNormalizeTopCatHom_apply
    (n : Nat) (M : PositiveColSumMatrix n) :
    colNormalizeTopCatHom n M = colNormalize n M.1 M.2 :=
  rfl

theorem rowNormalizeContinuousMap_rowLyapunov_eq_zero
    (n : Nat) (M : PositiveRowSumMatrix n) :
    rowLyapunov n (rowNormalizeContinuousMap n M) = 0 := by
  exact rowLyapunov_rowNormalize_eq_zero n M.1 M.2

theorem colNormalizeContinuousMap_colLyapunov_eq_zero
    (n : Nat) (M : PositiveColSumMatrix n) :
    colLyapunov n (colNormalizeContinuousMap n M) = 0 := by
  exact colLyapunov_colNormalize_eq_zero n M.1 M.2

end InfoGeometry.Topology.SinkhornScalingTopological
