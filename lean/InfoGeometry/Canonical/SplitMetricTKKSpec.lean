import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Algebra.SplitMetricSpace
import InfoGeometry.Canonical.TKKJordanPairData
import InfoGeometry.Canonical.SplitOctonionTKK55

/-!
# Abstract split-metric TKK specifications

This file is the common contract for the independent Zorn, split-octonion,
chiral-operator, exceptional-Lie, and nuclear realizations.  It deliberately
contains no concrete carrier.  A realization must supply the metric, Lie
bracket, five grades, and the compatibility of the Lie action with the metric.

An `EquivariantTKKHom` additionally records compatibility with an external
symmetry action.  It is not an equivalence until an inverse and bijectivity
have been proved.
-/

noncomputable section

namespace InfoGeometry.Canonical

open TKKJordanPairData
open SplitOctonionJordanForm
abbrev SplitMetricSpace := InfoGeometry.Algebra.SplitMetricSpace

open SplitOctonionTKK55

/-- The already-proved hyperbolic metric on the concrete ten-dimensional
split-octonion carrier, packaged in the abstract metric contract. -/
def splitOctonionTKKMetric : SplitMetricSpace ℝ where
  V := Carrier
  beta := LinearMap.mk₂ ℝ hyperbolicBeta
    hyperbolicBeta_add_left hyperbolicBeta_smul_left
    hyperbolicBeta_add_right hyperbolicBeta_smul_right
  beta_symm := ⟨by
    intro x y
    exact hyperbolicBeta_symmetric x y⟩
  beta_nondegenerate := by
    constructor
    · intro x hx
      rcases x with ⟨a, ⟨u, c⟩⟩
      have ha := hx (0, (0, 1))
      have hc := hx (1, (0, 0))
      have hu : ∀ v, beta44 u v = 0 := by
        intro v
        have hv := hx (0, (v, 0))
        simpa [hyperbolicBeta] using hv
      have hu0 := beta44_nondegenerate_left u hu
      simp [hyperbolicBeta] at ha hc
      simp [ha, hc, hu0]
    · intro x hx
      rcases x with ⟨a, ⟨u, c⟩⟩
      have ha := hx (0, (0, 1))
      have hc := hx (1, (0, 0))
      have hu : ∀ v, beta44 v u = 0 := by
        intro v
        have hv := hx (0, (v, 0))
        simpa [hyperbolicBeta] using hv
      have hu0 := beta44_nondegenerate_right u hu
      simp [hyperbolicBeta] at ha hc
      simp [ha, hc, hu0]
/- old proof retained for reference
  beta_nondegenerate_left := by
    intro x hx
    rcases x with ⟨a, ⟨u, c⟩⟩
    have ha := hx (0, (0, 1))
    have hc := hx (1, (0, 0))
    have hu : ∀ v, beta44 u v = 0 := by
      intro v
      have hv := hx (0, (v, 0))
      simpa [hyperbolicBeta] using hv
    have hu0 := beta44_nondegenerate_left u hu
    simp [hyperbolicBeta] at ha hc
    simp [ha, hc, hu0]
  beta_nondegenerate_right := by
    intro x hx
    rcases x with ⟨a, ⟨u, c⟩⟩
    have ha := hx (0, (0, 1))
    have hc := hx (1, (0, 0))
    have hu : ∀ v, beta44 v u = 0 := by
      intro v
      have hv := hx (0, (v, 0))
      simpa [hyperbolicBeta] using hv
    have hu0 := beta44_nondegenerate_right u hu
    simp [hyperbolicBeta] at ha hc
    simp [ha, hc, hu0] -/

theorem splitOctonionMetric_finrank :
    Module.finrank ℝ splitOctonionTKKMetric.V = 10 := by
  exact carrier_finrank

structure SplitMetricLieAlgebra (R : Type*) [CommRing R] where
  metric : SplitMetricSpace R
  L : Type*
  [lieRing : LieRing L]
  [addGroup : AddCommGroup L]
  [module : Module R L]
  [lieAlgebra : LieAlgebra R L]
  metric_action : L →ₗ[R] Module.End R metric.V
  action_skew : ∀ x u v,
    metric.beta (metric_action x u) v + metric.beta u (metric_action x v) = 0
  action_lie : ∀ x y,
    metric_action ⁅x, y⁆ = ⁅metric_action x, metric_action y⁆

attribute [instance] SplitMetricLieAlgebra.lieRing SplitMetricLieAlgebra.addGroup
attribute [instance] SplitMetricLieAlgebra.module SplitMetricLieAlgebra.lieAlgebra

open SplitOctonionTKK55

/-! The existing 45-dimensional block Lie algebra acting on the concrete
hyperbolic carrier. -/
noncomputable def splitOctonionLieAlgebra : SplitMetricLieAlgebra ℝ where
  metric := splitOctonionTKKMetric
  L := AbstractTKKCarrier
  metric_action := blockOperatorLinear
  action_skew := by
    intro d u v
    exact blockOperator_hyperbolic_skew d u v
  action_lie := by
    intro d e
    have h := abstractTKKLieEquiv_map_lie d e
    exact congrArg (fun T : hyperbolicSkewSubmodule =>
      (T : Module.End ℝ Carrier)) h

theorem splitOctonionLieAlgebra_finrank :
    Module.finrank ℝ splitOctonionLieAlgebra.L = 45 := by
  exact abstractTKK_finrank

structure SplitMetricTKK (R : Type*) [CommRing R]
    extends toLie : SplitMetricLieAlgebra R where
  grade : TKKGrade → Submodule R L
  bracket_mem_some : ∀ {i j k : TKKGrade}, gradeAdd i j = some k →
    ∀ {x y : L}, x ∈ grade i → y ∈ grade j → ⁅x, y⁆ ∈ grade k
  bracket_eq_zero_none : ∀ {i j : TKKGrade}, gradeAdd i j = none →
    ∀ {x y : L}, x ∈ grade i → y ∈ grade j → ⁅x, y⁆ = 0

attribute [instance] SplitMetricTKK.toLie

structure TKKRealization {R : Type*} [CommRing R]
    (S M : SplitMetricTKK R) where
  map : S.L →ₗ⁅R⁆ M.L
  map_grade : ∀ {i x}, x ∈ S.grade i → map x ∈ M.grade i

structure EquivariantTKKHom {R G : Type*} [CommRing R] [Monoid G]
    (S M : SplitMetricTKK R) where
  map : S.L →ₗ⁅R⁆ M.L
  sourceAction : G → S.L → S.L
  targetAction : G → M.L → M.L
  map_grade : ∀ {i x}, x ∈ S.grade i → map x ∈ M.grade i
  sourceAction_grade : ∀ g i x, x ∈ S.grade i → sourceAction g x ∈ S.grade i
  targetAction_grade : ∀ g i x, x ∈ M.grade i → targetAction g x ∈ M.grade i
  equivariant : ∀ g x, map (sourceAction g x) = targetAction g (map x)

structure EquivariantTKKEquiv {R G : Type*} [CommRing R] [Monoid G]
    (S M : SplitMetricTKK R) extends EquivariantTKKHom (G := G) S M where
  inverse : M.L →ₗ⁅R⁆ S.L
  inverse_map : ∀ x, inverse (map x) = x
  map_inverse : ∀ x, map (inverse x) = x
  inverse_equivariant : ∀ g x,
    inverse (targetAction g x) = sourceAction g (inverse x)

theorem EquivariantTKKHom.map_bracket
    {R G : Type*} [CommRing R] [Monoid G]
    {S M : SplitMetricTKK R} (F : EquivariantTKKHom (G := G) S M) (x y : S.L) :
    F.map ⁅x, y⁆ = ⁅F.map x, F.map y⁆ :=
  F.map.map_lie x y

theorem EquivariantTKKEquiv.bijective
    {R G : Type*} [CommRing R] [Monoid G]
    {S M : SplitMetricTKK R} (F : EquivariantTKKEquiv (G := G) S M) :
    Function.Bijective F.map := by
  constructor
  · intro x y h
    calc
      x = F.inverse (F.map x) := (F.inverse_map x).symm
      _ = F.inverse (F.map y) := by rw [h]
      _ = y := F.inverse_map y
  · intro y
    exact ⟨F.inverse y, F.map_inverse y⟩

end InfoGeometry.Canonical
