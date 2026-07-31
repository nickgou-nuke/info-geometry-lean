import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Multiscale

noncomputable section

/-- Concrete layerwise data for a covering tower with boundary exponents and normalized Stokes
currents. -/
structure CoveringTowerGodelBoundaryNormalizedStokesSystem where
  H0 : ℝ
  boundaryDegree : ℕ → ℕ
  boundaryLabel : ∀ n, Fin (boundaryDegree n) → ℕ
  boundaryExponent : ∀ n, Fin (boundaryDegree n) → ℕ
  collarFormIntegral : ∀ n, Fin (boundaryDegree n) → ℝ
  baseBoundaryValue : ℕ → ℝ
  baseCurrentValue : ℕ → ℝ

def degreeProduct (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℕ :=
  ∑ i : Fin (S.boundaryDegree n), S.boundaryExponent n i

def boundaryHeight (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  S.H0 ^ degreeProduct S n

def boundaryIntegral (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  S.baseBoundaryValue n * boundaryHeight S n

def currentIntegral (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  S.baseCurrentValue n * boundaryHeight S n

def normalizedBoundary (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  boundaryIntegral S n / boundaryHeight S n

def normalizedCurrent (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  currentIntegral S n / boundaryHeight S n

lemma boundaryHeight_pos (S : CoveringTowerGodelBoundaryNormalizedStokesSystem)
    (H0_pos : 0 < S.H0) (n : ℕ) : 0 < boundaryHeight S n := by
  unfold boundaryHeight
  exact pow_pos H0_pos _

lemma normalizedBoundary_eq_base (S : CoveringTowerGodelBoundaryNormalizedStokesSystem)
    (H0_pos : 0 < S.H0) (n : ℕ) :
    normalizedBoundary S n = S.baseBoundaryValue n := by
  have hHeight_ne : boundaryHeight S n ≠ 0 := (boundaryHeight_pos S H0_pos n).ne'
  unfold normalizedBoundary boundaryIntegral
  field_simp [hHeight_ne]

lemma normalizedCurrent_eq_base (S : CoveringTowerGodelBoundaryNormalizedStokesSystem)
    (H0_pos : 0 < S.H0) (n : ℕ) :
    normalizedCurrent S n = S.baseCurrentValue n := by
  have hHeight_ne : boundaryHeight S n ≠ 0 := (boundaryHeight_pos S H0_pos n).ne'
  unfold normalizedCurrent currentIntegral
  field_simp [hHeight_ne]

/-- Boundary-cost realization, power-law height, and inverse-limit compatibility from explicit
layer laws. -/
theorem paper_app_covering_tower_godel_boundary_normalized_stokes
    (S : CoveringTowerGodelBoundaryNormalizedStokesSystem)
    (H0_pos : 0 < S.H0)
    (baseLayerCompatibility : ∀ n,
      S.baseBoundaryValue (n + 1) = S.baseBoundaryValue n)
    (baseCurrent_eq_boundary : ∀ n,
      S.baseCurrentValue n = S.baseBoundaryValue n)
    (collarSum : ∀ n,
      (∑ i : Fin (S.boundaryDegree n), S.collarFormIntegral n i) =
        S.baseBoundaryValue n * S.H0 ^ (∑ i : Fin (S.boundaryDegree n),
          S.boundaryExponent n i)) :
    (∀ n, boundaryHeight S n = S.H0 ^ degreeProduct S n) ∧
      (∀ n,
        normalizedBoundary S n =
            (∑ i : Fin (S.boundaryDegree n), S.collarFormIntegral n i) /
              boundaryHeight S n ∧
          normalizedBoundary S n = normalizedCurrent S n) ∧
      (∀ n,
        normalizedBoundary S (n + 1) = normalizedBoundary S n ∧
          normalizedCurrent S (n + 1) = normalizedCurrent S n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    constructor
    · unfold normalizedBoundary boundaryIntegral boundaryHeight degreeProduct
      rw [collarSum n]
    · rw [normalizedBoundary_eq_base S H0_pos, normalizedCurrent_eq_base S H0_pos,
        baseCurrent_eq_boundary]
  · intro n
    constructor
    · rw [normalizedBoundary_eq_base S H0_pos, normalizedBoundary_eq_base S H0_pos,
        baseLayerCompatibility]
    · rw [normalizedCurrent_eq_base S H0_pos, normalizedCurrent_eq_base S H0_pos,
        baseCurrent_eq_boundary, baseCurrent_eq_boundary, baseLayerCompatibility]

end

end Omega.Multiscale
