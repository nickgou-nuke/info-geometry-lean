import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Multiscale

noncomputable section

/-- Concrete bookkeeping for a fibered inverse-tower square with normalized fiber integration.
The fields record the degree data and the layerwise raw identities used to derive the normalized
Beck--Chevalley, Fubini, and Stokes formulas. -/
structure NormalizedBCStokesFiberedInverseTowerData where
  baseDegree : ℕ → ℝ
  fiberDegree : ℕ → ℝ
  transportedBoundary : ℕ → ℝ
  transportedBulk : ℕ → ℝ
  fiberBoundary : ℕ → ℝ
  fiberBulk : ℕ → ℝ
  totalBoundary : ℕ → ℝ
  totalBulk : ℕ → ℝ
  totalDAlpha : ℕ → ℝ
  baseBoundary : ℕ → ℝ
  baseBulk : ℕ → ℝ
  baseDAlpha : ℕ → ℝ

namespace NormalizedBCStokesFiberedInverseTowerData

def cumulativeBaseDegree (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) D.baseDegree

def cumulativeFiberDegree (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) D.fiberDegree

def cumulativeTotalDegree (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) (fun j => D.baseDegree j * D.fiberDegree j)

def normalizedTransportedBoundary (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.transportedBoundary n / D.cumulativeFiberDegree n

def normalizedTransportedBulk (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.transportedBulk n / D.cumulativeFiberDegree n

def normalizedFiberBoundary (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.fiberBoundary n / D.cumulativeFiberDegree n

def normalizedFiberBulk (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.fiberBulk n / D.cumulativeFiberDegree n

def normalizedTotalBoundary (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.totalBoundary n / D.cumulativeTotalDegree n

def normalizedTotalBulk (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.totalBulk n / D.cumulativeTotalDegree n

def normalizedTotalDAlpha (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.totalDAlpha n / D.cumulativeTotalDegree n

def normalizedBaseBoundary (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.baseBoundary n / D.cumulativeBaseDegree n

def normalizedBaseBulk (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.baseBulk n / D.cumulativeBaseDegree n

def normalizedBaseDAlpha (D : NormalizedBCStokesFiberedInverseTowerData) (n : ℕ) : ℝ :=
  D.baseDAlpha n / D.cumulativeBaseDegree n

theorem cumulativeBaseDegree_pos (D : NormalizedBCStokesFiberedInverseTowerData)
    (baseDegree_pos : ∀ n, 0 < D.baseDegree n) (n : ℕ) :
    0 < D.cumulativeBaseDegree n := by
  exact Finset.prod_pos fun i _ => baseDegree_pos i

theorem cumulativeFiberDegree_pos (D : NormalizedBCStokesFiberedInverseTowerData)
    (fiberDegree_pos : ∀ n, 0 < D.fiberDegree n) (n : ℕ) :
    0 < D.cumulativeFiberDegree n := by
  exact Finset.prod_pos fun i _ => fiberDegree_pos i

theorem cumulativeTotalDegree_pos (D : NormalizedBCStokesFiberedInverseTowerData)
    (baseDegree_pos : ∀ n, 0 < D.baseDegree n)
    (fiberDegree_pos : ∀ n, 0 < D.fiberDegree n) (n : ℕ) :
    0 < D.cumulativeTotalDegree n := by
  exact Finset.prod_pos fun i _ => mul_pos (baseDegree_pos i) (fiberDegree_pos i)

theorem cumulativeTotalDegree_factorization (D : NormalizedBCStokesFiberedInverseTowerData)
    (n : ℕ) :
    D.cumulativeTotalDegree n = D.cumulativeBaseDegree n * D.cumulativeFiberDegree n := by
  induction n with
  | zero =>
      simp [cumulativeTotalDegree, cumulativeBaseDegree, cumulativeFiberDegree]
  | succ n ih =>
      calc
        D.cumulativeTotalDegree (n + 1)
            = D.cumulativeTotalDegree n * (D.baseDegree n * D.fiberDegree n) := by
                simp [cumulativeTotalDegree, Finset.prod_range_succ]
        _ = (D.cumulativeBaseDegree n * D.cumulativeFiberDegree n) *
              (D.baseDegree n * D.fiberDegree n) := by rw [ih]
        _ = (D.cumulativeBaseDegree n * D.baseDegree n) *
              (D.cumulativeFiberDegree n * D.fiberDegree n) := by ring
        _ = D.cumulativeBaseDegree (n + 1) * D.cumulativeFiberDegree (n + 1) := by
              simp [cumulativeBaseDegree, cumulativeFiberDegree, Finset.prod_range_succ,
                mul_assoc, mul_left_comm]

end NormalizedBCStokesFiberedInverseTowerData

open NormalizedBCStokesFiberedInverseTowerData

/-- Normalized Beck--Chevalley, Fubini, and Stokes equivalence for the fibered inverse tower.
    thm:app-normalized-bc-stokes-fibered-inverse-tower -/
theorem paper_app_normalized_bc_stokes_fibered_inverse_tower
    (D : NormalizedBCStokesFiberedInverseTowerData)
    (baseDegree_pos : ∀ n, 0 < D.baseDegree n)
    (fiberDegree_pos : ∀ n, 0 < D.fiberDegree n)
    (beckChevalleyBoundary_raw :
      ∀ n, D.fiberBoundary (n + 1) = D.transportedBoundary n * D.fiberDegree n)
    (beckChevalleyBulk_raw :
      ∀ n, D.fiberBulk (n + 1) = D.transportedBulk n * D.fiberDegree n)
    (fubiniBoundary_raw :
      ∀ n, D.totalBoundary n = D.baseBoundary n * Finset.prod (Finset.range n) D.fiberDegree)
    (fubiniBulk_raw :
      ∀ n, D.totalBulk n = D.baseBulk n * Finset.prod (Finset.range n) D.fiberDegree)
    (differentialFiberIntegration_raw :
      ∀ n, D.totalDAlpha n = D.baseDAlpha n * Finset.prod (Finset.range n) D.fiberDegree) :
    (∀ n, D.normalizedFiberBoundary (n + 1) = D.normalizedTransportedBoundary n ∧
      D.normalizedFiberBulk (n + 1) = D.normalizedTransportedBulk n) ∧
      (∀ n, D.normalizedTotalBulk n = D.normalizedBaseBulk n ∧
        D.normalizedTotalBoundary n = D.normalizedBaseBoundary n) ∧
      (∀ n, D.normalizedTotalDAlpha n = D.normalizedBaseDAlpha n ∧
        D.normalizedTotalBoundary n = D.normalizedBaseBoundary n ∧
        (D.normalizedTotalDAlpha n = D.normalizedTotalBoundary n ↔
          D.normalizedBaseDAlpha n = D.normalizedBaseBoundary n)) := by
  have hBC :
      ∀ n, D.normalizedFiberBoundary (n + 1) = D.normalizedTransportedBoundary n ∧
        D.normalizedFiberBulk (n + 1) = D.normalizedTransportedBulk n := by
    intro n
    have hCum :
        cumulativeFiberDegree D (n + 1) = cumulativeFiberDegree D n * D.fiberDegree n := by
      simp [cumulativeFiberDegree, Finset.prod_range_succ]
    have hCumNz : cumulativeFiberDegree D n ≠ 0 :=
      (cumulativeFiberDegree_pos D fiberDegree_pos n).ne'
    have hFiberNz : D.fiberDegree n ≠ 0 := (fiberDegree_pos n).ne'
    constructor
    · unfold normalizedFiberBoundary normalizedTransportedBoundary
      rw [beckChevalleyBoundary_raw n, hCum]
      field_simp [hCumNz, hFiberNz]
    · unfold normalizedFiberBulk normalizedTransportedBulk
      rw [beckChevalleyBulk_raw n, hCum]
      field_simp [hCumNz, hFiberNz]
  have hFubini :
      ∀ n, D.normalizedTotalBulk n = D.normalizedBaseBulk n ∧
        D.normalizedTotalBoundary n = D.normalizedBaseBoundary n := by
    intro n
    have hTotal :
        cumulativeTotalDegree D n = cumulativeBaseDegree D n * cumulativeFiberDegree D n :=
      cumulativeTotalDegree_factorization D n
    have hBaseNz : cumulativeBaseDegree D n ≠ 0 :=
      (cumulativeBaseDegree_pos D baseDegree_pos n).ne'
    have hFiberNz : cumulativeFiberDegree D n ≠ 0 :=
      (cumulativeFiberDegree_pos D fiberDegree_pos n).ne'
    have hBulkRaw : D.totalBulk n = D.baseBulk n * cumulativeFiberDegree D n := by
      simpa [cumulativeFiberDegree] using fubiniBulk_raw n
    have hBoundaryRaw : D.totalBoundary n = D.baseBoundary n * cumulativeFiberDegree D n := by
      simpa [cumulativeFiberDegree] using fubiniBoundary_raw n
    constructor
    · unfold normalizedTotalBulk normalizedBaseBulk
      rw [hBulkRaw, hTotal]
      field_simp [hBaseNz, hFiberNz]
    · unfold normalizedTotalBoundary normalizedBaseBoundary
      rw [hBoundaryRaw, hTotal]
      field_simp [hBaseNz, hFiberNz]
  have hStokes :
      ∀ n, D.normalizedTotalDAlpha n = D.normalizedBaseDAlpha n ∧
        D.normalizedTotalBoundary n = D.normalizedBaseBoundary n ∧
        (D.normalizedTotalDAlpha n = D.normalizedTotalBoundary n ↔
          D.normalizedBaseDAlpha n = D.normalizedBaseBoundary n) := by
    intro n
    have hTotal :
        cumulativeTotalDegree D n = cumulativeBaseDegree D n * cumulativeFiberDegree D n :=
      cumulativeTotalDegree_factorization D n
    have hBaseNz : cumulativeBaseDegree D n ≠ 0 :=
      (cumulativeBaseDegree_pos D baseDegree_pos n).ne'
    have hFiberNz : cumulativeFiberDegree D n ≠ 0 :=
      (cumulativeFiberDegree_pos D fiberDegree_pos n).ne'
    have hDiffRaw : D.totalDAlpha n = D.baseDAlpha n * cumulativeFiberDegree D n := by
      simpa [cumulativeFiberDegree] using differentialFiberIntegration_raw n
    have hDiff :
        normalizedTotalDAlpha D n = normalizedBaseDAlpha D n := by
      unfold normalizedTotalDAlpha normalizedBaseDAlpha
      rw [hDiffRaw, hTotal]
      field_simp [hBaseNz, hFiberNz]
    have hBoundary :
        normalizedTotalBoundary D n = normalizedBaseBoundary D n := (hFubini n).2
    refine ⟨hDiff, hBoundary, ?_⟩
    constructor <;> intro h
    · calc
        normalizedBaseDAlpha D n = normalizedTotalDAlpha D n := hDiff.symm
        _ = normalizedTotalBoundary D n := h
        _ = normalizedBaseBoundary D n := hBoundary
    · calc
        normalizedTotalDAlpha D n = normalizedBaseDAlpha D n := hDiff
        _ = normalizedBaseBoundary D n := h
        _ = normalizedTotalBoundary D n := hBoundary.symm
  exact ⟨hBC, hFubini, hStokes⟩

end

end Omega.Multiscale
