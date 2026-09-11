import InfoGeometry.Canonical.PositiveGrassmannianAmplituhedron
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open Matrix

/-! A finite coordinate bridge from a Peirce 2×2 channel to a one-row,
four-column positive Grassmannian chart.  This is a chart-level positivity
statement, not a positroid decomposition or canonical-form theorem. -/

def peirceChannelFlatten
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 1) (Fin 4) ℝ :=
  fun _ j => match j with
  | 0 => M 0 0
  | 1 => M 0 1
  | 2 => M 1 0
  | 3 => M 1 1

def peircePositiveChannelCell :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {M | ∀ i j, 0 ≤ M i j}

def peirceStrictlyPositiveChannelCell :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {M | ∀ i j, 0 < M i j}

theorem peircePositiveChannel_mem_grassmannianChart
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M ∈ peircePositiveChannelCell) :
    peirceChannelFlatten M ∈
      positiveGrassmannianChart (k := 1) (n := 4) := by
  change (∀ i j, 0 ≤ M i j) at hM
  intro s hs
  generalize h : s 0 = j
  fin_cases j <;>
    simp [peirceChannelFlatten, maximalMinor, h, hM]

theorem peirceStrictlyPositiveChannel_mem_grassmannianInterior
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M ∈ peirceStrictlyPositiveChannelCell) :
    peirceChannelFlatten M ∈
      positiveGrassmannianInterior (k := 1) (n := 4) := by
  change (∀ i j, 0 < M i j) at hM
  intro s hs
  generalize h : s 0 = j
  fin_cases j <;>
    simp [peirceChannelFlatten, maximalMinor, h, hM]

end InfoGeometry.Canonical
