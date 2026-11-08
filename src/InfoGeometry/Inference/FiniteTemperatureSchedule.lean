/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.GibbsTemperatureSusceptibility
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite temperature schedule selection

Temperature selection is performed over an explicit finite schedule. This
avoids asserting that an unconstrained continuous optimization of temperature
has a meaningful or unique solution.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators

variable {Data : Type*} [Fintype Data] [Nonempty Data]

theorem exists_schedule_max_susceptibility
    (E : Data → ℝ) (S : Finset ℝ) (hS : S.Nonempty)
    (hSpos : ∀ ε ∈ S, 0 < ε) :
    ∃ ε ∈ S, 0 < ε ∧
      ∀ δ ∈ S,
        temperatureSusceptibility E δ ≤ temperatureSusceptibility E ε := by
  let values : Finset ℝ := S.image (temperatureSusceptibility E)
  have hvalues : values.Nonempty := by
    exact hS.image (temperatureSusceptibility E)
  have hmax_mem : values.max' hvalues ∈ values :=
    Finset.max'_mem values hvalues
  rcases (Finset.mem_image.mp hmax_mem) with ⟨ε, hε, hεmax⟩
  refine ⟨ε, hε, hSpos ε hε, ?_⟩
  intro δ hδ
  have hδmem : temperatureSusceptibility E δ ∈ values := by
    exact Finset.mem_image.mpr ⟨δ, hδ, rfl⟩
  have hle : temperatureSusceptibility E δ ≤ values.max' hvalues :=
    Finset.le_max' values _ hδmem
  simpa [hεmax] using hle

end InfoGeometry.Inference.FiniteGibbs
