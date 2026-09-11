import InfoGeometry.Analysis.FiniteSpectralMellinTaylor
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Analysis.FiniteSpectralHeatMellin

Finite heat/Taylor/Mellin readouts for spectral data.

This file formalizes the finite algebraic core of the intuition that the heat
semigroup/Taylor frame and the Mellin/scaling frame are two readouts of the same
finite spectral data.

For finite spectral values `λᵢ` with weights `wᵢ`:

* the finite heat-Taylor prefix is
  `∑ k < N, ((-t)^k / k!) λᵢ^k`;
* summing that prefix over the finite spectrum is the same coefficient-weighted
  sum of integer Mellin/power moments;
* an abstract heat-Mellin scalar readout and an abstract spectral-scaling scalar
  readout agree on the finite spectrum whenever they agree pointwise on the
  finite spectral values.

No spectral theorem.
No heat-kernel convergence.
No Gamma integral.
No Mellin inversion.
No unbounded operator or projection-valued-measure calculus.
-/

namespace InfoGeometry.Analysis.FiniteSpectralHeatMellin

open Finset
open InfoGeometry.Analysis.FiniteSpectralMellinTaylor

variable {ι : Type*} [Fintype ι]

/-- The heat/Taylor coefficient `(-t)^k / k!`. -/
noncomputable def heatTaylorCoeff (t : ℂ) (k : ℕ) : ℂ :=
  (-t) ^ k / (Nat.factorial k : ℂ)

/-- Finite scalar heat-Taylor prefix at a spectral value. -/
noncomputable def scalarHeatTaylorPrefix (t lam : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, heatTaylorCoeff t k * lam ^ k

/-- Finite spectral heat-Taylor readout. -/
noncomputable def heatTaylorReadout (D : FiniteSpectralData ι ℂ) (t : ℂ) (N : ℕ) : ℂ :=
  ∑ i : ι, D.weight i * scalarHeatTaylorPrefix t (D.spectralValue i) N

@[simp]
theorem scalarHeatTaylorPrefix_zero (t lam : ℂ) :
    scalarHeatTaylorPrefix t lam 0 = 0 := by
  simp [scalarHeatTaylorPrefix]

@[simp]
theorem heatTaylorReadout_zero (D : FiniteSpectralData ι ℂ) (t : ℂ) :
    heatTaylorReadout D t 0 = 0 := by
  simp [heatTaylorReadout]

/-- Successor recursion for finite scalar heat-Taylor prefixes. -/
theorem scalarHeatTaylorPrefix_succ (t lam : ℂ) (N : ℕ) :
    scalarHeatTaylorPrefix t lam (N + 1) =
      scalarHeatTaylorPrefix t lam N + heatTaylorCoeff t N * lam ^ N := by
  simp [scalarHeatTaylorPrefix, Finset.sum_range_succ]

/-- Successor recursion for finite spectral heat-Taylor readouts. -/
theorem heatTaylorReadout_succ (D : FiniteSpectralData ι ℂ) (t : ℂ) (N : ℕ) :
    heatTaylorReadout D t (N + 1) =
      heatTaylorReadout D t N + heatTaylorCoeff t N * D.mellinMoment N := by
  unfold heatTaylorReadout
  rw [FiniteSpectralMellinTaylor.FiniteSpectralData.mellinMoment, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [scalarHeatTaylorPrefix_succ]
  ring

/--
Finite heat-Taylor readout equals the Taylor/Mellin moment prefix with heat
coefficients.
-/
theorem heatTaylorReadout_eq_taylorMomentPrefix
    (D : FiniteSpectralData ι ℂ) (t : ℂ) (N : ℕ) :
    heatTaylorReadout D t N = D.taylorMomentPrefix (heatTaylorCoeff t) N := by
  simpa [heatTaylorReadout, scalarHeatTaylorPrefix,
    FiniteSpectralMellinTaylor.FiniteSpectralData.pointwiseTaylorPrefix]
    using D.weighted_pointwiseTaylorPrefix_eq_taylorMomentPrefix (heatTaylorCoeff t) N

/-- Abstract finite heat-Mellin readout: sum a scalar transform over spectral weights. -/
noncomputable def heatMellinReadout
    (D : FiniteSpectralData ι ℂ) (heatMellinScalar : ℂ → ℂ) : ℂ :=
  ∑ i : ι, D.weight i * heatMellinScalar (D.spectralValue i)

/-- Abstract finite spectral-scaling readout: sum a scalar scaling function over weights. -/
noncomputable def spectralScalingReadout
    (D : FiniteSpectralData ι ℂ) (scaleScalar : ℂ → ℂ) : ℂ :=
  ∑ i : ι, D.weight i * scaleScalar (D.spectralValue i)

/--
If the scalar heat-Mellin readout and scalar spectral-scaling readout agree on
the finite spectrum, then their finite spectral readouts agree.
-/
theorem heatMellinReadout_eq_spectralScalingReadout_of_pointwise
    (D : FiniteSpectralData ι ℂ)
    (heatMellinScalar scaleScalar : ℂ → ℂ)
    (hpoint : ∀ i : ι, heatMellinScalar (D.spectralValue i) =
      scaleScalar (D.spectralValue i)) :
    heatMellinReadout D heatMellinScalar = spectralScalingReadout D scaleScalar := by
  unfold heatMellinReadout spectralScalingReadout
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [hpoint i]

end InfoGeometry.Analysis.FiniteSpectralHeatMellin
