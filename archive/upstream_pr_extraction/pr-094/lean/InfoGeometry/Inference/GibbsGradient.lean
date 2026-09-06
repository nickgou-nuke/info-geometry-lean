/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InfoGeometry.Inference.FiniteGibbsInference

/-!
# Gibbs reweighted gradient

For a one-dimensional parameter, this module proves the finite Gibbs identity
that the free-energy derivative is the Boltzmann-weighted average of the
energy derivatives. The result is local and finite; it does not assert global
optimization or an outlier interpretation.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

open FiniteGibbs

variable {Data : Type*} [Fintype Data] [Nonempty Data]

omit [Nonempty Data] in
theorem hasDerivAt_partitionFunction
    (M : FiniteGibbs.Model (Data := Data) (Theta := ℝ))
    (θ ε : ℝ) (g : Data → ℝ)
    (hg : ∀ i, HasDerivAt (M.energy i) (g i) θ) :
    HasDerivAt (fun t => partitionFunction M t ε)
      (∑ i : Data, Real.exp (-M.energy i θ / ε) * (-(g i) / ε)) θ := by
  unfold partitionFunction
  apply HasDerivAt.fun_sum
  intro i hi
  have harg : HasDerivAt (fun t => -M.energy i t / ε) (-(g i) / ε) θ := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((hg i).neg.const_mul ε⁻¹)
  simpa using (Real.hasDerivAt_exp _).comp θ harg

theorem hasDerivAt_freeEnergy
    (M : FiniteGibbs.Model (Data := Data) (Theta := ℝ))
    (θ ε : ℝ) (hε : ε ≠ 0) (g : Data → ℝ)
    (hg : ∀ i, HasDerivAt (M.energy i) (g i) θ) :
    HasDerivAt (fun t => freeEnergy M t ε)
      (∑ i : Data, weight M θ ε i * g i) θ := by
  have hZpos : 0 < partitionFunction M θ ε := partitionFunction_pos M θ ε
  have hZ : HasDerivAt (fun t => partitionFunction M t ε)
      (∑ i : Data, Real.exp (-M.energy i θ / ε) * (-(g i) / ε)) θ :=
    hasDerivAt_partitionFunction M θ ε g hg
  have hlog := hZ.log (partitionFunction_ne_zero M θ ε)
  have hfree := hlog.const_mul (-ε)
  have hweighted :
      (∑ i : Data, weight M θ ε i * g i) =
        -ε * ((∑ i : Data, Real.exp (-M.energy i θ / ε) * (-(g i) / ε)) /
          partitionFunction M θ ε) := by
    calc
      ∑ i : Data, weight M θ ε i * g i =
          ∑ i : Data,
            (-ε) *
              (Real.exp (-M.energy i θ / ε) * (-(g i) / ε) /
                partitionFunction M θ ε) := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold weight
        simp only [div_eq_mul_inv]
        field_simp [hε, partitionFunction_ne_zero M θ ε]
      _ = -ε * ∑ i : Data,
          (Real.exp (-M.energy i θ / ε) * (-(g i) / ε) /
            partitionFunction M θ ε) := by
        rw [← Finset.mul_sum]
      _ = -ε * ((∑ i : Data,
          Real.exp (-M.energy i θ / ε) * (-(g i) / ε)) /
            partitionFunction M θ ε) := by
        congr 1
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_mul]
  convert hfree using 1

end InfoGeometry.Inference
