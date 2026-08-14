import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Native Dirichlet-series readout for the Bost--Connes partition

This owner records only the convergent arithmetic series and its Mathlib zeta
identification.  It does not define a KMS state or a C*-dynamical system.
-/

namespace InfoGeometry.Arithmetic.BostConnesNativeZetaPartition

noncomputable def partitionSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s

theorem partitionSeries_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    partitionSeries s = riemannZeta s := by
  unfold partitionSeries
  simpa [Nat.cast_add] using (zeta_eq_tsum_one_div_nat_add_one_cpow hs).symm

theorem partitionSeries_ne_zero {s : ℂ} (hs : 1 < s.re) :
    partitionSeries s ≠ 0 := by
  rw [partitionSeries_eq_riemannZeta hs]
  exact riemannZeta_ne_zero_of_one_lt_re hs

theorem summable_partitionSeries_summand (s : ℂ) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) ↔ 1 < s.re := by
  simpa [Nat.cast_add] using
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).trans
      (Complex.summable_one_div_nat_cpow (p := s))

theorem not_summable_harmonic_shift :
    ¬ Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro h
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
  simpa [Nat.cast_add] using h

end InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
