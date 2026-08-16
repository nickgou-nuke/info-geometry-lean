import Mathlib.NumberTheory.LSeries.Dirichlet
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.BostConnes.BostConnesParity
import InfoGeometry.Canonical.BostConnesLiouvilleModularComm

open ArithmeticFunction BigOperators InfoGeometry.Arithmetic.BostConnesSystem
open scoped ArithmeticFunction.Moebius
open scoped LSeries.notation

/-!
This file provides operatorial Bost--Connes/Liouville intertwining and
Möbius/L-series readouts.
The historical namespace `BostConnesThermofield` is retained, but no Hilbert
space thermofield-double state, KMS state, or supersymmetric index is
constructed here.
-/

namespace BostConnesThermofield

abbrev BostConnesGenerator := {n : ℕ // 0 < n}

namespace BostConnesGenerator

abbrev mu_n (g : BostConnesGenerator) : ℕ := g.1

abbrev sector_pos (g : BostConnesGenerator) : 0 < g.mu_n := g.2

def mk (mu_n : ℕ) (sector_pos : 0 < mu_n) : BostConnesGenerator :=
  ⟨mu_n, sector_pos⟩

end BostConnesGenerator

namespace BostConnesGenerator

theorem sector_ne_zero (g : BostConnesGenerator) : g.mu_n ≠ 0 :=
  Nat.ne_of_gt g.sector_pos

end BostConnesGenerator

/-! The modular lane is operatorial: it is the supplied flow on the Cuntz
generators, not multiplication of two scalar readouts. -/

theorem operatorial_liouville_modular_intertwining
    {Op : Type*} [NormedRing Op] [NormedAlgebra ℂ Op] [StarRing Op]
    (C : InfoGeometry.Arithmetic.BostConnesSystem.CuntzMultiplicativeIndexing Op)
    (F : InfoGeometry.Canonical.BostConnesModularFlow.ArithmeticModularFlow C)
    (grading : InfoGeometry.Canonical.BostConnesModularFlow.LiouvilleModularInvariance C F)
    (t : ℝ) (n : ℕ+) :
    grading.Γ (F.σ t (C.generator n)) = F.σ t (grading.Γ (C.generator n)) :=
  InfoGeometry.Canonical.BostConnesModularFlow.witten_index_conserved_under_flow
    C F grading t n

/-! The following is an arithmetic Möbius/L-series readout, not a Witten
index: no supersymmetric Hamiltonian or supertrace is defined in this file. -/
noncomputable def moebiusLSeriesReadout (beta : ℝ) : ℝ :=
  ∑' n : ℕ+, (ArithmeticFunction.moebius n.val : ℝ) * (n.val : ℝ) ^ (-beta)

theorem moebiusLSeriesReadout_eq_tsum_nat_succ (beta : ℝ) :
    moebiusLSeriesReadout beta =
      ∑' n : ℕ,
        (ArithmeticFunction.moebius (n + 1) : ℝ) *
          ((n + 1 : ℕ) : ℝ) ^ (-beta) := by
  simpa [moebiusLSeriesReadout] using
    (tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ =>
        (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-beta)))

theorem moebius_LSeries_eq_reciprocal_zeta (beta : ℝ) (hbeta : beta > 1) :
    L ↗μ (beta : ℂ) = (riemannZeta (beta : ℂ))⁻¹ := by
  have hs : 1 < (beta : ℂ).re := by simpa using hbeta
  have hmul : riemannZeta (beta : ℂ) * L ↗μ (beta : ℂ) = 1 := by
    have h := LSeries_one_mul_Lseries_moebius (s := (beta : ℂ)) hs
    rw [LSeries_one_eq_riemannZeta hs] at h
    simpa [mul_comm] using h
  have hmul' : L ↗μ (beta : ℂ) * riemannZeta (beta : ℂ) = 1 := by
    simpa [mul_comm] using hmul
  have hz : riemannZeta (beta : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  exact (mul_eq_one_iff_eq_inv₀ hz).mp hmul'

theorem ofReal_moebiusLSeriesReadout_eq_moebius_LSeries
    (beta : ℝ) (hbeta : 1 < beta) :
    (moebiusLSeriesReadout beta : ℂ) = L ↗μ (beta : ℂ) := by
  have hs : 1 < (beta : ℂ).re := by simpa using hbeta
  have hsum : Summable (LSeries.term (↗μ) (beta : ℂ)) := by
    exact ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  rw [moebiusLSeriesReadout, Complex.ofReal_tsum]
  rw [LSeries]
  rw [hsum.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add]
  rw [← tsum_pnat_eq_tsum_succ]
  apply tsum_congr
  intro n
  rw [LSeries.term_of_ne_zero]
  · simp only [Complex.ofReal_mul]
    rw [Complex.ofReal_cpow (by positivity : 0 ≤ (n : ℝ))]
    rw [show ((n : ℝ) : ℂ) ^ ((-beta : ℝ) : ℂ) =
      (((n : ℝ) : ℂ) ^ ((beta : ℝ) : ℂ))⁻¹ by
        rw [← Complex.cpow_neg]
        congr 1
        norm_num]
    rw [div_eq_mul_inv]
    norm_num
  · exact PNat.ne_zero n

theorem ofReal_moebiusLSeriesReadout_eq_reciprocal_zeta
    (beta : ℝ) (hbeta : 1 < beta) :
    (moebiusLSeriesReadout beta : ℂ) = (riemannZeta (beta : ℂ))⁻¹ := by
  rw [ofReal_moebiusLSeriesReadout_eq_moebius_LSeries beta hbeta]
  exact moebius_LSeries_eq_reciprocal_zeta beta hbeta

/--
Möbius/Liouville decomposition statement.

The Möbius function decomposes as:
  μ(n) = squarefreeProj n × λ(n)

where:
  - λ(n) = (-1)^Ω(n) is the everywhere-defined parity factor
  - squarefreeProj n = 1 if n is squarefree, 0 otherwise

This shows μ is the squarefree projection of the full parity grading.
-/
theorem moebius_decomposition (n : ℕ) :
    ArithmeticFunction.moebius n =
      InfoGeometry.BostConnes.squarefreeProj n *
        InfoGeometry.BostConnes.liouvilleParity n := by
  exact InfoGeometry.BostConnes.moebius_eq_squarefreeProj_mul_liouvilleParity n

/--
Fermionic sectors: μ(n) ≠ 0 (squarefree integers).

This is the squarefree sector selected by the arithmetic predicate.
-/
def is_fermionic_sector (n : ℕ) : Prop :=
  Squarefree n

/-- The fermionic sector is exactly the nonzero Möbius sector. -/
theorem is_fermionic_sector_iff_moebius_ne_zero (n : ℕ) :
    is_fermionic_sector n ↔ ArithmeticFunction.moebius n ≠ 0 := by
  simpa [is_fermionic_sector] using
    (ArithmeticFunction.moebius_ne_zero_iff_squarefree (n := n)).symm

/-- The complementary arithmetic sector is exactly the zero Möbius sector. -/
theorem not_is_fermionic_sector_iff_moebius_eq_zero (n : ℕ) :
    ¬ is_fermionic_sector n ↔ ArithmeticFunction.moebius n = 0 := by
  have h := not_congr (is_fermionic_sector_iff_moebius_ne_zero n)
  simpa using h

/--
Even-parity sectors: λ(n) = +1.

Note: this includes both squarefree and non-squarefree integers.
-/
def is_bosonic_sector (n : ℕ) : Prop :=
  InfoGeometry.BostConnes.liouvilleParity n = 1

/--
Negative Möbius sectors: μ(n) = -1 (odd ω(n), squarefree).

This is the negative squarefree branch of the arithmetic decomposition.
-/
def is_mobius_fermionic_sector (n : ℕ) : Prop :=
  ArithmeticFunction.moebius n = -1

/--
Positive Möbius sectors: μ(n) = +1 (even ω(n), squarefree).
-/
def is_mobius_bosonic_sector (n : ℕ) : Prop :=
  ArithmeticFunction.moebius n = 1

/-- The arithmetic Möbius function vanishes on non-squarefree integers. -/
theorem pauli_exclusion (n : ℕ) :
    ¬Squarefree n → ArithmeticFunction.moebius n = 0 := by
  intro h
  exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree h

/--
Count fermionic (squarefree) sectors up to N.

This counts the squarefree branch up to N.
-/
noncomputable def count_fermionic (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (fun n => n > 0 ∧ Squarefree n) |>.card

/--
Count bosonic sectors (λ = +1) up to N.
-/
noncomputable def count_bosonic (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter
      (fun n => n > 0 ∧ InfoGeometry.BostConnes.liouvilleParity n = 1) |>.card

noncomputable def moebiusLSeriesReadout_approx (N : ℕ) (beta : ℝ) : ℝ :=
  ((Finset.range (N + 1)).filter (fun n => n > 0)).sum
    (fun n => (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-beta))

/-- The Liouville grading has unit square, so it is a genuine `±1` parity. -/
theorem liouvilleParity_sq (n : ℕ) :
    (InfoGeometry.BostConnes.liouvilleParity n : ℤ) *
      InfoGeometry.BostConnes.liouvilleParity n = 1 := by
  rw [InfoGeometry.BostConnes.liouvilleParity]
  rw [← pow_add]
  have h : ArithmeticFunction.cardFactors n + ArithmeticFunction.cardFactors n =
      2 * ArithmeticFunction.cardFactors n := by omega
  rw [h, pow_mul]
  norm_num

/-- The duplicated grading statement is reduced to `liouvilleParity_sq`. -/
theorem thermofield_preserves_grading (n : ℕ) :
    (InfoGeometry.BostConnes.liouvilleParity n : ℤ) *
      InfoGeometry.BostConnes.liouvilleParity n = 1 := by
  exact liouvilleParity_sq n

end BostConnesThermofield
