import Mathlib.Tactic

/-!
# Grand-Canonical Berezinian for Gapped Boson/Fermion Primons

Finite scalar model combining the even/odd blocks in one Berezinian.

For shifted energy `ξ = E - μ`, gap `Δ`, and inverse temperature `β`, define

`Eg = sqrt (ξ^2 + Δ^2)`
`x  = exp (-β * Eg)`.

The finite local factors are:

* fermionic/odd occupation numerator: `1 + x`;
* bosonic/even geometric denominator: `1 - x`;
* unified super partition ratio/Berezinian: `(1 + x) / (1 - x)`.

This is the local diagonal `1|1` Berezinian chart.  It is not a convergence
claim about an infinite product over all primes.
-/

noncomputable section

def gcBerShiftedEnergy (E μ : ℝ) : ℝ :=
  E - μ

def gcBerGappedEnergy (E μ Δ : ℝ) : ℝ :=
  Real.sqrt ((gcBerShiftedEnergy E μ) ^ 2 + Δ ^ 2)

def gcBerFugacity (β E μ Δ : ℝ) : ℝ :=
  Real.exp (-(β * gcBerGappedEnergy E μ Δ))

def gcBerFermionOddBlock (β E μ Δ : ℝ) : ℝ :=
  1 + gcBerFugacity β E μ Δ

def gcBerBosonEvenDenominator (β E μ Δ : ℝ) : ℝ :=
  1 - gcBerFugacity β E μ Δ

def gcDiagonalBerezinian (even odd : ℝ) : ℝ :=
  even / odd

def gcSuperBerezinian (β E μ Δ : ℝ) : ℝ :=
  gcDiagonalBerezinian
    (gcBerFermionOddBlock β E μ Δ)
    (gcBerBosonEvenDenominator β E μ Δ)

def gcGappedBosonFactor (β E μ Δ : ℝ) : ℝ :=
  (gcBerBosonEvenDenominator β E μ Δ)⁻¹

def gcGappedFermionFactor (β E μ Δ : ℝ) : ℝ :=
  gcBerFermionOddBlock β E μ Δ

theorem gcBerGappedEnergy_at_fermi_sq (μ Δ : ℝ) :
    (gcBerGappedEnergy μ μ Δ) ^ 2 = Δ ^ 2 := by
  have h : 0 ≤ (gcBerShiftedEnergy μ μ) ^ 2 + Δ ^ 2 := by positivity
  unfold gcBerGappedEnergy
  rw [Real.sq_sqrt h]
  simp [gcBerShiftedEnergy]

theorem gcBerFugacity_zero_gap_at_fermi (β μ : ℝ) :
    gcBerFugacity β μ μ 0 = 1 := by
  unfold gcBerFugacity gcBerGappedEnergy gcBerShiftedEnergy
  simp

theorem gcSuperBerezinian_eq_ratio (β E μ Δ : ℝ) :
    gcSuperBerezinian β E μ Δ =
      (1 + gcBerFugacity β E μ Δ) / (1 - gcBerFugacity β E μ Δ) := by
  simp [gcSuperBerezinian, gcDiagonalBerezinian, gcBerFermionOddBlock,
    gcBerBosonEvenDenominator]

theorem gcSuperBerezinian_eq_product {β E μ Δ : ℝ}
    (h : gcBerFugacity β E μ Δ ≠ 1) :
    gcSuperBerezinian β E μ Δ =
      gcGappedFermionFactor β E μ Δ * gcGappedBosonFactor β E μ Δ := by
  unfold gcSuperBerezinian gcDiagonalBerezinian gcGappedFermionFactor
    gcGappedBosonFactor gcBerFermionOddBlock gcBerBosonEvenDenominator
  have hden : 1 - gcBerFugacity β E μ Δ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp [hden]

theorem gcBerezinian_boson_denominator_cancel {β E μ Δ : ℝ}
    (h : gcBerFugacity β E μ Δ ≠ 1) :
    gcBerBosonEvenDenominator β E μ Δ * gcSuperBerezinian β E μ Δ =
      gcBerFermionOddBlock β E μ Δ := by
  rw [gcSuperBerezinian_eq_product h]
  unfold gcGappedBosonFactor gcBerBosonEvenDenominator gcGappedFermionFactor
  have hden : 1 - gcBerFugacity β E μ Δ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp [hden]

theorem gcBerezinian_local_cayley (x : ℝ) :
    (1 + x) / (1 - x) =
      gcDiagonalBerezinian (1 + x) (1 - x) := by
  simp [gcDiagonalBerezinian]

/-- Consolidated finite grand-canonical Berezinian package. -/
theorem grand_canonical_berezinian_synthesis :
    (∀ μ Δ, (gcBerGappedEnergy μ μ Δ) ^ 2 = Δ ^ 2) ∧
    (∀ β μ, gcBerFugacity β μ μ 0 = 1) ∧
    (∀ β E μ Δ, gcSuperBerezinian β E μ Δ =
      (1 + gcBerFugacity β E μ Δ) / (1 - gcBerFugacity β E μ Δ)) ∧
    (∀ β E μ Δ, gcBerFugacity β E μ Δ ≠ 1 →
      gcSuperBerezinian β E μ Δ =
        gcGappedFermionFactor β E μ Δ * gcGappedBosonFactor β E μ Δ) ∧
    (∀ β E μ Δ, gcBerFugacity β E μ Δ ≠ 1 →
      gcBerBosonEvenDenominator β E μ Δ * gcSuperBerezinian β E μ Δ =
        gcBerFermionOddBlock β E μ Δ) := by
  exact ⟨gcBerGappedEnergy_at_fermi_sq, gcBerFugacity_zero_gap_at_fermi,
    gcSuperBerezinian_eq_ratio, fun β E μ Δ h => gcSuperBerezinian_eq_product h,
    fun β E μ Δ h => gcBerezinian_boson_denominator_cancel h⟩

end noncomputable section
