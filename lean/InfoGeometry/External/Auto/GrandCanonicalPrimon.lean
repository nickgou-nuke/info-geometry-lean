import Mathlib.Tactic

/-!
# Grand Canonical Bosonic and Fermionic Primon Ensembles

Finite scalar grand-canonical layer.

For a mode of energy `E`, chemical potential `μ`, and inverse temperature `β`,
set

`ξ = E - μ`, `x = exp (-β * ξ)`.

Then the local finite formulas are:

* fermion: `Z_F = 1 + x`;
* boson truncated at occupation cutoff `K`: `Z_B,K = Σ_{k=0}^K x^k`;
* boson infinite geometric chart, away from `x = 1`: `Z_B = 1 / (1 - x)`.

This file keeps the bosonic infinite factor as a local geometric chart, not an
analytic convergence theorem.
-/

noncomputable section

def gcShiftedEnergy (E μ : ℝ) : ℝ :=
  E - μ

def gcFugacity (β E μ : ℝ) : ℝ :=
  Real.exp (-(β * gcShiftedEnergy E μ))

def gcFermionLocalPartition (β E μ : ℝ) : ℝ :=
  1 + gcFugacity β E μ

def gcBosonTruncatedPartition (β E μ : ℝ) (K : ℕ) : ℝ :=
  (Finset.range (K + 1)).sum fun k => (gcFugacity β E μ) ^ k

def gcBosonGeometricPartition (β E μ : ℝ) : ℝ :=
  (1 - gcFugacity β E μ)⁻¹

def gcGappedEnergy (E μ Δ : ℝ) : ℝ :=
  Real.sqrt ((gcShiftedEnergy E μ) ^ 2 + Δ ^ 2)

def gcGappedFugacity (β E μ Δ : ℝ) : ℝ :=
  Real.exp (-(β * gcGappedEnergy E μ Δ))

def gcGappedFermionPartition (β E μ Δ : ℝ) : ℝ :=
  1 + gcGappedFugacity β E μ Δ

def gcGappedBosonGeometricPartition (β E μ Δ : ℝ) : ℝ :=
  (1 - gcGappedFugacity β E μ Δ)⁻¹

def gcTwoFermionPartition (β E₁ E₂ μ : ℝ) : ℝ :=
  gcFermionLocalPartition β E₁ μ * gcFermionLocalPartition β E₂ μ

def gcTwoBosonTruncatedPartition (β E₁ E₂ μ : ℝ) (K : ℕ) : ℝ :=
  gcBosonTruncatedPartition β E₁ μ K * gcBosonTruncatedPartition β E₂ μ K

theorem gcShiftedEnergy_at_fermi (μ : ℝ) :
    gcShiftedEnergy μ μ = 0 := by
  simp [gcShiftedEnergy]

theorem gcFugacity_at_fermi (β μ : ℝ) :
    gcFugacity β μ μ = 1 := by
  simp [gcFugacity, gcShiftedEnergy]

theorem gcFermionLocalPartition_at_fermi (β μ : ℝ) :
    gcFermionLocalPartition β μ μ = 2 := by
  simp [gcFermionLocalPartition, gcFugacity_at_fermi]
  norm_num

theorem gcGappedEnergy_sq {E μ Δ : ℝ}
    (h : 0 ≤ (gcShiftedEnergy E μ) ^ 2 + Δ ^ 2) :
    (gcGappedEnergy E μ Δ) ^ 2 = (gcShiftedEnergy E μ) ^ 2 + Δ ^ 2 := by
  unfold gcGappedEnergy
  exact Real.sq_sqrt h

theorem gcGappedEnergy_at_fermi_sq (μ Δ : ℝ) :
    (gcGappedEnergy μ μ Δ) ^ 2 = Δ ^ 2 := by
  have hnonneg : 0 ≤ (gcShiftedEnergy μ μ) ^ 2 + Δ ^ 2 := by positivity
  rw [gcGappedEnergy_sq hnonneg]
  simp [gcShiftedEnergy]

theorem gcGappedEnergy_zero_gap_at_fermi (μ : ℝ) :
    gcGappedEnergy μ μ 0 = 0 := by
  unfold gcGappedEnergy gcShiftedEnergy
  simp

theorem gcGappedFugacity_zero_gap_at_fermi (β μ : ℝ) :
    gcGappedFugacity β μ μ 0 = 1 := by
  simp [gcGappedFugacity, gcGappedEnergy_zero_gap_at_fermi]

theorem gcGappedFermionPartition_zero_gap_at_fermi (β μ : ℝ) :
    gcGappedFermionPartition β μ μ 0 = 2 := by
  simp [gcGappedFermionPartition, gcGappedFugacity_zero_gap_at_fermi]
  norm_num

theorem gcGappedEnergy_dominates_gap (E μ Δ : ℝ) :
    |Δ| ≤ gcGappedEnergy E μ Δ := by
  unfold gcGappedEnergy
  have hle : Δ ^ 2 ≤ (gcShiftedEnergy E μ) ^ 2 + Δ ^ 2 := by
    nlinarith [sq_nonneg (gcShiftedEnergy E μ)]
  have habs : Real.sqrt (Δ ^ 2) = |Δ| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [← habs]
  exact Real.sqrt_le_sqrt hle

theorem gcBosonTruncatedPartition_zero (β E μ : ℝ) :
    gcBosonTruncatedPartition β E μ 0 = 1 := by
  simp [gcBosonTruncatedPartition]

theorem gcBosonTruncatedPartition_succ (β E μ : ℝ) (K : ℕ) :
    gcBosonTruncatedPartition β E μ (K + 1) =
      gcBosonTruncatedPartition β E μ K + (gcFugacity β E μ) ^ (K + 1) := by
  simp [gcBosonTruncatedPartition, Finset.sum_range_succ]

theorem finite_geometric_identity {x : ℝ} (hx : x ≠ 1) (K : ℕ) :
    (Finset.range (K + 1)).sum (fun k => x ^ k) =
      (1 - x ^ (K + 1)) / (1 - x) := by
  induction K with
  | zero =>
      have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      simp
      field_simp [hden]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      field_simp [hden]
      ring

theorem gcBosonTruncatedPartition_geometric {β E μ : ℝ}
    (h : gcFugacity β E μ ≠ 1) (K : ℕ) :
    gcBosonTruncatedPartition β E μ K =
      (1 - (gcFugacity β E μ) ^ (K + 1)) / (1 - gcFugacity β E μ) := by
  exact finite_geometric_identity h K

theorem gcFermionTwoModeExpansion (β E₁ E₂ μ : ℝ) :
    gcTwoFermionPartition β E₁ E₂ μ =
      1 + gcFugacity β E₁ μ + gcFugacity β E₂ μ +
        gcFugacity β E₁ μ * gcFugacity β E₂ μ := by
  unfold gcTwoFermionPartition gcFermionLocalPartition
  ring

theorem gcBosonTwoModeProduct (β E₁ E₂ μ : ℝ) (K : ℕ) :
    gcTwoBosonTruncatedPartition β E₁ E₂ μ K =
      gcBosonTruncatedPartition β E₁ μ K *
        gcBosonTruncatedPartition β E₂ μ K := by
  rfl

theorem gcBosonGeometric_local {β E μ : ℝ} (h : gcFugacity β E μ ≠ 1) :
    (1 - gcFugacity β E μ) * gcBosonGeometricPartition β E μ = 1 := by
  unfold gcBosonGeometricPartition
  field_simp [sub_ne_zero.mpr (Ne.symm h)]

theorem gcGappedBosonGeometric_local {β E μ Δ : ℝ}
    (h : gcGappedFugacity β E μ Δ ≠ 1) :
    (1 - gcGappedFugacity β E μ Δ) *
      gcGappedBosonGeometricPartition β E μ Δ = 1 := by
  unfold gcGappedBosonGeometricPartition
  field_simp [sub_ne_zero.mpr (Ne.symm h)]

/-- Consolidated grand-canonical primon package. -/
theorem grand_canonical_primon_synthesis :
    (∀ μ, gcShiftedEnergy μ μ = 0) ∧
    (∀ β μ, gcFugacity β μ μ = 1) ∧
    (∀ β μ, gcFermionLocalPartition β μ μ = 2) ∧
    (∀ μ Δ, (gcGappedEnergy μ μ Δ) ^ 2 = Δ ^ 2) ∧
    (∀ μ, gcGappedEnergy μ μ 0 = 0) ∧
    (∀ β μ, gcGappedFermionPartition β μ μ 0 = 2) ∧
    (∀ E μ Δ, |Δ| ≤ gcGappedEnergy E μ Δ) ∧
    (∀ β E μ, gcBosonTruncatedPartition β E μ 0 = 1) ∧
    (∀ β E μ K, gcBosonTruncatedPartition β E μ (K + 1) =
      gcBosonTruncatedPartition β E μ K + (gcFugacity β E μ) ^ (K + 1)) ∧
    (∀ β E₁ E₂ μ, gcTwoFermionPartition β E₁ E₂ μ =
      1 + gcFugacity β E₁ μ + gcFugacity β E₂ μ +
        gcFugacity β E₁ μ * gcFugacity β E₂ μ) ∧
    (∀ β E μ, gcFugacity β E μ ≠ 1 →
      (1 - gcFugacity β E μ) * gcBosonGeometricPartition β E μ = 1) ∧
    (∀ β E μ Δ, gcGappedFugacity β E μ Δ ≠ 1 →
      (1 - gcGappedFugacity β E μ Δ) *
        gcGappedBosonGeometricPartition β E μ Δ = 1) := by
  exact ⟨gcShiftedEnergy_at_fermi, gcFugacity_at_fermi,
    gcFermionLocalPartition_at_fermi, gcGappedEnergy_at_fermi_sq,
    gcGappedEnergy_zero_gap_at_fermi, gcGappedFermionPartition_zero_gap_at_fermi,
    gcGappedEnergy_dominates_gap, gcBosonTruncatedPartition_zero,
    gcBosonTruncatedPartition_succ, gcFermionTwoModeExpansion,
    fun β E μ h => gcBosonGeometric_local h,
    fun β E μ Δ h => gcGappedBosonGeometric_local h⟩

end noncomputable section
