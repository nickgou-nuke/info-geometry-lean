/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite formal core of the cuprate FL* claims

This owner records the algebraic and finite-dimensional content of the
Sachdev cuprate slides without promoting experimental interpretations to
unconditional theorems.  Normalized Fermi-surface areas are real numbers;
the Brillouin-zone normalization is part of the declared interface.

The Hubbard, ancilla, and AFL* definitions below are finite operator/model
interfaces.  An exact microscopic equivalence or an empirical fit requires
additional maps or data and is intentionally not asserted here.
-/

noncomputable section

namespace InfoGeometry.Physics.CuprateFLStarFormalization

open scoped BigOperators Matrix
open InfoGeometry.Algebra.FiniteSpin

/-! ## Density and pocket bookkeeping -/

/-- Chemical hole-carrier density in the one-band cuprate convention. -/
def chemicalHoleDensity (p : ℝ) : ℝ := 1 + p

/-- Hall density in the convention used by the slides. -/
def hallDensity (p : ℝ) : ℝ := p

/-- Conventional spin-degenerate Luttinger area, normalized by the Brillouin-zone area. -/
def conventionalLuttingerArea (p : ℝ) : ℝ := chemicalHoleDensity p / 2

/-- Area assigned to one FL* hole pocket. -/
def flStarPocketArea (p : ℝ) : ℝ := p / 8

/-- Area assigned to one thermal SDW pocket. -/
def thermalSDWPocketArea (p : ℝ) : ℝ := p / 4

/-- Total normalized area of the four FL* pockets. -/
def flStarTotalPocketArea (p : ℝ) : ℝ := 4 * flStarPocketArea p

@[simp] theorem chemicalHoleDensity_eq (p : ℝ) :
    chemicalHoleDensity p = 1 + p := rfl

@[simp] theorem hallDensity_eq (p : ℝ) : hallDensity p = p := rfl

@[simp] theorem conventionalLuttingerArea_eq (p : ℝ) :
    conventionalLuttingerArea p = (1 + p) / 2 := by
  rfl

@[simp] theorem flStarPocketArea_eq (p : ℝ) :
    flStarPocketArea p = p / 8 := rfl

@[simp] theorem thermalSDWPocketArea_eq (p : ℝ) :
    thermalSDWPocketArea p = p / 4 := rfl

@[simp] theorem flStarTotalPocketArea_eq (p : ℝ) :
    flStarTotalPocketArea p = p / 2 := by
  dsimp [flStarTotalPocketArea, flStarPocketArea]
  ring

/-- The FL* pocket total differs from the conventional `1 + p` count by one
filled spin-degenerate band, at the normalized-area level. -/
theorem conventional_minus_flStar_total (p : ℝ) :
    conventionalLuttingerArea p - flStarTotalPocketArea p = 1 / 2 := by
  dsimp [conventionalLuttingerArea, chemicalHoleDensity,
    flStarTotalPocketArea, flStarPocketArea]
  ring

/-- The numerical pocket areas quoted on the `p = 0.1` slide. -/
theorem pocket_areas_at_one_tenth :
    flStarPocketArea (1 / 10) = 1 / 80 ∧
      thermalSDWPocketArea (1 / 10) = 1 / 40 := by
  norm_num [flStarPocketArea, thermalSDWPocketArea]

/-- Four pockets of area `p/8` have total area `p/2`. -/
theorem four_flStar_pockets_total (p : ℝ) :
    (∑ _ : Fin 4, flStarPocketArea p) = flStarTotalPocketArea p := by
  simp [flStarTotalPocketArea]

/-- A finite family of four explicitly equal pocket areas has the same total. -/
theorem four_equal_pocket_areas_total (p : ℝ) (a : Fin 4 → ℝ)
    (ha : ∀ i, a i = flStarPocketArea p) :
    ∑ i, a i = p / 2 := by
  simp_rw [ha]
  simp [flStarPocketArea]
  ring

/-! ## The anisotropic pocket dispersion -/

/-- In-plane anisotropic quadratic dispersion with an optional interlayer term. -/
def pocketDispersion (m₁ m₂ tInter c kₓ kᵧ k_z : ℝ) : ℝ :=
  kₓ ^ 2 / (2 * m₁) + kᵧ ^ 2 / (2 * m₂) +
    2 * tInter * Real.cos (k_z * c)

/-- The in-plane dispersion is the `tInter = 0` specialization. -/
def inPlaneDispersion (m₁ m₂ kₓ kᵧ : ℝ) : ℝ :=
  kₓ ^ 2 / (2 * m₁) + kᵧ ^ 2 / (2 * m₂)

theorem pocketDispersion_zero_interlayer (m₁ m₂ c kₓ kᵧ k_z : ℝ) :
    pocketDispersion m₁ m₂ 0 c kₓ kᵧ k_z = inPlaneDispersion m₁ m₂ kₓ kᵧ := by
  simp [pocketDispersion, inPlaneDispersion]

theorem pocketDispersion_interlayer_term (m₁ m₂ tInter c kₓ kᵧ k_z : ℝ) :
    pocketDispersion m₁ m₂ tInter c kₓ kᵧ k_z -
        inPlaneDispersion m₁ m₂ kₓ kᵧ =
      2 * tInter * Real.cos (k_z * c) := by
  simp [pocketDispersion, inPlaneDispersion]

/-! ## Luttinger bookkeeping and d-wave symmetry -/

/-- Normalized Fermi volume before quotienting by filled bands. -/
def luttVolume (K n : ℝ) : ℝ := K * n

/-- The FL* volume after subtracting one local moment per unit cell. -/
def flStarVolume (K n localMoments : ℝ) : ℝ := K * (n - localMoments)

/-- Equality modulo a declared filled-band period. -/
def equivalentModulo (period x y : ℝ) : Prop :=
  ∃ k : ℤ, x - y = (k : ℝ) * period

theorem equivalentModulo_refl (period x : ℝ) : equivalentModulo period x x := by
  refine ⟨0, ?_⟩
  simp

theorem luttVolume_one_local_moment_gap (K n : ℝ) :
    luttVolume K n - flStarVolume K n 1 = K := by
  dsimp [luttVolume, flStarVolume]
  ring

theorem luttVolume_formula (K n : ℝ) : luttVolume K n = K * n := rfl

theorem flStarVolume_formula (K n localMoments : ℝ) :
    flStarVolume K n localMoments = K * (n - localMoments) := rfl

/-- Nearest-neighbor d-wave form factor. -/
def dWaveGap (delta kₓ kᵧ : ℝ) : ℝ :=
  delta * (Real.cos kₓ - Real.cos kᵧ)

theorem dWaveGap_swap (delta kₓ kᵧ : ℝ) :
    dWaveGap delta kᵧ kₓ = -dWaveGap delta kₓ kᵧ := by
  dsimp [dWaveGap]
  ring

theorem dWaveGap_diagonal (delta k : ℝ) : dWaveGap delta k k = 0 := by
  simp [dWaveGap]

theorem dWaveGap_antidiagonal (delta k : ℝ) :
    dWaveGap delta k (-k) = 0 := by
  simp [dWaveGap, Real.cos_neg]

/-! ## A finite Hubbard operator interface -/

/-- Operators on a finite Fock-space surrogate.  The index `i` is a finite
lattice site and `s` is the two-valued spin index. -/
abbrev HubbardOperator (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Number operator associated with an annihilation-operator family. -/
def numberOperator {N d : ℕ}
    (c : Fin N → Fin 2 → HubbardOperator d) (i : Fin N) (s : Fin 2) :
    HubbardOperator d :=
  (c i s).conjTranspose * c i s

/-- Finite Hubbard Hamiltonian with hopping and on-site interaction terms.
The CAR relations and the physical Fock representation are separate
hypotheses, rather than hidden in this definition. -/
def hubbardHamiltonian {N d : ℕ}
    (t : Fin N → Fin N → ℂ)
    (c : Fin N → Fin 2 → HubbardOperator d)
    (U : ℝ) : HubbardOperator d :=
  -∑ i, ∑ j, ∑ s, (t i j) •
      ((c i s).conjTranspose * c j s) +
    (U : ℂ) • ∑ i,
      numberOperator c i 0 * numberOperator c i 1

@[simp] theorem numberOperator_def {N d : ℕ}
    (c : Fin N → Fin 2 → HubbardOperator d) (i : Fin N) (s : Fin 2) :
    numberOperator c i s = (c i s).conjTranspose * c i s := rfl

theorem hubbardHamiltonian_eq_hopping_add_interaction {N d : ℕ}
    (t : Fin N → Fin N → ℂ)
    (c : Fin N → Fin 2 → HubbardOperator d)
    (U : ℝ) :
    hubbardHamiltonian t c U =
      (-∑ i, ∑ j, ∑ s, (t i j) •
        ((c i s).conjTranspose * c j s)) +
      (U : ℂ) • ∑ i,
        numberOperator c i 0 * numberOperator c i 1 := by
  rfl

/-- A finite spin-density family, abstracting the three Pauli components of
`c† σ c` without silently identifying it with an unrelated carrier. -/
abbrev SpinDensity (N d : ℕ) := Fin N → Fin 3 → HubbardOperator d

/-- Kondo coupling of an ancilla spin family to a finite spin-density family. -/
def kondoCoupling {N d : ℕ}
    (sf : Fin N → Fin 3 → HubbardOperator d)
    (spinDensity : SpinDensity N d) (JK : ℝ) : HubbardOperator d :=
  (JK / 2 : ℂ) • ∑ i, ∑ a, sf i a * spinDensity i a

/-- Rung exchange between the two ancilla spin layers. -/
def rungExchange {N d : ℕ}
    (sf sg : Fin N → Fin 3 → HubbardOperator d)
    (Jperp : ℝ) : HubbardOperator d :=
  (Jperp : ℂ) • ∑ i, ∑ a, sf i a * sg i a

/-- Finite ancilla-layer Hamiltonian.  Its operator relations are supplied by
separate CAR and spin-representation hypotheses. -/
def ancillaLayerHamiltonian {N d : ℕ}
    (t : Fin N → Fin N → ℂ)
    (c : Fin N → Fin 2 → HubbardOperator d)
    (sf sg : Fin N → Fin 3 → HubbardOperator d)
    (spinDensity : SpinDensity N d) (U JK Jperp : ℝ) : HubbardOperator d :=
  hubbardHamiltonian t c U + kondoCoupling sf spinDensity JK +
    rungExchange sf sg Jperp

theorem ancillaLayerHamiltonian_eq_three_terms {N d : ℕ}
    (t : Fin N → Fin N → ℂ)
    (c : Fin N → Fin 2 → HubbardOperator d)
    (sf sg : Fin N → Fin 3 → HubbardOperator d)
    (spinDensity : SpinDensity N d) (U JK Jperp : ℝ) :
    ancillaLayerHamiltonian t c sf sg spinDensity U JK Jperp =
      hubbardHamiltonian t c U + kondoCoupling sf spinDensity JK +
        rungExchange sf sg Jperp := by
  rfl

/-- The algebraic scaling relation `J_K² / J_⊥ = U`, with its necessary
nonzero-denominator hypothesis made explicit. -/
theorem kondo_scaling_ratio {JK Jperp U : ℝ}
    (hJperp : Jperp ≠ 0) (hscale : JK ^ 2 = U * Jperp) :
    JK ^ 2 / Jperp = U := by
  field_simp
  nlinarith

/-! ## Rung singlet projector -/

abbrev TwoSiteOperator := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The two-spin swap operator. -/
def spinSwap : TwoSiteOperator :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

theorem spinSwap_sq : spinSwap * spinSwap = (1 : TwoSiteOperator) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    spinSwap, Matrix.one_apply, Prod.mk.injEq]
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;> norm_num

/-- Projector onto the antisymmetric two-spin sector (the rung singlet
sector in the two-spin representation). -/
def rungSingletProjector : TwoSiteOperator :=
  ((1 : ℂ) / 2) • ((1 : TwoSiteOperator) - spinSwap)

theorem rungSingletProjector_idempotent :
    rungSingletProjector * rungSingletProjector = rungSingletProjector := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [rungSingletProjector, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, spinSwap, Matrix.one_apply, Prod.mk.injEq]
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;> norm_num

/-! ## FL/FL* hybridization distinction -/

/-- The hybridization order parameter used to distinguish the two variational
sectors in the slides. -/
def isFLStar (hybridization : ℝ) : Prop := hybridization = 0

def isFL (hybridization : ℝ) : Prop := hybridization ≠ 0

theorem flStar_or_fl (hybridization : ℝ) :
    isFLStar hybridization ∨ isFL hybridization := by
  by_cases h : hybridization = 0
  · exact Or.inl h
  · exact Or.inr h

theorem not_both_flStar_and_fl (hybridization : ℝ) :
    ¬ (isFLStar hybridization ∧ isFL hybridization) := by
  intro h
  exact h.2 h.1

/-! ## Finite AFL* parameter interface -/

/-- The order parameters retained by the finite AFL* mean-field interface. -/
structure AFLStarParameters where
  deltaC : ℝ
  deltaF : ℝ
  deltaG : ℝ
  hybridCF : ℝ
  hybridFG : ℝ
  hoppingG : ℝ

/-- The finite parameter conditions displayed for the superconducting phase. -/
def isDWaveSuperconductor (P : AFLStarParameters) : Prop :=
  P.deltaC ≠ 0 ∧ P.deltaF ≠ 0 ∧ P.deltaG ≠ 0

/-- The pseudogap FL* sector has no `c-f` hybridization in the displayed
mean-field parametrization. -/
def isFLStarPseudogap (P : AFLStarParameters) : Prop :=
  P.hybridCF = 0 ∧ P.hybridFG ≠ 0

theorem dWaveSuperconductor_requires_nonzero_pairings
    (P : AFLStarParameters) (hP : isDWaveSuperconductor P) :
    P.deltaC ≠ 0 ∧ P.deltaF ≠ 0 ∧ P.deltaG ≠ 0 := hP

theorem flStarPseudogap_has_zero_cf_hybridization
    (P : AFLStarParameters) (hP : isFLStarPseudogap P) :
    P.hybridCF = 0 := hP.1

end InfoGeometry.Physics.CuprateFLStarFormalization
