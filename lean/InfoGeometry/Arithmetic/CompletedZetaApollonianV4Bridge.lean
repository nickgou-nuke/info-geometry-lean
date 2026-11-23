/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
import InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
import InfoGeometry.Canonical.CompletedXiDatumInteropBridge
import InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
import InfoGeometry.Canonical.CompletedZetaPotentialSymmetryBridge
import InfoGeometry.Canonical.CompletedZetaV4CharacterBridge
import InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence
import InfoGeometry.Analysis.MellinGaussianHolomorphicWeighted
import InfoGeometry.Analysis.GammaVerticalStripBounds

/-!
# Completed Zeta, Apollonian Cayley Transform, and V4 Symmetry Bridge

## i. Overview

This module connects Mathlib's `completedRiemannZeta₀`, `completedRiemannZeta`,
and `riemannZeta` to the repository's `CompletedXiDatum`, `XiSymmetryDatum`,
centered `V4` orbit actions, Apollonian Cayley geometry, and Gaussian Mellin
archimedean factor owners without duplicating upstream Schwarz or `V4` proofs.
It makes no claim about the Riemann hypothesis, global Weil/Li equivalence,
or nonvanishing off the critical line.

## ii. Key results

- `completedRiemannZeta₀_conj`: Schwarz conjugation of entire
  `completedRiemannZeta₀` derived from `completedRiemannZeta_conj`.
- `actualCompletedZeta₀Datum` & `actualCompletedZetaDatum`: `CompletedXiDatum`
  realizations coherent with `actualCanonicalCompletedXiDatum`.
- `actualCompletedZetaXiSymmetryDatum` & `actualCompletedZeta_criticalLine_real`:
  `XiSymmetryDatum` for `completedRiemannZeta` and unconditional critical-line
  reality bridged to `actualXiSymmetryDatum_concrete`.
- `centeredV4_orbit_card_dichotomy_and_potential_invariance`: exact `{1, 2, 4}`
  `Finset.card` trichotomy for `v4CenteredPerm` orbits and `V4` potential
  invariance.
- `completedZeta_apollonian_archimedean_bridge`: joint archimedean Mellin,
  Gamma strip bound, Cayley unit-circle, and horizon-reflection bridge.

## iii. Table of contents

1. Schwarz conjugation re-exports and `completedRiemannZeta₀_conj`.
2. `CompletedXiDatum` instances and `actualCanonicalCompletedXiDatum` coherence.
3. `XiSymmetryDatum` instantiation and critical-line reality.
4. Centered `V4` orbit cardinality trichotomy and potential invariance.
5. Apollonian Cayley and archimedean Gaussian Mellin bridge.

## iv. References

- `InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge`
- `InfoGeometry.Canonical.ActualXiSymmetryDatumBridge`
- `InfoGeometry.Canonical.CompletedXiDatumInteropBridge`
- `InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation`
- `InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence`
- `InfoGeometry.Analysis.MellinGaussianHolomorphicWeighted`
- `InfoGeometry.Analysis.GammaVerticalStripBounds`
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Arithmetic.CompletedZetaApollonianV4Bridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
open InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
open InfoGeometry.Canonical.CompletedXiDatumInteropBridge
open InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation
open InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
open InfoGeometry.Canonical.CompletedZetaPotentialSymmetry
open InfoGeometry.Canonical.CompletedZetaV4Character
open InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence
open InfoGeometry.Analysis.MellinGaussianHolomorphicWeighted
open InfoGeometry.Analysis.GammaVerticalStripBounds
open InfoGeometry.Canonical.KleinFourTagRootNormalization

/-! ### 1. Schwarz Conjugation Re-exports and `completedRiemannZeta₀_conj` -/

/-- Re-export of Schwarz conjugation for Mathlib's `completedRiemannZeta`. -/
lemma completedRiemannZeta_conj_reexport (s : ℂ) :
    completedRiemannZeta (star s) = star (completedRiemannZeta s) :=
  ActualRiemannXiSchwarzBridge.completedRiemannZeta_conj s

/-- Re-export of Schwarz conjugation for `riemannXi`. -/
lemma actualRiemannXi_conj_reexport (s : ℂ) :
    riemannXi (star s) = star (riemannXi s) :=
  ActualRiemannXiSchwarzBridge.actualRiemannXi_conj s

/-- Schwarz conjugation for the entire completed zeta function
`completedRiemannZeta₀`, deduced unconditionally from `completedRiemannZeta_eq`
and `ActualRiemannXiSchwarzBridge.completedRiemannZeta_conj`. -/
lemma completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (star s) = star (completedRiemannZeta₀ s) := by
  have h0 : ∀ z : ℂ,
      completedRiemannZeta₀ z = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
    intro z
    linear_combination -completedRiemannZeta_eq z
  rw [h0 (star s), h0 s, ActualRiemannXiSchwarzBridge.completedRiemannZeta_conj s]
  simp [star_add, star_sub]

/-- Combined consistency bundle for `completedRiemannZeta_eq`, conjugation,
reflection, and entire differentiability of `completedRiemannZeta₀`. -/
lemma completedRiemannZeta_eq_conj_and_entire (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) ∧
    completedRiemannZeta (star s) =
      completedRiemannZeta₀ (star s) - 1 / star s - 1 / (1 - star s) ∧
    completedRiemannZeta₀ (star s) = star (completedRiemannZeta₀ s) ∧
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s ∧
    Differentiable ℂ completedRiemannZeta₀ :=
  ⟨completedRiemannZeta_eq s, completedRiemannZeta_eq (star s),
    completedRiemannZeta₀_conj s, completedRiemannZeta₀_one_sub s,
    differentiable_completedZeta₀⟩

/-! ### 2. `CompletedXiDatum` Instances and Coherence -/

/-- Canonical `CompletedXiDatum` realized by entire `completedRiemannZeta₀`. -/
def actualCompletedZeta₀Datum : CompletedXiDatum where
  xi := completedRiemannZeta₀
  reflection := completedRiemannZeta₀_one_sub
  schwarz := completedRiemannZeta₀_conj

/-- Canonical `CompletedXiDatum` realized by Mathlib's `completedRiemannZeta`. -/
def actualCompletedZetaDatum : CompletedXiDatum where
  xi := completedRiemannZeta
  reflection := completedRiemannZeta_one_sub
  schwarz := ActualRiemannXiSchwarzBridge.completedRiemannZeta_conj

/-- `V4`-invariance of `logModulusPotential` for both `completedRiemannZeta₀`
and `completedRiemannZeta`, together with norm-square and logarithmic coherence
with `CompletedXiDatumInteropBridge.actualCanonicalCompletedXiDatum`. -/
lemma actualCompletedZeta_v4_potential_invariance (s : ℂ) :
    (logModulusPotential actualCompletedZeta₀Datum (1 - s) =
        logModulusPotential actualCompletedZeta₀Datum s ∧
      logModulusPotential actualCompletedZeta₀Datum (star s) =
        logModulusPotential actualCompletedZeta₀Datum s ∧
      logModulusPotential actualCompletedZeta₀Datum (1 - star s) =
        logModulusPotential actualCompletedZeta₀Datum s) ∧
    (logModulusPotential actualCompletedZetaDatum (1 - s) =
        logModulusPotential actualCompletedZetaDatum s ∧
      logModulusPotential actualCompletedZetaDatum (star s) =
        logModulusPotential actualCompletedZetaDatum s ∧
      logModulusPotential actualCompletedZetaDatum (1 - star s) =
        logModulusPotential actualCompletedZetaDatum s) ∧
    actualCanonicalCompletedXiDatum.xi s =
      (1 / 2 : ℂ) * s * (s - 1) * actualCompletedZetaDatum.xi s ∧
    Complex.normSq (actualCanonicalCompletedXiDatum.xi s) =
      Complex.normSq ((1 / 2 : ℂ) * s * (s - 1)) *
        Complex.normSq (actualCompletedZetaDatum.xi s) ∧
    (s ≠ 0 → s ≠ 1 → completedRiemannZeta s ≠ 0 →
      logModulusPotential actualCanonicalCompletedXiDatum s =
        Real.log (Complex.normSq ((1 / 2 : ℂ) * s * (s - 1))) +
          logModulusPotential actualCompletedZetaDatum s) := by
  refine ⟨logModulusPotential_v4_invariant actualCompletedZeta₀Datum s,
    logModulusPotential_v4_invariant actualCompletedZetaDatum s, ?_, ?_, ?_⟩
  · rfl
  · change Complex.normSq ((1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s) =
      Complex.normSq ((1 / 2 : ℂ) * s * (s - 1)) *
        Complex.normSq (completedRiemannZeta s)
    exact map_mul Complex.normSq _ _
  · intro hs0 hs1 hcz
    have hpoly : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1)
    have hnsq_poly : Complex.normSq ((1 / 2 : ℂ) * s * (s - 1)) ≠ 0 :=
      (Complex.normSq_pos.mpr hpoly).ne'
    have hnsq_cz : Complex.normSq (completedRiemannZeta s) ≠ 0 :=
      (Complex.normSq_pos.mpr hcz).ne'
    dsimp [logModulusPotential]
    change Real.log (Complex.normSq ((1 / 2 : ℂ) * s * (s - 1) *
      completedRiemannZeta s)) = _
    rw [map_mul Complex.normSq, Real.log_mul hnsq_poly hnsq_cz]
    rfl

/-! ### 3. `XiSymmetryDatum` Instantiation and Critical-Line Reality -/

/-- Centered `XiSymmetryDatum` realized by `completedRiemannZeta (1 / 2 + u + I * tau)`. -/
def actualCompletedZetaXiSymmetryDatum : XiSymmetryDatum where
  A u tau := (completedRiemannZeta ((1 / 2 : ℂ) + ⟨u, tau⟩)).re
  B u tau := (completedRiemannZeta ((1 / 2 : ℂ) + ⟨u, tau⟩)).im
  parity_A u tau := by
    have harg : (1 / 2 : ℂ) + ⟨-u, -tau⟩ = 1 - ((1 / 2 : ℂ) + ⟨u, tau⟩) := by
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg, completedRiemannZeta_one_sub]
  parity_B u tau := by
    have harg : (1 / 2 : ℂ) + ⟨-u, -tau⟩ = 1 - ((1 / 2 : ℂ) + ⟨u, tau⟩) := by
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg, completedRiemannZeta_one_sub]
  schwarz_A u tau := by
    have harg : (1 / 2 : ℂ) + ⟨u, -tau⟩ = star ((1 / 2 : ℂ) + ⟨u, tau⟩) := by
      apply Complex.ext <;> simp
    rw [harg, ActualRiemannXiSchwarzBridge.completedRiemannZeta_conj]
    simp
  schwarz_B u tau := by
    have harg : (1 / 2 : ℂ) + ⟨u, -tau⟩ = star ((1 / 2 : ℂ) + ⟨u, tau⟩) := by
      apply Complex.ext <;> simp
    rw [harg, ActualRiemannXiSchwarzBridge.completedRiemannZeta_conj]
    simp

/-- Centered `XiSymmetryDatum` realized by entire `completedRiemannZeta₀`. -/
def actualCompletedZeta₀XiSymmetryDatum : XiSymmetryDatum where
  A u tau := (completedRiemannZeta₀ ((1 / 2 : ℂ) + ⟨u, tau⟩)).re
  B u tau := (completedRiemannZeta₀ ((1 / 2 : ℂ) + ⟨u, tau⟩)).im
  parity_A u tau := by
    have harg : (1 / 2 : ℂ) + ⟨-u, -tau⟩ = 1 - ((1 / 2 : ℂ) + ⟨u, tau⟩) := by
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg, completedRiemannZeta₀_one_sub]
  parity_B u tau := by
    have harg : (1 / 2 : ℂ) + ⟨-u, -tau⟩ = 1 - ((1 / 2 : ℂ) + ⟨u, tau⟩) := by
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg, completedRiemannZeta₀_one_sub]
  schwarz_A u tau := by
    have harg : (1 / 2 : ℂ) + ⟨u, -tau⟩ = star ((1 / 2 : ℂ) + ⟨u, tau⟩) := by
      apply Complex.ext <;> simp
    rw [harg, completedRiemannZeta₀_conj]
    simp
  schwarz_B u tau := by
    have harg : (1 / 2 : ℂ) + ⟨u, -tau⟩ = star ((1 / 2 : ℂ) + ⟨u, tau⟩) := by
      apply Complex.ext <;> simp
    rw [harg, completedRiemannZeta₀_conj]
    simp

/-- Unconditional critical-line reality for `completedRiemannZeta` and
`completedRiemannZeta₀`, together with the exact algebraic bridge to
`ActualXiSymmetryDatumBridge.actualXiSymmetryDatum_concrete`. -/
lemma actualCompletedZeta_criticalLine_real (u tau : ℝ) :
    (completedRiemannZeta ((1 / 2 : ℂ) + Complex.I * (tau : ℂ))).im = 0 ∧
    completedRiemannZeta ((1 / 2 : ℂ) + Complex.I * (tau : ℂ)) =
      ((completedRiemannZeta ((1 / 2 : ℂ) + Complex.I * (tau : ℂ))).re : ℂ) ∧
    (completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * (tau : ℂ))).im = 0 ∧
    centeredRiemannXi 0 tau = (centeredRiemannXiReal 0 tau : ℂ) ∧
    (⟨actualXiSymmetryDatum_concrete.A u tau,
        actualXiSymmetryDatum_concrete.B u tau⟩ : ℂ) =
      (1 / 2 : ℂ) * ((1 / 2 : ℂ) + ⟨u, tau⟩) * ((1 / 2 : ℂ) + ⟨u, tau⟩ - 1) *
        ⟨actualCompletedZetaXiSymmetryDatum.A u tau,
          actualCompletedZetaXiSymmetryDatum.B u tau⟩ := by
  have hc : (1 / 2 : ℂ) + ⟨0, tau⟩ = (1 / 2 : ℂ) + Complex.I * (tau : ℂ) := by
    apply Complex.ext <;> simp
  have him : (completedRiemannZeta ((1 / 2 : ℂ) + Complex.I * (tau : ℂ))).im = 0 := by
    have h := xi_imag_zero_on_critical_line actualCompletedZetaXiSymmetryDatum tau
    dsimp [actualCompletedZetaXiSymmetryDatum] at h
    rwa [hc] at h
  have him0 : (completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * (tau : ℂ))).im = 0 := by
    have h := xi_imag_zero_on_critical_line actualCompletedZeta₀XiSymmetryDatum tau
    dsimp [actualCompletedZeta₀XiSymmetryDatum] at h
    rwa [hc] at h
  have hreal : completedRiemannZeta ((1 / 2 : ℂ) + Complex.I * (tau : ℂ)) =
      ((completedRiemannZeta ((1 / 2 : ℂ) + Complex.I * (tau : ℂ))).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hxi : centeredRiemannXi 0 tau = (centeredRiemannXiReal 0 tau : ℂ) :=
    actualXiSymmetryDatum_concrete_criticalLine_real tau
  have hbridge : (⟨actualXiSymmetryDatum_concrete.A u tau,
        actualXiSymmetryDatum_concrete.B u tau⟩ : ℂ) =
      (1 / 2 : ℂ) * ((1 / 2 : ℂ) + ⟨u, tau⟩) * ((1 / 2 : ℂ) + ⟨u, tau⟩ - 1) *
        ⟨actualCompletedZetaXiSymmetryDatum.A u tau,
          actualCompletedZetaXiSymmetryDatum.B u tau⟩ := by
    have hlhs : (⟨actualXiSymmetryDatum_concrete.A u tau,
        actualXiSymmetryDatum_concrete.B u tau⟩ : ℂ) = centeredRiemannXi u tau := by
      apply Complex.ext <;> rfl
    have hrhs : (⟨actualCompletedZetaXiSymmetryDatum.A u tau,
        actualCompletedZetaXiSymmetryDatum.B u tau⟩ : ℂ) =
        completedRiemannZeta ((1 / 2 : ℂ) + ⟨u, tau⟩) := by
      apply Complex.ext <;> rfl
    have harg : (1 / 2 : ℂ) + (u : ℂ) + Complex.I * (tau : ℂ) =
        (1 / 2 : ℂ) + ⟨u, tau⟩ := by
      apply Complex.ext <;> simp
    rw [hlhs, hrhs]
    unfold centeredRiemannXi riemannXi
    rw [harg]
  exact ⟨him, hreal, him0, hxi, hbridge⟩

/-! ### 4. Centered `V4` Orbit Dichotomy and Potential Invariance -/

/-- Finite `V4` orbit of a centered coordinate `w : ℂ` under `v4CenteredPerm`. -/
def centeredV4Orbit (w : ℂ) : Finset ℂ := by
  classical
  exact Finset.image (fun g : V4 => v4CenteredPerm g w) Finset.univ

/-- Explicit four-element enumeration of `Finset.univ : Finset V4`. -/
lemma v4_univ_eq : (Finset.univ : Finset V4) = {1, v4P, v4T, v4PT} := by
  ext g
  fin_cases g <;> decide

/-- Explicit finset description `{w, -w, star w, -star w}` of `centeredV4Orbit w`. -/
lemma centeredV4Orbit_eq_finset (w : ℂ) :
    centeredV4Orbit w =
      ({w, -w, star w, -star w} : Finset ℂ) := by
  classical
  have h1 : v4CenteredPerm (1 : V4) w = w := v4CenteredPerm_id w
  have hP : v4CenteredPerm v4P w = -star w := v4CenteredPerm_P w
  have hT : v4CenteredPerm v4T w = star w := v4CenteredPerm_T w
  have hPT : v4CenteredPerm v4PT w = -w := v4CenteredPerm_PT w
  have huniv : (Finset.univ : Finset V4) = {1, v4P, v4T, v4PT} := v4_univ_eq
  ext z
  simp only [centeredV4Orbit, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨g, rfl⟩
    have hg : g ∈ ({1, v4P, v4T, v4PT} : Finset V4) := by
      rw [← huniv]
      exact Finset.mem_univ g
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · simp
    · simp [hP]
    · simp [hT]
    · simp [hPT]
  · intro hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨1, h1⟩
    · exact ⟨v4PT, hPT⟩
    · exact ⟨v4T, hT⟩
    · exact ⟨v4P, hP⟩

/-- For any `CompletedXiDatum`, `logModulusPotential` at `1 / 2 + w` is invariant
under every `g : V4` acting via `v4CenteredPerm g w`. -/
lemma logModulusPotential_v4CenteredPerm (D : CompletedXiDatum)
    (g : V4) (w : ℂ) :
    logModulusPotential D ((1 / 2 : ℂ) + v4CenteredPerm g w) =
      logModulusPotential D ((1 / 2 : ℂ) + w) := by
  have hinv := logModulusPotential_v4_invariant D ((1 / 2 : ℂ) + w)
  have huniv : g ∈ ({1, v4P, v4T, v4PT} : Finset V4) := by
    rw [← v4_univ_eq]
    exact Finset.mem_univ g
  simp only [Finset.mem_insert, Finset.mem_singleton] at huniv
  rcases huniv with rfl | rfl | rfl | rfl
  · rw [v4CenteredPerm_id]
  · rw [v4CenteredPerm_P]
    have harg : (1 / 2 : ℂ) + (-star w) = 1 - star ((1 / 2 : ℂ) + w) := by
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg]
    exact hinv.2.2
  · rw [v4CenteredPerm_T]
    have harg : (1 / 2 : ℂ) + star w = star ((1 / 2 : ℂ) + w) := by
      apply Complex.ext <;> simp
    rw [harg]
    exact hinv.2.1
  · rw [v4CenteredPerm_PT]
    have harg : (1 / 2 : ℂ) + (-w) = 1 - ((1 / 2 : ℂ) + w) := by
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg]
    exact hinv.1

/-- Exact `{1, 2, 4}` cardinality trichotomy for `centeredV4Orbit w`, paired with
open-strip invariance from `v4CenteredPerm_orbit_dichotomy_and_strip_invariance` and
`V4`-invariance of `logModulusPotential` for `actualCompletedZetaDatum` and
`actualCanonicalCompletedXiDatum`. -/
lemma centeredV4_orbit_card_dichotomy_and_potential_invariance (w : ℂ) :
    ((centeredV4Orbit w).card = 1 ↔ w = 0) ∧
    ((centeredV4Orbit w).card = 2 ↔
      (w.re = 0 ∧ w.im ≠ 0) ∨ (w.re ≠ 0 ∧ w.im = 0)) ∧
    ((centeredV4Orbit w).card = 4 ↔ w.re ≠ 0 ∧ w.im ≠ 0) ∧
    (∀ g : V4,
      (|(v4CenteredPerm g w).re| < 1 / 2 ↔ |w.re| < 1 / 2) ∧
      logModulusPotential actualCompletedZetaDatum ((1 / 2 : ℂ) + v4CenteredPerm g w) =
        logModulusPotential actualCompletedZetaDatum ((1 / 2 : ℂ) + w) ∧
      logModulusPotential actualCanonicalCompletedXiDatum
          ((1 / 2 : ℂ) + v4CenteredPerm g w) =
        logModulusPotential actualCanonicalCompletedXiDatum ((1 / 2 : ℂ) + w)) := by
  classical
  have hcard4_of : w.re ≠ 0 → w.im ≠ 0 → (centeredV4Orbit w).card = 4 := by
    intro hre him
    have hinj := v4CenteredPerm_orbit_dichotomy_and_strip_invariance.2.1 w hre him
    have hfv : Fintype.card V4 = 4 := by decide
    change (Finset.image (fun g : V4 => v4CenteredPerm g w) Finset.univ).card = 4
    rw [Finset.card_image_of_injective Finset.univ hinj, Finset.card_univ, hfv]
  have hcard2_re : w.re = 0 → w.im ≠ 0 → (centeredV4Orbit w).card = 2 := by
    intro hre him
    have hstar : star w = -w := by
      apply Complex.ext <;> simp [hre]
    have hne : w ≠ -w := by
      intro heq
      have him0 := congrArg Complex.im heq
      simp at him0
      exact him (by linarith)
    have hset : centeredV4Orbit w = ({w, -w} : Finset ℂ) := by
      rw [centeredV4Orbit_eq_finset]
      ext z
      simp [hstar]
      tauto
    rw [hset, Finset.card_pair hne]
  have hcard2_im : w.re ≠ 0 → w.im = 0 → (centeredV4Orbit w).card = 2 := by
    intro hre him
    have hstar : star w = w := by
      apply Complex.ext <;> simp [him]
    have hne : w ≠ -w := by
      intro heq
      have hre0 := congrArg Complex.re heq
      simp at hre0
      exact hre (by linarith)
    have hset : centeredV4Orbit w = ({w, -w} : Finset ℂ) := by
      rw [centeredV4Orbit_eq_finset]
      ext z
      simp [hstar]
    rw [hset, Finset.card_pair hne]
  have hcard1_of : w = 0 → (centeredV4Orbit w).card = 1 := by
    intro hw
    subst hw
    have hset : centeredV4Orbit 0 = ({0} : Finset ℂ) := by
      rw [centeredV4Orbit_eq_finset]
      ext z
      simp
    rw [hset, Finset.card_singleton]
  have h1 : (centeredV4Orbit w).card = 1 ↔ w = 0 := by
    constructor
    · intro hcard
      by_cases hre : w.re = 0 <;> by_cases him : w.im = 0
      · exact Complex.ext hre him
      · rw [hcard2_re hre him] at hcard; contradiction
      · rw [hcard2_im hre him] at hcard; contradiction
      · rw [hcard4_of hre him] at hcard; contradiction
    · exact hcard1_of
  have h2 : (centeredV4Orbit w).card = 2 ↔
      (w.re = 0 ∧ w.im ≠ 0) ∨ (w.re ≠ 0 ∧ w.im = 0) := by
    constructor
    · intro hcard
      by_cases hre : w.re = 0 <;> by_cases him : w.im = 0
      · have hw0 : w = 0 := Complex.ext hre him
        rw [hcard1_of hw0] at hcard
        contradiction
      · exact Or.inl ⟨hre, him⟩
      · exact Or.inr ⟨hre, him⟩
      · rw [hcard4_of hre him] at hcard
        contradiction
    · rintro (⟨hre, him⟩ | ⟨hre, him⟩)
      · exact hcard2_re hre him
      · exact hcard2_im hre him
  have h4 : (centeredV4Orbit w).card = 4 ↔ w.re ≠ 0 ∧ w.im ≠ 0 := by
    constructor
    · intro hcard
      by_cases hre : w.re = 0 <;> by_cases him : w.im = 0
      · have hw0 : w = 0 := Complex.ext hre him
        rw [hcard1_of hw0] at hcard
        contradiction
      · rw [hcard2_re hre him] at hcard
        contradiction
      · rw [hcard2_im hre him] at hcard
        contradiction
      · exact ⟨hre, him⟩
    · rintro ⟨hre, him⟩
      exact hcard4_of hre him
  refine ⟨h1, h2, h4, fun g => ?_⟩
  exact ⟨v4CenteredPerm_orbit_dichotomy_and_strip_invariance.2.2.1 g w,
    logModulusPotential_v4CenteredPerm actualCompletedZetaDatum g w,
    logModulusPotential_v4CenteredPerm actualCanonicalCompletedXiDatum g w⟩

/-! ### 5. Apollonian Cayley and Archimedean Gaussian Mellin Bridge -/

/-- Exact definitional coincidence of `WeilLiKreinGhostEquivalence.apollonianDiskMap`
and `ApollonianBipolarCayleyV4Dilation.apollonianCayleyW`. -/
lemma apollonianDiskMap_eq_apollonianCayleyW (w : ℂ) :
    apollonianDiskMap w = apollonianCayleyW w :=
  rfl

/-- Joint archimedean Mellin, functional-equation, Schwarz, Apollonian unit-circle,
horizon-reflection, Gamma vertical-strip bound, and critical-line reality bridge. -/
lemma completedZeta_apollonian_archimedean_bridge {s w : ℂ}
    (hs0 : s ≠ 0) (hs_re : 0 < s.re) (hw : CriticalLine ((1 / 2 : ℂ) + w)) :
    riemannZeta s = completedRiemannZeta s / Gammaℝ s ∧
    mellin (fun t : ℝ ↦ (Real.exp (-Real.pi * t ^ 2) : ℂ)) s =
      (2 : ℂ)⁻¹ * ((Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)) ∧
    2 * mellin (fun t : ℝ ↦ (Real.exp (-Real.pi * t ^ 2) : ℂ)) s = Gammaℝ s ∧
    completedRiemannZeta (1 - s) = completedRiemannZeta s ∧
    completedRiemannZeta (star s) = star (completedRiemannZeta s) ∧
    apollonianDiskMap w = apollonianCayleyW w ∧
    Complex.normSq (apollonianDiskMap w) = 1 ∧
    apollonianDiskMap (horizonReflect w) = (star (apollonianDiskMap w))⁻¹ ∧
    ‖(Complex.Gamma ((1 / 2 : ℂ) + w))⁻¹‖ ≤
      Real.exp (Real.pi * |((1 / 2 : ℂ) + w).im| / 2) ∧
    centeredRiemannXi 0 w.im = (centeredRiemannXiReal 0 w.im : ℂ) ∧
    riemannXi ((1 / 2 : ℂ) + w) = (centeredRiemannXiReal 0 w.im : ℂ) := by
  have hmellin := mellin_gaussian Real.pi_pos hs_re
  have h2mellin :
      2 * mellin (fun t : ℝ ↦ (Real.exp (-Real.pi * t ^ 2) : ℂ)) s = Gammaℝ s := by
    rw [hmellin, ← mul_assoc, mul_inv_cancel₀ (by norm_num), one_mul, Complex.Gammaℝ_def,
      ← neg_div]
  have hw_re : w.re = 0 := (criticalLine_centered_iff_re_eq_zero w).mp hw
  have hnsq : Complex.normSq (apollonianDiskMap w) = 1 :=
    (normSq_apollonianDiskMap_eq_one_iff_re_eq_zero w).mpr hw_re
  have hxi_real := actualXiSymmetryDatum_concrete_criticalLine_real w.im
  have hxi_w : riemannXi ((1 / 2 : ℂ) + w) = (centeredRiemannXiReal 0 w.im : ℂ) := by
    have hw_eq : (1 / 2 : ℂ) + w = (1 / 2 : ℂ) + (0 : ℝ) + Complex.I * (w.im : ℂ) := by
      apply Complex.ext <;> simp [hw_re]
    rw [hw_eq]
    exact hxi_real
  exact ⟨riemannZeta_def_of_ne_zero hs0, hmellin, h2mellin,
    completedRiemannZeta_one_sub s,
    ActualRiemannXiSchwarzBridge.completedRiemannZeta_conj s,
    apollonianDiskMap_eq_apollonianCayleyW w, hnsq,
    apollonianDiskMap_horizonReflect w,
    norm_inv_Gamma_half ((1 / 2 : ℂ) + w) hw,
    hxi_real, hxi_w⟩

end InfoGeometry.Arithmetic.CompletedZetaApollonianV4Bridge
