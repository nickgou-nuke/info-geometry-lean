/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinFourTagRootNormalization
import InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
import InfoGeometry.Arithmetic.RiemannXiV4CharacterBridge
import InfoGeometry.Algebra.BostConnesKMSPhaseTransition
import InfoGeometry.Quantum.BerryKeatingCCR
import InfoGeometry.QuantumGeometry.BerryKeatingDilationBridge

/-!
# Apollonian Bipolar Cayley Map, V₄ Dilation Adjoint Anomaly, and Bost–Connes Strip Alignment

This module formalizes the arithmetic and quantum-geometric synthesis connecting
the centered Apollonian Cayley transform, the dilation adjoint anomaly, Bost–Connes KMS
phase transitions, and the Klein four-group `V4` orbit structure:

1. **Star-Algebra Dilation Adjoint Anomaly & `Mat2C` Witnesses**:
   Reuses `InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne` alongside self-adjoint
   non-commutativity and the finite-dimensional CCR trace obstruction on `Mat2C`.
   Proves `dilationGen_star_adjoint_anomaly` (`star D = -D - 1`) and
   `berryKeatingH_selfAdjoint_from_dilation` connecting to
   `InfoGeometry.Quantum.BerryKeatingCCR.berryKeatingH` and `BerryKeatingDilationBridge`.
2. **Centered Bost–Connes KMS Strip Alignment (`bostConnes_centered_strip_alignment`)**:
   Under `w = s - 1/2`, aligns `BostConnesKMSPhaseTransition.isHighTemperaturePhase`
   (`0 < s.re ∧ s.re ≤ 1`) and `isLowTemperaturePhase` (`1 < s.re`) with the centered
   strip `-1/2 < w.re ∧ w.re ≤ 1/2` and half-plane `1/2 < w.re`.
3. **Centered `V4` Action & Orbit Dichotomy (`v4CenteredPerm_orbit_dichotomy_and_strip_invariance`)**:
   Constructs `v4CenteredPerm : V4 →* Equiv.Perm ℂ` (`id ↦ w`, `P ↦ -star w`, `T ↦ star w`,
   `PT ↦ -w`), proving the critical-line 2-point orbit collapse, off-line 4-point injectivity,
   open-strip invariance `|·.re| < 1/2`, and boundary flip `PT (1/2 + I * t) = -1/2 - I * t`.
4. **Apollonian Bipolar Cayley Geometry (`apollonianCayleyW_bipolar_circle_and_halfplane`,
   `apollonianCayleyW_antiholomorphic_and_fn26_link`)**:
   Defines `apollonianCayleyW w := (w - 1/2) / (w + 1/2)` (`= zetaDiskCoordinate (centeredToS w)`),
   proving `‖w + 1/2‖² - ‖w - 1/2‖² = 2 * w.re`, unconditional `OnLeeYangCircle (A w) ↔ w.re = 0`,
   pole-guarded disk/exterior equivalences, inversion `A(-w) = (A w)⁻¹`, and antiholomorphic
   reflection `A(-star w) = (starRingEnd ℂ (A w))⁻¹` linked to
   `klein_fn26_unit_circle_inversion_not_holomorphic_moebius`.
5. **Finite Xian-Jin Li Summand Positivity (`finite_li_kernel_circle_nonneg_and_offCircle_neg_witness`)**:
   Proves `0 ≤ ((1 - z^n) + (1 - (z⁻¹)^n)).re` on `normSq z = 1`, contrasted with the
   off-circle negative witness at `z = 1/2, n = 2` (`-9/4 < 0`).

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

set_option autoImplicit false

namespace InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation

open InfoGeometry.Canonical.KleinFourTagRootNormalization
open InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms

/-! ## Section 0: Noncommutativity Ground Witnesses (T16) -/

section NoncommWitness

/-- Standard elementary nilpotent matrix `E₀₁` over `ℂ`. -/
def matE01_C : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- Standard elementary nilpotent matrix `E₁₀` over `ℂ`. -/
def matE10_C : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- OpenGauss Trap T16: Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem matE01_mul_E10_ne_mul_E10_E01_C :
    matE01_C * matE10_C ≠ matE10_C * matE01_C := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [matE01_C, matE10_C, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- T16 witness reused from `FiniteSpinAlgebra`: `J_plus` and `J_minus` do not commute in `Mat2C`. -/
theorem mat2C_j_plus_j_minus_ne :
    InfoGeometry.Algebra.FiniteSpin.J_plus * InfoGeometry.Algebra.FiniteSpin.J_minus ≠
      InfoGeometry.Algebra.FiniteSpin.J_minus * InfoGeometry.Algebra.FiniteSpin.J_plus :=
  InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne

/-- T17 concrete `StarRing`/`StarModule ℂ` witness on `Mat2C`: `J_zero` and `J_plus + J_minus`
are self-adjoint (`star M = M`) and non-commuting. -/
theorem mat2C_starRing_selfAdjoint_noncomm_witness :
    star InfoGeometry.Algebra.FiniteSpin.J_zero = InfoGeometry.Algebra.FiniteSpin.J_zero ∧
    star (InfoGeometry.Algebra.FiniteSpin.J_plus + InfoGeometry.Algebra.FiniteSpin.J_minus) =
      InfoGeometry.Algebra.FiniteSpin.J_plus + InfoGeometry.Algebra.FiniteSpin.J_minus ∧
    InfoGeometry.Algebra.FiniteSpin.J_zero *
        (InfoGeometry.Algebra.FiniteSpin.J_plus + InfoGeometry.Algebra.FiniteSpin.J_minus) ≠
      (InfoGeometry.Algebra.FiniteSpin.J_plus + InfoGeometry.Algebra.FiniteSpin.J_minus) *
        InfoGeometry.Algebra.FiniteSpin.J_zero := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.star_eq_conjTranspose, InfoGeometry.Algebra.FiniteSpin.J_zero]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.star_eq_conjTranspose, InfoGeometry.Algebra.FiniteSpin.J_plus,
        InfoGeometry.Algebra.FiniteSpin.J_minus]
  · intro h
    have h01 := congrArg (fun M : InfoGeometry.Algebra.FiniteSpin.Mat2C => M 0 1) h
    norm_num [InfoGeometry.Algebra.FiniteSpin.J_zero,
      InfoGeometry.Algebra.FiniteSpin.J_plus,
      InfoGeometry.Algebra.FiniteSpin.J_minus,
      Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Finite-dimensional CCR trace obstruction (Wielandt–Wintner): `Mat2C` cannot satisfy
`[x, p] = I • 1`, justifying the abstract `[Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]`
formulation. -/
theorem mat2C_ccr_trace_obstruction (x p : InfoGeometry.Algebra.FiniteSpin.Mat2C) :
    x * p - p * x ≠ Complex.I • (1 : InfoGeometry.Algebra.FiniteSpin.Mat2C) := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_mul_comm x p, sub_self,
    Matrix.trace_smul, Matrix.trace_one] at ht
  norm_num at ht

end NoncommWitness

/-! ## Section 1: Dilation Adjoint Anomaly in Star Algebras -/

section DilationAnomaly

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The dilation generator `D := I • (x * p)`. -/
noncomputable def dilationGen (x p : A) : A :=
  Complex.I • (x * p)

/-- The symmetrized Berry–Keating Hamiltonian `H_BK := -I • (D + 1/2 • 1)`. -/
noncomputable def berryKeatingHam (x p : A) : A :=
  (-Complex.I) • (dilationGen x p + (1/2 : ℂ) • (1 : A))

/-- Master theorem: Dilation generator satisfies `star D = -D - 1`, and `H_BK` is self-adjoint. -/
theorem dilationGen_star_adjoint_anomaly (x p : A)
    (hx : star x = x) (hp : star p = p)
    (hccr : x * p - p * x = Complex.I • (1 : A)) :
    star (dilationGen x p) = - dilationGen x p - 1 ∧
    star (dilationGen x p + (1/2 : ℂ) • (1 : A)) = - (dilationGen x p + (1/2 : ℂ) • (1 : A)) ∧
    star (berryKeatingHam x p) = berryKeatingHam x p := by
  have hstar_I : star Complex.I = -Complex.I := Complex.conj_I
  have hpx : p * x = x * p - Complex.I • (1 : A) := by
    calc p * x = x * p - (x * p - p * x) := by noncomm_ring
      _ = x * p - Complex.I • (1 : A) := by rw [hccr]
  have hstar_D : star (dilationGen x p) = - dilationGen x p - 1 := by
    dsimp [dilationGen]
    rw [star_smul, star_mul, hp, hx, hstar_I, hpx]
    calc (-Complex.I) • (x * p - Complex.I • (1 : A))
      _ = (-Complex.I) • (x * p) - (-Complex.I) • (Complex.I • (1 : A)) := by
        rw [smul_sub]
      _ = - (Complex.I • (x * p)) - ((-Complex.I) * Complex.I) • (1 : A) := by
        rw [neg_smul, smul_smul]
      _ = - dilationGen x p - (1 : ℂ) • (1 : A) := by
        have : (-Complex.I) * Complex.I = 1 := by
          calc (-Complex.I) * Complex.I = - (Complex.I * Complex.I) := by ring
            _ = - (-1) := by rw [Complex.I_mul_I]
            _ = 1 := by ring
        rw [this]
        rfl
      _ = - dilationGen x p - 1 := by rw [one_smul]
  have hstar_skew : star (dilationGen x p + (1/2 : ℂ) • (1 : A)) = - (dilationGen x p + (1/2 : ℂ) • (1 : A)) := by
    rw [star_add, hstar_D, star_smul, star_one]
    have hstar_half : star (1/2 : ℂ) = (1/2 : ℂ) := by
      norm_num
    rw [hstar_half]
    calc (- dilationGen x p - 1) + (1/2 : ℂ) • (1 : A)
      _ = - dilationGen x p - (1 : ℂ) • (1 : A) + (1/2 : ℂ) • (1 : A) := by
        rw [one_smul]
      _ = - dilationGen x p + (-(1 : ℂ) + 1/2) • (1 : A) := by
        rw [one_smul]
        module
      _ = - dilationGen x p + (-(1/2 : ℂ)) • (1 : A) := by
        have : -(1 : ℂ) + 1/2 = -(1/2) := by ring
        rw [this]
      _ = - (dilationGen x p + (1/2 : ℂ) • (1 : A)) := by
        rw [neg_smul, neg_add]
  have hstar_ham : star (berryKeatingHam x p) = berryKeatingHam x p := by
    dsimp [berryKeatingHam]
    rw [star_smul, hstar_skew]
    have : star (-Complex.I) = Complex.I := by
      calc star (-Complex.I) = - star Complex.I := star_neg Complex.I
        _ = - (-Complex.I) := by rw [hstar_I]
        _ = Complex.I := neg_neg Complex.I
    rw [this, smul_neg, neg_smul]
  exact ⟨hstar_D, hstar_skew, hstar_ham⟩

/-- `BerryKeatingCCR.berryKeatingH` equals `-I • (dilationGen x p + 1/2 • 1)` under CCR
`[x, p] = I • 1`, and is self-adjoint (`star H = H`) as a consequence of the dilation anomaly. -/
theorem berryKeatingH_selfAdjoint_from_dilation (x p : A)
    (hx : star x = x) (hp : star p = p)
    (hccr : InfoGeometry.Quantum.BerryKeatingCCR.commutator x p = Complex.I • (1 : A)) :
    (-Complex.I) • (dilationGen x p + (1 / 2 : ℂ) • (1 : A)) =
        InfoGeometry.Quantum.BerryKeatingCCR.berryKeatingH x p ∧
      star (InfoGeometry.Quantum.BerryKeatingCCR.berryKeatingH x p) =
        InfoGeometry.Quantum.BerryKeatingCCR.berryKeatingH x p := by
  have h_norm := InfoGeometry.Quantum.BerryKeatingCCR.berry_keating_normal_ordered x p hccr
  have h_eq : (-Complex.I) • (dilationGen x p + (1 / 2 : ℂ) • (1 : A)) =
      InfoGeometry.Quantum.BerryKeatingCCR.berryKeatingH x p := by
    rw [h_norm]
    unfold dilationGen
    rw [smul_add, smul_smul, smul_smul]
    have h_mul_I : (-Complex.I) * Complex.I = (1 : ℂ) := by
      calc (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by ring
        _ = -(-1) := by rw [Complex.I_mul_I]
        _ = 1 := by ring
    have h_mul_half : (-Complex.I) * (1 / 2 : ℂ) = -(Complex.I / 2 : ℂ) := by ring
    rw [h_mul_I, h_mul_half, one_smul, neg_smul, ← sub_eq_add_neg]
  have h_anom := (dilationGen_star_adjoint_anomaly x p hx hp hccr).2.1
  have h_sa : star (InfoGeometry.Quantum.BerryKeatingCCR.berryKeatingH x p) =
      InfoGeometry.Quantum.BerryKeatingCCR.berryKeatingH x p := by
    rw [← h_eq, star_smul, h_anom]
    have h_star_negI : star (-Complex.I) = Complex.I := by
      rw [star_neg, show star Complex.I = -Complex.I from Complex.conj_I, neg_neg]
    rw [h_star_negI, smul_neg, neg_smul]
  exact ⟨h_eq, h_sa⟩

end DilationAnomaly

section DilationDerivation

/-- The dilation-shifted Hamiltonian `berryKeatingHam` coincides with the owner
`InfoGeometry.Quantum.BerryKeatingCCR.berryKeatingH` under the CCR `[x, p] = I • 1`. -/
theorem berryKeatingHam_eq_berryKeatingH {A : Type*} [Ring A] [Algebra ℂ A] (x p : A)
    (hccr : InfoGeometry.Quantum.BerryKeatingCCR.commutator x p = Complex.I • (1 : A)) :
    berryKeatingHam x p = InfoGeometry.Quantum.BerryKeatingCCR.berryKeatingH x p := by
  have h_norm := InfoGeometry.Quantum.BerryKeatingCCR.berry_keating_normal_ordered x p hccr
  rw [h_norm]
  unfold berryKeatingHam dilationGen
  rw [smul_add, smul_smul, smul_smul]
  have h_mul_I : (-Complex.I) * Complex.I = (1 : ℂ) := by
    calc (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by ring
      _ = -(-1) := by rw [Complex.I_mul_I]
      _ = 1 := by ring
  have h_mul_half : (-Complex.I) * (1 / 2 : ℂ) = -(Complex.I / 2 : ℂ) := by ring
  rw [h_mul_I, h_mul_half, one_smul, neg_smul, ← sub_eq_add_neg]

/-- Under `D K = 1` and `ħ = 1`, the derivation-lane `physicalHamiltonian` from
`BerryKeatingDilationBridge` matches the shifted Euler form `-I • (opEuler K D X + (1/2) • X)`. -/
theorem physicalHamiltonian_unit_hbar_eq_euler_shift {A : Type*} [Ring A] [Algebra ℂ A]
    (D : InfoGeometry.QuantumGeometry.BerryKeating.ComplexDerivation A)
    (K X : A) (hDK : D K = 1) :
    InfoGeometry.QuantumGeometry.BerryKeating.physicalHamiltonian 1 D K X =
      (-Complex.I) •
        (InfoGeometry.QuantumGeometry.BerryKeating.opEuler K D X + (1 / 2 : ℂ) • X) := by
  unfold InfoGeometry.QuantumGeometry.BerryKeating.physicalHamiltonian
  rw [InfoGeometry.QuantumGeometry.BerryKeating.dimensionlessBK_eq_euler_add_half D K hDK X]
  norm_num

end DilationDerivation

/-! ## Section 2: Bost–Connes KMS Strip Alignment -/

section BostConnesStrip

/-- Coordinate transformation mapping `s` in the standard critical strip to centered `w = s - 1/2`. -/
noncomputable def sToCentered (s : ℂ) : ℂ :=
  s - (1/2 : ℂ)

/-- Inverse transformation mapping centered `w` to `s = w + 1/2`. -/
noncomputable def centeredToS (w : ℂ) : ℂ :=
  w + (1/2 : ℂ)

@[simp] theorem sToCentered_centeredToS (w : ℂ) : sToCentered (centeredToS w) = w := by
  dsimp [sToCentered, centeredToS]
  ring

@[simp] theorem centeredToS_sToCentered (s : ℂ) : centeredToS (sToCentered s) = s := by
  dsimp [sToCentered, centeredToS]
  ring

/-- Master theorem: Critical strip `0 < s.re ∧ s.re ≤ 1` aligns with `-1/2 < w.re ∧ w.re ≤ 1/2`. -/
theorem bostConnes_centered_strip_alignment (s : ℂ) :
    (0 < s.re ∧ s.re ≤ 1) ↔ (-1/2 < (sToCentered s).re ∧ (sToCentered s).re ≤ 1/2) := by
  change (0 < s.re ∧ s.re ≤ 1) ↔
    (-1/2 < (s - (1/2 : ℂ)).re ∧ (s - (1/2 : ℂ)).re ≤ 1/2)
  have hRe : (s - (1/2 : ℂ)).re = s.re - (1/2 : ℝ) := by
    rw [Complex.sub_re]
    norm_num
  rw [hRe]
  constructor
  · intro ⟨h1, h2⟩
    constructor <;> linarith
  · intro ⟨h1, h2⟩
    constructor <;> linarith

/-- High-temperature Bost–Connes phase `0 < s.re ≤ 1` aligns with the centered strip
`-1/2 < (sToCentered s).re ≤ 1/2`. -/
theorem bostConnes_highTemp_centered_iff (s : ℂ) :
    InfoGeometry.Algebra.BostConnesKMSPhaseTransition.isHighTemperaturePhase s.re ↔
      (-1 / 2 < (sToCentered s).re ∧ (sToCentered s).re ≤ 1 / 2) :=
  bostConnes_centered_strip_alignment s

/-- Low-temperature Bost–Connes phase `1 < s.re` aligns with `1/2 < (sToCentered s).re`. -/
theorem bostConnes_lowTemp_centered_iff (s : ℂ) :
    InfoGeometry.Algebra.BostConnesKMSPhaseTransition.isLowTemperaturePhase s.re ↔
      1 / 2 < (sToCentered s).re := by
  dsimp [InfoGeometry.Algebra.BostConnesKMSPhaseTransition.isLowTemperaturePhase, sToCentered]
  have hhalf : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  constructor <;> intro h <;> linarith

/-- Inverse alignment in centered `w` coordinates via `centeredToS w`. -/
theorem bostConnes_centered_strip_alignment_centeredToS (w : ℂ) :
    InfoGeometry.Algebra.BostConnesKMSPhaseTransition.isHighTemperaturePhase (centeredToS w).re ↔
      (-1 / 2 < w.re ∧ w.re ≤ 1 / 2) := by
  have h := bostConnes_centered_strip_alignment (centeredToS w)
  rw [sToCentered_centeredToS w] at h
  exact h

/-- Disjointness of high- and low-temperature Bost–Connes phases in centered coordinates. -/
theorem bostConnes_centered_phases_disjoint (s : ℂ) :
    ¬ ((-1 / 2 < (sToCentered s).re ∧ (sToCentered s).re ≤ 1 / 2) ∧
        1 / 2 < (sToCentered s).re) := by
  rw [← bostConnes_highTemp_centered_iff s, ← bostConnes_lowTemp_centered_iff s]
  exact InfoGeometry.Algebra.BostConnesKMSPhaseTransition.phase_stratification_disjoint s.re

end BostConnesStrip

/-! ## Section 3: Centered V₄ Action & Orbit Dichotomy -/

section V4Orbit

/-- Action of `V4` on centered coordinates `ℂ`:
`id ↦ w`, parity `P ↦ -star w`, time-reversal `T ↦ star w`, and `PT ↦ -w`. -/
def v4Action (tag : V4) (w : ℂ) : ℂ :=
  if tag.toAdd = InfoGeometry.Geometry.KleinFourTag.id then w
  else if tag.toAdd = InfoGeometry.Geometry.KleinFourTag.P then - starRingEnd ℂ w
  else if tag.toAdd = InfoGeometry.Geometry.KleinFourTag.T then starRingEnd ℂ w
  else -w

private def v4Id : V4 := Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.id
private def v4Sigma1 : V4 := Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P
private def v4Sigma2 : V4 := Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T
private def v4Sigma3 : V4 := Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT

/-- Public `V4` generators matching `KleinFourTag`: parity `v4P`, time-reversal `v4T`,
and functional-equation involution `v4PT`. -/
def v4P : V4 := Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P
def v4T : V4 := Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T
def v4PT : V4 := Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT

/-- On the critical line `w.re = 0`, parity `P` fixes `w` and `T` acts as `-w`,
collapsing the `V4` orbit to `{w, -w}`. -/
theorem v4_critical_line_orbit_collapse (w : ℂ) (h : w.re = 0) :
    v4Action v4Sigma1 w = w ∧ v4Action v4Sigma2 w = -w := by
  have hw_star : starRingEnd ℂ w = -w := by
    apply Complex.ext
    · simp [h]
    · simp
  simp [v4Action, v4Sigma2, v4Sigma1, hw_star,
    InfoGeometry.Geometry.KleinFourTag.id, InfoGeometry.Geometry.KleinFourTag.T,
    InfoGeometry.Geometry.KleinFourTag.P]

/-- Off the critical line and real axis (`w.re ≠ 0 ∧ w.im ≠ 0`), the V₄ orbit has 4 distinct points. -/
theorem v4_off_line_orbit_four_distinct (w : ℂ) (hre : w.re ≠ 0) (him : w.im ≠ 0) :
    v4Action v4Id w ≠ v4Action v4Sigma1 w ∧
    v4Action v4Id w ≠ v4Action v4Sigma2 w ∧
    v4Action v4Id w ≠ v4Action v4Sigma3 w ∧
    v4Action v4Sigma1 w ≠ v4Action v4Sigma2 w ∧
    v4Action v4Sigma1 w ≠ v4Action v4Sigma3 w ∧
    v4Action v4Sigma2 w ≠ v4Action v4Sigma3 w := by
  unfold v4Action v4Id v4Sigma1 v4Sigma2 v4Sigma3
  simp only [toAdd_ofAdd,
    InfoGeometry.Geometry.KleinFourTag.id, InfoGeometry.Geometry.KleinFourTag.P,
    InfoGeometry.Geometry.KleinFourTag.T, InfoGeometry.Geometry.KleinFourTag.PT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have hh := congrArg Complex.re h; simp at hh; apply hre; linarith
  · intro h; have hh := congrArg Complex.im h; simp at hh; apply him; linarith
  · intro h; have hh := congrArg Complex.re h; simp at hh; apply hre; linarith
  · intro h; have hh := congrArg Complex.re h; simp at hh; apply hre; linarith
  · intro h; have hh := congrArg Complex.im h; simp at hh; apply him; linarith
  · intro h; have hh := congrArg Complex.re h; simp at hh; apply hre; linarith

/-- Action of `V4Group` on centered complex coordinates `ℂ`:
`I ↦ w`, `W1 ↦ -star w` (`P`), `W2 ↦ star w` (`T`), `W12 ↦ -w` (`PT`). -/
def v4GroupApply : InfoGeometry.Topology.V4RootSystem.V4Group → ℂ → ℂ
  | .I => fun w => w
  | .W1 => fun w => -star w
  | .W2 => fun w => star w
  | .W12 => fun w => -w

theorem v4GroupApply_involutive (g : InfoGeometry.Topology.V4RootSystem.V4Group) (w : ℂ) :
    v4GroupApply g (v4GroupApply g w) = w := by
  cases g <;> simp [v4GroupApply, star_neg]

theorem v4GroupApply_mul (g h : InfoGeometry.Topology.V4RootSystem.V4Group) (w : ℂ) :
    v4GroupApply (g * h) w = v4GroupApply g (v4GroupApply h w) := by
  change v4GroupApply (InfoGeometry.Topology.V4RootSystem.v4_mul g h) w =
    v4GroupApply g (v4GroupApply h w)
  cases g <;> cases h <;> simp [v4GroupApply, InfoGeometry.Topology.V4RootSystem.v4_mul, star_neg]

/-- Group homomorphism `V4Group →* Equiv.Perm ℂ`. -/
def v4GroupToPerm : InfoGeometry.Topology.V4RootSystem.V4Group →* Equiv.Perm ℂ where
  toFun g :=
    { toFun := v4GroupApply g
      invFun := v4GroupApply g
      left_inv := v4GroupApply_involutive g
      right_inv := v4GroupApply_involutive g }
  map_one' := by
    ext w
    rfl
  map_mul' g h := by
    ext w
    exact v4GroupApply_mul g h w

/-- Group homomorphism `V4 →* Equiv.Perm ℂ` in centered coordinates `w = s - 1/2`. -/
def v4CenteredPerm : V4 →* Equiv.Perm ℂ :=
  v4GroupToPerm.comp v4RootHom

@[simp] theorem v4CenteredPerm_id (w : ℂ) : v4CenteredPerm (1 : V4) w = w := by
  rw [map_one]
  rfl

@[simp] theorem v4CenteredPerm_P (w : ℂ) : v4CenteredPerm v4P w = -star w := by
  dsimp [v4CenteredPerm, v4P, v4RootHom]
  rw [v4RootMap_P]
  rfl

@[simp] theorem v4CenteredPerm_T (w : ℂ) : v4CenteredPerm v4T w = star w := by
  dsimp [v4CenteredPerm, v4T, v4RootHom]
  rw [v4RootMap_T]
  rfl

@[simp] theorem v4CenteredPerm_PT (w : ℂ) : v4CenteredPerm v4PT w = -w := by
  dsimp [v4CenteredPerm, v4PT, v4RootHom]
  rw [v4RootMap_PT]
  rfl

/-- Every element of `v4CenteredPerm` preserves `|w.re|`. -/
theorem v4CenteredPerm_abs_re (g : V4) (w : ℂ) :
    |(v4CenteredPerm g w).re| = |w.re| := by
  dsimp [v4CenteredPerm, v4GroupToPerm]
  cases v4RootHom g <;> simp [v4GroupApply, abs_neg]

/-- `V4` orbit dichotomy and open-strip invariance in centered coordinates `w = s - 1/2`:
1. On `w.re = 0`, `P` fixes `w`, `PT w = T w`, and `T w ≠ w` whenever `w.im ≠ 0`.
2. Off `w.re = 0` and `w.im = 0`, `g ↦ v4CenteredPerm g w` is injective (4-point orbit).
3. Every `g : V4` preserves the centered open critical strip `|w.re| < 1/2`.
4. `PT` exchanges the strip boundaries `1/2 + I * t` and `-1/2 - I * t`. -/
theorem v4CenteredPerm_orbit_dichotomy_and_strip_invariance :
    (∀ w : ℂ, w.re = 0 →
      v4CenteredPerm v4P w = w ∧
      v4CenteredPerm v4PT w = v4CenteredPerm v4T w ∧
      (w.im ≠ 0 → v4CenteredPerm v4T w ≠ w)) ∧
    (∀ w : ℂ, w.re ≠ 0 → w.im ≠ 0 →
      Function.Injective (fun g : V4 => v4CenteredPerm g w)) ∧
    (∀ (g : V4) (w : ℂ),
      (|(v4CenteredPerm g w).re| < 1 / 2 ↔ |w.re| < 1 / 2)) ∧
    (∀ t : ℝ,
      v4CenteredPerm v4PT ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) =
        -(1 / 2 : ℂ) - Complex.I * (t : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    have hP : v4CenteredPerm v4P w = w := by
      rw [v4CenteredPerm_P]
      apply Complex.ext
      · simp [hw]
      · simp
    have hPT : v4CenteredPerm v4PT w = v4CenteredPerm v4T w := by
      rw [v4CenteredPerm_PT, v4CenteredPerm_T]
      apply Complex.ext
      · simp [hw]
      · simp
    refine ⟨hP, hPT, ?_⟩
    intro him hTw
    rw [v4CenteredPerm_T] at hTw
    have him' := congrArg Complex.im hTw
    simp at him'
    apply him
    linarith
  · intro w hre him g h hgh
    apply v4RootEquiv.injective
    have hgh' : v4GroupToPerm (v4RootEquiv g) w = v4GroupToPerm (v4RootEquiv h) w := hgh
    cases hg : v4RootEquiv g <;> cases hh : v4RootEquiv h <;> rw [hg, hh] at hgh'
    all_goals
      first
      | rfl
      | (exfalso; have h1 := congrArg Complex.re hgh';
          simp [v4GroupToPerm, v4GroupApply] at h1; apply hre; linarith)
      | (exfalso; have h1 := congrArg Complex.im hgh';
          simp [v4GroupToPerm, v4GroupApply] at h1; apply him; linarith)
  · intro g w
    rw [v4CenteredPerm_abs_re]
  · intro t
    rw [v4CenteredPerm_PT]
    ring

end V4Orbit

/-! ## Section 4: Apollonian Bipolar Cayley Geometry -/

section ApollonianCayley

/-- The centered Apollonian Cayley map `A(w) := (w - 1/2) / (w + 1/2)`. -/
noncomputable def apollonianCayleyW (w : ℂ) : ℂ :=
  (w - (1/2 : ℂ)) / (w + (1/2 : ℂ))

/-- Difference of squared distances to the bipolar foci `±1/2` equals `2 * w.re`. -/
theorem normSq_bipolar_diff (w : ℂ) :
    Complex.normSq (w + (1/2 : ℂ)) - Complex.normSq (w - (1/2 : ℂ)) = 2 * w.re := by
  have h1 : (w + (1/2 : ℂ)).re = w.re + 1/2 := by
    rw [Complex.add_re]
    norm_num
  have h2 : (w + (1/2 : ℂ)).im = w.im := by
    rw [Complex.add_im]
    norm_num
  have h3 : (w - (1/2 : ℂ)).re = w.re - 1/2 := by
    rw [Complex.sub_re]
    norm_num
  have h4 : (w - (1/2 : ℂ)).im = w.im := by
    rw [Complex.sub_im]
    norm_num
  simp only [Complex.normSq_apply]
  rw [h1, h2, h3, h4]
  ring

/-- The image of `w` under the Apollonian Cayley map lies on the unit circle if and only if `w.re = 0`. -/
theorem apollonianCayleyW_unit_circle_iff (w : ℂ) (hw : w + (1/2 : ℂ) ≠ 0) :
    Complex.normSq (apollonianCayleyW w) = 1 ↔ w.re = 0 := by
  dsimp [apollonianCayleyW]
  rw [map_div₀]
  have hden : Complex.normSq (w + (1/2 : ℂ)) ≠ 0 := by
    intro hz
    apply hw
    exact Complex.normSq_eq_zero.mp hz
  rw [div_eq_one_iff_eq hden]
  have hdiff := normSq_bipolar_diff w
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- The guarded unit-circle statement in the repository's Lee–Yang predicate. -/
theorem apollonianCayleyW_leeYang_iff (w : ℂ) (hw : w + (1/2 : ℂ) ≠ 0) :
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnLeeYangCircle
      (apollonianCayleyW w) ↔ w.re = 0 :=
  apollonianCayleyW_unit_circle_iff w hw

/-- Unconditional Lee–Yang unit-circle characterization `OnLeeYangCircle (A w) ↔ w.re = 0`
(valid at `w = -1/2` because `A(-1/2) = 0` is not on the unit circle). -/
theorem apollonianCayleyW_leeYang_iff_unconditional (w : ℂ) :
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnLeeYangCircle
      (apollonianCayleyW w) ↔ w.re = 0 := by
  by_cases hw : w + (1 / 2 : ℂ) = 0
  · have hre : w.re = -(1 / 2 : ℝ) := by
      have hw' := congrArg Complex.re hw
      simp only [Complex.add_re, Complex.zero_re] at hw'
      have hhalf : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
      linarith
    have hA : apollonianCayleyW w = 0 := by
      dsimp [apollonianCayleyW]
      rw [hw, div_zero]
    constructor
    · intro hly
      exfalso
      rw [InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnLeeYangCircle,
        hA, Complex.normSq_zero] at hly
      norm_num at hly
    · intro hzero
      exfalso
      linarith
  · exact apollonianCayleyW_leeYang_iff w hw

/-- The bipolar equal-distance locus is precisely the imaginary axis.

This formulation is independent of division and remains valid at the Cayley pole. -/
theorem apollonian_bipolar_equidistance_iff (w : ℂ) :
    ‖w - (1/2 : ℂ)‖ = ‖w + (1/2 : ℂ)‖ ↔ w.re = 0 := by
  have hsq : ‖w - (1/2 : ℂ)‖ ^ 2 = ‖w + (1/2 : ℂ)‖ ^ 2 ↔ w.re = 0 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    have hdiff := normSq_bipolar_diff w
    constructor <;> intro h <;> linarith
  constructor
  · intro h
    apply hsq.mp
    rw [h]
  · intro h
    have h' := hsq.mpr h
    nlinarith [norm_nonneg (w - (1 / 2 : ℂ)), norm_nonneg (w + (1 / 2 : ℂ))]

/-- The Cayley image is in the open unit disk exactly on the right half-plane.

The nonzero denominator hypothesis is essential because Lean's field division is total. -/
theorem apollonianCayleyW_disk_iff (w : ℂ) (hw : w + (1/2 : ℂ) ≠ 0) :
    ‖apollonianCayleyW w‖ < 1 ↔ 0 < w.re := by
  have hden : 0 < Complex.normSq (w + (1/2 : ℂ)) :=
    Complex.normSq_pos.mpr hw
  have hsq : Complex.normSq (apollonianCayleyW w) < 1 ↔ 0 < w.re := by
    rw [apollonianCayleyW, Complex.normSq_div]
    rw [div_lt_one hden]
    have hdiff := normSq_bipolar_diff w
    constructor <;> intro h <;> linarith
  have hnorm (z : ℂ) : ‖z‖ < 1 ↔ Complex.normSq z < 1 := by
    rw [← Complex.sq_norm]
    constructor <;> intro h <;> nlinarith [norm_nonneg z]
  rw [hnorm, hsq]

/-- The Cayley image is outside the closed unit disk exactly on the left half-plane. -/
theorem apollonianCayleyW_exterior_iff (w : ℂ) (hw : w + (1/2 : ℂ) ≠ 0) :
    1 < ‖apollonianCayleyW w‖ ↔ w.re < 0 := by
  have hden : 0 < Complex.normSq (w + (1/2 : ℂ)) :=
    Complex.normSq_pos.mpr hw
  have hsq : 1 < Complex.normSq (apollonianCayleyW w) ↔ w.re < 0 := by
    rw [apollonianCayleyW, Complex.normSq_div]
    rw [one_lt_div hden]
    have hdiff := normSq_bipolar_diff w
    constructor <;> intro h <;> linarith
  have hnorm (z : ℂ) : 1 < ‖z‖ ↔ 1 < Complex.normSq z := by
    rw [← Complex.sq_norm]
    constructor <;> intro h <;> nlinarith [norm_nonneg z]
  rw [hnorm, hsq]

/-- The denominator guard cannot be dropped: at the pole, total division sends
the bipolar Cayley map to zero although the point lies in the left half-plane. -/
theorem apollonianCayleyW_pole_counterexample :
    apollonianCayleyW (-(1/2 : ℂ)) = 0 ∧
      ¬ (‖apollonianCayleyW (-(1/2 : ℂ))‖ < 1 ↔
          0 < (-(1/2 : ℂ)).re) ∧
      ¬ (1 < ‖apollonianCayleyW (-(1/2 : ℂ))‖ ↔
          (-(1/2 : ℂ)).re < 0) := by
  constructor
  · norm_num [apollonianCayleyW]
  · constructor <;> norm_num [apollonianCayleyW]

/-- Re-centering the standard `s` coordinate identifies the bipolar Cayley map
with the existing zeta disk coordinate. -/
theorem apollonianCayleyW_sToCentered (s : ℂ) :
    apollonianCayleyW (sToCentered s) =
      InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge.zetaDiskCoordinate s := by
  change ((s - (1 / 2 : ℂ)) - (1 / 2 : ℂ)) /
      ((s - (1 / 2 : ℂ)) + (1 / 2 : ℂ)) = (s - 1) / s
  congr 1 <;> ring

/-- The inverse coordinate change gives the same zeta disk coordinate identity. -/
theorem apollonianCayleyW_centeredToS (w : ℂ) :
    apollonianCayleyW w =
      InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge.zetaDiskCoordinate (centeredToS w) := by
  have h := apollonianCayleyW_sToCentered (centeredToS w)
  rw [sToCentered_centeredToS w] at h
  exact h

/-- Inversion identity: `A(-w) = (A(w))⁻¹`. -/
theorem apollonianCayleyW_neg (w : ℂ) :
    apollonianCayleyW (-w) = (apollonianCayleyW w)⁻¹ := by
  dsimp [apollonianCayleyW]
  have hnum : -w - (1/2 : ℂ) = - (w + (1/2 : ℂ)) := by ring
  have hdenom : -w + (1/2 : ℂ) = - (w - (1/2 : ℂ)) := by ring
  rw [hnum, hdenom, neg_div_neg_eq]
  rw [inv_div]

/-- Anti-holomorphic reflection identity: `A(-star w) = (star (A w))⁻¹`. -/
theorem apollonianCayleyW_neg_star (w : ℂ) :
    apollonianCayleyW (- starRingEnd ℂ w) = (starRingEnd ℂ (apollonianCayleyW w))⁻¹ := by
  dsimp [apollonianCayleyW]
  have hnum : - starRingEnd ℂ w - (1/2 : ℂ) = - starRingEnd ℂ (w + (1/2 : ℂ)) := by
    rw [Complex.ext_iff]
    constructor
    · simp
      ring
    · simp
  have hdenom : - starRingEnd ℂ w + (1/2 : ℂ) = - starRingEnd ℂ (w - (1/2 : ℂ)) := by
    rw [Complex.ext_iff]
    constructor
    · simp
      ring
    · simp
  rw [hnum, hdenom, neg_div_neg_eq, map_div₀, inv_div]

/-- Consolidated Apollonian bipolar Cayley circle and half-plane theorem:
coordinate alignment with `zetaDiskCoordinate`, bipolar normSq difference `2 * w.re`,
equidistance locus, unconditional `OnLeeYangCircle`, pole-guarded open disk and exterior,
and inversion identity `A(-w) = (A w)⁻¹`. -/
theorem apollonianCayleyW_bipolar_circle_and_halfplane :
    (∀ s : ℂ, apollonianCayleyW (sToCentered s) =
      InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge.zetaDiskCoordinate s) ∧
    (∀ w : ℂ, apollonianCayleyW w =
      InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge.zetaDiskCoordinate (centeredToS w)) ∧
    (∀ w : ℂ, Complex.normSq (w + (1 / 2 : ℂ)) - Complex.normSq (w - (1 / 2 : ℂ)) =
      2 * w.re) ∧
    (∀ w : ℂ, ‖w - (1 / 2 : ℂ)‖ = ‖w + (1 / 2 : ℂ)‖ ↔ w.re = 0) ∧
    (∀ w : ℂ, InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnLeeYangCircle
      (apollonianCayleyW w) ↔ w.re = 0) ∧
    (∀ w : ℂ, w + (1 / 2 : ℂ) ≠ 0 → (‖apollonianCayleyW w‖ < 1 ↔ 0 < w.re)) ∧
    (∀ w : ℂ, w + (1 / 2 : ℂ) ≠ 0 → (1 < ‖apollonianCayleyW w‖ ↔ w.re < 0)) ∧
    (∀ w : ℂ, apollonianCayleyW (-w) = (apollonianCayleyW w)⁻¹) :=
  ⟨apollonianCayleyW_sToCentered,
   apollonianCayleyW_centeredToS,
   normSq_bipolar_diff,
   apollonian_bipolar_equidistance_iff,
   apollonianCayleyW_leeYang_iff_unconditional,
   apollonianCayleyW_disk_iff,
   apollonianCayleyW_exterior_iff,
   apollonianCayleyW_neg⟩

/-- Unconditional antiholomorphic reflection `A(-star w) = (starRingEnd ℂ (A w))⁻¹`
paired with Klein's Footnote 26 obstruction showing that `z ↦ (starRingEnd ℂ z)⁻¹` is not
realized by any non-degenerate holomorphic Möbius transformation. -/
theorem apollonianCayleyW_antiholomorphic_and_fn26_link :
    (∀ w : ℂ,
      apollonianCayleyW (-star w) = (starRingEnd ℂ (apollonianCayleyW w))⁻¹) ∧
    ((∀ z : ℂ, z ≠ 0 →
      ((0 : ℂ) * starRingEnd ℂ z + 1) / ((1 : ℂ) * starRingEnd ℂ z + 0) =
        (starRingEnd ℂ z)⁻¹) ∧
      ¬ ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
        ∀ z : ℂ, z ≠ 0 → c * z + d ≠ 0 ∧
          (a * z + b) / (c * z + d) = (starRingEnd ℂ z)⁻¹) :=
  ⟨fun w => apollonianCayleyW_neg_star w,
   klein_fn26_unit_circle_inversion_not_holomorphic_moebius⟩

end ApollonianCayley

/-! ## Section 5: Finite Xian-Jin Li Summand Positivity -/

section LiCriterion

/-- For any point `z` on the unit circle `‖z‖ = 1`, the symmetric Li summand is non-negative. -/
theorem finite_li_kernel_circle_nonneg (z : ℂ) (n : ℕ) (hz : Complex.normSq z = 1) :
    0 ≤ ((1 - z^n) + (1 - (z⁻¹)^n)).re := by
  have hz_inv : z⁻¹ = starRingEnd ℂ z := by
    rw [Complex.inv_def, hz]
    simp
  have hz_pow_inv : (z⁻¹)^n = starRingEnd ℂ (z^n) := by
    rw [hz_inv, ← map_pow]
  have hsum : (1 - z^n) + (1 - (z⁻¹)^n) = 2 - (z^n + starRingEnd ℂ (z^n)) := by
    rw [hz_pow_inv]
    ring
  rw [hsum]
  have hre : (2 - (z^n + starRingEnd ℂ (z^n))).re = 2 - 2 * (z^n).re := by
    rw [Complex.sub_re, Complex.add_re, starRingEnd_apply,
      Complex.star_def, Complex.conj_re]
    simp
    ring
  rw [hre]
  have h_normSq_pow : Complex.normSq (z^n) = 1 := by
    rw [map_pow, hz, one_pow]
  have h_le_one : (z^n).re ≤ 1 := by
    have : (z^n).re^2 ≤ (z^n).re^2 + (z^n).im^2 := by nlinarith
    have h_norm : (z^n).re * (z^n).re + (z^n).im * (z^n).im = 1 := by
      exact h_normSq_pow
    nlinarith [h_norm]
  linarith

/-- Finite Xian-Jin Li summand positivity on `normSq z = 1` contrasted with an explicit
off-circle negative witness at `z = 1/2, n = 2` (`(1 - (1/2)^2) + (1 - 2^2) = -9/4 < 0`). -/
theorem finite_li_kernel_circle_nonneg_and_offCircle_neg_witness :
    (∀ (z : ℂ) (n : ℕ), Complex.normSq z = 1 →
      0 ≤ ((1 - z ^ n) + (1 - (z⁻¹) ^ n)).re) ∧
    (((1 - (1 / 2 : ℂ) ^ 2) + (1 - ((1 / 2 : ℂ)⁻¹) ^ 2)).re = -(9 / 4 : ℝ) ∧
     ((1 - (1 / 2 : ℂ) ^ 2) + (1 - ((1 / 2 : ℂ)⁻¹) ^ 2)).re < 0) := by
  refine ⟨finite_li_kernel_circle_nonneg, ?_⟩
  have hval :
      (1 - (1 / 2 : ℂ) ^ 2) + (1 - ((1 / 2 : ℂ)⁻¹) ^ 2) =
        ((-(9 / 4 : ℝ) : ℝ) : ℂ) := by
    norm_num
  rw [hval]
  norm_num

end LiCriterion

end InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation
