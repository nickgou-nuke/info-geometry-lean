/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge
import InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis
import InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge
import InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridge

/-!
# Wavefront KMS–Klein Duality Bridge: Günaydin–Gürsey Zorn Projectors, Real Peirce $\mathfrak{sl}_3(\mathbb{R})$ Color Action, Hadjiivanov Logarithmic Monodromy, and $\Phi_{24}(T) = \Phi_{12}(T^2)$ Reduction

This module integrates the Zorn split-octonion Günaydin–Gürsey $(\mathbf{1} \oplus \mathbf{1}) \oplus (\mathbf{3} \oplus \bar{\mathbf{3}})$
projector decomposition, the real Peirce $\mathfrak{sl}_3(\mathbb{R}) \subset \mathfrak{g}_{2(2)}$
color derivation bridge (`InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge`), the chiral
lightcone unipotent shear and Hadjiivanov logarithmic connection monodromy synthesis
(`InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis`), the cyclotomic
$\Phi_{24}(T) = \Phi_{12}(T^2)$ operator spine (`InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge`),
and the Unruh–Gibbs modular surprisal and $\mathrm{Cl}(5,5)$ lepton–quark quadratic reduction
(`InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridge`).

Each component retains its own mathematical carrier and scope:
1. **Section 1 — Zorn Split-Octonion Günaydin–Gürsey $(\mathbf{1} \oplus \mathbf{1}) \oplus (\mathbf{3} \oplus \bar{\mathbf{3}})$ Projectors, Real Peirce $\mathfrak{sl}_3(\mathbb{R})$ Color Intertwining, & Opposite-Sheet Weyl Scaling**:
   - Defines the four Peirce sector projectors `zornProjLeptonA`, `zornProjLeptonB`, `zornProjQuark`,
     and `zornProjAntiQuark` on `ZornSplitOctonion ℝ`, together with the color-singlet pairing
     `zornColorSingletPairing`.
   - Proves `zorn_gunaydin_gursey_direct_sum_decomposition` (exact additive reconstruction of every
     `x : ZornSplitOctonion ℝ` from its two leptonic diagonal singlets and quark/antiquark off-diagonal
     triplets), `zorn_quark_color_ray_norm_zero` (every pure quark or pure antiquark ray lies on the
     split null cone `zornNorm = 0`), and `zornNorm_eq_lepton_sub_colorSingletPairing`
     (`zornNorm x = x.a * x.b - zornColorSingletPairing x`).
   - Defines opposite-sheet scaling `sedenionOppositeWeylScale lam invLam X := (zornSmul lam X.1, zornSmul invLam X.2)`
     on `SplitSedenion ℝ`, proves `sedenionG2Derivation_commutes_oppositeWeylScale`, and packages
     `realPeirce_color_weyl_fock_spine`.
2. **Section 2 — Chiral Lightcone Unipotent Shear Readout, Hadjiivanov Braid Equivariance, and Cyclotomic $\Phi_{24}(T) = \Phi_{12}(T^2)$ Reduction**:
   - Proves `hadjiivanov_cyclotomic_w24_monodromy_spine`: combines the rank-two unipotent residue
     readout `unipotentResidueReadout (rankTwoLogResidue h) p v = (unipotentChiralShear p).mulVec v`
     and unit determinant $\det(I_2 + p S_+) = 1$, the rank-two Hadjiivanov monodromy realization
     `residueMonodromyEnd (rankTwoLogResidue h) = Matrix.mulVecLin (hadjiivanovMonodromy h)`,
     braid equivariance `residueMonodromyEnd_braid`, the cyclotomic polynomial reduction
     `phi24Eval T = phi12Eval (T ^ 2)`, and the diagonal square `sheetSwapLift_sq_apply`.
3. **Section 3 — Unruh–Gibbs First Law, Rindler–Milne Logarithmic Readouts, and Lepton-Sector Quadratic Reduction**:
   - Proves `wavefront_kms_klein_duality_master_spine`: packages the Unruh–Gibbs First Law of
     Entanglement `unruh_gibbs_surprisal_first_law_bridge`, the Rindler quadratic interval
     invariance `rindler_isometry`, the Milne logarithmic scale-shift law
     `milneKinematicTime_scale_shift`, and the lepton-sector quadratic reductions
     `lepton_sector_klein_quadric_reduction` and `zornNorm_lepton_sector_reduction`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix
open Finset

namespace InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridge

open InfoGeometry.Algebra
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Canonical.ChiralCausalConeFlow
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D
open InfoGeometry.Canonical.CyclotomicOperatorSpine
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionRankTwoBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance
open InfoGeometry.Thermodynamics.UnruhTemperature
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge
open InfoGeometry.Synthesis.RecoveredPhysicalInvariantsSynthesis
open InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
open InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridge
open InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge
open InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis

/-!
## Section 1: Zorn Split-Octonion Günaydin–Gürsey $(\mathbf{1} \oplus \mathbf{1}) \oplus (\mathbf{3} \oplus \bar{\mathbf{3}})$ Projectors, Real Peirce $\mathfrak{sl}_3(\mathbb{R})$ Color Intertwining, and Opposite-Sheet Weyl Scaling
-/

/-- Explicit $3 \times 3$ non-commutativity witness generator $E_{01}$ on `Matrix (Fin 3) (Fin 3) ℝ` (`T16`). -/
def colorGenE01 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- Companion $3 \times 3$ generator $E_{10}$ on `Matrix (Fin 3) (Fin 3) ℝ` (`T16`). -/
def colorGenE10 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- Explicit non-commutativity witness `colorGenE01 * colorGenE10 ≠ colorGenE10 * colorGenE01` on `Matrix (Fin 3) (Fin 3) ℝ`. -/
theorem colorGen_mul_ne_comm :
    colorGenE01 * colorGenE10 ≠ colorGenE10 * colorGenE01 := by
  intro h
  have h00 : (colorGenE01 * colorGenE10) 0 0 = (colorGenE10 * colorGenE01) 0 0 :=
    congrFun (congrFun h 0) 0
  norm_num [colorGenE01, colorGenE10, Matrix.mul_apply, Fin.sum_univ_three] at h00

/-- First Peirce leptonic singlet projector on `ZornSplitOctonion ℝ` (extracts upper-left scalar `a`). -/
def zornProjLeptonA (x : ZornSplitOctonion ℝ) : ZornSplitOctonion ℝ :=
  ⟨x.a, 0, 0, 0⟩

/-- Second Peirce leptonic singlet projector on `ZornSplitOctonion ℝ` (extracts lower-right scalar `b`). -/
def zornProjLeptonB (x : ZornSplitOctonion ℝ) : ZornSplitOctonion ℝ :=
  ⟨0, 0, 0, x.b⟩

/-- Quark color-triplet projector on `ZornSplitOctonion ℝ` (extracts upper-right vector `u ∈ ℝ³`). -/
def zornProjQuark (x : ZornSplitOctonion ℝ) : ZornSplitOctonion ℝ :=
  ⟨0, x.u, 0, 0⟩

/-- Antiquark color-antitriplet projector on `ZornSplitOctonion ℝ` (extracts lower-left vector `v ∈ ℝ³`). -/
def zornProjAntiQuark (x : ZornSplitOctonion ℝ) : ZornSplitOctonion ℝ :=
  ⟨0, 0, x.v, 0⟩

/-- **Günaydin–Gürsey $(\mathbf{1} \oplus \mathbf{1}) \oplus (\mathbf{3} \oplus \bar{\mathbf{3}})$ Direct-Sum Completeness on `ZornSplitOctonion ℝ`**:
Every Zorn split-octonion $x \in \mathbb{O}_s$ reconstructs as the sum of its two Peirce diagonal
leptonic singlets and its quark/antiquark off-diagonal color triplets. -/
theorem zorn_gunaydin_gursey_direct_sum_decomposition (x : ZornSplitOctonion ℝ) :
    zornAdd (zornAdd (zornProjLeptonA x) (zornProjLeptonB x))
      (zornAdd (zornProjQuark x) (zornProjAntiQuark x)) = x := by
  ext i <;>
    simp [zornAdd, zornProjLeptonA, zornProjLeptonB, zornProjQuark, zornProjAntiQuark]

/-- **Pure Quark and Pure Antiquark Color Rays Lie on the Split Null Cone**:
For any color vectors $u, v \in \mathbb{R}^3$, the pure quark state $\langle 0, u, 0, 0 \rangle$
and pure antiquark state $\langle 0, 0, v, 0 \rangle$ have vanishing split quadratic norm
`zornNorm = 0`. -/
theorem zorn_quark_color_ray_norm_zero (u_vec v_vec : Fin 3 → ℝ) :
    zornNorm (⟨0, u_vec, 0, 0⟩ : ZornSplitOctonion ℝ) = 0 ∧
    zornNorm (⟨0, 0, v_vec, 0⟩ : ZornSplitOctonion ℝ) = 0 := by
  have _ := (u_vec, v_vec)
  constructor <;> simp [zornNorm, vec3Dot]

/-- Color-singlet bilinear pairing $\sum_{c=1}^3 u_c v_c$ between the quark triplet `x.u`
and antiquark antitriplet `x.v` of a Zorn split-octonion $x \in \mathbb{O}_s$. -/
def zornColorSingletPairing (x : ZornSplitOctonion ℝ) : ℝ :=
  ∑ c : Fin 3, x.u c * x.v c

/-- **Zorn Split-Norm Decomposition into Leptonic Product Minus Color-Singlet Pairing**:
For every $x \in \mathrm{ZornSplitOctonion}\;\mathbb{R}$,
`zornNorm x = x.a * x.b - zornColorSingletPairing x`. -/
theorem zornNorm_eq_lepton_sub_colorSingletPairing (x : ZornSplitOctonion ℝ) :
    zornNorm x = x.a * x.b - zornColorSingletPairing x := by
  unfold zornNorm vec3Dot zornColorSingletPairing
  rw [Fin.sum_univ_three]

/-- Opposite-sheet scaling $(X_1, X_2) \mapsto (\lambda X_1, \lambda^{-1} X_2)$ on `SplitSedenion ℝ`. -/
def sedenionOppositeWeylScale (lam invLam : ℝ) (X : SplitSedenion ℝ) : SplitSedenion ℝ :=
  (zornSmul lam X.1, zornSmul invLam X.2)

/-- Every diagonally lifted 14-parameter $\mathfrak{g}_{2(2)}$ derivation `sedenionG2Derivation p`
commutes with opposite-sheet Weyl scaling `sedenionOppositeWeylScale lam invLam` on `SplitSedenion ℝ`. -/
theorem sedenionG2Derivation_commutes_oppositeWeylScale
    (p : Params) (lam invLam : ℝ) (X : SplitSedenion ℝ) :
    sedenionG2Derivation p (sedenionOppositeWeylScale lam invLam X) =
      sedenionOppositeWeylScale lam invLam (sedenionG2Derivation p X) := by
  apply Prod.ext
  · dsimp [sedenionG2Derivation, cdLift, sedenionOppositeWeylScale]
    exact zornG2Derivation_smul p lam X.1
  · dsimp [sedenionG2Derivation, cdLift, sedenionOppositeWeylScale]
    exact zornG2Derivation_smul p invLam X.2

/-- **Real Peirce $\mathfrak{sl}_3(\mathbb{R})$ Color, Opposite-Sheet Weyl Commutation, & Fock-Order Spine**:
For any trace-free $L \in \mathfrak{sl}_3(\mathbb{R})$, scale scalars $\lambda, \lambda^{-1} \in \mathbb{R}$,
split-sedenion $X \in \mathbb{S}_s$, and split-octonion $z \in \mathbb{O}_s$:
1. The doubled Peirce chart `sedenionPeirceAlignedToGG` intertwines `sedenionG2Derivation (realColorParameters L hL)`
   with `(evenColorTransform L, evenColorTransform L)`.
2. `sedenionG2Derivation (realColorParameters L hL)` commutes with `sedenionOppositeWeylScale lam invLam`.
3. In the Fock-ordered Günaydin–Gürsey chart, `zornToLeptonQuarkMultiplet (zornG2Derivation (realColorParameters L hL) z)`
   equals `peirceToFockOrderGG (evenColorTransform L (peirceAlignedZornToGG z))`. -/
theorem realPeirce_color_weyl_fock_spine
    (L : Matrix (Fin 3) (Fin 3) ℝ) (hL : Matrix.trace L = 0)
    (lam invLam : ℝ) (X : SplitSedenion ℝ) (z : ZornSplitOctonion ℝ) :
    (sedenionPeirceAlignedToGG (sedenionG2Derivation (realColorParameters L hL) X) =
      (evenColorTransform L (peirceAlignedZornToGG X.1),
       evenColorTransform L (peirceAlignedZornToGG X.2))) ∧
    (sedenionG2Derivation (realColorParameters L hL) (sedenionOppositeWeylScale lam invLam X) =
      sedenionOppositeWeylScale lam invLam (sedenionG2Derivation (realColorParameters L hL) X)) ∧
    (zornToLeptonQuarkMultiplet (zornG2Derivation (realColorParameters L hL) z) =
      peirceToFockOrderGG (evenColorTransform L (peirceAlignedZornToGG z))) := by
  refine ⟨(sedenionPeirceAligned_intertwines_realColor L hL X).1,
    sedenionG2Derivation_commutes_oppositeWeylScale (realColorParameters L hL) lam invLam X,
    fockOrderGG_realColor_action L hL z⟩

/-!
## Section 2: Chiral Lightcone Unipotent Shear Readout, Hadjiivanov Braid Equivariance, and Cyclotomic $\Phi_{24}(T) = \Phi_{12}(T^2)$ Reduction
-/

/-- **Hadjiivanov Logarithmic Monodromy, Unipotent Chiral Shear, & Cyclotomic $\Phi_{24}(T) = \Phi_{12}(T^2)$ Spine**:
For any complex module $V$, braid frame $F : \mathrm{LogResidueBraidFrame}\;V$, braid word
$g \in B_3$, channel $a \in \mathrm{Fin}\;3$, vector $w \in V$, conformal weight $h \in \mathbb{C}$,
shear parameters $p, q \in \mathbb{C}$, chiral state $X \in \mathrm{Chiral3}$, rank-two fiber vector
$v \in \mathrm{RankTwoFiber}$, and endomorphisms $T, A \in \mathrm{End}_{\mathbb{C}}(V)$:
1. Rank-two unipotent residue readout matches `unipotentChiralShear p` and has unit determinant:
   `unipotentResidueReadout (rankTwoLogResidue h) p v = (unipotentChiralShear p).mulVec v ∧ Matrix.det (unipotentChiralShear p) = 1`.
2. Rank-two Hadjiivanov monodromy realization:
   `residueMonodromyEnd (rankTwoLogResidue h) = Matrix.mulVecLin (hadjiivanovMonodromy h)`.
3. Braid equivariance of `residueMonodromyEnd` on `F`:
   `F.representation g (residueMonodromyEnd (frameResidue F a) w) = residueMonodromyEnd (frameResidue F (braidPermutation g a)) (F.representation g w)`.
4. Cyclotomic doubling identity `phi24Eval T = phi12Eval (T ^ 2)` and off-diagonal sheet-swap
   square `((sheetSwapLift A) ^ 2) (w, w) = ((A ^ 2) w, (A ^ 2) w)`. -/
theorem hadjiivanov_cyclotomic_w24_monodromy_spine
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3) (w : V)
    (h p q : ℂ) (X : Chiral3) (v : RankTwoFiber)
    (T A : Module.End ℂ V) :
    (unipotentResidueReadout (rankTwoLogResidue h) p v = (unipotentChiralShear p).mulVec v ∧
      Matrix.det (unipotentChiralShear p) = 1) ∧
    (residueMonodromyEnd (rankTwoLogResidue h) = Matrix.mulVecLin (hadjiivanovMonodromy h)) ∧
    (F.representation g (residueMonodromyEnd (frameResidue F a) w) =
      residueMonodromyEnd (frameResidue F (braidPermutation g a)) (F.representation g w)) ∧
    (phi24Eval T = phi12Eval (T ^ 2) ∧
      ((sheetSwapLift A) ^ 2) (w, w) = ((A ^ 2) w, (A ^ 2) w)) := by
  have h_shear := unipotentChiralShear_mul_and_det p q h X v
  refine ⟨⟨h_shear.2.2.2, h_shear.2.1⟩,
    rankTwo_residueMonodromyEnd_eq_mulVecLin h,
    residueMonodromyEnd_braid F g a w,
    ⟨phi24Eval_eq_phi12Eval_sq T, sheetSwapLift_sq_apply A (w, w)⟩⟩

/-!
## Section 3: Unruh–Gibbs First Law, Rindler–Milne Logarithmic Readouts, and Lepton-Sector Quadratic Reduction
-/

/-- **Wavefront KMS–Klein Duality Master Spine**:
Synthesizes the thermodynamic, logarithmic-clock, and lepton-sector quadratic readouts:
1. **Unruh–Gibbs First Law of Entanglement**: for a `RindlerObserver` with inverse temperature
   $\beta = \mathrm{inverseTemperature}\;\mathrm{obs}$, partition normalization $Z > 0$, and
   trace-preserving perturbation $\sum_i \delta\rho_i = 0$,
   $\sum_j \delta\rho_j \, H_{\mathrm{mod}}(p_j) = \frac{2\pi}{\mathrm{obs}.a} \sum_j \delta\rho_j E_j = \frac{1}{T_{\mathrm{U}}(\mathrm{obs})} \sum_j \delta\rho_j E_j$.
2. **Rindler Quadratic Interval Invariance & Milne Logarithmic Scale Shift**:
   `lightconePotential (rindler_boost X η) = lightconePotential X` and
   `milneKinematicTime t₀ (lam * t) - milneKinematicTime t₀ t = t₀ * Real.log lam`.
3. **Lepton-Sector Quadratic Reductions on `Fin 8 → ℝ` and `ZornSplitOctonion ℝ`**:
   `splitOctonionQuadraticForm x = 2 * x 0 * x 1` whenever `(gunaydinGurseySplit x).2 = 0`,
   and `zornNorm z = z.a * z.b` whenever `z.u = 0` and `z.v = 0`. -/
theorem wavefront_kms_klein_duality_master_spine
    {n : ℕ} (obs : RindlerObserver) (Z : ℝ) (E deltaRho : Fin n → ℝ)
    (hZ : 0 < Z) (h_trace_zero : ∑ i : Fin n, deltaRho i = 0) (i : Fin n)
    (X : Chiral3) (η : ℝ)
    (t₀ t lam : ℝ) (ht₀ : t₀ ≠ 0) (ht : t ≠ 0) (hlam : lam ≠ 0)
    (x : Fin 8 → ℝ) (h_quark_zero : (gunaydinGurseySplit x).2 = 0)
    (z : ZornSplitOctonion ℝ) (hu : z.u = 0) (hv : z.v = 0) :
    ((∑ j : Fin n, deltaRho j * modularSurprisal (gibbsState (inverseTemperature obs) Z E j)) =
        ((2 * Real.pi) / obs.a) * (∑ j : Fin n, deltaRho j * E j) ∧
      (∑ j : Fin n, deltaRho j * modularSurprisal (gibbsState (inverseTemperature obs) Z E j)) =
        (1 / unruhTemperature obs) * (∑ j : Fin n, deltaRho j * E j)) ∧
    (lightconePotential (rindler_boost X η) = lightconePotential X ∧
      milneKinematicTime t₀ (lam * t) - milneKinematicTime t₀ t = t₀ * Real.log lam) ∧
    (splitOctonionQuadraticForm x = 2 * x 0 * x 1 ∧
      zornNorm z = z.a * z.b) := by
  have h_unruh := unruh_gibbs_surprisal_first_law_bridge obs Z E deltaRho hZ h_trace_zero i
  refine ⟨h_unruh.2,
    ⟨rindler_isometry X η, milneKinematicTime_scale_shift t₀ t lam ht₀ ht hlam⟩,
    ⟨lepton_sector_klein_quadric_reduction x h_quark_zero,
      (zornNorm_lepton_sector_reduction z hu hv).1⟩⟩

/-- Projective stereographic quark coordinate $z^c(x) = u^c / a$ relative to the first leptonic
singlet $a \in \mathbb{R}$. -/
def celestialQuarkCoord (x : ZornSplitOctonion ℝ) (c : Fin 3) : ℝ :=
  x.u c / x.a

/-- Projective stereographic antiquark coordinate $\bar{z}_c(x) = v_c / a$ relative to the first
leptonic singlet $a \in \mathbb{R}$. -/
def celestialAntiQuarkCoord (x : ZornSplitOctonion ℝ) (c : Fin 3) : ℝ :=
  x.v c / x.a

/-- **Stereographic Null-Cone Reduction & 24-Element Double-Star Root-Sheet Readout**:
1. For any $x \in \mathrm{ZornSplitOctonion}\;\mathbb{R}$ on the split null cone (`zornNorm x = 0`)
   with vanishing second leptonic coordinate (`x.b = 0`) and non-zero first leptonic coordinate
   (`x.a ≠ 0`), the stereographic color pairing $\sum_{c=1}^3 z^c(x)\,\bar{z}_c(x)$ vanishes:
   `∑ c : Fin 3, celestialQuarkCoord x c * celestialAntiQuarkCoord x c = 0`.
2. Every concrete 14-parameter split-sedenion derivation `sedenionG2Derivation p` maps any
   zero-divisor pair `sedenionMul X Y = sedenionZero` into the first-order zero-divisor tangent
   locus `sedenionAdd (sedenionMul (sedenionG2Derivation p X) Y) (sedenionMul X (sedenionG2Derivation p Y)) = sedenionZero`.
3. The finite root-sheet carrier `DoubleStarSheetCarrier` has cardinality $24 = 12 \times 2$. -/
theorem celestial_null_quadric_and_doubleStar_root_sheet_spine
    (x : ZornSplitOctonion ℝ) (h_null : zornNorm x = 0) (hb : x.b = 0) (ha : x.a ≠ 0)
    (p : Params) (X Y : SplitSedenion ℝ) (hXY : sedenionMul X Y = sedenionZero) :
    (∑ c : Fin 3, celestialQuarkCoord x c * celestialAntiQuarkCoord x c = 0) ∧
    (sedenionAdd (sedenionMul (sedenionG2Derivation p X) Y)
      (sedenionMul X (sedenionG2Derivation p Y)) = sedenionZero) ∧
    (Fintype.card DoubleStarSheetCarrier = 24) := by
  refine ⟨?_,
    InfoGeometry.Synthesis.G2Sl2SeventeenParameterProductActionBridge.sedenionG2Derivation_preserves_zero_divisor_tangent
      p X Y hXY,
    doubleStarSheetCarrier_card⟩
  have h_dot : x.u 0 * x.v 0 + x.u 1 * x.v 1 + x.u 2 * x.v 2 = 0 := by
    unfold zornNorm vec3Dot at h_null
    rw [hb, mul_zero, zero_sub, neg_eq_zero] at h_null
    exact h_null
  unfold celestialQuarkCoord celestialAntiQuarkCoord
  rw [Fin.sum_univ_three]
  have h_factor :
      (x.u 0 / x.a) * (x.v 0 / x.a) + (x.u 1 / x.a) * (x.v 1 / x.a) +
        (x.u 2 / x.a) * (x.v 2 / x.a) =
      (x.u 0 * x.v 0 + x.u 1 * x.v 1 + x.u 2 * x.v 2) / (x.a * x.a) := by
    ring
  have _ := ha
  rw [h_factor, h_dot, zero_div]

end InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridge

end
