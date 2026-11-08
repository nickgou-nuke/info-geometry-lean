/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Canonical.ZetaKleinTomitaPeirceLaneBridge
import InfoGeometry.Thermo.ComplexThermodynamicLift
import InfoGeometry.Geometry.KleinFourTag

/-!
# KMS Periodic Winding Strips, Möbius Interval Doubling, Dirac Belt Helix, and the Double-Krein Ring

This module formalizes the causal poset and mathematical synthesis connecting:

1. **Stage 0 (`kmsPeriodicWindingStrip`) — Laplace $s$-Plane & Tomita–Takesaki KMS Winding Strips**:
   - The periodic KMS strips along the imaginary/modular axis with period $\beta > 0$,
     indexed by the integer winding number $k \in \mathbb{Z}$, and the $+1/2$ coordinate shift
     matching the centered Tomita KMS strip $[-1/2, 1/2]$ to the Riemann critical strip $[0, 1]$.
2. **Stage 1 (`expAndMobiusIntervalFold`) — Exponential Ray & Möbius Interval Doubling**:
   - The exponential map $(-\infty, 0, +\infty) \xrightarrow{\exp} (0, 1, +\infty)$ satisfying
     $\exp(-u) = (\exp u)^{-1}$, composed with the Möbius fold $M(x) = (1 + x)^{-1}$ which
     folds $[1, +\infty)$ onto $(0, 1/2]$ and satisfies $M(x^{-1}) = 1 - M(x)$, doubling
     the unit interval around the critical seam $u = 0 \mapsto 1/2$.
3. **Stage 2 (`compactifiedNibelungRing`) — Gluing $\pm\infty \mapsto 0$ into a Closed Ring**:
   - The folded radial coordinate $R(u) = \frac{2 \exp(u)}{1 + \exp(2u)} \in (0, 1]$ which
     maps both $-\infty$ and $+\infty$ asymptotically to $0$, achieves its unique maximum
     $R(0) = 1$ at the critical seam $u = 0$, and is invariant under $u \mapsto -u$.
4. **Stage 3 (`kleinFourAndDiracBeltHelix`) — $V_4$ Gluing vs. $D_4$ Dirac Belt Spinor Twist**:
   - On the double real Krein space $\mathrm{Mat}_2(\mathbb{R})$ with Krein grading
     $\eta = \mathrm{diag}(1, -1)$ and sheet-swap $W = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$,
     the generators anticommute ($\eta W = -W \eta \neq W \eta$), so the belt-twist element
     $B = \eta W$ has order $4$ ($B^2 = -I \neq I$, $B^4 = I$, the $4\pi$ Dirac belt twist),
     while the induced adjoint actions $\mathrm{Ad}_\eta(X) = \eta X \eta$ and
     $\mathrm{Ad}_W(X) = W X W$ commute and generate the Klein four-group $V_4 = \mathbb{Z}_2 \times \mathbb{Z}_2$.
5. **Stage 4 (`noncommutativePeirceKreinRing`) — Non-Commutative Operator Ring (`[Ring B]`) Realization**:
   - In any non-commutative ring `[Ring B]` with idempotent $P^2 = P$, the operatorial Cayley
     transform on the nilpotent Peirce cones, the commuting Klein $V_4$ action of parity conjugation
     $\mathcal{P}(X) = S X S$ and Tomita sheet-swap anti-automorphism $J$, and the helical
     Steinberg double-cover closure.
-/

noncomputable section

namespace InfoGeometry.Canonical.KMSStripMobiusKreinNibelungRing

open Matrix
open scoped Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Clifford.OperatorKleinTomitaCPT
open InfoGeometry.Physics

/-! ## 1. Causal Poset of the 5-Stage Construction -/

/-- Causal poset of the five-stage KMS-to-Nibelung-Ring synthesis. -/
inductive NibelungRingStage
  | kmsPeriodicWindingStrip
  | expAndMobiusIntervalFold
  | compactifiedNibelungRing
  | kleinFourAndDiracBeltHelix
  | noncommutativePeirceKreinRing
  deriving DecidableEq, Repr

instance instInhabitedNibelungRingStage : Inhabited NibelungRingStage :=
  ⟨.kmsPeriodicWindingStrip⟩

/--Topological rank in the causal poset. -/
def nibelungStageRank : NibelungRingStage → ℕ
  | .kmsPeriodicWindingStrip => 0
  | .expAndMobiusIntervalFold => 1
  | .compactifiedNibelungRing => 2
  | .kleinFourAndDiracBeltHelix => 3
  | .noncommutativePeirceKreinRing => 4

theorem nibelungStageRank_injective : Function.Injective nibelungStageRank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance instPartialOrderNibelungRingStage : PartialOrder NibelungRingStage :=
  PartialOrder.lift nibelungStageRank nibelungStageRank_injective

theorem nibelungStage_strict_chain :
    NibelungRingStage.kmsPeriodicWindingStrip < .expAndMobiusIntervalFold ∧
    NibelungRingStage.expAndMobiusIntervalFold < .compactifiedNibelungRing ∧
    NibelungRingStage.compactifiedNibelungRing < .kleinFourAndDiracBeltHelix ∧
    NibelungRingStage.kleinFourAndDiracBeltHelix < .noncommutativePeirceKreinRing := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## 2. Stage 0: Laplace $s$-Plane, KMS Periodic Winding Strips, and the $+1/2$ Riemann Shift -/

/-- Coordinate on the unfolded helical KMS covering space:
`winding` $\in \mathbb{Z}$ counts the KMS sheet/winding number,
`u` $\in \mathbb{R}$ is the centered real scale coordinate,
and `t` $\in \mathbb{R}$ is the modular/Laplace imaginary coordinate. -/
structure HelicalKMSCoord where
  winding : ℤ
  u : ℝ
  t : ℝ

instance instInhabitedHelicalKMSCoord : Inhabited HelicalKMSCoord :=
  ⟨⟨0, 0, 0⟩⟩

/-- Shift from the centered Tomita KMS strip $u \in [-1/2, 1/2]$ to the Riemann strip $\sigma \in [0, 1]$. -/
def kmsToRiemannShift (u : ℝ) : ℝ :=
  u + 1 / 2

/-- Inverse shift from the Riemann strip $\sigma \in [0, 1]$ to the centered KMS strip $u \in [-1/2, 1/2]$. -/
def riemannToKmsShift (σ : ℝ) : ℝ :=
  σ - 1 / 2

/-- Projection from the unfolded helical KMS coordinate to the shifted Laplace/Riemann $s$-plane. -/
def helicalToRiemannComplex (p : HelicalKMSCoord) : ℂ :=
  ((kmsToRiemannShift p.u : ℝ) : ℂ) + (p.t : ℂ) * Complex.I

/-- Helical deck translation by $m \in \mathbb{Z}$ KMS periods of length $\beta$. -/
def helixWindingShift (β : ℝ) (m : ℤ) (p : HelicalKMSCoord) : HelicalKMSCoord :=
  ⟨p.winding + m, p.u, p.t + (m : ℝ) * β⟩

/-- Helical belt twist combining $m$ half-period shifts with the $(-1)^m$ transverse flip. -/
def helixBeltTwist (Δ : ℝ) (m : ℤ) (p : HelicalKMSCoord) : HelicalKMSCoord :=
  ⟨p.winding + m, ((-1 : ℝ) ^ m) * p.u, p.t + (m : ℝ) * Δ⟩

/-- **Stage 0 Theorem**:
1. `kmsToRiemannShift` and `riemannToKmsShift` are mutual inverses;
2. The centered KMS strip $u \in [-1/2, 1/2]$ maps bijectively onto the Riemann strip $\sigma \in [0, 1]$;
3. The KMS reflection $u \mapsto -u$ becomes the functional reflection $\sigma \mapsto 1 - \sigma$,
   fixing the critical seam $u = 0 \iff \sigma = 1/2$;
4. `helixWindingShift` forms an exact $\mathbb{Z}$-action whose sheets are distinguished by `winding`;
5. Two half-turn belt twists (`helixBeltTwist Δ 1` composed with itself) restore the transverse
   coordinate `u` while advancing the winding number by `2` and the modular axis by `2 * Δ`. -/
theorem stage0_kms_winding_and_riemann_shift_package
    (u : ℝ) (β Δ : ℝ) (m₁ m₂ : ℤ) (p : HelicalKMSCoord) :
    riemannToKmsShift (kmsToRiemannShift u) = u ∧
    (u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ↔
      kmsToRiemannShift u ∈ Set.Icc (0 : ℝ) (1 : ℝ)) ∧
    kmsToRiemannShift (-u) = 1 - kmsToRiemannShift u ∧
    (u = 0 ↔ kmsToRiemannShift u = 1 / 2) ∧
    (helixWindingShift β m₁ p).winding = p.winding + m₁ ∧
    helixWindingShift β (m₁ + m₂) p =
      helixWindingShift β m₂ (helixWindingShift β m₁ p) ∧
    helixBeltTwist Δ 1 (helixBeltTwist Δ 1 p) =
      ⟨p.winding + 2, p.u, p.t + 2 * Δ⟩ := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · unfold riemannToKmsShift kmsToRiemannShift
    ring
  · unfold kmsToRiemannShift
    simp only [Set.mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · unfold kmsToRiemannShift
    ring
  · unfold kmsToRiemannShift
    constructor <;> intro h <;> linarith
  · cases p
    simp only [helixWindingShift, Int.cast_add]
    congr 1 <;> ring
  · cases p
    simp only [helixBeltTwist, zpow_one, Int.cast_one]
    congr 1 <;> ring

/-! ## 3. Stage 1 & 2: Exponential Ray, Möbius Interval Fold, and the Compactified Ring -/

/-- Möbius fold $M(x) = (1 + x)^{-1}$ mapping the multiplicative ray $(0, +\infty)$ into $(0, 1)$. -/
def mobiusUnitFold (x : ℝ) : ℝ :=
  1 / (1 + x)

/-- Composite logistic Möbius fold $u \mapsto (1 + \exp(u))^{-1}$ on $(-\infty, +\infty)$. -/
def expMobiusFold (u : ℝ) : ℝ :=
  mobiusUnitFold (Real.exp u)

/-- Compactified Nibelung ring radial coordinate $R(u) = \frac{2 \exp(u)}{1 + \exp(2u)} \in (0, 1]$,
which sends both infinities $u \to \pm\infty$ to $0$ and the critical seam $u = 0$ to $1$. -/
def foldedRingRadius (u : ℝ) : ℝ :=
  (2 * Real.exp u) / (1 + Real.exp (2 * u))

/-- **Stage 1 & 2 Theorem (Exponential Map, Möbius Interval Doubling, and Compactified Ring)**:
1. $\exp(0) = 1$ and $\exp(-u) = (\exp u)^{-1}$;
2. For any $x > 0$, the Möbius fold satisfies $M(x^{-1}) = 1 - M(x)$, folding $[1, +\infty)$
   onto $(0, 1/2]$ as the mirror image of $(0, 1] \to [1/2, 1)$ around $M(1) = 1/2$;
3. In logarithmic coordinates, `expMobiusFold (-u) = 1 - expMobiusFold u` and `expMobiusFold 0 = 1 / 2`;
4. The compactified ring radius `foldedRingRadius` satisfies:
   - `foldedRingRadius 0 = 1` (critical seam apex),
   - `foldedRingRadius (-u) = foldedRingRadius u` (gluing of the positive and negative sheets),
   - `0 < foldedRingRadius u` and `foldedRingRadius u ≤ 1` for all $u \in \mathbb{R}$,
   - `foldedRingRadius u = 1 ↔ u = 0` (unique seam maximum). -/
theorem stage1_and_2_exp_mobius_and_folded_ring_package
    (u : ℝ) (x : ℝ) (hx : 0 < x) :
    Real.exp 0 = 1 ∧
    Real.exp (-u) = (Real.exp u)⁻¹ ∧
    mobiusUnitFold x⁻¹ = 1 - mobiusUnitFold x ∧
    mobiusUnitFold 1 = 1 / 2 ∧
    expMobiusFold (-u) = 1 - expMobiusFold u ∧
    expMobiusFold 0 = 1 / 2 ∧
    foldedRingRadius 0 = 1 ∧
    foldedRingRadius (-u) = foldedRingRadius u ∧
    0 < foldedRingRadius u ∧
    foldedRingRadius u ≤ 1 ∧
    (foldedRingRadius u = 1 ↔ u = 0) := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have h1x : 1 + x ≠ 0 := by linarith
  have h1xinv : 1 + x⁻¹ ≠ 0 := by
    have : 0 < x⁻¹ := inv_pos.mpr hx
    linarith
  have hexp_pos : 0 < Real.exp u := Real.exp_pos u
  have hexp2_pos : 0 < Real.exp (2 * u) := Real.exp_pos (2 * u)
  have hdenom_pos : 0 < 1 + Real.exp (2 * u) := by linarith
  have hdenom_ne : 1 + Real.exp (2 * u) ≠ 0 := ne_of_gt hdenom_pos
  have hexp2_eq : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [two_mul, Real.exp_add]
  refine ⟨Real.exp_zero, Real.exp_neg u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold mobiusUnitFold
    field_simp [hx_ne, h1x, h1xinv]
    ring
  · unfold mobiusUnitFold
    norm_num
  · unfold expMobiusFold mobiusUnitFold
    rw [Real.exp_neg]
    have he_ne : Real.exp u ≠ 0 := ne_of_gt hexp_pos
    have h1e : 1 + Real.exp u ≠ 0 := by linarith
    have h1einv : 1 + (Real.exp u)⁻¹ ≠ 0 := by
      have : 0 < (Real.exp u)⁻¹ := inv_pos.mpr hexp_pos
      linarith
    field_simp [he_ne, h1e, h1einv]
    ring
  · unfold expMobiusFold mobiusUnitFold
    rw [Real.exp_zero]
    norm_num
  · unfold foldedRingRadius
    simp [Real.exp_zero]
    norm_num
  · unfold foldedRingRadius
    have h2neg : 2 * (-u) = -(2 * u) := by ring
    rw [h2neg, Real.exp_neg, Real.exp_neg]
    have he_ne : Real.exp u ≠ 0 := ne_of_gt hexp_pos
    have he2_ne : Real.exp (2 * u) ≠ 0 := ne_of_gt hexp2_pos
    have h1e2inv : 1 + (Real.exp (2 * u))⁻¹ ≠ 0 := by
      have : 0 < (Real.exp (2 * u))⁻¹ := inv_pos.mpr hexp2_pos
      linarith
    field_simp [he_ne, he2_ne, hdenom_ne, h1e2inv]
    rw [hexp2_eq]
    ring
  · unfold foldedRingRadius
    exact div_pos (by linarith) hdenom_pos
  · unfold foldedRingRadius
    rw [div_le_one hdenom_pos, hexp2_eq]
    have hsq : 0 ≤ (Real.exp u - 1) ^ 2 := sq_nonneg (Real.exp u - 1)
    linarith
  · unfold foldedRingRadius
    rw [div_eq_iff hdenom_ne, hexp2_eq]
    constructor
    · intro h
      have hsq : (Real.exp u - 1) ^ 2 = 0 := by linarith
      have he1 : Real.exp u = 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
      exact (Real.exp_eq_one_iff u).mp he1
    · intro hu
      subst hu
      simp [Real.exp_zero]
      ring

/-! ## 4. Stage 3: Double Real Krein Space, $D_4$ Dirac Belt Twist, and Adjoint Klein Four-Group $V_4$ -/

/-- Indefinite Krein grading matrix $\eta = \mathrm{diag}(1, -1)$ on the double real space $\mathbb{R}^{1,1}$. -/
def kreinEta : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- Sheet-exchange matrix $W = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ swapping the two folded rays. -/
def sheetSwapW : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- Dirac belt twist generator $B = \eta W = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$. -/
def diracBeltTwist : Matrix (Fin 2) (Fin 2) ℝ :=
  kreinEta * sheetSwapW

/-- Explicit non-commutativity witness: the Krein grading $\eta$ and sheet-swap $W$ do not commute. -/
theorem kreinEta_mul_sheetSwapW_ne :
    kreinEta * sheetSwapW ≠ sheetSwapW * kreinEta := by
  intro h
  have h01 : (kreinEta * sheetSwapW) 0 1 = (sheetSwapW * kreinEta) 0 1 := by
    rw [h]
  norm_num [kreinEta, sheetSwapW, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Adjoint action of the Klein four-group $V_4 = \mathbb{Z}_2 \times \mathbb{Z}_2$ on the
non-commutative matrix algebra $\mathrm{Mat}_2(\mathbb{R})$. -/
def kleinFourMatrixAct (tag : InfoGeometry.Geometry.KleinFourTag.Tag)
    (X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let X₁ := if tag.1 = 1 then kreinEta * X * kreinEta else X
  if tag.2 = 1 then sheetSwapW * X₁ * sheetSwapW else X₁

/-- **Stage 3 Theorem (Dirac Belt $4\pi$ Spinor Twist vs. Adjoint $V_4$ Gluing)**:
On the double real Krein matrix algebra $\mathrm{Mat}_2(\mathbb{R})$:
1. $\eta^2 = 1$ and $W^2 = 1$;
2. $\eta$ and $W$ anticommute: $\eta W = - W \eta$;
3. A single belt twist squares to $-1$ ($B^2 = -1$, spinor sign flip), whereas the doubled
   Dirac belt twist restores the identity ($B^4 = 1$);
4. On operators $X \in \mathrm{Mat}_2(\mathbb{R})$, conjugation by $\eta$ and conjugation by $W$
   commute ($\eta (W X W) \eta = W (\eta X \eta) W$), descending the $D_4$ spinor belt group
   to an exact Klein four-group $V_4$ action where every generator is an involution. -/
theorem stage3_double_krein_dirac_belt_and_v4_package
    (X : Matrix (Fin 2) (Fin 2) ℝ) :
    kreinEta * kreinEta = 1 ∧
    sheetSwapW * sheetSwapW = 1 ∧
    kreinEta * sheetSwapW = - (sheetSwapW * kreinEta) ∧
    diracBeltTwist * diracBeltTwist = -1 ∧
    (diracBeltTwist * diracBeltTwist) * (diracBeltTwist * diracBeltTwist) = 1 ∧
    kreinEta * (sheetSwapW * X * sheetSwapW) * kreinEta =
      sheetSwapW * (kreinEta * X * kreinEta) * sheetSwapW ∧
    kleinFourMatrixAct InfoGeometry.Geometry.KleinFourTag.P
      (kleinFourMatrixAct InfoGeometry.Geometry.KleinFourTag.P X) = X ∧
    kleinFourMatrixAct InfoGeometry.Geometry.KleinFourTag.T
      (kleinFourMatrixAct InfoGeometry.Geometry.KleinFourTag.T X) = X ∧
    kleinFourMatrixAct InfoGeometry.Geometry.KleinFourTag.P
      (kleinFourMatrixAct InfoGeometry.Geometry.KleinFourTag.T X) =
      kleinFourMatrixAct InfoGeometry.Geometry.KleinFourTag.PT X := by
  have hEtaSq : kreinEta * kreinEta = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [kreinEta, Matrix.mul_apply, Fin.sum_univ_two]
  have hWSq : sheetSwapW * sheetSwapW = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sheetSwapW, Matrix.mul_apply, Fin.sum_univ_two]
  have hAnticomm : kreinEta * sheetSwapW = - (sheetSwapW * kreinEta) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [kreinEta, sheetSwapW, Matrix.mul_apply, Fin.sum_univ_two]
  have hAdComm :
      kreinEta * (sheetSwapW * X * sheetSwapW) * kreinEta =
        sheetSwapW * (kreinEta * X * kreinEta) * sheetSwapW := by
    calc
      kreinEta * (sheetSwapW * X * sheetSwapW) * kreinEta
          = (kreinEta * sheetSwapW) * X * (sheetSwapW * kreinEta) := by noncomm_ring
      _ = (- (sheetSwapW * kreinEta)) * X * (sheetSwapW * kreinEta) := by rw [hAnticomm]
      _ = (sheetSwapW * kreinEta) * X * (- (sheetSwapW * kreinEta)) := by noncomm_ring
      _ = (sheetSwapW * kreinEta) * X * (kreinEta * sheetSwapW) := by rw [← hAnticomm]
      _ = sheetSwapW * (kreinEta * X * kreinEta) * sheetSwapW := by noncomm_ring
  refine ⟨hEtaSq, hWSq, hAnticomm, ?_, ?_, hAdComm, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [diracBeltTwist, kreinEta, sheetSwapW, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [diracBeltTwist, kreinEta, sheetSwapW, Matrix.mul_apply, Fin.sum_univ_two]
  · dsimp [kleinFourMatrixAct, InfoGeometry.Geometry.KleinFourTag.P]
    calc
      kreinEta * (kreinEta * X * kreinEta) * kreinEta
          = (kreinEta * kreinEta) * X * (kreinEta * kreinEta) := by noncomm_ring
      _ = 1 * X * 1 := by rw [hEtaSq]
      _ = X := by noncomm_ring
  · dsimp [kleinFourMatrixAct, InfoGeometry.Geometry.KleinFourTag.T]
    calc
      sheetSwapW * (sheetSwapW * X * sheetSwapW) * sheetSwapW
          = (sheetSwapW * sheetSwapW) * X * (sheetSwapW * sheetSwapW) := by noncomm_ring
      _ = 1 * X * 1 := by rw [hWSq]
      _ = X := by noncomm_ring
  · dsimp [kleinFourMatrixAct, InfoGeometry.Geometry.KleinFourTag.P,
      InfoGeometry.Geometry.KleinFourTag.T, InfoGeometry.Geometry.KleinFourTag.PT]
    exact hAdComm

/-! ## 5. Stage 4: General Non-Commutative Operator Ring (`[Ring B]`) Realization -/

section NonCommutativeOperatorRing

variable {B : Type*} [Ring B]

/-- Operatorial Cayley/Möbius transform on the positive Peirce nilpotent cone:
since $(\mathrm{conePlus}\;P\;A)^2 = 0$, the rational Cayley map
$(1 + e_+)(1 - e_+)^{-1} = (1 + e_+)^2 = 1 + e_+ + e_+$ is polynomial and exact in any ring `B`. -/
def opCayleyPlus (P A : B) : B :=
  1 + conePlus P A + conePlus P A

/-- Inverse operatorial Cayley/Möbius transform on the positive Peirce nilpotent cone. -/
def opCayleyPlusInv (P A : B) : B :=
  1 - conePlus P A - conePlus P A

/-- Constructor-indexed operator realization mapping each `NibelungRingStage` to its
canonical operator in `[Ring B]`. -/
def nibelungStageOperator (P A C X : B) : NibelungRingStage → B
  | .kmsPeriodicWindingStrip => evenGrade P X + oddGrade P X
  | .expAndMobiusIntervalFold => opCayleyPlus P A
  | .compactifiedNibelungRing => opCayleyPlusInv P A
  | .kleinFourAndDiracBeltHelix => steinbergBraid P A C
  | .noncommutativePeirceKreinRing => steinbergBraidInv P A C

/-- **Stage 4 Theorem (Non-Commutative Operator Ring Möbius Fold, Klein $V_4$ Action, and Helical Closure)**:
For any idempotent $P^2 = P$ in a non-commutative ring `[Ring B]` and any anti-automorphism
$J : \mathrm{AntiAutomorphism}\;B$ swapping the Peirce sheets $J(P) = 1 - P$:
1. The operatorial Cayley transform `opCayleyPlus P A` and `opCayleyPlusInv P A` are exact
   two-sided inverses;
2. Parity conjugation $\mathcal{P}(Y) = S Y S$ folds `opCayleyPlus P A` into its inverse
   `opCayleyPlusInv P A` (`parityConj P (opCayleyPlus P A) = opCayleyPlusInv P A`);
3. The Tomita anti-automorphism $J$ reverses the Krein grading $J(S) = -S$ and **commutes**
   with parity conjugation $\mathcal{P}$ on all operators $X \in B$:
   $$\mathcal{P}(J(X)) = J(\mathcal{P}(X))$$
   yielding a genuine non-commutative Klein four-group $V_4 = \langle \mathcal{P}, J \rangle$ action;
4. The helical Steinberg double-cover round-trip identity closes the operator ring back to $X$. -/
theorem stage4_noncommutative_peirce_krein_nibelung_ring_synthesis
    {P : B} (hP : P * P = P) (A C X : B)
    (J : AntiAutomorphism B) (hJP : J.toFun P = 1 - P) :
    nibelungStageOperator P A C X .kmsPeriodicWindingStrip = X ∧
    nibelungStageOperator P A C X .expAndMobiusIntervalFold *
      nibelungStageOperator P A C X .compactifiedNibelungRing = (1 : B) ∧
    nibelungStageOperator P A C X .compactifiedNibelungRing *
      nibelungStageOperator P A C X .expAndMobiusIntervalFold = (1 : B) ∧
    parityConj P (nibelungStageOperator P A C X .expAndMobiusIntervalFold) =
      nibelungStageOperator P A C X .compactifiedNibelungRing ∧
    J.toFun (invS P) = - invS P ∧
    parityConj P (J.toFun X) = J.toFun (parityConj P X) ∧
    parityConj P (nibelungStageOperator P A C X .kleinFourAndDiracBeltHelix) =
      nibelungStageOperator P A C X .noncommutativePeirceKreinRing ∧
    parityConj P
      (steinbergBraid P A C *
        parityConj P (steinbergBraid P A C * X * steinbergBraidInv P A C) *
        steinbergBraidInv P A C) = X := by
  have hJ1 : J.toFun 1 = 1 := (antiOppositeRingEquiv J).map_one
  have hJS : J.toFun (invS P) = - invS P := by
    dsimp [invS]
    have hsub1 : J.toFun (P - (1 - P)) = J.toFun P - J.toFun (1 - P) :=
      (antiOppositeRingEquiv J).map_sub (MulOpposite.op P) (MulOpposite.op (1 - P))
    have hsub2 : J.toFun (1 - P) = J.toFun 1 - J.toFun P :=
      (antiOppositeRingEquiv J).map_sub 1 (MulOpposite.op P)
    rw [hsub1, hsub2, hJP, hJ1]
    noncomm_ring
  have hPJ_comm : parityConj P (J.toFun X) = J.toFun (parityConj P X) := by
    dsimp [parityConj]
    rw [J.map_mul, J.map_mul, hJS]
    noncomm_ring
  dsimp only [nibelungStageOperator, opCayleyPlus, opCayleyPlusInv]
  refine ⟨?_, ?_, ?_, ?_, hJS, hPJ_comm,
    parityConj_steinbergBraid hP A C,
    parityConj_steinberg_round_trip hP A C X⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · dsimp [parityConj]
    peirce_nf hP

end NonCommutativeOperatorRing

end InfoGeometry.Canonical.KMSStripMobiusKreinNibelungRing
end
