/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.SplitComplex
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
import InfoGeometry.Canonical.FiniteParaKahler
import InfoGeometry.Canonical.ParaKahlerLagrangianDimension
import InfoGeometry.Canonical.ParaKahlerSymplecticLagrangian
import InfoGeometry.Canonical.SuperGrassmannianManifold
import InfoGeometry.Physics.DoubleFieldTheoryO55NarainCapstone
import InfoGeometry.Algebra.FormalSeriesCalculus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.LogCFTFiniteJordanBridge
import InfoGeometry.Canonical.ParaHyperkahlerPresymplecticBridge
import InfoGeometry.Canonical.BekensteinHawkingEntropyAreaBridge
import InfoGeometry.Holography.BekensteinHawkingDyadicEntropy
import InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
import InfoGeometry.Thermo.BipolarLinearCosymplecticStructure
import InfoGeometry.Thermodynamics.SouriauKillingFlow

/-!
# Born Geometry, Para-Kähler Triad, Para-Moyal Decoupling, DFT Section, EP2 Horizon Shear & Contact/Reeb Invariance

This module formalizes Milestone M4 (`E1–E8, C1, I1–I2`) from the source transcript
`1-GdlLgiKADUPj5kLOhiqP6-a1qQ1bUea`, reusing existing repository owners directly via import:

* **E1 (`SplitComplex`)**: Scoped `CommRing` / `Algebra` instances on `SplitComplex.Carrier`,
  `productRingEquiv : Carrier R ≃+* R × R`, idempotent partition of unity `P₊ + P₋ = 1`,
  `P₊ - P₋ = e`, `e ≠ ±1`, and idempotent expansion `w = (x+y)P₊ + (x-y)P₋`.
* **E2 (Split-CR & Factorized Wave Equation)**: On `ℝ × ℝ`, `ContDiff ℝ 2` symmetry of mixed
  partials yields `4 ∂₊∂₋ U = (∂ₓ² - ∂ᵧ²) U`, `SatisfiesSplitCR U V → SatisfiesWaveEq U`,
  constructive d'Alembert solutions, and split-complex decoupling.
* **E3 (Para-Kähler Adapted Darboux Triad)**: General-`n` `PhaseSpace n := (Fin n → ℝ) × (Fin n → ℝ)`
  instantiating `ParaKahlerMaurerCartanQGT.ParaKahlerDatum`, documenting the `T33:2359` sign
  (`g(u,v) = ω(Ku,v) = -ω(u,Kv)`), nondegeneracy, eigenspace isotropy via `FiniteParaKahler`,
  and Lagrangian half-dimension `finrank = n`.
* **E4 (Para-Moyal Star Product Decoupling)**: Both scalar `PowerSeries (Carrier ℝ)` exponential
  decoupling (reusing `FormalSeriesCalculus.formalExp`) and genuine non-commutative
  `MvPolynomial (Fin n ⊕ Fin n) ℝ` Para-Moyal star product `paraMoyalStar`, with decoupling,
  cross-sector firewall `P₊ P₋ = 0`, and non-commutativity witness at order `ℏ¹`.
* **E5 (Metriplectic Rotation Identity)**: Exact Darboux vector fields proving both
  `darbouxK (X_H dS) = Y_G 1 dS` (`T35:2493` for `darbouxMetric`) and
  `darbouxK (X_H dS) = 2 • Y_G 2 dS` (`T35:2559–2561` for `2 • darbouxMetric`), explicitly
  documenting the factor-of-2 convention difference, plus `dS(X_H) = 0`.
* **E6 (DFT Strong Constraint Section Condition)**: General-`D` `etaDFT` (proved equal to
  `DoubleFieldTheory.etaO55` at `D = 5`), `η^{MN}∂_M∂_N Ψ = 2 ∑ ∂_{q^a}∂_{p_a} Ψ`, idempotent
  leaf annihilation, and linkage to `SplitCharge.hyperbolicNorm`.
* **E7 (Diagonal `λ = -2` Hyperbolic Monge–Ampère)**: Analytic mixed partial Hessian of
  `𝒦(q,p) = ∑ ln(1 + qᵃ p_a)` on `∀ a, 0 < 1 + q a * p a`, proving `det(∂_q ∂_p 𝒦) = exp(-2 𝒦)`
  (explicitly scoped to `λ = -2` diagonal pairing; noting `T33:2373` index typo).
* **E8 (Born Geometry Triad & Born Reciprocity)**: General-`n` Born triad `(g, ω, K_swap)`,
  reciprocity `K · w = e · w`, and orthogonal Cayley–Hadamard transform intertwining E3 and E8.
* **C1 (Unipotent `EP₂` Horizon Shear `ℳ_{4π}` & BH Pairing)**: Real and complex matrix exponentials
  reusing `LogCFTFiniteJordanBridge.logCFTUnipotentFlow`, symplectic preservation against
  `ParaHyperkahlerPresymplecticBridge.I_mat` & `omega2`, `EP₂` non-diagonalizability over `ℝ` and `ℂ`,
  honest negated complex matrix `horizonShear4PiNegComplex` (`(M+1)² = 0`, not unipotent), and
  `BekensteinHawkingEntropyAreaBridge` + `BekensteinHawkingDyadicEntropy` bit-step pairing.
* **I1 (Cartan Magic Formula & Contact Volume Invariance)**: `Type*`-valued
  `CartanDifferentialAlgebra`, graded-derivation proof of `ℒ_R (α * (d α)^n) = 0`, compatibility
  with `CartanLieDerivativeMagicBridge.lieDerivativeEnd`, and non-vacuous Darboux contact 3-space
  instantiation `α = dz - y dx`.
* **I2 (Conditional K-Contact Reeb–Killing Isometry & Noether Conservation)**: Concrete K-contact
  metric `g_horiz + α ⊗ α` on `BipolarLinearCosymplecticStructure.State3`, Reeb flow isometry,
  planar Killing generator, conditional Killing/Stokes Noether conservation (`[bucket_2_conditional]`),
  and `SouriauKillingFlow.hodge_star_executes_legendre_transform` compatibility bridge
  (noting `[bucket_3_open_debt]` for the physical `19 ℏ_contact` identification).
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.BornParaKahlerHorizonShear

open scoped BigOperators TensorProduct
open Matrix

/-! ## E1. Split-Complex Ring `ℂ_s` & Orthogonal Idempotents -/

namespace SplitComplexRing

open InfoGeometry.Canonical.SplitComplex

scoped instance instCommRingCarrier {R : Type*} [CommRing R] : CommRing (Carrier R) where
  add := (· + ·)
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero := 0
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  neg := (-·)
  sub := (· - ·)
  zsmul := zsmulRec
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  neg_add_cancel a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  mul := (· * ·)
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_assoc := Carrier.mul_assoc_carrier
  one := 1
  one_mul := Carrier.one_mul_carrier
  mul_one := Carrier.mul_one_carrier
  mul_comm a b := by ext <;> simp <;> ring

scoped instance instSMulCarrier {R : Type*} [CommRing R] : SMul R (Carrier R) where
  smul r a := ⟨r * a.re, r * a.im⟩

@[simp] theorem smul_re_carrier {R : Type*} [CommRing R] (r : R) (a : Carrier R) :
    (r • a).re = r * a.re := rfl

@[simp] theorem smul_im_carrier {R : Type*} [CommRing R] (r : R) (a : Carrier R) :
    (r • a).im = r * a.im := rfl

scoped instance instAlgebraCarrier {R : Type*} [CommRing R] : Algebra R (Carrier R) where
  smul := (· • ·)
  algebraMap :=
    { toFun := fun r => ⟨r, 0⟩
      map_one' := rfl
      map_mul' := fun x y => by ext <;> simp
      map_zero' := rfl
      map_add' := fun x y => by ext <;> simp }
  commutes' r a := by ext <;> simp [mul_comm]
  smul_def' r a := by
    ext
    · change r * a.re = r * a.re + 0 * a.im; ring
    · change r * a.im = r * a.im + 0 * a.re; ring

scoped instance instSMulRatCarrier : SMul ℚ (Carrier ℝ) where
  smul q a := ⟨(q : ℝ) * a.re, (q : ℝ) * a.im⟩

scoped instance instAlgebraRatCarrier : Algebra ℚ (Carrier ℝ) where
  smul := (· • ·)
  algebraMap :=
    { toFun := fun q => ⟨(q : ℝ), 0⟩
      map_one' := by ext <;> simp
      map_mul' := fun x y => by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp }
  commutes' q a := by ext <;> simp [mul_comm]
  smul_def' q a := by
    ext
    · change (q : ℝ) * a.re = (q : ℝ) * a.re + 0 * a.im; ring
    · change (q : ℝ) * a.im = (q : ℝ) * a.im + 0 * a.re; ring

/-- Upgrade `Carrier.productEquiv` to a ring isomorphism `Carrier R ≃+* R × R`. -/
def productRingEquiv {R : Type*} [Field R] [CharZero R] : Carrier R ≃+* R × R where
  toEquiv := Carrier.productEquiv
  map_mul' x y := by
    change Carrier.toProduct (x * y) = Carrier.toProduct x * Carrier.toProduct y
    exact Carrier.toProduct_mul x y
  map_add' x y := by
    ext <;> simp [Carrier.productEquiv, Carrier.toProduct] <;> ring

/-- Partition of unity: `P₊ + P₋ = 1`. -/
theorem pPlus_add_pMinus {R : Type*} [Field R] [CharZero R] :
    Carrier.pPlus (R := R) + Carrier.pMinus (R := R) = 1 := by
  ext <;> simp [Carrier.pPlus, Carrier.pMinus]
  norm_num

/-- Difference of idempotents recovers the split generator: `P₊ - P₋ = ε`. -/
theorem pPlus_sub_pMinus {R : Type*} [Field R] [CharZero R] :
    Carrier.pPlus (R := R) - Carrier.pMinus (R := R) = Carrier.eps (R := R) := by
  ext <;> simp [Carrier.pPlus, Carrier.pMinus, Carrier.eps]
  ring

/-- The split generator `ε` is neither `1` nor `-1`. -/
theorem eps_ne_one_and_neg_one {R : Type*} [Field R] [CharZero R] :
    Carrier.eps (R := R) ≠ 1 ∧ Carrier.eps (R := R) ≠ -1 := by
  constructor
  · intro h
    have hre : (0 : R) = 1 := by simpa [Carrier.eps] using congrArg Carrier.re h
    exact zero_ne_one hre
  · intro h
    have hre : (0 : R) = -1 := by simpa [Carrier.eps] using congrArg Carrier.re h
    have h1 : (1 : R) = 0 := by simpa using congrArg Neg.neg hre.symm
    exact one_ne_zero h1

/-- Idempotent expansion `w = (x + y) P₊ + (x - y) P₋`. -/
theorem splitComplex_idempotent_decomp {R : Type*} [Field R] [CharZero R] (w : Carrier R) :
    w = (⟨w.re + w.im, 0⟩ : Carrier R) * Carrier.pPlus +
      (⟨w.re - w.im, 0⟩ : Carrier R) * Carrier.pMinus := by
  ext <;> simp [Carrier.pPlus, Carrier.pMinus] <;> ring

end SplitComplexRing

open SplitComplexRing

/-! ## E2. Split-Cauchy–Riemann & Factorized Wave Equation -/

section SplitCauchyRiemann

/-- Partial derivative in the first coordinate `∂ₓ f (x, y)`. -/
def partialX (f : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f (t, y)) x

/-- Partial derivative in the second coordinate `∂ᵧ f (x, y)`. -/
def partialY (f : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f (x, t)) y

/-- Null-cone derivative `∂₊ = ½ (∂ₓ + ∂ᵧ)`. -/
def partialPlus (f : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (partialX f x y + partialY f x y)

/-- Anti-null-cone derivative `∂₋ = ½ (∂ₓ - ∂ᵧ)`. -/
def partialMinus (f : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (partialX f x y - partialY f x y)

/-- Split-Cauchy–Riemann equations `∂ₓ U = ∂ᵧ V` and `∂ᵧ U = ∂ₓ V`. -/
def SatisfiesSplitCR (U V : ℝ × ℝ → ℝ) : Prop :=
  ∀ x y, partialX U x y = partialY V x y ∧ partialY U x y = partialX V x y

/-- 1+1D wave equation `(∂ₓ² - ∂ᵧ²) U = 0`. -/
def SatisfiesWaveEq (U : ℝ × ℝ → ℝ) : Prop :=
  ∀ x y, partialX (fun p => partialX U p.1 p.2) x y -
    partialY (fun p => partialY U p.1 p.2) x y = 0

private lemma hasDerivAt_pair_left (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : ℝ)) x := by
  simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x y)

private lemma hasDerivAt_pair_right (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (x, t)) ((0 : ℝ), (1 : ℝ)) y := by
  simpa using (hasDerivAt_const y x).prodMk (hasDerivAt_id y)

private lemma partialX_eq_fderiv {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    partialX f x y = fderiv ℝ f (x, y) (1, 0) := by
  have hd : HasDerivAt (fun t => f (t, y)) (fderiv ℝ f (x, y) (1, 0)) x :=
    (hf (x, y)).hasFDerivAt.comp_hasDerivAt x (hasDerivAt_pair_left x y)
  exact hd.deriv

private lemma partialY_eq_fderiv {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    partialY f x y = fderiv ℝ f (x, y) (0, 1) := by
  have hd : HasDerivAt (fun t => f (x, t)) (fderiv ℝ f (x, y) (0, 1)) y :=
    (hf (x, y)).hasFDerivAt.comp_hasDerivAt y (hasDerivAt_pair_right x y)
  exact hd.deriv

private lemma differentiable_fderiv_eval {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (v : ℝ × ℝ) :
    Differentiable ℝ (fun p : ℝ × ℝ => fderiv ℝ f p v) := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  exact (hf1.differentiable (by norm_num)).clm_apply (differentiable_const v)

private lemma fderiv_eval_eq {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (p v w : ℝ × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ f q v) p w = fderiv ℝ (fderiv ℝ f) p w v := by
  have hf1 : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) p
  have hclm := (hf1.hasFDerivAt.clm_apply (hasFDerivAt_const v p)).fderiv
  have hw := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L w) hclm
  simpa using hw

/-- Symmetry of mixed partial derivatives for `C²` functions on `ℝ × ℝ`. -/
theorem mixed_partials_commute {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x y : ℝ) :
    partialX (fun p => partialY f p.1 p.2) x y =
      partialY (fun p => partialX f p.1 p.2) x y := by
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfunX : (fun p : ℝ × ℝ => partialX f p.1 p.2) = fun p => fderiv ℝ f p (1, 0) := by
    ext p; exact partialX_eq_fderiv hf_diff p.1 p.2
  have hfunY : (fun p : ℝ × ℝ => partialY f p.1 p.2) = fun p => fderiv ℝ f p (0, 1) := by
    ext p; exact partialY_eq_fderiv hf_diff p.1 p.2
  rw [hfunY, hfunX]
  rw [partialX_eq_fderiv (differentiable_fderiv_eval hf (0, 1)) x y]
  rw [partialY_eq_fderiv (differentiable_fderiv_eval hf (1, 0)) x y]
  rw [fderiv_eval_eq hf (x, y) (0, 1) (1, 0), fderiv_eval_eq hf (x, y) (1, 0) (0, 1)]
  have hsymm : IsSymmSndFDerivAt ℝ f (x, y) :=
    (hf.contDiffAt).isSymmSndFDerivAt (n := 2) (by norm_num)
  exact hsymm.eq (1, 0) (0, 1)

/-- Factorization of the wave operator: `4 ∂₊ ∂₋ U = (∂ₓ² - ∂ᵧ²) U`. -/
theorem wave_factorization {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ 2 U) (x y : ℝ) :
    4 * partialPlus (fun p => partialMinus U p.1 p.2) x y =
      partialX (fun p => partialX U p.1 p.2) x y -
        partialY (fun p => partialY U p.1 p.2) x y := by
  have hU_diff : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hX_diff : Differentiable ℝ (fun p : ℝ × ℝ => partialX U p.1 p.2) := by
    have hfun : (fun p : ℝ × ℝ => partialX U p.1 p.2) = fun p => fderiv ℝ U p (1, 0) := by
      ext p; exact partialX_eq_fderiv hU_diff p.1 p.2
    rw [hfun]
    exact differentiable_fderiv_eval hU (1, 0)
  have hY_diff : Differentiable ℝ (fun p : ℝ × ℝ => partialY U p.1 p.2) := by
    have hfun : (fun p : ℝ × ℝ => partialY U p.1 p.2) = fun p => fderiv ℝ U p (0, 1) := by
      ext p; exact partialY_eq_fderiv hU_diff p.1 p.2
    rw [hfun]
    exact differentiable_fderiv_eval hU (0, 1)
  have hX_line : ∀ y', DifferentiableAt ℝ (fun t => partialX U t y') x := fun y' =>
    (hX_diff.comp (differentiable_id.prodMk (differentiable_const y'))) x
  have hY_line : ∀ y', DifferentiableAt ℝ (fun t => partialY U t y') x := fun y' =>
    (hY_diff.comp (differentiable_id.prodMk (differentiable_const y'))) x
  have hX_lineY : ∀ x', DifferentiableAt ℝ (fun t => partialX U x' t) y := fun x' =>
    (hX_diff.comp ((differentiable_const x').prodMk differentiable_id)) y
  have hY_lineY : ∀ x', DifferentiableAt ℝ (fun t => partialY U x' t) y := fun x' =>
    (hY_diff.comp ((differentiable_const x').prodMk differentiable_id)) y
  have hpX : partialX (fun p => partialMinus U p.1 p.2) x y =
      (1 / 2 : ℝ) * (partialX (fun p => partialX U p.1 p.2) x y -
        partialX (fun p => partialY U p.1 p.2) x y) := by
    dsimp [partialX, partialMinus]
    have hd : HasDerivAt (fun t => (1 / 2 : ℝ) * (partialX U t y - partialY U t y))
        ((1 / 2 : ℝ) * (deriv (fun t => partialX U t y) x - deriv (fun t => partialY U t y) x)) x :=
      ((hX_line y).hasDerivAt.sub (hY_line y).hasDerivAt).const_mul (1 / 2 : ℝ)
    exact hd.deriv
  have hpY : partialY (fun p => partialMinus U p.1 p.2) x y =
      (1 / 2 : ℝ) * (partialY (fun p => partialX U p.1 p.2) x y -
        partialY (fun p => partialY U p.1 p.2) x y) := by
    dsimp [partialY, partialMinus]
    have hd : HasDerivAt (fun t => (1 / 2 : ℝ) * (partialX U x t - partialY U x t))
        ((1 / 2 : ℝ) * (deriv (fun t => partialX U x t) y - deriv (fun t => partialY U x t) y)) y :=
      ((hX_lineY x).hasDerivAt.sub (hY_lineY x).hasDerivAt).const_mul (1 / 2 : ℝ)
    exact hd.deriv
  dsimp [partialPlus]
  rw [hpX, hpY, mixed_partials_commute hU x y]
  ring

/-- Split-Cauchy–Riemann implies the 1+1D wave equation `(∂ₓ² - ∂ᵧ²) U = 0`. -/
theorem splitCR_implies_wave {U V : ℝ × ℝ → ℝ}
    (hV : ContDiff ℝ 2 V) (hCR : SatisfiesSplitCR U V) :
    SatisfiesWaveEq U := by
  intro x y
  have h1 : (fun p : ℝ × ℝ => partialX U p.1 p.2) = fun p => partialY V p.1 p.2 := by
    ext p; exact (hCR p.1 p.2).1
  have h2 : (fun p : ℝ × ℝ => partialY U p.1 p.2) = fun p => partialX V p.1 p.2 := by
    ext p; exact (hCR p.1 p.2).2
  rw [h1, h2, mixed_partials_commute hV x y, sub_self]

/-- Constructive d'Alembert family satisfies both Split-CR and the wave equation. -/
theorem dalambert_splitCR_and_wave (fPlus fMinus : ℝ → ℝ)
    (hfP : ContDiff ℝ 2 fPlus) (hfM : ContDiff ℝ 2 fMinus) :
    let U := fun p : ℝ × ℝ => fPlus (p.1 + p.2) + fMinus (p.1 - p.2)
    let V := fun p : ℝ × ℝ => fPlus (p.1 + p.2) - fMinus (p.1 - p.2)
    SatisfiesSplitCR U V ∧ SatisfiesWaveEq U := by
  intro U V
  have hP_diff : Differentiable ℝ fPlus := hfP.differentiable (by norm_num)
  have hM_diff : Differentiable ℝ fMinus := hfM.differentiable (by norm_num)
  have hU_c2 : ContDiff ℝ 2 U :=
    (hfP.comp (contDiff_fst.add contDiff_snd)).add
      (hfM.comp (contDiff_fst.sub contDiff_snd))
  have hV_c2 : ContDiff ℝ 2 V :=
    (hfP.comp (contDiff_fst.add contDiff_snd)).sub
      (hfM.comp (contDiff_fst.sub contDiff_snd))
  have hCR : SatisfiesSplitCR U V := by
    intro x y
    have dPx := (hP_diff (x + y)).hasDerivAt.comp x ((hasDerivAt_id x).add_const y)
    have dMx := (hM_diff (x - y)).hasDerivAt.comp x ((hasDerivAt_id x).sub_const y)
    have dPy := (hP_diff (x + y)).hasDerivAt.comp y ((hasDerivAt_const y x).add (hasDerivAt_id y))
    have dMy := (hM_diff (x - y)).hasDerivAt.comp y ((hasDerivAt_const y x).sub (hasDerivAt_id y))
    have hUX : partialX U x y = deriv fPlus (x + y) + deriv fMinus (x - y) := by
      have hd : HasDerivAt (fun t => fPlus (t + y) + fMinus (t - y))
          (deriv fPlus (x + y) * 1 + deriv fMinus (x - y) * 1) x := dPx.add dMx
      rw [partialX]
      change deriv (fun t => fPlus (t + y) + fMinus (t - y)) x = _
      rw [hd.deriv]
      ring
    have hUY : partialY U x y = deriv fPlus (x + y) - deriv fMinus (x - y) := by
      have hd : HasDerivAt (fun t => fPlus (x + t) + fMinus (x - t))
          (deriv fPlus (x + y) * (0 + 1) + deriv fMinus (x - y) * (0 - 1)) y := dPy.add dMy
      rw [partialY]
      change deriv (fun t => fPlus (x + t) + fMinus (x - t)) y = _
      rw [hd.deriv]
      ring
    have hVX : partialX V x y = deriv fPlus (x + y) - deriv fMinus (x - y) := by
      have hd : HasDerivAt (fun t => fPlus (t + y) - fMinus (t - y))
          (deriv fPlus (x + y) * 1 - deriv fMinus (x - y) * 1) x := dPx.sub dMx
      rw [partialX]
      change deriv (fun t => fPlus (t + y) - fMinus (t - y)) x = _
      rw [hd.deriv]
      ring
    have hVY : partialY V x y = deriv fPlus (x + y) + deriv fMinus (x - y) := by
      have hd : HasDerivAt (fun t => fPlus (x + t) - fMinus (x - t))
          (deriv fPlus (x + y) * (0 + 1) - deriv fMinus (x - y) * (0 - 1)) y := dPy.sub dMy
      rw [partialY]
      change deriv (fun t => fPlus (x + t) - fMinus (x - t)) y = _
      rw [hd.deriv]
      ring
    exact ⟨hUX.trans hVY.symm, hUY.trans hVX.symm⟩
  exact ⟨hCR, splitCR_implies_wave hV_c2 hCR⟩

/-- Split-complex idempotent decoupling of the d'Alembert family. -/
theorem dalambert_splitComplex_decoupling (fPlus fMinus : ℝ → ℝ) (x y : ℝ) :
    let U := fPlus (x + y) + fMinus (x - y)
    let V := fPlus (x + y) - fMinus (x - y)
    (⟨U, V⟩ : InfoGeometry.Canonical.SplitComplex.Carrier ℝ) =
      ⟨2 * fPlus (x + y), 0⟩ * InfoGeometry.Canonical.SplitComplex.Carrier.pPlus +
        ⟨2 * fMinus (x - y), 0⟩ * InfoGeometry.Canonical.SplitComplex.Carrier.pMinus := by
  intro U V
  rw [splitComplex_idempotent_decomp (⟨U, V⟩ : InfoGeometry.Canonical.SplitComplex.Carrier ℝ)]
  have h1 : U + V = 2 * fPlus (x + y) := by dsimp [U, V]; ring
  have h2 : U - V = 2 * fMinus (x - y) := by dsimp [U, V]; ring
  simp only [h1, h2]

end SplitCauchyRiemann

/-! ## E3. General-`n` Para-Kähler Adapted Darboux Triad -/

section DarbouxParaKahler

open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
open InfoGeometry.Canonical.FiniteParaKahler

/-- `2n`-dimensional real Darboux phase space `(q, p)`. -/
abbrev PhaseSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

/-- Darboux para-complex involution `K (q, p) = (q, -p)`. -/
def darbouxK (n : ℕ) : PhaseSpace n →ₗ[ℝ] PhaseSpace n where
  toFun v := (v.1, -v.2)
  map_add' u v := by
    ext i
    · simp
    · simp; ring
  map_smul' c v := by ext i <;> simp

/-- Neutral Darboux metric `g(u, v) = ∑ a, (u.q a * v.p a + u.p a * v.q a)`. -/
def darbouxMetric (n : ℕ) : LinearMap.BilinForm ℝ (PhaseSpace n) :=
  LinearMap.mk₂ ℝ
    (fun u v => ∑ a : Fin n, (u.1 a * v.2 a + u.2 a * v.1 a))
    (fun u v w => by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [add_mul, mul_add]
      abel)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mul_add, mul_assoc])
    (fun u v w => by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [add_mul, mul_add]
      abel)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mul_add, mul_assoc, mul_left_comm])

/-- Canonical Darboux symplectic 2-form `ω(u, v) = ∑ a, (u.q a * v.p a - u.p a * v.q a)`. -/
def darbouxSymplectic (n : ℕ) : LinearMap.BilinForm ℝ (PhaseSpace n) :=
  LinearMap.mk₂ ℝ
    (fun u v => ∑ a : Fin n, (u.1 a * v.2 a - u.2 a * v.1 a))
    (fun u v w => by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [add_mul, mul_add, sub_add_sub_comm])
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mul_sub, mul_assoc])
    (fun u v w => by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [add_mul, mul_add, sub_add_sub_comm])
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mul_sub, mul_assoc, mul_left_comm])

@[simp] theorem darbouxK_apply (n : ℕ) (v : PhaseSpace n) :
    darbouxK n v = (v.1, -v.2) := rfl

@[simp] theorem darbouxMetric_apply (n : ℕ) (u v : PhaseSpace n) :
    darbouxMetric n u v = ∑ a : Fin n, (u.1 a * v.2 a + u.2 a * v.1 a) := rfl

@[simp] theorem darbouxSymplectic_apply (n : ℕ) (u v : PhaseSpace n) :
    darbouxSymplectic n u v = ∑ a : Fin n, (u.1 a * v.2 a - u.2 a * v.1 a) := rfl

/-- Darboux `ParaComplexStructure` instantiating `ParaKahlerMaurerCartanQGT`. -/
def darbouxParaComplex (n : ℕ) : ParaComplexStructure ℝ (PhaseSpace n) where
  K := darbouxK n
  K_sq := by
    ext v i <;> simp [darbouxK]

/-- Darboux `ParaKahlerDatum` instantiating `ParaKahlerMaurerCartanQGT.ParaKahlerDatum`. -/
def darbouxParaKahlerDatum (n : ℕ) : ParaKahlerDatum ℝ (PhaseSpace n) where
  metric := darbouxMetric n
  para := darbouxParaComplex n
  metric_symm u v := by
    simp only [darbouxMetric_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  metric_anti_compat u v := by
    simp only [darbouxMetric_apply, darbouxParaComplex, darbouxK_apply, Pi.neg_apply,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

/-- The Para-Berry 2-form of `darbouxParaKahlerDatum` coincides with `darbouxSymplectic`. -/
theorem darbouxParaKahlerDatum_paraBerryTwoForm (n : ℕ) (u v : PhaseSpace n) :
    (darbouxParaKahlerDatum n).paraBerryTwoForm u v = darbouxSymplectic n u v := by
  simp only [ParaKahlerDatum.paraBerryTwoForm, darbouxParaKahlerDatum, darbouxParaComplex,
    darbouxMetric_apply, darbouxK_apply, darbouxSymplectic_apply, Pi.neg_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Sign reconciliation for `T33:2359`: with `K = diag(I, -I)`, `g(u,v) = ω(Ku, v)`. -/
theorem darbouxMetric_eq_symplectic_K_left (n : ℕ) (u v : PhaseSpace n) :
    darbouxMetric n u v = darbouxSymplectic n (darbouxK n u) v := by
  simp only [darbouxMetric_apply, darbouxSymplectic_apply, darbouxK_apply, Pi.neg_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Sign reconciliation for `T33:2359`: putting `K` on the right flips sign, `g(u,v) = -ω(u, Kv)`. -/
theorem darbouxMetric_eq_neg_symplectic_K_right (n : ℕ) (u v : PhaseSpace n) :
    darbouxMetric n u v = -darbouxSymplectic n u (darbouxK n v) := by
  simp only [darbouxMetric_apply, darbouxSymplectic_apply, darbouxK_apply, Pi.neg_apply,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Nondegeneracy of the Darboux neutral metric. -/
theorem darbouxMetric_nondegenerate (n : ℕ) : (darbouxMetric n).Nondegenerate := by
  constructor
  · intro u hu
    ext i
    · have h := hu (0, Pi.single i 1)
      simpa [darbouxMetric_apply, Pi.single_apply] using h
    · have h := hu (Pi.single i 1, 0)
      simpa [darbouxMetric_apply, Pi.single_apply] using h
  · intro v hv
    ext i
    · have h := hv (0, Pi.single i 1)
      simpa [darbouxMetric_apply, Pi.single_apply] using h
    · have h := hv (Pi.single i 1, 0)
      simpa [darbouxMetric_apply, Pi.single_apply] using h

/-- Dual identification via `FiniteParaKahler.metric_toDual_apply`. -/
theorem darbouxMetric_toDual_apply (n : ℕ) (u v : PhaseSpace n) :
    (darbouxParaKahlerDatum n).metric.toDual (darbouxMetric_nondegenerate n) u v =
      darbouxMetric n u v :=
  metric_toDual_apply (darbouxParaKahlerDatum n) (darbouxMetric_nondegenerate n) u v

/-- Both `+1` and `-1` Darboux eigensheets are totally isotropic (via `FiniteParaKahler`). -/
theorem darboux_sheet_isotropic (n : ℕ) :
    (∀ u v, darbouxK n u = u → darbouxK n v = v → darbouxMetric n u v = 0) ∧
      (∀ u v, darbouxK n u = -u → darbouxK n v = -v → darbouxMetric n u v = 0) :=
  ⟨fun _ _ hu hv => plus_metric_isotropic (darbouxParaKahlerDatum n) hu hv,
   fun _ _ hu hv => minus_metric_isotropic (darbouxParaKahlerDatum n) hu hv⟩

/-- The `+1` Darboux eigensheet `range ((1/2) • (id + K))` has exact dimension `n`. -/
theorem darboux_lagrangian_finrank (n : ℕ) :
    Module.finrank ℝ (LinearMap.range ((1 / 2 : ℝ) • (LinearMap.id + darbouxK n))) = n := by
  let P := (1 / 2 : ℝ) • (LinearMap.id + darbouxK n)
  have hmem : ∀ q : Fin n → ℝ, (q, (0 : Fin n → ℝ)) ∈ LinearMap.range P := by
    intro q
    refine ⟨(q, 0), ?_⟩
    ext i
    · simp [P, darbouxK]; ring
    · simp [P, darbouxK]
  let e : (Fin n → ℝ) ≃ₗ[ℝ] LinearMap.range P :=
    { toFun := fun q => ⟨(q, 0), hmem q⟩
      invFun := fun v => v.1.1
      left_inv := fun q => rfl
      right_inv := by
        rintro ⟨⟨q, p⟩, ⟨⟨q0, p0⟩, h⟩⟩
        apply Subtype.ext
        have h1 : (1 / 2 : ℝ) • (q0 + q0) = q := by
          have := congrArg Prod.fst h
          simpa [P, darbouxK] using this
        have h2 : (1 / 2 : ℝ) • (p0 + -p0) = p := by
          have := congrArg Prod.snd h
          simpa [P, darbouxK] using this
        have hp : p = 0 := by
          rw [← h2]
          ext i
          simp
        subst hp
        rfl
      map_add' := fun x y => by apply Subtype.ext; ext i <;> simp
      map_smul' := fun c x => by apply Subtype.ext; ext i <;> simp }
  rw [← LinearEquiv.finrank_eq e, Module.finrank_fin_fun]

end DarbouxParaKahler

/-! ## E4. Formal Power-Series Para-Moyal Decoupling -/

section ParaMoyal

open InfoGeometry.Canonical.SplitComplex
open InfoGeometry.Algebra.FormalSeriesCalculus

/-- Embed a real formal power series into the `P₊` sector of `PowerSeries (Carrier ℝ)`. -/
def embedPlusSeries (s : PowerSeries ℝ) : PowerSeries (Carrier ℝ) :=
  PowerSeries.mk fun k =>
    ⟨PowerSeries.coeff k s / 2, PowerSeries.coeff k s / 2⟩

/-- Embed a real formal power series into the `P₋` sector of `PowerSeries (Carrier ℝ)`. -/
def embedMinusSeries (s : PowerSeries ℝ) : PowerSeries (Carrier ℝ) :=
  PowerSeries.mk fun k =>
    ⟨PowerSeries.coeff k s / 2, -(PowerSeries.coeff k s / 2)⟩

private theorem eps_pow_eq_ite {R : Type*} [CommRing R] (k : ℕ) :
    (Carrier.eps (R := R)) ^ k = if Even k then 1 else Carrier.eps (R := R) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    by_cases hn : Even n
    · have hodd : ¬Even (n + 1) := by simpa [Nat.even_add_one] using hn
      simp [hn, hodd]
    · have hev : Even (n + 1) := by simpa [Nat.even_add_one] using hn
      simp [hn, hev, Carrier.eps_sq]

/-- Scalar Para-Moyal formal exponential decoupling in `PowerSeries (Carrier ℝ)`,
reusing `FormalSeriesCalculus.formalExp`. -/
theorem exp_eps_half_X_decoupling :
    PowerSeries.rescale ((1 / 2 : ℝ) • Carrier.eps (R := ℝ)) (formalExp (Carrier ℝ)) =
      embedPlusSeries (PowerSeries.rescale (1 / 2 : ℝ) (formalExp ℝ)) +
        embedMinusSeries (PowerSeries.rescale (-(1 / 2 : ℝ)) (formalExp ℝ)) := by
  ext k
  · simp only [PowerSeries.coeff_rescale, coeff_formalExp, map_add, PowerSeries.coeff_mk,
      embedPlusSeries, embedMinusSeries, Carrier.add_re]
    change (((((1 / 2 : ℝ) • Carrier.eps (R := ℝ)) ^ k) *
      algebraMap ℚ (Carrier ℝ) (1 / (k.factorial : ℚ))).re) = _
    rw [smul_pow, eps_pow_eq_ite]
    by_cases hk : Even k
    · have hneg : (-2⁻¹ : ℝ) ^ k = (2⁻¹ : ℝ) ^ k := by
        simpa using hk.neg_pow (2⁻¹ : ℝ)
      simp only [hk, ↓reduceIte]
      change (((1 / 2 : ℝ) ^ k • (1 : Carrier ℝ)) *
        (⟨((1 / (k.factorial : ℚ) : ℚ) : ℝ), 0⟩ : Carrier ℝ)).re = _
      simp only [Carrier.mul_re, smul_re_carrier, smul_im_carrier, Carrier.one_re,
        Carrier.one_im, mul_one, mul_zero, add_zero, one_div, Rat.cast_inv, Rat.cast_natCast]
      rw [show (algebraMap ℚ ℝ) (k.factorial : ℚ)⁻¹ = (k.factorial : ℝ)⁻¹ by simp, hneg]
      ring
    · have hneg : (-2⁻¹ : ℝ) ^ k = -((2⁻¹ : ℝ) ^ k) := by
        simpa using (Nat.not_even_iff_odd.mp hk).neg_pow (2⁻¹ : ℝ)
      simp only [hk, ↓reduceIte]
      change (((1 / 2 : ℝ) ^ k • (Carrier.eps : Carrier ℝ)) *
        (⟨((1 / (k.factorial : ℚ) : ℚ) : ℝ), 0⟩ : Carrier ℝ)).re = _
      simp only [Carrier.mul_re, smul_re_carrier, smul_im_carrier, Carrier.eps_re,
        Carrier.eps_im, mul_zero, mul_one, zero_mul, add_zero, one_div, Rat.cast_inv, Rat.cast_natCast]
      rw [show (algebraMap ℚ ℝ) (k.factorial : ℚ)⁻¹ = (k.factorial : ℝ)⁻¹ by simp, hneg]
      ring
  · simp only [PowerSeries.coeff_rescale, coeff_formalExp, map_add, PowerSeries.coeff_mk,
      embedPlusSeries, embedMinusSeries, Carrier.add_im]
    change (((((1 / 2 : ℝ) • Carrier.eps (R := ℝ)) ^ k) *
      algebraMap ℚ (Carrier ℝ) (1 / (k.factorial : ℚ))).im) = _
    rw [smul_pow, eps_pow_eq_ite]
    by_cases hk : Even k
    · have hneg : (-2⁻¹ : ℝ) ^ k = (2⁻¹ : ℝ) ^ k := by
        simpa using hk.neg_pow (2⁻¹ : ℝ)
      simp only [hk, ↓reduceIte]
      change (((1 / 2 : ℝ) ^ k • (1 : Carrier ℝ)) *
        (⟨((1 / (k.factorial : ℚ) : ℚ) : ℝ), 0⟩ : Carrier ℝ)).im = _
      simp only [Carrier.mul_im, smul_re_carrier, smul_im_carrier, Carrier.one_re,
        Carrier.one_im, mul_zero, mul_one, one_div, Rat.cast_inv, Rat.cast_natCast]
      rw [show (algebraMap ℚ ℝ) (k.factorial : ℚ)⁻¹ = (k.factorial : ℝ)⁻¹ by simp, hneg]
      ring
    · have hneg : (-2⁻¹ : ℝ) ^ k = -((2⁻¹ : ℝ) ^ k) := by
        simpa using (Nat.not_even_iff_odd.mp hk).neg_pow (2⁻¹ : ℝ)
      simp only [hk, ↓reduceIte]
      change (((1 / 2 : ℝ) ^ k • (Carrier.eps : Carrier ℝ)) *
        (⟨((1 / (k.factorial : ℚ) : ℚ) : ℝ), 0⟩ : Carrier ℝ)).im = _
      simp only [Carrier.mul_im, smul_re_carrier, smul_im_carrier, Carrier.eps_re,
        Carrier.eps_im, mul_zero, mul_one, zero_add, one_div, Rat.cast_inv, Rat.cast_natCast]
      rw [show (algebraMap ℚ ℝ) (k.factorial : ℚ)⁻¹ = (k.factorial : ℝ)⁻¹ by simp, hneg]
      ring

/-- Phase-space polynomial observable algebra `ℝ[q₁,…,qₙ, p₁,…,pₙ]`. -/
abbrev PhasePoly (n : ℕ) := MvPolynomial (Fin n ⊕ Fin n) ℝ

/-- `k`-th iterated Poisson bidifferential operator `𝒫ᵏ(f, g)`. -/
def poissonBideriv {n : ℕ} : ℕ → PhasePoly n → PhasePoly n → PhasePoly n
  | 0, f, g => f * g
  | k + 1, f, g =>
    ∑ a : Fin n,
      (poissonBideriv k (MvPolynomial.pderiv (Sum.inl a) f) (MvPolynomial.pderiv (Sum.inr a) g) -
       poissonBideriv k (MvPolynomial.pderiv (Sum.inr a) f) (MvPolynomial.pderiv (Sum.inl a) g))

private lemma poissonBideriv_add_left {n : ℕ} :
    ∀ (k : ℕ) (f₁ f₂ g : PhasePoly n),
      poissonBideriv k (f₁ + f₂) g = poissonBideriv k f₁ g + poissonBideriv k f₂ g
  | 0, f₁, f₂, g => by simp [poissonBideriv, add_mul]
  | k + 1, f₁, f₂, g => by
    simp only [poissonBideriv, map_add, poissonBideriv_add_left k]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

private lemma poissonBideriv_add_right {n : ℕ} :
    ∀ (k : ℕ) (f g₁ g₂ : PhasePoly n),
      poissonBideriv k f (g₁ + g₂) = poissonBideriv k f g₁ + poissonBideriv k f g₂
  | 0, f, g₁, g₂ => by simp [poissonBideriv, mul_add]
  | k + 1, f, g₁, g₂ => by
    simp only [poissonBideriv, map_add, poissonBideriv_add_right k]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

private lemma poissonBideriv_sub_left {n : ℕ} :
    ∀ (k : ℕ) (f₁ f₂ g : PhasePoly n),
      poissonBideriv k (f₁ - f₂) g = poissonBideriv k f₁ g - poissonBideriv k f₂ g
  | 0, f₁, f₂, g => by simp [poissonBideriv, sub_mul]
  | k + 1, f₁, f₂, g => by
    simp only [poissonBideriv, map_sub, poissonBideriv_sub_left k]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

private lemma poissonBideriv_sub_right {n : ℕ} :
    ∀ (k : ℕ) (f g₁ g₂ : PhasePoly n),
      poissonBideriv k f (g₁ - g₂) = poissonBideriv k f g₁ - poissonBideriv k f g₂
  | 0, f, g₁, g₂ => by simp [poissonBideriv, mul_sub]
  | k + 1, f, g₁, g₂ => by
    simp only [poissonBideriv, map_sub, poissonBideriv_sub_right k]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

private lemma poissonBideriv_neg_left {n : ℕ} (k : ℕ) (f g : PhasePoly n) :
    poissonBideriv k (-f) g = -poissonBideriv k f g := by
  have h := poissonBideriv_sub_left k 0 f g
  have h0 : ∀ m (x : PhasePoly n), poissonBideriv m 0 x = 0 := by
    intro m
    induction m with
    | zero => intro x; simp [poissonBideriv]
    | succ m ih => intro x; simp [poissonBideriv, ih]
  rw [zero_sub, h0] at h
  simpa using h

private lemma poissonBideriv_neg_right {n : ℕ} (k : ℕ) (f g : PhasePoly n) :
    poissonBideriv k f (-g) = -poissonBideriv k f g := by
  have h := poissonBideriv_sub_right k f 0 g
  have h0 : ∀ m (x : PhasePoly n), poissonBideriv m x 0 = 0 := by
    intro m
    induction m with
    | zero => intro x; simp [poissonBideriv]
    | succ m ih => intro x; simp [poissonBideriv, ih]
  rw [zero_sub, h0] at h
  simpa using h

/-- Standard Moyal star product `f ⋆_s g = ∑ (sᵏ / k!) 𝒫ᵏ(f, g)` in `PowerSeries (PhasePoly n)`. -/
def moyalStar {n : ℕ} (s : ℝ) (f g : PhasePoly n) : PowerSeries (PhasePoly n) :=
  PowerSeries.mk fun k => ((s ^ k) / (k.factorial : ℝ)) • poissonBideriv k f g

/-- Embed `PowerSeries (PhasePoly n)` into the `P₊` sector of `PowerSeries (Carrier (PhasePoly n))`. -/
def embedPlusPoly {n : ℕ} (s : PowerSeries (PhasePoly n)) :
    PowerSeries (Carrier (PhasePoly n)) :=
  PowerSeries.mk fun k =>
    ⟨(1 / 2 : ℝ) • PowerSeries.coeff k s, (1 / 2 : ℝ) • PowerSeries.coeff k s⟩

/-- Embed `PowerSeries (PhasePoly n)` into the `P₋` sector of `PowerSeries (Carrier (PhasePoly n))`. -/
def embedMinusPoly {n : ℕ} (s : PowerSeries (PhasePoly n)) :
    PowerSeries (Carrier (PhasePoly n)) :=
  PowerSeries.mk fun k =>
    ⟨(1 / 2 : ℝ) • PowerSeries.coeff k s, -((1 / 2 : ℝ) • PowerSeries.coeff k s)⟩

/-- `ℂ_s`-bilinear extension of `poissonBideriv k` to `Carrier (PhasePoly n)`:
`𝒫ᵏ(f₁ + e f₂, g₁ + e g₂) = (𝒫ᵏ(f₁,g₁) + 𝒫ᵏ(f₂,g₂)) + e (𝒫ᵏ(f₁,g₂) + 𝒫ᵏ(f₂,g₁))`. -/
def carrierPoissonBideriv {n : ℕ} (k : ℕ) (F G : Carrier (PhasePoly n)) :
    Carrier (PhasePoly n) :=
  ⟨poissonBideriv k F.re G.re + poissonBideriv k F.im G.im,
   poissonBideriv k F.re G.im + poissonBideriv k F.im G.re⟩

/-- Formal Para-Moyal star product `F ⋆_e G = ∑ ((1/2)ᵏ / k!) εᵏ · 𝒫ᵏ(F, G)`. -/
def paraMoyalStar {n : ℕ} (F G : Carrier (PhasePoly n)) :
    PowerSeries (Carrier (PhasePoly n)) :=
  PowerSeries.mk fun k =>
    let c : ℝ := (1 / 2 : ℝ) ^ k / (k.factorial : ℝ)
    let P := carrierPoissonBideriv k F G
    let epsk := Carrier.eps (R := PhasePoly n) ^ k
    ⟨c • (epsk * P).re, c • (epsk * P).im⟩

private lemma smul_half_plus_plus {M : Type*} [AddCommGroup M] [Module ℝ M] (c : ℝ) (a b : M) :
    (1 / 2 * c) • (a + b) + (1 / 2 * c) • (a - b) = c • a := by
  simp only [smul_add, smul_sub]
  have h : ((1 / 2 * c) • a + (1 / 2 * c) • b) + ((1 / 2 * c) • a - (1 / 2 * c) • b) =
      (1 / 2 * c + 1 / 2 * c) • a := by
    simp only [add_smul]; abel
  rw [h]
  have h1 : (1 / 2 : ℝ) * c + 1 / 2 * c = c := by ring
  rw [h1]

private lemma smul_half_plus_minus {M : Type*} [AddCommGroup M] [Module ℝ M] (c : ℝ) (a b : M) :
    (1 / 2 * c) • (a + b) + (1 / 2 * (-c)) • (a - b) = c • b := by
  simp only [smul_add, smul_sub]
  have h : (1 / 2 * c) • a + (1 / 2 * c) • b + ((1 / 2 * (-c)) • a - (1 / 2 * (-c)) • b) =
      (1 / 2 * c + 1 / 2 * (-c)) • a + (1 / 2 * c - 1 / 2 * (-c)) • b := by
    simp only [add_smul, sub_smul]; abel
  rw [h]
  have h1 : (1 / 2 : ℝ) * c + 1 / 2 * (-c) = 0 := by ring
  have h2 : (1 / 2 : ℝ) * c - 1 / 2 * (-c) = c := by ring
  rw [h1, h2, zero_smul, zero_add]

private lemma smul_half_sub_plus {M : Type*} [AddCommGroup M] [Module ℝ M] (c : ℝ) (a b : M) :
    (1 / 2 * c) • (a + b) + -((1 / 2 * c) • (a - b)) = c • b := by
  simp only [smul_add, smul_sub]
  have h : (1 / 2 * c) • a + (1 / 2 * c) • b + -((1 / 2 * c) • a - (1 / 2 * c) • b) =
      (1 / 2 * c - 1 / 2 * c) • a + (1 / 2 * c + 1 / 2 * c) • b := by
    simp only [add_smul, sub_smul]; abel
  rw [h, sub_self, zero_smul, zero_add]
  have h2 : (1 / 2 : ℝ) * c + 1 / 2 * c = c := by ring
  rw [h2]

private lemma smul_half_sub_minus {M : Type*} [AddCommGroup M] [Module ℝ M] (c : ℝ) (a b : M) :
    (1 / 2 * c) • (a + b) + -((1 / 2 * (-c)) • (a - b)) = c • a := by
  simp only [smul_add, smul_sub]
  have h : (1 / 2 * c) • a + (1 / 2 * c) • b + -((1 / 2 * (-c)) • a - (1 / 2 * (-c)) • b) =
      (1 / 2 * c - 1 / 2 * (-c)) • a + (1 / 2 * c + 1 / 2 * (-c)) • b := by
    simp only [add_smul, sub_smul]; abel
  rw [h]
  have h1 : (1 / 2 : ℝ) * c - 1 / 2 * (-c) = c := by ring
  have h2 : (1 / 2 : ℝ) * c + 1 / 2 * (-c) = 0 := by ring
  rw [h1, h2, zero_smul, add_zero]

/-- **Para-Moyal Decoupling Theorem**:
`F ⋆_e G = (F₊ ⋆_{1/2} G₊) P₊ + (F₋ ⋆_{-1/2} G₋) P₋` to all orders in `ℏ`. -/
theorem paraMoyalStar_decoupling {n : ℕ} (F G : Carrier (PhasePoly n)) :
    paraMoyalStar F G =
      embedPlusPoly (moyalStar (1 / 2) (F.re + F.im) (G.re + G.im)) +
        embedMinusPoly (moyalStar (-(1 / 2)) (F.re - F.im) (G.re - G.im)) := by
  have hplus : ∀ k : ℕ,
      poissonBideriv k (F.re + F.im) (G.re + G.im) =
        (poissonBideriv k F.re G.re + poissonBideriv k F.im G.im) +
          (poissonBideriv k F.re G.im + poissonBideriv k F.im G.re) := by
    intro k
    rw [poissonBideriv_add_left, poissonBideriv_add_right, poissonBideriv_add_right]
    abel
  have hminus : ∀ k : ℕ,
      poissonBideriv k (F.re - F.im) (G.re - G.im) =
        (poissonBideriv k F.re G.re + poissonBideriv k F.im G.im) -
          (poissonBideriv k F.re G.im + poissonBideriv k F.im G.re) := by
    intro k
    rw [poissonBideriv_sub_left, poissonBideriv_sub_right, poissonBideriv_sub_right]
    abel
  apply PowerSeries.ext
  intro k
  apply Carrier.ext
  · simp only [paraMoyalStar, embedPlusPoly, embedMinusPoly, moyalStar, map_add,
      PowerSeries.coeff_mk, Carrier.add_re]
    rw [eps_pow_eq_ite, hplus k, hminus k]
    set A := poissonBideriv k F.re G.re + poissonBideriv k F.im G.im
    set B := poissonBideriv k F.re G.im + poissonBideriv k F.im G.re
    by_cases hk : Even k
    · have hneg : (-(1 / 2 : ℝ)) ^ k = (1 / 2 : ℝ) ^ k := hk.neg_pow (1 / 2 : ℝ)
      simp only [hk, ↓reduceIte, one_mul, carrierPoissonBideriv, hneg, smul_smul]
      exact (smul_half_plus_plus ((1 / 2 : ℝ) ^ k / (k.factorial : ℝ)) A B).symm
    · have hneg : (-(1 / 2 : ℝ)) ^ k = -((1 / 2 : ℝ) ^ k) :=
        (Nat.not_even_iff_odd.mp hk).neg_pow (1 / 2 : ℝ)
      simp only [hk, ↓reduceIte, carrierPoissonBideriv, hneg, Carrier.mul_re,
        Carrier.eps_re, Carrier.eps_im, zero_mul, one_mul, zero_add, smul_smul, neg_div]
      exact (smul_half_plus_minus ((1 / 2 : ℝ) ^ k / (k.factorial : ℝ)) A B).symm
  · simp only [paraMoyalStar, embedPlusPoly, embedMinusPoly, moyalStar, map_add,
      PowerSeries.coeff_mk, Carrier.add_im]
    rw [eps_pow_eq_ite, hplus k, hminus k]
    set A := poissonBideriv k F.re G.re + poissonBideriv k F.im G.im
    set B := poissonBideriv k F.re G.im + poissonBideriv k F.im G.re
    by_cases hk : Even k
    · have hneg : (-(1 / 2 : ℝ)) ^ k = (1 / 2 : ℝ) ^ k := hk.neg_pow (1 / 2 : ℝ)
      simp only [hk, ↓reduceIte, one_mul, carrierPoissonBideriv, hneg, smul_smul]
      exact (smul_half_sub_plus ((1 / 2 : ℝ) ^ k / (k.factorial : ℝ)) A B).symm
    · have hneg : (-(1 / 2 : ℝ)) ^ k = -((1 / 2 : ℝ) ^ k) :=
        (Nat.not_even_iff_odd.mp hk).neg_pow (1 / 2 : ℝ)
      simp only [hk, ↓reduceIte, carrierPoissonBideriv, hneg, Carrier.mul_im,
        Carrier.eps_re, Carrier.eps_im, zero_mul, one_mul, zero_add, smul_smul, neg_div]
      exact (smul_half_sub_minus ((1 / 2 : ℝ) ^ k / (k.factorial : ℝ)) A B).symm

/-- **Algebraic Firewall**: pure `P₊` and pure `P₋` sectors have vanishing Para-Moyal product
to all orders in `ℏ` (`P₊ P₋ = 0`). -/
theorem paraMoyalStar_cross_sector_zero {n : ℕ} (f g : PhasePoly n) :
    paraMoyalStar (⟨f, f⟩ : Carrier (PhasePoly n)) (⟨g, -g⟩ : Carrier (PhasePoly n)) = 0 := by
  rw [paraMoyalStar_decoupling]
  have hzero_right : ∀ m (x : PhasePoly n), poissonBideriv m x 0 = 0 := by
    intro m
    induction m with
    | zero => intro x; simp [poissonBideriv]
    | succ m ih => intro x; simp [poissonBideriv, ih]
  have hzero_left : ∀ m (y : PhasePoly n), poissonBideriv m 0 y = 0 := by
    intro m
    induction m with
    | zero => intro y; simp [poissonBideriv]
    | succ m ih => intro y; simp [poissonBideriv, ih]
  apply PowerSeries.ext
  intro k
  apply Carrier.ext
  · simp [embedPlusPoly, embedMinusPoly, moyalStar, hzero_right k (f + f), hzero_left k (g + g)]
  · simp [embedPlusPoly, embedMinusPoly, moyalStar, hzero_right k (f + f), hzero_left k (g + g)]

/-- Genuine non-commutativity witness for `paraMoyalStar`: `[q₀, p₀]_{⋆_e} ≠ 0` at order `ℏ¹`. -/
theorem paraMoyalStar_noncomm_witness :
    paraMoyalStar (n := 1) ⟨MvPolynomial.X (Sum.inl 0), 0⟩ ⟨MvPolynomial.X (Sum.inr 0), 0⟩ ≠
      paraMoyalStar (n := 1) ⟨MvPolynomial.X (Sum.inr 0), 0⟩ ⟨MvPolynomial.X (Sum.inl 0), 0⟩ := by
  intro h
  have hc := congrArg (fun s => (PowerSeries.coeff 1 s).im) h
  have h1 : poissonBideriv 1 (MvPolynomial.X (Sum.inl 0) : PhasePoly 1)
      (MvPolynomial.X (Sum.inr 0)) = 1 := by
    simp [poissonBideriv, MvPolynomial.pderiv_X]
  have h2 : poissonBideriv 1 (MvPolynomial.X (Sum.inr 0) : PhasePoly 1)
      (MvPolynomial.X (Sum.inl 0)) = -1 := by
    simp [poissonBideriv, MvPolynomial.pderiv_X]
  have h0_l : poissonBideriv 1 (0 : PhasePoly 1) (MvPolynomial.X (Sum.inr 0)) = 0 := by
    simp [poissonBideriv]
  have h0_r : poissonBideriv 1 (MvPolynomial.X (Sum.inl 0) : PhasePoly 1) 0 = 0 := by
    simp [poissonBideriv]
  have h0_l' : poissonBideriv 1 (0 : PhasePoly 1) (MvPolynomial.X (Sum.inl 0)) = 0 := by
    simp [poissonBideriv]
  have h0_r' : poissonBideriv 1 (MvPolynomial.X (Sum.inr 0) : PhasePoly 1) 0 = 0 := by
    simp [poissonBideriv]
  simp only [paraMoyalStar, PowerSeries.coeff_mk, pow_one, Nat.factorial_one, Nat.cast_one,
    div_one, carrierPoissonBideriv, Carrier.mul_im, Carrier.eps_re, Carrier.eps_im,
    zero_mul, one_mul, zero_add, h1, h2, h0_l, h0_r, h0_l', h0_r', add_zero] at hc
  have hC := congrArg (MvPolynomial.eval 0) hc
  norm_num at hC

end ParaMoyal

/-! ## E5. Metriplectic Rotation Identity (`K(X_S) = Y_S` vs `K(X_S) = 2 Y_S`) -/

section MetriplecticRotation

/-- Hamiltonian vector field `X_S = (∂_p S, -∂_q S)` for covector `dS = (∂_q S, ∂_p S)`. -/
def darbouxX_H (n : ℕ) (dS : PhaseSpace n) : PhaseSpace n :=
  (dS.2, -dS.1)

/-- Metric gradient vector field `Y_S^{(c)} = c⁻¹ (∂_p S, ∂_q S)` for `c • darbouxMetric n`.
For `c = 1` (`darbouxMetric`), `K(X_S) = Y_S` (`T35:2493`).
For `c = 2` (`2 • darbouxMetric`), `K(X_S) = 2 • Y_S` (`T35:2559–2561`). -/
def darbouxY_G (n : ℕ) (c : ℝ) (dS : PhaseSpace n) : PhaseSpace n :=
  (c⁻¹ • dS.2, c⁻¹ • dS.1)

/-- Symplectic defining law `ω(X_S, v) = dS(v)`. -/
theorem darbouxX_H_symplectic_law (n : ℕ) (dS v : PhaseSpace n) :
    darbouxSymplectic n (darbouxX_H n dS) v = ∑ a : Fin n, (dS.1 a * v.1 a + dS.2 a * v.2 a) := by
  simp only [darbouxSymplectic_apply, darbouxX_H, Pi.neg_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Metric defining law `(c • darbouxMetric)(Y_S^{(c)}, v) = dS(v)` for `c ≠ 0`. -/
theorem darbouxY_G_metric_law (n : ℕ) (c : ℝ) (hc : c ≠ 0) (dS v : PhaseSpace n) :
    c * darbouxMetric n (darbouxY_G n c dS) v = ∑ a : Fin n, (dS.1 a * v.1 a + dS.2 a * v.2 a) := by
  simp only [darbouxMetric_apply, darbouxY_G, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp [hc]
  ring

/-- Unit-metric metriplectic rotation (`T35:2493`): `K(X_S) = Y_S^{(1)}`. -/
theorem darboux_metriplectic_rotation_unit (n : ℕ) (dS : PhaseSpace n) :
    darbouxK n (darbouxX_H n dS) = darbouxY_G n 1 dS := by
  ext i <;> simp [darbouxK, darbouxX_H, darbouxY_G]

/-- Factor-of-2 scaled metriplectic rotation (`T35:2559–2561`): `K(X_S) = 2 • Y_S^{(2)}`. -/
theorem darboux_metriplectic_rotation_two (n : ℕ) (dS : PhaseSpace n) :
    darbouxK n (darbouxX_H n dS) = (2 : ℝ) • darbouxY_G n 2 dS := by
  ext i <;> simp [darbouxK, darbouxX_H, darbouxY_G]

/-- Unconditional energy/entropy conservation along the Hamiltonian flow: `dS(X_S) = 0`. -/
theorem darboux_energy_conservation_along_X (n : ℕ) (dS : PhaseSpace n) :
    ∑ a : Fin n, (dS.1 a * (darbouxX_H n dS).1 a + dS.2 a * (darbouxX_H n dS).2 a) = 0 := by
  simp only [darbouxX_H, Pi.neg_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  ring

/-- Exact rate along the indefinite Darboux gradient `Y_S^{(c)}`:
`dS(Y_S^{(c)}) = 2 c⁻¹ ∑ ∂_q S · ∂_p S` (sign depends on signature, not unconditionally ≥ 0). -/
theorem darboux_entropy_rate_along_Y (n : ℕ) (c : ℝ) (dS : PhaseSpace n) :
    ∑ a : Fin n, (dS.1 a * (darbouxY_G n c dS).1 a + dS.2 a * (darbouxY_G n c dS).2 a) =
      2 * c⁻¹ * ∑ a : Fin n, dS.1 a * dS.2 a := by
  simp only [darbouxY_G, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end MetriplecticRotation

/-! ## E6. DFT Strong Constraint Section Condition -/

section DFTSectionCondition

open InfoGeometry.Physics.DoubleFieldTheory
open InfoGeometry.Algebraic.Split
open InfoGeometry.Canonical.SplitComplex

/-- `O(D, D)` metric `η_D = [[0, I_D], [I_D, 0]]` on `Fin D ⊕ Fin D`. -/
def etaDFT (D : ℕ) : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℝ :=
  Matrix.fromBlocks 0 1 1 0

/-- Exact identification of `etaDFT 5` with `DoubleFieldTheory.etaO55`. -/
theorem etaDFT_five_eq_etaO55 :
    Matrix.reindex (finSumFinEquiv (m := 5) (n := 5)) (finSumFinEquiv (m := 5) (n := 5))
      (etaDFT 5) = etaO55 := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.surjective i with ⟨a | a, rfl⟩ <;>
    rcases finSumFinEquiv.surjective j with ⟨b | b, rfl⟩ <;>
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · simp only [etaDFT, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, etaO55]
    split_ifs with h
    · simp only [finSumFinEquiv_apply_left, Fin.val_castAdd] at h
      have ha : (a : ℕ) < 5 := a.isLt
      have hb : (b : ℕ) < 5 := b.isLt
      exfalso; omega
    · rfl
  · simp only [etaDFT, Matrix.fromBlocks_apply₁₂, Matrix.one_apply, etaO55]
    split_ifs with h1 h2
    · rfl
    · subst h1
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd,
        Fin.val_natAdd, Nat.add_sub_cancel_left] at h2
      exfalso
      exact h2 (Or.inl ⟨a.isLt, Nat.le_add_right 5 (a : ℕ), trivial⟩)
    · next h2 =>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd,
        Fin.val_natAdd, Nat.add_sub_cancel_left] at h2
      have ha : (a : ℕ) < 5 := a.isLt
      have hb : (b : ℕ) < 5 := b.isLt
      have hv : (a : ℕ) ≠ (b : ℕ) := Fin.val_ne_of_ne h1
      exfalso; omega
    · rfl
  · simp only [etaDFT, Matrix.fromBlocks_apply₂₁, Matrix.one_apply, etaO55]
    split_ifs with h1 h2
    · rfl
    · subst h1
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd,
        Fin.val_natAdd, Nat.add_sub_cancel_left] at h2
      exfalso
      exact h2 (Or.inr ⟨Nat.le_add_right 5 (a : ℕ), a.isLt, trivial⟩)
    · next h2 =>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd,
        Fin.val_natAdd, Nat.add_sub_cancel_left] at h2
      have ha : (a : ℕ) < 5 := a.isLt
      have hb : (b : ℕ) < 5 := b.isLt
      have hv : (a : ℕ) ≠ (b : ℕ) := Fin.val_ne_of_ne h1
      exfalso; omega
    · rfl
  · simp only [etaDFT, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, etaO55]
    split_ifs with h
    · simp only [finSumFinEquiv_apply_right, Fin.val_natAdd] at h
      have ha : (a : ℕ) < 5 := a.isLt
      have hb : (b : ℕ) < 5 := b.isLt
      exfalso; omega
    · rfl

/-- Second-order DFT strong constraint operator `η^{MN} ∂_M ∂_N Ψ = 2 ∑ ∂_{q^a} ∂_{p_a} Ψ`. -/
def dftSectionOperator (D : ℕ) (Psi : PhaseSpace D → ℝ) (q p : Fin D → ℝ) : ℝ :=
  2 * ∑ a : Fin D,
    deriv (fun s => deriv (fun t => Psi (Function.update q a s, Function.update p a t)) (p a)) (q a)

/-- First-order bilinear weak-section contraction `∑ (∂_q Φ ∂_p Ψ + ∂_p Φ ∂_q Ψ)`. -/
def dftWeakSection (D : ℕ) (dqPhi dpPhi dqPsi dpPsi : Fin D → ℝ) : ℝ :=
  ∑ a : Fin D, (dqPhi a * dpPsi a + dpPhi a * dqPsi a)

/-- Equivalence of DFT strong constraint vanishing with `∑ ∂_{q^a} ∂_{p_a} Ψ = 0`. -/
theorem dftSection_iff_plus_minus_annihilation (D : ℕ) (Psi : PhaseSpace D → ℝ) (q p : Fin D → ℝ) :
    dftSectionOperator D Psi q p = 0 ↔
      ∑ a : Fin D,
        deriv (fun s => deriv (fun t => Psi (Function.update q a s, Function.update p a t)) (p a))
          (q a) = 0 := by
  dsimp [dftSectionOperator]
  constructor
  · intro h
    linarith
  · intro h
    rw [h, mul_zero]

/-- Any field independent of dual coordinates `p` satisfies the DFT strong constraint identically. -/
theorem dftSection_of_independent_p (D : ℕ) (f : (Fin D → ℝ) → ℝ) (q p : Fin D → ℝ) :
    dftSectionOperator D (fun x => f x.1) q p = 0 := by
  dsimp [dftSectionOperator]
  simp

/-- Any field independent of coordinates `q` satisfies the DFT strong constraint identically. -/
theorem dftSection_of_independent_q (D : ℕ) (g : (Fin D → ℝ) → ℝ) (q p : Fin D → ℝ) :
    dftSectionOperator D (fun x => g x.2) q p = 0 := by
  dsimp [dftSectionOperator]
  simp

/-- Split-complex idempotent annihilation for the DFT weak section condition. -/
theorem dft_splitComplex_idempotent_annihilation (D : ℕ)
    (dqPhi dpPhi dqPsi dpPsi : Fin D → ℝ)
    (h1 : ∀ a, dpPhi a = 0 ∧ dpPsi a = 0) :
    dftWeakSection D dqPhi dpPhi dqPsi dpPsi = 0 ∧
      ∀ a, (⟨dqPhi a, 0⟩ * Carrier.pPlus (R := ℝ)) *
        (⟨0, dpPsi a⟩ * Carrier.pMinus (R := ℝ)) = 0 := by
  constructor
  · dsimp [dftWeakSection]
    refine Finset.sum_eq_zero fun a _ => ?_
    obtain ⟨hL, hR⟩ := h1 a
    simp [hL, hR]
  · intro a
    rw [mul_assoc, ← mul_assoc (Carrier.pPlus (R := ℝ)),
      mul_comm (Carrier.pPlus (R := ℝ)) ⟨0, dpPsi a⟩,
      mul_assoc ⟨0, dpPsi a⟩ (Carrier.pPlus (R := ℝ)) (Carrier.pMinus (R := ℝ)),
      Carrier.pPlus_mul_pMinus, mul_zero, mul_zero]

/-- Narain charge level-matching (`hyperbolicNorm q = 0`) is equivalent to the discrete DFT
section condition `p · w = 0`, reusing `DoubleFieldTheory.narain_lattice_is_even`. -/
theorem narain_charge_null_iff_dft_section (q : SplitCharge 5) :
    SplitCharge.hyperbolicNorm q = 0 ↔ ∑ i : Fin 5, q.momentum i * q.winding i = 0 := by
  rw [narain_lattice_is_even q]
  omega

end DFTSectionCondition

/-! ## E7. Diagonal `λ = -2` Hyperbolic Monge–Ampère Verification -/

section MongeAmpere

/-- Para-Kähler log potential `𝒦(q, p) = ∑_{a=1}^n ln(1 + qᵃ p_a)`. -/
def paraKahlerLogPotential (n : ℕ) (q p : Fin n → ℝ) : ℝ :=
  ∑ a : Fin n, Real.log (1 + q a * p a)

/-- Explicit diagonal mixed Hessian `diag((1 + qᵃ p_a)⁻²)`. -/
def paraKahlerDiagHessian (n : ℕ) (q p : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun a => (1 + q a * p a)⁻¹ ^ 2)

/-- Analytic mixed partial Hessian `∂_{qᵃ} ∂_{p_b} 𝒦(q, p)` computed via `deriv` of `deriv`.
Note (`T33:2373` typo): `g_{ab}` and `ω_{ab}` both use this mixed block `H_{ab} = ∂_{qᵃ}∂_{p_b} 𝒦`,
entering `g` symmetrically as `[[0, H], [Hᵀ, 0]]` and `ω` skew-symmetrically as `[[0, H], [-Hᵀ, 0]]`. -/
def analyticMixedHessian (n : ℕ) (q p : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b =>
    deriv (fun s => deriv (fun t => paraKahlerLogPotential n
      (Function.update q a s) (Function.update p b t)) (p b)) (q a)

private lemma inner_deriv_paraKahlerLogPotential (n : ℕ) (q p : Fin n → ℝ)
    (a b : Fin n) (s : ℝ) (hpos : 0 < 1 + Function.update q a s b * p b) :
    deriv (fun t => paraKahlerLogPotential n (Function.update q a s) (Function.update p b t))
      (p b) =
      Function.update q a s b * (1 + Function.update q a s b * p b)⁻¹ := by
  have hfun : (fun t => paraKahlerLogPotential n (Function.update q a s) (Function.update p b t)) =
      fun t => Real.log (1 + Function.update q a s b * t) +
        ∑ c ∈ Finset.univ.erase b, Real.log (1 + Function.update q a s c * p c) := by
    ext t
    dsimp [paraKahlerLogPotential]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b)]
    congr 1
    · simp [Function.update]
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hne : c ≠ b := (Finset.mem_erase.mp hc).1
      simp [Function.update_of_ne hne]
  rw [hfun]
  have hlin : HasDerivAt (fun t => 1 + Function.update q a s b * t)
      (0 + Function.update q a s b * 1) (p b) :=
    (hasDerivAt_const (p b) 1).add ((hasDerivAt_id (p b)).const_mul (Function.update q a s b))
  rw [zero_add, mul_one] at hlin
  have hlog : HasDerivAt (fun t => Real.log (1 + Function.update q a s b * t))
      (Function.update q a s b / (1 + Function.update q a s b * p b)) (p b) := by
    simpa [mul_comm] using hlin.log hpos.ne'
  have htot := hlog.add_const (∑ c ∈ Finset.univ.erase b, Real.log (1 + Function.update q a s c * p c))
  rw [htot.deriv, div_eq_mul_inv]

/-- The analytic mixed Hessian of `𝒦(q, p)` equals `paraKahlerDiagHessian n q p`. -/
theorem analyticMixedHessian_eq_diag (n : ℕ) (q p : Fin n → ℝ)
    (hpos : ∀ a, 0 < 1 + q a * p a) :
    analyticMixedHessian n q p = paraKahlerDiagHessian n q p := by
  ext a b
  dsimp [analyticMixedHessian, paraKahlerDiagHessian]
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.diagonal_apply_eq]
    have hcont : Continuous (fun s : ℝ => 1 + s * p a) :=
      continuous_const.add (continuous_id.mul continuous_const)
    have hopen : IsOpen {s : ℝ | 0 < 1 + s * p a} := isOpen_lt continuous_const hcont
    have hev : ∀ᶠ s in nhds (q a),
        deriv (fun t => paraKahlerLogPotential n (Function.update q a s) (Function.update p a t))
          (p a) = s * (1 + s * p a)⁻¹ := by
      filter_upwards [hopen.mem_nhds (hpos a)] with s hs
      have hs' : 0 < 1 + Function.update q a s a * p a := by simpa using hs
      simpa using inner_deriv_paraKahlerLogPotential n q p a a s hs'
    rw [Filter.EventuallyEq.deriv_eq hev]
    have h1 : HasDerivAt (fun s => 1 + s * p a) (0 + 1 * p a) (q a) :=
      (hasDerivAt_const (q a) 1).add ((hasDerivAt_id (q a)).mul_const (p a))
    rw [zero_add, one_mul] at h1
    have hinv : HasDerivAt (fun s => (1 + s * p a)⁻¹) (-(p a) / (1 + q a * p a) ^ 2) (q a) :=
      h1.inv (hpos a).ne'
    have hprod := (hasDerivAt_id (q a)).mul hinv
    have hderiv : deriv (fun x => x * (1 + x * p a)⁻¹) (q a) =
        1 * (1 + q a * p a)⁻¹ + q a * (-(p a) / (1 + q a * p a) ^ 2) := by
      change deriv ((id : ℝ → ℝ) * fun s => (1 + s * p a)⁻¹) (q a) = _
      exact hprod.deriv
    rw [hderiv]
    have hne : 1 + q a * p a ≠ 0 := (hpos a).ne'
    field_simp [hne]
    ring
  · have hne : b ≠ a := Ne.symm hab
    simp only [Matrix.diagonal_apply_ne _ hab]
    have hev : ∀ s : ℝ,
        deriv (fun t => paraKahlerLogPotential n (Function.update q a s) (Function.update p b t))
          (p b) = q b * (1 + q b * p b)⁻¹ := by
      intro s
      have hpos_b : 0 < 1 + Function.update q a s b * p b := by
        simpa [Function.update_of_ne hne] using hpos b
      have h := inner_deriv_paraKahlerLogPotential n q p a b s hpos_b
      simpa [Function.update_of_ne hne] using h
    simp [hev]

/-- Determinant of the diagonal mixed Hessian equals `exp(-2 𝒦)` (`λ = -2` diagonal case). -/
theorem paraKahlerDiagHessian_det_eq_exp_neg_two (n : ℕ) (q p : Fin n → ℝ)
    (hpos : ∀ a, 0 < 1 + q a * p a) :
    (paraKahlerDiagHessian n q p).det = Real.exp (-2 * paraKahlerLogPotential n q p) := by
  dsimp [paraKahlerDiagHessian, paraKahlerLogPotential]
  rw [Matrix.det_diagonal, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [show (-2 : ℝ) * Real.log (1 + q a * p a) = (2 : ℕ) * (-Real.log (1 + q a * p a)) by norm_num,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log (hpos a)]

/-- **Analytic Diagonal Hyperbolic Monge–Ampère Theorem** (`λ = -2`):
For `𝒦(q,p) = ∑ ln(1 + qᵃ p_a)` on the positivity domain `∀ a, 0 < 1 + q a * p a`,
`det(∂_q ∂_p 𝒦) = exp(-2 𝒦)`. -/
theorem analytic_hyperbolic_monge_ampere_neg_two (n : ℕ) (q p : Fin n → ℝ)
    (hpos : ∀ a, 0 < 1 + q a * p a) :
    (analyticMixedHessian n q p).det = Real.exp (-2 * paraKahlerLogPotential n q p) := by
  rw [analyticMixedHessian_eq_diag n q p hpos]
  exact paraKahlerDiagHessian_det_eq_exp_neg_two n q p hpos

end MongeAmpere

/-! ## E8. Born Geometry Triad & Born Reciprocity (`K · w = e · w` + Cayley–Hadamard Isometry) -/

section BornGeometry

open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
open InfoGeometry.Canonical.SplitComplex

/-- Born reciprocity swap involution `K_swap (q, p) = (p, q)` (`T38:2892`). -/
def bornSwapK (n : ℕ) : PhaseSpace n →ₗ[ℝ] PhaseSpace n where
  toFun v := (v.2, v.1)
  map_add' u v := by ext i <;> simp
  map_smul' c v := by ext i <;> simp

/-- Born split metric `g_Born(u, v) = ∑ a, (u.q a * v.q a - u.p a * v.p a)` (`T38:2892`). -/
def bornSplitMetric (n : ℕ) : LinearMap.BilinForm ℝ (PhaseSpace n) :=
  LinearMap.mk₂ ℝ
    (fun u v => ∑ a : Fin n, (u.1 a * v.1 a - u.2 a * v.2 a))
    (fun u v w => by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [add_mul, mul_add, sub_add_sub_comm])
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mul_sub, mul_assoc])
    (fun u v w => by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [add_mul, mul_add, sub_add_sub_comm])
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mul_sub, mul_assoc, mul_left_comm])

/-- Born symplectic 2-form `ω_Born = darbouxSymplectic`. -/
abbrev bornSymplectic (n : ℕ) := darbouxSymplectic n

@[simp] theorem bornSwapK_apply (n : ℕ) (v : PhaseSpace n) :
    bornSwapK n v = (v.2, v.1) := rfl

@[simp] theorem bornSplitMetric_apply (n : ℕ) (u v : PhaseSpace n) :
    bornSplitMetric n u v = ∑ a : Fin n, (u.1 a * v.1 a - u.2 a * v.2 a) := rfl

/-- Born `ParaComplexStructure`. -/
def bornParaComplex (n : ℕ) : ParaComplexStructure ℝ (PhaseSpace n) where
  K := bornSwapK n
  K_sq := by
    ext v <;> simp [bornSwapK]

/-- Born `ParaKahlerDatum` instantiating `ParaKahlerMaurerCartanQGT.ParaKahlerDatum`. -/
def bornParaKahlerDatum (n : ℕ) : ParaKahlerDatum ℝ (PhaseSpace n) where
  metric := bornSplitMetric n
  para := bornParaComplex n
  metric_symm u v := by
    simp only [bornSplitMetric_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  metric_anti_compat u v := by
    simp only [bornSplitMetric_apply, bornParaComplex, bornSwapK_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

/-- Born triad compatibility: `g(X, Y) = ω(X, K Y)`. -/
theorem born_triad_g_eq_omega_K (n : ℕ) (X Y : PhaseSpace n) :
    bornSplitMetric n X Y = bornSymplectic n X (bornSwapK n Y) := by
  simp only [bornSplitMetric_apply, bornSymplectic, darbouxSymplectic_apply, bornSwapK_apply]

/-- Born triad metric anti-invariance: `g(K X, K Y) = -g(X, Y)`. -/
theorem born_triad_g_anti_inv (n : ℕ) (X Y : PhaseSpace n) :
    bornSplitMetric n (bornSwapK n X) (bornSwapK n Y) = -bornSplitMetric n X Y :=
  (bornParaKahlerDatum n).metric_anti_compat X Y

/-- Born triad symplectic anti-invariance: `ω(K X, K Y) = -ω(X, Y)`. -/
theorem born_triad_omega_anti_inv (n : ℕ) (X Y : PhaseSpace n) :
    bornSymplectic n (bornSwapK n X) (bornSwapK n Y) = -bornSymplectic n X Y := by
  simp only [bornSymplectic, darbouxSymplectic_apply, bornSwapK_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Embed `(q, p) ∈ PhaseSpace n` componentwise as split-complex numbers `qᵃ + e pᵃ`. -/
def toSplitVec {n : ℕ} (w : PhaseSpace n) (a : Fin n) : Carrier ℝ :=
  ⟨w.1 a, w.2 a⟩

/-- **Born Reciprocity Identity (`T38:2898`)**: `K · w = e · w = p + e q`. -/
theorem born_reciprocity_K_eq_eps_mul (n : ℕ) (w : PhaseSpace n) (a : Fin n) :
    toSplitVec (bornSwapK n w) a = Carrier.eps * toSplitVec w a := by
  ext <;> simp [toSplitVec, bornSwapK, Carrier.eps]

/-- In idempotent coordinates `(w₊, w₋)`, `K` acts by `(+1, -1)`. -/
theorem born_reciprocity_idempotent_eigen (n : ℕ) (w : PhaseSpace n) (a : Fin n) :
    Carrier.toProduct (toSplitVec (bornSwapK n w) a) =
      ((Carrier.toProduct (toSplitVec w a)).1, -(Carrier.toProduct (toSplitVec w a)).2) := by
  ext <;> simp [Carrier.toProduct, toSplitVec, bornSwapK]
  ring

/-- Orthogonal Cayley–Hadamard transform `T(x, y) = (1/√2)(x + y, x - y)`. -/
def cayleyHadamardTransform (n : ℕ) : PhaseSpace n ≃ₗ[ℝ] PhaseSpace n where
  toFun v := ((Real.sqrt 2)⁻¹ • (v.1 + v.2), (Real.sqrt 2)⁻¹ • (v.1 - v.2))
  invFun u := ((Real.sqrt 2)⁻¹ • (u.1 + u.2), (Real.sqrt 2)⁻¹ • (u.1 - u.2))
  left_inv v := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    ext i <;> simp <;> field_simp [hne] <;> rw [hsq] <;> ring
  right_inv u := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    ext i <;> simp <;> field_simp [hne] <;> rw [hsq] <;> ring
  map_add' u v := by
    ext i <;> simp <;> ring
  map_smul' c v := by
    ext i <;> simp <;> ring

/-- Cayley–Hadamard intertwines Born swap `K_swap` (E8) with Darboux `K` (E3). -/
theorem cayleyHadamard_intertwines_K (n : ℕ) (v : PhaseSpace n) :
    cayleyHadamardTransform n (bornSwapK n v) = darbouxK n (cayleyHadamardTransform n v) := by
  ext i
  · simp [cayleyHadamardTransform, bornSwapK, darbouxK]; ring
  · simp [cayleyHadamardTransform, bornSwapK, darbouxK]; ring

/-- Cayley–Hadamard is an exact isometry from `bornSplitMetric` (E8) to `darbouxMetric` (E3). -/
theorem cayleyHadamard_metric_isometry (n : ℕ) (u v : PhaseSpace n) :
    darbouxMetric n (cayleyHadamardTransform n u) (cayleyHadamardTransform n v) =
      bornSplitMetric n u v := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  simp only [darbouxMetric_apply, bornSplitMetric_apply, cayleyHadamardTransform,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    field_simp [hne]
    nlinarith [hs2]
  calc
    (Real.sqrt 2)⁻¹ * (u.1 a + u.2 a) * ((Real.sqrt 2)⁻¹ * (v.1 a - v.2 a)) +
        (Real.sqrt 2)⁻¹ * (u.1 a - u.2 a) * ((Real.sqrt 2)⁻¹ * (v.1 a + v.2 a))
      = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) *
          ((u.1 a + u.2 a) * (v.1 a - v.2 a) + (u.1 a - u.2 a) * (v.1 a + v.2 a)) := by ring
    _ = (1 / 2) * (2 * (u.1 a * v.1 a - u.2 a * v.2 a)) := by rw [hsq]; ring
    _ = u.1 a * v.1 a - u.2 a * v.2 a := by ring

/-- Cayley–Hadamard flips the symplectic sign (`det T = -1`), explaining the E3 vs E8 sign swap. -/
theorem cayleyHadamard_symplectic_anti_isometry (n : ℕ) (u v : PhaseSpace n) :
    darbouxSymplectic n (cayleyHadamardTransform n u) (cayleyHadamardTransform n v) =
      -bornSymplectic n u v := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  simp only [darbouxSymplectic_apply, bornSymplectic, cayleyHadamardTransform,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    field_simp [hne]
    nlinarith [hs2]
  calc
    (Real.sqrt 2)⁻¹ * (u.1 a + u.2 a) * ((Real.sqrt 2)⁻¹ * (v.1 a - v.2 a)) -
        (Real.sqrt 2)⁻¹ * (u.1 a - u.2 a) * ((Real.sqrt 2)⁻¹ * (v.1 a + v.2 a))
      = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) *
          ((u.1 a + u.2 a) * (v.1 a - v.2 a) - (u.1 a - u.2 a) * (v.1 a + v.2 a)) := by ring
    _ = (1 / 2) * (-2 * (u.1 a * v.2 a - u.2 a * v.1 a)) := by rw [hsq]; ring
    _ = -(u.1 a * v.2 a - u.2 a * v.1 a) := by ring

end BornGeometry

/-! ## C1. Unipotent `EP₂` Horizon Shear `ℳ_{4π}` & Bekenstein–Hawking Pairing -/

section HorizonShear

open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Physics
open InfoGeometry.Canonical.ParaHyperkahlerPresymplecticBridge
open InfoGeometry.Canonical.BekensteinHawkingEntropyAreaBridge
open InfoGeometry.Holography.BekensteinHawkingDyadicEntropy

/-- Real unipotent horizon shear `ℳ_{4π}^ℝ = !![1, 4π; 0, 1]` (`T03`, `T06`, `T09`, `T41`). -/
def horizonShear4PiReal : Mat2R :=
  logCFTUnipotentFlow (4 * Real.pi)

/-- Complex unipotent horizon shear `ℳ_{4π}^ℂ = !![1, 4π i; 0, 1]` (`T44`, `T47`, `T53`). -/
def horizonShear4PiComplex : Mat2C :=
  logCFTUnipotentFlow ((4 * Real.pi : ℂ) * Complex.I)

/-- Negated complex shear `-ℳ_{4π}^ℂ = !![-1, -4π i; 0, -1]` (`T01:86`).
Note (`DEF14`): this is NOT unipotent (`(M - 1)² ≠ 0`), but satisfies `(M + 1)² = 0` and `det M = 1`. -/
def horizonShear4PiNegComplex : Mat2C :=
  -horizonShear4PiComplex

/-- Planck area `ℓ_Pl² = G ℏ` in units where `c = 1`. -/
def planckArea (G hbar : ℝ) : ℝ :=
  G * hbar

/-- Single dyadic horizon area step `Δ𝒜 = 4 ℓ_Pl² ln 2`. -/
def horizonAreaStep (G hbar : ℝ) : ℝ :=
  4 * planckArea G hbar * dyadicEntropyQuantum

/-- Explicit non-commutativity witness on `Mat2R`. -/
theorem mat2R_noncomm_witness :
    (N_log : Mat2R) * (N_log : Mat2R)ᵀ ≠ (N_log : Mat2R)ᵀ * (N_log : Mat2R) := by
  intro h
  have h00 := congrArg (fun M : Mat2R => M 0 0) h
  norm_num [N_log, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Explicit non-commutativity witness on `Mat2C` (reusing `FiniteSpin.j_plus_j_minus_ne`). -/
theorem mat2C_noncomm_witness : J_plus * J_minus ≠ J_minus * J_plus :=
  j_plus_j_minus_ne

/-- Real matrix exponential of the scaled Jordan nilpotent `t • N_log`. -/
theorem real_logCFTUnipotentFlow_eq_exp (t : ℝ) :
    logCFTUnipotentFlow t = NormedSpace.exp (t • (N_log : Mat2R)) := by
  have hsq : (t • (N_log : Mat2R)) * (t • (N_log : Mat2R)) = 0 := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, N_log_sq_zero, smul_zero, smul_zero]
  have hpow : ∀ k : ℕ, 2 ≤ k → (t • (N_log : Mat2R)) ^ k = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_add, pow_two, hsq, mul_zero]
  rw [NormedSpace.exp_eq_tsum ℝ]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, logCFTUnipotentFlow]
  · intro k hk
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_range, not_lt] at hk
      exact hk
    rw [hpow k hk2, smul_zero]

/-- `horizonShear4PiReal = exp !![0, 4π; 0, 0]`. -/
theorem horizonShear4PiReal_eq_exp :
    horizonShear4PiReal = NormedSpace.exp !![(0 : ℝ), 4 * Real.pi; 0, 0] := by
  have hmat : (4 * Real.pi) • (N_log : Mat2R) = !![(0 : ℝ), 4 * Real.pi; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N_log]
  rw [horizonShear4PiReal, real_logCFTUnipotentFlow_eq_exp, hmat]

/-- `horizonShear4PiComplex = exp !![0, 4π i; 0, 0]` (reusing `complex_logCFTUnipotentFlow_eq_exp`). -/
theorem horizonShear4PiComplex_eq_exp :
    horizonShear4PiComplex = NormedSpace.exp !![(0 : ℂ), (4 * Real.pi : ℂ) * Complex.I; 0, 0] := by
  have hmat : ((4 * Real.pi : ℂ) * Complex.I) • (N_log : Mat2C) =
      !![(0 : ℂ), (4 * Real.pi : ℂ) * Complex.I; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N_log]
  rw [horizonShear4PiComplex, complex_logCFTUnipotentFlow_eq_exp, hmat]

/-- Phase-space action `ℳ_{4π}^ℝ (φ, Π_φ) = (φ + 4π Π_φ, Π_φ)`. -/
theorem horizonShear4PiReal_mulVec (phi pi_phi : ℝ) :
    horizonShear4PiReal *ᵥ ![phi, pi_phi] = ![phi + 4 * Real.pi * pi_phi, pi_phi] := by
  rw [horizonShear4PiReal, logCFTUnipotentFlow_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Symplectic preservation of `logCFTUnipotentFlow` against `ParaHyperkahlerPresymplecticBridge.I_mat`. -/
theorem unipotentFlow_symplectic (t : ℝ) :
    (logCFTUnipotentFlow t)ᵀ * I_mat * logCFTUnipotentFlow t = I_mat := by
  rw [logCFTUnipotentFlow_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `ℳ_{4π}^ℝ` preserves `ParaHyperkahlerPresymplecticBridge.omega2`. -/
theorem horizonShear4PiReal_preserves_omega2 (u v : Vec2R) :
    omega2 (horizonShear4PiReal *ᵥ u) (horizonShear4PiReal *ᵥ v) = omega2 u v := by
  dsimp [omega2, horizonShear4PiReal]
  rw [logCFTUnipotentFlow_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `ℳ_{4π}^ℂ` preserves the complex symplectic matrix `!![0, 1; -1, 0]`. -/
theorem horizonShear4PiComplex_symplectic :
    horizonShear4PiComplexᵀ * !![(0 : ℂ), 1; -1, 0] * horizonShear4PiComplex =
      !![(0 : ℂ), 1; -1, 0] := by
  dsimp [horizonShear4PiComplex]
  rw [logCFTUnipotentFlow_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `-ℳ_{4π}^ℂ` also preserves the complex symplectic matrix `!![0, 1; -1, 0]`. -/
theorem horizonShear4PiNegComplex_symplectic :
    horizonShear4PiNegComplexᵀ * !![(0 : ℂ), 1; -1, 0] * horizonShear4PiNegComplex =
      !![(0 : ℂ), 1; -1, 0] := by
  dsimp [horizonShear4PiNegComplex]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact horizonShear4PiComplex_symplectic

/-- `ℳ_{4π}^ℝ` is a nontrivial `EP₂` Jordan shear: `M - 1 ≠ 0` and `(M - 1)² = 0`. -/
theorem horizonShear4PiReal_ep2_nilpotent :
    horizonShear4PiReal - 1 ≠ 0 ∧ (horizonShear4PiReal - 1) ^ 2 = 0 := by
  have hsub : horizonShear4PiReal - 1 = (4 * Real.pi) • (N_log : Mat2R) := by
    simp [horizonShear4PiReal, logCFTUnipotentFlow]
  constructor
  · intro h
    rw [hsub] at h
    have h01 := congrArg (fun M : Mat2R => M 0 1) h
    simp [N_log, Real.pi_ne_zero] at h01
  · rw [hsub, pow_two, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, N_log_sq_zero,
      smul_zero, smul_zero]

/-- `ℳ_{4π}^ℝ` is not diagonalizable over `ℝ`. -/
theorem horizonShear4PiReal_not_diagonalizable :
    ¬∃ (P D : Mat2R), IsUnit P ∧ Matrix.IsDiag D ∧ P * horizonShear4PiReal = D * P := by
  rintro ⟨P, D, hP, hD, hconj⟩
  have hsub : P * (horizonShear4PiReal - 1) = (D - 1) * P := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hconj]
  have hsq : P * (horizonShear4PiReal - 1) ^ 2 = (D - 1) ^ 2 * P := by
    calc
      P * (horizonShear4PiReal - 1) ^ 2
        = (P * (horizonShear4PiReal - 1)) * (horizonShear4PiReal - 1) := by
            rw [pow_two, mul_assoc]
      _ = ((D - 1) * P) * (horizonShear4PiReal - 1) := by rw [hsub]
      _ = (D - 1) * (P * (horizonShear4PiReal - 1)) := by rw [mul_assoc]
      _ = (D - 1) * ((D - 1) * P) := by rw [hsub]
      _ = (D - 1) ^ 2 * P := by rw [← mul_assoc, ← pow_two]
  rw [horizonShear4PiReal_ep2_nilpotent.2, mul_zero] at hsq
  rcases hP with ⟨u, rfl⟩
  have hD2 : (D - 1) ^ 2 = 0 := by
    calc
      (D - 1) ^ 2 = ((D - 1) ^ 2 * (u : Mat2R)) * ((u⁻¹ : Units Mat2R) : Mat2R) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = 0 * ((u⁻¹ : Units Mat2R) : Mat2R) := by rw [← hsq]
      _ = 0 := zero_mul _
  have hDeq : D = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hdiag : ((D - 1) * (D - 1)) i i = (D i i - 1) ^ 2 := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · simp [pow_two]
        · intro k _ hki
          have hDk : D i k = 0 := hD hki.symm
          simp [Matrix.sub_apply, hDk, hki.symm]
        · simp
      have hzero : (D i i - 1) ^ 2 = 0 := by
        rw [← hdiag, ← pow_two, hD2]
        simp
      have h1 : D i i - 1 = 0 := sq_eq_zero_iff.mp hzero
      simp [sub_eq_zero.mp h1]
    · simp [hD hij, Matrix.one_apply_ne hij]
  rw [hDeq, one_mul] at hconj
  have hM1 : horizonShear4PiReal = 1 := by
    calc
      horizonShear4PiReal = ((u⁻¹ : Units Mat2R) : Mat2R) * ((u : Mat2R) * horizonShear4PiReal) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ((u⁻¹ : Units Mat2R) : Mat2R) * (u : Mat2R) := by rw [hconj]
      _ = 1 := Units.inv_mul u
  exact horizonShear4PiReal_ep2_nilpotent.1 (sub_eq_zero.mpr hM1)

/-- `ℳ_{4π}^ℂ` is not diagonalizable over `ℂ`. -/
theorem horizonShear4PiComplex_not_diagonalizable :
    ¬∃ (P D : Mat2C), IsUnit P ∧ Matrix.IsDiag D ∧ P * horizonShear4PiComplex = D * P := by
  have hsubM : horizonShear4PiComplex - 1 =
      ((4 * Real.pi : ℂ) * Complex.I) • (N_log : Mat2C) := by
    simp [horizonShear4PiComplex, logCFTUnipotentFlow]
  have hne : horizonShear4PiComplex - 1 ≠ 0 := by
    intro h
    rw [hsubM] at h
    have h01 := congrArg (fun M : Mat2C => M 0 1) h
    simp [N_log, Real.pi_ne_zero, Complex.I_ne_zero] at h01
  have hsqM : (horizonShear4PiComplex - 1) ^ 2 = 0 := by
    rw [hsubM, pow_two, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, N_log_sq_zero,
      smul_zero, smul_zero]
  rintro ⟨P, D, hP, hD, hconj⟩
  have hsub : P * (horizonShear4PiComplex - 1) = (D - 1) * P := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hconj]
  have hsq : P * (horizonShear4PiComplex - 1) ^ 2 = (D - 1) ^ 2 * P := by
    calc
      P * (horizonShear4PiComplex - 1) ^ 2
        = (P * (horizonShear4PiComplex - 1)) * (horizonShear4PiComplex - 1) := by
            rw [pow_two, mul_assoc]
      _ = ((D - 1) * P) * (horizonShear4PiComplex - 1) := by rw [hsub]
      _ = (D - 1) * (P * (horizonShear4PiComplex - 1)) := by rw [mul_assoc]
      _ = (D - 1) * ((D - 1) * P) := by rw [hsub]
      _ = (D - 1) ^ 2 * P := by rw [← mul_assoc, ← pow_two]
  rw [hsqM, mul_zero] at hsq
  rcases hP with ⟨u, rfl⟩
  have hD2 : (D - 1) ^ 2 = 0 := by
    calc
      (D - 1) ^ 2 = ((D - 1) ^ 2 * (u : Mat2C)) * ((u⁻¹ : Units Mat2C) : Mat2C) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = 0 * ((u⁻¹ : Units Mat2C) : Mat2C) := by rw [← hsq]
      _ = 0 := zero_mul _
  have hDeq : D = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hdiag : ((D - 1) * (D - 1)) i i = (D i i - 1) ^ 2 := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · simp [pow_two]
        · intro k _ hki
          have hDk : D i k = 0 := hD hki.symm
          simp [Matrix.sub_apply, hDk, hki.symm]
        · simp
      have hzero : (D i i - 1) ^ 2 = 0 := by
        rw [← hdiag, ← pow_two, hD2]
        simp
      have h1 : D i i - 1 = 0 := sq_eq_zero_iff.mp hzero
      simp [sub_eq_zero.mp h1]
    · simp [hD hij, Matrix.one_apply_ne hij]
  rw [hDeq, one_mul] at hconj
  have hM1 : horizonShear4PiComplex = 1 := by
    calc
      horizonShear4PiComplex = ((u⁻¹ : Units Mat2C) : Mat2C) * ((u : Mat2C) * horizonShear4PiComplex) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ((u⁻¹ : Units Mat2C) : Mat2C) * (u : Mat2C) := by rw [hconj]
      _ = 1 := Units.inv_mul u
  exact hne (sub_eq_zero.mpr hM1)

/-- Honest `DEF14` characterization of `-ℳ_{4π}^ℂ` (`T01:86`): it is anti-unipotent
(`(M + 1) ≠ 0`, `(M + 1)² = 0`, `det M = 1`) and NOT unipotent (`(M - 1)² ≠ 0`). -/
theorem horizonShear4PiNegComplex_anti_unipotent :
    horizonShear4PiNegComplex + 1 ≠ 0 ∧
      (horizonShear4PiNegComplex + 1) ^ 2 = 0 ∧
      horizonShear4PiNegComplex.det = 1 ∧
      (horizonShear4PiNegComplex - 1) ^ 2 ≠ 0 := by
  have hadd : horizonShear4PiNegComplex + 1 = -(((4 * Real.pi : ℂ) * Complex.I) • (N_log : Mat2C)) := by
    simp [horizonShear4PiNegComplex, horizonShear4PiComplex, logCFTUnipotentFlow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [hadd] at h
    have h01 := congrArg (fun M : Mat2C => M 0 1) h
    simp [N_log, Real.pi_ne_zero, Complex.I_ne_zero] at h01
  · rw [hadd, pow_two, neg_mul_neg, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, N_log_sq_zero,
      smul_zero, smul_zero]
  · dsimp [horizonShear4PiNegComplex, horizonShear4PiComplex]
    rw [logCFTUnipotentFlow_apply, Matrix.det_fin_two]
    simp
  · intro h
    have h00 := congrArg (fun M : Mat2C => M 0 0) h
    dsimp [horizonShear4PiNegComplex, horizonShear4PiComplex] at h00
    rw [logCFTUnipotentFlow_apply] at h00
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Adding one dyadic horizon area step `Δ𝒜 = 4 G ℏ ln 2` increases `bekensteinHawkingEntropy`
by `ln 2` (reusing `BekensteinHawkingEntropyAreaBridge.bekenstein_hawking_entropy_add`). -/
theorem bekensteinHawking_horizonAreaStep (area G hbar : ℝ) (hG : G ≠ 0) (hh : hbar ≠ 0) :
    BekensteinHawkingEntropyAreaBridge.bekensteinHawkingEntropy
        (area + horizonAreaStep G hbar) G hbar =
      BekensteinHawkingEntropyAreaBridge.bekensteinHawkingEntropy area G hbar + Real.log 2 := by
  rw [bekenstein_hawking_entropy_add]
  dsimp [BekensteinHawkingEntropyAreaBridge.bekensteinHawkingEntropy,
    horizonAreaStep, planckArea, dyadicEntropyQuantum]
  have hden : 4 * G * hbar ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hG) hh
  field_simp [hden]

/-- Discrete `n`-step horizon shear paired with `n`-bit Bekenstein–Hawking dyadic entropy. -/
theorem horizonShear4PiReal_pow_bh_pairing (n : ℕ) (phi pi_phi G hbar : ℝ)
    (hG : G ≠ 0) (hh : hbar ≠ 0) :
    (horizonShear4PiReal ^ n) *ᵥ ![phi, pi_phi] =
        ![phi + (n : ℝ) * (4 * Real.pi) * pi_phi, pi_phi] ∧
      BekensteinHawkingEntropyAreaBridge.bekensteinHawkingEntropy
        ((n : ℝ) * horizonAreaStep G hbar) G hbar = dyadicEntropyBits n := by
  constructor
  · dsimp [horizonShear4PiReal]
    rw [logCFTUnipotentFlow_pow, nsmul_eq_mul, logCFTUnipotentFlow_apply]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · dsimp [BekensteinHawkingEntropyAreaBridge.bekensteinHawkingEntropy,
      horizonAreaStep, planckArea, dyadicEntropyBits]
    have hden : 4 * G * hbar ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hG) hh
    field_simp [hden]

end HorizonShear

/-! ## I1. Graded-Derivation Cartan Magic Formula & Darboux Contact Volume Invariance -/

section CartanMagic

open InfoGeometry.Canonical.CartanLieDerivativeMagicBridge

/-- Algebraic differential graded algebra with parity involution `σ`, exterior derivative `d`,
and interior product `ι` (`Type*`-valued, avoiding `: Prop` wrapper constructors). -/
structure CartanDifferentialAlgebra (R A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  parity : A →ₐ[R] A
  parity_involution : ∀ x : A, parity (parity x) = x
  d : A →ₗ[R] A
  iota : A →ₗ[R] A
  d_sq : d.comp d = 0
  d_parity : ∀ x : A, d (parity x) = -parity (d x)
  iota_parity : ∀ x : A, iota (parity x) = -parity (iota x)
  d_leibniz : ∀ x y : A, d (x * y) = d x * y + parity x * d y
  iota_leibniz : ∀ x y : A, iota (x * y) = iota x * y + parity x * iota y

namespace CartanDifferentialAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Cartan's Lie derivative `ℒ = d ∘ ι + ι ∘ d`. -/
def lieDeriv (C : CartanDifferentialAlgebra R A) : A →ₗ[R] A :=
  C.d.comp C.iota + C.iota.comp C.d

/-- Compatibility bridge with `CartanLieDerivativeMagicBridge.lieDerivativeEnd`. -/
theorem cartanLieDeriv_eq_bridge {V : Type*} [AddCommGroup V] [Module R V]
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (C : CartanDifferentialAlgebra R (ExteriorAlgebra R V))
    (hd : C.d = d) (hi : C.iota = iota_X) :
    C.lieDeriv = lieDerivativeEnd d iota_X := by
  subst hd
  subst hi
  rfl

/-- `d ∘ ℒ = ℒ ∘ d`. -/
theorem lieDeriv_comm_d (C : CartanDifferentialAlgebra R A) :
    C.d.comp C.lieDeriv = C.lieDeriv.comp C.d := by
  ext x
  have hd2 : ∀ y : A, C.d (C.d y) = 0 := fun y => LinearMap.congr_fun C.d_sq y
  simp only [lieDeriv, LinearMap.comp_apply, LinearMap.add_apply, map_add, hd2, zero_add,
    map_zero, add_zero]

theorem lieDeriv_comm_d_apply (C : CartanDifferentialAlgebra R A) (x : A) :
    C.d (C.lieDeriv x) = C.lieDeriv (C.d x) :=
  LinearMap.congr_fun C.lieDeriv_comm_d x

/-- Cartan's Lie derivative `ℒ = d ∘ ι + ι ∘ d` is an ordinary derivation of `A`. -/
theorem lieDeriv_leibniz (C : CartanDifferentialAlgebra R A) (x y : A) :
    C.lieDeriv (x * y) = C.lieDeriv x * y + x * C.lieDeriv y := by
  change C.d (C.iota (x * y)) + C.iota (C.d (x * y)) =
    (C.d (C.iota x) + C.iota (C.d x)) * y + x * (C.d (C.iota y) + C.iota (C.d y))
  rw [C.iota_leibniz, C.d_leibniz, map_add, map_add, C.d_leibniz, C.d_leibniz,
    C.iota_leibniz, C.iota_leibniz, C.d_parity, C.iota_parity, C.parity_involution]
  noncomm_ring

/-- `ℒ(1) = 0`. -/
theorem lieDeriv_one (C : CartanDifferentialAlgebra R A) :
    C.lieDeriv 1 = 0 := by
  have h := C.lieDeriv_leibniz 1 1
  simp only [mul_one, one_mul] at h
  have h0 : C.lieDeriv 1 + 0 = C.lieDeriv 1 + C.lieDeriv 1 := by simpa using h
  exact (add_left_cancel h0).symm

/-- `ℒ(x) = 0 → ℒ(x^n) = 0`. -/
theorem lieDeriv_pow_eq_zero (C : CartanDifferentialAlgebra R A) {x : A}
    (hx : C.lieDeriv x = 0) (n : ℕ) :
    C.lieDeriv (x ^ n) = 0 := by
  induction n with
  | zero => simpa using C.lieDeriv_one
  | succ n ih =>
    rw [pow_succ', C.lieDeriv_leibniz, hx, ih, zero_mul, mul_zero, add_zero]

/-- Reeb invariance of the contact 1-form: `ι_R α = 1 ∧ ι_R (d α) = 0 → ℒ_R α = 0`. -/
theorem reeb_lieDeriv_alpha_eq_zero (C : CartanDifferentialAlgebra R A) (α : A)
    (h_alpha : C.iota α = 1) (h_dalpha : C.iota (C.d α) = 0) :
    C.lieDeriv α = 0 := by
  have hd1 : C.d 1 = 0 := by
    have h := C.d_leibniz 1 1
    simp only [mul_one, map_one, one_mul] at h
    have h0 : C.d 1 + 0 = C.d 1 + C.d 1 := by simpa using h
    exact (add_left_cancel h0).symm
  change C.d (C.iota α) + C.iota (C.d α) = 0
  rw [h_alpha, h_dalpha, hd1, add_zero]

/-- **Contact Volume Invariance**: `ι_R α = 1 ∧ ι_R (d α) = 0 → ℒ_R (α ∧ (d α)^n) = 0`. -/
theorem contact_volume_lieDeriv_eq_zero (C : CartanDifferentialAlgebra R A) (α : A)
    (h_alpha : C.iota α = 1) (h_dalpha : C.iota (C.d α) = 0) (n : ℕ) :
    C.lieDeriv (α * (C.d α) ^ n) = 0 := by
  have hLα : C.lieDeriv α = 0 := C.reeb_lieDeriv_alpha_eq_zero α h_alpha h_dalpha
  have hLdα : C.lieDeriv (C.d α) = 0 := by
    rw [← C.lieDeriv_comm_d_apply, hLα, map_zero]
  rw [C.lieDeriv_leibniz, hLα, C.lieDeriv_pow_eq_zero hLdα n, zero_mul, mul_zero, add_zero]

end CartanDifferentialAlgebra

/-! ### Concrete Non-Vacuous Darboux Contact 3-Space Instantiation -/

/-- Darboux contact 3-space polynomial exterior forms `ℝ[x,y,z] ⊗_ℝ Λ(ℝ³)`. -/
abbrev DarbouxForms := MvPolynomial (Fin 3) ℝ ⊗[ℝ] ExteriorAlgebra ℝ (Fin 3 → ℝ)

private abbrev Ext3 := ExteriorAlgebra ℝ (Fin 3 → ℝ)
private abbrev Poly3 := MvPolynomial (Fin 3) ℝ

private def extInvolute : Ext3 →ₐ[ℝ] Ext3 :=
  CliffordAlgebra.involute (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ)))

/-- Parity involution on `DarbouxForms`. -/
def darbouxParity : DarbouxForms →ₐ[ℝ] DarbouxForms :=
  Algebra.TensorProduct.map (AlgHom.id ℝ Poly3) extInvolute

private theorem extInvolute_involutive (ω : Ext3) : extInvolute (extInvolute ω) = ω :=
  CliffordAlgebra.involute_involute ω

private theorem extInvolute_iota (v : Fin 3 → ℝ) :
    extInvolute (ExteriorAlgebra.ι ℝ v) = -ExteriorAlgebra.ι ℝ v :=
  CliffordAlgebra.involute_ι v

private lemma poly3_pderiv_comm (i j : Fin 3) (f : Poly3) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  let C : Derivation ℝ Poly3 Poly3 :=
    ⁅(MvPolynomial.pderiv i : Derivation ℝ Poly3 Poly3),
      (MvPolynomial.pderiv j : Derivation ℝ Poly3 Poly3)⁆
  have hC : C = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [C, Derivation.commutator_apply, MvPolynomial.pderiv_def]
  have hzero : MvPolynomial.pderiv i (MvPolynomial.pderiv j f) -
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) = 0 := by
    simpa [C, Derivation.commutator_apply] using Derivation.congr_fun hC f
  exact sub_eq_zero.mp hzero

private theorem iota_mul_eq_involute_mul_iota (v : Fin 3 → ℝ) (ω : Ext3) :
    ExteriorAlgebra.ι ℝ v * ω = extInvolute ω * ExteriorAlgebra.ι ℝ v := by
  induction ω using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [extInvolute, AlgHom.map_algebraMap, Algebra.commutes]
  | add x y hx hy =>
    simp only [mul_add, map_add, add_mul, hx, hy]
  | ι_mul x u hx =>
    have hswap : ExteriorAlgebra.ι ℝ v * ExteriorAlgebra.ι ℝ u =
        -(ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v) := by
      have h := ExteriorAlgebra.ι_add_mul_swap (R := ℝ) v u
      exact eq_neg_of_add_eq_zero_left h
    calc
      ExteriorAlgebra.ι ℝ v * (ExteriorAlgebra.ι ℝ u * x)
        = (ExteriorAlgebra.ι ℝ v * ExteriorAlgebra.ι ℝ u) * x := by rw [← mul_assoc]
      _ = -(ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v) * x := by rw [hswap]
      _ = -(ExteriorAlgebra.ι ℝ u * (ExteriorAlgebra.ι ℝ v * x)) := by rw [neg_mul, mul_assoc]
      _ = -(ExteriorAlgebra.ι ℝ u * (extInvolute x * ExteriorAlgebra.ι ℝ v)) := by rw [hx]
      _ = -((ExteriorAlgebra.ι ℝ u * extInvolute x) * ExteriorAlgebra.ι ℝ v) := by
            rw [← mul_assoc]
      _ = extInvolute (ExteriorAlgebra.ι ℝ u * x) * ExteriorAlgebra.ι ℝ v := by
            rw [map_mul, extInvolute_iota, neg_mul, neg_mul]

private def darbouxTermD (i : Fin 3) : DarbouxForms →ₗ[ℝ] DarbouxForms :=
  TensorProduct.map (MvPolynomial.pderiv i).toLinearMap
    (Algebra.lmul ℝ Ext3 (ExteriorAlgebra.ι ℝ (Pi.single i 1)))

/-- Exterior derivative `d = ∑ᵢ ∂ᵢ ⊗ (dxⁱ ∧ ·)` on `DarbouxForms`. -/
def darbouxD : DarbouxForms →ₗ[ℝ] DarbouxForms :=
  ∑ i : Fin 3, darbouxTermD i

private theorem darbouxD_tmul (f : Poly3) (ω : Ext3) :
    darbouxD (f ⊗ₜ[ℝ] ω) =
      ∑ i : Fin 3, MvPolynomial.pderiv i f ⊗ₜ[ℝ] (ExteriorAlgebra.ι ℝ (Pi.single i 1) * ω) := by
  simp [darbouxD, darbouxTermD, LinearMap.sum_apply, TensorProduct.map_tmul]

private theorem darbouxD_sq : darbouxD.comp darbouxD = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul f ω =>
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [darbouxD_tmul, map_sum]
    simp_rw [darbouxD_tmul, ← mul_assoc]
    set T : Fin 3 → Fin 3 → DarbouxForms := fun i j =>
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) ⊗ₜ[ℝ]
        ((ExteriorAlgebra.ι ℝ (Pi.single j 1) * ExteriorAlgebra.ι ℝ (Pi.single i 1)) * ω)
    have hpair : ∀ i j : Fin 3, T i j + T j i = 0 := by
      intro i j
      dsimp only [T]
      rw [poly3_pderiv_comm j i f, ← TensorProduct.tmul_add, ← add_mul,
        ExteriorAlgebra.ι_add_mul_swap, zero_mul, TensorProduct.tmul_zero]
    have hdouble : (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, T i j) = 0 := by
      rw [two_smul]
      nth_rw 2 [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => hpair i j
    exact (smul_eq_zero.mp hdouble).resolve_left (by norm_num)
  | add x y hx hy => simp [map_add, hx, hy]

private theorem darbouxD_parity (x : DarbouxForms) :
    darbouxD (darbouxParity x) = -darbouxParity (darbouxD x) := by
  induction x using TensorProduct.inductionOn with
  | tmul f ω =>
    simp only [darbouxParity, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      darbouxD_tmul, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, extInvolute_iota, neg_mul, TensorProduct.tmul_neg, neg_neg]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    abel

private theorem darbouxD_leibniz (x y : DarbouxForms) :
    darbouxD (x * y) = darbouxD x * y + darbouxParity x * darbouxD y := by
  induction x using TensorProduct.inductionOn with
  | tmul f₁ ω₁ =>
    induction y using TensorProduct.inductionOn with
    | tmul f₂ ω₂ =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, darbouxD_tmul, darbouxParity,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPolynomial.pderiv_mul, TensorProduct.add_tmul, ← mul_assoc,
        iota_mul_eq_involute_mul_iota (Pi.single i 1) ω₁, mul_assoc]
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [mul_add, map_add, hy₁, hy₂]
      abel
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [add_mul, map_add, hx₁, hx₂]
    abel

/-- Reeb interior product `ι_{∂_z}` on `DarbouxForms` (`R = e₂`). -/
def darbouxIotaR : DarbouxForms →ₗ[ℝ] DarbouxForms :=
  LinearMap.lTensor Poly3 (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ)))
    (LinearMap.proj 2))

private theorem contractLeft_involute (φ : Module.Dual ℝ (Fin 3 → ℝ)) (ω : Ext3) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ))) φ (extInvolute ω) =
      -extInvolute (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ))) φ ω) := by
  induction ω using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp [extInvolute, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    abel
  | ι_mul x v hx =>
    rw [map_mul, extInvolute_iota, neg_mul, map_neg,
      CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul,
      hx, map_sub, map_smul, map_mul, extInvolute_iota]
    simp only [neg_mul, neg_sub, sub_neg_eq_add]
    rw [mul_neg]
    abel

private theorem contractLeft_mul (φ : Module.Dual ℝ (Fin 3 → ℝ)) (ω₁ ω₂ : Ext3) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ))) φ (ω₁ * ω₂) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ))) φ ω₁ * ω₂ +
        extInvolute ω₁ *
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ))) φ ω₂ := by
  induction ω₁ using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [extInvolute, map_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul,
      CliffordAlgebra.contractLeft_one, smul_zero, zero_mul, zero_add]
  | add x y hx hy =>
    simp only [add_mul, map_add, hx, hy]
    abel
  | ι_mul x v hx =>
    rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, hx, CliffordAlgebra.contractLeft_ι_mul,
      map_mul, extInvolute_iota]
    simp only [sub_mul, smul_mul_assoc, mul_assoc, neg_mul, mul_add]
    abel

private theorem darbouxIotaR_parity (x : DarbouxForms) :
    darbouxIotaR (darbouxParity x) = -darbouxParity (darbouxIotaR x) := by
  induction x using TensorProduct.inductionOn with
  | tmul f ω =>
    simp only [darbouxParity, darbouxIotaR, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      LinearMap.lTensor_tmul, contractLeft_involute, TensorProduct.tmul_neg]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    abel

private theorem darbouxIotaR_leibniz (x y : DarbouxForms) :
    darbouxIotaR (x * y) = darbouxIotaR x * y + darbouxParity x * darbouxIotaR y := by
  induction x using TensorProduct.inductionOn with
  | tmul f₁ ω₁ =>
    induction y using TensorProduct.inductionOn with
    | tmul f₂ ω₂ =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, darbouxIotaR, LinearMap.lTensor_tmul,
        darbouxParity, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, contractLeft_mul,
        TensorProduct.tmul_add]
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [mul_add, map_add, hy₁, hy₂]
      abel
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [add_mul, map_add, hx₁, hx₂]
    abel

/-- Concrete `CartanDifferentialAlgebra` on Darboux contact 3-space `DarbouxForms`. -/
def darbouxCartanAlgebra : CartanDifferentialAlgebra ℝ DarbouxForms where
  parity := darbouxParity
  parity_involution x := by
    induction x using TensorProduct.inductionOn with
    | tmul f ω => simp [darbouxParity, extInvolute_involutive]
    | add a b ha hb => simp [map_add, ha, hb]
  d := darbouxD
  iota := darbouxIotaR
  d_sq := darbouxD_sq
  d_parity := darbouxD_parity
  iota_parity := darbouxIotaR_parity
  d_leibniz := darbouxD_leibniz
  iota_leibniz := darbouxIotaR_leibniz

/-- Canonical Darboux contact 1-form `α = dz - y dx`. -/
def darbouxAlpha : DarbouxForms :=
  (1 : Poly3) ⊗ₜ[ℝ] ExteriorAlgebra.ι ℝ (Pi.single 2 1) -
    (MvPolynomial.X 1) ⊗ₜ[ℝ] ExteriorAlgebra.ι ℝ (Pi.single 0 1)

/-- `ι_{∂_z} α = 1`. -/
theorem darbouxIotaR_alpha : darbouxIotaR darbouxAlpha = 1 := by
  dsimp [darbouxAlpha, darbouxIotaR]
  rw [map_sub, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
  rw [CliffordAlgebra.contractLeft_ι, CliffordAlgebra.contractLeft_ι]
  simp [Algebra.TensorProduct.one_def]

/-- `ι_{∂_z} (d α) = 0`. -/
theorem darbouxIotaR_d_alpha : darbouxIotaR (darbouxD darbouxAlpha) = 0 := by
  have hd : darbouxD darbouxAlpha =
      -((1 : Poly3) ⊗ₜ[ℝ]
        (ExteriorAlgebra.ι ℝ (Pi.single 1 1) * ExteriorAlgebra.ι ℝ (Pi.single 0 1))) := by
    dsimp [darbouxAlpha]
    rw [map_sub, darbouxD_tmul, darbouxD_tmul]
    simp [Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply]
  rw [hd]
  dsimp [darbouxIotaR]
  rw [map_neg, LinearMap.lTensor_tmul, CliffordAlgebra.contractLeft_ι_mul]
  simp

set_option maxHeartbeats 400000 in
/-- Non-vacuity: the Darboux contact volume form `α ∧ dα` is nonzero! -/
theorem darboux_volume_ne_zero : darbouxAlpha * (darbouxD darbouxAlpha) ^ 1 ≠ 0 := by
  intro hvol
  let c0 := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ)))
    (LinearMap.proj (0 : Fin 3))
  let c1 := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ)))
    (LinearMap.proj (1 : Fin 3))
  let c2 := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Fin 3 → ℝ)))
    (LinearMap.proj (2 : Fin 3))
  let eval0 : Poly3 →ₗ[ℝ] ℝ := (MvPolynomial.aeval (0 : Fin 3 → ℝ)).toLinearMap
  let probe : DarbouxForms →ₗ[ℝ] ℝ ⊗[ℝ] Ext3 :=
    TensorProduct.map eval0 (c1.comp (c0.comp c2))
  let e0 : Ext3 := ExteriorAlgebra.ι ℝ (Pi.single (0 : Fin 3) (1 : ℝ))
  let e1 : Ext3 := ExteriorAlgebra.ι ℝ (Pi.single (1 : Fin 3) (1 : ℝ))
  let e2 : Ext3 := ExteriorAlgebra.ι ℝ (Pi.single (2 : Fin 3) (1 : ℝ))
  have hd : darbouxD darbouxAlpha = -((1 : Poly3) ⊗ₜ[ℝ] (e1 * e0)) := by
    dsimp [darbouxAlpha, e0, e1]
    rw [map_sub, darbouxD_tmul, darbouxD_tmul]
    simp [Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply]
  have hterm : darbouxAlpha * (darbouxD darbouxAlpha) ^ 1 =
      -((1 : Poly3) ⊗ₜ[ℝ] (e2 * (e1 * e0))) +
      (MvPolynomial.X 1) ⊗ₜ[ℝ] (e0 * (e1 * e0)) := by
    have hneg1 : -((1 : Poly3) ⊗ₜ[ℝ] (e1 * e0)) = (-1 : Poly3) ⊗ₜ[ℝ] (e1 * e0) :=
      (TensorProduct.neg_tmul (1 : Poly3) (e1 * e0)).symm
    rw [pow_one, hd, hneg1]
    dsimp [darbouxAlpha, e0, e1, e2]
    rw [sub_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_neg, mul_one, TensorProduct.neg_tmul, TensorProduct.neg_tmul,
      sub_neg_eq_add]
  have hprobe_zero : probe (darbouxAlpha * (darbouxD darbouxAlpha) ^ 1) = 0 := by
    rw [hvol, map_zero]
  rw [hterm, map_add, map_neg] at hprobe_zero
  have hX1 : eval0 (MvPolynomial.X 1) = 0 := by simp [eval0]
  have h1 : eval0 (1 : Poly3) = 1 := by simp [eval0]
  have hc2 : c2 (e2 * (e1 * e0)) = e1 * e0 := by
    dsimp [c2, e0, e1, e2]
    rw [CliffordAlgebra.contractLeft_ι_mul]
    simp only [LinearMap.proj_apply, Pi.single_eq_same, one_smul]
    rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι]
    simp
  have hc0 : c0 (e1 * e0) = -e1 := by
    dsimp [c0, e0, e1]
    rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι]
    simp
  have hc1 : c1 (-e1) = -1 := by
    dsimp [c1, e1]
    rw [map_neg, CliffordAlgebra.contractLeft_ι]
    simp
  have hprobe_val :
      -(probe ((1 : Poly3) ⊗ₜ[ℝ] (e2 * (e1 * e0)))) +
      probe ((MvPolynomial.X 1) ⊗ₜ[ℝ] (e0 * (e1 * e0))) =
      (1 : ℝ) ⊗ₜ[ℝ] 1 := by
    simp only [probe, TensorProduct.map_tmul, hX1, TensorProduct.zero_tmul, add_zero, h1,
      LinearMap.comp_apply, hc2, hc0, hc1, TensorProduct.tmul_neg, neg_neg]
  rw [hprobe_val] at hprobe_zero
  have hunit := congrArg (Algebra.TensorProduct.lid ℝ Ext3) hprobe_zero
  simp only [Algebra.TensorProduct.lid_tmul, one_smul, map_zero] at hunit
  exact one_ne_zero hunit

/-- Exact contact volume invariance on Darboux contact 3-space: `ℒ_{∂_z}(α ∧ dα) = 0`. -/
theorem darboux_contact_volume_invariance :
    darbouxCartanAlgebra.lieDeriv (darbouxAlpha * (darbouxD darbouxAlpha) ^ 1) = 0 :=
  darbouxCartanAlgebra.contact_volume_lieDeriv_eq_zero darbouxAlpha
    darbouxIotaR_alpha darbouxIotaR_d_alpha 1

end CartanMagic

/-! ## I2. K-Contact Reeb–Killing Isometry & Conditional Noether Conservation -/

section KContactNoether

open InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
open InfoGeometry.Thermo.BipolarLinearCosymplecticStructure

/-- K-contact metric `g_contact = g_horiz + α ⊗ α` on `BipolarLinearCosymplecticStructure.State3`. -/
def bipolarKContactMetric (u v : State3) : ℝ :=
  u 1 * v 1 + u 2 * v 2 + etaCovector u * etaCovector v

/-- Reeb compatibility `g(R, v) = α(v)`. -/
theorem bipolarKContactMetric_reeb_dual (v : State3) :
    bipolarKContactMetric reebVector v = etaCovector v := by
  simp [bipolarKContactMetric, reebVector, etaBasis3, etaCovector]

/-- Reeb vector has unit length `g(R, R) = 1`. -/
theorem bipolarKContactMetric_reeb_unit :
    bipolarKContactMetric reebVector reebVector = 1 := by
  rw [bipolarKContactMetric_reeb_dual, etaCovector_reebVector]

/-- Linear Reeb translation flow `Φ_t(x) = x + t • R`. -/
def bipolarReebFlow (t : ℝ) (x : State3) : State3 :=
  x + t • reebVector

/-- The Reeb flow is an exact isometry of `bipolarKContactMetric`. -/
theorem bipolarReebFlow_isometry (t : ℝ) (u v : State3) :
    bipolarKContactMetric (bipolarReebFlow t u - bipolarReebFlow t v)
        (bipolarReebFlow t u - bipolarReebFlow t v) =
      bipolarKContactMetric (u - v) (u - v) := by
  have hdiff : bipolarReebFlow t u - bipolarReebFlow t v = u - v := by
    dsimp [bipolarReebFlow]
    abel
  rw [hdiff]

/-- Planar rotational Killing generator `ξ(η, θ, a) = (0, -a, θ)` on `State3`. -/
def bipolarPlanarKillingGen : State3 →ₗ[ℝ] State3 where
  toFun x := ![0, -x 2, x 1]
  map_add' x y := by
    ext i
    fin_cases i
    · simp
    · simp; ring
    · simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

/-- `bipolarPlanarKillingGen` satisfies the skew-Killing equation `g(ξ u, v) + g(u, ξ v) = 0`. -/
theorem bipolarPlanarKillingGen_killing (u v : State3) :
    bipolarKContactMetric (bipolarPlanarKillingGen u) v +
      bipolarKContactMetric u (bipolarPlanarKillingGen v) = 0 := by
  simp [bipolarKContactMetric, bipolarPlanarKillingGen, etaCovector]

/-- `bipolarPlanarKillingGen` annihilates `R` and preserves both `α` and `ω_horiz`. -/
theorem bipolarPlanarKillingGen_preserves_cosymplectic (u v : State3) :
    etaCovector (bipolarPlanarKillingGen u) = 0 ∧
      horizontalTwoForm (bipolarPlanarKillingGen u) v +
        horizontalTwoForm u (bipolarPlanarKillingGen v) = 0 ∧
      bipolarPlanarKillingGen reebVector = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bipolarPlanarKillingGen, etaCovector]
  · simp [horizontalTwoForm, bipolarPlanarKillingGen]
    ring
  · ext i
    fin_cases i <;> simp [bipolarPlanarKillingGen, reebVector, etaBasis3]

/-- **Conditional K-Contact Killing Noether Constant (`[bucket_2_conditional]`)**:
If a 1-parameter isometry semigroup `Φ_t` preserves `g` and fixes the Reeb/Killing vector `r`,
then the Noether pairing `g(r, Φ_t u)` is conserved for all `t`. -/
theorem killing_flow_noether_semigroup_constant {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : LinearMap.BilinForm ℝ V) (Φ : ℝ → V →ₗ[ℝ] V) (r : V)
    (hIso : ∀ t u v, g (Φ t u) (Φ t v) = g u v)
    (hFix : ∀ t, Φ t r = r) (t : ℝ) (u : V) :
    g r (Φ t u) = g r u := by
  calc
    g r (Φ t u) = g (Φ t r) (Φ t u) := by rw [hFix t]
    _ = g r u := hIso t r u

/-- **Analytic `State3` Killing Flow Constant (`[bucket_2_conditional]`)**:
Along any flow `γ : ℝ → State3` with `γ'(t) = K(γ(t))` for a Killing generator `K` of
`bipolarKContactMetric`, the Killing kinetic norm `g(γ'(t), γ'(t))` has zero derivative. -/
theorem killing_flow_noether_constant (K : State3 →ₗ[ℝ] State3)
    (hKilling : ∀ u v, bipolarKContactMetric (K u) v + bipolarKContactMetric u (K v) = 0)
    (γ : ℝ → State3) (hFlow : ∀ t, HasDerivAt γ (K (γ t)) t) (t : ℝ) :
    HasDerivAt (fun s => bipolarKContactMetric (K (γ s)) (K (γ s))) 0 t := by
  have hKderiv : ∀ i : Fin 3,
      HasDerivAt (fun s => (K (γ s)) i) ((K (K (γ t))) i) t := by
    intro i
    have hcomp : HasDerivAt (fun s => K (γ s)) (K (K (γ t))) t :=
      K.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hFlow t)
    exact (hasDerivAt_pi.mp hcomp) i
  have h1 := (hKderiv 1).mul (hKderiv 1)
  have h2 := (hKderiv 2).mul (hKderiv 2)
  have h0 := (hKderiv 0).mul (hKderiv 0)
  have htot : HasDerivAt (fun s => bipolarKContactMetric (K (γ s)) (K (γ s)))
      (2 * bipolarKContactMetric (K (K (γ t))) (K (γ t))) t := by
    have heq : (fun s => bipolarKContactMetric (K (γ s)) (K (γ s))) =
        fun s => (K (γ s) 1) * (K (γ s) 1) + (K (γ s) 2) * (K (γ s) 2) +
          (K (γ s) 0) * (K (γ s) 0) := by
      ext s
      simp [bipolarKContactMetric, etaCovector]
    rw [heq]
    convert (h1.add h2).add h0 using 1
    simp [bipolarKContactMetric, etaCovector]
    ring
  have hzero : bipolarKContactMetric (K (K (γ t))) (K (γ t)) = 0 := by
    have h := hKilling (K (γ t)) (K (γ t))
    have hsymm : bipolarKContactMetric (K (γ t)) (K (K (γ t))) =
        bipolarKContactMetric (K (K (γ t))) (K (γ t)) := by
      simp only [bipolarKContactMetric]; ring
    linarith
  rw [hzero, mul_zero] at htot
  exact htot

/-- **Conditional Stokes + Cartan Noether Charge Conservation (`[bucket_2_conditional]`)**:
For any closed-cycle integral `∫_Σ` satisfying Stokes (`∫_Σ dω = 0`), the Lie variation of
the contact volume form `∫_Σ ℒ_R (α ∧ (dα)^n) = 0`.
*(Equating `∫_Σ α ∧ (dα)^n` with `19 ℏ_contact` in `T71:5485` remains `[bucket_3_open_debt]`.)* -/
theorem stokes_noether_contact_volume_zero {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (C : CartanDifferentialAlgebra R A) (integral : A →ₗ[R] R)
    (α : A) (h_alpha : C.iota α = 1) (h_dalpha : C.iota (C.d α) = 0) (n : ℕ) :
    integral (C.lieDeriv (α * (C.d α) ^ n)) = 0 := by
  rw [C.contact_volume_lieDeriv_eq_zero α h_alpha h_dalpha n, map_zero]

/-- Conditional Stokes invariance of any closed form under Cartan's Lie derivative:
`d μ = 0 → ∫_Σ ℒ_R μ = ∫_Σ d(ι_R μ) = 0` (`[bucket_2_conditional]`). -/
theorem stokes_closed_form_lieDeriv_zero {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (C : CartanDifferentialAlgebra R A) (integral : A →ₗ[R] R)
    (hStokes : ∀ ω : A, integral (C.d ω) = 0)
    (μ : A) (hClosed : C.d μ = 0) :
    integral (C.lieDeriv μ) = 0 := by
  change integral (C.d (C.iota μ) + C.iota (C.d μ)) = 0
  rw [hClosed, map_zero, add_zero, hStokes (C.iota μ)]

/-- **Souriau–Legendre & K-Contact Killing Compatibility (`[bucket_2_conditional]`)**:
Reuses `InfoGeometry.Thermodynamics.hodge_star_executes_legendre_transform` on the doubled Krein
carrier alongside the semigroup Noether conservation law.
*(Physical identification of the conserved Noether charge with `19 ℏ_contact` is `[bucket_3_open_debt]`.)* -/
theorem souriau_legendre_killing_compatibility
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (reference comparison : InfoGeometry.Krein.DoubledSpace E)
    (X Y : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)
    (hJ : InfoGeometry.Canonical.OnsagerCasimirJ.IsJInvariant X)
    (hY : InfoGeometry.Canonical.OnsagerCasimirJ.IsJInvariant Y)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : LinearMap.BilinForm ℝ V) (Φ : ℝ → V →ₗ[ℝ] V) (r : V)
    (hIso : ∀ t u v, g (Φ t u) (Φ t v) = g u v)
    (hFix : ∀ t, Φ t r = r) (t : ℝ) (u : V) :
    InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation (E := E)
        (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E) reference)
        (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E) comparison)
        (InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis X) Y =
      -InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation (E := E)
        reference comparison
        (InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis X) Y ∧
    g r (Φ t u) = g r u :=
  ⟨InfoGeometry.Thermodynamics.hodge_star_executes_legendre_transform
      (E := E) reference comparison X Y hJ hY,
   killing_flow_noether_semigroup_constant g Φ r hIso hFix t u⟩

end KContactNoether

end InfoGeometry.Canonical.BornParaKahlerHorizonShear
