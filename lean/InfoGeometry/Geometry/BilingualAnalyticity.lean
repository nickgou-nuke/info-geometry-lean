/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Real.Hyperreal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Parahyperkahler.AnalyticExcision
import InfoGeometry.InformationGeometry.BurgSteinSelfConcordance

noncomputable section

namespace InfoGeometry.Geometry.BilingualAnalyticity

/-! ## 1. Phase structures -/

/--
A real-linear phase structure.

This is the real doubled replacement for multiplication by `i`.
-/
structure PhaseStructure
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- Phase axis / complex structure. -/
  K : X →L[ℝ] X

  /-- `K² = -1`. -/
  K_square :
    K.comp K = -(ContinuousLinearMap.id ℝ X)

namespace PhaseStructure

variable
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (J : PhaseStructure X)

/--
Phase-linearity of a bounded real-linear map between phase spaces.
-/
def IsPhaseLinearMap
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y)
    (Ktar : PhaseStructure Y) : Prop :=
  L.comp J.K = Ktar.K.comp L

variable
    {Y Z : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Pointwise form of phase-linearity. -/
theorem phaseLinear_apply
    {KX : PhaseStructure X}
    {KY : PhaseStructure Y}
    {L : X →L[ℝ] Y}
    (hL : KX.IsPhaseLinearMap L KY)
    (v : X) :
    L (KX.K v) = KY.K (L v) := by
  have h := congrArg (fun T : X →L[ℝ] Y => T v) hL
  simpa [IsPhaseLinearMap, ContinuousLinearMap.comp_apply] using h

/-- The identity map is phase-linear. -/
theorem id_phaseLinear
    (KX : PhaseStructure X) :
    KX.IsPhaseLinearMap (ContinuousLinearMap.id ℝ X) KX := by
  ext v
  simp

/-- Composition of phase-linear maps is phase-linear. -/
theorem comp_phaseLinear
    (KX : PhaseStructure X)
    (KY : PhaseStructure Y)
    (KZ : PhaseStructure Z)
    {L : X →L[ℝ] Y}
    {M : Y →L[ℝ] Z}
    (hL : KX.IsPhaseLinearMap L KY)
    (hM : KY.IsPhaseLinearMap M KZ) :
    KX.IsPhaseLinearMap (M.comp L) KZ := by
  dsimp [IsPhaseLinearMap] at hL hM ⊢
  calc
    (M.comp L).comp KX.K = M.comp (L.comp KX.K) := by
      ext v
      simp [ContinuousLinearMap.comp_apply]
    _ = M.comp (KY.K.comp L) := by rw [hL]
    _ = (M.comp KY.K).comp L := by
      ext v
      simp [ContinuousLinearMap.comp_apply]
    _ = (KZ.K.comp M).comp L := by rw [hM]
    _ = KZ.K.comp (M.comp L) := by
      ext v
      simp [ContinuousLinearMap.comp_apply]

end PhaseStructure

/-! ## 2. Cauchy analyticity -/

/--
Cauchy analyticity at a point, in real phase-linear form.

This is pointwise Cauchy analyticity/differentiability. It is not a
power-series or open-neighborhood holomorphicity assertion.

The function is real-Fréchet differentiable, and its derivative commutes with
the phase structures.
-/
structure CauchyAnalyticAt
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (F : X → Y)
    (x : X) where

  /-- Real Fréchet derivative. -/
  deriv : X →L[ℝ] Y

  /-- Real differentiability witness. -/
  has_fderiv_at :
    HasFDerivAt F deriv x

  /--
  Cauchy-Riemann law in phase form:

  `dF_x ∘ Kdom = Ktar ∘ dF_x`.
  -/
  phase_linear_deriv :
    deriv.comp Kdom.K = Ktar.K.comp deriv

namespace CauchyAnalyticAt

variable
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Kdom : PhaseStructure X}
    {Ktar : PhaseStructure Y}
    {F : X → Y}
    {x : X}

variable (A : CauchyAnalyticAt Kdom Ktar F x)

/--
Pointwise Cauchy-Riemann law.
-/
theorem cauchyRiemann_apply
    (v : X) :
    A.deriv (Kdom.K v) = Ktar.K (A.deriv v) := by
  exact PhaseStructure.phaseLinear_apply A.phase_linear_deriv v

/-- The derivative is phase-linear. -/
theorem deriv_phaseLinear :
    Kdom.IsPhaseLinearMap A.deriv Ktar :=
  A.phase_linear_deriv

end CauchyAnalyticAt

/-! ## 2A. Constructive Cauchy-analytic constructors -/

namespace CauchyAnalyticAt

variable
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/--
The identity map is Cauchy-analytic for any phase structure.
-/
def id
    (K : PhaseStructure X)
    (x : X) :
    CauchyAnalyticAt K K (fun y : X => y) x where
  deriv := ContinuousLinearMap.id ℝ X
  has_fderiv_at := by

    exact hasFDerivAt_id x
  phase_linear_deriv := by
    ext v
    simp

/--
A constant map is Cauchy-analytic, with zero derivative.
-/
def const
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (y0 : Y)
    (x : X) :
    CauchyAnalyticAt Kdom Ktar (fun _ : X => y0) x where
  deriv := 0
  has_fderiv_at := by

    exact hasFDerivAt_const y0 x
  phase_linear_deriv := by
    ext v
    simp

/--
A continuous real-linear map whose operator commutes with the source and target
phase structures is Cauchy-analytic everywhere.
-/
def ofContinuousLinearMap
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (L : X →L[ℝ] Y)
    (hL : L.comp Kdom.K = Ktar.K.comp L)
    (x : X) :
    CauchyAnalyticAt Kdom Ktar (fun y : X => L y) x where
  deriv := L
  has_fderiv_at := by

    exact L.hasFDerivAt
  phase_linear_deriv := hL

/--
Composition of Cauchy-analytic maps is Cauchy-analytic.

This is the constructive phase-form Cauchy-Riemann chain rule.
-/
def comp
    {KX : PhaseStructure X}
    {KY : PhaseStructure Y}
    {KZ : PhaseStructure Z}
    {F : X → Y}
    {G : Y → Z}
    {x : X}
    (A : CauchyAnalyticAt KX KY F x)
    (B : CauchyAnalyticAt KY KZ G (F x)) :
    CauchyAnalyticAt KX KZ (fun u : X => G (F u)) x where
  deriv := B.deriv.comp A.deriv
  has_fderiv_at := by

    exact B.has_fderiv_at.comp x A.has_fderiv_at
  phase_linear_deriv := by
    ext v
    change B.deriv (A.deriv (KX.K v)) =
      KZ.K (B.deriv (A.deriv v))
    rw [A.cauchyRiemann_apply v]
    rw [B.cauchyRiemann_apply (A.deriv v)]

/--
The derivative of the composition is the expected composite derivative.
-/
theorem comp_deriv
    {KX : PhaseStructure X}
    {KY : PhaseStructure Y}
    {KZ : PhaseStructure Z}
    {F : X → Y}
    {G : Y → Z}
    {x : X}
    (A : CauchyAnalyticAt KX KY F x)
    (B : CauchyAnalyticAt KY KZ G (F x)) :
    (comp A B).deriv = B.deriv.comp A.deriv :=
  rfl

end CauchyAnalyticAt

/-! ## 2B. Mathlib complex analyticity bridge -/

/--
The canonical phase axis on `ℂ`, viewed as a real continuous-linear map:
multiplication by `I`.
-/
noncomputable def complexIMap : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.mul ℝ ℂ Complex.I

/--
The canonical real phase structure on `ℂ`.

Its phase operator is multiplication by `I`, so the square law is the usual
`I * I = -1`.
-/
noncomputable def complexPhaseStructure : PhaseStructure ℂ where
  K := complexIMap
  K_square := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply]
    change Complex.I * (Complex.I * z) = -z
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/--
A complex continuous-linear map is phase-linear after restriction of scalars
to `ℝ`.
-/
theorem complexLinearMap_phaseLinear
    (L : ℂ →L[ℂ] ℂ) :
    complexPhaseStructure.IsPhaseLinearMap (L.restrictScalars ℝ)
      complexPhaseStructure := by
  ext z
  simp only [ContinuousLinearMap.comp_apply]
  change L (Complex.I * z) = Complex.I * L z
  simpa only [smul_eq_mul] using L.map_smul Complex.I z

/--
Mathlib power-series analyticity over `ℂ` implies the repository's pointwise
Cauchy analyticity on the canonical complex phase structure.

This is only the honest one-way bridge: `AnalyticAt` supplies a complex
Fréchet derivative, and complex linearity of that derivative supplies the
phase-form Cauchy-Riemann law.
-/
def analyticAt_complex_to_cauchyAnalyticAt
    {f : ℂ → ℂ}
    {x : ℂ}
    (hf : AnalyticAt ℂ f x) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f x := by
  let dC : ℂ →L[ℂ] ℂ := fderiv ℂ f x
  refine
    { deriv := dC.restrictScalars ℝ
      has_fderiv_at := ?_
      phase_linear_deriv := ?_ }
  · exact hf.differentiableAt.hasFDerivAt.restrictScalars ℝ
  · exact complexLinearMap_phaseLinear dC

/-- Canonical real phase structure `v ↦ B • v` induced by any unit bivector
`B : A` (`B * B = -1`) in a real normed algebra `A` acting on a normed `A`-module `X`. -/
noncomputable def bivectorPhaseStructure
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Module A X] [IsScalarTower ℝ A X] [ContinuousSMul A X]
    (B : A) (hB : B * B = -1) :
    PhaseStructure X where
  K :=
    { toFun := fun v : X => B • v
      map_add' := fun u v => smul_add B u v
      map_smul' := fun r v => by
        simp only [RingHom.id_apply]
        calc
          B • (r • v)
              = B • ((r • (1 : A)) • v) := by rw [smul_one_smul]
          _ = (B * (r • (1 : A))) • v := by rw [smul_smul]
          _ = ((r • (1 : A)) * B) • v := by
              rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
          _ = (r • (1 : A)) • (B • v) := by rw [smul_smul]
          _ = r • (B • v) := by rw [smul_one_smul]
      cont := continuous_const.smul continuous_id }
  K_square := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, neg_apply, ContinuousLinearMap.id_apply]
    rw [smul_smul, hB, neg_one_smul]

/-- Bivector rotor `R(θ) = cos θ • 1 + sin θ • B` generated by a unit bivector `B` (`B * B = -1`). -/
noncomputable def bivectorRotor
    {A : Type*} [Ring A] [Module ℝ A]
    (B : A) (θ : ℝ) : A :=
  Real.cos θ • (1 : A) + Real.sin θ • B

theorem bivectorRotor_zero
    {A : Type*} [Ring A] [Module ℝ A] (B : A) :
    bivectorRotor B 0 = 1 := by
  simp [bivectorRotor]

theorem bivectorRotor_pi_div_two
    {A : Type*} [Ring A] [Module ℝ A] (B : A) :
    bivectorRotor B (Real.pi / 2) = B := by
  simp [bivectorRotor]

theorem bivectorRotor_mul
    {A : Type*} [Ring A] [Algebra ℝ A]
    {B : A} (hB : B * B = -1) (θ₁ θ₂ : ℝ) :
    bivectorRotor B θ₁ * bivectorRotor B θ₂ = bivectorRotor B (θ₁ + θ₂) := by
  unfold bivectorRotor
  rw [add_mul, mul_add, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hB, smul_neg]
  rw [Real.cos_add, Real.sin_add]
  simp only [sub_smul, add_smul, smul_smul]
  simp only [mul_comm (Real.cos θ₂), mul_comm (Real.sin θ₂)]
  abel

theorem bivectorRotor_mul_neg
    {A : Type*} [Ring A] [Algebra ℝ A]
    {B : A} (hB : B * B = -1) (θ : ℝ) :
    bivectorRotor B θ * bivectorRotor B (-θ) = 1 := by
  rw [bivectorRotor_mul hB, add_neg_cancel, bivectorRotor_zero]

/-- Continuous real-linear rotor action `v ↦ R(θ) • v` on a normed `A`-module. -/
noncomputable def bivectorRotorMap
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Module A X] [IsScalarTower ℝ A X] [ContinuousSMul A X]
    (B : A) (θ : ℝ) : X →L[ℝ] X where
  toFun := fun v => bivectorRotor B θ • v
  map_add' := fun u v => smul_add _ u v
  map_smul' := fun r v => by
    simp only [RingHom.id_apply]
    calc
      bivectorRotor B θ • (r • v)
          = bivectorRotor B θ • ((r • (1 : A)) • v) := by rw [smul_one_smul]
      _ = (bivectorRotor B θ * (r • (1 : A))) • v := by rw [smul_smul]
      _ = ((r • (1 : A)) * bivectorRotor B θ) • v := by
          rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      _ = (r • (1 : A)) • (bivectorRotor B θ • v) := by rw [smul_smul]
      _ = r • (bivectorRotor B θ • v) := by rw [smul_one_smul]
  cont := continuous_const.smul continuous_id

/-- Every bivector rotor `R(θ)` commutes with the bivector phase axis `B`. -/
theorem bivectorRotorMap_isPhaseLinear
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Module A X] [IsScalarTower ℝ A X] [ContinuousSMul A X]
    {B : A} (hB : B * B = -1) (θ : ℝ) :
    (bivectorPhaseStructure X B hB).IsPhaseLinearMap
      (bivectorRotorMap X B θ) (bivectorPhaseStructure X B hB) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, bivectorPhaseStructure,
    bivectorRotorMap, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  rw [smul_smul, smul_smul]
  congr 1
  unfold bivectorRotor
  rw [add_mul, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- Every bivector rotor action `v ↦ R(θ) • v` is Cauchy-analytic everywhere. -/
def bivectorRotorMap_cauchyAnalyticAt
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Module A X] [IsScalarTower ℝ A X] [ContinuousSMul A X]
    {B : A} (hB : B * B = -1) (θ : ℝ) (x : X) :
    CauchyAnalyticAt (bivectorPhaseStructure X B hB) (bivectorPhaseStructure X B hB)
      (fun v => bivectorRotor B θ • v) x :=
  CauchyAnalyticAt.ofContinuousLinearMap
    (bivectorPhaseStructure X B hB) (bivectorPhaseStructure X B hB)
    (bivectorRotorMap X B θ) (bivectorRotorMap_isPhaseLinear X hB θ) x

/-- General bivector-plane equivariance: a bounded `ℝ`-linear map commutes with
the bivector phase axes `B` and `B'` iff it intertwines the entire `ℝ`-linear
rotor plane `a • 1 + b • B`. -/
theorem isPhaseLinearMap_bivector_iff_plane
    {A A' X Y : Type*}
    [NormedRing A] [NormedAlgebra ℝ A]
    [NormedRing A'] [NormedAlgebra ℝ A']
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Module A X] [IsScalarTower ℝ A X] [ContinuousSMul A X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [Module A' Y] [IsScalarTower ℝ A' Y] [ContinuousSMul A' Y]
    {B : A} (hB : B * B = -1) {B' : A'} (hB' : B' * B' = -1)
    (L : X →L[ℝ] Y) :
    (bivectorPhaseStructure X B hB).IsPhaseLinearMap L (bivectorPhaseStructure Y B' hB') ↔
      ∀ (a b : ℝ) (v : X), L ((a • (1 : A) + b • B) • v) = (a • (1 : A') + b • B') • L v := by
  constructor
  · intro hL a b v
    have hB_eq : L (B • v) = B' • L v := by
      simpa [bivectorPhaseStructure] using PhaseStructure.phaseLinear_apply hL v
    rw [add_smul, smul_one_smul, smul_assoc, L.map_add, L.map_smul, L.map_smul, hB_eq]
    rw [add_smul, smul_one_smul, smul_assoc]
  · intro hplane
    ext v
    have h := hplane 0 1 v
    simpa [bivectorPhaseStructure] using h

/-- General rotor equivariance: a bounded `ℝ`-linear map commutes with the
bivector phase axes `B` and `B'` iff it intertwines all bivector rotors
`R(θ) = cos θ • 1 + sin θ • B`. -/
theorem isPhaseLinearMap_bivector_iff_rotor
    {A A' X Y : Type*}
    [NormedRing A] [NormedAlgebra ℝ A]
    [NormedRing A'] [NormedAlgebra ℝ A']
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Module A X] [IsScalarTower ℝ A X] [ContinuousSMul A X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [Module A' Y] [IsScalarTower ℝ A' Y] [ContinuousSMul A' Y]
    {B : A} (hB : B * B = -1) {B' : A'} (hB' : B' * B' = -1)
    (L : X →L[ℝ] Y) :
    (bivectorPhaseStructure X B hB).IsPhaseLinearMap L (bivectorPhaseStructure Y B' hB') ↔
      ∀ (θ : ℝ) (v : X), L (bivectorRotor B θ • v) = bivectorRotor B' θ • L v := by
  constructor
  · intro hL θ v
    exact (isPhaseLinearMap_bivector_iff_plane hB hB' L).mp hL (Real.cos θ) (Real.sin θ) v
  · intro hrot
    ext v
    have h := hrot (Real.pi / 2) v
    simpa [bivectorPhaseStructure, bivectorRotor_pi_div_two] using h

/-- Canonical real phase structure on any complex normed space, obtained as the
`A = ℂ, B = Complex.I` specialization of `bivectorPhaseStructure`. -/
noncomputable def complexSpacePhaseStructure
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] :
    PhaseStructure X :=
  bivectorPhaseStructure X (Complex.I : ℂ) Complex.I_mul_I

/-- For a continuous `ℝ`-linear map between complex normed spaces, commuting with
`complexSpacePhaseStructure` is equivalent to full `ℂ`-linearity. -/
theorem isPhaseLinearMap_iff_complex_smul
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (L : X →L[ℝ] Y) :
    (complexSpacePhaseStructure X).IsPhaseLinearMap L (complexSpacePhaseStructure Y) ↔
      ∀ (c : ℂ) (v : X), L (c • v) = c • L v := by
  constructor
  · intro hL c v
    have hplane := (isPhaseLinearMap_bivector_iff_plane
      (X := X) (Y := Y) Complex.I_mul_I Complex.I_mul_I L).mp hL c.re c.im v
    have hc : c.re • (1 : ℂ) + c.im • Complex.I = c := by
      simp [Complex.real_smul, Complex.re_add_im]
    simpa [hc] using hplane
  · intro hC
    ext v
    exact hC Complex.I v

/-- Upgrade a phase-linear `ℝ`-continuous linear map between complex normed spaces
to a `ℂ`-continuous linear map. -/
noncomputable def complexLinearMapOfPhaseLinear
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (L : X →L[ℝ] Y)
    (hL : (complexSpacePhaseStructure X).IsPhaseLinearMap L (complexSpacePhaseStructure Y)) :
    X →L[ℂ] Y where
  toFun := L
  map_add' := L.map_add
  map_smul' := (isPhaseLinearMap_iff_complex_smul L).mp hL
  cont := L.continuous

/-- A `CauchyAnalyticAt` datum between complex normed spaces yields a genuine
`ℂ`-Fréchet derivative `HasFDerivAt`. -/
theorem hasFDerivAt_complex_of_cauchyAnalyticAt
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {f : X → Y} {x : X}
    (A : CauchyAnalyticAt (complexSpacePhaseStructure X) (complexSpacePhaseStructure Y) f x) :
    HasFDerivAt f (complexLinearMapOfPhaseLinear A.deriv A.phase_linear_deriv) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa [complexLinearMapOfPhaseLinear] using hasFDerivAt_iff_isLittleO_nhds_zero.mp A.has_fderiv_at

/-- Characterization of complex Fréchet differentiability as real Fréchet
differentiability with phase-linear derivative (`CauchyAnalyticAt`). -/
theorem differentiableAt_complex_iff_cauchyAnalyticAt
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {f : X → Y} {x : X} :
    DifferentiableAt ℂ f x ↔
      Nonempty (CauchyAnalyticAt (complexSpacePhaseStructure X) (complexSpacePhaseStructure Y) f x) := by
  constructor
  · intro hf
    let dC : X →L[ℂ] Y := fderiv ℂ f x
    refine ⟨{
      deriv := dC.restrictScalars ℝ
      has_fderiv_at := hf.hasFDerivAt.restrictScalars ℝ
      phase_linear_deriv := by
        ext v
        exact dC.map_smul Complex.I v
    }⟩
  · rintro ⟨A⟩
    exact (hasFDerivAt_complex_of_cauchyAnalyticAt A).differentiableAt

/-- On any open set `U : Set ℂ`, pointwise `CauchyAnalyticAt` (real Fréchet
differentiability + phase commutation) upgrades to full Mathlib power-series
analyticity `AnalyticOnNhd ℂ f U`. -/
theorem analyticOnNhd_complex_of_cauchyAnalyticAt
    {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    {f : ℂ → Y} {U : Set ℂ} (hU : IsOpen U)
    (hCA : ∀ z ∈ U,
      Nonempty (CauchyAnalyticAt complexPhaseStructure (complexSpacePhaseStructure Y) f z)) :
    AnalyticOnNhd ℂ f U := by
  have hDiff : DifferentiableOn ℂ f U := by
    intro z hz
    rcases hCA z hz with ⟨A⟩
    have hK : complexPhaseStructure = complexSpacePhaseStructure ℂ := by
      unfold complexPhaseStructure complexSpacePhaseStructure bivectorPhaseStructure
      congr 1
    rw [hK] at A
    exact (hasFDerivAt_complex_of_cauchyAnalyticAt A).differentiableAt.differentiableWithinAt
  exact hDiff.analyticOnNhd hU

/-! ## 2B. Weyl-gauge scaled-vicinity and nonstandard Hyperreal analyticity -/

section WeylAndHyperreal

open Filter Topology

/-- Weyl-gauge scaled ball around `x` with conformal weight `exp (σ x)`. -/
def weylBall {X : Type*} [NormedAddCommGroup X]
    (σ : X → ℝ) (x : X) (ε : ℝ) : Set X :=
  {y | Real.exp (σ x) * ‖y - x‖ < ε}

/-- Weyl-gauge scaled vicinity filter around `x`. -/
def weylVicinityFilter {X : Type*} [NormedAddCommGroup X]
    (σ : X → ℝ) (x : X) : Filter X :=
  ⨅ ε ∈ Set.Ioi (0 : ℝ), Filter.principal (weylBall σ x ε)

theorem weylVicinityFilter_hasBasis {X : Type*} [NormedAddCommGroup X]
    (σ : X → ℝ) (x : X) :
    (weylVicinityFilter σ x).HasBasis (fun ε : ℝ => 0 < ε) (weylBall σ x) := by
  unfold weylVicinityFilter
  have hB : (⨅ ε ∈ Set.Ioi (0 : ℝ), Filter.principal (weylBall σ x ε)).HasBasis
      (fun ε : ℝ => ε ∈ Set.Ioi 0) (weylBall σ x) := by
    refine Filter.hasBasis_biInf_principal ?_ ⟨1, Set.mem_Ioi.mpr one_pos⟩
    intro ε₁ hε₁ ε₂ hε₂
    refine ⟨min ε₁ ε₂, Set.mem_Ioi.mpr (lt_min hε₁ hε₂), ?_⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · simp only [weylBall, Set.mem_ofPred_eq] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_left _ _)
    · simp only [weylBall, Set.mem_ofPred_eq] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_right _ _)
  simpa only [Set.mem_Ioi] using hB

/-- The Weyl-gauge scaled vicinity filter equals the standard neighborhood
filter `𝓝 x`, because the conformal factor `exp (σ x)` is strictly positive. -/
theorem weylVicinityFilter_eq_nhds {X : Type*} [NormedAddCommGroup X]
    (σ : X → ℝ) (x : X) :
    weylVicinityFilter σ x = 𝓝 x := by
  refine (weylVicinityFilter_hasBasis σ x).ext Metric.nhds_basis_ball ?_ ?_
  · intro ε hε
    refine ⟨ε / Real.exp (σ x), div_pos hε (Real.exp_pos (σ x)), ?_⟩
    intro y hy
    simp only [Metric.mem_ball, dist_eq_norm] at hy
    simp only [weylBall, Set.mem_ofPred_eq]
    calc
      Real.exp (σ x) * ‖y - x‖
          < Real.exp (σ x) * (ε / Real.exp (σ x)) :=
            mul_lt_mul_of_pos_left hy (Real.exp_pos (σ x))
      _ = ε := mul_div_cancel₀ ε (Real.exp_pos (σ x)).ne'
  · intro ε hε
    refine ⟨Real.exp (σ x) * ε, mul_pos (Real.exp_pos (σ x)) hε, ?_⟩
    intro y hy
    simp only [weylBall, Set.mem_ofPred_eq] at hy
    simp only [Metric.mem_ball, dist_eq_norm]
    exact lt_of_mul_lt_mul_left hy (Real.exp_pos (σ x)).le

/-- Changing the Weyl gauge `σ ↦ σ'` leaves the scaled vicinity filter
invariant. -/
theorem weylVicinityFilter_gauge_invariant {X : Type*} [NormedAddCommGroup X]
    (σ σ' : X → ℝ) (x : X) :
    weylVicinityFilter σ x = weylVicinityFilter σ' x := by
  rw [weylVicinityFilter_eq_nhds σ x, weylVicinityFilter_eq_nhds σ' x]

/-- Fréchet differentiability expressed against the Weyl-gauge scaled vicinity
filter. -/
theorem hasFDerivAt_iff_weylVicinity
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (σ : X → ℝ) (f : X → Y) (A : X →L[ℝ] Y) (x : X) :
    HasFDerivAt f A x ↔
      Tendsto (fun y => ‖y - x‖⁻¹ * ‖f y - f x - A (y - x)‖)
        (weylVicinityFilter σ x) (𝓝 0) := by
  rw [weylVicinityFilter_eq_nhds σ x, hasFDerivAt_iff_tendsto]

/-- Nonstandard Hyperreal derivative: if `HasDerivAt f f' x`, then for every
nonzero null sequence `h : ℕ → ℝ` representing a nonzero infinitesimal
`Hyperreal.ofSeq h`, the hyperreal difference quotient tends to `f'` and has
standard part `f'`. -/
theorem hyperreal_deriv_tendsto
    {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    {h : ℕ → ℝ} (h0 : ∀ n, h n ≠ 0) (ht : Tendsto h atTop (𝓝 0)) :
    (Hyperreal.ofSeq (fun n => (f (x + h n) - f x) / h n)).Tendsto (𝓝 f') := by
  rw [Hyperreal.tendsto_ofSeq]
  have hSlope : Tendsto (fun d : ℝ => (f (x + d) - f x) / d) (𝓝[≠] 0) (𝓝 f') := by
    simpa only [div_eq_inv_mul, smul_eq_mul] using hf.tendsto_slope_zero
  have hWithin : Tendsto h atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within h ht
      (Eventually.of_forall h0)
  exact (hSlope.comp hWithin).mono_left
    (Filter.hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)

theorem hyperreal_deriv_stdPart
    {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    {h : ℕ → ℝ} (h0 : ∀ n, h n ≠ 0) (ht : Tendsto h atTop (𝓝 0)) :
    ArchimedeanClass.stdPart
        (Hyperreal.ofSeq (fun n => (f (x + h n) - f x) / h n)) = f' :=
  Hyperreal.stdPart_of_tendsto (hyperreal_deriv_tendsto hf h0 ht)

/-- Nonstandard characterization of `HasDerivAt`: `f` has derivative `f'` at
`x` if and only if for every nonzero null sequence `h`, the hyperreal difference
quotient along `Hyperreal.ofSeq h` is infinitely close to `f'`. -/
theorem hasDerivAt_iff_hyperreal_tendsto
    {f : ℝ → ℝ} {f' x : ℝ} :
    HasDerivAt f f' x ↔
      ∀ h : ℕ → ℝ, (∀ n, h n ≠ 0) → Tendsto h atTop (𝓝 0) →
        (Hyperreal.ofSeq (fun n => (f (x + h n) - f x) / h n)).Tendsto (𝓝 f') := by
  constructor
  · intro hf h h0 ht
    exact hyperreal_deriv_tendsto hf h0 ht
  · intro hAll
    rw [hasDerivAt_iff_tendsto_slope]
    have hSlope0 :
        Tendsto (fun d : ℝ => (f (x + d) - f x) / d) (𝓝[≠] 0) (𝓝 f') := by
      refine Metric.tendsto_nhdsWithin_nhds.2 ?_
      intro ε hε
      by_contra hNo
      push Not at hNo
      have hSeq : ∀ n : ℕ, ∃ d : ℝ, d ≠ 0 ∧ ‖d‖ < ((n : ℝ) + 1)⁻¹ ∧
          ε ≤ ‖(f (x + d) - f x) / d - f'‖ := by
        intro n
        obtain ⟨d, hd0, hdDist, hdFar⟩ := hNo ((n : ℝ) + 1)⁻¹ (by positivity)
        exact ⟨d, hd0, by simpa [Real.dist_eq] using hdDist,
          by simpa [Real.dist_eq] using hdFar⟩
      choose d hd0 hdNorm hdFar using hSeq
      have hLim : Tendsto d atTop (𝓝 0) := by
        refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
        have hInv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
          simpa only [one_div] using
            (tendsto_one_div_add_atTop_nhds_zero_nat :
              Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
        exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hdNorm n).le) hInv
      have hHyp := hAll d hd0 hLim
      rw [Hyperreal.tendsto_ofSeq, Metric.tendsto_nhds] at hHyp
      have hEv := hHyp ε hε
      obtain ⟨n, hn⟩ := hEv.exists
      exact (not_lt_of_ge (hdFar n)) (by simpa [Real.dist_eq] using hn)
    have hShift : Tendsto (fun y : ℝ => y - x) (𝓝[≠] x) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hSub : ContinuousAt (fun y : ℝ => y - x) x :=
          (continuous_id.sub continuous_const).continuousAt
        simpa only [sub_self] using hSub.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact sub_ne_zero.mpr hy
    have hMap : Tendsto (slope f x) (𝓝[≠] x) (𝓝 f') := by
      have hComp := hSlope0.comp hShift
      refine hComp.congr ?_
      intro y
      simp only [Function.comp_apply, add_sub_cancel, slope_def_field]
    exact hMap

end WeylAndHyperreal

/-! ## 2C. Dikin ellipsoids, self-concordant barrier metric, and Weyl-gauge bridge -/

section DikinWeylBridge

open Filter Topology
open InfoGeometry.Parahyperkahler.AnalyticExcision
open InfoGeometry.InformationGeometry.BurgStein

/-- The Dikin ellipsoid inequality `(y - x)^2 ≤ r^2 * x^2` is equivalent to the
Burg--Stein logarithmic barrier Hessian metric bound `d2F x * (y - x)^2 ≤ r^2`. -/
theorem inDikin_iff_d2F {x y r : ℝ} (hx : 0 < x) :
    InDikin x y r ↔ d2F x * (y - x) ^ 2 ≤ r ^ 2 := by
  unfold InDikin d2F
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  rw [inv_pow]
  constructor
  · intro h
    calc
      (x ^ 2)⁻¹ * (y - x) ^ 2 ≤ (x ^ 2)⁻¹ * (r ^ 2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hx2.le)
      _ = r ^ 2 := by
        rw [mul_comm (r ^ 2) (x ^ 2), ← mul_assoc, inv_mul_cancel₀ hx2.ne', one_mul]
  · intro h
    calc
      (y - x) ^ 2 = x ^ 2 * ((x ^ 2)⁻¹ * (y - x) ^ 2) := by
        rw [← mul_assoc, mul_inv_cancel₀ hx2.ne', one_mul]
      _ ≤ x ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left h hx2.le
      _ = r ^ 2 * x ^ 2 := mul_comm _ _

/-- For `x > 0` and `r ≥ 0`, `InDikin x y r` is equivalent to the Weyl-scaled
norm bound `exp (-log x) * ‖y - x‖ ≤ r`. -/
theorem inDikin_iff_exp_neg_log_le {x y r : ℝ} (hx : 0 < x) (hr : 0 ≤ r) :
    InDikin x y r ↔ Real.exp (-Real.log x) * ‖y - x‖ ≤ r := by
  rw [Real.exp_neg, Real.exp_log hx, Real.norm_eq_abs]
  unfold InDikin
  have hx_nonneg : 0 ≤ x := hx.le
  constructor
  · intro h
    have hsq : (x⁻¹ * |y - x|) ^ 2 ≤ r ^ 2 := by
      rw [mul_pow, sq_abs, inv_pow]
      calc
        (x ^ 2)⁻¹ * (y - x) ^ 2 ≤ (x ^ 2)⁻¹ * (r ^ 2 * x ^ 2) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (sq_nonneg x))
        _ = r ^ 2 := by
          rw [mul_comm (r ^ 2) (x ^ 2), ← mul_assoc, inv_mul_cancel₀ (sq_pos_of_pos hx).ne',
            one_mul]
    exact le_of_sq_le_sq hsq hr
  · intro h
    have hmul : |y - x| ≤ r * x := by
      calc
        |y - x| = x * (x⁻¹ * |y - x|) := by
          rw [← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]
        _ ≤ x * r := mul_le_mul_of_nonneg_left h hx_nonneg
        _ = r * x := mul_comm _ _
    have hsq : |y - x| ^ 2 ≤ (r * x) ^ 2 :=
      sq_le_sq' (by linarith [abs_nonneg (y - x), mul_nonneg hr hx_nonneg]) hmul
    simpa [sq_abs, mul_pow] using hsq

/-- Every open Weyl ball under the logarithmic-barrier gauge `σ(t) = -log t` is
contained in the corresponding Dikin ellipsoid. -/
theorem mem_weylBall_logBarrier_imp_inDikin {x y r : ℝ} (hx : 0 < x)
    (hy : y ∈ weylBall (fun t => -Real.log t) x r) :
    InDikin x y r := by
  simp only [weylBall, Set.mem_ofPred_eq] at hy
  have hr : 0 ≤ r := by
    have hnn : 0 ≤ Real.exp (-Real.log x) * ‖y - x‖ :=
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    exact hnn.trans hy.le
  exact (inDikin_iff_exp_neg_log_le hx hr).2 hy.le

/-- Filter generated by Dikin ellipsoids `{y | InDikin x y r}` for `r > 0`. -/
def dikinFilter (x : ℝ) : Filter ℝ :=
  ⨅ r ∈ Set.Ioi (0 : ℝ), Filter.principal {y | InDikin x y r}

theorem dikinFilter_hasBasis (x : ℝ) :
    (dikinFilter x).HasBasis (fun r : ℝ => 0 < r) (fun r => {y | InDikin x y r}) := by
  unfold dikinFilter
  have hB : (⨅ r ∈ Set.Ioi (0 : ℝ), Filter.principal {y | InDikin x y r}).HasBasis
      (fun r : ℝ => r ∈ Set.Ioi 0) (fun r => {y | InDikin x y r}) := by
    refine Filter.hasBasis_biInf_principal ?_ ⟨1, Set.mem_Ioi.mpr one_pos⟩
    intro r₁ hr₁ r₂ hr₂
    refine ⟨min r₁ r₂, Set.mem_Ioi.mpr (lt_min hr₁ hr₂), ?_⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · simp only [Set.mem_ofPred_eq, InDikin] at hy ⊢
      have hmin : (min r₁ r₂) ^ 2 ≤ r₁ ^ 2 :=
        sq_le_sq' (by linarith [lt_min (Set.mem_Ioi.mp hr₁) (Set.mem_Ioi.mp hr₂),
          Set.mem_Ioi.mp hr₁]) (min_le_left _ _)
      exact hy.trans (mul_le_mul_of_nonneg_right hmin (sq_nonneg x))
    · simp only [Set.mem_ofPred_eq, InDikin] at hy ⊢
      have hmin : (min r₁ r₂) ^ 2 ≤ r₂ ^ 2 :=
        sq_le_sq' (by linarith [lt_min (Set.mem_Ioi.mp hr₁) (Set.mem_Ioi.mp hr₂),
          Set.mem_Ioi.mp hr₂]) (min_le_right _ _)
      exact hy.trans (mul_le_mul_of_nonneg_right hmin (sq_nonneg x))
  simpa only [Set.mem_Ioi] using hB

/-- **Dikin–Weyl Equivalence:** On the positive cone `x > 0`, the Dikin
ellipsoid filter coincides with the Weyl-gauge vicinity filter under the
logarithmic barrier weight `σ(t) = -log t` (and hence with `𝓝 x`). -/
theorem dikinFilter_eq_weylVicinityFilter {x : ℝ} (hx : 0 < x) :
    dikinFilter x = weylVicinityFilter (fun t => -Real.log t) x := by
  refine (dikinFilter_hasBasis x).ext
    (weylVicinityFilter_hasBasis (fun t => -Real.log t) x) ?_ ?_
  · intro r hr
    refine ⟨r, hr, fun y hy => ?_⟩
    exact mem_weylBall_logBarrier_imp_inDikin hx hy
  · intro r hr
    refine ⟨r / 2, half_pos hr, fun y hy => ?_⟩
    simp only [Set.mem_ofPred_eq] at hy
    have hle := (inDikin_iff_exp_neg_log_le hx (half_pos hr).le).1 hy
    simp only [weylBall, Set.mem_ofPred_eq]
    linarith

theorem dikinFilter_eq_nhds {x : ℝ} (hx : 0 < x) :
    dikinFilter x = 𝓝 x := by
  rw [dikinFilter_eq_weylVicinityFilter hx, weylVicinityFilter_eq_nhds]

/-- Affine scaling equivariance of the Dikin ellipsoid filter under `y ↦ a * y`
for `a ≠ 0`. -/
theorem dikinFilter_affine_map {x a : ℝ} (ha : a ≠ 0) :
    Filter.map (fun y => a * y) (dikinFilter x) = dikinFilter (a * x) := by
  refine ((dikinFilter_hasBasis x).map (fun y => a * y)).ext
    (dikinFilter_hasBasis (a * x)) ?_ ?_
  · intro r hr
    refine ⟨r, hr, fun y hy => ?_⟩
    refine ⟨a⁻¹ * y, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq] at hy ⊢
      have h' : InDikin (a * x) (a * (a⁻¹ * y)) r := by
        simpa [← mul_assoc, mul_inv_cancel₀ ha] using hy
      exact (dikin_affine_scaling x (a⁻¹ * y) r a ha).1 h'
    · simp [← mul_assoc, mul_inv_cancel₀ ha]
  · intro r hr
    refine ⟨r, hr, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_ofPred_eq] at hy ⊢
    exact (dikin_affine_scaling x y r a ha).2 hy

end DikinWeylBridge

/-! ## 3. Operator-valued one-forms -/

/--
An abstract operator-valued one-form.

`Point` is the geometric point space.
`Tangent` is the tangent direction type.
`Value` is the noncommutative target/readout type.
-/
abbrev OperatorOneForm
    (Point Tangent Value : Type*) :=
  Point → Tangent → Value

/--
Left Cauchy form.

In a concrete operator model this is morally

`ω_F(Z,V) = F(Z) ∘ V`.

The multiplication/order is supplied by `leftAction`.
-/
def leftCauchyForm
    {Point Tangent Value : Type*}
    (F : Point → Value)
    (leftAction : Value → Tangent → Value) :
    OperatorOneForm Point Tangent Value :=
  fun Z V => leftAction (F Z) V

/--
Right Cauchy form.

In a concrete operator model this is morally

`ω_F(Z,V) = V ∘ F(Z)`.

The multiplication/order is supplied by `rightAction`.
-/
def rightCauchyForm
    {Point Tangent Value : Type*}
    (F : Point → Value)
    (rightAction : Tangent → Value → Value) :
    OperatorOneForm Point Tangent Value :=
  fun Z V => rightAction V (F Z)

/-! ## 4. Hestenes/Stokes geometric integral backend -/

/--
A geometric integral calculus backend.

This is the Hestenes generalized Stokes/Gauss layer.

It does not pretend to construct integration from scratch. A concrete model
supplies path, boundary, volume, and geometric-derivative data.

The key law is:

`boundaryIntegral Ω ω = volumeIntegral Ω (geometricDerivative ω)`.
-/
structure GeometricIntegralBackend
    (Region Point Tangent Value : Type*)
    [AddCommGroup Value] [Module ℝ Value] where

  /-- Boundary integral of an operator-valued one-form. -/
  boundaryIntegral :
    Region → OperatorOneForm Point Tangent Value → Value

  /-- Volume integral of a value-valued density/readout. -/
  volumeIntegral :
    Region → (Point → Value) → Value

  /--
  Geometric derivative / exterior derivative / Hestenes vector derivative of
  a one-form.
  -/
  geometricDerivative :
    OperatorOneForm Point Tangent Value → Point → Value

  /-- Generalized Stokes/Gauss theorem. -/
  stokes_eq :
    ∀ Ω ω,
      boundaryIntegral Ω ω =
        volumeIntegral Ω (geometricDerivative ω)

  /--
  If a density vanishes pointwise on the relevant region, its volume integral
  vanishes.

  The precise support/membership condition is model-dependent, so this generic
  backend uses a global pointwise-zero form.
  -/
  volumeIntegral_zero_of_pointwise_zero :
    ∀ Ω f,
      (∀ p : Point, f p = 0) →
        volumeIntegral Ω f = 0

namespace GeometricIntegralBackend

variable
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]

variable (I : GeometricIntegralBackend Region Point Tangent Value)

/--
A one-form is Hestenes-closed / monogenic when its geometric derivative
vanishes.
-/
def IsClosedGeometricForm
    (ω : OperatorOneForm Point Tangent Value) : Prop :=
  ∀ p : Point, I.geometricDerivative ω p = 0

/--
Constructive Cauchy-Stokes theorem:

if the Hestenes/geometric derivative of the form vanishes, then the boundary
integral vanishes.
-/
theorem boundaryIntegral_eq_zero_of_closed
    (Ω : Region)
    (ω : OperatorOneForm Point Tangent Value)
    (hclosed : I.IsClosedGeometricForm ω) :
    I.boundaryIntegral Ω ω = 0 := by
  rw [I.stokes_eq Ω ω]
  exact I.volumeIntegral_zero_of_pointwise_zero Ω
    (I.geometricDerivative ω)
    hclosed

end GeometricIntegralBackend

/-! ## 5. Hestenes analyticity -/

/--
A concrete calibration assigning a geometric one-form to a function.

Using this avoids attaching an arbitrary closed form to an unrelated function:
the Hestenes form is definitionally `formOf F`.
-/
structure HestenesFormCalibration
    (Point Tangent Value : Type*) where
  /-- Geometric one-form associated to a value-valued function. -/
  formOf :
    (Point → Value) → OperatorOneForm Point Tangent Value

/--
Hestenes analyticity on a region.

A function is Hestenes-analytic relative to a chosen Cauchy form if the
associated geometric one-form is closed/monogenic.
-/
structure HestenesAnalyticOn
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (F : Point → Value) where

  /-- The Cauchy/geometric one-form associated to `F`. -/
  cauchyForm :
    OperatorOneForm Point Tangent Value

  /-- The form is closed/monogenic. -/
  closed_form :
    I.IsClosedGeometricForm cauchyForm

namespace HestenesAnalyticOn

variable
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {F : Point → Value}

variable (A : HestenesAnalyticOn I F)

/--
Cauchy theorem in Hestenes-Stokes form:

the integral of the analytic Cauchy form around a boundary vanishes.
-/
theorem boundaryIntegral_eq_zero
    (Ω : Region) :
    I.boundaryIntegral Ω A.cauchyForm = 0 :=
  I.boundaryIntegral_eq_zero_of_closed Ω A.cauchyForm A.closed_form

/-- Construct a Hestenes-analytic datum from a closed geometric form. -/
def ofClosedForm
    (ω : OperatorOneForm Point Tangent Value)
    (hω : I.IsClosedGeometricForm ω) :
    HestenesAnalyticOn I F where
  cauchyForm := ω
  closed_form := hω

/-- The boundary integral of a closed form vanishes. -/
theorem boundaryIntegral_eq_zero_of_closedForm
    (Ω : Region)
    (ω : OperatorOneForm Point Tangent Value)
    (hω : I.IsClosedGeometricForm ω) :
    I.boundaryIntegral Ω ω = 0 :=
  I.boundaryIntegral_eq_zero_of_closed Ω ω hω

/--
Construct a Hestenes-analytic datum from a concrete function-to-form
calibration.  This is the non-vacuous constructor: the stored form is
definitionally the calibrated form of `F`.
-/
def ofCalibration
    (C : HestenesFormCalibration Point Tangent Value)
    (hclosed : I.IsClosedGeometricForm (C.formOf F)) :
    HestenesAnalyticOn I F where
  cauchyForm := C.formOf F
  closed_form := hclosed

@[simp]
theorem ofCalibration_cauchyForm
    (C : HestenesFormCalibration Point Tangent Value)
    (hclosed : I.IsClosedGeometricForm (C.formOf F)) :
    (ofCalibration (I := I) (F := F) C hclosed).cauchyForm = C.formOf F :=
  by
    rfl

end HestenesAnalyticOn

/-! ## 6A. Constructive Cauchy/Hestenes compatibility -/

/--
A constructive Cauchy/Hestenes compatibility backend.

This replaces a vague compatibility proposition by explicit data:

* `cauchyFormOf L` builds the geometric Cauchy form from a real derivative `L`;
* `obstructionOf L` is the Hestenes/geometric obstruction associated to `L`;
* phase-linearity of `L` forces that obstruction to vanish;
* the geometric derivative of the Cauchy form is exactly that obstruction.

Thus Cauchy phase-linearity constructively implies Hestenes closedness.
-/
structure CauchyHestenesCompatibility
    {X Y Region Point Tangent Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [AddCommGroup Value] [Module ℝ Value]
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (I : GeometricIntegralBackend Region Point Tangent Value) where

  /-- Geometric Cauchy form associated to a real derivative. -/
  cauchyFormOf :
    (X →L[ℝ] Y) → OperatorOneForm Point Tangent Value

  /--
  Cauchy/Hestenes obstruction associated to a derivative.

  Morally this is the geometric derivative of the Cauchy form, equivalent to
  the Cauchy-Riemann obstruction.
  -/
  obstructionOf :
    (X →L[ℝ] Y) → Point → Value

  /-- If the derivative is phase-linear, the obstruction vanishes. -/
  obstruction_zero_of_phaseLinear :
    ∀ L : X →L[ℝ] Y,
      L.comp Kdom.K = Ktar.K.comp L →
        ∀ p : Point, obstructionOf L p = 0

  /-- The geometric derivative of the Cauchy form is exactly the obstruction. -/
  geometricDerivative_eq_obstruction :
    ∀ L : X →L[ℝ] Y,
      ∀ p : Point,
        I.geometricDerivative (cauchyFormOf L) p =
          obstructionOf L p

namespace CauchyHestenesCompatibility

variable
    {X Y Region Point Tangent Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [AddCommGroup Value] [Module ℝ Value]
    {Kdom : PhaseStructure X}
    {Ktar : PhaseStructure Y}
    {I : GeometricIntegralBackend Region Point Tangent Value}

variable (B : CauchyHestenesCompatibility Kdom Ktar I)

/-- A phase-linear derivative produces a closed Hestenes Cauchy form. -/
theorem closed_form_of_phaseLinear
    (L : X →L[ℝ] Y)
    (hL : L.comp Kdom.K = Ktar.K.comp L) :
    I.IsClosedGeometricForm (B.cauchyFormOf L) := by
  intro p
  rw [B.geometricDerivative_eq_obstruction L p]
  exact B.obstruction_zero_of_phaseLinear L hL p

/-- A Cauchy-analytic derivative produces a closed Hestenes form. -/
theorem closed_form_of_cauchyAnalyticAt
    {F : X → Y}
    {x : X}
    (A : CauchyAnalyticAt Kdom Ktar F x) :
    I.IsClosedGeometricForm (B.cauchyFormOf A.deriv) :=
  B.closed_form_of_phaseLinear A.deriv A.phase_linear_deriv

/--
Construct the Hestenes analytic datum from a Cauchy analytic datum and a
compatibility backend.
-/
def hestenesAnalyticOfCauchy
    {F : X → Y}
    {Fgeo : Point → Value}
    {x : X}
    (A : CauchyAnalyticAt Kdom Ktar F x) :
    HestenesAnalyticOn I Fgeo where
  cauchyForm := B.cauchyFormOf A.deriv
  closed_form := B.closed_form_of_cauchyAnalyticAt A

/--
Constructive bilingual Cauchy theorem.

If a function is Cauchy-analytic and the model supplies a Cauchy/Hestenes
compatibility backend, then the corresponding Hestenes boundary integral
vanishes.
-/
theorem boundaryIntegral_eq_zero_of_cauchyAnalyticAt
    {F : X → Y}
    {x : X}
    (A : CauchyAnalyticAt Kdom Ktar F x)
    (Ω : Region) :
    I.boundaryIntegral Ω (B.cauchyFormOf A.deriv) = 0 :=
  I.boundaryIntegral_eq_zero_of_closed
    Ω
    (B.cauchyFormOf A.deriv)
    (B.closed_form_of_cauchyAnalyticAt A)

/--
A phase-linear derivative gives a zero boundary integral for its Cauchy form.
-/
theorem boundaryIntegral_eq_zero_of_phaseLinear
    (L : X →L[ℝ] Y)
    (hL : L.comp Kdom.K = Ktar.K.comp L)
    (Ω : Region) :
    I.boundaryIntegral Ω (B.cauchyFormOf L) = 0 :=
  I.boundaryIntegral_eq_zero_of_closed
    Ω
    (B.cauchyFormOf L)
    (B.closed_form_of_phaseLinear L hL)

end CauchyHestenesCompatibility

/-! ## 6B. Bilingual analyticity, processed -/

/--
Bilingual analyticity.

This packages:

* Cauchy side: phase-linear real derivative;
* constructive Cauchy/Hestenes compatibility.

The Hestenes closed form is now derived from the Cauchy side. It is not stored
as an independent shadow.
-/
structure BilingualAnalyticAt
    {X Y Region Point Tangent Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [AddCommGroup Value] [Module ℝ Value]
    (Kdom : PhaseStructure X)
    (Ktar : PhaseStructure Y)
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (F : X → Y)
    (Fgeo : Point → Value)
    (x : X) where

  /-- Cauchy/phase derivative analyticity. -/
  cauchy :
    CauchyAnalyticAt Kdom Ktar F x

  /--
  Constructive compatibility between the Cauchy derivative and the Hestenes
  geometric form.
  -/
  compatibility :
    CauchyHestenesCompatibility Kdom Ktar I

namespace BilingualAnalyticAt

variable
    {X Y Region Point Tangent Value : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [AddCommGroup Value] [Module ℝ Value]
    {Kdom : PhaseStructure X}
    {Ktar : PhaseStructure Y}
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {F : X → Y}
    {Fgeo : Point → Value}
    {x : X}

variable (A : BilingualAnalyticAt Kdom Ktar I F Fgeo x)

/--
Cauchy-Riemann law from the bilingual analytic datum.
-/
theorem cauchyRiemann_apply
    (v : X) :
    A.cauchy.deriv (Kdom.K v) =
      Ktar.K (A.cauchy.deriv v) :=
  A.cauchy.cauchyRiemann_apply v

/--
The associated Hestenes analytic datum is constructed from the Cauchy side.
-/
def hestenes :
    HestenesAnalyticOn I Fgeo :=
  A.compatibility.hestenesAnalyticOfCauchy A.cauchy

/-- The Hestenes form is closed by construction from the Cauchy derivative. -/
theorem closed_form_from_cauchy :
    I.IsClosedGeometricForm
      (A.compatibility.cauchyFormOf A.cauchy.deriv) :=
  A.compatibility.closed_form_of_cauchyAnalyticAt A.cauchy

/-- The Hestenes boundary theorem follows constructively from the Cauchy side. -/
theorem boundaryIntegral_eq_zero_from_cauchy
    (Ω : Region) :
    I.boundaryIntegral Ω
      (A.compatibility.cauchyFormOf A.cauchy.deriv) = 0 :=
  A.compatibility.boundaryIntegral_eq_zero_of_cauchyAnalyticAt A.cauchy Ω

/--
Hestenes boundary Cauchy theorem from the bilingual analytic datum.

This is the short-form API theorem for downstream modules.  The form itself is
the one constructed from the Cauchy derivative by the compatibility backend.
-/
theorem boundaryIntegral_eq_zero
    (Ω : Region) :
    I.boundaryIntegral Ω A.hestenes.cauchyForm = 0 :=
  A.hestenes.boundaryIntegral_eq_zero Ω

end BilingualAnalyticAt

/-! ## 7. Operator target specializations -/

/--
A noncommutative operator analyticity side.

Left and right forms are distinct in a noncommutative algebra. A model may
choose one side or require both.
-/
inductive OperatorAnalyticSide where
  | left
  | right
  | twoSided
deriving DecidableEq, Repr

/--
A noncommutative Cauchy-form calibration.

Left and right Cauchy forms differ in a noncommutative target. They agree on
values that are central for the chosen left/right actions.
-/
structure NoncommutativeCauchyFormCalibration
    (Point Tangent Value : Type*) where

  /-- Left action, morally `F(Z) ∘ dZ`. -/
  leftAction :
    Value → Tangent → Value

  /-- Right action, morally `dZ ∘ F(Z)`. -/
  rightAction :
    Tangent → Value → Value

  /-- Values for which left and right action agree. -/
  IsCentralValue :
    Value → Prop

  /-- Constructive left/right compatibility on central values. -/
  left_right_compatibility :
    ∀ (a : Value) (v : Tangent),
      IsCentralValue a →
        leftAction a v = rightAction v a

namespace NoncommutativeCauchyFormCalibration

variable {Point Tangent Value : Type*}
variable (C : NoncommutativeCauchyFormCalibration Point Tangent Value)

/-- Left operator Cauchy form of `F`. -/
def leftForm
    (F : Point → Value) :
    OperatorOneForm Point Tangent Value :=
  leftCauchyForm F C.leftAction

/-- Right operator Cauchy form of `F`. -/
def rightForm
    (F : Point → Value) :
    OperatorOneForm Point Tangent Value :=
  rightCauchyForm F C.rightAction

/-- If `F` takes central values, the left and right Cauchy forms coincide. -/
theorem leftForm_eq_rightForm_of_central
    (F : Point → Value)
    (hF : ∀ Z : Point, C.IsCentralValue (F Z)) :
    C.leftForm F = C.rightForm F := by
  apply funext
  intro Z
  apply funext
  intro V
  dsimp [leftForm, rightForm, leftCauchyForm, rightCauchyForm]
  exact C.left_right_compatibility (F Z) V (hF Z)

end NoncommutativeCauchyFormCalibration

/-! ## 7A. Multiplicative ring-valued Cauchy calibration -/

/--
Concrete multiplicative Cauchy-form calibration for ring-valued forms.

Left action is multiplication on the left.
Right action is multiplication on the right.
Centrality is literal commutation with every tangent value.
-/
def multiplicativeCauchyFormCalibration
    (Point Value : Type*)
    [Ring Value] :
    NoncommutativeCauchyFormCalibration Point Value Value where
  leftAction := fun a v => a * v
  rightAction := fun v a => v * a
  IsCentralValue := fun a => ∀ v : Value, a * v = v * a
  left_right_compatibility := by
    intro a v ha
    exact ha v

namespace multiplicativeCauchyFormCalibration

variable {Point Value : Type*}
variable [Ring Value]

/-- Centrality predicate for the multiplicative calibration. -/
theorem isCentralValue_iff
    (a : Value) :
    (multiplicativeCauchyFormCalibration Point Value).IsCentralValue a ↔
      ∀ v : Value, a * v = v * a :=
  Iff.rfl

/-- If `Value` is a complex algebra, scalar values are central. -/
theorem algebraMap_isCentralValue
    [Algebra ℂ Value]
    (ζ : ℂ) :
    (multiplicativeCauchyFormCalibration Point Value).IsCentralValue
      (algebraMap ℂ Value ζ) := by
  intro v
  exact Algebra.commutes ζ v

/--
For scalar-valued functions embedded into a complex algebra, left and right
multiplicative Cauchy forms coincide.
-/
theorem leftForm_eq_rightForm_of_scalarValued
    [Algebra ℂ Value]
    (F : Point → ℂ) :
    (multiplicativeCauchyFormCalibration Point Value).leftForm
        (fun Z : Point => algebraMap ℂ Value (F Z))
      =
    (multiplicativeCauchyFormCalibration Point Value).rightForm
        (fun Z : Point => algebraMap ℂ Value (F Z)) := by
  apply
    (multiplicativeCauchyFormCalibration Point Value).leftForm_eq_rightForm_of_central
  intro Z
  exact algebraMap_isCentralValue (Point := Point) (Value := Value) (F Z)

end multiplicativeCauchyFormCalibration

/-! ## 8. Noncommutative Cauchy kernel -/

/--
A noncommutative Cauchy kernel datum.

In classical complex analysis the Cauchy kernel is `(ζ - z)⁻¹`.

In an operator algebra, the difference element and inverse must be supplied
with explicit left and right inverse laws.

The predicate `IsAdmissible ζ z` excludes singular pairs, such as `ζ = z`
in the scalar complex model.
-/
structure NoncommutativeCauchyKernel
    (Param Point Value : Type*) [Ring Value] where

  /-- Pairs where the kernel exists. -/
  IsAdmissible :
    Param → Point → Prop

  /-- Difference element, morally `ζ - z`. -/
  diff :
    Param → Point → Value

  /-- Kernel element, morally `(ζ - z)⁻¹`. -/
  kernel :
    Param → Point → Value

  /-- Left inverse law: `(ζ-z) * (ζ-z)⁻¹ = 1`. -/
  left_inverse :
    ∀ ζ z,
      IsAdmissible ζ z →
        diff ζ z * kernel ζ z = 1

  /-- Right inverse law: `(ζ-z)⁻¹ * (ζ-z) = 1`. -/
  right_inverse :
    ∀ ζ z,
      IsAdmissible ζ z →
        kernel ζ z * diff ζ z = 1

namespace NoncommutativeCauchyKernel

variable {Param Point Value : Type*} [Ring Value]
variable (K : NoncommutativeCauchyKernel Param Point Value)

/-- The difference times the kernel is `1` on admissible pairs. -/
theorem diff_mul_kernel
    (ζ : Param)
    (z : Point)
    (h : K.IsAdmissible ζ z) :
    K.diff ζ z * K.kernel ζ z = 1 :=
  K.left_inverse ζ z h

/-- The kernel times the difference is `1` on admissible pairs. -/
theorem kernel_mul_diff
    (ζ : Param)
    (z : Point)
    (h : K.IsAdmissible ζ z) :
    K.kernel ζ z * K.diff ζ z = 1 :=
  K.right_inverse ζ z h

/-- A kernel with two-sided inverse laws is unique on admissible pairs. -/
theorem kernel_unique
    (ζ : Param)
    (z : Point)
    (hadm : K.IsAdmissible ζ z)
    (hInv : Value)
    (h_right : hInv * K.diff ζ z = 1) :
    hInv = K.kernel ζ z := by
  calc
    hInv = hInv * 1 := by
      rw [mul_one]
    _ = hInv * (K.diff ζ z * K.kernel ζ z) := by
      rw [K.left_inverse ζ z hadm]
    _ = (hInv * K.diff ζ z) * K.kernel ζ z := by
      rw [mul_assoc]
    _ = 1 * K.kernel ζ z := by
      rw [h_right]
    _ = K.kernel ζ z := by
      rw [one_mul]

end NoncommutativeCauchyKernel

/-! ## 9. Scalar complex Cauchy kernel -/

/--
The scalar complex Cauchy kernel.

Admissibility excludes the diagonal `ζ = z`, equivalently `ζ - z ≠ 0`.
-/
def scalarComplexCauchyKernel :
    NoncommutativeCauchyKernel ℂ ℂ ℂ where
  IsAdmissible := fun ζ z => ζ - z ≠ 0
  diff := fun ζ z => ζ - z
  kernel := fun ζ z => (ζ - z)⁻¹
  left_inverse := by
    intro ζ z h
    exact mul_inv_cancel₀ h
  right_inverse := by
    intro ζ z h
    exact inv_mul_cancel₀ h

namespace scalarComplexCauchyKernel

/-- Admissibility for the scalar complex kernel is exactly nonvanishing of `ζ - z`. -/
theorem admissible_iff
    (ζ z : ℂ) :
    scalarComplexCauchyKernel.IsAdmissible ζ z ↔ ζ - z ≠ 0 :=
  Iff.rfl

/-- Scalar complex difference times Cauchy kernel is `1`. -/
theorem diff_mul_kernel
    (ζ z : ℂ)
    (h : ζ - z ≠ 0) :
    scalarComplexCauchyKernel.diff ζ z *
      scalarComplexCauchyKernel.kernel ζ z = 1 :=
  scalarComplexCauchyKernel.left_inverse ζ z h

/-- Scalar complex Cauchy kernel times difference is `1`. -/
theorem kernel_mul_diff
    (ζ z : ℂ)
    (h : ζ - z ≠ 0) :
    scalarComplexCauchyKernel.kernel ζ z *
      scalarComplexCauchyKernel.diff ζ z = 1 :=
  scalarComplexCauchyKernel.right_inverse ζ z h

/-- Uniqueness of the scalar complex Cauchy kernel. -/
theorem kernel_unique
    (ζ z : ℂ)
    (h : ζ - z ≠ 0)
    (u : ℂ)
    (h_right : u * (ζ - z) = 1) :
    u = scalarComplexCauchyKernel.kernel ζ z :=
  NoncommutativeCauchyKernel.kernel_unique
    scalarComplexCauchyKernel ζ z h u h_right

end scalarComplexCauchyKernel

/-! ## 11. General supplied operator resolvent kernel -/

/--
Ring-level phase linearity for an operator target.

`T` is phase-linear relative to `K` when it commutes with `K`.
-/
def PhaseLinearValue
    {Value : Type*} [Mul Value]
    (K T : Value) : Prop :=
  T * K = K * T

/-- A scalar element in a complex algebra. -/
def scalarOperator
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    (ζ : ℂ) : Value :=
  algebraMap ℂ Value ζ

/-- The operator resolvent difference: `ζ • 1 - Z`. -/
def operatorResolventDiff
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    (ζ : ℂ)
    (Z : Value) : Value :=
  scalarOperator ζ - Z

/-- Scalar operators commute with all elements of a complex algebra. -/
theorem scalarOperator_commutes
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    (ζ : ℂ)
    (Z : Value) :
    scalarOperator ζ * Z = Z * scalarOperator ζ := by
  exact Algebra.commutes ζ Z

/-- Scalar operators are phase-linear relative to every phase axis. -/
theorem scalarOperator_phaseLinear
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    (K : Value)
    (ζ : ℂ) :
    PhaseLinearValue K (scalarOperator ζ) := by
  dsimp [PhaseLinearValue]
  exact scalarOperator_commutes ζ K

/-- If `Z` commutes with `K`, then `ζ•1 - Z` also commutes with `K`. -/
theorem operatorResolventDiff_phaseLinear
    {Value : Type*} [Ring Value] [Algebra ℂ Value]
    {K Z : Value}
    (ζ : ℂ)
    (hZ : PhaseLinearValue K Z) :
    PhaseLinearValue K (operatorResolventDiff ζ Z) := by
  dsimp [PhaseLinearValue, operatorResolventDiff]
  calc
    (scalarOperator ζ - Z) * K
        = scalarOperator ζ * K - Z * K := by
          rw [sub_mul]
    _ = K * scalarOperator ζ - K * Z := by
          rw [scalarOperator_commutes ζ K, hZ]
    _ = K * (scalarOperator ζ - Z) := by
          rw [mul_sub]

/--
If `B` is invertible with inverse `Binv`, and `X` commutes with `B`, then
`X` commutes with `Binv`.
-/
theorem inverse_commutes_of_commutes
    {Value : Type*} [Monoid Value]
    {X B Binv : Value}
    (h_right : B * Binv = 1)
    (h_left : Binv * B = 1)
    (hXB : X * B = B * X) :
    X * Binv = Binv * X := by
  calc
    X * Binv
        = 1 * (X * Binv) := by
          rw [one_mul]
    _ = (Binv * B) * (X * Binv) := by
          rw [h_left]
    _ = Binv * (B * X) * Binv := by
          simp only [mul_assoc]
    _ = Binv * (X * B) * Binv := by
          rw [hXB.symm]
    _ = (Binv * X) * (B * Binv) := by
          simp only [mul_assoc]
    _ = (Binv * X) * 1 := by
          rw [h_right]
    _ = Binv * X := by
          rw [mul_one]

/-- If a phase-linear element has a two-sided inverse, its inverse is phase-linear. -/
theorem inverse_phaseLinear_of_twoSided_inverse
    {Value : Type*} [Ring Value]
    {K B Binv : Value}
    (hB : PhaseLinearValue K B)
    (h_right : B * Binv = 1)
    (h_left : Binv * B = 1) :
    PhaseLinearValue K Binv := by
  dsimp [PhaseLinearValue] at hB ⊢
  have h :
      K * Binv = Binv * K :=
    inverse_commutes_of_commutes
      (X := K)
      (B := B)
      (Binv := Binv)
      h_right
      h_left
      hB.symm
  exact h.symm

/--
A supplied operator resolvent kernel.

This is the general noncommutative operator version of `(ζ•1 - Z)⁻¹`.

The inverse is not postulated as a vague law. It is carried by explicit
left/right inverse equations.
-/
structure SuppliedOperatorResolventKernel
    (Value : Type*) [Ring Value] [Algebra ℂ Value] where

  /-- Admissible spectral parameter/operator pairs. -/
  IsAdmissible :
    ℂ → Value → Prop

  /-- The supplied resolvent inverse. -/
  kernel :
    ℂ → Value → Value

  /-- Left inverse law. -/
  left_inverse :
    ∀ ζ Z,
      IsAdmissible ζ Z →
        operatorResolventDiff ζ Z * kernel ζ Z = 1

  /-- Right inverse law. -/
  right_inverse :
    ∀ ζ Z,
      IsAdmissible ζ Z →
        kernel ζ Z * operatorResolventDiff ζ Z = 1

namespace SuppliedOperatorResolventKernel

variable {Value : Type*} [Ring Value] [Algebra ℂ Value]
variable (R : SuppliedOperatorResolventKernel Value)

/-- Convert a supplied operator resolvent into a noncommutative Cauchy kernel. -/
def toCauchyKernel :
    NoncommutativeCauchyKernel ℂ Value Value where
  IsAdmissible := R.IsAdmissible
  diff := operatorResolventDiff
  kernel := R.kernel
  left_inverse := R.left_inverse
  right_inverse := R.right_inverse

/-- Difference times resolvent kernel is identity on admissible pairs. -/
theorem diff_mul_kernel
    (ζ : ℂ)
    (Z : Value)
    (h : R.IsAdmissible ζ Z) :
    operatorResolventDiff ζ Z * R.kernel ζ Z = 1 :=
  R.left_inverse ζ Z h

/-- Resolvent kernel times difference is identity on admissible pairs. -/
theorem kernel_mul_diff
    (ζ : ℂ)
    (Z : Value)
    (h : R.IsAdmissible ζ Z) :
    R.kernel ζ Z * operatorResolventDiff ζ Z = 1 :=
  R.right_inverse ζ Z h

/-- Uniqueness of the supplied operator resolvent kernel. -/
theorem kernel_unique
    (ζ : ℂ)
    (Z : Value)
    (h : R.IsAdmissible ζ Z)
    (U : Value)
    (h_right : U * operatorResolventDiff ζ Z = 1) :
    U = R.kernel ζ Z :=
  NoncommutativeCauchyKernel.kernel_unique
    R.toCauchyKernel ζ Z h U h_right

/--
If `Z` is phase-linear relative to `K`, then its supplied resolvent kernel is
also phase-linear.
-/
theorem kernel_phaseLinear_of_phaseLinear
    {K Z : Value}
    (ζ : ℂ)
    (h : R.IsAdmissible ζ Z)
    (hZ : PhaseLinearValue K Z) :
    PhaseLinearValue K (R.kernel ζ Z) := by
  have hdiff :
      PhaseLinearValue K (operatorResolventDiff ζ Z) :=
    operatorResolventDiff_phaseLinear ζ hZ
  exact
    inverse_phaseLinear_of_twoSided_inverse
      hdiff
      (R.left_inverse ζ Z h)
      (R.right_inverse ζ Z h)

end SuppliedOperatorResolventKernel

end InfoGeometry.Geometry.BilingualAnalyticity
