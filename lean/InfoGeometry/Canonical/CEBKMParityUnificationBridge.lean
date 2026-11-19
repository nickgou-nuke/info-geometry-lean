/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
import InfoGeometry.Canonical.ErlangenOperator2Bridge
import InfoGeometry.Canonical.OperatorFrechetForms
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.Thermo.OnsagerDifferentialFormsBridge
import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint
import InfoGeometry.Canonical.FiniteMatrixGibbsParity

/-!
# Concrete Parity Reciprocity and Arbitrary-Degree Fréchet–CE–BKM–Onsager Unification

This module extends `CEBKMOnsagerSystem`, `CEBKMOnsagerGibbsIntegration`,
`CEBKMOnsagerGibbsNOperatorFamily`, and `ErlangenOperator2Bridge` with genuine
concrete `TimeReversal` involutions and `ParityOnsagerSystem` instances:

1. **Unconditional `star` parity on BKM covariance** (`bkmRealBilinForm_star`,
   `expectationReal_star`, `centeredStatistic_star`, `centeredBKMRealCovariance_star`)
   and its induced `starDerivationTimeReversal` on `CEBKMOnsagerSystem` (where
   `ceCurvatureBKMProbeForm` is time-odd precisely for self-adjoint probes `Q`).
2. **Unified `ℝ`-algebra `*`-automorphism parity** (`τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n`
   with `τ² = id`, `τ D.rho = D.rho`, and `(finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re`),
   encompassing both `ℂ`-linear inner conjugation `Ad_Γ` and `ℂ`-antilinear entrywise
   complex conjugation `conjStarAlgEquiv`, with explicit `n = 2` noncommutative
   non-vanishing witnesses.
3. **Arbitrary-degree unification** across `ParityOnsagerFormPairing`,
   `DerivationExteriorCalculus` (`ceExteriorDerivative`, `ceWedge`, `ceCurvature`,
   `ceCurvature_eq`), and `OperatorFrechetForms` (`SmoothOpMap`, `frechetFormToCEForm`,
   `frechetExtDerivReal`, `logPartitionOneForm`, and
   `frechetExtDeriv_logPartition_bkmHessian_alignment`).
-/

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 800000

namespace InfoGeometry.Canonical.CEBKMParityUnificationBridge

open Matrix
open scoped Interval
open SouriauOnsagerBKM
open SouriauOnsagerBKM.FaithfulDensityOperator
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem
open InfoGeometry.Thermo.OnsagerFormsBridge
open InfoGeometry.Algebra
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Canonical.ErlangenOperator2 (ErlangenOperatorDatum HasJReciprocity)
open InfoGeometry.Canonical (gibbsNOperatorFamilyErlangenDatum
  gibbsNOperatorFamilyErlangenDatum_reciprocity_and_hessian)
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsRpowNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.BKMScalarGaugeQuotient
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.Canonical.CEBKMOnsagerSystem
open InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration
open InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Physics.KleinBottleSewingExact

private def carrierEnd {n : ℕ} (x : Carrier n) : Module.End ℝ (GibbsOperator n) :=
  (show NonAssocDerivation.derivations ℝ (GibbsOperator n) from x).1

/-! ## Section 1: Unconditional `star` Parity on BKM Covariance -/

section BKMStarParity

/-- Pointwise `star`-reflection identity for the Kubo–Mori integrand on
`FiniteOperatorAlgebra n`. -/
theorem kuboMoriIntegrand_star {n : ℕ}
    (D : FaithfulDensityOperator n) (A B : FiniteOperatorAlgebra n) (s : ℝ) :
    D.kuboMoriIntegrand (star A) (star B) s =
      star (D.kuboMoriIntegrand A B (1 - s)) := by
  unfold FaithfulDensityOperator.kuboMoriIntegrand
  rw [← finiteOperatorTrace_star]
  simp only [StarMul.star_mul, star_star, D.star_rpow, sub_sub_cancel]
  calc
    finiteOperatorTrace (D.rpow s * A * D.rpow (1 - s) * star B) =
        finiteOperatorTrace ((D.rpow s * A * D.rpow (1 - s)) * star B) := by
          simp only [mul_assoc]
    _ = finiteOperatorTrace (star B * (D.rpow s * A * D.rpow (1 - s))) :=
          finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace (star B * (D.rpow s * (A * D.rpow (1 - s)))) := by
          simp only [mul_assoc]

/-- Complex Kubo–Mori pairing intertwines `star` with complex conjugation. -/
theorem kuboMoriPairing_star {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) :
    D.kuboMoriPairing (star A) (star B) = star (D.kuboMoriPairing A B) := by
  unfold FaithfulDensityOperator.kuboMoriPairing
  have hInt : IntervalIntegrable (D.kuboMoriIntegrand A B) MeasureTheory.volume 0 1 :=
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow A B hpow).intervalIntegrable 0 1
  have h1 :
      (∫ s in (0 : ℝ)..1, D.kuboMoriIntegrand (star A) (star B) s) =
        ∫ s in (0 : ℝ)..1, star (D.kuboMoriIntegrand A B (1 - s)) := by
    apply intervalIntegral.integral_congr
    intro s _
    exact kuboMoriIntegrand_star D A B s
  have h2 :
      (∫ s in (0 : ℝ)..1, star (D.kuboMoriIntegrand A B (1 - s))) =
        ∫ s in (0 : ℝ)..1, star (D.kuboMoriIntegrand A B s) := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left
        (f := fun s : ℝ => star (D.kuboMoriIntegrand A B s)) (a := (0 : ℝ)) (b := 1) 1)
  have h3 :
      (∫ s in (0 : ℝ)..1, star (D.kuboMoriIntegrand A B s)) =
        star (∫ s in (0 : ℝ)..1, D.kuboMoriIntegrand A B s) :=
    ContinuousLinearMap.intervalIntegral_comp_comm
      Complex.conjCLE.toContinuousLinearMap hInt
  exact h1.trans (h2.trans h3)

/-- Unconditional `star`-invariance of the real BKM bilinear form on `FiniteOperatorAlgebra n`. -/
theorem bkmRealBilinForm_star {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) :
    D.bkmRealBilinForm hpow (star A) (star B) = D.bkmRealBilinForm hpow A B := by
  rw [D.bkmRealBilinForm_apply, D.bkmRealBilinForm_apply, kuboMoriPairing_star D hpow A B]
  exact Complex.conj_re _

/-- Unconditional `star`-invariance of the real expectation value in `D`. -/
theorem expectationReal_star {n : ℕ}
    (D : FaithfulDensityOperator n) (A : GibbsOperator n) :
    expectationReal D (star A) = expectationReal D A := by
  unfold expectationReal
  have hrho : star D.rho = D.rho := D.strictlyPositive.isSelfAdjoint.star_eq
  have htr : finiteOperatorTrace (D.rho * star A) =
      star (finiteOperatorTrace (D.rho * A)) := by
    calc
      finiteOperatorTrace (D.rho * star A) =
          finiteOperatorTrace (star (A * D.rho)) := by
            rw [star_mul, hrho]
      _ = star (finiteOperatorTrace (A * D.rho)) := finiteOperatorTrace_star _
      _ = star (finiteOperatorTrace (D.rho * A)) := by
            rw [finiteOperatorTrace_mul_comm A D.rho]
  rw [htr]
  exact Complex.conj_re _

/-- Centering commutes with `star`. -/
theorem centeredStatistic_star {n : ℕ}
    (D : FaithfulDensityOperator n) (A : GibbsOperator n) :
    centeredStatistic D (star A) = star (centeredStatistic D A) := by
  unfold centeredStatistic
  rw [expectationReal_star D A]
  have hsub :
      star (A - expectationReal D A • (1 : GibbsOperator n)) =
        star A - star (expectationReal D A • (1 : GibbsOperator n)) :=
    star_sub A (expectationReal D A • (1 : GibbsOperator n))
  have hsmul :
      star (expectationReal D A • (1 : GibbsOperator n)) =
        expectationReal D A • (1 : GibbsOperator n) := by
    rw [real_smul_eq_complex_smul, star_smul, star_one, Complex.star_def, Complex.conj_ofReal,
      ← real_smul_eq_complex_smul]
  rw [hsub, hsmul]

/-- Centering is `ℝ`-homogeneous. -/
theorem centeredStatistic_real_smul {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (r : ℝ) (A : GibbsOperator n) :
    centeredStatistic D (r • A) = r • centeredStatistic D A := by
  rw [← centeringLinearMap_apply D hpow, map_smul, centeringLinearMap_apply]

/-- Unconditional `star`-invariance of the centered BKM real covariance. -/
theorem centeredBKMRealCovariance_star {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : GibbsOperator n) :
    centeredBKMRealCovariance D hpow (star A) (star B) =
      centeredBKMRealCovariance D hpow A B := by
  unfold centeredBKMRealCovariance
  rw [centeredStatistic_star D A, centeredStatistic_star D B]
  exact bkmRealBilinForm_star D hpow _ _

end BKMStarParity

/-! ## Section 2: `star` Time Reversal on `GibbsOperator n`, `Carrier n`, and `CEBKMOnsagerSystem` -/

section CEStarParity

/-- Adjoint involution `A ↦ star A` as a `TimeReversal` on `GibbsOperator n`. -/
def starTimeReversal (n : ℕ) : TimeReversal (GibbsOperator n) where
  op := (finiteOperatorStarRealCLM n).toLinearMap
  involutive := star_star

@[simp] theorem starTimeReversal_apply {n : ℕ} (A : GibbsOperator n) :
    (starTimeReversal n).op A = star A :=
  rfl

/-- Conjugate a real derivation by `star`: `carrierEnd (starDerivation x) u = star (carrierEnd x (star u))`.
This preserves the Leibniz rule because `star` is an anti-automorphism reversing both factors. -/
def starDerivation {n : ℕ} (x : Carrier n) : Carrier n :=
  show NonAssocDerivation.derivations ℝ (GibbsOperator n) from
    ⟨(finiteOperatorStarRealCLM n).toLinearMap.comp
        ((carrierEnd x).comp (finiteOperatorStarRealCLM n).toLinearMap),
      fun u v => by
        change star (carrierEnd x (star (u * v))) =
          star (carrierEnd x (star u)) * v + u * star (carrierEnd x (star v))
        have hleib : carrierEnd x (star v * star u) =
            carrierEnd x (star v) * star u + star v * carrierEnd x (star u) :=
          NonAssocDerivation.derivations_leibniz ℝ (GibbsOperator n)
            (show NonAssocDerivation.derivations ℝ (GibbsOperator n) from x) (star v) (star u)
        have hop_add : ∀ A B : GibbsOperator n, star (A + B) = star A + star B :=
          (finiteOperatorStarRealCLM n).map_add
        rw [StarMul.star_mul, hleib, hop_add,
          StarMul.star_mul, StarMul.star_mul, star_star, star_star, add_comm]⟩

@[simp] theorem starDerivation_apply {n : ℕ} (x : Carrier n) (u : GibbsOperator n) :
    carrierEnd (starDerivation x) u = star (carrierEnd x (star u)) :=
  rfl

theorem starDerivation_involutive {n : ℕ} (x : Carrier n) :
    starDerivation (starDerivation x) = x := by
  have hext : ∀ {a b : Carrier n}, (∀ u : GibbsOperator n, carrierEnd a u = carrierEnd b u) → a = b :=
    fun h => Subtype.ext (LinearMap.ext h)
  apply hext
  intro u
  rw [starDerivation_apply, starDerivation_apply, star_star, star_star]

theorem starDerivation_add {n : ℕ} (x y : Carrier n) :
    starDerivation (x + y) = starDerivation x + starDerivation y := by
  have hext : ∀ {a b : Carrier n}, (∀ u : GibbsOperator n, carrierEnd a u = carrierEnd b u) → a = b :=
    fun h => Subtype.ext (LinearMap.ext h)
  apply hext
  intro u
  change star (carrierEnd (x + y) (star u)) =
    star (carrierEnd x (star u)) + star (carrierEnd y (star u))
  have hxy : carrierEnd (x + y) (star u) = carrierEnd x (star u) + carrierEnd y (star u) := rfl
  have hop_add : ∀ A B : GibbsOperator n, star (A + B) = star A + star B :=
    (finiteOperatorStarRealCLM n).map_add
  rw [hxy, hop_add]

theorem starDerivation_smul {n : ℕ} (r : ℝ) (x : Carrier n) :
    starDerivation (r • x) = r • starDerivation x := by
  have hext : ∀ {a b : Carrier n}, (∀ u : GibbsOperator n, carrierEnd a u = carrierEnd b u) → a = b :=
    fun h => Subtype.ext (LinearMap.ext h)
  apply hext
  intro u
  change star (carrierEnd (r • x) (star u)) = r • star (carrierEnd x (star u))
  have hrx : carrierEnd (r • x) (star u) = r • carrierEnd x (star u) := rfl
  rw [hrx, ← finiteOperatorStarRealCLM_apply (n := n), map_smul, finiteOperatorStarRealCLM_apply]

/-- `star`-conjugation of derivations as a `TimeReversal` on `Carrier n`. -/
def starDerivationTimeReversal (n : ℕ) : TimeReversal (Carrier n) where
  op :=
    { toFun := starDerivation
      map_add' := starDerivation_add
      map_smul' := starDerivation_smul }
  involutive := starDerivation_involutive

@[simp] theorem starDerivationTimeReversal_apply {n : ℕ} (x : Carrier n) :
    (starDerivationTimeReversal n).op x = starDerivation x :=
  rfl

/-- On any definite-`star`-parity observable (`star a = ε • a` with `ε = ±1`),
the centered CE-BKM dissipative form is `starDerivationTimeReversal`-even. -/
theorem centeredCEBKMForm_starDerivation_even_of_parity {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : star a = ε • a)
    (x y : Carrier n) :
    centeredCEBKMForm D hpow a ((starDerivationTimeReversal n).op x)
        ((starDerivationTimeReversal n).op y) =
      centeredCEBKMForm D hpow a x y := by
  have hform : ∀ z : Carrier n,
      finiteCEOperatorForm n a ((starDerivationTimeReversal n).op z) =
        ε • star (finiteCEOperatorForm n a z) := fun z => by
    change carrierEnd ((starDerivationTimeReversal n).op z) a = ε • star (carrierEnd z a)
    rw [starDerivationTimeReversal_apply, starDerivation_apply, ha, (carrierEnd z).map_smul,
      ← finiteOperatorStarRealCLM_apply (n := n), map_smul, finiteOperatorStarRealCLM_apply]
  rw [centeredCEBKMForm_apply, centeredCEBKMForm_apply, hform x, hform y]
  unfold centeredBKMRealCovariance
  rw [centeredStatistic_real_smul D hpow ε (star (finiteCEOperatorForm n a x)),
    centeredStatistic_real_smul D hpow ε (star (finiteCEOperatorForm n a y))]
  rw [(D.bkmRealBilinForm hpow).map_smul, LinearMap.smul_apply,
    (D.bkmRealBilinForm hpow _).map_smul]
  rw [centeredStatistic_star, centeredStatistic_star, bkmRealBilinForm_star D hpow]
  rcases hε with rfl | rfl <;> simp

/-- For any self-adjoint observable `a`, `centeredCEBKMForm` is `starDerivationTimeReversal`-even. -/
theorem centeredCEBKMForm_starDerivation_even {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a : GibbsOperator n) (ha : IsSelfAdjoint a) (x y : Carrier n) :
    centeredCEBKMForm D hpow a ((starDerivationTimeReversal n).op x)
        ((starDerivationTimeReversal n).op y) =
      centeredCEBKMForm D hpow a x y :=
  centeredCEBKMForm_starDerivation_even_of_parity D hpow a
    (Or.inl rfl) (by simpa [IsSelfAdjoint] using ha.star_eq) x y

/-- Exact `star`-reversal sign law for the CE curvature BKM probe form:
because `star` is an anti-automorphism, `[star X, star Y] = - star [X, Y]`, so
`ceCurvatureBKMProbeForm` reflects the probe `Q` to `- star Q`. -/
theorem ceCurvatureBKMProbeForm_starDerivation_eq {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a Q : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : star a = ε • a)
    (x y : Carrier n) :
    ceCurvatureBKMProbeForm D hpow a Q
        ((starDerivationTimeReversal n).op x) ((starDerivationTimeReversal n).op y) =
      - ceCurvatureBKMProbeForm D hpow a (star Q) x y := by
  rw [ceCurvatureBKMProbeForm_apply, ceCurvatureBKMProbeForm_apply]
  let K := realDerivationsLane (GibbsOperator n)
  let Γ := exteriorDerivativeZero K a
  have hcurv : ∀ u v : Carrier n,
      connectionCurvature K Γ u v = carrierEnd u a * carrierEnd v a - carrierEnd v a * carrierEnd u a :=
    fun u v => by
      rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero K a, zero_add]
      rfl
  rw [hcurv ((starDerivationTimeReversal n).op x) ((starDerivationTimeReversal n).op y),
    hcurv x y]
  have hform : ∀ z : Carrier n,
      carrierEnd ((starDerivationTimeReversal n).op z) a = ε • star (carrierEnd z a) := fun z => by
    rw [starDerivationTimeReversal_apply, starDerivation_apply, ha, (carrierEnd z).map_smul,
      ← finiteOperatorStarRealCLM_apply (n := n), map_smul, finiteOperatorStarRealCLM_apply]
  rw [hform x, hform y]
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hcomm :
      (ε • star (carrierEnd x a)) * (ε • star (carrierEnd y a)) -
          (ε • star (carrierEnd y a)) * (ε • star (carrierEnd x a)) =
        -star (carrierEnd x a * carrierEnd y a - carrierEnd y a * carrierEnd x a) := by
    have hrsmul : ∀ (r : ℝ) (X Y : GibbsOperator n), (r • X) * Y = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul]
    have hmulr : ∀ (r : ℝ) (X Y : GibbsOperator n), X * (r • Y) = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, mul_smul_comm, ← real_smul_eq_complex_smul]
    have hop_sub : ∀ A B : GibbsOperator n, star (A - B) = star A - star B :=
      (finiteOperatorStarRealCLM n).map_sub
    rw [hrsmul, hmulr, hrsmul, hmulr, smul_smul, smul_smul, hε2, one_smul, one_smul,
      hop_sub, StarMul.star_mul, StarMul.star_mul, neg_sub]
  rw [hcomm]
  have hb0 := bkmRealBilinForm_star D hpow
    (carrierEnd x a * carrierEnd y a - carrierEnd y a * carrierEnd x a) (star Q)
  rw [star_star] at hb0
  calc
    D.bkmRealBilinForm hpow (-star (carrierEnd x a * carrierEnd y a - carrierEnd y a * carrierEnd x a)) Q =
        -D.bkmRealBilinForm hpow
          (star (carrierEnd x a * carrierEnd y a - carrierEnd y a * carrierEnd x a)) Q := by
          rw [LinearMap.map_neg, LinearMap.neg_apply]
    _ = -D.bkmRealBilinForm hpow
          (carrierEnd x a * carrierEnd y a - carrierEnd y a * carrierEnd x a) (star Q) := by
          rw [hb0]

/-- For a self-adjoint probe `Q` (`star Q = Q`), `ceCurvatureBKMProbeForm` is
`starDerivationTimeReversal`-odd. -/
theorem ceCurvatureBKMProbeForm_starDerivation_odd_of_parity {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a Q : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : star a = ε • a)
    (hQ : IsSelfAdjoint Q) (x y : Carrier n) :
    ceCurvatureBKMProbeForm D hpow a Q
        ((starDerivationTimeReversal n).op x) ((starDerivationTimeReversal n).op y) =
      - ceCurvatureBKMProbeForm D hpow a Q x y := by
  rw [ceCurvatureBKMProbeForm_starDerivation_eq D hpow a Q hε ha x y, hQ.star_eq]

/-- For self-adjoint `a` and `Q`, `ceCurvatureBKMProbeForm` is `starDerivationTimeReversal`-odd. -/
theorem ceCurvatureBKMProbeForm_starDerivation_odd {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a Q : GibbsOperator n) (ha : IsSelfAdjoint a) (hQ : IsSelfAdjoint Q)
    (x y : Carrier n) :
    ceCurvatureBKMProbeForm D hpow a Q
        ((starDerivationTimeReversal n).op x) ((starDerivationTimeReversal n).op y) =
      - ceCurvatureBKMProbeForm D hpow a Q x y :=
  ceCurvatureBKMProbeForm_starDerivation_odd_of_parity D hpow a Q
    (Or.inl rfl) (by simpa [IsSelfAdjoint] using ha.star_eq) hQ x y

/-- Concrete `ParityOnsagerSystem (Carrier n)` extending `finiteCEOnsagerSystem`
under `starDerivationTimeReversal` for definite-parity observable `a` and self-adjoint probe `Q`. -/
def finiteCEParityOnsagerSystem_of_parity {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a Q : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : star a = ε • a)
    (hQ : IsSelfAdjoint Q) :
    ParityOnsagerSystem (Carrier n) where
  toOnsagerCasimirSystem := finiteCEOnsagerSystem D hpow a Q
  T := starDerivationTimeReversal n
  dissipative_T_even := centeredCEBKMForm_starDerivation_even_of_parity D hpow a hε ha
  reversible_T_odd := ceCurvatureBKMProbeForm_starDerivation_odd_of_parity D hpow a Q hε ha hQ

/-- Concrete `ParityOnsagerSystem (Carrier n)` extending `finiteCEOnsagerSystem`
under `starDerivationTimeReversal` for self-adjoint `a` and `Q`. -/
def finiteCEParityOnsagerSystem {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a Q : GibbsOperator n) (ha : IsSelfAdjoint a) (hQ : IsSelfAdjoint Q) :
    ParityOnsagerSystem (Carrier n) :=
  finiteCEParityOnsagerSystem_of_parity D hpow a Q
    (Or.inl rfl) (by simpa [IsSelfAdjoint] using ha.star_eq) hQ

end CEStarParity

/-! ## Section 3: Unified `ℝ`-Algebra `*`-Automorphism Parity Layer -/

section AutParity

/-- An `ℝ`-algebra `*`-automorphism fixing `D.rho` fixes every real CFC power `D.rpow s`. -/
theorem aut_rpow {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n)
    (D : FaithfulDensityOperator n) (hτ_rho : τ D.rho = D.rho) (s : ℝ) :
    τ (D.rpow s) = D.rpow s := by
  unfold FaithfulDensityOperator.rpow
  change τ (D.rho ^ s) = D.rho ^ s
  rw [CFC.rpow_eq_cfc_real D.strictlyPositive.nonneg]
  have hcont_τ : Continuous τ :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := τ, map_add' := map_add τ, map_smul' := map_smul τ } :
        GibbsOperator n →ₗ[ℝ] GibbsOperator n)
  have hcont_f : ContinuousOn (fun x : ℝ => x ^ s) (spectrum ℝ D.rho) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x s
      (Or.inl (ne_of_gt (IsStrictlyPositive.spectrum_pos D.strictlyPositive hx)))).continuousWithinAt
  rw [StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) τ (fun x : ℝ => x ^ s) D.rho
    hcont_f hcont_τ D.strictlyPositive.isSelfAdjoint
    (D.strictlyPositive.isSelfAdjoint.map τ), hτ_rho]

/-- Any `ℝ`-algebra `*`-automorphism preserving `D.rho` and the real part of the trace
preserves `D.bkmRealBilinForm`. This covers both `ℂ`-linear `Ad_Γ` and `ℂ`-antilinear
entrywise conjugation. -/
theorem bkmRealBilinForm_aut {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (A B : GibbsOperator n) :
    D.bkmRealBilinForm hpow (τ A) (τ B) = D.bkmRealBilinForm hpow A B := by
  rw [D.bkmRealBilinForm_apply, D.bkmRealBilinForm_apply]
  have hInt1 : IntervalIntegrable (D.kuboMoriIntegrand (τ A) (τ B)) MeasureTheory.volume 0 1 :=
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow (τ A) (τ B) hpow).intervalIntegrable 0 1
  have hInt2 : IntervalIntegrable (D.kuboMoriIntegrand A B) MeasureTheory.volume 0 1 :=
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow A B hpow).intervalIntegrable 0 1
  have hre1 :
      (D.kuboMoriPairing (τ A) (τ B)).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand (τ A) (τ B) s).re := by
    unfold FaithfulDensityOperator.kuboMoriPairing
    symm
    exact ContinuousLinearMap.intervalIntegral_comp_comm (RCLike.reCLM : ℂ →L[ℝ] ℝ) hInt1
  have hre2 :
      (D.kuboMoriPairing A B).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand A B s).re := by
    unfold FaithfulDensityOperator.kuboMoriPairing
    symm
    exact ContinuousLinearMap.intervalIntegral_comp_comm (RCLike.reCLM : ℂ →L[ℝ] ℝ) hInt2
  rw [hre1, hre2]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [FaithfulDensityOperator.kuboMoriIntegrand]
  conv_lhs =>
    rw [← aut_rpow τ D hτ_rho s, ← aut_rpow τ D hτ_rho (1 - s), ← map_star τ A,
      ← map_mul τ, ← map_mul τ, ← map_mul τ]
  exact hτ_tr _

/-- Real expectation invariance under a `D.rho`- and real-trace-preserving `*`-automorphism. -/
theorem expectationReal_aut {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n)
    (D : FaithfulDensityOperator n)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (A : GibbsOperator n) :
    expectationReal D (τ A) = expectationReal D A := by
  unfold expectationReal
  conv_lhs => rw [← hτ_rho, ← map_mul τ]
  exact hτ_tr (D.rho * A)

/-- Centering commutes with any `D.rho`- and real-trace-preserving `*`-automorphism. -/
theorem centeredStatistic_aut {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n)
    (D : FaithfulDensityOperator n)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (A : GibbsOperator n) :
    centeredStatistic D (τ A) = τ (centeredStatistic D A) := by
  unfold centeredStatistic
  rw [expectationReal_aut τ D hτ_rho hτ_tr A, map_sub, map_smul, map_one]

/-- Centered BKM real covariance invariance under a `D.rho`- and real-trace-preserving
`*`-automorphism. -/
theorem centeredBKMRealCovariance_aut {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (A B : GibbsOperator n) :
    centeredBKMRealCovariance D hpow (τ A) (τ B) =
      centeredBKMRealCovariance D hpow A B := by
  unfold centeredBKMRealCovariance
  rw [centeredStatistic_aut τ D hτ_rho hτ_tr A, centeredStatistic_aut τ D hτ_rho hτ_tr B]
  exact bkmRealBilinForm_aut τ D hpow hτ_rho hτ_tr _ _

/-- View an involutive `ℝ`-algebra `*`-automorphism as a `TimeReversal (GibbsOperator n)`. -/
def autTimeReversal {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n)
    (hτ_inv : ∀ X, τ (τ X) = X) :
    TimeReversal (GibbsOperator n) where
  op :=
    { toFun := τ
      map_add' := map_add τ
      map_smul' := map_smul τ }
  involutive := hτ_inv

@[simp] theorem autTimeReversal_apply {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (X : GibbsOperator n) :
    (autTimeReversal τ hτ_inv).op X = τ X :=
  rfl

/-- Push a derivation forward by an `ℝ`-algebra `*`-automorphism:
`carrierEnd (autDerivation τ x) u = τ (carrierEnd x (τ.symm u))`. -/
def autDerivation {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (x : Carrier n) : Carrier n :=
  let τLM : GibbsOperator n →ₗ[ℝ] GibbsOperator n :=
    { toFun := τ, map_add' := map_add τ, map_smul' := map_smul τ }
  let τSymmLM : GibbsOperator n →ₗ[ℝ] GibbsOperator n :=
    { toFun := τ.symm, map_add' := map_add τ.symm, map_smul' := map_smul τ.symm }
  show NonAssocDerivation.derivations ℝ (GibbsOperator n) from
    ⟨τLM.comp ((carrierEnd x).comp τSymmLM),
      fun u v => by
        change τ (carrierEnd x (τ.symm (u * v))) =
          τ (carrierEnd x (τ.symm u)) * v + u * τ (carrierEnd x (τ.symm v))
        have hleib : carrierEnd x (τ.symm u * τ.symm v) =
            carrierEnd x (τ.symm u) * τ.symm v + τ.symm u * carrierEnd x (τ.symm v) :=
          NonAssocDerivation.derivations_leibniz ℝ (GibbsOperator n)
            (show NonAssocDerivation.derivations ℝ (GibbsOperator n) from x) (τ.symm u) (τ.symm v)
        rw [map_mul τ.symm, hleib, map_add, map_mul, map_mul]
        simp⟩

@[simp] theorem autDerivation_apply {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (x : Carrier n) (u : GibbsOperator n) :
    carrierEnd (autDerivation τ x) u = τ (carrierEnd x (τ.symm u)) :=
  rfl

theorem autDerivation_involutive {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n)
    (hτ_inv : ∀ X, τ (τ X) = X) (x : Carrier n) :
    autDerivation τ (autDerivation τ x) = x := by
  have hext : ∀ {a b : Carrier n}, (∀ u : GibbsOperator n, carrierEnd a u = carrierEnd b u) → a = b :=
    fun h => Subtype.ext (LinearMap.ext h)
  apply hext
  intro u
  have hsymm : ∀ w, τ.symm w = τ w := fun w =>
    τ.injective ((τ.apply_symm_apply w).trans (hτ_inv w).symm)
  rw [autDerivation_apply, autDerivation_apply, hsymm, hsymm, hτ_inv, hτ_inv]

theorem autDerivation_add {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (x y : Carrier n) :
    autDerivation τ (x + y) = autDerivation τ x + autDerivation τ y := by
  have hext : ∀ {a b : Carrier n}, (∀ u : GibbsOperator n, carrierEnd a u = carrierEnd b u) → a = b :=
    fun h => Subtype.ext (LinearMap.ext h)
  apply hext
  intro u
  change τ (carrierEnd (x + y) (τ.symm u)) =
    τ (carrierEnd x (τ.symm u)) + τ (carrierEnd y (τ.symm u))
  have hxy : carrierEnd (x + y) (τ.symm u) =
      carrierEnd x (τ.symm u) + carrierEnd y (τ.symm u) := rfl
  rw [hxy, map_add]

theorem autDerivation_smul {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (r : ℝ) (x : Carrier n) :
    autDerivation τ (r • x) = r • autDerivation τ x := by
  have hext : ∀ {a b : Carrier n}, (∀ u : GibbsOperator n, carrierEnd a u = carrierEnd b u) → a = b :=
    fun h => Subtype.ext (LinearMap.ext h)
  apply hext
  intro u
  change τ (carrierEnd (r • x) (τ.symm u)) = r • τ (carrierEnd x (τ.symm u))
  have hrx : carrierEnd (r • x) (τ.symm u) = r • carrierEnd x (τ.symm u) := rfl
  rw [hrx, map_smul]

/-- Involutive `*`-automorphism conjugation on derivations as a `TimeReversal (Carrier n)`. -/
def autDerivationTimeReversal {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n)
    (hτ_inv : ∀ X, τ (τ X) = X) :
    TimeReversal (Carrier n) where
  op :=
    { toFun := autDerivation τ
      map_add' := autDerivation_add τ
      map_smul' := autDerivation_smul τ }
  involutive := autDerivation_involutive τ hτ_inv

@[simp] theorem autDerivationTimeReversal_apply {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (x : Carrier n) :
    (autDerivationTimeReversal τ hτ_inv).op x = autDerivation τ x :=
  rfl

/-- Centered CE-BKM dissipative form is `autDerivationTimeReversal`-even for any
definite-parity observable `τ a = ε • a` (`ε = ±1`). -/
theorem centeredCEBKMForm_autDerivation_even_of_parity {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : τ a = ε • a)
    (x y : Carrier n) :
    centeredCEBKMForm D hpow a ((autDerivationTimeReversal τ hτ_inv).op x)
        ((autDerivationTimeReversal τ hτ_inv).op y) =
      centeredCEBKMForm D hpow a x y := by
  have hsymm : τ.symm a = ε • a :=
    τ.injective (by
      calc
        τ (τ.symm a) = a := τ.apply_symm_apply a
        _ = τ (τ a) := (hτ_inv a).symm
        _ = τ (ε • a) := by rw [ha])
  have hform : ∀ z : Carrier n,
      finiteCEOperatorForm n a ((autDerivationTimeReversal τ hτ_inv).op z) =
        ε • τ (finiteCEOperatorForm n a z) := fun z => by
    change carrierEnd ((autDerivationTimeReversal τ hτ_inv).op z) a = ε • τ (carrierEnd z a)
    rw [autDerivationTimeReversal_apply, autDerivation_apply, hsymm, (carrierEnd z).map_smul, map_smul]
  rw [centeredCEBKMForm_apply, centeredCEBKMForm_apply, hform x, hform y]
  unfold centeredBKMRealCovariance
  rw [centeredStatistic_real_smul D hpow ε (τ (finiteCEOperatorForm n a x)),
    centeredStatistic_real_smul D hpow ε (τ (finiteCEOperatorForm n a y))]
  rw [(D.bkmRealBilinForm hpow).map_smul, LinearMap.smul_apply,
    (D.bkmRealBilinForm hpow _).map_smul]
  rw [centeredStatistic_aut τ D hτ_rho hτ_tr, centeredStatistic_aut τ D hτ_rho hτ_tr,
    bkmRealBilinForm_aut τ D hpow hτ_rho hτ_tr]
  rcases hε with rfl | rfl <;> simp

/-- For `τ a = a`, `centeredCEBKMForm` is `autDerivationTimeReversal`-even. -/
theorem centeredCEBKMForm_autDerivation_even {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a : GibbsOperator n) (ha : τ a = a) (x y : Carrier n) :
    centeredCEBKMForm D hpow a ((autDerivationTimeReversal τ hτ_inv).op x)
        ((autDerivationTimeReversal τ hτ_inv).op y) =
      centeredCEBKMForm D hpow a x y :=
  centeredCEBKMForm_autDerivation_even_of_parity τ hτ_inv D hpow hτ_rho hτ_tr a
    (Or.inl rfl) (by simpa using ha) x y

/-- Exact `*`-automorphism transport law for `ceCurvatureBKMProbeForm`:
since `τ` is multiplicative, `[τ X, τ Y] = τ [X, Y]`, so `ceCurvatureBKMProbeForm`
transports the probe `Q` to `τ Q` (flipping sign precisely when `τ Q = -Q`). -/
theorem ceCurvatureBKMProbeForm_autDerivation_eq {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a Q : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : τ a = ε • a)
    (x y : Carrier n) :
    ceCurvatureBKMProbeForm D hpow a Q
        ((autDerivationTimeReversal τ hτ_inv).op x) ((autDerivationTimeReversal τ hτ_inv).op y) =
      ceCurvatureBKMProbeForm D hpow a (τ Q) x y := by
  rw [ceCurvatureBKMProbeForm_apply, ceCurvatureBKMProbeForm_apply]
  let K := realDerivationsLane (GibbsOperator n)
  let Γ := exteriorDerivativeZero K a
  have hcurv : ∀ u v : Carrier n,
      connectionCurvature K Γ u v = carrierEnd u a * carrierEnd v a - carrierEnd v a * carrierEnd u a :=
    fun u v => by
      rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero K a, zero_add]
      rfl
  rw [hcurv ((autDerivationTimeReversal τ hτ_inv).op x) ((autDerivationTimeReversal τ hτ_inv).op y),
    hcurv x y]
  have hsymm : τ.symm a = ε • a :=
    τ.injective (by
      calc
        τ (τ.symm a) = a := τ.apply_symm_apply a
        _ = τ (τ a) := (hτ_inv a).symm
        _ = τ (ε • a) := by rw [ha])
  have hform : ∀ z : Carrier n,
      carrierEnd ((autDerivationTimeReversal τ hτ_inv).op z) a = ε • τ (carrierEnd z a) := fun z => by
    rw [autDerivationTimeReversal_apply, autDerivation_apply, hsymm, (carrierEnd z).map_smul, map_smul]
  rw [hform x, hform y]
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hcomm :
      (ε • τ (carrierEnd x a)) * (ε • τ (carrierEnd y a)) -
          (ε • τ (carrierEnd y a)) * (ε • τ (carrierEnd x a)) =
        τ (carrierEnd x a * carrierEnd y a - carrierEnd y a * carrierEnd x a) := by
    have hrsmul : ∀ (r : ℝ) (X Y : GibbsOperator n), (r • X) * Y = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul]
    have hmulr : ∀ (r : ℝ) (X Y : GibbsOperator n), X * (r • Y) = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, mul_smul_comm, ← real_smul_eq_complex_smul]
    rw [hrsmul, hmulr, hrsmul, hmulr, smul_smul, smul_smul, hε2, one_smul, one_smul,
      ← map_mul τ, ← map_mul τ, ← map_sub τ]
  rw [hcomm]
  calc
    D.bkmRealBilinForm hpow (τ (carrierEnd x a * carrierEnd y a - carrierEnd y a * carrierEnd x a)) Q =
        D.bkmRealBilinForm hpow
          (τ (carrierEnd x a * carrierEnd y a - carrierEnd y a * carrierEnd x a)) (τ (τ Q)) := by
          rw [hτ_inv Q]
    _ = D.bkmRealBilinForm hpow (carrierEnd x a * carrierEnd y a - carrierEnd y a * carrierEnd x a) (τ Q) :=
          bkmRealBilinForm_aut τ D hpow hτ_rho hτ_tr _ _

/-- For a `τ`-odd probe (`τ Q = -Q`), `ceCurvatureBKMProbeForm` is
`autDerivationTimeReversal`-odd. -/
theorem ceCurvatureBKMProbeForm_autDerivation_odd_of_parity {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a Q : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : τ a = ε • a)
    (hQ : τ Q = -Q) (x y : Carrier n) :
    ceCurvatureBKMProbeForm D hpow a Q
        ((autDerivationTimeReversal τ hτ_inv).op x) ((autDerivationTimeReversal τ hτ_inv).op y) =
      - ceCurvatureBKMProbeForm D hpow a Q x y := by
  rw [ceCurvatureBKMProbeForm_autDerivation_eq τ hτ_inv D hpow hτ_rho hτ_tr a Q hε ha x y, hQ]
  rw [ceCurvatureBKMProbeForm_apply, ceCurvatureBKMProbeForm_apply, map_neg]

/-- For `τ a = a` and `τ Q = -Q`, `ceCurvatureBKMProbeForm` is `autDerivationTimeReversal`-odd. -/
theorem ceCurvatureBKMProbeForm_autDerivation_odd {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a Q : GibbsOperator n) (ha : τ a = a) (hQ : τ Q = -Q) (x y : Carrier n) :
    ceCurvatureBKMProbeForm D hpow a Q
        ((autDerivationTimeReversal τ hτ_inv).op x) ((autDerivationTimeReversal τ hτ_inv).op y) =
      - ceCurvatureBKMProbeForm D hpow a Q x y :=
  ceCurvatureBKMProbeForm_autDerivation_odd_of_parity τ hτ_inv D hpow hτ_rho hτ_tr a Q
    (Or.inl rfl) (by simpa using ha) hQ x y

/-- `ParityOnsagerSystem (Carrier n)` extending `finiteCEOnsagerSystem` under an
involutive `ℝ`-algebra `*`-automorphism `τ` with `τ a = ε • a` and `τ Q = -Q`. -/
def finiteCEParityOnsagerSystemOfAut_of_parity {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a Q : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : τ a = ε • a)
    (hQ : τ Q = -Q) :
    ParityOnsagerSystem (Carrier n) where
  toOnsagerCasimirSystem := finiteCEOnsagerSystem D hpow a Q
  T := autDerivationTimeReversal τ hτ_inv
  dissipative_T_even :=
    centeredCEBKMForm_autDerivation_even_of_parity τ hτ_inv D hpow hτ_rho hτ_tr a hε ha
  reversible_T_odd :=
    ceCurvatureBKMProbeForm_autDerivation_odd_of_parity τ hτ_inv D hpow hτ_rho hτ_tr a Q hε ha hQ

/-- `ParityOnsagerSystem (Carrier n)` extending `finiteCEOnsagerSystem` under an
involutive `ℝ`-algebra `*`-automorphism `τ` with `τ a = a` and `τ Q = -Q`. -/
def finiteCEParityOnsagerSystemOfAut {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a Q : GibbsOperator n) (ha : τ a = a) (hQ : τ Q = -Q) :
    ParityOnsagerSystem (Carrier n) :=
  finiteCEParityOnsagerSystemOfAut_of_parity τ hτ_inv D hpow hτ_rho hτ_tr a Q
    (Or.inl rfl) (by simpa using ha) hQ

end AutParity

/-! ## Section 4: Concrete `*`-Automorphisms (`Ad_Γ` & Entrywise Conjugation) and `n = 2` Witnesses -/

section ConcreteAutomorphismsAndWitnesses

/-- Inner conjugation `Ad_Γ(X) = Γ * X * Γ` by a self-adjoint involution `Γ * Γ = 1`
as an `ℝ`-algebra `*`-automorphism of `GibbsOperator n`. -/
def adGammaStarAlgEquiv {n : ℕ} (Γ : GibbsOperator n)
    (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1) :
    GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n where
  toFun X := Γ * X * Γ
  invFun X := Γ * X * Γ
  left_inv X := by
    calc
      Γ * (Γ * X * Γ) * Γ = (Γ * Γ) * X * (Γ * Γ) := by noncomm_ring
      _ = X := by rw [hΓ_sq, one_mul, mul_one]
  right_inv X := by
    calc
      Γ * (Γ * X * Γ) * Γ = (Γ * Γ) * X * (Γ * Γ) := by noncomm_ring
      _ = X := by rw [hΓ_sq, one_mul, mul_one]
  map_mul' X Y := by
    calc
      Γ * (X * Y) * Γ = Γ * X * 1 * Y * Γ := by noncomm_ring
      _ = Γ * X * (Γ * Γ) * Y * Γ := by rw [hΓ_sq]
      _ = (Γ * X * Γ) * (Γ * Y * Γ) := by noncomm_ring
  map_add' X Y := by noncomm_ring
  map_smul' r X := by
    simp only [real_smul_eq_complex_smul, mul_smul_comm, smul_mul_assoc]
  map_star' X := by
    simp only [star_mul, hΓ_sa.star_eq, mul_assoc]

@[simp] theorem adGammaStarAlgEquiv_apply {n : ℕ} (Γ : GibbsOperator n)
    (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1) (X : GibbsOperator n) :
    adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq X = Γ * X * Γ :=
  rfl

theorem adGammaStarAlgEquiv_involutive {n : ℕ} (Γ : GibbsOperator n)
    (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1) (X : GibbsOperator n) :
    adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq (adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq X) = X :=
  (adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq).left_inv X

theorem adGammaStarAlgEquiv_trace {n : ℕ} (Γ : GibbsOperator n)
    (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1) (X : GibbsOperator n) :
    finiteOperatorTrace (adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq X) = finiteOperatorTrace X := by
  change finiteOperatorTrace (Γ * X * Γ) = finiteOperatorTrace X
  rw [finiteOperatorTrace_mul_comm (Γ * X) Γ, ← mul_assoc, hΓ_sq, one_mul]

theorem adGammaStarAlgEquiv_trace_re {n : ℕ} (Γ : GibbsOperator n)
    (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1) (X : GibbsOperator n) :
    (finiteOperatorTrace (adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq X)).re =
      (finiteOperatorTrace X).re :=
  congrArg Complex.re (adGammaStarAlgEquiv_trace Γ hΓ_sa hΓ_sq X)

theorem adGammaStarAlgEquiv_rho_fixed {n : ℕ} (Γ : GibbsOperator n)
    (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1)
    (D : FaithfulDensityOperator n) (hcomm : Commute D.rho Γ) :
    adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq D.rho = D.rho := by
  change Γ * D.rho * Γ = D.rho
  rw [← hcomm.eq, mul_assoc, hΓ_sq, mul_one]

theorem adGammaStarAlgEquiv_gibbs_commute {n : ℕ}
    (H Γ : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hcomm : Commute H Γ) :
    Commute (faithfulGibbsDensity H hH hZ).rho Γ := by
  rw [faithfulGibbsDensity_rho_eq_normalizedGibbsCFC H hH hZ]
  exact hcomm.cfc_real (normalizedScalarGibbsWeight (gibbsPartitionReal H))

theorem adGammaStarAlgEquiv_gibbs_fixed {n : ℕ}
    (H Γ : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1) (hcomm : Commute H Γ) :
    adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq (faithfulGibbsDensity H hH hZ).rho =
      (faithfulGibbsDensity H hH hZ).rho :=
  adGammaStarAlgEquiv_rho_fixed Γ hΓ_sa hΓ_sq (faithfulGibbsDensity H hH hZ)
    (adGammaStarAlgEquiv_gibbs_commute H Γ hH hZ hcomm)

theorem adGammaStarAlgEquiv_odd_of_anticomm {n : ℕ}
    (Γ Q : GibbsOperator n) (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1)
    (hanti : Q * Γ = -(Γ * Q)) :
    adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq Q = -Q := by
  change Γ * Q * Γ = -Q
  calc
    Γ * Q * Γ = Γ * (Q * Γ) := by rw [mul_assoc]
    _ = Γ * (-(Γ * Q)) := by rw [hanti]
    _ = -(Γ * (Γ * Q)) := mul_neg Γ (Γ * Q)
    _ = -((Γ * Γ) * Q) := by rw [mul_assoc]
    _ = -Q := by rw [hΓ_sq, one_mul]

/-- Entrywise complex conjugation on `GibbsOperator n` relative to the canonical
coordinate basis `ketBasis (Fin n)`. -/
def conjOpFun {n : ℕ} (X : GibbsOperator n) : GibbsOperator n :=
  matrixOp ((matrixOfOp X).map (starRingEnd ℂ))

theorem conjOpFun_involutive {n : ℕ} (X : GibbsOperator n) :
    conjOpFun (conjOpFun X) = X := by
  unfold conjOpFun
  rw [matrixOfOp_matrixOp]
  have h : ((matrixOfOp X).map (starRingEnd ℂ)).map (starRingEnd ℂ) = matrixOfOp X := by
    ext i j
    simp
  rw [h, matrixOp_matrixOfOp]

theorem conjOpFun_add {n : ℕ} (X Y : GibbsOperator n) :
    conjOpFun (X + Y) = conjOpFun X + conjOpFun Y := by
  unfold conjOpFun
  apply matrixOfOp_injective
  change matrixOfOp (matrixOp ((matrixOfOp (X + Y)).map (starRingEnd ℂ))) =
    matrixOfOp (matrixOp ((matrixOfOp X).map (starRingEnd ℂ)) +
      matrixOp ((matrixOfOp Y).map (starRingEnd ℂ)))
  rw [matrixOfOp_add, matrixOfOp_matrixOp, matrixOfOp_add, matrixOfOp_matrixOp,
    matrixOfOp_matrixOp]
  ext i j
  simp

theorem conjOpFun_mul {n : ℕ} (X Y : GibbsOperator n) :
    conjOpFun (X * Y) = conjOpFun X * conjOpFun Y := by
  unfold conjOpFun
  apply matrixOfOp_injective
  change matrixOfOp (matrixOp ((matrixOfOp (X.comp Y)).map (starRingEnd ℂ))) =
    matrixOfOp ((matrixOp ((matrixOfOp X).map (starRingEnd ℂ))).comp
      (matrixOp ((matrixOfOp Y).map (starRingEnd ℂ))))
  rw [matrixOfOp_comp, matrixOfOp_comp, matrixOfOp_matrixOp, matrixOfOp_matrixOp,
    matrixOfOp_matrixOp]
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

theorem conjOpFun_one (n : ℕ) :
    conjOpFun (1 : GibbsOperator n) = 1 := by
  unfold conjOpFun
  apply matrixOfOp_injective
  change matrixOfOp (matrixOp ((matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace n))).map (starRingEnd ℂ))) =
    matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace n))
  rw [matrixOfOp_matrixOp, matrixOfOp_id]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem conjOpFun_star {n : ℕ} (X : GibbsOperator n) :
    conjOpFun (star X) = star (conjOpFun X) := by
  unfold conjOpFun
  apply matrixOfOp_injective
  change matrixOfOp (matrixOp ((matrixOfOp (ContinuousLinearMap.adjoint X)).map (starRingEnd ℂ))) =
    matrixOfOp (ContinuousLinearMap.adjoint (matrixOp ((matrixOfOp X).map (starRingEnd ℂ))))
  rw [matrixOfOp_adjoint, matrixOfOp_adjoint, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
  congr 1

theorem conjOpFun_real_smul {n : ℕ} (r : ℝ) (X : GibbsOperator n) :
    conjOpFun (r • X) = r • conjOpFun X := by
  unfold conjOpFun
  apply matrixOfOp_injective
  rw [matrixOfOp_real_smul, matrixOfOp_real_smul, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
  ext i j
  simp

/-- Entrywise complex conjugation as a `ℂ`-antilinear, `ℝ`-linear `*`-automorphism
`GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n`. -/
def conjStarAlgEquiv (n : ℕ) : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n where
  toFun := conjOpFun
  invFun := conjOpFun
  left_inv := conjOpFun_involutive
  right_inv := conjOpFun_involutive
  map_mul' := conjOpFun_mul
  map_add' := conjOpFun_add
  map_smul' := conjOpFun_real_smul
  map_star' := conjOpFun_star

@[simp] theorem conjStarAlgEquiv_apply {n : ℕ} (X : GibbsOperator n) :
    conjStarAlgEquiv n X = conjOpFun X :=
  rfl

theorem conjStarAlgEquiv_involutive {n : ℕ} (X : GibbsOperator n) :
    conjStarAlgEquiv n (conjStarAlgEquiv n X) = X :=
  conjOpFun_involutive X

/-- Entrywise conjugation conjugates the trace (`finiteOperatorTrace (conj X) = star (finiteOperatorTrace X)`),
rather than preserving its imaginary part; hence its real part is invariant. -/
theorem conjStarAlgEquiv_trace {n : ℕ} (X : GibbsOperator n) :
    finiteOperatorTrace (conjStarAlgEquiv n X) = star (finiteOperatorTrace X) := by
  unfold finiteOperatorTrace
  rw [conjStarAlgEquiv_apply, conjOpFun, matrixOfOp_matrixOp]
  simp [Matrix.trace]

theorem conjStarAlgEquiv_trace_re {n : ℕ} (X : GibbsOperator n) :
    (finiteOperatorTrace (conjStarAlgEquiv n X)).re = (finiteOperatorTrace X).re := by
  rw [conjStarAlgEquiv_trace]
  exact Complex.conj_re _

theorem conjStarAlgEquiv_gibbs_fixed {n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_real : conjStarAlgEquiv n H = H) :
    conjStarAlgEquiv n (faithfulGibbsDensity H hH hZ).rho =
      (faithfulGibbsDensity H hH hZ).rho := by
  rw [faithfulGibbsDensity_rho_eq_normalizedGibbsCFC H hH hZ]
  have hcont_τ : Continuous (conjStarAlgEquiv n) :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := conjStarAlgEquiv n
         map_add' := map_add (conjStarAlgEquiv n)
         map_smul' := map_smul (conjStarAlgEquiv n) } :
        GibbsOperator n →ₗ[ℝ] GibbsOperator n)
  have hcont_f : ContinuousOn (normalizedScalarGibbsWeight (gibbsPartitionReal H)) (spectrum ℝ H) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  rw [StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) (conjStarAlgEquiv n)
    (normalizedScalarGibbsWeight (gibbsPartitionReal H)) H hcont_f hcont_τ hH
    (hH.map (conjStarAlgEquiv n)), hH_real]

theorem conjStarAlgEquiv_purelyImaginary_odd {n : ℕ} (S : GibbsOperator n)
    (hS : conjStarAlgEquiv n S = S) :
    conjStarAlgEquiv n (Complex.I • S) = -(Complex.I • S) := by
  change matrixOp ((matrixOfOp (Complex.I • S)).map (starRingEnd ℂ)) = -(Complex.I • S)
  apply matrixOfOp_injective
  have hSmat : (matrixOfOp S).map (starRingEnd ℂ) = matrixOfOp S := by
    have := congrArg matrixOfOp hS
    simpa [conjStarAlgEquiv, conjOpFun] using this
  rw [matrixOfOp_matrixOp, matrixOfOp_complex_smul]
  have hneg : -(Complex.I • S) = (-Complex.I) • S := by
    rw [← neg_one_smul ℂ (Complex.I • S), smul_smul, neg_one_mul]
  rw [hneg, matrixOfOp_complex_smul]
  ext i j
  have hij := congrFun (congrFun hSmat i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_I] at hij ⊢
  rw [hij]

/-! ### Concrete `n = 2` Non-Trivial Noncommutative Witness -/

section ConcreteQubitWitness

/-- Concrete inner derivation `ad(X) : u ↦ X * u - u * X` in `Carrier n`. -/
def innerDerivation {n : ℕ} (X : GibbsOperator n) : Carrier n :=
  show NonAssocDerivation.derivations ℝ (GibbsOperator n) from
    ⟨{ toFun := fun u => X * u - u * X
       map_add' := fun u v => by noncomm_ring
       map_smul' := fun r u => by
         simp only [RingHom.id_apply, real_smul_eq_complex_smul, smul_mul_assoc, mul_smul_comm,
           smul_sub] },
     fun u v => by
       change X * (u * v) - (u * v) * X = (X * u - u * X) * v + u * (X * v - v * X)
       simp only [sub_mul, mul_sub, mul_assoc]
       abel⟩

@[simp] theorem innerDerivation_apply {n : ℕ} (X u : GibbsOperator n) :
    carrierEnd (innerDerivation X) u = X * u - u * X :=
  rfl

/-- Concrete Pauli-Z operator on `FiniteHilbertSpace 2`. -/
def tiltOp2 : GibbsOperator 2 := matrixOp tilt2

/-- Concrete Pauli-X operator on `FiniteHilbertSpace 2`. -/
def switchOp2 : GibbsOperator 2 := matrixOp switch2

theorem tiltOp2_isSelfAdjoint : IsSelfAdjoint tiltOp2 := by
  rw [isSelfAdjoint_iff]
  apply matrixOfOp_injective
  change matrixOfOp (ContinuousLinearMap.adjoint (matrixOp tilt2)) = matrixOfOp (matrixOp tilt2)
  rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, tilt2]

theorem switchOp2_isSelfAdjoint : IsSelfAdjoint switchOp2 := by
  rw [isSelfAdjoint_iff]
  apply matrixOfOp_injective
  change matrixOfOp (ContinuousLinearMap.adjoint (matrixOp switch2)) = matrixOfOp (matrixOp switch2)
  rw [matrixOfOp_adjoint, matrixOfOp_matrixOp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, switch2]

theorem tiltOp2_sq : tiltOp2 * tiltOp2 = 1 := by
  apply matrixOfOp_injective
  change matrixOfOp ((matrixOp tilt2).comp (matrixOp tilt2)) =
    matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2))
  rw [matrixOfOp_comp, matrixOfOp_matrixOp, matrixOfOp_id, tilt2_sq]

theorem switchOp2_sq : switchOp2 * switchOp2 = 1 := by
  apply matrixOfOp_injective
  change matrixOfOp ((matrixOp switch2).comp (matrixOp switch2)) =
    matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2))
  rw [matrixOfOp_comp, matrixOfOp_matrixOp, matrixOfOp_id, switch2_sq]

theorem tiltOp2_switchOp2_anticomm : tiltOp2 * switchOp2 = -(switchOp2 * tiltOp2) := by
  apply matrixOfOp_injective
  change matrixOfOp (tiltOp2.comp switchOp2) = matrixOfOp (-(switchOp2.comp tiltOp2))
  rw [matrixOfOp_comp, tiltOp2, switchOp2, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
  have hneg : matrixOfOp (-(matrixOp switch2).comp (matrixOp tilt2)) =
      -(matrixOfOp ((matrixOp switch2).comp (matrixOp tilt2))) :=
    (LinearMap.toMatrix (ketBasis (Fin 2)) (ketBasis (Fin 2))).map_neg _
  rw [hneg, matrixOfOp_comp, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
  exact tilt2_switch2_anticomm

theorem conj_tiltOp2 : conjStarAlgEquiv 2 tiltOp2 = tiltOp2 := by
  rw [conjStarAlgEquiv_apply, conjOpFun, tiltOp2, matrixOfOp_matrixOp]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tilt2]

theorem conj_switchOp2 : conjStarAlgEquiv 2 switchOp2 = switchOp2 := by
  rw [conjStarAlgEquiv_apply, conjOpFun, switchOp2, matrixOfOp_matrixOp]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [switch2]

theorem switchOp2_ne_zero : switchOp2 ≠ 0 := by
  intro h
  have hm := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 0 1) h
  rw [switchOp2, matrixOfOp_matrixOp, matrixOfOp_zero] at hm
  norm_num [switch2] at hm

/-- Non-vacuity witness on `n = 2` for both `starDerivationTimeReversal` and
`adGammaStarAlgEquiv tiltOp2`: with `H = tiltOp2`, `a = switchOp2`, `Q = switchOp2`,
the `ParityOnsagerSystem` satisfies Onsager–Casimir reciprocity AND has strictly
nonzero dissipation (`0 < dissipative x x`) and strictly nonzero curvature reversibility
(`reversible x y < 0`). -/
theorem qubit_noncommutative_star_and_adGamma_witness
    (hZ : 0 < gibbsPartitionReal tiltOp2) :
    let D := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ
    let hpow := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint hZ
    let PS_star := finiteCEParityOnsagerSystem D hpow switchOp2 switchOp2
      switchOp2_isSelfAdjoint switchOp2_isSelfAdjoint
    let τ := adGammaStarAlgEquiv tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq
    let PS_aut := finiteCEParityOnsagerSystemOfAut_of_parity τ
      (adGammaStarAlgEquiv_involutive tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq)
      D hpow
      (adGammaStarAlgEquiv_gibbs_fixed tiltOp2 tiltOp2 tiltOp2_isSelfAdjoint hZ
        tiltOp2_isSelfAdjoint tiltOp2_sq (Commute.refl tiltOp2))
      (adGammaStarAlgEquiv_trace_re tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq)
      switchOp2 switchOp2 (Or.inr rfl)
      (by
        rw [adGammaStarAlgEquiv_odd_of_anticomm tiltOp2 switchOp2
          tiltOp2_isSelfAdjoint tiltOp2_sq (by rw [tiltOp2_switchOp2_anticomm, neg_neg])]
        exact (neg_one_smul ℝ switchOp2).symm)
      (adGammaStarAlgEquiv_odd_of_anticomm tiltOp2 switchOp2
        tiltOp2_isSelfAdjoint tiltOp2_sq (by rw [tiltOp2_switchOp2_anticomm, neg_neg]))
    let x := innerDerivation tiltOp2
    let y := innerDerivation (tiltOp2 * switchOp2)
    (0 < PS_star.dissipative x x) ∧ (PS_star.reversible x y < 0) ∧
      (0 < PS_aut.dissipative x x) ∧ (PS_aut.reversible x y < 0) ∧
      (PS_star.totalGenerator (PS_star.T.op x) (PS_star.T.op y) = PS_star.totalGenerator y x) ∧
      (PS_aut.totalGenerator (PS_aut.T.op x) (PS_aut.T.op y) = PS_aut.totalGenerator y x) := by
  intro D hpow PS_star τ PS_aut x y
  have hx_val : finiteCEOperatorForm 2 switchOp2 x = (2 : ℝ) • (tiltOp2 * switchOp2) := by
    change carrierEnd x switchOp2 = _
    rw [innerDerivation_apply]
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    rw [hsw, sub_neg_eq_add, ← two_smul ℝ (tiltOp2 * switchOp2)]
  have hnot_gauge : ((2 : ℝ) • (tiltOp2 * switchOp2)) ∉ scalarGauge 2 := by
    intro hmem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have hm := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 0 1) hr
    have hL : matrixOfOp (r • (1 : GibbsOperator 2)) 0 1 = 0 := by
      rw [matrixOfOp_real_smul]
      change (r : ℂ) * matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2)) 0 1 = 0
      rw [matrixOfOp_id]
      simp
    have hR : matrixOfOp ((2 : ℝ) • (tiltOp2 * switchOp2)) 0 1 = 2 := by
      rw [matrixOfOp_real_smul]
      change (2 : ℂ) * matrixOfOp (tiltOp2.comp switchOp2) 0 1 = 2
      rw [matrixOfOp_comp, tiltOp2, switchOp2, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
      norm_num [tilt2, switch2, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hL, hR] at hm
    norm_num at hm
  have hdiss_pos : 0 < PS_star.dissipative x x := by
    change 0 < centeredCEBKMForm D hpow switchOp2 x x
    rw [centeredCEBKMForm_apply, hx_val, centeredBKMRealCovariance_self,
      FaithfulDensityOperator.bkmRealBilinForm_apply]
    apply D.kuboMoriPairing_self_re_pos _ hpow
    intro hzero
    exact hnot_gauge ((centeredStatistic_eq_zero_iff D hpow _).mp hzero)
  have hrev_neg : PS_star.reversible x y < 0 := by
    change ceCurvatureBKMProbeForm D hpow switchOp2 switchOp2 x y < 0
    rw [ceCurvatureBKMProbeForm_apply]
    have hcurv :
        connectionCurvature (realDerivationsLane (GibbsOperator 2))
          (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) switchOp2) x y =
          (-8 : ℝ) • switchOp2 := by
      rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
      change carrierEnd x switchOp2 * carrierEnd y switchOp2 -
        carrierEnd y switchOp2 * carrierEnd x switchOp2 = (-8 : ℝ) • switchOp2
      have hy_val : carrierEnd y switchOp2 = (2 : ℝ) • tiltOp2 := by
        rw [innerDerivation_apply]
        have h1 : (tiltOp2 * switchOp2) * switchOp2 = tiltOp2 := by
          rw [mul_assoc, switchOp2_sq, mul_one]
        have h2 : switchOp2 * (tiltOp2 * switchOp2) = -tiltOp2 := by
          have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
            rw [tiltOp2_switchOp2_anticomm, neg_neg]
          have hop : (-((tiltOp2 * switchOp2))) * switchOp2 = -((tiltOp2 * switchOp2) * switchOp2) := by
            apply ContinuousLinearMap.ext; intro v; simp
          rw [← mul_assoc, hsw, hop, mul_assoc, switchOp2_sq, mul_one]
        rw [h1, h2, sub_neg_eq_add, ← two_smul ℝ tiltOp2]
      have hx' : carrierEnd x switchOp2 = (2 : ℝ) • (tiltOp2 * switchOp2) := hx_val
      rw [hx', hy_val, real_smul_eq_complex_smul 2 (tiltOp2 * switchOp2),
        real_smul_eq_complex_smul 2 tiltOp2, real_smul_eq_complex_smul (-8) switchOp2]
      push_cast
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
      norm_num
      have hsub4 : (4 : ℂ) • ((tiltOp2 * switchOp2) * tiltOp2) -
          (4 : ℂ) • (tiltOp2 * (tiltOp2 * switchOp2)) =
          (4 : ℂ) • ((tiltOp2 * switchOp2) * tiltOp2 - tiltOp2 * (tiltOp2 * switchOp2)) := by
        apply ContinuousLinearMap.ext; intro v; simp [smul_sub]
      rw [hsub4]
      have h1 : (tiltOp2 * switchOp2) * tiltOp2 = -switchOp2 := by
        have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
          rw [tiltOp2_switchOp2_anticomm, neg_neg]
        have hop : tiltOp2 * (-(tiltOp2 * switchOp2)) = -(tiltOp2 * (tiltOp2 * switchOp2)) := by
          apply ContinuousLinearMap.ext; intro v; simp
        rw [mul_assoc, hsw, hop, ← mul_assoc, tiltOp2_sq, one_mul]
      have h2 : tiltOp2 * (tiltOp2 * switchOp2) = switchOp2 := by
        rw [← mul_assoc, tiltOp2_sq, one_mul]
      rw [h1, h2]
      have hneg2 : -switchOp2 - switchOp2 = (-2 : ℂ) • switchOp2 := by
        apply ContinuousLinearMap.ext; intro v
        simp only [_root_.sub_apply, _root_.neg_apply, _root_.smul_apply]
        module
      rw [hneg2, smul_smul]
      norm_num
    rw [hcurv, (D.bkmRealBilinForm hpow).map_smul, LinearMap.smul_apply,
      D.bkmRealBilinForm_apply]
    have hpos : 0 < (D.kuboMoriPairing switchOp2 switchOp2).re :=
      D.kuboMoriPairing_self_re_pos switchOp2 hpow switchOp2_ne_zero
    change (-8 : ℝ) * (D.kuboMoriPairing switchOp2 switchOp2).re < 0
    linarith
  refine ⟨hdiss_pos, hrev_neg, hdiss_pos, hrev_neg,
    PS_star.onsager_casimir_master_reciprocity x y,
    PS_aut.onsager_casimir_master_reciprocity x y⟩

/-- Non-vacuity witness on `n = 2` for `conjStarAlgEquiv 2` (`ℂ`-antilinear conjugation):
with `H = tiltOp2` (real), `a = switchOp2` (real), and `Q = Complex.I • switchOp2`
(purely imaginary), `conjStarAlgEquiv 2` satisfies `ParityOnsagerSystem` reciprocity
with strictly positive dissipation and strictly nonzero curvature reversibility. -/
theorem qubit_noncommutative_conj_witness
    (hZ : 0 < gibbsPartitionReal tiltOp2) :
    let D := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ
    let hpow := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint hZ
    let Q := Complex.I • switchOp2
    let PS_conj := finiteCEParityOnsagerSystemOfAut (conjStarAlgEquiv 2)
      (conjStarAlgEquiv_involutive (n := 2)) D hpow
      (conjStarAlgEquiv_gibbs_fixed tiltOp2 tiltOp2_isSelfAdjoint hZ conj_tiltOp2)
      (conjStarAlgEquiv_trace_re (n := 2))
      switchOp2 Q conj_switchOp2
      (conjStarAlgEquiv_purelyImaginary_odd switchOp2 conj_switchOp2)
    let x := innerDerivation tiltOp2
    let y := innerDerivation (Complex.I • (tiltOp2 * switchOp2))
    (0 < PS_conj.dissipative x x) ∧ (PS_conj.reversible x y ≠ 0) ∧
      (PS_conj.totalGenerator (PS_conj.T.op x) (PS_conj.T.op y) = PS_conj.totalGenerator y x) := by
  intro D hpow Q PS_conj x y
  have hx_val : finiteCEOperatorForm 2 switchOp2 x = (2 : ℝ) • (tiltOp2 * switchOp2) := by
    change carrierEnd x switchOp2 = _
    rw [innerDerivation_apply]
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    rw [hsw, sub_neg_eq_add, ← two_smul ℝ (tiltOp2 * switchOp2)]
  have hnot_gauge : ((2 : ℝ) • (tiltOp2 * switchOp2)) ∉ scalarGauge 2 := by
    intro hmem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have hm := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 0 1) hr
    have hL : matrixOfOp (r • (1 : GibbsOperator 2)) 0 1 = 0 := by
      rw [matrixOfOp_real_smul]
      change (r : ℂ) * matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2)) 0 1 = 0
      rw [matrixOfOp_id]
      simp
    have hR : matrixOfOp ((2 : ℝ) • (tiltOp2 * switchOp2)) 0 1 = 2 := by
      rw [matrixOfOp_real_smul]
      change (2 : ℂ) * matrixOfOp (tiltOp2.comp switchOp2) 0 1 = 2
      rw [matrixOfOp_comp, tiltOp2, switchOp2, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
      norm_num [tilt2, switch2, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hL, hR] at hm
    norm_num at hm
  have hdiss_pos : 0 < PS_conj.dissipative x x := by
    change 0 < centeredCEBKMForm D hpow switchOp2 x x
    rw [centeredCEBKMForm_apply, hx_val, centeredBKMRealCovariance_self,
      FaithfulDensityOperator.bkmRealBilinForm_apply]
    apply D.kuboMoriPairing_self_re_pos _ hpow
    intro hzero
    exact hnot_gauge ((centeredStatistic_eq_zero_iff D hpow _).mp hzero)
  have hy_val : carrierEnd y switchOp2 = Complex.I • ((2 : ℝ) • tiltOp2) := by
    rw [innerDerivation_apply, smul_mul_assoc, mul_smul_comm]
    have h1 : (tiltOp2 * switchOp2) * switchOp2 = tiltOp2 := by
      rw [mul_assoc, switchOp2_sq, mul_one]
    have h2 : switchOp2 * (tiltOp2 * switchOp2) = -tiltOp2 := by
      have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
        rw [tiltOp2_switchOp2_anticomm, neg_neg]
      have hop : (-((tiltOp2 * switchOp2))) * switchOp2 = -((tiltOp2 * switchOp2) * switchOp2) := by
        apply ContinuousLinearMap.ext; intro v; simp
      rw [← mul_assoc, hsw, hop, mul_assoc, switchOp2_sq, mul_one]
    have hdiff :
        (tiltOp2 * switchOp2) * switchOp2 - switchOp2 * (tiltOp2 * switchOp2) =
          (2 : ℝ) • tiltOp2 := by
      rw [h1, h2, sub_neg_eq_add, ← two_smul ℝ tiltOp2]
    rw [← hdiff]
    apply ContinuousLinearMap.ext; intro v; simp [smul_sub]
  have hcomm_eq :
      carrierEnd x switchOp2 * carrierEnd y switchOp2 -
          carrierEnd y switchOp2 * carrierEnd x switchOp2 = (-8 : ℝ) • Q := by
    have hx' : carrierEnd x switchOp2 = (2 : ℝ) • (tiltOp2 * switchOp2) := hx_val
    have h2a : (2 : ℝ) • (tiltOp2 * switchOp2) = (2 : ℂ) • (tiltOp2 * switchOp2) := by
      rw [real_smul_eq_complex_smul]; norm_cast
    have h2b : (2 : ℝ) • tiltOp2 = (2 : ℂ) • tiltOp2 := by
      rw [real_smul_eq_complex_smul]; norm_cast
    have h8 : (-8 : ℝ) • switchOp2 = (-8 : ℂ) • switchOp2 := by
      rw [real_smul_eq_complex_smul]; norm_cast
    have h8Q : (-8 : ℝ) • (Complex.I • switchOp2) = (-8 : ℂ) • (Complex.I • switchOp2) := by
      rw [real_smul_eq_complex_smul]; norm_cast
    rw [hx', hy_val, h2a, h2b]
    change ((2 : ℂ) • (tiltOp2 * switchOp2)) * (Complex.I • ((2 : ℂ) • tiltOp2)) -
        (Complex.I • ((2 : ℂ) • tiltOp2)) * ((2 : ℂ) • (tiltOp2 * switchOp2)) =
      (-8 : ℝ) • (Complex.I • switchOp2)
    rw [h8Q]
    have hL : ((2 : ℂ) • (tiltOp2 * switchOp2)) * (Complex.I • ((2 : ℂ) • tiltOp2)) =
        Complex.I • (((2 : ℂ) • (tiltOp2 * switchOp2)) * ((2 : ℂ) • tiltOp2)) :=
      mul_smul_comm Complex.I ((2 : ℂ) • (tiltOp2 * switchOp2)) ((2 : ℂ) • tiltOp2)
    have hR : (Complex.I • ((2 : ℂ) • tiltOp2)) * ((2 : ℂ) • (tiltOp2 * switchOp2)) =
        Complex.I • (((2 : ℂ) • tiltOp2) * ((2 : ℂ) • (tiltOp2 * switchOp2))) :=
      smul_mul_assoc Complex.I ((2 : ℂ) • tiltOp2) ((2 : ℂ) • (tiltOp2 * switchOp2))
    have hcore : ((2 : ℂ) • (tiltOp2 * switchOp2)) * ((2 : ℂ) • tiltOp2) -
        ((2 : ℂ) • tiltOp2) * ((2 : ℂ) • (tiltOp2 * switchOp2)) = (-8 : ℂ) • switchOp2 := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
      norm_num
      have hsub4 : (4 : ℂ) • ((tiltOp2 * switchOp2) * tiltOp2) -
          (4 : ℂ) • (tiltOp2 * (tiltOp2 * switchOp2)) =
          (4 : ℂ) • ((tiltOp2 * switchOp2) * tiltOp2 - tiltOp2 * (tiltOp2 * switchOp2)) := by
        apply ContinuousLinearMap.ext; intro v; simp [smul_sub]
      rw [hsub4]
      have h1 : (tiltOp2 * switchOp2) * tiltOp2 = -switchOp2 := by
        have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
          rw [tiltOp2_switchOp2_anticomm, neg_neg]
        have hop : tiltOp2 * (-(tiltOp2 * switchOp2)) = -(tiltOp2 * (tiltOp2 * switchOp2)) := by
          apply ContinuousLinearMap.ext; intro v; simp
        rw [mul_assoc, hsw, hop, ← mul_assoc, tiltOp2_sq, one_mul]
      have h2 : tiltOp2 * (tiltOp2 * switchOp2) = switchOp2 := by
        rw [← mul_assoc, tiltOp2_sq, one_mul]
      rw [h1, h2]
      have hneg2 : -switchOp2 - switchOp2 = (-2 : ℂ) • switchOp2 := by
        apply ContinuousLinearMap.ext; intro v
        simp only [_root_.sub_apply, _root_.neg_apply, _root_.smul_apply]
        module
      rw [hneg2, smul_smul]
      norm_num
    calc
      ((2 : ℂ) • (tiltOp2 * switchOp2)) * (Complex.I • ((2 : ℂ) • tiltOp2)) -
          (Complex.I • ((2 : ℂ) • tiltOp2)) * ((2 : ℂ) • (tiltOp2 * switchOp2)) =
        Complex.I • (((2 : ℂ) • (tiltOp2 * switchOp2)) * ((2 : ℂ) • tiltOp2) -
            ((2 : ℂ) • tiltOp2) * ((2 : ℂ) • (tiltOp2 * switchOp2))) := by
            rw [hL, hR]
            apply ContinuousLinearMap.ext; intro v; simp [smul_sub]
      _ = Complex.I • ((-8 : ℂ) • switchOp2) := by rw [hcore]
      _ = (-8 : ℂ) • (Complex.I • switchOp2) :=
            smul_comm Complex.I (-8 : ℂ) switchOp2
  have hrev_ne : PS_conj.reversible x y ≠ 0 := by
    change ceCurvatureBKMProbeForm D hpow switchOp2 Q x y ≠ 0
    rw [ceCurvatureBKMProbeForm_apply]
    have hcurv :
        connectionCurvature (realDerivationsLane (GibbsOperator 2))
          (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) switchOp2) x y =
          (-8 : ℝ) • Q := by
      rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
      exact hcomm_eq
    rw [hcurv, (D.bkmRealBilinForm hpow).map_smul, LinearMap.smul_apply,
      D.bkmRealBilinForm_apply]
    have hQ_ne : Q ≠ 0 := by
      intro hQ0
      have h0 : Complex.I • switchOp2 = 0 := hQ0
      have h1 : (-Complex.I) • (Complex.I • switchOp2) = (0 : GibbsOperator 2) := by
        rw [h0]
        apply ContinuousLinearMap.ext
        intro v
        simp
      rw [smul_smul] at h1
      have hII : (-Complex.I) * Complex.I = 1 := by
        rw [neg_mul, Complex.I_mul_I, neg_neg]
      rw [hII, one_smul] at h1
      exact switchOp2_ne_zero h1
    have hpos : 0 < (D.kuboMoriPairing Q Q).re :=
      D.kuboMoriPairing_self_re_pos Q hpow hQ_ne
    change (-8 : ℝ) * (D.kuboMoriPairing Q Q).re ≠ 0
    linarith
  exact ⟨hdiss_pos, hrev_ne, PS_conj.onsager_casimir_master_reciprocity x y⟩

end ConcreteQubitWitness

end ConcreteAutomorphismsAndWitnesses

/-! ## Section 5: Gibbs, `NOperatorForm` Family, and `ErlangenOperator2Bridge` Parity Upgrades -/

section GibbsFamilyAndErlangen

/-- Gibbs-state specialization of `finiteCEParityOnsagerSystem_of_parity`. -/
def finiteGibbsCEParityOnsagerSystem_of_parity {n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a Q : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : star a = ε • a)
    (hQ : IsSelfAdjoint Q) :
    ParityOnsagerSystem (Carrier n) :=
  finiteCEParityOnsagerSystem_of_parity
    (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ)
    a Q hε ha hQ

/-- Gibbs-state specialization of `finiteCEParityOnsagerSystem` (`IsSelfAdjoint a`, `IsSelfAdjoint Q`). -/
def finiteGibbsCEParityOnsagerSystem {n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a Q : GibbsOperator n) (ha : IsSelfAdjoint a) (hQ : IsSelfAdjoint Q) :
    ParityOnsagerSystem (Carrier n) :=
  finiteCEParityOnsagerSystem
    (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ)
    a Q ha hQ

/-- Any `ℝ`-algebra `*`-automorphism fixing `H` fixes the faithful Gibbs density `(faithfulGibbsDensity H hH hZ).rho`. -/
theorem aut_faithfulGibbsDensity_rho {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H) :
    τ (faithfulGibbsDensity H hH hZ).rho = (faithfulGibbsDensity H hH hZ).rho := by
  rw [faithfulGibbsDensity_rho_eq_normalizedGibbsCFC H hH hZ]
  have hcont_τ : Continuous τ :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := τ, map_add' := map_add τ, map_smul' := map_smul τ } :
        GibbsOperator n →ₗ[ℝ] GibbsOperator n)
  have hcont_f : ContinuousOn (normalizedScalarGibbsWeight (gibbsPartitionReal H)) (spectrum ℝ H) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  rw [StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) τ
    (normalizedScalarGibbsWeight (gibbsPartitionReal H)) H hcont_f hcont_τ hH (hH.map τ), hτ_H]

/-- Gibbs-state specialization of `finiteCEParityOnsagerSystemOfAut_of_parity`. -/
def finiteGibbsCEParityOnsagerSystemOfAut_of_parity {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a Q : GibbsOperator n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ha : τ a = ε • a)
    (hQ : τ Q = -Q) :
    ParityOnsagerSystem (Carrier n) :=
  finiteCEParityOnsagerSystemOfAut_of_parity τ hτ_inv
    (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ)
    (aut_faithfulGibbsDensity_rho τ H hH hZ hτ_H)
    hτ_tr a Q hε ha hQ

/-- Gibbs-state specialization of `finiteCEParityOnsagerSystemOfAut` (`τ H = H`, `τ a = a`, `τ Q = -Q`). -/
def finiteGibbsCEParityOnsagerSystemOfAut {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a Q : GibbsOperator n) (ha : τ a = a) (hQ : τ Q = -Q) :
    ParityOnsagerSystem (Carrier n) :=
  finiteGibbsCEParityOnsagerSystemOfAut_of_parity τ hτ_inv H hH hZ hτ_H hτ_tr a Q
    (Or.inl rfl) (by simpa using ha) hQ

/-- Product `TimeReversal` on `Fin m → V` acting componentwise. -/
def familyTimeReversal (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : TimeReversal V) : TimeReversal (Fin m → V) where
  op :=
    { toFun := fun x i => T.op (x i)
      map_add' := fun x y => funext fun i => map_add T.op (x i) (y i)
      map_smul' := fun r x => funext fun i => map_smul T.op r (x i) }
  involutive := fun x => funext fun i => T.involutive (x i)

@[simp] theorem familyTimeReversal_apply (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : TimeReversal V) (x : Fin m → V) (i : Fin m) :
    (familyTimeReversal m T).op x i = T.op (x i) :=
  rfl

/-- Signed product `TimeReversal` on `Fin m → V` supporting mixed component observable
parities `s i ∈ {1, -1}`. -/
def signedFamilyTimeReversal (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : Fin m → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (T : TimeReversal V) : TimeReversal (Fin m → V) where
  op :=
    { toFun := fun x i => s i • T.op (x i)
      map_add' := fun x y => funext fun i => by simp [map_add, smul_add]
      map_smul' := fun r x => funext fun i => by simp [map_smul, smul_comm r (s i)] }
  involutive := fun x => funext fun i => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul, T.involutive, smul_smul]
    rcases hs i with h | h <;> simp [h]

@[simp] theorem signedFamilyTimeReversal_apply (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : Fin m → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (T : TimeReversal V) (x : Fin m → V) (i : Fin m) :
    (signedFamilyTimeReversal m s hs T).op x i = s i • T.op (x i) :=
  rfl

/-- Mixed-parity `NOperatorForm` family `ParityOnsagerSystem` under `starDerivationTimeReversal`
(`star (a i) = s i • a i`, `s i = ±1`, `IsSelfAdjoint Q`). -/
def finiteGibbsCEFamilyNOperatorParitySystem_of_parity {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n) (s : Fin m → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (ha : ∀ i, star (a i) = s i • a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) :
    ParityOnsagerSystem (FamilyCarrier m n) where
  toOnsagerCasimirSystem := finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q
  T := signedFamilyTimeReversal m s hs (starDerivationTimeReversal n)
  dissipative_T_even x y := by
    change finiteCEFamilyNOperatorDissipativeForm
        (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ) a c
        ((signedFamilyTimeReversal m s hs (starDerivationTimeReversal n)).op x)
        ((signedFamilyTimeReversal m s hs (starDerivationTimeReversal n)).op y) =
      finiteCEFamilyNOperatorDissipativeForm
        (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ) a c x y
    rw [finiteCEFamilyNOperatorDissipativeForm_apply, finiteCEFamilyNOperatorDissipativeForm_apply]
    have hread : ∀ z : FamilyCarrier m n,
        finiteGibbsCEFamilyNOperatorReadoutLinear a c
          ((signedFamilyTimeReversal m s hs (starDerivationTimeReversal n)).op z) =
          star (finiteGibbsCEFamilyNOperatorReadoutLinear a c z) := fun z => by
      rw [finiteGibbsCEFamilyNOperatorReadoutLinear_apply,
        finiteGibbsCEFamilyNOperatorReadoutLinear_apply]
      have hstarsum :
          star (∑ i : Fin m, c i • finiteGibbsCEFamilyComponentForm a i (z i)) =
            ∑ i : Fin m, star (c i • finiteGibbsCEFamilyComponentForm a i (z i)) := by
        rw [← finiteOperatorStarRealCLM_apply (n := n), map_sum]
        rfl
      rw [hstarsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [finiteGibbsCEFamilyComponentForm_apply, finiteGibbsCEFamilyComponentForm_apply,
        signedFamilyTimeReversal_apply, map_smul]
      have hform : finiteCEOperatorForm n (a i) ((starDerivationTimeReversal n).op (z i)) =
          s i • star (finiteCEOperatorForm n (a i) (z i)) := by
        change carrierEnd ((starDerivationTimeReversal n).op (z i)) (a i) =
          s i • star (carrierEnd (z i) (a i))
        rw [starDerivationTimeReversal_apply, starDerivation_apply, ha i, (carrierEnd (z i)).map_smul,
          ← finiteOperatorStarRealCLM_apply (n := n), map_smul, finiteOperatorStarRealCLM_apply]
      rw [hform, smul_smul, smul_smul]
      have hs2 : s i * s i = 1 := by rcases hs i with h | h <;> simp [h]
      rw [mul_assoc (c i) (s i) (s i), hs2, mul_one]
      change c i • star (finiteCEOperatorForm n (a i) (z i)) =
        star (c i • finiteCEOperatorForm n (a i) (z i))
      rw [← finiteOperatorStarRealCLM_apply (n := n), ← (finiteOperatorStarRealCLM n).map_smul (c i) _,
        finiteOperatorStarRealCLM_apply]
    rw [hread x, hread y]
    exact centeredBKMRealCovariance_star _ _ _ _
  reversible_T_odd x y := by
    change finiteCEFamilyNOperatorCurvatureProbeForm
        (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ) a c Q
        ((signedFamilyTimeReversal m s hs (starDerivationTimeReversal n)).op x)
        ((signedFamilyTimeReversal m s hs (starDerivationTimeReversal n)).op y) =
      -finiteCEFamilyNOperatorCurvatureProbeForm
        (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ) a c Q x y
    rw [finiteCEFamilyNOperatorCurvatureProbeForm_apply,
      finiteCEFamilyNOperatorCurvatureProbeForm_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [signedFamilyTimeReversal_apply, LinearMap.map_smul, LinearMap.smul_apply]
    rw [ceCurvatureBKMProbeForm_starDerivation_odd_of_parity _ _ (a i) Q (hs i) (ha i) hQ]
    have hs2 : s i * s i = 1 := by rcases hs i with h | h <;> simp [h]
    simp only [smul_eq_mul, mul_neg]
    congr 1
    calc
      c i * (s i * (s i * ceCurvatureBKMProbeForm _ _ (a i) Q (x i) (y i))) =
          c i * ((s i * s i) * ceCurvatureBKMProbeForm _ _ (a i) Q (x i) (y i)) := by ring
      _ = c i * ceCurvatureBKMProbeForm _ _ (a i) Q (x i) (y i) := by rw [hs2, one_mul]

/-- Uniform-parity `NOperatorForm` family `ParityOnsagerSystem` under `familyTimeReversal m (starDerivationTimeReversal n)`. -/
def finiteGibbsCEFamilyNOperatorParitySystem {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, IsSelfAdjoint (a i))
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) :
    ParityOnsagerSystem (FamilyCarrier m n) where
  toOnsagerCasimirSystem := finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q
  T := familyTimeReversal m (starDerivationTimeReversal n)
  dissipative_T_even x y := by
    have hT : ∀ z : FamilyCarrier m n,
        (familyTimeReversal m (starDerivationTimeReversal n)).op z =
          (signedFamilyTimeReversal m (fun _ => 1) (fun _ => Or.inl rfl)
            (starDerivationTimeReversal n)).op z :=
      fun z => funext fun i => (one_smul ℝ _).symm
    rw [hT x, hT y]
    exact (finiteGibbsCEFamilyNOperatorParitySystem_of_parity H hH hZ a
      (fun _ => 1) (fun _ => Or.inl rfl)
      (fun i => by simpa [IsSelfAdjoint] using (ha i).star_eq) c Q hQ).dissipative_T_even x y
  reversible_T_odd x y := by
    have hT : ∀ z : FamilyCarrier m n,
        (familyTimeReversal m (starDerivationTimeReversal n)).op z =
          (signedFamilyTimeReversal m (fun _ => 1) (fun _ => Or.inl rfl)
            (starDerivationTimeReversal n)).op z :=
      fun z => funext fun i => (one_smul ℝ _).symm
    rw [hT x, hT y]
    exact (finiteGibbsCEFamilyNOperatorParitySystem_of_parity H hH hZ a
      (fun _ => 1) (fun _ => Or.inl rfl)
      (fun i => by simpa [IsSelfAdjoint] using (ha i).star_eq) c Q hQ).reversible_T_odd x y

/-- Mixed-parity `NOperatorForm` family `ParityOnsagerSystem` under an involutive
`ℝ`-algebra `*`-automorphism `τ` (`τ H = H`, `τ (a i) = s i • a i`, `τ Q = -Q`). -/
def finiteGibbsCEFamilyNOperatorParitySystemOfAut_of_parity {m n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a : Fin m → GibbsOperator n) (s : Fin m → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (ha : ∀ i, τ (a i) = s i • a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : τ Q = -Q) :
    ParityOnsagerSystem (FamilyCarrier m n) where
  toOnsagerCasimirSystem := finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q
  T := signedFamilyTimeReversal m s hs (autDerivationTimeReversal τ hτ_inv)
  dissipative_T_even x y := by
    change finiteCEFamilyNOperatorDissipativeForm
        (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ) a c
        ((signedFamilyTimeReversal m s hs (autDerivationTimeReversal τ hτ_inv)).op x)
        ((signedFamilyTimeReversal m s hs (autDerivationTimeReversal τ hτ_inv)).op y) =
      finiteCEFamilyNOperatorDissipativeForm
        (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ) a c x y
    rw [finiteCEFamilyNOperatorDissipativeForm_apply, finiteCEFamilyNOperatorDissipativeForm_apply]
    have hread : ∀ z : FamilyCarrier m n,
        finiteGibbsCEFamilyNOperatorReadoutLinear a c
          ((signedFamilyTimeReversal m s hs (autDerivationTimeReversal τ hτ_inv)).op z) =
          τ (finiteGibbsCEFamilyNOperatorReadoutLinear a c z) := fun z => by
      rw [finiteGibbsCEFamilyNOperatorReadoutLinear_apply,
        finiteGibbsCEFamilyNOperatorReadoutLinear_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [finiteGibbsCEFamilyComponentForm_apply, finiteGibbsCEFamilyComponentForm_apply,
        signedFamilyTimeReversal_apply, map_smul]
      have hsymm : τ.symm (a i) = s i • a i :=
        τ.injective (by
          calc
            τ (τ.symm (a i)) = a i := τ.apply_symm_apply (a i)
            _ = τ (τ (a i)) := (hτ_inv (a i)).symm
            _ = τ (s i • a i) := by rw [ha i])
      have hform : finiteCEOperatorForm n (a i) ((autDerivationTimeReversal τ hτ_inv).op (z i)) =
          s i • τ (finiteCEOperatorForm n (a i) (z i)) := by
        change carrierEnd ((autDerivationTimeReversal τ hτ_inv).op (z i)) (a i) =
          s i • τ (carrierEnd (z i) (a i))
        rw [autDerivationTimeReversal_apply, autDerivation_apply, hsymm,
          (carrierEnd (z i)).map_smul, map_smul]
      rw [hform, smul_smul, smul_smul]
      have hs2 : s i * s i = 1 := by rcases hs i with h | h <;> simp [h]
      rw [mul_assoc (c i) (s i) (s i), hs2, mul_one, map_smul]
    rw [hread x, hread y]
    exact centeredBKMRealCovariance_aut τ _ _
      (aut_faithfulGibbsDensity_rho τ H hH hZ hτ_H) hτ_tr _ _
  reversible_T_odd x y := by
    change finiteCEFamilyNOperatorCurvatureProbeForm
        (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ) a c Q
        ((signedFamilyTimeReversal m s hs (autDerivationTimeReversal τ hτ_inv)).op x)
        ((signedFamilyTimeReversal m s hs (autDerivationTimeReversal τ hτ_inv)).op y) =
      -finiteCEFamilyNOperatorCurvatureProbeForm
        (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ) a c Q x y
    rw [finiteCEFamilyNOperatorCurvatureProbeForm_apply,
      finiteCEFamilyNOperatorCurvatureProbeForm_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [signedFamilyTimeReversal_apply, LinearMap.map_smul, LinearMap.smul_apply]
    rw [ceCurvatureBKMProbeForm_autDerivation_odd_of_parity τ hτ_inv _ _
      (aut_faithfulGibbsDensity_rho τ H hH hZ hτ_H) hτ_tr (a i) Q (hs i) (ha i) hQ]
    have hs2 : s i * s i = 1 := by rcases hs i with h | h <;> simp [h]
    simp only [smul_eq_mul, mul_neg]
    congr 1
    calc
      c i * (s i * (s i * ceCurvatureBKMProbeForm _ _ (a i) Q (x i) (y i))) =
          c i * ((s i * s i) * ceCurvatureBKMProbeForm _ _ (a i) Q (x i) (y i)) := by ring
      _ = c i * ceCurvatureBKMProbeForm _ _ (a i) Q (x i) (y i) := by rw [hs2, one_mul]

/-- Uniform-parity `NOperatorForm` family `ParityOnsagerSystem` under `familyTimeReversal m (autDerivationTimeReversal τ hτ_inv)`. -/
def finiteGibbsCEFamilyNOperatorParitySystemOfAut {m n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, τ (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : τ Q = -Q) :
    ParityOnsagerSystem (FamilyCarrier m n) where
  toOnsagerCasimirSystem := finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q
  T := familyTimeReversal m (autDerivationTimeReversal τ hτ_inv)
  dissipative_T_even x y := by
    have hT : ∀ z : FamilyCarrier m n,
        (familyTimeReversal m (autDerivationTimeReversal τ hτ_inv)).op z =
          (signedFamilyTimeReversal m (fun _ => 1) (fun _ => Or.inl rfl)
            (autDerivationTimeReversal τ hτ_inv)).op z :=
      fun z => funext fun i => (one_smul ℝ _).symm
    rw [hT x, hT y]
    exact (finiteGibbsCEFamilyNOperatorParitySystemOfAut_of_parity τ hτ_inv H hH hZ
      hτ_H hτ_tr a (fun _ => 1) (fun _ => Or.inl rfl)
      (fun i => by simpa using ha i) c Q hQ).dissipative_T_even x y
  reversible_T_odd x y := by
    have hT : ∀ z : FamilyCarrier m n,
        (familyTimeReversal m (autDerivationTimeReversal τ hτ_inv)).op z =
          (signedFamilyTimeReversal m (fun _ => 1) (fun _ => Or.inl rfl)
            (autDerivationTimeReversal τ hτ_inv)).op z :=
      fun z => funext fun i => (one_smul ℝ _).symm
    rw [hT x, hT y]
    exact (finiteGibbsCEFamilyNOperatorParitySystemOfAut_of_parity τ hτ_inv H hH hZ
      hτ_H hτ_tr a (fun _ => 1) (fun _ => Or.inl rfl)
      (fun i => by simpa using ha i) c Q hQ).reversible_T_odd x y

/-- Convert any `TimeReversal V` into `OperatorFrechetForms.ExchangeInvolution V`. -/
def timeReversalToExchangeInvolution {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : TimeReversal V) : ExchangeInvolution V where
  exchange :=
    { toLinearMap := T.op
      invFun := T.op
      left_inv := T.involutive
      right_inv := T.involutive }
  exchange_sq := T.involutive

@[simp] theorem timeReversalToExchangeInvolution_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : TimeReversal V) (x : V) :
    (timeReversalToExchangeInvolution T).exchange x = T.op x :=
  rfl

/-- Hypothesis-free `ErlangenOperatorDatum` specialization of
`ErlangenOperator2Bridge.gibbsNOperatorFamilyErlangenDatum` using
`familyTimeReversal m (starDerivationTimeReversal n)` for self-adjoint `a` and `Q`. -/
@[irreducible] def gibbsNOperatorFamilyStarErlangenDatum
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, IsSelfAdjoint (a i))
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) :
    ErlangenOperatorDatum ℝ G Unit (FamilyCarrier m n) :=
  let PS := finiteGibbsCEFamilyNOperatorParitySystem H hH hZ a ha c Q hQ
  gibbsNOperatorFamilyErlangenDatum (G := G) H hH hZ a c Q
    (timeReversalToExchangeInvolution PS.T)
    PS.dissipative_T_even PS.reversible_T_odd

@[simp] theorem gibbsNOperatorFamilyStarErlangenDatum_responseMetric
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, IsSelfAdjoint (a i))
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (s : Unit) (x y : FamilyCarrier m n) :
    (gibbsNOperatorFamilyStarErlangenDatum (G := G) H hH hZ a ha c Q hQ).responseMetric s x y =
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative x y := by
  unfold gibbsNOperatorFamilyStarErlangenDatum
  rfl

@[simp] theorem gibbsNOperatorFamilyStarErlangenDatum_onsagerPairing
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, IsSelfAdjoint (a i))
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (s : Unit) (x y : FamilyCarrier m n) :
    (gibbsNOperatorFamilyStarErlangenDatum (G := G) H hH hZ a ha c Q hQ).onsagerPairing s x y =
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).totalGenerator x y := by
  unfold gibbsNOperatorFamilyStarErlangenDatum
  rfl

@[simp] theorem gibbsNOperatorFamilyStarErlangenDatum_casimirJ
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, IsSelfAdjoint (a i))
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (x : FamilyCarrier m n) :
    (gibbsNOperatorFamilyStarErlangenDatum (G := G) H hH hZ a ha c Q hQ).casimirJ x =
      (familyTimeReversal m (starDerivationTimeReversal n)).op x := by
  unfold gibbsNOperatorFamilyStarErlangenDatum
  rfl

theorem gibbsNOperatorFamilyStarErlangenDatum_reciprocity_and_hessian
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, IsSelfAdjoint (a i))
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (D₁ D₂ : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hD₁ : IsSelfAdjoint
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c (finiteCEFrechetFamilyDirection D₁))) :
    let datum := gibbsNOperatorFamilyStarErlangenDatum (G := G) H hH hZ a ha c Q hQ
    let T := familyTimeReversal m (starDerivationTimeReversal n)
    HasJReciprocity datum.onsagerPairing T.op ∧
      datum.responseMetric ()
          (finiteCEFrechetFamilyDirection D₁)
          (finiteCEFrechetFamilyDirection D₂) =
        (secondFDerivLogPartitionReadout H
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₁))
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₂))).re := by
  dsimp only
  unfold gibbsNOperatorFamilyStarErlangenDatum
  let PS := finiteGibbsCEFamilyNOperatorParitySystem H hH hZ a ha c Q hQ
  have h := gibbsNOperatorFamilyErlangenDatum_reciprocity_and_hessian (G := G) H hH hZ a c Q
    (timeReversalToExchangeInvolution PS.T)
    PS.dissipative_T_even PS.reversible_T_odd D₁ D₂ hD₁
  exact ⟨fun A B s => h.1 A B s, h.2⟩

/-- Hypothesis-free `ErlangenOperatorDatum` specialization of
`ErlangenOperator2Bridge.gibbsNOperatorFamilyErlangenDatum` using an involutive
`ℝ`-algebra `*`-automorphism `τ` (`τ H = H`, `τ (a i) = a i`, `τ Q = -Q`). -/
@[irreducible] def gibbsNOperatorFamilyAutErlangenDatum
    {G : Type*} [Group G] {m n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, τ (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : τ Q = -Q) :
    ErlangenOperatorDatum ℝ G Unit (FamilyCarrier m n) :=
  let PS := finiteGibbsCEFamilyNOperatorParitySystemOfAut τ hτ_inv H hH hZ hτ_H hτ_tr a ha c Q hQ
  gibbsNOperatorFamilyErlangenDatum (G := G) H hH hZ a c Q
    (timeReversalToExchangeInvolution PS.T)
    PS.dissipative_T_even PS.reversible_T_odd

@[simp] theorem gibbsNOperatorFamilyAutErlangenDatum_responseMetric
    {G : Type*} [Group G] {m n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, τ (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : τ Q = -Q)
    (s : Unit) (x y : FamilyCarrier m n) :
    (gibbsNOperatorFamilyAutErlangenDatum (G := G) τ hτ_inv H hH hZ hτ_H hτ_tr a ha c Q hQ).responseMetric s x y =
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative x y := by
  unfold gibbsNOperatorFamilyAutErlangenDatum
  rfl

@[simp] theorem gibbsNOperatorFamilyAutErlangenDatum_onsagerPairing
    {G : Type*} [Group G] {m n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, τ (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : τ Q = -Q)
    (s : Unit) (x y : FamilyCarrier m n) :
    (gibbsNOperatorFamilyAutErlangenDatum (G := G) τ hτ_inv H hH hZ hτ_H hτ_tr a ha c Q hQ).onsagerPairing s x y =
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).totalGenerator x y := by
  unfold gibbsNOperatorFamilyAutErlangenDatum
  rfl

@[simp] theorem gibbsNOperatorFamilyAutErlangenDatum_casimirJ
    {G : Type*} [Group G] {m n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, τ (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : τ Q = -Q)
    (x : FamilyCarrier m n) :
    (gibbsNOperatorFamilyAutErlangenDatum (G := G) τ hτ_inv H hH hZ hτ_H hτ_tr a ha c Q hQ).casimirJ x =
      (familyTimeReversal m (autDerivationTimeReversal τ hτ_inv)).op x := by
  unfold gibbsNOperatorFamilyAutErlangenDatum
  rfl

theorem gibbsNOperatorFamilyAutErlangenDatum_reciprocity_and_hessian
    {G : Type*} [Group G] {m n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, τ (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ : τ Q = -Q)
    (D₁ D₂ : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hD₁ : IsSelfAdjoint
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c (finiteCEFrechetFamilyDirection D₁))) :
    let datum := gibbsNOperatorFamilyAutErlangenDatum (G := G) τ hτ_inv H hH hZ hτ_H hτ_tr a ha c Q hQ
    let T := familyTimeReversal m (autDerivationTimeReversal τ hτ_inv)
    HasJReciprocity datum.onsagerPairing T.op ∧
      datum.responseMetric ()
          (finiteCEFrechetFamilyDirection D₁)
          (finiteCEFrechetFamilyDirection D₂) =
        (secondFDerivLogPartitionReadout H
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₁))
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₂))).re := by
  dsimp only
  unfold gibbsNOperatorFamilyAutErlangenDatum
  let PS := finiteGibbsCEFamilyNOperatorParitySystemOfAut τ hτ_inv H hH hZ hτ_H hτ_tr a ha c Q hQ
  have h := gibbsNOperatorFamilyErlangenDatum_reciprocity_and_hessian (G := G) H hH hZ a c Q
    (timeReversalToExchangeInvolution PS.T)
    PS.dissipative_T_even PS.reversible_T_odd D₁ D₂ hD₁
  exact ⟨fun A B s => h.1 A B s, h.2⟩

/-- Concrete `Ad_Γ` specialization of `gibbsNOperatorFamilyAutErlangenDatum`. -/
@[irreducible] def gibbsNOperatorFamilyAdGammaErlangenDatum
    {G : Type*} [Group G] {m n : ℕ}
    (Γ : GibbsOperator n) (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_comm : Commute H Γ)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, Commute (a i) Γ)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_anti : Q * Γ = -(Γ * Q)) :
    ErlangenOperatorDatum ℝ G Unit (FamilyCarrier m n) :=
  gibbsNOperatorFamilyAutErlangenDatum (G := G)
    (adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq)
    (adGammaStarAlgEquiv_involutive Γ hΓ_sa hΓ_sq)
    H hH hZ
    (by
      change Γ * H * Γ = H
      rw [← hH_comm.eq, mul_assoc, hΓ_sq, mul_one])
    (adGammaStarAlgEquiv_trace_re Γ hΓ_sa hΓ_sq)
    a
    (fun i => by
      change Γ * a i * Γ = a i
      rw [← (ha i).eq, mul_assoc, hΓ_sq, mul_one])
    c Q
    (adGammaStarAlgEquiv_odd_of_anticomm Γ Q hΓ_sa hΓ_sq hQ_anti)

@[simp] theorem gibbsNOperatorFamilyAdGammaErlangenDatum_responseMetric
    {G : Type*} [Group G] {m n : ℕ}
    (Γ : GibbsOperator n) (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_comm : Commute H Γ)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, Commute (a i) Γ)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_anti : Q * Γ = -(Γ * Q))
    (s : Unit) (x y : FamilyCarrier m n) :
    (gibbsNOperatorFamilyAdGammaErlangenDatum (G := G)
      Γ hΓ_sa hΓ_sq H hH hZ hH_comm a ha c Q hQ_anti).responseMetric s x y =
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative x y := by
  unfold gibbsNOperatorFamilyAdGammaErlangenDatum
  exact gibbsNOperatorFamilyAutErlangenDatum_responseMetric _ _ H hH hZ _ _ a _ c Q _ s x y

@[simp] theorem gibbsNOperatorFamilyAdGammaErlangenDatum_onsagerPairing
    {G : Type*} [Group G] {m n : ℕ}
    (Γ : GibbsOperator n) (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_comm : Commute H Γ)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, Commute (a i) Γ)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_anti : Q * Γ = -(Γ * Q))
    (s : Unit) (x y : FamilyCarrier m n) :
    (gibbsNOperatorFamilyAdGammaErlangenDatum (G := G)
      Γ hΓ_sa hΓ_sq H hH hZ hH_comm a ha c Q hQ_anti).onsagerPairing s x y =
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).totalGenerator x y := by
  unfold gibbsNOperatorFamilyAdGammaErlangenDatum
  exact gibbsNOperatorFamilyAutErlangenDatum_onsagerPairing _ _ H hH hZ _ _ a _ c Q _ s x y

@[simp] theorem gibbsNOperatorFamilyAdGammaErlangenDatum_casimirJ
    {G : Type*} [Group G] {m n : ℕ}
    (Γ : GibbsOperator n) (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_comm : Commute H Γ)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, Commute (a i) Γ)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_anti : Q * Γ = -(Γ * Q))
    (x : FamilyCarrier m n) :
    (gibbsNOperatorFamilyAdGammaErlangenDatum (G := G)
      Γ hΓ_sa hΓ_sq H hH hZ hH_comm a ha c Q hQ_anti).casimirJ x =
      (familyTimeReversal m (autDerivationTimeReversal (adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq)
        (adGammaStarAlgEquiv_involutive Γ hΓ_sa hΓ_sq))).op x := by
  unfold gibbsNOperatorFamilyAdGammaErlangenDatum
  exact gibbsNOperatorFamilyAutErlangenDatum_casimirJ _ _ H hH hZ _ _ a _ c Q _ x

theorem gibbsNOperatorFamilyAdGammaErlangenDatum_reciprocity_and_hessian
    {G : Type*} [Group G] {m n : ℕ}
    (Γ : GibbsOperator n) (hΓ_sa : IsSelfAdjoint Γ) (hΓ_sq : Γ * Γ = 1)
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_comm : Commute H Γ)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, Commute (a i) Γ)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_anti : Q * Γ = -(Γ * Q))
    (D₁ D₂ : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hD₁ : IsSelfAdjoint
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c (finiteCEFrechetFamilyDirection D₁))) :
    let datum := gibbsNOperatorFamilyAdGammaErlangenDatum (G := G)
      Γ hΓ_sa hΓ_sq H hH hZ hH_comm a ha c Q hQ_anti
    let T := familyTimeReversal m (autDerivationTimeReversal (adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq)
      (adGammaStarAlgEquiv_involutive Γ hΓ_sa hΓ_sq))
    HasJReciprocity datum.onsagerPairing T.op ∧
      datum.responseMetric ()
          (finiteCEFrechetFamilyDirection D₁)
          (finiteCEFrechetFamilyDirection D₂) =
        (secondFDerivLogPartitionReadout H
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₁))
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₂))).re := by
  dsimp only
  unfold gibbsNOperatorFamilyAdGammaErlangenDatum
  exact gibbsNOperatorFamilyAutErlangenDatum_reciprocity_and_hessian (G := G)
    (adGammaStarAlgEquiv Γ hΓ_sa hΓ_sq)
    (adGammaStarAlgEquiv_involutive Γ hΓ_sa hΓ_sq)
    H hH hZ
    (by
      change Γ * H * Γ = H
      rw [← hH_comm.eq, mul_assoc, hΓ_sq, mul_one])
    (adGammaStarAlgEquiv_trace_re Γ hΓ_sa hΓ_sq)
    a
    (fun i => by
      change Γ * a i * Γ = a i
      rw [← (ha i).eq, mul_assoc, hΓ_sq, mul_one])
    c Q
    (adGammaStarAlgEquiv_odd_of_anticomm Γ Q hΓ_sa hΓ_sq hQ_anti)
    D₁ D₂ hD₁

/-- Concrete entrywise conjugation specialization of `gibbsNOperatorFamilyAutErlangenDatum`. -/
@[irreducible] def gibbsNOperatorFamilyConjErlangenDatum
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_real : conjStarAlgEquiv n H = H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, conjStarAlgEquiv n (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_odd : conjStarAlgEquiv n Q = -Q) :
    ErlangenOperatorDatum ℝ G Unit (FamilyCarrier m n) :=
  gibbsNOperatorFamilyAutErlangenDatum (G := G)
    (conjStarAlgEquiv n)
    (conjStarAlgEquiv_involutive (n := n))
    H hH hZ hH_real
    (conjStarAlgEquiv_trace_re (n := n))
    a ha c Q hQ_odd

@[simp] theorem gibbsNOperatorFamilyConjErlangenDatum_responseMetric
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_real : conjStarAlgEquiv n H = H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, conjStarAlgEquiv n (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_odd : conjStarAlgEquiv n Q = -Q)
    (s : Unit) (x y : FamilyCarrier m n) :
    (gibbsNOperatorFamilyConjErlangenDatum (G := G)
      H hH hZ hH_real a ha c Q hQ_odd).responseMetric s x y =
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative x y := by
  unfold gibbsNOperatorFamilyConjErlangenDatum
  exact gibbsNOperatorFamilyAutErlangenDatum_responseMetric _ _ H hH hZ hH_real _ a ha c Q hQ_odd s x y

@[simp] theorem gibbsNOperatorFamilyConjErlangenDatum_onsagerPairing
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_real : conjStarAlgEquiv n H = H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, conjStarAlgEquiv n (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_odd : conjStarAlgEquiv n Q = -Q)
    (s : Unit) (x y : FamilyCarrier m n) :
    (gibbsNOperatorFamilyConjErlangenDatum (G := G)
      H hH hZ hH_real a ha c Q hQ_odd).onsagerPairing s x y =
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).totalGenerator x y := by
  unfold gibbsNOperatorFamilyConjErlangenDatum
  exact gibbsNOperatorFamilyAutErlangenDatum_onsagerPairing _ _ H hH hZ hH_real _ a ha c Q hQ_odd s x y

@[simp] theorem gibbsNOperatorFamilyConjErlangenDatum_casimirJ
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_real : conjStarAlgEquiv n H = H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, conjStarAlgEquiv n (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_odd : conjStarAlgEquiv n Q = -Q)
    (x : FamilyCarrier m n) :
    (gibbsNOperatorFamilyConjErlangenDatum (G := G)
      H hH hZ hH_real a ha c Q hQ_odd).casimirJ x =
      (familyTimeReversal m (autDerivationTimeReversal (conjStarAlgEquiv n)
        (conjStarAlgEquiv_involutive (n := n)))).op x := by
  unfold gibbsNOperatorFamilyConjErlangenDatum
  exact gibbsNOperatorFamilyAutErlangenDatum_casimirJ _ _ H hH hZ hH_real _ a ha c Q hQ_odd x

theorem gibbsNOperatorFamilyConjErlangenDatum_reciprocity_and_hessian
    {G : Type*} [Group G] {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hH_real : conjStarAlgEquiv n H = H)
    (a : Fin m → GibbsOperator n) (ha : ∀ i, conjStarAlgEquiv n (a i) = a i)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (hQ_odd : conjStarAlgEquiv n Q = -Q)
    (D₁ D₂ : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hD₁ : IsSelfAdjoint
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c (finiteCEFrechetFamilyDirection D₁))) :
    let datum := gibbsNOperatorFamilyConjErlangenDatum (G := G) H hH hZ hH_real a ha c Q hQ_odd
    let T := familyTimeReversal m (autDerivationTimeReversal (conjStarAlgEquiv n)
      (conjStarAlgEquiv_involutive (n := n)))
    HasJReciprocity datum.onsagerPairing T.op ∧
      datum.responseMetric ()
          (finiteCEFrechetFamilyDirection D₁)
          (finiteCEFrechetFamilyDirection D₂) =
        (secondFDerivLogPartitionReadout H
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₁))
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₂))).re := by
  dsimp only
  unfold gibbsNOperatorFamilyConjErlangenDatum
  exact gibbsNOperatorFamilyAutErlangenDatum_reciprocity_and_hessian (G := G)
    (conjStarAlgEquiv n)
    (conjStarAlgEquiv_involutive (n := n))
    H hH hZ hH_real
    (conjStarAlgEquiv_trace_re (n := n))
    a ha c Q hQ_odd D₁ D₂ hD₁

end GibbsFamilyAndErlangen

/-! ## Section 6: Arbitrary-Degree Unification across `ceCurvature` and `ParityOnsagerFormPairing` -/

section ArbitraryDegreeCEUnification

/-- Centered BKM real covariance bundled as a `LinearMap.BilinForm ℝ (GibbsOperator n)`. -/
@[irreducible] def centeredBKMRealCovarianceBilin {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) :
    LinearMap.BilinForm ℝ (GibbsOperator n) :=
  (D.bkmRealBilinForm hpow).compl₁₂ (centeringLinearMap D hpow) (centeringLinearMap D hpow)

@[simp] theorem centeredBKMRealCovarianceBilin_apply {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (X Y : GibbsOperator n) :
    centeredBKMRealCovarianceBilin D hpow X Y = centeredBKMRealCovariance D hpow X Y := by
  unfold centeredBKMRealCovarianceBilin
  simp [centeredBKMRealCovariance]

/-- Fixed-probe commutator BKM bilinear form `(X, Y) ↦ g_BKM([X, Y], Q)` on `GibbsOperator n`. -/
@[irreducible] def commutatorBKMProbeForm {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (Q : GibbsOperator n) :
    LinearMap.BilinForm ℝ (GibbsOperator n) :=
  LinearMap.mk₂ ℝ
    (fun X Y => D.bkmRealBilinForm hpow (X * Y - Y * X) Q)
    (fun X₁ X₂ Y => by
      have hsub : (X₁ + X₂) * Y - Y * (X₁ + X₂) = (X₁ * Y - Y * X₁) + (X₂ * Y - Y * X₂) := by
        noncomm_ring
      rw [hsub, map_add, LinearMap.add_apply])
    (fun r X Y => by
      have hsm : (r • X) * Y - Y * (r • X) = r • (X * Y - Y * X) := by
        simp only [real_smul_eq_complex_smul, smul_mul_assoc, mul_smul_comm, smul_sub]
      rw [hsm, map_smul, LinearMap.smul_apply])
    (fun X Y₁ Y₂ => by
      have hsub : X * (Y₁ + Y₂) - (Y₁ + Y₂) * X = (X * Y₁ - Y₁ * X) + (X * Y₂ - Y₂ * X) := by
        noncomm_ring
      rw [hsub, map_add, LinearMap.add_apply])
    (fun r X Y => by
      have hsm : X * (r • Y) - (r • Y) * X = r • (X * Y - Y * X) := by
        simp only [real_smul_eq_complex_smul, mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [hsm, map_smul, LinearMap.smul_apply])

@[simp] theorem commutatorBKMProbeForm_apply {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (Q X Y : GibbsOperator n) :
    commutatorBKMProbeForm D hpow Q X Y = D.bkmRealBilinForm hpow (X * Y - Y * X) Q := by
  unfold commutatorBKMProbeForm
  rfl

theorem commutatorBKMProbeForm_skew {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (Q X Y : GibbsOperator n) :
    commutatorBKMProbeForm D hpow Q X Y = -commutatorBKMProbeForm D hpow Q Y X := by
  simp only [commutatorBKMProbeForm_apply]
  have hneg : X * Y - Y * X = -(Y * X - X * Y) := by noncomm_ring
  rw [hneg, LinearMap.map_neg, LinearMap.neg_apply]

/-- Operator-level `OnsagerCasimirSystem (GibbsOperator n)` with centered BKM dissipation
and commutator BKM probe reversibility. -/
@[irreducible] def centeredBKMOnsagerSystem {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (Q : GibbsOperator n) :
    OnsagerCasimirSystem (GibbsOperator n) where
  dissipative := centeredBKMRealCovarianceBilin D hpow
  reversible := commutatorBKMProbeForm D hpow Q
  dissipative_symm X Y := by
    simp only [centeredBKMRealCovarianceBilin_apply]
    exact centeredBKMRealCovariance_symm D hpow X Y
  reversible_skew := commutatorBKMProbeForm_skew D hpow Q
  dissipative_nonneg X := by
    simp only [centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovariance_self]
    exact D.kuboMoriPairing_self_re_nonneg (centeredStatistic D X) hpow

@[simp] theorem centeredBKMOnsagerSystem_dissipative {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (Q : GibbsOperator n) :
    (centeredBKMOnsagerSystem D hpow Q).dissipative = centeredBKMRealCovarianceBilin D hpow := by
  unfold centeredBKMOnsagerSystem
  rfl

@[simp] theorem centeredBKMOnsagerSystem_reversible {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (Q : GibbsOperator n) :
    (centeredBKMOnsagerSystem D hpow Q).reversible = commutatorBKMProbeForm D hpow Q := by
  unfold centeredBKMOnsagerSystem
  rfl

@[simp] theorem centeredBKMOnsagerSystem_totalGenerator {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (Q : GibbsOperator n)
    (u v : GibbsOperator n) :
    (centeredBKMOnsagerSystem D hpow Q).totalGenerator u v =
      centeredBKMRealCovariance D hpow u v + D.bkmRealBilinForm hpow (u * v - v * u) Q := by
  dsimp [OnsagerCasimirSystem.totalGenerator]
  rw [centeredBKMOnsagerSystem_dissipative, centeredBKMOnsagerSystem_reversible,
    centeredBKMRealCovarianceBilin_apply, commutatorBKMProbeForm_apply]
  rfl

/-- Operator-level `ParityOnsagerSystem (GibbsOperator n)` under `starTimeReversal n`
for a self-adjoint probe `Q`. -/
@[irreducible] def centeredBKMParityOnsagerSystem {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) :
    ParityOnsagerSystem (GibbsOperator n) where
  toOnsagerCasimirSystem := centeredBKMOnsagerSystem D hpow Q
  T := starTimeReversal n
  dissipative_T_even X Y := by
    simp only [centeredBKMOnsagerSystem_dissipative, starTimeReversal_apply,
      centeredBKMRealCovarianceBilin_apply]
    exact centeredBKMRealCovariance_star D hpow X Y
  reversible_T_odd X Y := by
    simp only [centeredBKMOnsagerSystem_reversible, starTimeReversal_apply,
      commutatorBKMProbeForm_apply]
    have hop_sub : ∀ A B : GibbsOperator n, star (A - B) = star A - star B :=
      (finiteOperatorStarRealCLM n).map_sub
    have hst : star X * star Y - star Y * star X = -star (X * Y - Y * X) := by
      rw [hop_sub, StarMul.star_mul, StarMul.star_mul, neg_sub]
    have hb0 := bkmRealBilinForm_star D hpow (X * Y - Y * X) Q
    rw [hQ.star_eq] at hb0
    calc
      D.bkmRealBilinForm hpow (star X * star Y - star Y * star X) Q =
          D.bkmRealBilinForm hpow (-star (X * Y - Y * X)) Q := by rw [hst]
      _ = -D.bkmRealBilinForm hpow (star (X * Y - Y * X)) Q := by
            rw [LinearMap.map_neg, LinearMap.neg_apply]
      _ = -D.bkmRealBilinForm hpow (X * Y - Y * X) Q := by rw [hb0]

@[simp] theorem centeredBKMParityOnsagerSystem_T {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) :
    (centeredBKMParityOnsagerSystem D hpow Q hQ).T = starTimeReversal n := by
  unfold centeredBKMParityOnsagerSystem
  rfl

@[simp] theorem centeredBKMParityOnsagerSystem_dissipative {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) :
    (centeredBKMParityOnsagerSystem D hpow Q hQ).dissipative =
      centeredBKMRealCovarianceBilin D hpow := by
  unfold centeredBKMParityOnsagerSystem
  exact centeredBKMOnsagerSystem_dissipative D hpow Q

@[simp] theorem centeredBKMParityOnsagerSystem_reversible {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) :
    (centeredBKMParityOnsagerSystem D hpow Q hQ).reversible =
      commutatorBKMProbeForm D hpow Q := by
  unfold centeredBKMParityOnsagerSystem
  exact centeredBKMOnsagerSystem_reversible D hpow Q

@[simp] theorem centeredBKMParityOnsagerSystem_totalGenerator {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (u v : GibbsOperator n) :
    (centeredBKMParityOnsagerSystem D hpow Q hQ).totalGenerator u v =
      centeredBKMRealCovariance D hpow u v + D.bkmRealBilinForm hpow (u * v - v * u) Q := by
  dsimp [OnsagerCasimirSystem.totalGenerator]
  rw [centeredBKMParityOnsagerSystem_dissipative, centeredBKMParityOnsagerSystem_reversible,
    centeredBKMRealCovarianceBilin_apply, commutatorBKMProbeForm_apply]
  rfl

/-- Operator-level `ParityOnsagerSystem (GibbsOperator n)` under an involutive
`ℝ`-algebra `*`-automorphism `τ` (`τ D.rho = D.rho`, real-trace preserving, `τ Q = -Q`). -/
@[irreducible] def centeredBKMParityOnsagerSystemOfAut {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) :
    ParityOnsagerSystem (GibbsOperator n) where
  toOnsagerCasimirSystem := centeredBKMOnsagerSystem D hpow Q
  T := autTimeReversal τ hτ_inv
  dissipative_T_even X Y := by
    simp only [centeredBKMOnsagerSystem_dissipative, autTimeReversal_apply,
      centeredBKMRealCovarianceBilin_apply]
    exact centeredBKMRealCovariance_aut τ D hpow hτ_rho hτ_tr X Y
  reversible_T_odd X Y := by
    simp only [centeredBKMOnsagerSystem_reversible, autTimeReversal_apply,
      commutatorBKMProbeForm_apply]
    rw [← map_mul τ, ← map_mul τ, ← map_sub τ]
    have h := bkmRealBilinForm_aut τ D hpow hτ_rho hτ_tr (X * Y - Y * X) (τ Q)
    rw [hτ_inv Q] at h
    rw [h, hQ, LinearMap.map_neg]

@[simp] theorem centeredBKMParityOnsagerSystemOfAut_T {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) :
    (centeredBKMParityOnsagerSystemOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ).T =
      autTimeReversal τ hτ_inv := by
  unfold centeredBKMParityOnsagerSystemOfAut
  rfl

@[simp] theorem centeredBKMParityOnsagerSystemOfAut_dissipative {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) :
    (centeredBKMParityOnsagerSystemOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ).dissipative =
      centeredBKMRealCovarianceBilin D hpow := by
  unfold centeredBKMParityOnsagerSystemOfAut
  exact centeredBKMOnsagerSystem_dissipative D hpow Q

@[simp] theorem centeredBKMParityOnsagerSystemOfAut_reversible {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) :
    (centeredBKMParityOnsagerSystemOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ).reversible =
      commutatorBKMProbeForm D hpow Q := by
  unfold centeredBKMParityOnsagerSystemOfAut
  exact centeredBKMOnsagerSystem_reversible D hpow Q

@[simp] theorem centeredBKMParityOnsagerSystemOfAut_totalGenerator {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) (u v : GibbsOperator n) :
    (centeredBKMParityOnsagerSystemOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ).totalGenerator u v =
      centeredBKMRealCovariance D hpow u v + D.bkmRealBilinForm hpow (u * v - v * u) Q := by
  dsimp [OnsagerCasimirSystem.totalGenerator]
  rw [centeredBKMParityOnsagerSystemOfAut_dissipative,
    centeredBKMParityOnsagerSystemOfAut_reversible,
    centeredBKMRealCovarianceBilin_apply, commutatorBKMProbeForm_apply]
  rfl

/-! ### Additive Combinators for `ParityOnsagerFormPairing` and `DerivationLieLane` -/

/-- Pull back a `ParityOnsagerFormPairing V A m` along a linear value map `f : B →ₗ[ℝ] A`
intertwined with a form `TimeReversal` on `V [⋀^Fin m]→ₗ[ℝ] B`. -/
def parityOnsagerFormPairingMapValues
    {V A B : Type*} {m : ℕ}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    (f : B →ₗ[ℝ] A) (P : ParityOnsagerFormPairing V A m)
    (T_B : TimeReversal (V [⋀^Fin m]→ₗ[ℝ] B))
    (hT : ∀ ω : V [⋀^Fin m]→ₗ[ℝ] B,
      mapValuesFormLM f (T_B.op ω) = P.T.op (mapValuesFormLM f ω)) :
    ParityOnsagerFormPairing V B m where
  toOnsagerFormPairing := P.toOnsagerFormPairing.mapValues f
  T := T_B
  dissipative_T_even ω η := by
    change P.dissipative (mapValuesFormLM f (T_B.op ω)) (mapValuesFormLM f (T_B.op η)) =
      P.dissipative (mapValuesFormLM f ω) (mapValuesFormLM f η)
    rw [hT ω, hT η]
    exact P.dissipative_T_even _ _
  reversible_T_odd ω η := by
    change P.reversible (mapValuesFormLM f (T_B.op ω)) (mapValuesFormLM f (T_B.op η)) =
      -P.reversible (mapValuesFormLM f ω) (mapValuesFormLM f η)
    rw [hT ω, hT η]
    exact P.reversible_T_odd _ _

/-- Specialization of `parityOnsagerFormPairingMapValues` when the form time reversals
are `formTimeReversal` induced by `T_B0 : TimeReversal B` and `T_A0 : TimeReversal A`. -/
def parityOnsagerFormPairingMapValues_ofFormTimeReversal
    {V A B : Type*} {m : ℕ}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    (f : B →ₗ[ℝ] A) (P : OnsagerFormPairing V A m)
    (T_A0 : TimeReversal A) (T_B0 : TimeReversal B)
    (hD_even : ∀ ω η : V [⋀^Fin m]→ₗ[ℝ] A,
      P.dissipative ((formTimeReversal T_A0 m).op ω) ((formTimeReversal T_A0 m).op η) =
        P.dissipative ω η)
    (hR_odd : ∀ ω η : V [⋀^Fin m]→ₗ[ℝ] A,
      P.reversible ((formTimeReversal T_A0 m).op ω) ((formTimeReversal T_A0 m).op η) =
        -P.reversible ω η)
    (hf : ∀ b : B, f (T_B0.op b) = T_A0.op (f b)) :
    ParityOnsagerFormPairing V B m :=
  let PP : ParityOnsagerFormPairing V A m :=
    { toOnsagerFormPairing := P
      T := formTimeReversal T_A0 m
      dissipative_T_even := hD_even
      reversible_T_odd := hR_odd }
  parityOnsagerFormPairingMapValues f PP (formTimeReversal T_B0 m) (fun ω => by
    ext v
    change f (T_B0.op (ω v)) = T_A0.op (f (ω v))
    exact hf (ω v))

/-- Push forward a `ParityOnsagerFormPairing W A m` along `ϕ : W →ₗ[ℝ] V` intertwined
with a `TimeReversal` on `V [⋀^Fin m]→ₗ[ℝ] A`. -/
def parityOnsagerFormPairingPushforward
    {V W A : Type*} {m : ℕ}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [AddCommGroup A] [Module ℝ A]
    (ϕ : W →ₗ[ℝ] V) (P : ParityOnsagerFormPairing W A m)
    (T_V : TimeReversal (V [⋀^Fin m]→ₗ[ℝ] A))
    (hT : ∀ ω : V [⋀^Fin m]→ₗ[ℝ] A,
      pullbackFormLM ϕ (T_V.op ω) = P.T.op (pullbackFormLM ϕ ω)) :
    ParityOnsagerFormPairing V A m where
  toOnsagerFormPairing := P.toOnsagerFormPairing.pushforward ϕ
  T := T_V
  dissipative_T_even ω η := by
    change P.dissipative (pullbackFormLM ϕ (T_V.op ω)) (pullbackFormLM ϕ (T_V.op η)) =
      P.dissipative (pullbackFormLM ϕ ω) (pullbackFormLM ϕ η)
    rw [hT ω, hT η]
    exact P.dissipative_T_even _ _
  reversible_T_odd ω η := by
    change P.reversible (pullbackFormLM ϕ (T_V.op ω)) (pullbackFormLM ϕ (T_V.op η)) =
      -P.reversible (pullbackFormLM ϕ ω) (pullbackFormLM ϕ η)
    rw [hT ω, hT η]
    exact P.reversible_T_odd _ _

/-- Pull a `ParityOnsagerSystem A` back along `x ↦ K.operatorAction x a` to `K.L`
when `T_L : TimeReversal K.L` satisfies `K.operatorAction (T_L.op x) a = ε • PS.T.op (K.operatorAction x a)`. -/
def inducedDerivationLaneParityOnsagerSystem
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (PS : ParityOnsagerSystem A) (K : DerivationLieLane ℝ A) (a : A)
    (T_L : TimeReversal K.L) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hequiv : ∀ x : K.L, K.operatorAction (T_L.op x) a = ε • PS.T.op (K.operatorAction x a)) :
    ParityOnsagerSystem K.L where
  toOnsagerCasimirSystem := inducedDerivationLaneOnsagerSystem PS.toOnsagerCasimirSystem K a
  T := T_L
  dissipative_T_even x y := by
    change PS.dissipative (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![T_L.op x])
        (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![T_L.op y]) =
      PS.dissipative (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![x])
        (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![y])
    have hact : ∀ z : K.L,
        ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![z] = K.operatorAction z a :=
      fun z => actionExteriorDerivative_zero_apply K.toLieActionLane
        (zeroFormAlternatingEquiv K a) ![z]
    rw [hact (T_L.op x), hact (T_L.op y), hact x, hact y, hequiv x, hequiv y]
    rw [PS.dissipative.map_smul, LinearMap.smul_apply, (PS.dissipative _).map_smul,
      PS.dissipative_T_even]
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    simp only [smul_eq_mul]
    calc
      ε * (ε * PS.dissipative (K.operatorAction x a) (K.operatorAction y a)) =
          (ε * ε) * PS.dissipative (K.operatorAction x a) (K.operatorAction y a) := by ring
      _ = PS.dissipative (K.operatorAction x a) (K.operatorAction y a) := by rw [hε2, one_mul]
  reversible_T_odd x y := by
    change PS.reversible (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![T_L.op x])
        (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![T_L.op y]) =
      -PS.reversible (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![x])
        (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![y])
    have hact : ∀ z : K.L,
        ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![z] = K.operatorAction z a :=
      fun z => actionExteriorDerivative_zero_apply K.toLieActionLane
        (zeroFormAlternatingEquiv K a) ![z]
    rw [hact (T_L.op x), hact (T_L.op y), hact x, hact y, hequiv x, hequiv y]
    rw [PS.reversible.map_smul, LinearMap.smul_apply, (PS.reversible _).map_smul,
      PS.reversible_T_odd]
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    simp only [smul_eq_mul, mul_neg]
    congr 1
    calc
      ε * (ε * PS.reversible (K.operatorAction x a) (K.operatorAction y a)) =
          (ε * ε) * PS.reversible (K.operatorAction x a) (K.operatorAction y a) := by ring
      _ = PS.reversible (K.operatorAction x a) (K.operatorAction y a) := by rw [hε2, one_mul]

/-- The induced `ParityOnsagerSystem` from `centeredBKMParityOnsagerSystem` along
`realDerivationsLane (GibbsOperator n)` agrees pointwise with `finiteCEParityOnsagerSystem`
for `dissipative`, `reversible`, and `totalGenerator`. -/
theorem inducedDerivationLaneParityOnsagerSystem_eq_finiteCE {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a Q : GibbsOperator n) (ha : IsSelfAdjoint a) (hQ : IsSelfAdjoint Q)
    (x y : Carrier n) :
    let K := realDerivationsLane (GibbsOperator n)
    let PS_ind := inducedDerivationLaneParityOnsagerSystem
      (centeredBKMParityOnsagerSystem D hpow Q hQ) K a
      (starDerivationTimeReversal n) (Or.inl rfl)
      (fun z => by
        rw [centeredBKMParityOnsagerSystem_T, starTimeReversal_apply, one_smul]
        change star (carrierEnd z (star a)) = star (carrierEnd z a)
        rw [ha.star_eq])
    let PS_ce := finiteCEParityOnsagerSystem D hpow a Q ha hQ
    PS_ind.totalGenerator x y = PS_ce.totalGenerator x y := by
  intro K PS_ind PS_ce
  have h0 : PS_ind.totalGenerator x y =
      (centeredBKMParityOnsagerSystem D hpow Q hQ).totalGenerator
        (K.operatorAction x a) (K.operatorAction y a) :=
    inducedDerivationLaneOnsagerSystem_totalGenerator
      (centeredBKMParityOnsagerSystem D hpow Q hQ).toOnsagerCasimirSystem K a x y
  have hop : ∀ z : Carrier n, K.operatorAction z a = finiteCEOperatorForm n a z := fun _ => rfl
  have hcurv :
      connectionCurvature (realDerivationsLane (GibbsOperator n))
          (exteriorDerivativeZero (realDerivationsLane (GibbsOperator n)) a) x y =
        finiteCEOperatorForm n a x * finiteCEOperatorForm n a y -
          finiteCEOperatorForm n a y * finiteCEOperatorForm n a x := by
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    rfl
  change PS_ind.totalGenerator x y =
    centeredCEBKMForm D hpow a x y + ceCurvatureBKMProbeForm D hpow a Q x y
  rw [h0, centeredBKMParityOnsagerSystem_totalGenerator,
    centeredCEBKMForm_apply, ceCurvatureBKMProbeForm_apply, hop x, hop y, hcurv]

/-! ### Arbitrary-Degree `DerivationOperatorForm` Lifts & `ceCurvature` Degree-2 Bridge -/

/-- Lift `centeredBKMParityOnsagerSystem` to arbitrary-degree `DerivationOperatorForm`
via `ParityOnsagerFormPairing.ofValueParity`. -/
@[irreducible] def centeredBKMOnsagerFormPairing_ofValueParity {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (v : Fin m → Carrier n) :
    ParityOnsagerFormPairing (Carrier n) (GibbsOperator n) m :=
  ParityOnsagerFormPairing.ofValueParity (centeredBKMParityOnsagerSystem D hpow Q hQ) v

@[simp] theorem centeredBKMOnsagerFormPairing_ofValueParity_T {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) (v : Fin m → Carrier n) :
    (centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ v).T =
      formTimeReversal (starTimeReversal n) m := by
  unfold centeredBKMOnsagerFormPairing_ofValueParity
  change formTimeReversal (centeredBKMParityOnsagerSystem D hpow Q hQ).T m = _
  rw [centeredBKMParityOnsagerSystem_T]

@[simp] theorem centeredBKMOnsagerFormPairing_ofValueParity_dissipative {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) (v : Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ v).dissipative ω η =
      centeredBKMRealCovariance D hpow (ω v) (η v) := by
  unfold centeredBKMOnsagerFormPairing_ofValueParity
  change (centeredBKMParityOnsagerSystem D hpow Q hQ).dissipative (ω v) (η v) = _
  rw [centeredBKMParityOnsagerSystem_dissipative, centeredBKMRealCovarianceBilin_apply]

@[simp] theorem centeredBKMOnsagerFormPairing_ofValueParity_reversible {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) (v : Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ v).reversible ω η =
      commutatorBKMProbeForm D hpow Q (ω v) (η v) := by
  unfold centeredBKMOnsagerFormPairing_ofValueParity
  change (centeredBKMParityOnsagerSystem D hpow Q hQ).reversible (ω v) (η v) = _
  rw [centeredBKMParityOnsagerSystem_reversible]

@[simp] theorem centeredBKMOnsagerFormPairing_ofValueParity_totalGenerator {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) (v : Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ v).totalGenerator ω η =
      centeredBKMRealCovariance D hpow (ω v) (η v) +
        commutatorBKMProbeForm D hpow Q (ω v) (η v) := by
  dsimp [OnsagerCasimirSystem.totalGenerator]
  rw [centeredBKMOnsagerFormPairing_ofValueParity_dissipative,
    centeredBKMOnsagerFormPairing_ofValueParity_reversible]

/-- Lift `centeredBKMParityOnsagerSystem` to arbitrary-degree `DerivationOperatorForm`
via `ParityOnsagerFormPairing.ofWeightedValueParity`. -/
@[irreducible] def centeredBKMOnsagerFormPairing_ofWeightedValueParity {n m : ℕ} {ι : Type*} [Fintype ι]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (frames : ι → Fin m → Carrier n) :
    ParityOnsagerFormPairing (Carrier n) (GibbsOperator n) m :=
  ParityOnsagerFormPairing.ofWeightedValueParity
    (centeredBKMParityOnsagerSystem D hpow Q hQ) w hw frames

@[simp] theorem centeredBKMOnsagerFormPairing_ofWeightedValueParity_T {n m : ℕ} {ι : Type*} [Fintype ι]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (frames : ι → Fin m → Carrier n) :
    (centeredBKMOnsagerFormPairing_ofWeightedValueParity D hpow Q hQ w hw frames).T =
      formTimeReversal (starTimeReversal n) m := by
  unfold centeredBKMOnsagerFormPairing_ofWeightedValueParity
  change formTimeReversal (centeredBKMParityOnsagerSystem D hpow Q hQ).T m = _
  rw [centeredBKMParityOnsagerSystem_T]

@[simp] theorem centeredBKMOnsagerFormPairing_ofWeightedValueParity_dissipative
    {n m : ℕ} {ι : Type*} [Fintype ι]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (frames : ι → Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairing_ofWeightedValueParity D hpow Q hQ w hw frames).dissipative ω η =
      ∑ i : ι, w i * centeredBKMRealCovariance D hpow (ω (frames i)) (η (frames i)) := by
  unfold centeredBKMOnsagerFormPairing_ofWeightedValueParity
  change (∑ i : ι, w i • (centeredBKMParityOnsagerSystem D hpow Q hQ).dissipative.compl₁₂
      (evalAlternatingForm (Carrier n) (GibbsOperator n) m (frames i))
      (evalAlternatingForm (Carrier n) (GibbsOperator n) m (frames i))) ω η = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
    evalAlternatingForm_apply, centeredBKMParityOnsagerSystem_dissipative,
    centeredBKMRealCovarianceBilin_apply, smul_eq_mul]

@[simp] theorem centeredBKMOnsagerFormPairing_ofWeightedValueParity_reversible
    {n m : ℕ} {ι : Type*} [Fintype ι]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (frames : ι → Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairing_ofWeightedValueParity D hpow Q hQ w hw frames).reversible ω η =
      ∑ i : ι, w i * commutatorBKMProbeForm D hpow Q (ω (frames i)) (η (frames i)) := by
  unfold centeredBKMOnsagerFormPairing_ofWeightedValueParity
  change (∑ i : ι, w i • (centeredBKMParityOnsagerSystem D hpow Q hQ).reversible.compl₁₂
      (evalAlternatingForm (Carrier n) (GibbsOperator n) m (frames i))
      (evalAlternatingForm (Carrier n) (GibbsOperator n) m (frames i))) ω η = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
    evalAlternatingForm_apply, centeredBKMParityOnsagerSystem_reversible, smul_eq_mul]

@[simp] theorem centeredBKMOnsagerFormPairing_ofWeightedValueParity_totalGenerator
    {n m : ℕ} {ι : Type*} [Fintype ι]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (frames : ι → Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairing_ofWeightedValueParity D hpow Q hQ w hw frames).totalGenerator ω η =
      (∑ i : ι, w i * centeredBKMRealCovariance D hpow (ω (frames i)) (η (frames i))) +
        ∑ i : ι, w i * commutatorBKMProbeForm D hpow Q (ω (frames i)) (η (frames i)) := by
  dsimp [OnsagerCasimirSystem.totalGenerator]
  rw [centeredBKMOnsagerFormPairing_ofWeightedValueParity_dissipative,
    centeredBKMOnsagerFormPairing_ofWeightedValueParity_reversible]

/-- Unconditional domain-orbit lift of `centeredBKMOnsagerSystem` with
`starDerivationTimeReversal n` to arbitrary-degree `DerivationOperatorForm`. -/
@[irreducible] def centeredBKMOnsagerFormPairing_ofDomainOrbit {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (v : Fin m → Carrier n) :
    ParityOnsagerFormPairing (Carrier n) (GibbsOperator n) m :=
  ParityOnsagerFormPairing.ofDomainOrbit
    (centeredBKMOnsagerSystem D hpow Q) (starDerivationTimeReversal n) v

@[simp] theorem centeredBKMOnsagerFormPairing_ofDomainOrbit_T {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (v : Fin m → Carrier n) :
    (centeredBKMOnsagerFormPairing_ofDomainOrbit D hpow Q v).T =
      domainFormTimeReversal (starDerivationTimeReversal n) m := by
  unfold centeredBKMOnsagerFormPairing_ofDomainOrbit
  rfl

@[simp] theorem centeredBKMOnsagerFormPairing_ofDomainOrbit_dissipative {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (v : Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairing_ofDomainOrbit D hpow Q v).dissipative ω η =
      centeredBKMRealCovariance D hpow (ω v) (η v) +
        centeredBKMRealCovariance D hpow
          (ω (fun i => starDerivation (v i)))
          (η (fun i => starDerivation (v i))) := by
  unfold centeredBKMOnsagerFormPairing_ofDomainOrbit ParityOnsagerFormPairing.ofDomainOrbit
  simp only [LinearMap.BilinForm.add_apply, LinearMap.compl₁₂_apply, evalAlternatingForm_apply,
    centeredBKMOnsagerSystem_dissipative, centeredBKMRealCovarianceBilin_apply,
    starDerivationTimeReversal_apply]

@[simp] theorem centeredBKMOnsagerFormPairing_ofDomainOrbit_reversible {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (v : Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairing_ofDomainOrbit D hpow Q v).reversible ω η =
      commutatorBKMProbeForm D hpow Q (ω v) (η v) -
        commutatorBKMProbeForm D hpow Q
          (ω (fun i => starDerivation (v i)))
          (η (fun i => starDerivation (v i))) := by
  unfold centeredBKMOnsagerFormPairing_ofDomainOrbit ParityOnsagerFormPairing.ofDomainOrbit
  simp only [LinearMap.sub_apply, LinearMap.compl₁₂_apply, evalAlternatingForm_apply,
    centeredBKMOnsagerSystem_reversible, starDerivationTimeReversal_apply]

@[simp] theorem centeredBKMOnsagerFormPairing_ofDomainOrbit_totalGenerator {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (v : Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairing_ofDomainOrbit D hpow Q v).totalGenerator ω η =
      (centeredBKMRealCovariance D hpow (ω v) (η v) +
        centeredBKMRealCovariance D hpow
          (ω (fun i => starDerivation (v i)))
          (η (fun i => starDerivation (v i)))) +
      (commutatorBKMProbeForm D hpow Q (ω v) (η v) -
        commutatorBKMProbeForm D hpow Q
          (ω (fun i => starDerivation (v i)))
          (η (fun i => starDerivation (v i)))) := by
  dsimp [OnsagerCasimirSystem.totalGenerator]
  rw [centeredBKMOnsagerFormPairing_ofDomainOrbit_dissipative,
    centeredBKMOnsagerFormPairing_ofDomainOrbit_reversible]

/-- Lift `centeredBKMParityOnsagerSystemOfAut` to arbitrary-degree `DerivationOperatorForm`. -/
@[irreducible] def centeredBKMOnsagerFormPairingOfAut_ofValueParity {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q)
    (v : Fin m → Carrier n) :
    ParityOnsagerFormPairing (Carrier n) (GibbsOperator n) m :=
  ParityOnsagerFormPairing.ofValueParity
    (centeredBKMParityOnsagerSystemOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ) v

@[simp] theorem centeredBKMOnsagerFormPairingOfAut_ofValueParity_T {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) (v : Fin m → Carrier n) :
    (centeredBKMOnsagerFormPairingOfAut_ofValueParity
      τ hτ_inv D hpow hτ_rho hτ_tr Q hQ v).T =
      formTimeReversal (autTimeReversal τ hτ_inv) m := by
  unfold centeredBKMOnsagerFormPairingOfAut_ofValueParity
  change formTimeReversal
      (centeredBKMParityOnsagerSystemOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ).T m = _
  rw [centeredBKMParityOnsagerSystemOfAut_T]

@[simp] theorem centeredBKMOnsagerFormPairingOfAut_ofValueParity_dissipative {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) (v : Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairingOfAut_ofValueParity
      τ hτ_inv D hpow hτ_rho hτ_tr Q hQ v).dissipative ω η =
      centeredBKMRealCovariance D hpow (ω v) (η v) := by
  unfold centeredBKMOnsagerFormPairingOfAut_ofValueParity
  change (centeredBKMParityOnsagerSystemOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ).dissipative
      (ω v) (η v) = _
  rw [centeredBKMParityOnsagerSystemOfAut_dissipative, centeredBKMRealCovarianceBilin_apply]

@[simp] theorem centeredBKMOnsagerFormPairingOfAut_ofValueParity_reversible {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) (v : Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairingOfAut_ofValueParity
      τ hτ_inv D hpow hτ_rho hτ_tr Q hQ v).reversible ω η =
      commutatorBKMProbeForm D hpow Q (ω v) (η v) := by
  unfold centeredBKMOnsagerFormPairingOfAut_ofValueParity
  change (centeredBKMParityOnsagerSystemOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ).reversible
      (ω v) (η v) = _
  rw [centeredBKMParityOnsagerSystemOfAut_reversible]

@[simp] theorem centeredBKMOnsagerFormPairingOfAut_ofValueParity_totalGenerator {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) (v : Fin m → Carrier n)
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    (centeredBKMOnsagerFormPairingOfAut_ofValueParity
      τ hτ_inv D hpow hτ_rho hτ_tr Q hQ v).totalGenerator ω η =
      centeredBKMRealCovariance D hpow (ω v) (η v) +
        commutatorBKMProbeForm D hpow Q (ω v) (η v) := by
  dsimp [OnsagerCasimirSystem.totalGenerator]
  rw [centeredBKMOnsagerFormPairingOfAut_ofValueParity_dissipative,
    centeredBKMOnsagerFormPairingOfAut_ofValueParity_reversible]

/-- Arbitrary-degree master reciprocity for `ceExteriorDerivative` on `GibbsOperator n`. -/
theorem centeredBKM_ceExteriorDerivative_reciprocity {n m : ℕ}
    (PP : ParityOnsagerFormPairing (Carrier n) (GibbsOperator n) (m + 1))
    (ω η : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) m) :
    PP.totalGenerator
        (PP.T.op (ceExteriorDerivative (realDerivationsLane (GibbsOperator n)) m ω))
        (PP.T.op (ceExteriorDerivative (realDerivationsLane (GibbsOperator n)) m η)) =
      PP.totalGenerator
        (ceExteriorDerivative (realDerivationsLane (GibbsOperator n)) m η)
        (ceExteriorDerivative (realDerivationsLane (GibbsOperator n)) m ω) :=
  onsager_pairing_ceExteriorDerivative_reciprocity
    (realDerivationsLane (GibbsOperator n)) m PP ω η

/-- Arbitrary-degree master reciprocity for `ceWedge` on `GibbsOperator n`. -/
theorem centeredBKM_ceWedge_reciprocity {n p q : ℕ}
    (PP : ParityOnsagerFormPairing (Carrier n) (GibbsOperator n) (p + q))
    (ω₁ : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) p)
    (η₁ : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) q)
    (ω₂ : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) p)
    (η₂ : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) q) :
    PP.totalGenerator
        (PP.T.op (ceWedge (realDerivationsLane (GibbsOperator n)) ω₁ η₁))
        (PP.T.op (ceWedge (realDerivationsLane (GibbsOperator n)) ω₂ η₂)) =
      PP.totalGenerator
        (ceWedge (realDerivationsLane (GibbsOperator n)) ω₂ η₂)
        (ceWedge (realDerivationsLane (GibbsOperator n)) ω₁ η₁) :=
  onsager_pairing_ceWedge_reciprocity
    (realDerivationsLane (GibbsOperator n)) PP ω₁ η₁ ω₂ η₂

/-- Degree-2 master reciprocity for `ceCurvature` on `GibbsOperator n`. -/
theorem centeredBKM_ceCurvature_reciprocity {n : ℕ}
    (PP : ParityOnsagerFormPairing (Carrier n) (GibbsOperator n) 2)
    (Γ₁ Γ₂ : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) 1) :
    PP.totalGenerator
        (PP.T.op (ceCurvature (realDerivationsLane (GibbsOperator n)) Γ₁))
        (PP.T.op (ceCurvature (realDerivationsLane (GibbsOperator n)) Γ₂)) =
      PP.totalGenerator
        (ceCurvature (realDerivationsLane (GibbsOperator n)) Γ₂)
        (ceCurvature (realDerivationsLane (GibbsOperator n)) Γ₁) :=
  onsager_pairing_ceCurvature_reciprocity
    (realDerivationsLane (GibbsOperator n)) PP Γ₁ Γ₂

/-- Degree-2 `ceCurvature` on `oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K a)`
evaluates on `![x, y]` to the connection curvature `(x a) * (y a) - (y a) * (x a)`,
directly supplying the probe argument of `CEBKMOnsagerSystem.ceCurvatureBKMProbeForm`. -/
theorem ceCurvature_exteriorDerivativeZero_bkmProbe_eq {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a Q : GibbsOperator n) (x y : Carrier n) :
    let K := realDerivationsLane (GibbsOperator n)
    let Γ := exteriorDerivativeZero K a
    D.bkmRealBilinForm hpow (ceCurvature K (oneFormAlternatingLinearEquiv K Γ) ![x, y]) Q =
      ceCurvatureBKMProbeForm D hpow a Q x y := by
  intro K Γ
  rw [ceCurvature_eq K Γ, twoCochainEquivDerivationOperatorForm_apply]
  rfl

/-- Degree-2 `ParityOnsagerFormPairing` evaluation of `ceCurvature` on exact 1-forms
connects directly to `commutatorBKMProbeForm` and satisfies master Onsager–Casimir
reciprocity under `centeredBKMOnsagerFormPairing_ofValueParity`. -/
theorem ceCurvature_degree2_parity_bridge {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (a b Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (x y : Carrier n) :
    let K := realDerivationsLane (GibbsOperator n)
    let Γ₁ := oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K a)
    let Γ₂ := oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K b)
    (centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ ![x, y]).reversible
        (ceCurvature K Γ₁) (ceCurvature K Γ₂) =
        commutatorBKMProbeForm D hpow Q
          (connectionCurvature K (exteriorDerivativeZero K a) x y)
          (connectionCurvature K (exteriorDerivativeZero K b) x y) ∧
      (centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ ![x, y]).totalGenerator
          ((centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ ![x, y]).T.op
            (ceCurvature K Γ₁))
          ((centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ ![x, y]).T.op
            (ceCurvature K Γ₂)) =
        (centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ ![x, y]).totalGenerator
          (ceCurvature K Γ₂) (ceCurvature K Γ₁) := by
  intro K Γ₁ Γ₂
  refine ⟨?_, centeredBKM_ceCurvature_reciprocity
    (centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ ![x, y]) Γ₁ Γ₂⟩
  rw [centeredBKMOnsagerFormPairing_ofValueParity_reversible,
    ceCurvature_eq K (exteriorDerivativeZero K a),
    ceCurvature_eq K (exteriorDerivativeZero K b),
    twoCochainEquivDerivationOperatorForm_apply,
    twoCochainEquivDerivationOperatorForm_apply]
  rfl

end ArbitraryDegreeCEUnification

/-! ## Section 7: `OperatorFrechetForms` Unification (`SmoothOpMap`, `RealOperatorFrechetForm`, `logPartitionOneForm`) -/

section OperatorFrechetUnification

/-- Point evaluation `f ↦ f H` on `SmoothOpMap 𝕜 A` as a `𝕜`-algebra homomorphism. -/
def smoothOpMapEvalAlgHom {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] (H : A) :
    SmoothOpMap 𝕜 A →ₐ[𝕜] A where
  toFun f := f H
  map_one' := SmoothOpMap.one_apply H
  map_mul' f g := SmoothOpMap.mul_apply f g H
  map_zero' := SmoothOpMap.zero_apply H
  map_add' f g := SmoothOpMap.add_apply f g H
  commutes' _ := rfl

@[simp] theorem smoothOpMapEvalAlgHom_apply {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] (H : A) (f : SmoothOpMap 𝕜 A) :
    smoothOpMapEvalAlgHom H f = f H :=
  rfl

/-- Point evaluation `f ↦ f H` on `SmoothOpMap ℝ A` as an `ℝ`-linear map. -/
def smoothOpMapEvalLM {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] (H : A) :
    SmoothOpMap ℝ A →ₗ[ℝ] A :=
  (smoothOpMapEvalAlgHom H).toLinearMap

@[simp] theorem smoothOpMapEvalLM_apply {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (H : A) (f : SmoothOpMap ℝ A) :
    smoothOpMapEvalLM H f = f H :=
  rfl

/-- Post-composition by `star` on `SmoothOpMap ℝ (GibbsOperator n)` as a `TimeReversal`. -/
def starSmoothOpTimeReversal (n : ℕ) : TimeReversal (SmoothOpMap ℝ (GibbsOperator n)) where
  op :=
    { toFun := fun f =>
        ⟨fun x => star (f x), (finiteOperatorStarRealCLM n).contDiff.comp f.contDiff⟩
      map_add' := fun f g => SmoothOpMap.ext fun x => star_add (f x) (g x)
      map_smul' := fun r f => SmoothOpMap.ext fun x => by
        change star (r • f x) = r • star (f x)
        rw [← finiteOperatorStarRealCLM_apply (n := n), map_smul, finiteOperatorStarRealCLM_apply] }
  involutive f := SmoothOpMap.ext fun x => star_star (f x)

@[simp] theorem starSmoothOpTimeReversal_apply {n : ℕ}
    (f : SmoothOpMap ℝ (GibbsOperator n)) (x : GibbsOperator n) :
    ((starSmoothOpTimeReversal n).op f) x = star (f x) :=
  rfl

theorem smoothOpMapEvalLM_starSmoothOpTimeReversal {n : ℕ}
    (H : GibbsOperator n) (f : SmoothOpMap ℝ (GibbsOperator n)) :
    smoothOpMapEvalLM H ((starSmoothOpTimeReversal n).op f) =
      (starTimeReversal n).op (smoothOpMapEvalLM H f) :=
  rfl

/-- Post-composition by an involutive `ℝ`-algebra `*`-automorphism `τ` on
`SmoothOpMap ℝ (GibbsOperator n)` as a `TimeReversal`. -/
def autSmoothOpTimeReversal {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X) :
    TimeReversal (SmoothOpMap ℝ (GibbsOperator n)) where
  op :=
    let τLM : GibbsOperator n →ₗ[ℝ] GibbsOperator n :=
      { toFun := τ, map_add' := map_add τ, map_smul' := map_smul τ }
    let τCLM : GibbsOperator n →L[ℝ] GibbsOperator n :=
      τLM.toContinuousLinearMap
    { toFun := fun f =>
        ⟨fun x => τ (f x), τCLM.contDiff.comp f.contDiff⟩
      map_add' := fun f g => SmoothOpMap.ext fun x => map_add τ (f x) (g x)
      map_smul' := fun r f => SmoothOpMap.ext fun x => map_smul τ r (f x) }
  involutive f := SmoothOpMap.ext fun x => hτ_inv (f x)

@[simp] theorem autSmoothOpTimeReversal_apply {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (f : SmoothOpMap ℝ (GibbsOperator n)) (x : GibbsOperator n) :
    ((autSmoothOpTimeReversal τ hτ_inv).op f) x = τ (f x) :=
  rfl

theorem smoothOpMapEvalLM_autSmoothOpTimeReversal {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : GibbsOperator n) (f : SmoothOpMap ℝ (GibbsOperator n)) :
    smoothOpMapEvalLM H ((autSmoothOpTimeReversal τ hτ_inv).op f) =
      (autTimeReversal τ hτ_inv).op (smoothOpMapEvalLM H f) :=
  rfl

/-! ### `Module ℝ (GibbsOperator n)` `ContDiff` Diamond Helpers -/

/-- Any `ℝ`-linear map out of `GibbsOperator n` is `C^∞`-smooth, avoiding the
`realOperatorModule` vs `realOperatorNormedSpace` `Module ℝ` instance diamond on
`ContinuousLinearMap.mul ℝ (GibbsOperator n)`. -/
theorem contDiff_realLinearMap_gibbsOperator {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : GibbsOperator n → F)
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (r : ℝ) x, f (r • x) = r • f x) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) f := by
  let _ : NormedSpace ℝ (GibbsOperator n) := realOperatorNormedSpace n
  let L : GibbsOperator n →ₗ[ℝ] F :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun r x => by
        change f ((r : ℂ) • x) = r • f x
        rw [← real_smul_eq_complex_smul r x]
        exact hsmul r x }
  have hcont : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hb : IsBoundedLinearMap ℝ f :=
    ({ toLinearMap := L, cont := hcont } : GibbsOperator n →L[ℝ] F).isBoundedLinearMap
  exact hb.contDiff

/-- Left multiplication `X ↦ H * X` as a continuous `ℝ`-linear operator on `GibbsOperator n`,
bypassing `ContinuousLinearMap.mul ℝ (GibbsOperator n)`'s `Module ℝ` diamond. -/
def leftMulRealCLM {n : ℕ} (H : GibbsOperator n) :
    GibbsOperator n →L[ℝ] GibbsOperator n :=
  { toLinearMap :=
      { toFun := fun X => H * X
        map_add' := fun X Y => mul_add H X Y
        map_smul' := fun r X => by
          simp only [RingHom.id_apply]
          rw [real_smul_eq_complex_smul, mul_smul_comm, ← real_smul_eq_complex_smul] }
    cont :=
      let L : GibbsOperator n →ₗ[ℝ] GibbsOperator n :=
        { toFun := fun X => H * X
          map_add' := fun X Y => mul_add H X Y
          map_smul' := fun r X => by
            simp only [RingHom.id_apply]
            rw [real_smul_eq_complex_smul, mul_smul_comm, ← real_smul_eq_complex_smul] }
      LinearMap.continuous_of_finiteDimensional L }

@[simp] theorem leftMulRealCLM_apply {n : ℕ} (H X : GibbsOperator n) :
    leftMulRealCLM H X = H * X :=
  rfl

/-- `H ↦ leftMulRealCLM H` is `C^∞`-smooth on `GibbsOperator n`. -/
theorem contDiff_leftMul_gibbsOperator (n : ℕ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (leftMulRealCLM (n := n)) :=
  contDiff_realLinearMap_gibbsOperator leftMulRealCLM
    (fun H₁ H₂ => by
      apply ContinuousLinearMap.ext
      intro X
      change (H₁ + H₂) * X = H₁ * X + H₂ * X
      exact add_mul H₁ H₂ X)
    (fun r H => by
      apply ContinuousLinearMap.ext
      intro X
      change (r • H) * X = (r : ℂ) • (H * X)
      rw [real_smul_eq_complex_smul, smul_mul_assoc])

/-- Concrete non-constant smooth `RealOperatorFrechetForm` of degree 1:
`H ↦ (X ↦ H * X)`. -/
def smoothLeftMulOneForm (n : ℕ) :
    RealOperatorFrechetForm (GibbsOperator n) (GibbsOperator n) (GibbsOperator n) 1 :=
  fun H => ContinuousAlternatingMap.ofSubsingleton ℝ (GibbsOperator n) (GibbsOperator n)
    (0 : Fin 1) (leftMulRealCLM H)

@[simp] theorem smoothLeftMulOneForm_apply {n : ℕ} (H X : GibbsOperator n) :
    smoothLeftMulOneForm n H ![X] = H * X :=
  rfl

/-- `smoothLeftMulOneForm n` is `C^∞`-smooth without hitting the `Module ℝ` instance diamond. -/
theorem contDiff_smoothLeftMulOneForm (n : ℕ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (smoothLeftMulOneForm n) :=
  contDiff_realLinearMap_gibbsOperator (smoothLeftMulOneForm n)
    (fun H₁ H₂ => by
      apply ContinuousAlternatingMap.ext
      intro v
      change (H₁ + H₂) * v 0 = H₁ * v 0 + H₂ * v 0
      exact add_mul H₁ H₂ (v 0))
    (fun r H => by
      apply ContinuousAlternatingMap.ext
      intro v
      change (r • H) * v 0 = (r : ℂ) • (H * v 0)
      rw [real_smul_eq_complex_smul, smul_mul_assoc])

/-- Exact Fréchet exterior derivative of `smoothLeftMulOneForm n`:
`d_Fr(H ↦ (X ↦ H * X))_H(u, v) = u * v - v * u`. -/
theorem frechetExtDerivReal_smoothLeftMulOneForm {n : ℕ}
    (H u v : GibbsOperator n) :
    frechetExtDerivReal (smoothLeftMulOneForm n) H ![u, v] = u * v - v * u := by
  rw [frechetExtDerivReal, frechetExtDerivK_apply
    ((contDiff_smoothLeftMulOneForm n).differentiable (by simp) H)]
  rw [Fin.sum_univ_two]
  have h0 : (0 : Fin 2).removeNth ![u, v] = ![v] := by
    ext i; fin_cases i; rfl
  have h1 : (1 : Fin 2).removeNth ![u, v] = ![u] := by
    ext i; fin_cases i; rfl
  have hf : ∀ w : GibbsOperator n,
      fderiv ℝ (fun y : GibbsOperator n => smoothLeftMulOneForm n y ![w]) H =
        { toLinearMap :=
            { toFun := fun y => y * w
              map_add' := fun y₁ y₂ => add_mul y₁ y₂ w
              map_smul' := fun r y => by
                simp only [RingHom.id_apply]
                rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul] }
          cont :=
            LinearMap.continuous_of_finiteDimensional
              ({ toFun := fun y => y * w
                 map_add' := fun y₁ y₂ => add_mul y₁ y₂ w
                 map_smul' := fun r y => by
                   simp only [RingHom.id_apply]
                   rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul] } :
                GibbsOperator n →ₗ[ℝ] GibbsOperator n) } := fun w => by
    let Rw : GibbsOperator n →L[ℝ] GibbsOperator n :=
      { toLinearMap :=
          { toFun := fun y => y * w
            map_add' := fun y₁ y₂ => add_mul y₁ y₂ w
            map_smul' := fun r y => by
              simp only [RingHom.id_apply]
              rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul] }
        cont :=
          LinearMap.continuous_of_finiteDimensional
            ({ toFun := fun y => y * w
               map_add' := fun y₁ y₂ => add_mul y₁ y₂ w
               map_smul' := fun r y => by
                 simp only [RingHom.id_apply]
                 rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul] } :
              GibbsOperator n →ₗ[ℝ] GibbsOperator n) }
    have hfun : (fun y : GibbsOperator n => smoothLeftMulOneForm n y ![w]) = Rw := by
      funext y
      exact smoothLeftMulOneForm_apply y w
    rw [hfun]
    exact Rw.fderiv
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    h0, h1, Matrix.cons_val_zero, Matrix.cons_val_one, hf]
  change u * v + -(v * u) = u * v - v * u
  rw [sub_eq_add_neg]

/-- Forget smoothness to transport `FrechetVectorField ℝ (GibbsOperator n)` linearly
into `Carrier n = (realDerivationsLane (GibbsOperator n)).L`.
Note: `FrechetVectorField` uses the opposite Lie bracket (`VectorField.lieBracket`), so this
is an `ℝ`-linear map for `pullbackFormLM`, not a `LieHom`. -/
def frechetVectorFieldToCarrier {n : ℕ} :
    FrechetVectorField ℝ (GibbsOperator n) →ₗ[ℝ] Carrier n where
  toFun D := FrechetBridge.toRealDerivation D.toDerivation
  map_add' D E := by
    apply Subtype.ext
    ext x
    rfl
  map_smul' r D := by
    apply Subtype.ext
    ext x
    rfl

@[simp] theorem frechetVectorFieldToCarrier_apply {n : ℕ}
    (D : FrechetVectorField ℝ (GibbsOperator n)) (x : GibbsOperator n) :
    (frechetVectorFieldToCarrier D).1 x = D.toDerivation x :=
  rfl

/-- Lift a complex continuous derivation `D : FrechetOperatorDerivation ℂ (GibbsOperator n)`
into `FrechetVectorField ℝ (GibbsOperator n)`. -/
def frechetVectorFieldFromComplex {n : ℕ}
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n)) :
    FrechetVectorField ℝ (GibbsOperator n) :=
  ⟨restrictScalarsReal D⟩

@[simp] theorem frechetVectorFieldToCarrier_fromComplex {n : ℕ}
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n)) :
    frechetVectorFieldToCarrier (frechetVectorFieldFromComplex D) =
      finiteCEFrechetDirection D :=
  rfl

/-- Commutative evaluation square relating:
1. `mapValuesFormLM (smoothOpMapEvalLM H) (frechetFormToCEForm m ω hω)` on `FrechetVectorField ℝ A`,
2. direct evaluation of `ω H` on `(D i) H`, and
3. `pullbackFormLM (finiteCEOperatorForm n H) (ω H).toAlternatingMap` on `finiteCEFrechetDirection (D i)`. -/
theorem frechetForm_eval_eq_pullback {n m : ℕ}
    (ω : RealOperatorFrechetForm (GibbsOperator n) (GibbsOperator n) (GibbsOperator n) m)
    (hω : ContDiff ℝ (⊤ : WithTop ℕ∞) ω)
    (H : GibbsOperator n)
    (D : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n)) :
    mapValuesFormLM (smoothOpMapEvalLM H) (frechetFormToCEForm m ω hω)
        (fun i => frechetVectorFieldFromComplex (D i)) =
      ω H (fun i => D i H) ∧
    pullbackFormLM (finiteCEOperatorForm n H) (ω H).toAlternatingMap
        (fun i => finiteCEFrechetDirection (D i)) =
      ω H (fun i => D i H) := by
  constructor
  · change smoothOpMapEvalLM H (frechetFormToCEForm m ω hω
        (fun i => frechetVectorFieldFromComplex (D i))) = _
    rw [smoothOpMapEvalLM_apply, frechetFormToCEForm_apply]
    rfl
  · rw [pullbackFormLM_apply]
    rfl

/-- Compatibility of `frechetExtDerivReal` with `ceExteriorDerivative` after
pointwise evaluation `mapValuesFormLM (smoothOpMapEvalLM H)`. -/
theorem frechetExtDerivReal_eval_eq_ceExteriorDerivative {n m : ℕ}
    (ω : RealOperatorFrechetForm (GibbsOperator n) (GibbsOperator n) (GibbsOperator n) m)
    (hω : ContDiff ℝ (⊤ : WithTop ℕ∞) ω) (H : GibbsOperator n) :
    mapValuesFormLM (smoothOpMapEvalLM H)
        (frechetFormToCEForm (m + 1) (frechetExtDerivReal ω) (contDiff_frechetExtDerivK hω)) =
      mapValuesFormLM (smoothOpMapEvalLM H)
        (ceExteriorDerivative (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)) m
          (frechetFormToCEForm m ω hω)) := by
  unfold frechetExtDerivReal
  rw [frechetExtDerivK_linear_eq_ceExteriorDerivative]

/-- Lift `centeredBKMParityOnsagerSystem` via `parityOnsagerFormPairingMapValues`
along `smoothOpMapEvalLM H` to a `ParityOnsagerFormPairing` on
`DerivationOperatorForm (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)) m`. -/
@[irreducible] def frechetFormParityOnsagerPairing {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L) :
    ParityOnsagerFormPairing
      (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L
      (SmoothOpMap ℝ (GibbsOperator n)) m :=
  parityOnsagerFormPairingMapValues_ofFormTimeReversal
    (smoothOpMapEvalLM H)
    (OnsagerFormPairing.ofFrame (centeredBKMOnsagerSystem D hpow Q) v)
    (starTimeReversal n)
    (starSmoothOpTimeReversal n)
    (fun ω η => by
      simp only [OnsagerFormPairing.ofFrame_dissipative, formTimeReversal_apply,
        starTimeReversal_apply, centeredBKMOnsagerSystem_dissipative,
        centeredBKMRealCovarianceBilin_apply]
      exact centeredBKMRealCovariance_star D hpow (ω v) (η v))
    (fun ω η => by
      simp only [OnsagerFormPairing.ofFrame_reversible, formTimeReversal_apply,
        starTimeReversal_apply]
      have h := (centeredBKMParityOnsagerSystem D hpow Q hQ).reversible_T_odd (ω v) (η v)
      simpa only [centeredBKMParityOnsagerSystem_reversible, centeredBKMParityOnsagerSystem_T,
        starTimeReversal_apply, centeredBKMOnsagerSystem_reversible] using h)
    (smoothOpMapEvalLM_starSmoothOpTimeReversal H)

@[simp] theorem frechetFormParityOnsagerPairing_T {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L) :
    (frechetFormParityOnsagerPairing D hpow Q hQ H v).T =
      formTimeReversal (starSmoothOpTimeReversal n) m := by
  unfold frechetFormParityOnsagerPairing
  rfl

@[simp] theorem frechetFormParityOnsagerPairing_dissipative {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : DerivationOperatorForm (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)) m) :
    (frechetFormParityOnsagerPairing D hpow Q hQ H v).dissipative ω η =
      centeredBKMRealCovariance D hpow ((ω v) H) ((η v) H) := by
  unfold frechetFormParityOnsagerPairing
  change (centeredBKMOnsagerSystem D hpow Q).dissipative ((ω v) H) ((η v) H) = _
  rw [centeredBKMOnsagerSystem_dissipative, centeredBKMRealCovarianceBilin_apply]

@[simp] theorem frechetFormParityOnsagerPairing_reversible {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : DerivationOperatorForm (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)) m) :
    (frechetFormParityOnsagerPairing D hpow Q hQ H v).reversible ω η =
      commutatorBKMProbeForm D hpow Q ((ω v) H) ((η v) H) := by
  unfold frechetFormParityOnsagerPairing
  change (centeredBKMOnsagerSystem D hpow Q).reversible ((ω v) H) ((η v) H) = _
  rw [centeredBKMOnsagerSystem_reversible]

@[simp] theorem frechetFormParityOnsagerPairing_totalGenerator {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q) (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : DerivationOperatorForm (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)) m) :
    (frechetFormParityOnsagerPairing D hpow Q hQ H v).totalGenerator ω η =
      centeredBKMRealCovariance D hpow ((ω v) H) ((η v) H) +
        commutatorBKMProbeForm D hpow Q ((ω v) H) ((η v) H) := by
  dsimp [OnsagerCasimirSystem.totalGenerator]
  rw [frechetFormParityOnsagerPairing_dissipative,
    frechetFormParityOnsagerPairing_reversible]

/-- Lift `centeredBKMParityOnsagerSystemOfAut` via `parityOnsagerFormPairingMapValues`
along `smoothOpMapEvalLM H` to a `ParityOnsagerFormPairing` on
`DerivationOperatorForm (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)) m`
under `autSmoothOpTimeReversal τ hτ_inv`. -/
@[irreducible] def frechetFormParityOnsagerPairingOfAut {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q)
    (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L) :
    ParityOnsagerFormPairing
      (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L
      (SmoothOpMap ℝ (GibbsOperator n)) m :=
  parityOnsagerFormPairingMapValues_ofFormTimeReversal
    (smoothOpMapEvalLM H)
    (OnsagerFormPairing.ofFrame (centeredBKMOnsagerSystem D hpow Q) v)
    (autTimeReversal τ hτ_inv)
    (autSmoothOpTimeReversal τ hτ_inv)
    (fun ω η => by
      simp only [OnsagerFormPairing.ofFrame_dissipative, formTimeReversal_apply,
        autTimeReversal_apply, centeredBKMOnsagerSystem_dissipative,
        centeredBKMRealCovarianceBilin_apply]
      exact centeredBKMRealCovariance_aut τ D hpow hτ_rho hτ_tr (ω v) (η v))
    (fun ω η => by
      simp only [OnsagerFormPairing.ofFrame_reversible, formTimeReversal_apply,
        autTimeReversal_apply]
      have h := (centeredBKMParityOnsagerSystemOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ).reversible_T_odd
        (ω v) (η v)
      simpa only [centeredBKMParityOnsagerSystemOfAut_reversible,
        centeredBKMParityOnsagerSystemOfAut_T, autTimeReversal_apply,
        centeredBKMOnsagerSystem_reversible] using h)
    (smoothOpMapEvalLM_autSmoothOpTimeReversal τ hτ_inv H)

@[simp] theorem frechetFormParityOnsagerPairingOfAut_T {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L) :
    (frechetFormParityOnsagerPairingOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ H v).T =
      formTimeReversal (autSmoothOpTimeReversal τ hτ_inv) m := by
  unfold frechetFormParityOnsagerPairingOfAut
  rfl

@[simp] theorem frechetFormParityOnsagerPairingOfAut_dissipative {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : DerivationOperatorForm (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)) m) :
    (frechetFormParityOnsagerPairingOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ H v).dissipative ω η =
      centeredBKMRealCovariance D hpow ((ω v) H) ((η v) H) := by
  unfold frechetFormParityOnsagerPairingOfAut
  change (centeredBKMOnsagerSystem D hpow Q).dissipative ((ω v) H) ((η v) H) = _
  rw [centeredBKMOnsagerSystem_dissipative, centeredBKMRealCovarianceBilin_apply]

@[simp] theorem frechetFormParityOnsagerPairingOfAut_reversible {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : DerivationOperatorForm (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)) m) :
    (frechetFormParityOnsagerPairingOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ H v).reversible ω η =
      commutatorBKMProbeForm D hpow Q ((ω v) H) ((η v) H) := by
  unfold frechetFormParityOnsagerPairingOfAut
  change (centeredBKMOnsagerSystem D hpow Q).reversible ((ω v) H) ((η v) H) = _
  rw [centeredBKMOnsagerSystem_reversible]

@[simp] theorem frechetFormParityOnsagerPairingOfAut_totalGenerator {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q) (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : DerivationOperatorForm (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)) m) :
    (frechetFormParityOnsagerPairingOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ H v).totalGenerator ω η =
      centeredBKMRealCovariance D hpow ((ω v) H) ((η v) H) +
        commutatorBKMProbeForm D hpow Q ((ω v) H) ((η v) H) := by
  dsimp [OnsagerCasimirSystem.totalGenerator]
  rw [frechetFormParityOnsagerPairingOfAut_dissipative,
    frechetFormParityOnsagerPairingOfAut_reversible]

/-- Master Onsager–Casimir reciprocity for smooth `RealOperatorFrechetForm`s lifted via `frechetFormToCEForm`. -/
theorem frechetFormParityOnsagerPairing_reciprocity {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : RealOperatorFrechetForm (GibbsOperator n) (GibbsOperator n) (GibbsOperator n) m)
    (hω : ContDiff ℝ (⊤ : WithTop ℕ∞) ω)
    (hη : ContDiff ℝ (⊤ : WithTop ℕ∞) η) :
    let PP := frechetFormParityOnsagerPairing D hpow Q hQ H v
    PP.totalGenerator (PP.T.op (frechetFormToCEForm m ω hω))
        (PP.T.op (frechetFormToCEForm m η hη)) =
      PP.totalGenerator (frechetFormToCEForm m η hη) (frechetFormToCEForm m ω hω) :=
  onsager_pairing_derivationForm_reciprocity
    (frechetVectorFieldDerivationLane ℝ (GibbsOperator n))
    (frechetFormParityOnsagerPairing D hpow Q hQ H v)
    (frechetFormToCEForm m ω hω) (frechetFormToCEForm m η hη)

/-- Master Onsager–Casimir reciprocity for smooth `RealOperatorFrechetForm`s under
`frechetFormParityOnsagerPairingOfAut` (`autSmoothOpTimeReversal`). -/
theorem frechetFormParityOnsagerPairingOfAut_reciprocity {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q)
    (H : GibbsOperator n)
    (v : Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : RealOperatorFrechetForm (GibbsOperator n) (GibbsOperator n) (GibbsOperator n) m)
    (hω : ContDiff ℝ (⊤ : WithTop ℕ∞) ω)
    (hη : ContDiff ℝ (⊤ : WithTop ℕ∞) η) :
    let PP := frechetFormParityOnsagerPairingOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ H v
    PP.totalGenerator (PP.T.op (frechetFormToCEForm m ω hω))
        (PP.T.op (frechetFormToCEForm m η hη)) =
      PP.totalGenerator (frechetFormToCEForm m η hη) (frechetFormToCEForm m ω hω) :=
  onsager_pairing_derivationForm_reciprocity
    (frechetVectorFieldDerivationLane ℝ (GibbsOperator n))
    (frechetFormParityOnsagerPairingOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ H v)
    (frechetFormToCEForm m ω hω) (frechetFormToCEForm m η hη)

/-- Master Onsager–Casimir reciprocity on `frechetExtDerivReal ω`, `frechetExtDerivReal η`
matching `ceExteriorDerivative` via `frechetExtDerivK_linear_eq_ceExteriorDerivative`. -/
theorem frechetExtDerivReal_parityOnsager_reciprocity {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (Q : GibbsOperator n) (hQ : IsSelfAdjoint Q)
    (H : GibbsOperator n)
    (v : Fin (m + 1) → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : RealOperatorFrechetForm (GibbsOperator n) (GibbsOperator n) (GibbsOperator n) m)
    (hω : ContDiff ℝ (⊤ : WithTop ℕ∞) ω)
    (hη : ContDiff ℝ (⊤ : WithTop ℕ∞) η) :
    let K := frechetVectorFieldDerivationLane ℝ (GibbsOperator n)
    let PP := frechetFormParityOnsagerPairing D hpow Q hQ H v
    PP.totalGenerator
        (PP.T.op (frechetFormToCEForm (m + 1) (frechetExtDerivReal ω) (contDiff_frechetExtDerivK hω)))
        (PP.T.op (frechetFormToCEForm (m + 1) (frechetExtDerivReal η) (contDiff_frechetExtDerivK hη))) =
      PP.totalGenerator
        (ceExteriorDerivative K m (frechetFormToCEForm m η hη))
        (ceExteriorDerivative K m (frechetFormToCEForm m ω hω)) := by
  intro K PP
  unfold frechetExtDerivReal
  rw [frechetExtDerivK_linear_eq_ceExteriorDerivative,
    frechetExtDerivK_linear_eq_ceExteriorDerivative]
  exact onsager_pairing_ceExteriorDerivative_reciprocity K m PP
    (frechetFormToCEForm m ω hω) (frechetFormToCEForm m η hη)

/-- Master Onsager–Casimir reciprocity on `frechetExtDerivReal ω`, `frechetExtDerivReal η`
under `frechetFormParityOnsagerPairingOfAut`. -/
theorem frechetExtDerivReal_parityOnsagerOfAut_reciprocity {n m : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (hτ_rho : τ D.rho = D.rho)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (Q : GibbsOperator n) (hQ : τ Q = -Q)
    (H : GibbsOperator n)
    (v : Fin (m + 1) → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L)
    (ω η : RealOperatorFrechetForm (GibbsOperator n) (GibbsOperator n) (GibbsOperator n) m)
    (hω : ContDiff ℝ (⊤ : WithTop ℕ∞) ω)
    (hη : ContDiff ℝ (⊤ : WithTop ℕ∞) η) :
    let K := frechetVectorFieldDerivationLane ℝ (GibbsOperator n)
    let PP := frechetFormParityOnsagerPairingOfAut τ hτ_inv D hpow hτ_rho hτ_tr Q hQ H v
    PP.totalGenerator
        (PP.T.op (frechetFormToCEForm (m + 1) (frechetExtDerivReal ω) (contDiff_frechetExtDerivK hω)))
        (PP.T.op (frechetFormToCEForm (m + 1) (frechetExtDerivReal η) (contDiff_frechetExtDerivK hη))) =
      PP.totalGenerator
        (ceExteriorDerivative K m (frechetFormToCEForm m η hη))
        (ceExteriorDerivative K m (frechetFormToCEForm m ω hω)) := by
  intro K PP
  unfold frechetExtDerivReal
  rw [frechetExtDerivK_linear_eq_ceExteriorDerivative,
    frechetExtDerivK_linear_eq_ceExteriorDerivative]
  exact onsager_pairing_ceExteriorDerivative_reciprocity K m PP
    (frechetFormToCEForm m ω hω) (frechetFormToCEForm m η hη)

/-- Real-part projection of a `ℂ`-valued `OperatorFrechetForm A T ℂ m` into
`RealOperatorFrechetForm A T ℝ m`. -/
def complexFrechetFormRe {A T : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedSpace ℂ A]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedSpace ℂ T]
    {m : ℕ} (ω : OperatorFrechetForm A T ℂ m) :
    RealOperatorFrechetForm A T ℝ m :=
  fun x =>
    { toContinuousMultilinearMap :=
        Complex.reCLM.compContinuousMultilinearMap
          ((ω x).toContinuousMultilinearMap.restrictScalars ℝ)
      map_eq_zero_of_eq' := fun v i j hv hij => by
        simp [(ω x).map_eq_zero_of_eq v hv hij] }

@[simp] theorem complexFrechetFormRe_apply {A T : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedSpace ℂ A]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedSpace ℂ T]
    {m : ℕ} (ω : OperatorFrechetForm A T ℂ m) (x : A) (v : Fin m → T) :
    complexFrechetFormRe ω x v = (ω x v).re :=
  rfl

/-- Full unification of degree-1 `logPartitionOneForm`, `operatorFrechetJet`,
`frechetExtDeriv_logPartition_bkmHessian_alignment`, and `finiteGibbsCEParityOnsagerSystem`
(under `starDerivationTimeReversal`).

Note on reversible-curvature degeneracy under `star`: because `hA₁ : IsSelfAdjoint A₁`,
`hA₂ : IsSelfAdjoint A₂`, and `hQ : IsSelfAdjoint Q` force `[A₁, A₂]` to be anti-self-adjoint,
`PS.reversible x₁ x₂ = 0` holds identically across all valid inputs
(`logPartitionOneForm_finiteGibbs_star_unification_reversible_eq_zero`). For genuinely
non-degenerate simultaneous positive Hessian and nonzero reversible curvature, use
`logPartitionOneForm_finiteGibbs_aut_unification` with a `τ`-odd anti-self-adjoint probe `Q`
(`logPartitionOneForm_finiteGibbs_aut_unification_nondegenerate_witness`). -/
theorem logPartitionOneForm_finiteGibbs_star_unification {n : ℕ}
    (H a Q : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (ha : IsSelfAdjoint a) (hQ : IsSelfAdjoint Q)
    (D₁ D₂ : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hA₁ : IsSelfAdjoint (finiteCEOperatorForm n a (finiteCEFrechetDirection D₁)))
    (hA₂ : IsSelfAdjoint (finiteCEOperatorForm n a (finiteCEFrechetDirection D₂))) :
    let x₁ := finiteCEFrechetDirection D₁
    let x₂ := finiteCEFrechetDirection D₂
    let A₁ := finiteCEOperatorForm n a x₁
    let A₂ := finiteCEOperatorForm n a x₂
    let PS := finiteGibbsCEParityOnsagerSystem H hH hZ a Q ha hQ
    (A₁ = operatorFrechetJet 1 (D₁ : GibbsOperator n → GibbsOperator n) H (fun _ => a) ∧
     A₂ = operatorFrechetJet 1 (D₂ : GibbsOperator n → GibbsOperator n) H (fun _ => a)) ∧
    complexFrechetFormRe (logPartitionOneForm n) H ![A₁] =
      expectationReal (faithfulGibbsDensity H hH hZ) A₁ ∧
    frechetExtDeriv (logPartitionOneForm n) H ![A₁, A₂] = 0 ∧
    (secondFDerivLogPartitionReadout H A₁ A₂).re = PS.dissipative x₁ x₂ ∧
    PS.totalGenerator (PS.T.op x₁) (PS.T.op x₂) = PS.totalGenerator x₂ x₁ := by
  intro x₁ x₂ A₁ A₂ PS
  have hjet₁ : A₁ = operatorFrechetJet 1 (D₁ : GibbsOperator n → GibbsOperator n) H (fun _ => a) := by
    change finiteCEOperatorForm n a (finiteCEFrechetDirection D₁) = _
    rw [finiteCEOperatorForm, component_apply]
    exact (operatorFrechetJet_one_apply_eq_exteriorDerivativeZero D₁ H a).symm
  have hjet₂ : A₂ = operatorFrechetJet 1 (D₂ : GibbsOperator n → GibbsOperator n) H (fun _ => a) := by
    change finiteCEOperatorForm n a (finiteCEFrechetDirection D₂) = _
    rw [finiteCEOperatorForm, component_apply]
    exact (operatorFrechetJet_one_apply_eq_exteriorDerivativeZero D₂ H a).symm
  have hexp :
      complexFrechetFormRe (logPartitionOneForm n) H ![A₁] =
        expectationReal (faithfulGibbsDensity H hH hZ) A₁ := by
    rw [complexFrechetFormRe_apply]
    change (logTracedExponentialDerivative H A₁).re = _
    rw [logTracedExponentialDerivative_apply_eq_expectation,
      operatorExpectation_eq_faithfulGibbsDensity_expectation H hH hZ A₁]
    rfl
  have halign := frechetExtDeriv_logPartition_bkmHessian_alignment H hH hZ A₁ A₂ hA₁ hA₂
  have hdiss :
      (secondFDerivLogPartitionReadout H A₁ A₂).re = PS.dissipative x₁ x₂ :=
    finiteGibbsCEOnsagerSystem_dissipative_eq_logPartitionHessian H a Q hH hZ D₁ D₂ hA₁
  exact ⟨⟨hjet₁, hjet₂⟩, hexp, halign.1, hdiss, PS.onsager_casimir_master_reciprocity x₁ x₂⟩

/-- Companion structural degeneracy theorem for `logPartitionOneForm_finiteGibbs_star_unification`:
whenever `Q`, `A₁`, and `A₂` are all self-adjoint, the reversible curvature term
`(finiteGibbsCEParityOnsagerSystem H hH hZ a Q ha hQ).reversible x₁ x₂` vanishes identically. -/
theorem logPartitionOneForm_finiteGibbs_star_unification_reversible_eq_zero {n : ℕ}
    (H a Q : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (ha : IsSelfAdjoint a) (hQ : IsSelfAdjoint Q)
    (D₁ D₂ : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hA₁ : IsSelfAdjoint (finiteCEOperatorForm n a (finiteCEFrechetDirection D₁)))
    (hA₂ : IsSelfAdjoint (finiteCEOperatorForm n a (finiteCEFrechetDirection D₂))) :
    let x₁ := finiteCEFrechetDirection D₁
    let x₂ := finiteCEFrechetDirection D₂
    let PS := finiteGibbsCEParityOnsagerSystem H hH hZ a Q ha hQ
    PS.reversible x₁ x₂ = 0 := by
  intro x₁ x₂ PS
  let D := faithfulGibbsDensity H hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
  change ceCurvatureBKMProbeForm D hpow a Q x₁ x₂ = 0
  rw [ceCurvatureBKMProbeForm_apply]
  have hcurv :
      connectionCurvature (realDerivationsLane (GibbsOperator n))
          (exteriorDerivativeZero (realDerivationsLane (GibbsOperator n)) a) x₁ x₂ =
        finiteCEOperatorForm n a x₁ * finiteCEOperatorForm n a x₂ -
          finiteCEOperatorForm n a x₂ * finiteCEOperatorForm n a x₁ := by
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    rfl
  rw [hcurv]
  have hop_sub : ∀ A B : GibbsOperator n, star (A - B) = star A - star B :=
    (finiteOperatorStarRealCLM n).map_sub
  have hstar_comm :
      star (finiteCEOperatorForm n a x₁ * finiteCEOperatorForm n a x₂ -
          finiteCEOperatorForm n a x₂ * finiteCEOperatorForm n a x₁) =
        -(finiteCEOperatorForm n a x₁ * finiteCEOperatorForm n a x₂ -
            finiteCEOperatorForm n a x₂ * finiteCEOperatorForm n a x₁) := by
    rw [hop_sub, StarMul.star_mul, StarMul.star_mul,
      hA₁.star_eq, hA₂.star_eq, neg_sub]
  have hb := bkmRealBilinForm_star D hpow
    (finiteCEOperatorForm n a x₁ * finiteCEOperatorForm n a x₂ -
      finiteCEOperatorForm n a x₂ * finiteCEOperatorForm n a x₁) Q
  rw [hstar_comm, hQ.star_eq, LinearMap.map_neg, LinearMap.neg_apply] at hb
  linarith

/-- Full unification of degree-1 `logPartitionOneForm`, `operatorFrechetJet`,
`frechetExtDeriv_logPartition_bkmHessian_alignment`, and `finiteGibbsCEParityOnsagerSystemOfAut`
(under an involutive `ℝ`-algebra `*`-automorphism `τ`). -/
theorem logPartitionOneForm_finiteGibbs_aut_unification {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H a Q : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (ha : τ a = a) (hQ : τ Q = -Q)
    (D₁ D₂ : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hA₁ : IsSelfAdjoint (finiteCEOperatorForm n a (finiteCEFrechetDirection D₁)))
    (hA₂ : IsSelfAdjoint (finiteCEOperatorForm n a (finiteCEFrechetDirection D₂))) :
    let x₁ := finiteCEFrechetDirection D₁
    let x₂ := finiteCEFrechetDirection D₂
    let A₁ := finiteCEOperatorForm n a x₁
    let A₂ := finiteCEOperatorForm n a x₂
    let PS := finiteGibbsCEParityOnsagerSystemOfAut τ hτ_inv H hH hZ hτ_H hτ_tr a Q ha hQ
    (A₁ = operatorFrechetJet 1 (D₁ : GibbsOperator n → GibbsOperator n) H (fun _ => a) ∧
     A₂ = operatorFrechetJet 1 (D₂ : GibbsOperator n → GibbsOperator n) H (fun _ => a)) ∧
    complexFrechetFormRe (logPartitionOneForm n) H ![A₁] =
      expectationReal (faithfulGibbsDensity H hH hZ) A₁ ∧
    frechetExtDeriv (logPartitionOneForm n) H ![A₁, A₂] = 0 ∧
    (secondFDerivLogPartitionReadout H A₁ A₂).re = PS.dissipative x₁ x₂ ∧
    PS.totalGenerator (PS.T.op x₁) (PS.T.op x₂) = PS.totalGenerator x₂ x₁ := by
  intro x₁ x₂ A₁ A₂ PS
  have hjet₁ : A₁ = operatorFrechetJet 1 (D₁ : GibbsOperator n → GibbsOperator n) H (fun _ => a) := by
    change finiteCEOperatorForm n a (finiteCEFrechetDirection D₁) = _
    rw [finiteCEOperatorForm, component_apply]
    exact (operatorFrechetJet_one_apply_eq_exteriorDerivativeZero D₁ H a).symm
  have hjet₂ : A₂ = operatorFrechetJet 1 (D₂ : GibbsOperator n → GibbsOperator n) H (fun _ => a) := by
    change finiteCEOperatorForm n a (finiteCEFrechetDirection D₂) = _
    rw [finiteCEOperatorForm, component_apply]
    exact (operatorFrechetJet_one_apply_eq_exteriorDerivativeZero D₂ H a).symm
  have hexp :
      complexFrechetFormRe (logPartitionOneForm n) H ![A₁] =
        expectationReal (faithfulGibbsDensity H hH hZ) A₁ := by
    rw [complexFrechetFormRe_apply]
    change (logTracedExponentialDerivative H A₁).re = _
    rw [logTracedExponentialDerivative_apply_eq_expectation,
      operatorExpectation_eq_faithfulGibbsDensity_expectation H hH hZ A₁]
    rfl
  have halign := frechetExtDeriv_logPartition_bkmHessian_alignment H hH hZ A₁ A₂ hA₁ hA₂
  have hdiss :
      (secondFDerivLogPartitionReadout H A₁ A₂).re = PS.dissipative x₁ x₂ :=
    finiteGibbsCEOnsagerSystem_dissipative_eq_logPartitionHessian H a Q hH hZ D₁ D₂ hA₁
  exact ⟨⟨hjet₁, hjet₂⟩, hexp, halign.1, hdiss, PS.onsager_casimir_master_reciprocity x₁ x₂⟩

/-- Concrete complex inner derivation `u ↦ X * u - u * X` as a
`FrechetOperatorDerivation ℂ (GibbsOperator n)`. -/
def innerFrechetComplexDeriv {n : ℕ} (X : GibbsOperator n) :
    FrechetOperatorDerivation ℂ (GibbsOperator n) where
  toContinuousLinearMap :=
    ContinuousLinearMap.mul ℂ (GibbsOperator n) X -
      (ContinuousLinearMap.mul ℂ (GibbsOperator n)).flip X
  leibniz u v := by
    change X * (u * v) - (u * v) * X = (X * u - u * X) * v + u * (X * v - v * X)
    simp only [sub_mul, mul_sub, mul_assoc]
    abel

@[simp] theorem innerFrechetComplexDeriv_apply {n : ℕ} (X u : GibbsOperator n) :
    innerFrechetComplexDeriv X u = X * u - u * X :=
  rfl

end OperatorFrechetUnification

/-! ## Section 8: Default-Budget Verification & Non-Degeneracy Witnesses (`200000` heartbeats, `512` rec depth) -/

section DefaultBudgetStressTests

set_option synthInstance.maxHeartbeats 20000
set_option maxHeartbeats 200000
set_option maxRecDepth 512

/-- Non-degenerate concrete `n = 2` witness for `logPartitionOneForm_finiteGibbs_aut_unification`
(using `conjStarAlgEquiv 2`, `H = tiltOp2`, `a = switchOp2`, `Q = Complex.I • switchOp2`)
elaborating at default `maxHeartbeats 200000` and proving simultaneously
`0 < (secondFDerivLogPartitionReadout ...).re` AND `PS.reversible x₁ x₂ < 0`. -/
theorem logPartitionOneForm_finiteGibbs_aut_unification_nondegenerate_witness :
    let hZ := InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge.tracedExponential_re_pos_of_isSelfAdjoint
      tiltOp2 tiltOp2_isSelfAdjoint
    let τ := conjStarAlgEquiv 2
    let Q := Complex.I • switchOp2
    let D₁ := innerFrechetComplexDeriv (Complex.I • tiltOp2)
    let D₂ := innerFrechetComplexDeriv (Complex.I • tiltOp2 + tiltOp2 * switchOp2)
    let x₁ := finiteCEFrechetDirection D₁
    let x₂ := finiteCEFrechetDirection D₂
    let A₁ := finiteCEOperatorForm 2 switchOp2 x₁
    let A₂ := finiteCEOperatorForm 2 switchOp2 x₂
    let PS := finiteGibbsCEParityOnsagerSystemOfAut τ (conjStarAlgEquiv_involutive (n := 2))
      tiltOp2 tiltOp2_isSelfAdjoint hZ conj_tiltOp2 (conjStarAlgEquiv_trace_re (n := 2))
      switchOp2 Q conj_switchOp2 (conjStarAlgEquiv_purelyImaginary_odd switchOp2 conj_switchOp2)
    (0 < (secondFDerivLogPartitionReadout tiltOp2 A₁ A₂).re) ∧
      (PS.reversible x₁ x₂ < 0) ∧
      (PS.totalGenerator (PS.T.op x₁) (PS.T.op x₂) = PS.totalGenerator x₂ x₁) := by
  intro hZ τ Q D₁ D₂ x₁ x₂ A₁ A₂ PS
  have hi_sa : IsSelfAdjoint (Complex.I • (tiltOp2 * switchOp2)) := by
    rw [isSelfAdjoint_iff, star_smul, Complex.star_def, Complex.conj_I,
      StarMul.star_mul, tiltOp2_isSelfAdjoint.star_eq, switchOp2_isSelfAdjoint.star_eq]
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    rw [hsw, smul_neg, neg_smul, neg_neg]
  have h_sa_smul : ∀ (r : ℝ) {X : GibbsOperator 2}, IsSelfAdjoint X → IsSelfAdjoint (r • X) :=
    fun r X hX => by
      rw [isSelfAdjoint_iff, real_smul_eq_complex_smul, star_smul, Complex.star_def,
        Complex.conj_ofReal, hX.star_eq]
  have hA₁_eq : A₁ = (2 * Complex.I) • (tiltOp2 * switchOp2) := by
    change (Complex.I • tiltOp2) * switchOp2 - switchOp2 * (Complex.I • tiltOp2) = _
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    rw [smul_mul_assoc, mul_smul_comm, hsw, smul_neg, sub_neg_eq_add,
      ← two_smul ℂ (Complex.I • (tiltOp2 * switchOp2)), smul_smul]
  have hA₁_sa : IsSelfAdjoint A₁ := by
    rw [hA₁_eq, show (2 * Complex.I) • (tiltOp2 * switchOp2) =
      (2 : ℝ) • (Complex.I • (tiltOp2 * switchOp2)) by
      rw [real_smul_eq_complex_smul, smul_smul]; norm_cast]
    exact h_sa_smul (2 : ℝ) hi_sa
  have hA₂_eq : A₂ = A₁ + (2 : ℝ) • tiltOp2 := by
    have hcomm : (tiltOp2 * switchOp2) * switchOp2 - switchOp2 * (tiltOp2 * switchOp2) =
        (2 : ℝ) • tiltOp2 := by
      have h1 : (tiltOp2 * switchOp2) * switchOp2 = tiltOp2 := by
        rw [mul_assoc, switchOp2_sq, mul_one]
      have h2 : switchOp2 * (tiltOp2 * switchOp2) = -tiltOp2 := by
        have hop : (-(tiltOp2 * switchOp2)) * switchOp2 = -((tiltOp2 * switchOp2) * switchOp2) :=
          ContinuousLinearMap.ext fun _ => rfl
        calc
          switchOp2 * (tiltOp2 * switchOp2) = (switchOp2 * tiltOp2) * switchOp2 := by rw [mul_assoc]
          _ = (-(tiltOp2 * switchOp2)) * switchOp2 := by rw [tiltOp2_switchOp2_anticomm, neg_neg]
          _ = -((tiltOp2 * switchOp2) * switchOp2) := hop
          _ = -tiltOp2 := by rw [mul_assoc, switchOp2_sq, mul_one]
      rw [h1, h2, sub_neg_eq_add, ← two_smul ℝ tiltOp2]
    change (Complex.I • tiltOp2 + tiltOp2 * switchOp2) * switchOp2 -
        switchOp2 * (Complex.I • tiltOp2 + tiltOp2 * switchOp2) = A₁ + (2 : ℝ) • tiltOp2
    rw [add_mul, mul_add]
    have hsub : ((Complex.I • tiltOp2) * switchOp2 + (tiltOp2 * switchOp2) * switchOp2) -
        (switchOp2 * (Complex.I • tiltOp2) + switchOp2 * (tiltOp2 * switchOp2)) =
        ((Complex.I • tiltOp2) * switchOp2 - switchOp2 * (Complex.I • tiltOp2)) +
          ((tiltOp2 * switchOp2) * switchOp2 - switchOp2 * (tiltOp2 * switchOp2)) := by
      abel
    rw [hsub, hcomm]
    rfl
  have hA₂_sa : IsSelfAdjoint A₂ := by
    have hop_add : ∀ A B : GibbsOperator 2, star (A + B) = star A + star B :=
      (finiteOperatorStarRealCLM 2).map_add
    rw [hA₂_eq, isSelfAdjoint_iff, hop_add, hA₁_sa.star_eq,
      (h_sa_smul (2 : ℝ) tiltOp2_isSelfAdjoint).star_eq]
  have huni := logPartitionOneForm_finiteGibbs_aut_unification τ (conjStarAlgEquiv_involutive (n := 2))
    tiltOp2 switchOp2 Q tiltOp2_isSelfAdjoint hZ conj_tiltOp2 (conjStarAlgEquiv_trace_re (n := 2))
    conj_switchOp2 (conjStarAlgEquiv_purelyImaginary_odd switchOp2 conj_switchOp2)
    D₁ D₂ hA₁_sa hA₂_sa
  let D := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ
  let hpow := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint hZ
  have hcov_ortho : centeredBKMRealCovariance D hpow A₁ tiltOp2 = 0 := by
    let σ := adGammaStarAlgEquiv tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq
    have hσ_A₁ : σ A₁ = -A₁ := by
      rw [hA₁_eq]
      change tiltOp2 * ((2 * Complex.I) • (tiltOp2 * switchOp2)) * tiltOp2 =
        -((2 * Complex.I) • (tiltOp2 * switchOp2))
      rw [mul_smul_comm, smul_mul_assoc]
      have hmid : tiltOp2 * (tiltOp2 * switchOp2) * tiltOp2 = -(tiltOp2 * switchOp2) := by
        rw [← mul_assoc tiltOp2 tiltOp2 switchOp2, tiltOp2_sq, one_mul,
          tiltOp2_switchOp2_anticomm, neg_neg]
      rw [hmid, smul_neg]
    have hσ_Z : σ tiltOp2 = tiltOp2 := by
      change tiltOp2 * tiltOp2 * tiltOp2 = tiltOp2
      rw [tiltOp2_sq, one_mul]
    have hcov := centeredBKMRealCovariance_aut σ D hpow
      (adGammaStarAlgEquiv_gibbs_fixed tiltOp2 tiltOp2 tiltOp2_isSelfAdjoint hZ
        tiltOp2_isSelfAdjoint tiltOp2_sq (Commute.refl tiltOp2))
      (adGammaStarAlgEquiv_trace_re tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq) A₁ tiltOp2
    rw [hσ_A₁, hσ_Z] at hcov
    have hneg : centeredBKMRealCovariance D hpow (-A₁) tiltOp2 =
        -centeredBKMRealCovariance D hpow A₁ tiltOp2 := by
      rw [← centeredBKMRealCovarianceBilin_apply, map_neg, LinearMap.neg_apply,
        centeredBKMRealCovarianceBilin_apply]
    rw [hneg] at hcov
    linarith
  have hhess_pos : 0 < (secondFDerivLogPartitionReadout tiltOp2 A₁ A₂).re := by
    rw [huni.2.2.2.1]
    change centeredCEBKMForm D hpow switchOp2 x₁ x₂ > 0
    rw [centeredCEBKMForm_apply]
    change 0 < centeredBKMRealCovariance D hpow A₁ A₂
    rw [hA₂_eq, ← centeredBKMRealCovarianceBilin_apply, map_add, map_smul,
      centeredBKMRealCovarianceBilin_apply, centeredBKMRealCovarianceBilin_apply, hcov_ortho,
      smul_zero, add_zero, centeredBKMRealCovariance_self, D.bkmRealBilinForm_apply]
    apply D.kuboMoriPairing_self_re_pos _ hpow
    intro hzero
    rw [hA₁_eq] at hzero
    have hnot_gauge : ((2 * Complex.I) • (tiltOp2 * switchOp2)) ∉ scalarGauge 2 := by
      intro hmem
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
      have hm := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 0 1) hr
      have hL : matrixOfOp (r • (1 : GibbsOperator 2)) 0 1 = 0 := by
        rw [matrixOfOp_real_smul]
        change (r : ℂ) * matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2)) 0 1 = 0
        rw [matrixOfOp_id]
        simp
      have hR : matrixOfOp (((2 * Complex.I) • (tiltOp2 * switchOp2))) 0 1 = 2 * Complex.I := by
        rw [matrixOfOp_complex_smul]
        change (2 * Complex.I) * matrixOfOp (tiltOp2.comp switchOp2) 0 1 = 2 * Complex.I
        rw [matrixOfOp_comp, tiltOp2, switchOp2, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
        have h01 : (tilt2 * switch2) 0 1 = 1 := by
          norm_num [tilt2, switch2, Matrix.mul_apply, Fin.sum_univ_two]
        rw [h01, mul_one]
      rw [hL, hR] at hm
      have him := congrArg Complex.im hm
      norm_num at him
    exact hnot_gauge ((centeredStatistic_eq_zero_iff D hpow _).mp hzero)
  have hrev_neg : PS.reversible x₁ x₂ < 0 := by
    change ceCurvatureBKMProbeForm D hpow switchOp2 Q x₁ x₂ < 0
    rw [ceCurvatureBKMProbeForm_apply]
    have hcurv :
        connectionCurvature (realDerivationsLane (GibbsOperator 2))
            (exteriorDerivativeZero (realDerivationsLane (GibbsOperator 2)) switchOp2) x₁ x₂ =
          A₁ * A₂ - A₂ * A₁ := by
      rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
      rfl
    have hcomm : A₁ * A₂ - A₂ * A₁ = (-8 : ℝ) • Q := by
      have hrsmul : ∀ (r : ℝ) (X Y : GibbsOperator 2), (r • X) * Y = r • (X * Y) :=
        fun r X Y => by rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul]
      have hmulr : ∀ (r : ℝ) (X Y : GibbsOperator 2), X * (r • Y) = r • (X * Y) :=
        fun r X Y => by rw [real_smul_eq_complex_smul, mul_smul_comm, ← real_smul_eq_complex_smul]
      rw [hA₂_eq, mul_add, add_mul]
      have hsub : (A₁ * A₁ + A₁ * ((2 : ℝ) • tiltOp2)) -
          (A₁ * A₁ + ((2 : ℝ) • tiltOp2) * A₁) =
          (2 : ℝ) • (A₁ * tiltOp2 - tiltOp2 * A₁) := by
        rw [hmulr, hrsmul, smul_sub]
        abel
      have hsub2 : (2 * Complex.I) • ((tiltOp2 * switchOp2) * tiltOp2) -
          (2 * Complex.I) • (tiltOp2 * (tiltOp2 * switchOp2)) =
          (2 * Complex.I) • ((tiltOp2 * switchOp2) * tiltOp2 - tiltOp2 * (tiltOp2 * switchOp2)) :=
        (smul_sub (2 * Complex.I) _ _).symm
      rw [hsub, hA₁_eq, smul_mul_assoc, mul_smul_comm, hsub2]
      have hXZ : (tiltOp2 * switchOp2) * tiltOp2 - tiltOp2 * (tiltOp2 * switchOp2) =
          (-2 : ℝ) • switchOp2 := by
        have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
          rw [tiltOp2_switchOp2_anticomm, neg_neg]
        have hop : tiltOp2 * (-(tiltOp2 * switchOp2)) = -(tiltOp2 * (tiltOp2 * switchOp2)) :=
          ContinuousLinearMap.ext fun _ => tiltOp2.map_neg _
        have h1 : (tiltOp2 * switchOp2) * tiltOp2 = -switchOp2 := by
          rw [mul_assoc, hsw, hop, ← mul_assoc, tiltOp2_sq, one_mul]
        have h2 : tiltOp2 * (tiltOp2 * switchOp2) = switchOp2 := by
          rw [← mul_assoc, tiltOp2_sq, one_mul]
        rw [h1, h2, real_smul_eq_complex_smul]
        apply ContinuousLinearMap.ext
        intro v
        simp only [_root_.sub_apply, _root_.neg_apply, _root_.smul_apply]
        push_cast
        module
      rw [hXZ, real_smul_eq_complex_smul (-2 : ℝ), real_smul_eq_complex_smul (2 : ℝ),
        real_smul_eq_complex_smul (-8 : ℝ), smul_smul, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [hcurv, hcomm, (D.bkmRealBilinForm hpow).map_smul, LinearMap.smul_apply,
      D.bkmRealBilinForm_apply]
    have hQ_ne : Q ≠ 0 := by
      intro hQ0
      have h1 : (-Complex.I) • Q = (0 : GibbsOperator 2) := by
        rw [hQ0]
        apply ContinuousLinearMap.ext; intro v; simp
      change (-Complex.I) • (Complex.I • switchOp2) = 0 at h1
      rw [smul_smul, show (-Complex.I) * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg],
        one_smul] at h1
      exact switchOp2_ne_zero h1
    have hpos : 0 < (D.kuboMoriPairing Q Q).re := D.kuboMoriPairing_self_re_pos Q hpow hQ_ne
    change (-8 : ℝ) * (D.kuboMoriPairing Q Q).re < 0
    linarith
  exact ⟨hhess_pos, hrev_neg, huni.2.2.2.2⟩

-- Default-budget (`200000` heartbeats, `512` rec depth) stress test (a):
-- `centeredBKM_ceExteriorDerivative_reciprocity` at `m = 2` with `realDerivationsLane (GibbsOperator 2)`.
example
    (ω₂ η₂ : DerivationOperatorForm (realDerivationsLane (GibbsOperator 2)) 2) :
    let hZ := InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge.tracedExponential_re_pos_of_isSelfAdjoint
      tiltOp2 tiltOp2_isSelfAdjoint
    let D := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ
    let hpow := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint hZ
    let xZ := innerDerivation tiltOp2
    let yZX := innerDerivation (tiltOp2 * switchOp2)
    let P3 := centeredBKMOnsagerFormPairing_ofValueParity D hpow switchOp2 switchOp2_isSelfAdjoint
      ![xZ, yZX, xZ + yZX]
    P3.totalGenerator
        (P3.T.op (ceExteriorDerivative (realDerivationsLane (GibbsOperator 2)) 2 ω₂))
        (P3.T.op (ceExteriorDerivative (realDerivationsLane (GibbsOperator 2)) 2 η₂)) =
      P3.totalGenerator
        (ceExteriorDerivative (realDerivationsLane (GibbsOperator 2)) 2 η₂)
        (ceExteriorDerivative (realDerivationsLane (GibbsOperator 2)) 2 ω₂) := by
  intro hZ D hpow xZ yZX P3
  exact centeredBKM_ceExteriorDerivative_reciprocity P3 ω₂ η₂

-- Default-budget (`200000` heartbeats, `512` rec depth) stress test (b):
-- `exact centeredBKM_ceWedge_reciprocity P3 ...` at `p = 1, q = 2` against `ParityOnsagerFormPairing _ _ 3`.
example
    (ω₁ ω₂ : DerivationOperatorForm (realDerivationsLane (GibbsOperator 2)) 1)
    (η₁ η₂ : DerivationOperatorForm (realDerivationsLane (GibbsOperator 2)) 2) :
    let hZ := InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge.tracedExponential_re_pos_of_isSelfAdjoint
      tiltOp2 tiltOp2_isSelfAdjoint
    let D := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ
    let hpow := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint hZ
    let xZ := innerDerivation tiltOp2
    let yZX := innerDerivation (tiltOp2 * switchOp2)
    let P3 : ParityOnsagerFormPairing (Carrier 2) (GibbsOperator 2) 3 :=
      centeredBKMOnsagerFormPairing_ofValueParity D hpow switchOp2 switchOp2_isSelfAdjoint
        ![xZ, yZX, xZ + yZX]
    P3.totalGenerator
        (P3.T.op (ceWedge (realDerivationsLane (GibbsOperator 2)) ω₁ η₁))
        (P3.T.op (ceWedge (realDerivationsLane (GibbsOperator 2)) ω₂ η₂)) =
      P3.totalGenerator
        (ceWedge (realDerivationsLane (GibbsOperator 2)) ω₂ η₂)
        (ceWedge (realDerivationsLane (GibbsOperator 2)) ω₁ η₁) := by
  intro hZ D hpow xZ yZX P3
  exact centeredBKM_ceWedge_reciprocity P3 ω₁ η₁ ω₂ η₂

-- Default-budget (`200000` heartbeats, `512` rec depth) stress test (c):
-- caller `let PP := centeredBKMOnsagerFormPairing_ofValueParity ...`, `rw [hbr.1]`,
-- and `centeredBKM_ceCurvature_reciprocity`, with strictly negative reversible curvature.
example :
    let hZ := InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge.tracedExponential_re_pos_of_isSelfAdjoint
      tiltOp2 tiltOp2_isSelfAdjoint
    let D := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ
    let hpow := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint hZ
    let xZ := innerDerivation tiltOp2
    let yZX := innerDerivation (tiltOp2 * switchOp2)
    let K := realDerivationsLane (GibbsOperator 2)
    let Γ₁ := oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K switchOp2)
    let Γ₂ := oneFormAlternatingLinearEquiv K
      (exteriorDerivativeZero K (switchOp2 + tiltOp2 * switchOp2))
    let PP := centeredBKMOnsagerFormPairing_ofValueParity D hpow tiltOp2 tiltOp2_isSelfAdjoint ![xZ, yZX]
    PP.reversible (ceCurvature K Γ₁) (ceCurvature K Γ₂) < 0 ∧
      PP.totalGenerator (PP.T.op (ceCurvature K Γ₁)) (PP.T.op (ceCurvature K Γ₂)) =
        PP.totalGenerator (ceCurvature K Γ₂) (ceCurvature K Γ₁) := by
  intro hZ D hpow xZ yZX K Γ₁ Γ₂ PP
  have hbr := ceCurvature_degree2_parity_bridge D hpow switchOp2
    (switchOp2 + tiltOp2 * switchOp2) tiltOp2 tiltOp2_isSelfAdjoint xZ yZX
  refine ⟨?_, centeredBKM_ceCurvature_reciprocity PP Γ₁ Γ₂⟩
  rw [hbr.1, commutatorBKMProbeForm_apply]
  have hcore : ((2 : ℝ) • (tiltOp2 * switchOp2)) * ((2 : ℝ) • tiltOp2) -
      ((2 : ℝ) • tiltOp2) * ((2 : ℝ) • (tiltOp2 * switchOp2)) = (-8 : ℝ) • switchOp2 := by
    rw [real_smul_eq_complex_smul 2 (tiltOp2 * switchOp2),
      real_smul_eq_complex_smul 2 tiltOp2,
      real_smul_eq_complex_smul (-8) switchOp2]
    push_cast
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num
    have hsub4 : (4 : ℂ) • ((tiltOp2 * switchOp2) * tiltOp2) -
        (4 : ℂ) • (tiltOp2 * (tiltOp2 * switchOp2)) =
        (4 : ℂ) • ((tiltOp2 * switchOp2) * tiltOp2 - tiltOp2 * (tiltOp2 * switchOp2)) :=
      ContinuousLinearMap.ext fun v => (smul_sub (4 : ℂ) _ _).symm
    rw [hsub4]
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    have hop : tiltOp2 * (-(tiltOp2 * switchOp2)) = -(tiltOp2 * (tiltOp2 * switchOp2)) :=
      ContinuousLinearMap.ext fun _ => tiltOp2.map_neg _
    have h1 : (tiltOp2 * switchOp2) * tiltOp2 = -switchOp2 := by
      rw [mul_assoc, hsw, hop, ← mul_assoc, tiltOp2_sq, one_mul]
    have h2 : tiltOp2 * (tiltOp2 * switchOp2) = switchOp2 := by
      rw [← mul_assoc, tiltOp2_sq, one_mul]
    rw [h1, h2]
    have hneg2 : -switchOp2 - switchOp2 = (-2 : ℂ) • switchOp2 := by
      apply ContinuousLinearMap.ext; intro v
      simp only [_root_.sub_apply, _root_.neg_apply, _root_.smul_apply]
      module
    rw [hneg2, smul_smul]
    norm_num
  have hF₁ : connectionCurvature K (exteriorDerivativeZero K switchOp2) xZ yZX =
      (-8 : ℝ) • switchOp2 := by
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    change carrierEnd xZ switchOp2 * carrierEnd yZX switchOp2 -
      carrierEnd yZX switchOp2 * carrierEnd xZ switchOp2 = _
    have hx : carrierEnd xZ switchOp2 = (2 : ℝ) • (tiltOp2 * switchOp2) := by
      rw [innerDerivation_apply]
      have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
        rw [tiltOp2_switchOp2_anticomm, neg_neg]
      rw [hsw, sub_neg_eq_add, ← two_smul ℝ (tiltOp2 * switchOp2)]
    have hy : carrierEnd yZX switchOp2 = (2 : ℝ) • tiltOp2 := by
      rw [innerDerivation_apply]
      have h1 : (tiltOp2 * switchOp2) * switchOp2 = tiltOp2 := by
        rw [mul_assoc, switchOp2_sq, mul_one]
      have h2 : switchOp2 * (tiltOp2 * switchOp2) = -tiltOp2 := by
        have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
          rw [tiltOp2_switchOp2_anticomm, neg_neg]
        have hop : (-(tiltOp2 * switchOp2)) * switchOp2 = -((tiltOp2 * switchOp2) * switchOp2) :=
          ContinuousLinearMap.ext fun _ => rfl
        rw [← mul_assoc, hsw, hop, mul_assoc, switchOp2_sq, mul_one]
      rw [h1, h2, sub_neg_eq_add, ← two_smul ℝ tiltOp2]
    rw [hx, hy]
    exact hcore
  have hF₂ : connectionCurvature K
      (exteriorDerivativeZero K (switchOp2 + tiltOp2 * switchOp2)) xZ yZX =
      (-8 : ℝ) • switchOp2 + (-8 : ℝ) • (tiltOp2 * switchOp2) := by
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add]
    change carrierEnd xZ (switchOp2 + tiltOp2 * switchOp2) *
        carrierEnd yZX (switchOp2 + tiltOp2 * switchOp2) -
      carrierEnd yZX (switchOp2 + tiltOp2 * switchOp2) *
        carrierEnd xZ (switchOp2 + tiltOp2 * switchOp2) = _
    have hx_ZX : carrierEnd xZ (tiltOp2 * switchOp2) = (2 : ℝ) • switchOp2 := by
      rw [innerDerivation_apply]
      have h1 : tiltOp2 * (tiltOp2 * switchOp2) = switchOp2 := by
        rw [← mul_assoc, tiltOp2_sq, one_mul]
      have h2 : (tiltOp2 * switchOp2) * tiltOp2 = -switchOp2 := by
        have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
          rw [tiltOp2_switchOp2_anticomm, neg_neg]
        have hop : tiltOp2 * (-(tiltOp2 * switchOp2)) = -(tiltOp2 * (tiltOp2 * switchOp2)) :=
          ContinuousLinearMap.ext fun _ => tiltOp2.map_neg _
        rw [mul_assoc, hsw, hop, ← mul_assoc, tiltOp2_sq, one_mul]
      rw [h1, h2, sub_neg_eq_add, ← two_smul ℝ switchOp2]
    have hy_ZX : carrierEnd yZX (tiltOp2 * switchOp2) = 0 := by
      rw [innerDerivation_apply, sub_self]
    have hx_add : carrierEnd xZ (switchOp2 + tiltOp2 * switchOp2) =
        (2 : ℝ) • (tiltOp2 * switchOp2) + (2 : ℝ) • switchOp2 := by
      rw [map_add]
      have hxX : carrierEnd xZ switchOp2 = (2 : ℝ) • (tiltOp2 * switchOp2) := by
        have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
          rw [tiltOp2_switchOp2_anticomm, neg_neg]
        rw [innerDerivation_apply, hsw, sub_neg_eq_add, ← two_smul ℝ (tiltOp2 * switchOp2)]
      rw [hxX, hx_ZX]
    have hy_add : carrierEnd yZX (switchOp2 + tiltOp2 * switchOp2) = (2 : ℝ) • tiltOp2 := by
      rw [map_add, hy_ZX, add_zero, innerDerivation_apply]
      have h1 : (tiltOp2 * switchOp2) * switchOp2 = tiltOp2 := by
        rw [mul_assoc, switchOp2_sq, mul_one]
      have h2 : switchOp2 * (tiltOp2 * switchOp2) = -tiltOp2 := by
        have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
          rw [tiltOp2_switchOp2_anticomm, neg_neg]
        have hop : (-(tiltOp2 * switchOp2)) * switchOp2 = -((tiltOp2 * switchOp2) * switchOp2) :=
          ContinuousLinearMap.ext fun _ => rfl
        rw [← mul_assoc, hsw, hop, mul_assoc, switchOp2_sq, mul_one]
      rw [h1, h2, sub_neg_eq_add, ← two_smul ℝ tiltOp2]
    rw [hx_add, hy_add, add_mul, mul_add]
    have hsplit : (((2 : ℝ) • (tiltOp2 * switchOp2)) * ((2 : ℝ) • tiltOp2) +
          ((2 : ℝ) • switchOp2) * ((2 : ℝ) • tiltOp2)) -
        (((2 : ℝ) • tiltOp2) * ((2 : ℝ) • (tiltOp2 * switchOp2)) +
          ((2 : ℝ) • tiltOp2) * ((2 : ℝ) • switchOp2)) =
        (((2 : ℝ) • (tiltOp2 * switchOp2)) * ((2 : ℝ) • tiltOp2) -
          ((2 : ℝ) • tiltOp2) * ((2 : ℝ) • (tiltOp2 * switchOp2))) +
        (((2 : ℝ) • switchOp2) * ((2 : ℝ) • tiltOp2) -
          ((2 : ℝ) • tiltOp2) * ((2 : ℝ) • switchOp2)) := by
      abel
    rw [hsplit, hcore]
    congr 1
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    have hrsmul : ∀ (r : ℝ) (X Y : GibbsOperator 2), (r • X) * Y = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul]
    have hmulr : ∀ (r : ℝ) (X Y : GibbsOperator 2), X * (r • Y) = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, mul_smul_comm, ← real_smul_eq_complex_smul]
    rw [hrsmul, hmulr, hrsmul, hmulr, smul_smul, smul_smul, hsw, smul_neg, sub_eq_add_neg]
    norm_num
    rw [← neg_smul, ← add_smul]
    norm_num
    rw [← neg_smul]
  rw [hF₁, hF₂]
  have hcomm : ((-8 : ℝ) • switchOp2) * ((-8 : ℝ) • switchOp2 + (-8 : ℝ) • (tiltOp2 * switchOp2)) -
      ((-8 : ℝ) • switchOp2 + (-8 : ℝ) • (tiltOp2 * switchOp2)) * ((-8 : ℝ) • switchOp2) =
      (-128 : ℝ) • tiltOp2 := by
    rw [mul_add, add_mul]
    have hsplit : (((-8 : ℝ) • switchOp2) * ((-8 : ℝ) • switchOp2) +
          ((-8 : ℝ) • switchOp2) * ((-8 : ℝ) • (tiltOp2 * switchOp2))) -
        (((-8 : ℝ) • switchOp2) * ((-8 : ℝ) • switchOp2) +
          ((-8 : ℝ) • (tiltOp2 * switchOp2)) * ((-8 : ℝ) • switchOp2)) =
        ((-8 : ℝ) • switchOp2) * ((-8 : ℝ) • (tiltOp2 * switchOp2)) -
          ((-8 : ℝ) • (tiltOp2 * switchOp2)) * ((-8 : ℝ) • switchOp2) := by
      abel
    have hrsmul : ∀ (r : ℝ) (X Y : GibbsOperator 2), (r • X) * Y = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul]
    have hmulr : ∀ (r : ℝ) (X Y : GibbsOperator 2), X * (r • Y) = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, mul_smul_comm, ← real_smul_eq_complex_smul]
    rw [hsplit, hrsmul, hmulr, hrsmul, hmulr, smul_smul, smul_smul]
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    have hop : (-(tiltOp2 * switchOp2)) * switchOp2 = -((tiltOp2 * switchOp2) * switchOp2) :=
      ContinuousLinearMap.ext fun _ => rfl
    have h1 : switchOp2 * (tiltOp2 * switchOp2) = -tiltOp2 := by
      rw [← mul_assoc, hsw, hop, mul_assoc, switchOp2_sq, mul_one]
    have h2 : (tiltOp2 * switchOp2) * switchOp2 = tiltOp2 := by
      rw [mul_assoc, switchOp2_sq, mul_one]
    rw [h1, h2, smul_neg]
    norm_num
    rw [sub_eq_add_neg, ← neg_smul, ← add_smul]
    norm_num
    rw [← neg_smul]
  rw [hcomm, (D.bkmRealBilinForm hpow).map_smul, LinearMap.smul_apply, D.bkmRealBilinForm_apply]
  have htilt_not_gauge : tiltOp2 ∉ scalarGauge 2 := by
    intro hmem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have h00 := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 0 0) hr
    have h11 := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 1 1) hr
    have h00L : matrixOfOp (r • (1 : GibbsOperator 2)) 0 0 = r := by
      rw [matrixOfOp_real_smul]
      change (r : ℂ) * matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2)) 0 0 = r
      rw [matrixOfOp_id]; simp
    have h11L : matrixOfOp (r • (1 : GibbsOperator 2)) 1 1 = r := by
      rw [matrixOfOp_real_smul]
      change (r : ℂ) * matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2)) 1 1 = r
      rw [matrixOfOp_id]; simp
    have h00R : matrixOfOp tiltOp2 0 0 = 1 := by
      rw [tiltOp2, matrixOfOp_matrixOp]; norm_num [tilt2]
    have h11R : matrixOfOp tiltOp2 1 1 = -1 := by
      rw [tiltOp2, matrixOfOp_matrixOp]; norm_num [tilt2]
    rw [h00L, h00R] at h00
    rw [h11L, h11R] at h11
    have h00re := congrArg Complex.re h00
    have h11re := congrArg Complex.re h11
    norm_num at h00re h11re
    linarith
  have htilt_ne : tiltOp2 ≠ 0 := fun h => htilt_not_gauge (h ▸ Submodule.zero_mem _)
  have hpos : 0 < (D.kuboMoriPairing tiltOp2 tiltOp2).re :=
    D.kuboMoriPairing_self_re_pos tiltOp2 hpow htilt_ne
  change (-128 : ℝ) * (D.kuboMoriPairing tiltOp2 tiltOp2).re < 0
  linarith

/-- Default-budget (`200000` heartbeats, `512` rec depth) stress test (d) & Requirement 3:
non-constant `RealOperatorFrechetForm` witness (`smoothLeftMulOneForm 2`) satisfying
`frechetExtDerivReal_parityOnsager_reciprocity` AND strict positivity `0 < PP2.totalGenerator dω dω`. -/
theorem smoothLeftMulOneForm_frechetExtDeriv_defaultBudget_witness :
    let hZ := InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge.tracedExponential_re_pos_of_isSelfAdjoint
      tiltOp2 tiltOp2_isSelfAdjoint
    let D := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ
    let hpow := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint hZ
    let ω := smoothLeftMulOneForm 2
    let hω := contDiff_smoothLeftMulOneForm 2
    let V₁ := frechetVectorFieldFromComplex (innerFrechetComplexDeriv (tiltOp2 * switchOp2))
    let V₂ := frechetVectorFieldFromComplex (innerFrechetComplexDeriv switchOp2)
    let K := frechetVectorFieldDerivationLane ℝ (GibbsOperator 2)
    let PP2 := frechetFormParityOnsagerPairing D hpow tiltOp2 tiltOp2_isSelfAdjoint tiltOp2 ![V₁, V₂]
    let dω := frechetFormToCEForm (1 + 1) (frechetExtDerivReal ω) (contDiff_frechetExtDerivK hω)
    0 < PP2.totalGenerator dω dω ∧
      PP2.totalGenerator (PP2.T.op dω) (PP2.T.op dω) =
        PP2.totalGenerator (ceExteriorDerivative K 1 (frechetFormToCEForm 1 ω hω))
          (ceExteriorDerivative K 1 (frechetFormToCEForm 1 ω hω)) := by
  intro hZ D hpow ω hω V₁ V₂ K PP2 dω
  refine ⟨?_, frechetExtDerivReal_parityOnsager_reciprocity D hpow tiltOp2 tiltOp2_isSelfAdjoint
    tiltOp2 ![V₁, V₂] ω ω hω hω⟩
  rw [frechetFormParityOnsagerPairing_totalGenerator]
  have hrev_zero : commutatorBKMProbeForm D hpow tiltOp2 ((dω ![V₁, V₂]) tiltOp2)
      ((dω ![V₁, V₂]) tiltOp2) = 0 := by
    have hskew := commutatorBKMProbeForm_skew D hpow tiltOp2 ((dω ![V₁, V₂]) tiltOp2)
      ((dω ![V₁, V₂]) tiltOp2)
    linarith
  rw [hrev_zero, add_zero]
  have heval : (dω ![V₁, V₂]) tiltOp2 = (-8 : ℝ) • tiltOp2 := by
    have hfun : (fun i : Fin 2 => (![V₁, V₂] i).toDerivation tiltOp2) =
        ![V₁.toDerivation tiltOp2, V₂.toDerivation tiltOp2] := by
      ext i; fin_cases i <;> rfl
    dsimp [dω]
    change frechetExtDerivReal ω tiltOp2 (fun i : Fin 2 => (![V₁, V₂] i).toDerivation tiltOp2) = _
    rw [hfun, frechetExtDerivReal_smoothLeftMulOneForm]
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    have hv1 : V₁.toDerivation tiltOp2 = (-2 : ℝ) • switchOp2 := by
      change (tiltOp2 * switchOp2) * tiltOp2 - tiltOp2 * (tiltOp2 * switchOp2) = _
      have hop : tiltOp2 * (-(tiltOp2 * switchOp2)) = -(tiltOp2 * (tiltOp2 * switchOp2)) :=
        ContinuousLinearMap.ext fun _ => tiltOp2.map_neg _
      have h1 : (tiltOp2 * switchOp2) * tiltOp2 = -switchOp2 := by
        rw [mul_assoc, hsw, hop, ← mul_assoc, tiltOp2_sq, one_mul]
      have h2 : tiltOp2 * (tiltOp2 * switchOp2) = switchOp2 := by
        rw [← mul_assoc, tiltOp2_sq, one_mul]
      rw [h1, h2, real_smul_eq_complex_smul]
      apply ContinuousLinearMap.ext; intro v
      simp only [_root_.sub_apply, _root_.neg_apply, _root_.smul_apply]
      push_cast; module
    have hv2 : V₂.toDerivation tiltOp2 = (-2 : ℝ) • (tiltOp2 * switchOp2) := by
      change switchOp2 * tiltOp2 - tiltOp2 * switchOp2 = _
      rw [hsw, real_smul_eq_complex_smul]
      apply ContinuousLinearMap.ext; intro v
      simp only [_root_.sub_apply, _root_.neg_apply, _root_.smul_apply]
      push_cast; module
    have hrsmul : ∀ (r : ℝ) (X Y : GibbsOperator 2), (r • X) * Y = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, smul_mul_assoc, ← real_smul_eq_complex_smul]
    have hmulr : ∀ (r : ℝ) (X Y : GibbsOperator 2), X * (r • Y) = r • (X * Y) :=
      fun r X Y => by rw [real_smul_eq_complex_smul, mul_smul_comm, ← real_smul_eq_complex_smul]
    rw [hv1, hv2, hrsmul, hmulr, hrsmul, hmulr, smul_smul, smul_smul]
    have hop : (-(tiltOp2 * switchOp2)) * switchOp2 = -((tiltOp2 * switchOp2) * switchOp2) :=
      ContinuousLinearMap.ext fun _ => rfl
    have h1 : switchOp2 * (tiltOp2 * switchOp2) = -tiltOp2 := by
      rw [← mul_assoc, hsw, hop, mul_assoc, switchOp2_sq, mul_one]
    have h2 : (tiltOp2 * switchOp2) * switchOp2 = tiltOp2 := by
      rw [mul_assoc, switchOp2_sq, mul_one]
    rw [h1, h2, smul_neg]
    norm_num
    rw [sub_eq_add_neg, ← neg_smul, ← add_smul]
    norm_num
    rw [← neg_smul]
  rw [heval, centeredBKMRealCovariance_self, D.bkmRealBilinForm_apply]
  apply D.kuboMoriPairing_self_re_pos _ hpow
  intro hzero
  have hmem := (centeredStatistic_eq_zero_iff D hpow _).mp hzero
  have htilt_mem : tiltOp2 ∈ scalarGauge 2 := by
    have hmul := (scalarGauge 2).smul_mem (-1 / 8 : ℝ) hmem
    rw [smul_smul] at hmul
    norm_num at hmul
    exact hmul
  have htilt_not_gauge : tiltOp2 ∉ scalarGauge 2 := by
    intro hm
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hm
    have h00 := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 0 0) hr
    have h11 := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 1 1) hr
    have h00L : matrixOfOp (r • (1 : GibbsOperator 2)) 0 0 = r := by
      rw [matrixOfOp_real_smul]
      change (r : ℂ) * matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2)) 0 0 = r
      rw [matrixOfOp_id]; simp
    have h11L : matrixOfOp (r • (1 : GibbsOperator 2)) 1 1 = r := by
      rw [matrixOfOp_real_smul]
      change (r : ℂ) * matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2)) 1 1 = r
      rw [matrixOfOp_id]; simp
    have h00R : matrixOfOp tiltOp2 0 0 = 1 := by
      rw [tiltOp2, matrixOfOp_matrixOp]; norm_num [tilt2]
    have h11R : matrixOfOp tiltOp2 1 1 = -1 := by
      rw [tiltOp2, matrixOfOp_matrixOp]; norm_num [tilt2]
    rw [h00L, h00R] at h00
    rw [h11L, h11R] at h11
    have h00re := congrArg Complex.re h00
    have h11re := congrArg Complex.re h11
    norm_num at h00re h11re
    linarith
  exact htilt_not_gauge htilt_mem

-- Default-budget (`200000` heartbeats, `512` rec depth) test for
-- `gibbsNOperatorFamilyAdGammaErlangenDatum_reciprocity_and_hessian` and
-- `gibbsNOperatorFamilyConjErlangenDatum_reciprocity_and_hessian`.
example :
    let hZ := InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge.tracedExponential_re_pos_of_isSelfAdjoint
      tiltOp2 tiltOp2_isSelfAdjoint
    let aAd := ![(tiltOp2 : GibbsOperator 2), (1 : GibbsOperator 2)]
    let c : Fin 2 → ℝ := ![1, 1]
    let DAd := ![innerFrechetComplexDeriv (Complex.I • switchOp2), (0 : FrechetOperatorDerivation ℂ (GibbsOperator 2))]
    let datumAd := gibbsNOperatorFamilyAdGammaErlangenDatum (G := Equiv.Perm (Fin 2))
      tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq tiltOp2 tiltOp2_isSelfAdjoint hZ
      (Commute.refl tiltOp2) aAd
      (fun i => by fin_cases i <;> simp [aAd]) c switchOp2
      (by rw [tiltOp2_switchOp2_anticomm, neg_neg])
    let aConj := ![(switchOp2 : GibbsOperator 2), (tiltOp2 : GibbsOperator 2)]
    let DConj := ![innerFrechetComplexDeriv (Complex.I • tiltOp2),
      innerFrechetComplexDeriv (Complex.I • switchOp2)]
    let datumConj := gibbsNOperatorFamilyConjErlangenDatum (G := Equiv.Perm (Fin 2))
      tiltOp2 tiltOp2_isSelfAdjoint hZ conj_tiltOp2 aConj
      (fun i => by fin_cases i; exact conj_switchOp2; exact conj_tiltOp2) c
      (Complex.I • switchOp2) (conjStarAlgEquiv_purelyImaginary_odd switchOp2 conj_switchOp2)
    HasJReciprocity datumAd.onsagerPairing
        (familyTimeReversal 2 (autDerivationTimeReversal
          (adGammaStarAlgEquiv tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq)
          (adGammaStarAlgEquiv_involutive tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq))).op ∧
      datumAd.responseMetric ()
          (finiteCEFrechetFamilyDirection DAd) (finiteCEFrechetFamilyDirection DAd) =
        (secondFDerivLogPartitionReadout tiltOp2
          (finiteGibbsCEFamilyNOperatorReadoutLinear aAd c (finiteCEFrechetFamilyDirection DAd))
          (finiteGibbsCEFamilyNOperatorReadoutLinear aAd c (finiteCEFrechetFamilyDirection DAd))).re ∧
      HasJReciprocity datumConj.onsagerPairing
        (familyTimeReversal 2 (autDerivationTimeReversal (conjStarAlgEquiv 2)
          (conjStarAlgEquiv_involutive (n := 2)))).op ∧
      datumConj.responseMetric ()
          (finiteCEFrechetFamilyDirection DConj) (finiteCEFrechetFamilyDirection DConj) =
        (secondFDerivLogPartitionReadout tiltOp2
          (finiteGibbsCEFamilyNOperatorReadoutLinear aConj c (finiteCEFrechetFamilyDirection DConj))
          (finiteGibbsCEFamilyNOperatorReadoutLinear aConj c (finiteCEFrechetFamilyDirection DConj))).re := by
  intro hZ aAd c DAd datumAd aConj DConj datumConj
  have hi_sa : IsSelfAdjoint (Complex.I • (tiltOp2 * switchOp2)) := by
    rw [isSelfAdjoint_iff, star_smul, Complex.star_def, Complex.conj_I,
      StarMul.star_mul, tiltOp2_isSelfAdjoint.star_eq, switchOp2_isSelfAdjoint.star_eq]
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    rw [hsw, smul_neg, neg_smul, neg_neg]
  have h_sa_smul : ∀ (r : ℝ) {X : GibbsOperator 2}, IsSelfAdjoint X → IsSelfAdjoint (r • X) :=
    fun r X hX => by
      rw [isSelfAdjoint_iff, real_smul_eq_complex_smul, star_smul, Complex.star_def,
        Complex.conj_ofReal, hX.star_eq]
  have hDAd : IsSelfAdjoint
      (finiteGibbsCEFamilyNOperatorReadoutLinear aAd c (finiteCEFrechetFamilyDirection DAd)) := by
    rw [finiteGibbsCEFamilyNOperatorReadoutLinear_apply, Fin.sum_univ_two]
    have h0 : finiteGibbsCEFamilyComponentForm aAd 0 (finiteCEFrechetFamilyDirection DAd 0) =
        (-2 : ℝ) • (Complex.I • (tiltOp2 * switchOp2)) := by
      change (Complex.I • switchOp2) * tiltOp2 - tiltOp2 * (Complex.I • switchOp2) = _
      have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
        rw [tiltOp2_switchOp2_anticomm, neg_neg]
      rw [smul_mul_assoc, mul_smul_comm, hsw, smul_neg, neg_sub_left,
        ← two_smul ℂ (Complex.I • (tiltOp2 * switchOp2)), real_smul_eq_complex_smul,
        smul_smul, smul_smul]
      push_cast
      apply ContinuousLinearMap.ext; intro v
      simp only [_root_.neg_apply, _root_.smul_apply]
      module
    have h1 : finiteGibbsCEFamilyComponentForm aAd 1 (finiteCEFrechetFamilyDirection DAd 1) = 0 := by
      change (0 : FrechetOperatorDerivation ℂ (GibbsOperator 2)) (1 : GibbsOperator 2) = 0
      rfl
    rw [h0, h1]
    dsimp [c]
    simp only [one_smul, add_zero]
    exact h_sa_smul (-2 : ℝ) hi_sa
  have hDConj : IsSelfAdjoint
      (finiteGibbsCEFamilyNOperatorReadoutLinear aConj c (finiteCEFrechetFamilyDirection DConj)) := by
    rw [finiteGibbsCEFamilyNOperatorReadoutLinear_apply, Fin.sum_univ_two]
    have h0 : finiteGibbsCEFamilyComponentForm aConj 0 (finiteCEFrechetFamilyDirection DConj 0) =
        (2 : ℝ) • (Complex.I • (tiltOp2 * switchOp2)) := by
      change (Complex.I • tiltOp2) * switchOp2 - switchOp2 * (Complex.I • tiltOp2) = _
      have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
        rw [tiltOp2_switchOp2_anticomm, neg_neg]
      rw [smul_mul_assoc, mul_smul_comm, hsw, smul_neg, sub_neg_eq_add,
        ← two_smul ℂ (Complex.I • (tiltOp2 * switchOp2)), real_smul_eq_complex_smul]
      push_cast; rfl
    have h1 : finiteGibbsCEFamilyComponentForm aConj 1 (finiteCEFrechetFamilyDirection DConj 1) =
        (-2 : ℝ) • (Complex.I • (tiltOp2 * switchOp2)) := by
      change (Complex.I • switchOp2) * tiltOp2 - tiltOp2 * (Complex.I • switchOp2) = _
      have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
        rw [tiltOp2_switchOp2_anticomm, neg_neg]
      rw [smul_mul_assoc, mul_smul_comm, hsw, smul_neg, neg_sub_left,
        ← two_smul ℂ (Complex.I • (tiltOp2 * switchOp2)), real_smul_eq_complex_smul,
        smul_smul, smul_smul]
      push_cast
      apply ContinuousLinearMap.ext; intro v
      simp only [_root_.neg_apply, _root_.smul_apply]
      module
    rw [h0, h1]
    dsimp [c]
    simp only [one_smul]
    have hop_add : ∀ A B : GibbsOperator 2, star (A + B) = star A + star B :=
      (finiteOperatorStarRealCLM 2).map_add
    rw [isSelfAdjoint_iff, hop_add,
      (h_sa_smul (2 : ℝ) hi_sa).star_eq, (h_sa_smul (-2 : ℝ) hi_sa).star_eq]
  have hAd := gibbsNOperatorFamilyAdGammaErlangenDatum_reciprocity_and_hessian
    (G := Equiv.Perm (Fin 2)) tiltOp2 tiltOp2_isSelfAdjoint tiltOp2_sq
    tiltOp2 tiltOp2_isSelfAdjoint hZ (Commute.refl tiltOp2) aAd
    (fun i => by fin_cases i <;> simp [aAd]) c switchOp2
    (by rw [tiltOp2_switchOp2_anticomm, neg_neg]) DAd DAd hDAd
  have hConj := gibbsNOperatorFamilyConjErlangenDatum_reciprocity_and_hessian
    (G := Equiv.Perm (Fin 2)) tiltOp2 tiltOp2_isSelfAdjoint hZ conj_tiltOp2 aConj
    (fun i => by fin_cases i; exact conj_switchOp2; exact conj_tiltOp2) c
    (Complex.I • switchOp2) (conjStarAlgEquiv_purelyImaginary_odd switchOp2 conj_switchOp2)
    DConj DConj hDConj
  exact ⟨hAd.1, hAd.2, hConj.1, hConj.2⟩

end DefaultBudgetStressTests

end InfoGeometry.Canonical.CEBKMParityUnificationBridge
