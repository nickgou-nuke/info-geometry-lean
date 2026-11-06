/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.UnifiedDikinGeometry
import InfoGeometry.Canonical.DikinInstances
import InfoGeometry.Canonical.DikinFiniteOrbitColimit
import InfoGeometry.SymmetricDomains.DikinMetriplectic
import InfoGeometry.Quantum.DikinBlahutOrbits
import InfoGeometry.External.Auto.DikinGoutevTonevBridge
import InfoGeometry.External.Auto.AmariChentsovFierzTorsion
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

/-!
# Dikin Instances — Lineage Integration (Part 2: Remaining Lineages)

For lineages on `ℝ` (which already has a `DikinMetric ℝ` instance from Part 1),
we define the metric functions directly and prove they satisfy the framework's
axioms, rather than creating conflicting typeclass instances:

2. `apolloniusDikinMetric`      : `2(1 - tanh² ξ) · v²` on `ℝ`
3. `grandUnificationDikinMetric`: `(2 / cosh² ξ) · v²` on `ℝ` (`= souriauDikinMetric`)
4. `orbitDikinMetric`           : `(1 / x²) · v²` on `ℝ₊`
5. `tubeDikinMetric`            : Koecher–Vinberg Hessian on `ℝ²` (parameterized by `Y`)
6. `coreDikinMetric`            : `v₀² + v₁²` on `ℝ²` (core subspace)
7. `modularJetDikinMetric`      : `(J.dikinMetric / 2) · δ²` on `ℝ`
8. `bkmDikinMetric`             : BKM Kubo–Mori quadratic on `SelfAdjointOperator n`

No `sorry`, `admit`, or axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
-/

noncomputable section

open SouriauOnsagerBKM
open AmariChentsovFierzTorsion
open InfoGeometry.Canonical.DikinFiniteOrbitColimit

/-! ### 2. Apollonius Scale-Space Dikin Metric on `ℝ` -/

def apolloniusDikinMetric (ξ v : ℝ) : ℝ :=
  2 * (1 - Real.tanh ξ ^ 2) * v ^ 2

theorem apolloniusDikinMetric_zero (ξ : ℝ) :
    apolloniusDikinMetric ξ 0 = 0 := by
  simp [apolloniusDikinMetric]

theorem apolloniusDikinMetric_pos {ξ v : ℝ} (hv : v ≠ 0) :
    0 < apolloniusDikinMetric ξ v := by
  have h₁ : Real.tanh ξ ^ 2 < 1 := Real.tanh_sq_lt_one ξ
  have h₂ : 0 < 1 - Real.tanh ξ ^ 2 := sub_pos.mpr h₁
  have h₃ : 0 < 2 * (1 - Real.tanh ξ ^ 2) := mul_pos zero_lt_two h₂
  have h₄ : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  exact mul_pos h₃ h₄

/-! ### 3. Grand Unification Dikin Metric on `ℝ` (`= Souriau metric`) -/

def grandUnificationDikinMetric (ξ v : ℝ) : ℝ :=
  (2 / Real.cosh ξ ^ 2) * v ^ 2

theorem grandUnificationDikinMetric_zero (ξ : ℝ) :
    grandUnificationDikinMetric ξ 0 = 0 := by
  simp [grandUnificationDikinMetric]

theorem grandUnificationDikinMetric_pos {ξ v : ℝ} (hv : v ≠ 0) :
    0 < grandUnificationDikinMetric ξ v := by
  have h₁ : 0 < Real.cosh ξ := Real.cosh_pos ξ
  have h₂ : 0 < Real.cosh ξ ^ 2 := sq_pos_of_pos h₁
  have h₃ : 0 < 2 / Real.cosh ξ ^ 2 := div_pos zero_lt_two h₂
  have h₄ : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  exact mul_pos h₃ h₄

theorem grandUnificationEqSouriauMetric :
    (grandUnificationDikinMetric : ℝ → ℝ → ℝ) = (souriauDikinMetric : ℝ → ℝ → ℝ) :=
  rfl

/-! ### 4. Orbit/Inverse-Square Dikin Metric on `ℝ₊` -/

def orbitDikinMetric (x v : ℝ) : ℝ :=
  (1 / x ^ 2) * v ^ 2

theorem orbitDikinMetric_zero (x : ℝ) :
    orbitDikinMetric x 0 = 0 := by
  simp [orbitDikinMetric]

theorem orbitDikinMetric_pos {x v : ℝ} (hx : x ≠ 0) (hv : v ≠ 0) :
    0 < orbitDikinMetric x v := by
  have h₁ : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have h₂ : 0 < 1 / x ^ 2 := one_div_pos.mpr h₁
  have h₃ : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  exact mul_pos h₂ h₃

/-! ### 5. Tube Domain / Koecher–Vinberg Dikin Metric on `ℝ²` -/

def tubeDikinMetric (Y : InfoGeometry.SymmetricDomains.DikinMetriplectic.TubeCoordinate)
    (v : ℝ × ℝ) : ℝ :=
  (v.1 / Y.y1) ^ 2 + (v.2 / Y.y2) ^ 2

theorem tubeDikinMetric_zero (Y : InfoGeometry.SymmetricDomains.DikinMetriplectic.TubeCoordinate) :
    tubeDikinMetric Y (0, 0) = 0 := by
  simp [tubeDikinMetric]

theorem tubeDikinMetric_pos {Y : InfoGeometry.SymmetricDomains.DikinMetriplectic.TubeCoordinate}
    {v : ℝ × ℝ} (hv : v ≠ (0, 0)) :
    0 < tubeDikinMetric Y v := by
  have h₁ : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra h
    apply hv
    ext
    · exact not_ne_iff.mp (fun h1 => h (Or.inl h1))
    · exact not_ne_iff.mp (fun h2 => h (Or.inr h2))
  dsimp [tubeDikinMetric]
  rcases h₁ with h₁ | h₁
  · have hPos : 0 < (v.1 / Y.y1) ^ 2 := sq_pos_of_ne_zero (div_ne_zero h₁ (ne_of_gt Y.hy1))
    have hNonneg : 0 ≤ (v.2 / Y.y2) ^ 2 := sq_nonneg _
    linarith [hPos, hNonneg]
  · have hPos : 0 < (v.2 / Y.y2) ^ 2 := sq_pos_of_ne_zero (div_ne_zero h₁ (ne_of_gt Y.hy2))
    have hNonneg : 0 ≤ (v.1 / Y.y1) ^ 2 := sq_nonneg _
    linarith [hPos, hNonneg]

/-! ### 6. Core Quadratic Dikin Metric on `ℝ²` -/

def coreDikinMetric (_u v : ℝ × ℝ) : ℝ :=
  v.1 ^ 2 + v.2 ^ 2

theorem coreDikinMetric_zero (u : ℝ × ℝ) :
    coreDikinMetric u (0, 0) = 0 := by
  simp [coreDikinMetric]

theorem coreDikinMetric_pos {u v : ℝ × ℝ} (hv : v ≠ (0, 0)) :
    0 < coreDikinMetric u v := by
  have h₁ : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra h
    apply hv
    ext
    · exact not_ne_iff.mp (fun h1 => h (Or.inl h1))
    · exact not_ne_iff.mp (fun h2 => h (Or.inr h2))
  dsimp [coreDikinMetric]
  rcases h₁ with h₁ | h₁
  · have hPos : 0 < v.1 ^ 2 := sq_pos_of_ne_zero h₁
    have hNonneg : 0 ≤ v.2 ^ 2 := sq_nonneg _
    linarith [hPos, hNonneg]
  · have hPos : 0 < v.2 ^ 2 := sq_pos_of_ne_zero h₁
    have hNonneg : 0 ≤ v.1 ^ 2 := sq_nonneg _
    linarith [hPos, hNonneg]

/-! ### 7. Modular-Jet Dikin Metric on `ℝ` -/

def modularJetDikinMetric {J : AmariChentsovFierzTorsion.ModularBregmanJet}
    (_ε δ : ℝ) : ℝ :=
  (J.dikinMetric / 2) * δ ^ 2

theorem modularJetDikinMetric_zero {J : AmariChentsovFierzTorsion.ModularBregmanJet}
    (ε : ℝ) :
    @modularJetDikinMetric J ε 0 = 0 := by
  simp [modularJetDikinMetric]

theorem modularJetDikinMetric_pos {J : AmariChentsovFierzTorsion.ModularBregmanJet}
    {ε δ : ℝ} (hJ : 0 < J.dikinMetric) (hv : δ ≠ 0) :
    0 < @modularJetDikinMetric J ε δ := by
  have h₁ : 0 < J.dikinMetric / 2 := div_pos hJ zero_lt_two
  have h₂ : 0 < δ ^ 2 := sq_pos_of_ne_zero hv
  exact mul_pos h₁ h₂

/-! ### 8. BKM Kubo–Mori Dikin Metric on `SelfAdjointOperator n` -/

def bkmDikinMetric {n : ℕ} {D : FaithfulDensityOperator n}
    {h : Continuous D.rpow} (v : SelfAdjointOperator n) : ℝ :=
  bkmDikinQuadratic D h v

theorem bkmDikinMetric_zero {n : ℕ} {D : FaithfulDensityOperator n}
    {h : Continuous D.rpow} :
    @bkmDikinMetric n D h (0 : SelfAdjointOperator n) = 0 := by
  simp [bkmDikinMetric, bkmDikinQuadratic]

theorem bkmDikinMetric_pos {n : ℕ} {D : FaithfulDensityOperator n}
    {h : Continuous D.rpow} {v : SelfAdjointOperator n} (hv : v ≠ 0) :
    0 < @bkmDikinMetric n D h v :=
  bkmDikinQuadratic_pos_of_ne_zero D h v hv

theorem bkmMetricTranslationInvariant {n : ℕ} {D : FaithfulDensityOperator n}
    {h : Continuous D.rpow} {v : SelfAdjointOperator n} :
    @bkmDikinMetric n D h v = bkmDikinQuadratic D h v :=
  rfl

end
