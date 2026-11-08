/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.CarrierInnerModularBoundary

/-!
# Naturality of the complex-parameter inner action on the matrix tower

For a fixed finite attention seed, this file transports its complex
exponential conjugation to every full matrix stage above the seed and proves
compatibility with the tower maps and the algebraic direct-limit readout.
The results are algebraic: no analytic continuation, holomorphicity,
completion, or unitarity claim for arbitrary complex parameters is made.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.CarrierInnerComplexFlowNaturality

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.QuantumContext.CarrierInnerModularBoundary

/-- The fixed-seed complex exponential transported to stage `n`. -/
def complexModularExponentialAtStage (k n : ℕ) (hkn : k ≤ n)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) : MatrixStage n :=
  rawMap hkn (complexModularExponential k logits β z)

/-- The fixed-seed complex inner action on an arbitrary full matrix at stage
`n`, for `k ≤ n`. -/
def flowAtStage (k n : ℕ) (hkn : k ≤ n)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ)
    (A : MatrixStage n) : MatrixStage n :=
  complexModularExponentialAtStage k n hkn logits β z * A *
    complexModularExponentialAtStage k n hkn logits β (-z)

/-- Composition of the concrete tower maps, evaluated on a matrix. -/
theorem rawMap_comp_apply {i j n : ℕ} (hij : i ≤ j) (hjn : j ≤ n)
    (A : MatrixStage i) :
    rawMap hjn (rawMap hij A) = rawMap (le_trans hij hjn) A := by
  exact congrArg (fun f : MatrixStage i →⋆ₐ[ℂ] MatrixStage n => f A)
    (concreteMap_comp hij hjn)

/-- Naturality of the full-matrix stage action under every bonding map above
the fixed seed. -/
theorem flowAtStage_natural (k m n : ℕ) (hkm : k ≤ m) (hmn : m ≤ n)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) (A : MatrixStage m) :
    rawMap hmn (flowAtStage k m hkm logits β z A) =
      flowAtStage k n (le_trans hkm hmn) logits β z (rawMap hmn A) := by
  simp only [flowAtStage, complexModularExponentialAtStage, map_mul]
  rw [rawMap_comp_apply hkm hmn,
    rawMap_comp_apply hkm hmn]

/-- Readout of the stage action agrees with the complex inner action on the
actual algebraic matrix direct-limit carrier. -/
theorem carrierComplexModularFlow_stage (k n : ℕ) (hkn : k ≤ n)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) (A : MatrixStage n) :
    carrierComplexModularFlow k logits β z (stageInjection n A) =
      stageInjection n (flowAtStage k n hkn logits β z A) := by
  change stageInjection k (complexModularExponential k logits β z) *
      stageInjection n A *
        stageInjection k (complexModularExponential k logits β (-z)) =
    stageInjection n
      (complexModularExponentialAtStage k n hkn logits β z * A *
        complexModularExponentialAtStage k n hkn logits β (-z))
  rw [← stageInjection_transition hkn
      (complexModularExponential k logits β z),
    ← stageInjection_transition hkn
      (complexModularExponential k logits β (-z))]
  rw [← stageInjection_mul, ← stageInjection_mul]
  rfl

end InfoGeometry.QuantumContext.CarrierInnerComplexFlowNaturality

end
