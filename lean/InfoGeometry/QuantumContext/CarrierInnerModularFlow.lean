/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
import InfoGeometry.Canonical.Cl11TraceGNSColimitBridge

/-!
# Fixed-seed inner automorphism action on the matrix direct limit

For one chosen finite attention seed, its stage unitaries embed into the actual
noncommutative matrix direct-limit carrier. Inner conjugation by those elements
defines a one-parameter group of *-automorphisms on every carrier element,
extending the finite-stage action. This file does not identify that action as
modular for the selected colimit state: state invariance and the KMS boundary
identity on arbitrary carrier elements are not proved here. It also does not
identify independently selected seeds at different stages or assert a
norm-continuous action on a C*-completion.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.CarrierInnerModularFlow

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
open InfoGeometry.Canonical.Cl11TraceGNSColimitBridge

/-- The stage-`k` modular unitary, viewed in the genuine matrix direct limit. -/
def carrierModularUnitary (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) : Carrier :=
  stageInjection k (modularUnitary logits β t)

@[simp]
theorem carrierModularUnitary_add (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t s : ℝ) :
    carrierModularUnitary k logits β (t + s) =
      carrierModularUnitary k logits β t * carrierModularUnitary k logits β s := by
  change stageInjection k (modularUnitary logits β (t + s)) =
    stageInjection k (modularUnitary logits β t) *
      stageInjection k (modularUnitary logits β s)
  rw [modularUnitary_add, map_mul]

@[simp]
theorem carrierModularUnitary_zero (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β : ℝ) :
    carrierModularUnitary k logits β 0 = 1 := by
  change stageInjection k (modularUnitary logits β 0) = (1 : Carrier)
  rw [modularUnitary_zero, map_one]

@[simp]
theorem carrierModularUnitary_mul_neg (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) :
    carrierModularUnitary k logits β t * carrierModularUnitary k logits β (-t) = 1 := by
  rw [← carrierModularUnitary_add]
  simp

@[simp]
theorem carrierModularUnitary_neg_mul (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) :
    carrierModularUnitary k logits β (-t) * carrierModularUnitary k logits β t = 1 := by
  rw [← carrierModularUnitary_add]
  simp

@[simp]
theorem star_carrierModularUnitary (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) :
    star (carrierModularUnitary k logits β t) =
      carrierModularUnitary k logits β (-t) := by
  simp [carrierModularUnitary, modularUnitary_star]

/-- Inner conjugation by the selected finite-stage modular unitary, acting on
the entire algebraic direct-limit carrier. -/
def carrierModularFlow (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) (x : Carrier) : Carrier :=
  carrierModularUnitary k logits β t * x *
    carrierModularUnitary k logits β (-t)

@[simp]
theorem carrierModularFlow_zero (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β : ℝ) (x : Carrier) :
    carrierModularFlow k logits β 0 x = x := by
  simp [carrierModularFlow]

@[simp]
theorem carrierModularFlow_one (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) :
    carrierModularFlow k logits β t 1 = 1 := by
  simp only [carrierModularFlow, mul_one]
  exact carrierModularUnitary_mul_neg k logits β t

theorem carrierModularFlow_add (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t s : ℝ) (x : Carrier) :
    carrierModularFlow k logits β (t + s) x =
      carrierModularFlow k logits β t (carrierModularFlow k logits β s x) := by
  simp only [carrierModularFlow, carrierModularUnitary_add]
  rw [show -(t + s) = -s + -t by rw [neg_add_rev]]
  simp only [carrierModularUnitary_add]
  simp only [mul_assoc]

theorem carrierModularFlow_mul (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) (x y : Carrier) :
    carrierModularFlow k logits β t (x * y) =
      carrierModularFlow k logits β t x * carrierModularFlow k logits β t y := by
  simp only [carrierModularFlow]
  calc
    carrierModularUnitary k logits β t * (x * y) *
        carrierModularUnitary k logits β (-t) =
      carrierModularUnitary k logits β t *
        (x * (y * carrierModularUnitary k logits β (-t))) := by
          simp only [mul_assoc]
    _ = carrierModularUnitary k logits β t *
        (x * (carrierModularUnitary k logits β (-t) *
          (carrierModularUnitary k logits β t *
            (y * carrierModularUnitary k logits β (-t))))) := by
          calc
            _ = carrierModularUnitary k logits β t *
                (x * ((carrierModularUnitary k logits β (-t) *
                  carrierModularUnitary k logits β t) *
                  (y * carrierModularUnitary k logits β (-t)))) := by
                    rw [carrierModularUnitary_neg_mul, one_mul]
            _ = _ := by simp only [mul_assoc]
    _ = (carrierModularUnitary k logits β t * x *
          carrierModularUnitary k logits β (-t)) *
        (carrierModularUnitary k logits β t * y *
          carrierModularUnitary k logits β (-t)) := by
          simp only [mul_assoc]

theorem carrierModularFlow_add_arg (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) (x y : Carrier) :
    carrierModularFlow k logits β t (x + y) =
      carrierModularFlow k logits β t x + carrierModularFlow k logits β t y := by
  simp only [carrierModularFlow]
  rw [mul_add, add_mul]

theorem carrierModularFlow_star (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) (x : Carrier) :
    carrierModularFlow k logits β t (star x) =
      star (carrierModularFlow k logits β t x) := by
  simp only [carrierModularFlow, star_mul, star_carrierModularUnitary, neg_neg]
  rw [mul_assoc]

theorem carrierModularFlow_inverse (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) (x : Carrier) :
    carrierModularFlow k logits β (-t)
        (carrierModularFlow k logits β t x) = x := by
  rw [← carrierModularFlow_add]
  simp

/-- On the selected finite matrix stage, the direct-limit action agrees with
the already-proved matrix modular flow on every full matrix observable. -/
theorem carrierModularFlow_stage (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) (A : MatrixStage k) :
    carrierModularFlow k logits β t (stageInjection k A) =
      stageInjection k (modularFlow logits β t A) := by
  change stageInjection k (modularUnitary logits β t) * stageInjection k A *
      stageInjection k (modularUnitary logits β (-t)) =
    stageInjection k (modularUnitary logits β t * A *
      modularUnitary logits β (-t))
  rw [← stageInjection_mul, ← stageInjection_mul]

/-- Two off-diagonal matrix units at stage one remain noncommuting after their
canonical injection into `Carrier`; this witnesses that the action's carrier
is the full noncommutative matrix direct limit. -/
def stageOneE01 : MatrixStage 1 :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

def stageOneE10 : MatrixStage 1 :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem carrier_noncommuting_matrix_units :
    stageInjection 1 stageOneE01 * stageInjection 1 stageOneE10 ≠
      stageInjection 1 stageOneE10 * stageInjection 1 stageOneE01 := by
  intro h
  have hstage : stageOneE01 * stageOneE10 = stageOneE10 * stageOneE01 := by
    apply cuntzStageInjection_injective 1
    simpa only [map_mul] using h
  have h00 := congrFun (congrFun hstage 0) 0
  simp [stageOneE01, stageOneE10, Matrix.mul_apply] at h00

end InfoGeometry.QuantumContext.CarrierInnerModularFlow

end
