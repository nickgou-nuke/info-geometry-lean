/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Action.Defs
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Clifford.HestenesLorentzJordanCone

namespace InfoGeometry.Riemannian

open InfoGeometry.Clifford.Hestenes
open CliffordAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem coneAction_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Over any non-commutative `*-ring` `[Ring B] [StarRing B]`, the bilateral cone action
`(g, x) ↦ g * x * star g` satisfies the multiplicative action law
`(g₁ * g₂) * x * star (g₁ * g₂) = g₁ * (g₂ * x * star g₂) * star g₁`. -/
theorem ring_cone_action_mul
    {B : Type*} [Ring B] [StarRing B] (g₁ g₂ x : B) :
    (g₁ * g₂) * x * star (g₁ * g₂) = g₁ * (g₂ * x * star g₂) * star g₁ := by
  simp [star_mul, mul_assoc]

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M)

/-- Дефиниране на двустранното действие (Conjugation Action) чрез Clifford елемент 
    и неговия Hestenes Adjoint (reverse) оператор. -/
def coneConjugationAction (G : ClPlus Q) (X : ClPlus Q) : ClPlus Q :=
  L_action Q G (R_action Q (hestenesAdjoint Q v0 G) X)

/-- hestenesAdjoint на идентитета е идентитетът. -/
theorem hestenesAdjoint_one (hv0_norm : Q v0 = 1) : hestenesAdjoint Q v0 (1 : ClPlus Q) = 1 := by
  apply Subtype.ext
  dsimp [hestenesAdjoint]
  rw [reverse.map_one, mul_one]
  exact gamma0_sq Q v0 hv0_norm

/-- Доказателство, че идентитетът действа тривиално: 1 ⬝ X = X -/
theorem coneAction_one (hv0_norm : Q v0 = 1) (X : ClPlus Q) : coneConjugationAction Q v0 1 X = X := by
  dsimp [coneConjugationAction]
  apply Subtype.ext
  dsimp [L_action, R_action]
  have h_adj : (hestenesAdjoint Q v0 (1 : ClPlus Q)).val = 1 := by
    rw [hestenesAdjoint_one Q v0 hv0_norm]
    rfl
  rw [h_adj, mul_one, one_mul]

/-- hestenesAdjoint обръща реда на умножение (анти-автоморфизъм). -/
theorem hestenesAdjoint_mul (hv0_norm : Q v0 = 1) (G1 G2 : ClPlus Q) :
    hestenesAdjoint Q v0 (G1 * G2) = hestenesAdjoint Q v0 G2 * hestenesAdjoint Q v0 G1 := by
  apply Subtype.ext
  dsimp [hestenesAdjoint]
  rw [CliffordAlgebra.reverse.map_mul]
  have hsq := gamma0_sq Q v0 hv0_norm
  calc gamma0 Q v0 * (reverse G2.val * reverse G1.val) * gamma0 Q v0
    _ = gamma0 Q v0 * reverse G2.val * 1 * reverse G1.val * gamma0 Q v0 := by simp only [mul_assoc, mul_one]
    _ = gamma0 Q v0 * reverse G2.val * (gamma0 Q v0 * gamma0 Q v0) * reverse G1.val * gamma0 Q v0 := by rw [hsq]
    _ = (gamma0 Q v0 * reverse G2.val * gamma0 Q v0) * (gamma0 Q v0 * reverse G1.val * gamma0 Q v0) := by simp only [mul_assoc]

/-- Доказателство за свойството на съвместимост: (G1 * G2) ⬝ X = G1 ⬝ (G2 ⬝ X) -/
theorem coneAction_mul (hv0_norm : Q v0 = 1) (G1 G2 : ClPlus Q) (X : ClPlus Q) :
    coneConjugationAction Q v0 (G1 * G2) X = coneConjugationAction Q v0 G1 (coneConjugationAction Q v0 G2 X) := by
  apply Subtype.ext
  dsimp [coneConjugationAction, L_action, R_action]
  have h_adj := congrArg Subtype.val (hestenesAdjoint_mul Q v0 hv0_norm G1 G2)
  dsimp at h_adj
  rw [h_adj]
  simp only [mul_assoc]

/-- Официално регистриране на действието като MulAction в Lean 4 типажите -/
def coneConjugationMulAction (hv0_norm : Q v0 = 1) : MulAction (ClPlus Q) (ClPlus Q) where
  smul := coneConjugationAction Q v0
  one_smul := coneAction_one Q v0 hv0_norm
  mul_smul := coneAction_mul Q v0 hv0_norm

end InfoGeometry.Riemannian
