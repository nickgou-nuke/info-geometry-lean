/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import InfoGeometry.Physics.WillertonIsbellAmariDuality

/-!
# Audit Module: WillertonIsbellAmariDualityAudit

Automated kernel verification of Section 5.97:
Simon Willerton's Isbell Duality, Legendre–Fenchel Adjunction, and Amari Information Slack.
-/

namespace InfoGeometry.Physics.WillertonIsbellAmariAudit

set_option linter.unusedVariables false

open scoped BigOperators
open InfoGeometry.Physics.WillertonIsbellAmari

-- 1. Signature and Type Verification

#check (costTensor_assoc : ∀ (a b c : ℝ), costTensor (costTensor a b) c = costTensor a (costTensor b c))
#check (costTensor_unit_left : ∀ (a : ℝ), costTensor costUnit a = a)
#check (costTensor_unit_right : ∀ (a : ℝ), costTensor a costUnit = a)

#check (pairing_comm : ∀ {D : ℕ} (x y : Fin D → ℝ), pairing x y = pairing y x)
#check (pairing_add_left : ∀ {D : ℕ} (x1 x2 y : Fin D → ℝ), pairing (fun i => x1 i + x2 i) y = pairing x1 y + pairing x2 y)
#check (pairing_sub_left : ∀ {D : ℕ} (x1 x2 y : Fin D → ℝ), pairing (fun i => x1 i - x2 i) y = pairing x1 y - pairing x2 y)
#check (pairing_sub_right : ∀ {D : ℕ} (x y1 y2 : Fin D → ℝ), pairing x (fun i => y1 i - y2 i) = pairing x y1 - pairing x y2)
#check (pairing_smul_left : ∀ {D : ℕ} (c : ℝ) (x y : Fin D → ℝ), pairing (fun i => c * x i) y = c * pairing x y)

#check (fenchel_young_slack_nonneg :
  ∀ {D : ℕ} (P : IsbellLegendrePair D) (x y : Fin D → ℝ), 0 ≤ adjunctionSlack P x y)

#check (fenchel_young_slack_at_contact :
  ∀ {D : ℕ} (P : IsbellLegendrePair D) (x : Fin D → ℝ), adjunctionSlack P x (P.contact_map x) = 0)

#check (biconjugate_at_contact :
  ∀ {D : ℕ} (P : IsbellLegendrePair D) (x : Fin D → ℝ),
    pairing x (P.contact_map x) - P.f_star (P.contact_map x) = P.f x)

#check (bregmanDivergence_nonneg :
  ∀ {D : ℕ} (P : IsbellLegendrePair D) (theta1 theta2 : Fin D → ℝ),
    0 ≤ bregmanDivergence P theta1 theta2)

#check (bregmanDivergence_self :
  ∀ {D : ℕ} (P : IsbellLegendrePair D) (theta : Fin D → ℝ),
    bregmanDivergence P theta theta = 0)

#check (bregman_three_point_identity :
  ∀ {D : ℕ} (P : IsbellLegendrePair D) (theta1 theta2 theta3 : Fin D → ℝ),
    bregmanDivergence P theta1 theta3 - bregmanDivergence P theta1 theta2 - bregmanDivergence P theta2 theta3 =
    pairing (fun i => theta1 i - theta2 i) (fun i => P.contact_map theta2 i - P.contact_map theta3 i))

#check (amari_generalized_pythagorean :
  ∀ {D : ℕ} (P : IsbellLegendrePair D) (theta1 theta2 theta3 : Fin D → ℝ)
    (h_ortho : pairing (fun i => theta1 i - theta2 i) (fun i => P.contact_map theta2 i - P.contact_map theta3 i) = 0),
    bregmanDivergence P theta1 theta3 =
    bregmanDivergence P theta1 theta2 + bregmanDivergence P theta2 theta3)

#check (chuDual_eval :
  ∀ {X Y K : Type*} (C : ChuSpace X Y K) (x : X) (y : Y),
    (chuDual C).eval y x = C.eval x y)

#check (chuDual_involutive :
  ∀ {X Y K : Type*} (C : ChuSpace X Y K),
    (chuDual (chuDual C)).eval = C.eval)

#check (isbellChuSpace_symmetric :
  ∀ (D : ℕ) (x y : Fin D → ℝ),
    (isbellChuSpace D).eval x y = (chuDual (isbellChuSpace D)).eval x y)

#check (willerton_isbell_amari_duality_synthesis :
  ∀ {D : ℕ} (P : IsbellLegendrePair D) (x y z : Fin D → ℝ) (c : ℝ)
    (a b : ℝ) (theta1 theta2 theta3 : Fin D → ℝ)
    (h_ortho : pairing (fun i => theta1 i - theta2 i) (fun i => P.contact_map theta2 i - P.contact_map theta3 i) = 0),
    (costTensor (costTensor a b) c = costTensor a (costTensor b c)) ∧
    (costTensor costUnit a = a) ∧
    (pairing x y = pairing y x) ∧
    (pairing (fun i => x i + y i) z = pairing x z + pairing y z) ∧
    (pairing (fun i => c * x i) y = c * pairing x y) ∧
    (0 ≤ adjunctionSlack P x y) ∧
    (adjunctionSlack P x (P.contact_map x) = 0) ∧
    (pairing x (P.contact_map x) - P.f_star (P.contact_map x) = P.f x) ∧
    (0 ≤ bregmanDivergence P x y) ∧
    (bregmanDivergence P x x = 0) ∧
    (bregmanDivergence P theta1 theta3 - bregmanDivergence P theta1 theta2 - bregmanDivergence P theta2 theta3 =
     pairing (fun i => theta1 i - theta2 i) (fun i => P.contact_map theta2 i - P.contact_map theta3 i)) ∧
    (bregmanDivergence P theta1 theta3 = bregmanDivergence P theta1 theta2 + bregmanDivergence P theta2 theta3) ∧
    ((chuDual (chuDual (isbellChuSpace D))).eval = (isbellChuSpace D).eval) ∧
    ((isbellChuSpace D).eval x y = (chuDual (isbellChuSpace D)).eval x y))

#check (makeCertifiedWillertonIsbellAmariDualitySynthesis :
  CertifiedWillertonIsbellAmariDualitySynthesis)

-- 2. Axiom Footprint Verification
#print axioms costTensor_assoc
#print axioms costTensor_unit_left
#print axioms costTensor_unit_right
#print axioms pairing_comm
#print axioms pairing_add_left
#print axioms pairing_sub_left
#print axioms pairing_sub_right
#print axioms pairing_smul_left
#print axioms fenchel_young_slack_nonneg
#print axioms fenchel_young_slack_at_contact
#print axioms biconjugate_at_contact
#print axioms bregmanDivergence_nonneg
#print axioms bregmanDivergence_self
#print axioms bregman_three_point_identity
#print axioms amari_generalized_pythagorean
#print axioms chuDual_eval
#print axioms chuDual_involutive
#print axioms isbellChuSpace_symmetric
#print axioms willerton_isbell_amari_duality_synthesis
#print axioms makeCertifiedWillertonIsbellAmariDualitySynthesis

end InfoGeometry.Physics.WillertonIsbellAmariAudit
