import InfoGeometry.Algebra.OSp12InductiveColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Algebra.SupergradedBracket

/-!
# OSp(1|2) Colimit Readback Bridge

Compatible-cone readback of OSp(1|2) superbracket relations from the genuine
algebraic direct limit into any downstream target EndV.

Each RHS carries the scalar multiplication inside `toLimit n` — the readback
theorem is exactly the image of the finite-stage relation through the ring hom.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 40000

namespace InfoGeometry.Algebra.OSp12ColimitReadback

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.Algebra.OSp12InductiveColimit
open InfoGeometry.Algebra.OSp12

variable {V : Type} [AddCommGroup V] [Module ℝ V]

local notation "EndV" => OSp12.Op V
local notation "StageFamily" => (fun _ : ℕ => EndV)

/--
Readback `[H, Ep] = toLimit n (2·Ep)` through the genuine direct limit.
-/
theorem readback_H_Ep
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (n : ℕ) :
    superBracket false false (toLimit n (surf n).H) (toLimit n (surf n).Ep) =
      toLimit n ((2 : ℝ) • (surf n).Ep) := by
  have hcolim : superBracket false false
      (ofStage (bond := bond) n ((surf n).H))
      (ofStage (bond := bond) n ((surf n).Ep)) =
    ofStage (bond := bond) n ((2 : ℝ) • (surf n).Ep) := by
    simpa [two_smul] using
      superBracket_eq_transport (ofStage (bond := bond) n) (surf n).H_Ep
  let φ := directLimitLift (Stage := StageFamily) bond toLimit hcone
  have hread := superBracket_eq_transport φ hcolim
  unfold ofStage at hread
  repeat rw [directLimitLift_of (Stage := StageFamily) bond toLimit hcone n] at hread
  exact hread

/--
Readback `[H, Em] = toLimit n (-2·Em)` through the genuine direct limit.
-/
theorem readback_H_Em
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (n : ℕ) :
    superBracket false false (toLimit n (surf n).H) (toLimit n (surf n).Em) =
      toLimit n ((-2 : ℝ) • (surf n).Em) := by
  have hcolim : superBracket false false
      (ofStage (bond := bond) n ((surf n).H))
      (ofStage (bond := bond) n ((surf n).Em)) =
    ofStage (bond := bond) n ((-2 : ℝ) • (surf n).Em) := by
    simpa [two_smul] using
      superBracket_eq_transport (ofStage (bond := bond) n) (surf n).H_Em
  let φ := directLimitLift (Stage := StageFamily) bond toLimit hcone
  have hread := superBracket_eq_transport φ hcolim
  unfold ofStage at hread
  repeat rw [directLimitLift_of (Stage := StageFamily) bond toLimit hcone n] at hread
  exact hread

/--
Readback `[Ep, Em] = toLimit n H` through the genuine direct limit.
-/
theorem readback_Ep_Em
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (n : ℕ) :
    superBracket false false (toLimit n (surf n).Ep) (toLimit n (surf n).Em) =
      toLimit n (surf n).H := by
  have hcolim : superBracket false false
      (ofStage (bond := bond) n ((surf n).Ep))
      (ofStage (bond := bond) n ((surf n).Em)) =
    ofStage (bond := bond) n ((surf n).H) := by
    exact superBracket_eq_transport (ofStage (bond := bond) n) (surf n).Ep_Em
  let φ := directLimitLift (Stage := StageFamily) bond toLimit hcone
  have hread := superBracket_eq_transport φ hcolim
  unfold ofStage at hread
  repeat rw [directLimitLift_of (Stage := StageFamily) bond toLimit hcone n] at hread
  exact hread

/--
Readback `{G1, G1} = toLimit n (2·Ep)` through the genuine direct limit.
-/
theorem readback_G1_G1
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (n : ℕ) :
    superBracket true true (toLimit n (surf n).G1) (toLimit n (surf n).G1) =
      toLimit n ((2 : ℝ) • (surf n).Ep) := by
  have hcolim : superBracket true true
      (ofStage (bond := bond) n ((surf n).G1))
      (ofStage (bond := bond) n ((surf n).G1)) =
    ofStage (bond := bond) n ((2 : ℝ) • (surf n).Ep) := by
    simpa [two_smul] using
      superBracket_eq_transport (ofStage (bond := bond) n) (surf n).G1_G1
  let φ := directLimitLift (Stage := StageFamily) bond toLimit hcone
  have hread := superBracket_eq_transport φ hcolim
  unfold ofStage at hread
  repeat rw [directLimitLift_of (Stage := StageFamily) bond toLimit hcone n] at hread
  exact hread

/--
Readback `{G2, G2} = toLimit n (-2·Em)` through the genuine direct limit.
-/
theorem readback_G2_G2
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (n : ℕ) :
    superBracket true true (toLimit n (surf n).G2) (toLimit n (surf n).G2) =
      toLimit n ((-2 : ℝ) • (surf n).Em) := by
  have hcolim : superBracket true true
      (ofStage (bond := bond) n ((surf n).G2))
      (ofStage (bond := bond) n ((surf n).G2)) =
    ofStage (bond := bond) n ((-2 : ℝ) • (surf n).Em) := by
    simpa [two_smul] using
      superBracket_eq_transport (ofStage (bond := bond) n) (surf n).G2_G2
  let φ := directLimitLift (Stage := StageFamily) bond toLimit hcone
  have hread := superBracket_eq_transport φ hcolim
  unfold ofStage at hread
  repeat rw [directLimitLift_of (Stage := StageFamily) bond toLimit hcone n] at hread
  exact hread

end InfoGeometry.Algebra.OSp12ColimitReadback
