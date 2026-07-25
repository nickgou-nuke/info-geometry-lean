import InfoGeometry.Algebra.OSp12
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Algebra.SupergradedBracket

noncomputable section

namespace InfoGeometry.Algebra.OSp12InductiveColimit

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.Algebra.OSp12

variable {V : Type} [AddCommGroup V] [Module ℝ V]

local notation "EndV" => OSp12.Op V
local notation "StageFamily" => (fun _ : ℕ => EndV)

abbrev Limit (bond : ∀ _n : ℕ, EndV →+* EndV) : Type :=
  DirectLimitSuperClosure (Stage := StageFamily) bond

def ofStage (bond : ∀ _n : ℕ, EndV →+* EndV) (n : ℕ) : EndV →+* Limit bond :=
  directLimitOf (Stage := StageFamily) bond n

@[simp] theorem ofStage_apply_bond
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (n : ℕ) (x : EndV) :
    ofStage (bond := bond) (n + 1) (bond n x) = ofStage (bond := bond) n x := by
  exact directLimitOf_bond (Stage := StageFamily) bond n x

section DirectLimitRelations

variable
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))

@[simp] theorem directLimit_hΓ
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    φ (surf n).Γ * φ (surf n).Γ = 1 :=
  congrArg (ofStage (bond := bond) n) (surf n).hΓ

@[simp] theorem directLimit_G1_odd
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    φ ((surf n).Γ * (surf n).G1) = -φ ((surf n).G1 * (surf n).Γ) :=
  congrArg (ofStage (bond := bond) n) (surf n).G1_odd

@[simp] theorem directLimit_H_Ep
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false false (φ (surf n).H) (φ (surf n).Ep) =
      (2 : ℝ) • φ (surf n).Ep :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).H_Ep

@[simp] theorem directLimit_H_Em
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false false (φ (surf n).H) (φ (surf n).Em) =
      (-2 : ℝ) • φ (surf n).Em :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).H_Em

@[simp] theorem directLimit_Ep_Em
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false false (φ (surf n).Ep) (φ (surf n).Em) = φ (surf n).H :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).Ep_Em

@[simp] theorem directLimit_H_G1
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false true (φ (surf n).H) (φ (surf n).G1) = φ (surf n).G1 :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).H_G1

@[simp] theorem directLimit_H_G2
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false true (φ (surf n).H) (φ (surf n).G2) =
      (-1 : ℝ) • φ (surf n).G2 :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).H_G2

@[simp] theorem directLimit_Ep_G2
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false true (φ (surf n).Ep) (φ (surf n).G2) = φ (surf n).G1 :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).Ep_G2

@[simp] theorem directLimit_Em_G1
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false true (φ (surf n).Em) (φ (surf n).G1) = φ (surf n).G2 :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).Em_G1

@[simp] theorem directLimit_G1_G1
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket true true (φ (surf n).G1) (φ (surf n).G1) =
      (2 : ℝ) • φ (surf n).Ep :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).G1_G1

@[simp] theorem directLimit_G2_G2
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket true true (φ (surf n).G2) (φ (surf n).G2) =
      (-2 : ℝ) • φ (surf n).Em :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).G2_G2

@[simp] theorem directLimit_G1_G2
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket true true (φ (surf n).G1) (φ (surf n).G2) = -φ (surf n).H :=
  superBracket_eq_transport (ofStage (bond := bond) n) (surf n).G1_G2

end DirectLimitRelations

end InfoGeometry.Algebra.OSp12InductiveColimit
