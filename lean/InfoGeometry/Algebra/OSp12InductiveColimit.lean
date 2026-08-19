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

@[simp] theorem directLimit_hΓ
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    φ (surf n).Γ * φ (surf n).Γ = 1 :=
  by
    dsimp
    simpa using congrArg (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.hΓ (hSurf n))

@[simp] theorem directLimit_G1_odd
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    φ ((surf n).Γ * (surf n).G1) = -φ ((surf n).G1 * (surf n).Γ) :=
  by
    dsimp
    simpa using congrArg (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.G1_odd (hSurf n))

@[simp] theorem directLimit_H_Ep
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false false (φ (surf n).H) (φ (surf n).Ep) =
      φ ((2 : ℝ) • (surf n).Ep) :=
  by
    dsimp
    exact superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.H_Ep (hSurf n))

@[simp] theorem directLimit_H_Em
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false false (φ (surf n).H) (φ (surf n).Em) =
      φ ((-2 : ℝ) • (surf n).Em) :=
  by
    dsimp
    exact superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.H_Em (hSurf n))

@[simp] theorem directLimit_Ep_Em
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false false (φ (surf n).Ep) (φ (surf n).Em) = φ (surf n).H :=
  by
    dsimp
    exact superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.Ep_Em (hSurf n))

@[simp] theorem directLimit_H_G1
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false true (φ (surf n).H) (φ (surf n).G1) = φ (surf n).G1 :=
  by
    dsimp
    simpa using superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.H_G1 (hSurf n))

@[simp] theorem directLimit_H_G2
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false true (φ (surf n).H) (φ (surf n).G2) =
      φ ((-1 : ℝ) • (surf n).G2) :=
  by
    dsimp
    exact superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.H_G2 (hSurf n))

@[simp] theorem directLimit_Ep_G2
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false true (φ (surf n).Ep) (φ (surf n).G2) = φ (surf n).G1 :=
  by
    dsimp
    exact superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.Ep_G2 (hSurf n))

@[simp] theorem directLimit_Em_G1
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket false true (φ (surf n).Em) (φ (surf n).G1) = φ (surf n).G2 :=
  by
    dsimp
    exact superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.Em_G1 (hSurf n))

@[simp] theorem directLimit_G1_G1
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket true true (φ (surf n).G1) (φ (surf n).G1) =
      φ ((2 : ℝ) • (surf n).Ep) :=
  by
    dsimp
    exact superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.G1_G1 (hSurf n))

@[simp] theorem directLimit_G2_G2
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket true true (φ (surf n).G2) (φ (surf n).G2) =
      φ ((-2 : ℝ) • (surf n).Em) :=
  by
    dsimp
    exact superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.G2_G2 (hSurf n))

@[simp] theorem directLimit_G1_G2
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (surf : ∀ n : ℕ, OperatorSurface (V := V))
    (hSurf : ∀ n : ℕ, OperatorSurfaceLaws (surf n))
    (n : ℕ) :
    let φ := ofStage (bond := bond) n
    superBracket true true (φ (surf n).G1) (φ (surf n).G2) = -φ (surf n).H :=
  by
    dsimp
    exact superBracket_eq_transport (ofStage (bond := bond) n)
      (OperatorSurfaceLaws.G1_G2 (hSurf n))

end DirectLimitRelations

end InfoGeometry.Algebra.OSp12InductiveColimit
