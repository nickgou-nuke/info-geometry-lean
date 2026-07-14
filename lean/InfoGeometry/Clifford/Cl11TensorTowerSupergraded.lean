import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Supergraded brackets on the finite `Cl(1,1)` tensor tower

This module connects the repository's supergraded bracket lane to the concrete
matrix tower used for repeated tensoring by the finite `Cl(1,1)` model.

The only infinite object used here is the existing algebraic direct limit from
`Cl11TensorTowerLimit`.  No topological or analytic completion is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace Cl11TensorTowerSupergraded

open InfoGeometry.Algebra.SupergradedBracket

/-- Finite stage of the matrix model for the iterated `Cl(1,1)` tensor string. -/
abbrev Stage (n : ℕ) : Type := InfoGeometry.Clifford.Cl11TensorTower.MatStage n

/-- Parity-controlled superbracket at a finite stage. -/
def stageSuperBracket (px py : Bool) {n : ℕ} (A B : Stage n) : Stage n :=
  superBracket px py A B

@[simp]
theorem stageSuperBracket_odd_odd {n : ℕ} (A B : Stage n) :
    stageSuperBracket true true A B = A * B + B * A := by
  rfl

@[simp]
theorem stageSuperBracket_even_left {n : ℕ} (py : Bool) (A B : Stage n) :
    stageSuperBracket false py A B = A * B - B * A := by
  cases py <;> rfl

@[simp]
theorem stageSuperBracket_even_right {n : ℕ} (px : Bool) (A B : Stage n) :
    stageSuperBracket px false A B = A * B - B * A := by
  cases px <;> rfl

/-- The one-step `Cl(1,1)` tensor embedding preserves superbrackets. -/
theorem stageEmbed_superBracket
    (px py : Bool) {n : ℕ} (A B : Stage n) :
    InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (stageSuperBracket px py A B) =
      stageSuperBracket px py (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A) (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n B) := by
  exact map_superBracket (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n).toRingHom px py A B

/-- Superbracket closure at one stage transports one step in the tensor string. -/
theorem stageEmbed_superBracket_eq
    (px py : Bool) {n : ℕ} {A B C : Stage n}
    (h : stageSuperBracket px py A B = C) :
    stageSuperBracket px py (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A) (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n B) =
      InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n C := by
  rw [← stageEmbed_superBracket, h]

/-- Stagewise superbracket closure along the whole finite tensor string. -/
theorem stageSuperBracketClosure_all
    (px py : Bool)
    (X Y Z : ∀ n : ℕ, Stage n)
    (h0 : SuperBracketClosureAt (Stage := Stage) px py X Y Z 0)
    (hX : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (X n) = X (n + 1))
    (hY : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (Y n) = Y (n + 1))
    (hZ : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (Z n) = Z (n + 1)) :
    ∀ n : ℕ, SuperBracketClosureAt (Stage := Stage) px py X Y Z n := by
  exact superBracketClosure_all InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond px py X Y Z h0 hX hY hZ

/-- Canonical finite-stage map into the existing algebraic direct limit. -/
abbrev ofStage (n : ℕ) : Stage n →+* InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
  InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n

/-- Canonical images in the algebraic direct limit preserve superbrackets. -/
theorem ofStage_superBracket
    (px py : Bool) {n : ℕ} (A B : Stage n) :
    ofStage n (stageSuperBracket px py A B) =
      superBracket px py (ofStage n A) (ofStage n B) := by
  exact map_superBracket (ofStage n) px py A B

/-- A finite superbracket identity gives the corresponding direct-limit image identity. -/
theorem limit_superBracket_eq
    (px py : Bool) {n : ℕ} {A B C : Stage n}
    (h : stageSuperBracket px py A B = C) :
    superBracket px py (ofStage n A) (ofStage n B) = ofStage n C := by
  rw [← ofStage_superBracket, h]

/-- Odd--odd finite closure becomes an anticommutator identity in the direct limit. -/
theorem limit_odd_odd_eq
    {n : ℕ} {A B C : Stage n}
    (h : A * B + B * A = C) :
    superBracket true true (ofStage n A) (ofStage n B) = ofStage n C := by
  exact limit_superBracket_eq true true h

/-- Even-in-left finite closure becomes a commutator identity in the direct limit. -/
theorem limit_even_left_eq
    (py : Bool) {n : ℕ} {A B C : Stage n}
    (h : A * B - B * A = C) :
    superBracket false py (ofStage n A) (ofStage n B) = ofStage n C := by
  exact limit_superBracket_eq false py h

/-- Even-in-right finite closure becomes a commutator identity in the direct limit. -/
theorem limit_even_right_eq
    (px : Bool) {n : ℕ} {A B C : Stage n}
    (h : A * B - B * A = C) :
    superBracket px false (ofStage n A) (ofStage n B) = ofStage n C := by
  cases px <;> exact limit_superBracket_eq _ false h

/-- Stagewise superbracket closure on the tensor string, viewed in the direct limit. -/
theorem limit_stageSuperBracketClosure_all
    (px py : Bool)
    (X Y Z : ∀ n : ℕ, Stage n)
    (h0 : SuperBracketClosureAt (Stage := Stage) px py X Y Z 0)
    (hX : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (X n) = X (n + 1))
    (hY : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (Y n) = Y (n + 1))
    (hZ : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (Z n) = Z (n + 1)) :
    ∀ n : ℕ,
      superBracket px py (ofStage n (X n)) (ofStage n (Y n)) = ofStage n (Z n) := by
  intro n
  exact limit_superBracket_eq px py (stageSuperBracketClosure_all px py X Y Z h0 hX hY hZ n)

/-- Stable finite tensor strings have a stage-zero superbracket value in the direct limit. -/
theorem finite_sequence_superBracket_in_limit
    (px py : Bool)
    (X Y Z : ∀ n : ℕ, Stage n)
    (h0 : SuperBracketClosureAt (Stage := Stage) px py X Y Z 0)
    (hX : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (X n) = X (n + 1))
    (hY : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (Y n) = Y (n + 1))
    (hZ : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (Z n) = Z (n + 1)) :
    ∀ n : ℕ,
      superBracket px py (ofStage n (X n)) (ofStage n (Y n)) = ofStage 0 (Z 0) := by
  intro n
  calc
    superBracket px py (ofStage n (X n)) (ofStage n (Y n)) = ofStage n (Z n) := by
      exact limit_stageSuperBracketClosure_all px py X Y Z h0 hX hY hZ n
    _ = ofStage 0 (Z 0) := by
      exact InfoGeometry.Clifford.Cl11TensorTowerLimit.finite_sequence_constant_in_limit Z hZ n

end Cl11TensorTowerSupergraded
