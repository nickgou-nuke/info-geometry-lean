import Mathlib.Tactic
import InfoGeometry.External.Auto.tomita_kms_v4

/-!
# Hestenes-Krein carrier and colimit bridge

This file packages the finite algebraic spine that the repository already
supports:

* `J_cpx` is the bivector-rotor replacement for `i`;
* `J_mod` is the modular/Krein reflection;
* conjugation by `J_mod` is bracket-compatible for the commutator bracket;
* a stage tower records the finite embedding/compatibility data;
* a colimit record packages the functorial lift interface.

This is theorem-honest and finite.  It does not claim analytic Tomita
continuation or an actual completed Hilbert-space limit.
-/

noncomputable section

namespace HestenesKreinColimitBridge

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The bivector rotor / real `i` replacement. -/
def rotorUnit : M2R := J_cpx

/-- The modular/Krein reflection. -/
def mirrorUnit : M2R := J_mod

/-- Commutator bracket on the finite matrix carrier. -/
def commutator (A B : M2R) : M2R := A * B - B * A

/-- If `Q * P = 1`, conjugation `A ↦ P * A * Q` preserves commutators. -/
theorem conjAct_commutator (P Q : M2R) (hQP : Q * P = 1) (A B : M2R) :
    (P * A * Q) * (P * B * Q) - (P * B * Q) * (P * A * Q) =
    P * (A * B - B * A) * Q := by
  calc
    (P * A * Q) * (P * B * Q) - (P * B * Q) * (P * A * Q)
        = (P * A * (Q * P) * B * Q) - (P * B * (Q * P) * A * Q) := by
          simp [Matrix.mul_assoc]
    _ = (P * A * 1 * B * Q) - (P * B * 1 * A * Q) := by rw [hQP]
    _ = P * (A * B - B * A) * Q := by
      simp [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]

/-- Left multiplication by a fixed matrix. -/
def leftMult (A : M2R) : M2R →ₗ[ℝ] M2R where
  toFun := fun X => A * X
  map_add' := by
    intro X Y
    simp [Matrix.mul_add]
  map_smul' := by
    intro c X
    simp

/-- Conjugation by a fixed matrix. -/
def conjugate (A : M2R) : M2R →ₗ[ℝ] M2R where
  toFun := fun X => A * X * A
  map_add' := by
    intro X Y
    simp [mul_add, add_mul, mul_assoc]
  map_smul' := by
    intro c X
    simp [mul_assoc]

@[simp] theorem rotorUnit_sq :
    rotorUnit * rotorUnit = -(1 : M2R) := J_cpx_sq_neg_I

@[simp] theorem mirrorUnit_sq :
    mirrorUnit * mirrorUnit = (1 : M2R) := J_mod_sq_I

/-- The modular mirror flips the bivector rotor. -/
theorem mirrorUnit_rotorUnit_neg :
    mirrorUnit * rotorUnit * mirrorUnit = -rotorUnit := by
  simpa [rotorUnit, mirrorUnit] using J_mod_commutant

/-- Left multiplication by the bivector rotor squares to `-id`. -/
theorem leftMult_rotor_sq (X : M2R) :
    leftMult rotorUnit (leftMult rotorUnit X) = -X := by
  simp [leftMult]
  rw [← Matrix.mul_assoc, rotorUnit_sq]
  simp

/-- Conjugation by the modular mirror is an involution. -/
theorem conjugate_mirror_sq (X : M2R) :
    conjugate mirrorUnit (conjugate mirrorUnit X) = X := by
  simp [conjugate]
  simp [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, mirrorUnit_sq]
  simp

/-- Conjugation by the modular mirror preserves the commutator bracket. -/
theorem conjugate_preserves_commutator (A B : M2R) :
    conjugate mirrorUnit (commutator A B) =
      commutator (conjugate mirrorUnit A) (conjugate mirrorUnit B) := by
  simpa [commutator, conjugate] using
    (conjAct_commutator mirrorUnit mirrorUnit J_mod_sq_I A B).symm

/-- A finite carrier stage: rotor, mirror, and bracket data. -/
structure HestenesKreinStage where
  Carrier : Type*
  [hAdd : AddCommGroup Carrier]
  [hMod : Module ℝ Carrier]
  rotor : Carrier →ₗ[ℝ] Carrier
  mirror : Carrier →ₗ[ℝ] Carrier
  bracket : Carrier → Carrier → Carrier
  rotor_sq : ∀ x : Carrier, rotor (rotor x) = -x
  mirror_sq : ∀ x : Carrier, mirror (mirror x) = x
  bracket_mirror : ∀ x y : Carrier, mirror (bracket x y) = bracket (mirror x) (mirror y)

attribute [instance] HestenesKreinStage.hAdd HestenesKreinStage.hMod

/-- The concrete `2×2` matrix stage coming from the Tomita/Krein rotor pair. -/
def matrixStage : HestenesKreinStage where
  Carrier := M2R
  rotor := leftMult rotorUnit
  mirror := conjugate mirrorUnit
  bracket := commutator
  rotor_sq := leftMult_rotor_sq
  mirror_sq := conjugate_mirror_sq
  bracket_mirror := conjugate_preserves_commutator

/-- A tower of finite Hestenes-Krein stages with embeddings. -/
structure HestenesKreinTower where
  Stage : ℕ → Type*
  [hAdd : ∀ n, AddCommGroup (Stage n)]
  [hMod : ∀ n, Module ℝ (Stage n)]
  rotor : ∀ n, Stage n →ₗ[ℝ] Stage n
  mirror : ∀ n, Stage n →ₗ[ℝ] Stage n
  bracket : ∀ n, Stage n → Stage n → Stage n
  emb : ∀ n, Stage n →ₗ[ℝ] Stage (n + 1)
  rotor_compat : ∀ n (x : Stage n), emb n (rotor n x) = rotor (n + 1) (emb n x)
  mirror_compat : ∀ n (x : Stage n), emb n (mirror n x) = mirror (n + 1) (emb n x)
  bracket_compat : ∀ n (x y : Stage n),
    emb n (bracket n x y) = bracket (n + 1) (emb n x) (emb n y)

attribute [instance] HestenesKreinTower.hAdd HestenesKreinTower.hMod

/-- A colimit-lift interface mirroring the repo's direct-limit style. -/
structure HestenesKreinCompatibleLift (T : HestenesKreinTower) where
  Carrier : Type*
  [hAdd : AddCommGroup Carrier]
  [hMod : Module ℝ Carrier]
  inc : ∀ n, T.Stage n →ₗ[ℝ] Carrier
  hInc : ∀ n, (inc (n + 1)).comp (T.emb n) = inc n
  Jlim : Carrier →ₗ[ℝ] Carrier
  Ilim : Carrier →ₗ[ℝ] Carrier
  J_compat : ∀ n (x : T.Stage n), Jlim (inc n x) = inc n (T.mirror n x)
  I_compat : ∀ n (x : T.Stage n), Ilim (inc n x) = inc n (T.rotor n x)

attribute [instance] HestenesKreinCompatibleLift.hAdd HestenesKreinCompatibleLift.hMod

/-- The one-stage constant tower built from the concrete matrix carrier. -/
def oneStageTower : HestenesKreinTower where
  Stage := fun _ => M2R
  rotor := fun _ => matrixStage.rotor
  mirror := fun _ => matrixStage.mirror
  bracket := fun _ => matrixStage.bracket
  emb := fun _ => LinearMap.id
  rotor_compat := by
    intro n x
    rfl
  mirror_compat := by
    intro n x
    rfl
  bracket_compat := by
    intro n x y
    rfl

/-- The corresponding one-stage compatible-lift package. -/
def oneStageCompatibleLift : HestenesKreinCompatibleLift oneStageTower where
  Carrier := M2R
  inc := fun _ => LinearMap.id
  hInc := by
    intro n
    ext X
    rfl
  Jlim := matrixStage.mirror
  Ilim := matrixStage.rotor
  J_compat := by
    intro n x
    rfl
  I_compat := by
    intro n x
    rfl

end HestenesKreinColimitBridge
