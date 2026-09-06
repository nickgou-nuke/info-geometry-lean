import Mathlib
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Native conjugate-linear exchange of Zorn color sectors

This module promotes the finite carrier-level content of the downstream
`ZornColorChargeConjugation` owner to the main `InfoGeometry` surface.

The map conjugates complex coefficients and exchanges the two scalar slots and
the upper/lower color lanes. It is an involution and exchanges the two native
complex diagonal projector slots.

This carrier is the complex `SplitOctonionBraidSU3.Zorn` model and is kept
separate from the canonical `G2TrifactorSU3` Zorn carrier used by
`QCDFureyZornProjectorBridge`.

No physical charge-conjugation, CPT, or particle identification theorem is
asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDZornChargeConjugationBridge

open InfoGeometry.Physics.SplitOctonionBraidSU3

abbrev Zorn := InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn
abbrev complexConjHom : ℂ →+* ℂ := Complex.conjAe.toRingEquiv.toRingHom

/-- Upper complex diagonal projector slot. -/
def diagPlus : Zorn where
  a := 1
  u := 0
  v := 0
  b := 0

/-- Lower complex diagonal projector slot. -/
def diagMinus : Zorn where
  a := 0
  u := 0
  v := 0
  b := 1

/-- Conjugate coefficients and exchange scalar/color sectors. -/
def particleConjZorn (X : Zorn) : Zorn where
  a := complexConjHom X.b
  u := fun i => complexConjHom (X.v i)
  v := fun i => complexConjHom (X.u i)
  b := complexConjHom X.a

/-- The native Zorn conjugation is additive. -/
theorem particleConjZorn_add (X Y : Zorn) :
    particleConjZorn (zornAdd X Y) =
      zornAdd (particleConjZorn X) (particleConjZorn Y) := by
  apply zorn_ext
  · simp [particleConjZorn, zornAdd]
  · funext i; simp [particleConjZorn, zornAdd]
  · funext i; simp [particleConjZorn, zornAdd]
  · simp [particleConjZorn, zornAdd]

/-- The native Zorn conjugation is conjugate-linear for scalar multiplication. -/
theorem particleConjZorn_smul (c : ℂ) (X : Zorn) :
    particleConjZorn (zornSmul c X) =
      zornSmul (complexConjHom c) (particleConjZorn X) := by
  apply zorn_ext
  · simp [particleConjZorn, zornSmul]
  · funext i; simp [particleConjZorn, zornSmul]
  · funext i; simp [particleConjZorn, zornSmul]
  · simp [particleConjZorn, zornSmul]

/-- The conjugate-linear Zorn exchange is involutive. -/
@[simp] theorem particleConjZorn_sq (X : Zorn) :
    particleConjZorn (particleConjZorn X) = X := by
  apply zorn_ext
  · simp [particleConjZorn, complexConjHom]
  · funext i; simp [particleConjZorn, complexConjHom]
  · funext i; simp [particleConjZorn, complexConjHom]
  · simp [particleConjZorn, complexConjHom]

/-- The two complex diagonal projector slots are exchanged. -/
@[simp] theorem particleConjZorn_diagPlus :
    particleConjZorn diagPlus = diagMinus := by
  apply zorn_ext
  · simp [particleConjZorn, diagPlus, diagMinus, complexConjHom]
  · funext i; simp [particleConjZorn, diagPlus, diagMinus, complexConjHom]
  · funext i; simp [particleConjZorn, diagPlus, diagMinus, complexConjHom]
  · simp [particleConjZorn, diagPlus, diagMinus, complexConjHom]

@[simp] theorem particleConjZorn_diagMinus :
    particleConjZorn diagMinus = diagPlus := by
  apply zorn_ext
  · simp [particleConjZorn, diagPlus, diagMinus, complexConjHom]
  · funext i; simp [particleConjZorn, diagPlus, diagMinus, complexConjHom]
  · funext i; simp [particleConjZorn, diagPlus, diagMinus, complexConjHom]
  · simp [particleConjZorn, diagPlus, diagMinus, complexConjHom]

/-- A pure upper lane is sent to the conjugated lower lane. -/
theorem particleConjZorn_upper
    (u : Fin 3 → ℂ) :
    particleConjZorn
        { a := 0, u := u, v := 0, b := 0 } =
      { a := 0, u := 0, v := fun i => complexConjHom (u i), b := 0 } := by
  apply zorn_ext
  · simp [particleConjZorn]
  · funext i; simp [particleConjZorn]
  · funext i; simp [particleConjZorn]
  · simp [particleConjZorn]

/-- A pure lower lane is sent to the conjugated upper lane. -/
theorem particleConjZorn_lower
    (v : Fin 3 → ℂ) :
    particleConjZorn
        { a := 0, u := 0, v := v, b := 0 } =
      { a := 0, u := fun i => complexConjHom (v i), v := 0, b := 0 } := by
  apply zorn_ext
  · simp [particleConjZorn]
  · funext i; simp [particleConjZorn]
  · funext i; simp [particleConjZorn]
  · simp [particleConjZorn]

/-- Consolidated native Zorn conjugation packet. -/
theorem zorn_charge_conjugation_packet (X : Zorn) :
    particleConjZorn (particleConjZorn X) = X ∧
    particleConjZorn diagPlus = diagMinus ∧
    particleConjZorn diagMinus = diagPlus ∧
    (∀ c : ℂ, particleConjZorn (zornSmul c X) =
      zornSmul (complexConjHom c) (particleConjZorn X)) :=
  ⟨particleConjZorn_sq X,
    particleConjZorn_diagPlus,
    particleConjZorn_diagMinus,
    fun c => particleConjZorn_smul c X⟩

end InfoGeometry.Physics.QCDZornChargeConjugationBridge

end noncomputable section
