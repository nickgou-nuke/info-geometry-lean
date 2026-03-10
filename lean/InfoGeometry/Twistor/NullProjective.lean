import InfoGeometry.Convex.ProjectiveRays
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Projective Null Cone

Mathlib-native twistor model as projectivized null rays of a quadratic form.
-/

open scoped Classical
open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor

variable {K : Type*} {V : Type*}
variable [Field K] [AddCommGroup V] [Module K V]

/-- A projective point is null if (equivalently) any nonzero representative is null. -/
def IsNull (Q : QuadraticForm K V) : ℙ K V → Prop :=
  Projectivization.lift
    (f := fun v : { v : V // v ≠ 0 } => Q v = 0)
    (hf := by
      intro a b t ht
      apply propext
      constructor
      · intro ha
        have ht0 : t ≠ 0 := by
          intro htz
          have : (a : V) = 0 := by simpa [htz] using ht
          exact a.2 this
        have hscaled : (t * t) * Q (b : V) = 0 := by
          have hta : Q (t • (b : V)) = 0 := by simpa [ht] using ha
          simpa [Q.map_smul, smul_eq_mul] using hta
        exact (mul_eq_zero.mp hscaled).resolve_left (mul_ne_zero ht0 ht0)
      · intro hb
        have hta : Q (t • (b : V)) = 0 := by
          simp [Q.map_smul, hb, smul_eq_mul]
        simpa [ht] using hta)

/-- Projective null cone (`twistor space`) associated to `Q`. -/
abbrev TwistorSpace (Q : QuadraticForm K V) : Type _ :=
  { p : ℙ K V // IsNull Q p }

/-- A nonzero null vector defines a twistor point. -/
def twistorMk (Q : QuadraticForm K V) (v : V) (hv : v ≠ 0) (hQ : Q v = 0) :
    TwistorSpace Q :=
  ⟨Projectivization.mk K v hv, by
    simpa [IsNull] using hQ⟩

@[simp] theorem isNull_mk_iff (Q : QuadraticForm K V) (v : V) (hv : v ≠ 0) :
    IsNull (K := K) (V := V) Q (Projectivization.mk K v hv) ↔ Q v = 0 := by
  simp [IsNull, Projectivization.lift_mk]

section Doubled

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Mathlib-native projective states on doubled space. -/
abbrev DoubledProjectiveState : Type _ := InfoGeometry.Convex.ProjectiveState (E := E)

/-- Twistor space on doubled states for a chosen quadratic form. -/
abbrev DoubledTwistorSpace (Q : QuadraticForm ℝ (DoubledSpace E)) : Type _ :=
  TwistorSpace Q

/-- Constructor on doubled states from a nonzero null representative. -/
noncomputable def doubledTwistorMk
    (Q : QuadraticForm ℝ (DoubledSpace E))
    (v : DoubledSpace E) (hv : v ≠ 0) (hQ : Q v = 0) :
    DoubledTwistorSpace Q :=
  twistorMk Q v hv hQ

theorem isNull_projectivize_iff
    (Q : QuadraticForm ℝ (DoubledSpace E))
    (v : DoubledSpace E) (hv : v ≠ 0) :
    IsNull Q
      (InfoGeometry.Convex.projectivize (E := E) v hv) ↔ Q v = 0 := by
  change IsNull Q (Projectivization.mk ℝ v hv) ↔ Q v = 0
  exact isNull_mk_iff (K := ℝ) (V := DoubledSpace E) (Q := Q) v hv

attribute [simp] isNull_projectivize_iff

end Doubled

/-- Abstract chiral-factorization contract for null vectors. -/
class ChiralFactorization
    {Splus Sminus : Type*}
    [AddCommGroup Splus] [Module K Splus]
    [AddCommGroup Sminus] [Module K Sminus]
    (Q : QuadraticForm K V) where
  factor : Splus → Sminus → V
  null_of_factor : ∀ ψ χ, Q (factor ψ χ) = 0
  factor_of_null : ∀ v, Q v = 0 → ∃ ψ χ, factor ψ χ = v

end InfoGeometry.Twistor
