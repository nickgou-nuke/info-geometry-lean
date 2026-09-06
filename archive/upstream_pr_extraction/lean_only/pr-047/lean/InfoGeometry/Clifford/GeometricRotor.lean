import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Krein.DoubledSpace

/-!
# InfoGeometry.Clifford.GeometricRotor

Hestenes-style rotor module.
We model a rotor as the classical `cos(θ/2) + sin(θ/2) B` action on the doubled
carrier space, with `B² = -1`.
-/

namespace InfoGeometry.Clifford

open InfoGeometry.Canonical.HestenesRealStructures
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A rotor generator as an operator on the doubled carrier.

This is a subtype because the only extra datum is the square identity; the
operator itself remains the native `ContinuousLinearMap` carrier. -/
abbrev Bivector (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :=
  {op : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E //
    op.comp op = -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E))}

namespace Bivector

abbrev op (B : Bivector E) :
    InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E :=
  B.1

abbrev square_neg (B : Bivector E) :
  B.op.comp B.op = -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) :=
  B.2

/- A scalar frequency/mass scale on the existing bivector generator.  This is
   only an operator-level construction; no physical mass interpretation is
   asserted here. -/
noncomputable def scaled (B : Bivector E) (ω : ℝ) :
    InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E :=
  ω • B.op

theorem scaled_comp_scaled (B : Bivector E) (ω : ℝ) :
    (B.scaled ω).comp (B.scaled ω) =
      -(ω ^ 2 • ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hBBu : B.op (B.op u) = -u := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f => f u) B.square_neg
  simp [scaled, smul_smul, hBBu, pow_two]

end Bivector

/-- Rotor parameters in operational form. -/
abbrev Rotor (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  Bivector E × ℝ

/-- Compatibility accessor for the bivector component of a rotor. -/
abbrev Rotor.B (R : Rotor E) : Bivector E := R.1

/-- Compatibility accessor for the rotation parameter of a rotor. -/
abbrev Rotor.θ (R : Rotor E) : ℝ := R.2

namespace Rotor

/-- Exponential-like map `exp(-B θ / 2)` represented by `cos(θ/2) I + sin(θ/2) B`. -/
noncomputable def exp (R : Rotor E) : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E :=
  Real.cos (R.θ / 2) • (ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) +
    Real.sin (R.θ / 2) • R.B.op

/-- Hestenes reverse for this parameterization:
`R̃ = cos(θ/2) I - sin(θ/2) B`. -/
noncomputable def reverse (R : Rotor E) : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E :=
  Real.cos (R.θ / 2) • (ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) -
    Real.sin (R.θ / 2) • R.B.op

/-- `R · R̃ = 1` as an operator identity (using `B² = -1`). -/
theorem exp_reverse (R : Rotor E) :
    R.exp.comp (R.reverse) = (ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hBBu : R.B.op (R.B.op u) = -u := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f => f u) R.B.square_neg
  calc
    (R.exp.comp (R.reverse)) u
        = (Real.cos (R.θ / 2) * Real.cos (R.θ / 2) +
          Real.sin (R.θ / 2) * Real.sin (R.θ / 2)) • u := by
      have hmul : Real.cos (R.θ / 2) * Real.sin (R.θ / 2) = Real.sin (R.θ / 2) * Real.cos (R.θ / 2) := by ring
      simp [exp, reverse, sub_eq_add_neg, add_smul, smul_add, smul_smul, hBBu, hmul,
        ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ContinuousLinearMap.smul_comp]
      have hcancel :
          (Real.sin (R.θ / 2) * Real.cos (R.θ / 2)) • R.B.op u +
            -((Real.sin (R.θ / 2) * Real.cos (R.θ / 2)) • R.B.op u) = (0 : InfoGeometry.Krein.DoubledSpace E) := by
        simp
      simp [add_assoc, add_left_comm, add_comm, hcancel]
    _ = ((Real.cos (R.θ / 2)) ^ 2 + (Real.sin (R.θ / 2)) ^ 2) • u := by
      ring_nf
    _ = (1 : ℝ) • u := by
      have htrig : (Real.cos (R.θ / 2)) ^ 2 + (Real.sin (R.θ / 2)) ^ 2 = 1 := by
        nlinarith [Real.sin_sq_add_cos_sq (R.θ / 2)]
      rw [htrig]
    _ = (ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) u := by simp

/-- The reverse product gives the same identity (`R̃·R = 1`). -/
theorem reverse_comp_exp (R : Rotor E) :
    R.reverse.comp R.exp = (ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hBBu : R.B.op (R.B.op u) = -u := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f => f u) R.B.square_neg
  calc
    (R.reverse.comp R.exp) u
        = (Real.cos (R.θ / 2) * Real.cos (R.θ / 2) +
          Real.sin (R.θ / 2) * Real.sin (R.θ / 2)) • u := by
      have hmul : Real.cos (R.θ / 2) * Real.sin (R.θ / 2) = Real.sin (R.θ / 2) * Real.cos (R.θ / 2) := by ring
      simp [exp, reverse, sub_eq_add_neg, add_smul, smul_add, smul_smul, hBBu, hmul,
        ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ContinuousLinearMap.smul_comp]
      have hcancel :
          (Real.sin (R.θ / 2) * Real.cos (R.θ / 2)) • R.B.op u +
            -((Real.sin (R.θ / 2) * Real.cos (R.θ / 2)) • R.B.op u) = (0 : InfoGeometry.Krein.DoubledSpace E) := by
        simp
      simp [add_assoc, add_left_comm, add_comm, hcancel]
    _ = ((Real.cos (R.θ / 2)) ^ 2 + (Real.sin (R.θ / 2)) ^ 2) • u := by
      ring_nf
    _ = (1 : ℝ) • u := by
      have htrig : (Real.cos (R.θ / 2)) ^ 2 + (Real.sin (R.θ / 2)) ^ 2 = 1 := by
        nlinarith [Real.sin_sq_add_cos_sq (R.θ / 2)]
      rw [htrig]
    _ = (ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) u := by simp

/-- Double-sided action on vectors via `R x R̃` in operational form.
`ψ ↦ R (R̃ ψ)`. -/
noncomputable def evolve (R : Rotor E) (ψ : InfoGeometry.Krein.DoubledSpace E) : InfoGeometry.Krein.DoubledSpace E :=
  R.exp (R.reverse ψ)

/-! Conjugation by a real rotor on the associative operator envelope.  This
does not identify the rotor with an antilinear or complex operation. -/

noncomputable def conjugate (R : Rotor E)
    (T : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) :
    InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E :=
  R.exp.comp (T.comp R.reverse)

theorem conjugate_apply (R : Rotor E)
    (T : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)
    (ψ : InfoGeometry.Krein.DoubledSpace E) :
    conjugate R T ψ = R.exp (T (R.reverse ψ)) := by
  rfl

theorem conjugate_mul (R : Rotor E)
    (T U : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) :
    conjugate R (T.comp U) =
      (conjugate R T).comp (conjugate R U) := by
  apply ContinuousLinearMap.ext
  intro ψ
  change R.exp (T (U (R.reverse ψ))) =
    R.exp (T (R.reverse (R.exp (U (R.reverse ψ)))))
  have hrev : R.reverse (R.exp (U (R.reverse ψ))) =
      U (R.reverse ψ) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun f => f (U (R.reverse ψ))) (R.reverse_comp_exp)
  rw [hrev]

theorem conjugate_id (R : Rotor E) :
    conjugate R (ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) =
      ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro ψ
  simp [conjugate, ContinuousLinearMap.comp_apply, Rotor.exp_reverse]

/-- Modular flow is the 1-parameter family `R(s) = exp(-K s / 2)`. -/
def modularFlow (K : Bivector E) (s : ℝ) : Rotor E :=
  (K, s)

@[simp] theorem evolve_zero (K : Bivector E) (ψ : InfoGeometry.Krein.DoubledSpace E) :
    evolve (R := modularFlow K 0) ψ = ψ := by
  dsimp [evolve, modularFlow, Rotor.exp, Rotor.reverse]
  have hBBu : K.op (K.op ψ) = -ψ := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun f => f ψ) K.square_neg
  simpa [hBBu, Rotor.θ, smul_add, add_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- One full `2π` rotor turn acts by `-1` on the spinorial transport operator. -/
theorem exp_two_pi_eq_neg_id (K : Bivector E) :
    (modularFlow K (2 * Real.pi)).exp =
      -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  apply ContinuousLinearMap.ext
  intro u
  unfold Rotor.exp Rotor.modularFlow
  have hhalf : ((2 * Real.pi : ℝ) / 2) = Real.pi := by ring
  rw [hhalf, Real.cos_pi, Real.sin_pi]
  ext <;> simp

end Rotor

end InfoGeometry.Clifford
