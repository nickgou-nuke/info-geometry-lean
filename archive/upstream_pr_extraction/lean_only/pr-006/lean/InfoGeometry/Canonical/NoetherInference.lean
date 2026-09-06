import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Core.SymmetricLieGeneric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped Invertible

/-!
# Noether Inference

Compile-oriented core for the physical-informational bridges.

This module formalizes:
1. **Information Killing Fields** as Krein-skew generators on the doubled space.
2. **Hessian Invariance** at the infinitesimal and orbit levels.
3. **Fisher-Killing Bridge** as a constructive proportionality theorem on an
   ambient symmetric Lie algebra of operators.
-/

namespace InfoGeometry.Canonical.NoetherInference

open InfoGeometry.Krein
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Core.Generic
open KreinSpace

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Ambient operator space on the doubled carrier. -/
abbrev Op := DoubledSpace E →L[ℝ] DoubledSpace E

/-- Information Killing field: a Krein-skew generator on the doubled space. -/
def InformationKillingField : Type :=
  { A : Op E // IsKreinSkewAdjoint A }

/--
Infinitesimal Hessian invariance:
a Krein-skew generator is an infinitesimal isometry of the Hessian form.
-/
theorem InformationKillingField.preserves_hessian
    (A : InformationKillingField (E := E))
    (x y : DoubledSpace E) :
    hessianIndefiniteForm (E := E) (A.1 x) y +
      hessianIndefiniteForm (E := E) x (A.1 y) = 0 := by
  simpa using
    (IsKreinSkewAdjoint.hessian_infinitesimal
      (E := E) (A := A.1) A.2 x y)

/-- Fisher/Hessian bilinear form at a state `v`, evaluated on operator generators. -/
noncomputable def fisherBilinAt (v : DoubledSpace E) :
    LinearMap.BilinForm ℝ (Op E) :=
  LinearMap.mk₂ ℝ
    (fun X Y => hessianIndefiniteForm (E := E) (X v) (Y v))
    (by
      intro X₁ X₂ Y
      simp [hessianIndefiniteForm, KreinSpace.kreinInner_add_left])
    (by
      intro a X Y
      simp [hessianIndefiniteForm, KreinSpace.kreinInner_smul_left])
    (by
      intro X Y₁ Y₂
      simp [hessianIndefiniteForm, KreinSpace.kreinInner_add_right])
    (by
      intro a X Y
      simp [hessianIndefiniteForm, KreinSpace.kreinInner_smul_right])

@[simp] lemma fisherBilinAt_apply
    (v : DoubledSpace E) (X Y : Op E) :
    fisherBilinAt (E := E) v X Y =
      hessianIndefiniteForm (E := E) (X v) (Y v) := rfl

section FisherKilling

variable [Invertible (2 : ℝ)]
variable [Module.Free ℝ (Op E)] [Module.Finite ℝ (Op E)]

/--
Constructive Fisher-Killing proportionality from an explicit global bridge.
This matches the actual API of `SymmetricLieAlgebra`.
-/
theorem fisher_metric_eq_killing_form_constructive
    (S : SymmetricLieAlgebra ℝ (Op E))
    (X0 Y0 : Op E)
    (v0 : DoubledSpace E)
    (hB0 : S.B (S.P_minus X0) (S.P_minus Y0) ≠ 0)
    (hH0 : hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) ≠ 0)
    (hBridge :
      ∀ (X Y : Op E) (v : DoubledSpace E),
        hessianIndefiniteForm (E := E) (X v) (Y v) *
          S.B (S.P_minus X0) (S.P_minus Y0)
            =
        hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) *
          S.B (S.P_minus X) (S.P_minus Y)) :
    ∃ c : ℝ, c ≠ 0 ∧
      ∀ (X Y : Op E) (v : DoubledSpace E),
        hessianIndefiniteForm (E := E) (X v) (Y v) =
          c * S.B (S.P_minus X) (S.P_minus Y) := by
  let B0 : ℝ := S.B (S.P_minus X0) (S.P_minus Y0)
  let H0 : ℝ := hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0)
  have hB0' : B0 ≠ 0 := by simpa [B0] using hB0
  have hH0' : H0 ≠ 0 := by simpa [H0] using hH0
  refine ⟨H0 / B0, div_ne_zero hH0' hB0', ?_⟩
  intro X Y v
  let Bxy : ℝ := S.B (S.P_minus X) (S.P_minus Y)
  have hscaled :
      hessianIndefiniteForm (E := E) (X v) (Y v) * B0 = H0 * Bxy := by
    simpa [B0, H0, Bxy] using hBridge X Y v
  have hdiv :
      (hessianIndefiniteForm (E := E) (X v) (Y v) * B0) / B0 =
        (H0 * Bxy) / B0 := by
    exact congrArg (fun z => z / B0) hscaled
  have hmain :
      hessianIndefiniteForm (E := E) (X v) (Y v) = (H0 * Bxy) / B0 := by
    calc
      hessianIndefiniteForm (E := E) (X v) (Y v)
          = (hessianIndefiniteForm (E := E) (X v) (Y v) * B0) / B0 := by
              field_simp [hB0']
      _ = (H0 * Bxy) / B0 := hdiv
  calc
    hessianIndefiniteForm (E := E) (X v) (Y v) = (H0 * Bxy) / B0 := hmain
    _ = (H0 / B0) * Bxy := by ring
    _ = (H0 / B0) * S.B (S.P_minus X) (S.P_minus Y) := by rfl

/--
User-facing Fisher-Killing bridge on the ambient symmetric Lie algebra.

It is intentionally stated on `Op E`, not on `InformationKillingField`,
because this subtype does not automatically inherit the full Lie-algebra
structure needed by `killingForm`.
-/
theorem fisher_metric_eq_killing_form
    (S : SymmetricLieAlgebra ℝ (Op E))
    (X0 Y0 : Op E)
    (v0 : DoubledSpace E)
    (hB0 : S.B (S.P_minus X0) (S.P_minus Y0) ≠ 0)
    (hH0 : hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) ≠ 0)
    (hBridge :
      ∀ (X Y : Op E) (v : DoubledSpace E),
        hessianIndefiniteForm (E := E) (X v) (Y v) *
          S.B (S.P_minus X0) (S.P_minus Y0)
            =
        hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) *
          S.B (S.P_minus X) (S.P_minus Y)) :
    ∃ c : ℝ, c ≠ 0 ∧
      ∀ (X Y : Op E) (v : DoubledSpace E),
        hessianIndefiniteForm (E := E) (X v) (Y v) =
          c * S.B (S.P_minus X) (S.P_minus Y) := by
  exact fisher_metric_eq_killing_form_constructive
    (E := E) (S := S) (X0 := X0) (Y0 := Y0) (v0 := v0)
    (hB0 := hB0) (hH0 := hH0) (hBridge := hBridge)

end FisherKilling

/--
Operator-valued symmetry orbit.
`U t` is the symmetry at time `t`; the state update is `U t` applied to the prior.
-/
structure BayesianSymmetryOrbit (prior : DoubledSpace E) where
  generator : InformationKillingField (E := E)
  U : ℝ → Op E
  U_zero : U 0 = ContinuousLinearMap.id ℝ (DoubledSpace E)
  preserves_hessian :
    ∀ t x y,
      hessianIndefiniteForm (E := E) (U t x) (U t y) =
        hessianIndefiniteForm (E := E) x y

/-- The updated state at time `t`. -/
def BayesianSymmetryOrbit.update
    {prior : DoubledSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior) :
    ℝ → DoubledSpace E :=
  fun t => orbit.U t prior

@[simp] theorem BayesianSymmetryOrbit.update_apply
    {prior : DoubledSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior)
    (t : ℝ) :
    orbit.update t = orbit.U t prior := rfl

@[simp] theorem BayesianSymmetryOrbit.update_zero
    {prior : DoubledSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior) :
    orbit.update 0 = prior := by
  simp [BayesianSymmetryOrbit.update, orbit.U_zero]

/-- Diagonal Hessian self-preservation along the symmetry orbit. -/
theorem BayesianSymmetryOrbit.flow_equivariant
    {prior : DoubledSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior) :
    ∀ t, hessianIndefiniteForm (E := E) (orbit.update t) (orbit.update t) =
      hessianIndefiniteForm (E := E) prior prior := by
  intro t
  simpa [BayesianSymmetryOrbit.update] using
    orbit.preserves_hessian t prior prior

end InfoGeometry.Canonical.NoetherInference
