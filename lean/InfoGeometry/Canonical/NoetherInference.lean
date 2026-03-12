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
abbrev Op (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E

/-- Local alias for the doubled carrier. -/
abbrev DSpace (E : Type*) := InfoGeometry.Krein.DoubledSpace E

/-- Information Killing field: a Krein-skew generator on the doubled space. -/
def InformationKillingField (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : Type _ :=
  { A : Op E // InfoGeometry.Krein.is_krein_skew_adjoint A }

/--
Infinitesimal Hessian invariance:
a Krein-skew generator is an infinitesimal isometry of the Hessian form.
-/
theorem InformationKillingField.preserves_hessian
    (A : InformationKillingField (E := E))
    (x y : DSpace E) :
    hessian_indefinite_form (E := E) (A.1 x) y +
      hessian_indefinite_form (E := E) x (A.1 y) = 0 := by
  simpa using
    (InfoGeometry.Krein.is_krein_skew_adjoint_hessian_infinitesimal
      (E := E) (A := A.1) A.2 x y)

/-- Evaluation at a fixed doubled vector as a linear map on doubled endomorphisms. -/
noncomputable def evalAt (v : DSpace E) : Op E →ₗ[ℝ] DSpace E :=
  (ContinuousLinearMap.coeLM (R := ℝ) (S := ℝ) (M := DSpace E) (N₃ := DSpace E)).flip v

@[simp] lemma evalAt_apply (v : DSpace E) (X : Op E) : evalAt (E := E) v X = X v := rfl

/-- Fisher/Hessian bilinear form at a state `v`, evaluated on operator generators. -/
noncomputable def fisherBilinAt (v : DSpace E) :
    LinearMap.BilinForm ℝ (Op E) :=
  (KreinSpace.kreinBilin (H := DSpace E)).comp (evalAt (E := E) v) (evalAt (E := E) v)

@[simp] lemma fisherBilinAt_apply
    (v : DSpace E) (X Y : Op E) :
    fisherBilinAt v X Y = hessian_indefinite_form (E := E) (X v) (Y v) := by
  simp [fisherBilinAt, hessian_indefinite_form, LinearMap.BilinForm.comp_apply, evalAt,
    KreinSpace.kreinBilin]

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
    (v0 : DSpace E)
    (hB0 : S.B (S.P_minus X0) (S.P_minus Y0) ≠ 0)
    (hH0 : hessian_indefinite_form (E := E) (X0 v0) (Y0 v0) ≠ 0)
    (hBridge :
      ∀ (X Y : Op E) (v : DSpace E),
        hessian_indefinite_form (E := E) (X v) (Y v) *
          S.B (S.P_minus X0) (S.P_minus Y0)
            =
        hessian_indefinite_form (E := E) (X0 v0) (Y0 v0) *
          S.B (S.P_minus X) (S.P_minus Y)) :
    ∃ c : ℝ, c ≠ 0 ∧
      ∀ (X Y : Op E) (v : DSpace E),
        hessian_indefinite_form (E := E) (X v) (Y v) =
          c * S.B (S.P_minus X) (S.P_minus Y) := by
  let B0 : ℝ := S.B (S.P_minus X0) (S.P_minus Y0)
  let H0 : ℝ := hessian_indefinite_form (E := E) (X0 v0) (Y0 v0)
  have hB0' : B0 ≠ 0 := by simpa [B0] using hB0
  have hH0' : H0 ≠ 0 := by simpa [H0] using hH0
  refine ⟨H0 / B0, div_ne_zero hH0' hB0', ?_⟩
  intro X Y v
  let Bxy : ℝ := S.B (S.P_minus X) (S.P_minus Y)
  have hscaled :
      hessian_indefinite_form (E := E) (X v) (Y v) * B0 = H0 * Bxy := by
    simpa [B0, H0, Bxy] using hBridge X Y v
  have hdiv :
      (hessian_indefinite_form (E := E) (X v) (Y v) * B0) / B0 =
        (H0 * Bxy) / B0 := by
    exact congrArg (fun z => z / B0) hscaled
  have hmain :
      hessian_indefinite_form (E := E) (X v) (Y v) = (H0 * Bxy) / B0 := by
    calc
      hessian_indefinite_form (E := E) (X v) (Y v)
          = (hessian_indefinite_form (E := E) (X v) (Y v) * B0) / B0 := by
              field_simp [hB0']
      _ = (H0 * Bxy) / B0 := hdiv
  calc
    hessian_indefinite_form (E := E) (X v) (Y v) = (H0 * Bxy) / B0 := hmain
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
    (v0 : DSpace E)
    (hB0 : S.B (S.P_minus X0) (S.P_minus Y0) ≠ 0)
    (hH0 : hessian_indefinite_form (E := E) (X0 v0) (Y0 v0) ≠ 0)
    (hBridge :
      ∀ (X Y : Op E) (v : DSpace E),
        hessian_indefinite_form (E := E) (X v) (Y v) *
          S.B (S.P_minus X0) (S.P_minus Y0)
            =
        hessian_indefinite_form (E := E) (X0 v0) (Y0 v0) *
          S.B (S.P_minus X) (S.P_minus Y)) :
    ∃ c : ℝ, c ≠ 0 ∧
      ∀ (X Y : Op E) (v : DSpace E),
        hessian_indefinite_form (E := E) (X v) (Y v) =
          c * S.B (S.P_minus X) (S.P_minus Y) := by
  exact fisher_metric_eq_killing_form_constructive
    (E := E) (S := S) (X0 := X0) (Y0 := Y0) (v0 := v0)
    (hB0 := hB0) (hH0 := hH0) (hBridge := hBridge)

end FisherKilling

/--
Operator-valued symmetry orbit.
`U t` is the symmetry at time `t`; the state update is `U t` applied to the prior.
-/
structure BayesianSymmetryOrbit (prior : DSpace E) where
  generator : InformationKillingField (E := E)
  U : ℝ → Op E
  U_zero : U 0 = ContinuousLinearMap.id ℝ (DSpace E)
  preserves_hessian :
    ∀ t x y,
      hessian_indefinite_form (E := E) (U t x) (U t y) =
        hessian_indefinite_form (E := E) x y

/-- The updated state at time `t`. -/
def BayesianSymmetryOrbit.update
    {prior : DSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior) :
    ℝ → DSpace E :=
  fun t => orbit.U t prior

@[simp] theorem BayesianSymmetryOrbit.update_apply
    {prior : DSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior)
    (t : ℝ) :
    orbit.update t = orbit.U t prior := rfl

@[simp] theorem BayesianSymmetryOrbit.update_zero
    {prior : DSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior) :
    orbit.update 0 = prior := by
  simp [BayesianSymmetryOrbit.update, orbit.U_zero]

/-- Diagonal Hessian self-preservation along the symmetry orbit. -/
theorem BayesianSymmetryOrbit.flow_equivariant
    {prior : DSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior) :
    ∀ t, hessian_indefinite_form (E := E) (orbit.update t) (orbit.update t) =
      hessian_indefinite_form (E := E) prior prior := by
  intro t
  simpa [BayesianSymmetryOrbit.update] using
    orbit.preserves_hessian t prior prior

end InfoGeometry.Canonical.NoetherInference
