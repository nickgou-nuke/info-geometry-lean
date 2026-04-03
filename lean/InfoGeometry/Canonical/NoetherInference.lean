import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.Automorphisms
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Core.UnifiedGeometry
import InfoGeometry.Core.SymmetricLieGeneric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option linter.unusedSectionVars false

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

/--
Fisher/Hessian bilinear form is preserved when both the state and the operator
generators are transported by a hessian-preserving linear equivalence.
-/
theorem fisherBilinAt_conjugate_eq
    (U : DSpace E ≃L[ℝ] DSpace E)
    (hU :
      ∀ x y : DSpace E,
        hessian_indefinite_form (E := E) (U x) (U y)
          = hessian_indefinite_form (E := E) x y)
    (v : DSpace E)
    (X Y : Op E) :
    fisherBilinAt (E := E) (U v)
      (InfoGeometry.Krein.conjugateCLM U X)
      (InfoGeometry.Krein.conjugateCLM U Y)
      =
    fisherBilinAt (E := E) v X Y := by
  rw [fisherBilinAt_apply, fisherBilinAt_apply]
  have hX :
      InfoGeometry.Krein.conjugateCLM U X (U v) = U (X v) := by
    change U.conjContinuousAlgEquiv X (U v) = U (X v)
    simp
  have hY :
      InfoGeometry.Krein.conjugateCLM U Y (U v) = U (Y v) := by
    change U.conjContinuousAlgEquiv Y (U v) = U (Y v)
    simp
  rw [hX, hY]
  exact hU (X v) (Y v)

section FisherKilling

variable [Invertible (2 : ℝ)]
variable [Module.Free ℝ (Op E)] [Module.Finite ℝ (Op E)]

/-!
Schur-type proportionality on `S.𝔭` is not owned in this file.
Until a constructive proportionality theorem is proved in the symmetric-Lie owner
layer, the Fisher/Killing corridor here starts from explicit base relations.
-/

/--
Basepoint Fisher/Killing proportionality transports along any
hessian-preserving linear equivalence when the operator generators are
conjugated accordingly.
-/
theorem fisher_metric_eq_killing_form_of_orbit_base_relation
    (S : SymmetricLieAlgebra ℝ (Op E))
    (U : DSpace E ≃L[ℝ] DSpace E)
    (hU :
      ∀ x y : DSpace E,
        hessian_indefinite_form (E := E) (U x) (U y)
          = hessian_indefinite_form (E := E) x y)
    (v0 : DSpace E)
    (c : ℝ)
    (hBase :
      ∀ (X Y : Op E),
        fisherBilinAt (E := E) v0 X Y =
          c * S.B (S.P_minus X) (S.P_minus Y)) :
    ∀ (X Y : Op E),
      fisherBilinAt (E := E) (U v0)
        (InfoGeometry.Krein.conjugateCLM U X)
        (InfoGeometry.Krein.conjugateCLM U Y)
        =
      c * S.B (S.P_minus X) (S.P_minus Y) := by
  intro X Y
  calc
    fisherBilinAt (E := E) (U v0)
        (InfoGeometry.Krein.conjugateCLM U X)
        (InfoGeometry.Krein.conjugateCLM U Y)
      =
        fisherBilinAt (E := E) v0 X Y := by
          exact fisherBilinAt_conjugate_eq (E := E) U hU v0 X Y
    _ = c * S.B (S.P_minus X) (S.P_minus Y) := hBase X Y

/--
The Killing form on operator endomorphisms is invariant under conjugation by a
continuous linear equivalence.
-/
theorem killing_form_conjugate_eq
    (S : SymmetricLieAlgebra ℝ (Op E))
    (U : DSpace E ≃L[ℝ] DSpace E)
    (X Y : Op E) :
    S.B (InfoGeometry.Krein.conjugateCLM U X)
        (InfoGeometry.Krein.conjugateCLM U Y)
      =
    S.B X Y := by
  simpa [InfoGeometry.Krein.conjugateCLM] using
    (LieAlgebra.killingForm_of_equiv_apply
      (R := ℝ) (L := Op E) (L' := Op E)
      (InfoGeometry.Krein.conjEnd U).toLieEquiv X Y)

/--
If the symmetric involution `θ` commutes with operator conjugation, then the
Cartan-minus projection `P₋` also commutes with that conjugation.
-/
theorem P_minus_conjugate_eq_of_theta_commutes
    (S : SymmetricLieAlgebra ℝ (Op E))
    (U : DSpace E ≃L[ℝ] DSpace E)
    (hθComm :
      ∀ X : Op E,
        S.θ (InfoGeometry.Krein.conjugateCLM U X)
          = InfoGeometry.Krein.conjugateCLM U (S.θ X))
    (X : Op E) :
    S.P_minus (InfoGeometry.Krein.conjugateCLM U X)
      =
    InfoGeometry.Krein.conjugateCLM U (S.P_minus X) := by
  rw [S.P_minus_apply, S.P_minus_apply, hθComm X]
  change
      (⅟ (2 : ℝ)) •
          (U.conjContinuousAlgEquiv X - U.conjContinuousAlgEquiv (S.θ X))
        =
      U.conjContinuousAlgEquiv ((⅟ (2 : ℝ)) • (X - S.θ X))
  simp [sub_eq_add_neg]

/--
Under commutation of `θ` with operator conjugation, the Killing form of the
`P₋`-projected generators is invariant under conjugation.
-/
theorem killing_form_P_minus_conjugate_eq_of_theta_commutes
    (S : SymmetricLieAlgebra ℝ (Op E))
    (U : DSpace E ≃L[ℝ] DSpace E)
    (hθComm :
      ∀ X : Op E,
        S.θ (InfoGeometry.Krein.conjugateCLM U X)
          = InfoGeometry.Krein.conjugateCLM U (S.θ X))
    (X Y : Op E) :
    S.B (S.P_minus (InfoGeometry.Krein.conjugateCLM U X))
        (S.P_minus (InfoGeometry.Krein.conjugateCLM U Y))
      =
    S.B (S.P_minus X) (S.P_minus Y) := by
  rw [P_minus_conjugate_eq_of_theta_commutes (E := E) S U hθComm X,
    P_minus_conjugate_eq_of_theta_commutes (E := E) S U hθComm Y]
  exact killing_form_conjugate_eq (E := E) S U (S.P_minus X) (S.P_minus Y)

/--
For the symmetric Lie algebra induced by conjugation with an involution `J`,
operator conjugation by `U` commutes with `θ` as soon as `U` commutes with `J`.
-/
theorem theta_commutes_with_operator_conjugation_of_commutes_with_involution
    (J : DSpace E →L[ℝ] DSpace E)
    (hJ : J.comp J = ContinuousLinearMap.id ℝ (DSpace E))
    (U : DSpace E ≃L[ℝ] DSpace E)
    (hComm : ∀ x : DSpace E, J (U x) = U (J x))
    (X : Op E) :
    (InfoGeometry.Core.conjugationSymmetricLieAlgebra J hJ).θ
        (InfoGeometry.Krein.conjugateCLM U X)
      =
    InfoGeometry.Krein.conjugateCLM U
      ((InfoGeometry.Core.conjugationSymmetricLieAlgebra J hJ).θ X) := by
  have hComm_symm : ∀ x : DSpace E, J (U.symm x) = U.symm (J x) := by
    intro x
    simpa using congrArg U.symm (hComm (U.symm x)).symm
  apply ContinuousLinearMap.ext
  intro v
  change J (U (X (U.symm (J v)))) = U (J (X (J (U.symm v))))
  rw [← hComm_symm v]
  exact hComm (X (J (U.symm v)))

/--
If the Killing side is also invariant under the same conjugation action, then
the transported Fisher/Killing proportionality is expressed entirely in terms
of the conjugated generators.
-/
theorem fisher_metric_eq_killing_form_of_orbit_base_relation_and_killing_conjugation_invariance
    (S : SymmetricLieAlgebra ℝ (Op E))
    (U : DSpace E ≃L[ℝ] DSpace E)
    (hU :
      ∀ x y : DSpace E,
        hessian_indefinite_form (E := E) (U x) (U y)
          = hessian_indefinite_form (E := E) x y)
    (v0 : DSpace E)
    (c : ℝ)
    (hBase :
      ∀ (X Y : Op E),
        fisherBilinAt (E := E) v0 X Y =
          c * S.B (S.P_minus X) (S.P_minus Y))
    (hKInv :
      ∀ (X Y : Op E),
        S.B (S.P_minus (InfoGeometry.Krein.conjugateCLM U X))
            (S.P_minus (InfoGeometry.Krein.conjugateCLM U Y))
          =
        S.B (S.P_minus X) (S.P_minus Y)) :
    ∀ (X Y : Op E),
      fisherBilinAt (E := E) (U v0)
        (InfoGeometry.Krein.conjugateCLM U X)
        (InfoGeometry.Krein.conjugateCLM U Y)
        =
      c * S.B (S.P_minus (InfoGeometry.Krein.conjugateCLM U X))
          (S.P_minus (InfoGeometry.Krein.conjugateCLM U Y)) := by
  intro X Y
  calc
    fisherBilinAt (E := E) (U v0)
        (InfoGeometry.Krein.conjugateCLM U X)
        (InfoGeometry.Krein.conjugateCLM U Y)
      =
        c * S.B (S.P_minus X) (S.P_minus Y) := by
          exact fisher_metric_eq_killing_form_of_orbit_base_relation
            (E := E) S U hU v0 c hBase X Y
    _ =
        c * S.B (S.P_minus (InfoGeometry.Krein.conjugateCLM U X))
            (S.P_minus (InfoGeometry.Krein.conjugateCLM U Y)) := by
          rw [hKInv X Y]

/--
Orbit-level Fisher/Killing proportionality under a more structural hypothesis:
the symmetric involution `θ` commutes with operator conjugation, so the
required Killing-side invariance is derived rather than supplied separately.
-/
theorem fisher_metric_eq_killing_form_of_orbit_base_relation_of_theta_commutes
    (S : SymmetricLieAlgebra ℝ (Op E))
    (U : DSpace E ≃L[ℝ] DSpace E)
    (hU :
      ∀ x y : DSpace E,
        hessian_indefinite_form (E := E) (U x) (U y)
          = hessian_indefinite_form (E := E) x y)
    (v0 : DSpace E)
    (c : ℝ)
    (hBase :
      ∀ (X Y : Op E),
        fisherBilinAt (E := E) v0 X Y =
          c * S.B (S.P_minus X) (S.P_minus Y))
    (hθComm :
      ∀ X : Op E,
        S.θ (InfoGeometry.Krein.conjugateCLM U X)
          = InfoGeometry.Krein.conjugateCLM U (S.θ X)) :
    ∀ (X Y : Op E),
      fisherBilinAt (E := E) (U v0)
        (InfoGeometry.Krein.conjugateCLM U X)
        (InfoGeometry.Krein.conjugateCLM U Y)
        =
      c * S.B (S.P_minus (InfoGeometry.Krein.conjugateCLM U X))
          (S.P_minus (InfoGeometry.Krein.conjugateCLM U Y)) := by
  intro X Y
  exact fisher_metric_eq_killing_form_of_orbit_base_relation_and_killing_conjugation_invariance
    (E := E) S U hU v0 c hBase
    (hKInv := killing_form_P_minus_conjugate_eq_of_theta_commutes
      (E := E) S U hθComm) X Y

/--
Specialized orbit-level Fisher/Killing transport for the symmetric Lie algebra
coming from conjugation by an involution `J`: the required `θ`-commutation is
derived from the concrete relation `J ∘ U = U ∘ J`.
-/
theorem fisher_metric_eq_killing_form_of_orbit_base_relation_of_commutes_with_involution
    (J : DSpace E →L[ℝ] DSpace E)
    (hJ : J.comp J = ContinuousLinearMap.id ℝ (DSpace E))
    (U : DSpace E ≃L[ℝ] DSpace E)
    (hU :
      ∀ x y : DSpace E,
        hessian_indefinite_form (E := E) (U x) (U y)
          = hessian_indefinite_form (E := E) x y)
    (hComm : ∀ x : DSpace E, J (U x) = U (J x))
    (v0 : DSpace E)
    (c : ℝ)
    (hBase :
      ∀ (X Y : Op E),
        fisherBilinAt (E := E) v0 X Y =
          c * (InfoGeometry.Core.conjugationSymmetricLieAlgebra J hJ).B
            ((InfoGeometry.Core.conjugationSymmetricLieAlgebra J hJ).P_minus X)
            ((InfoGeometry.Core.conjugationSymmetricLieAlgebra J hJ).P_minus Y)) :
    ∀ (X Y : Op E),
      fisherBilinAt (E := E) (U v0)
        (InfoGeometry.Krein.conjugateCLM U X)
        (InfoGeometry.Krein.conjugateCLM U Y)
        =
      c * (InfoGeometry.Core.conjugationSymmetricLieAlgebra J hJ).B
          ((InfoGeometry.Core.conjugationSymmetricLieAlgebra J hJ).P_minus
            (InfoGeometry.Krein.conjugateCLM U X))
          ((InfoGeometry.Core.conjugationSymmetricLieAlgebra J hJ).P_minus
            (InfoGeometry.Krein.conjugateCLM U Y)) := by
  exact fisher_metric_eq_killing_form_of_orbit_base_relation_of_theta_commutes
    (E := E)
    (S := InfoGeometry.Core.conjugationSymmetricLieAlgebra J hJ)
    (U := U) (hU := hU) (v0 := v0) (c := c) (hBase := hBase)
    (hθComm := theta_commutes_with_operator_conjugation_of_commutes_with_involution
      (E := E) (J := J) (hJ := hJ) (U := U) (hComm := hComm))

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

end InfoGeometry.Canonical.NoetherInference
