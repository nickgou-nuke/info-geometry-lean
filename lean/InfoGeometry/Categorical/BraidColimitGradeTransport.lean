import InfoGeometry.Categorical.BraidColimitVirasoroAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.GradeActionInterface

noncomputable section

/-! Grade transport for compatible finite-stage braid actions.

This owner connects the categorical braid-colimit interface to the generic
noncommutative grade-action interface.  It records only the stage-wise law;
descent of the grade family to the colimit remains a separate theorem.
-/

namespace InfoGeometry.Categorical.BraidColimitGradeTransport

open CategoryTheory
open InfoGeometry.Categorical.BraidColimitVirasoroAction
open InfoGeometry.OperatorAlgebra

universe u

variable {𝕜 V : Type u} [CommRing 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable {B : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupDiagram.{u}}
variable {A : CompatibleStageAction 𝕜 V B}

/-- A compatible braid action equipped with explicit grade transport at every
finite stage.  The permutation is allowed to depend on the stage element. -/
structure CompatibleStageGradeAction
    (A : CompatibleStageAction 𝕜 V B) (ι : Type*) where
  grade : ι → Set V
  perm : ∀ n : ℕ, B.obj n → ι → ι
  stage_maps_grade : ∀ (n : ℕ) (b : B.obj n),
    MapsToGrade grade
      (fun _ : Unit => fun x =>
        ((A.stages.app n b : LinearAut 𝕜 V).toLinearMap x))
      (fun _ i => perm n b i)

namespace CompatibleStageGradeAction

variable {ι : Type*} (G : CompatibleStageGradeAction (B := B) A ι)

/-- Every element of the specialised group filtered colimit has a finite-stage
representative.  This is the concrete quotient-surjectivity theorem supplied
by Mathlib's filtered-colimit construction; it is not inferred merely from
the word `colimit`. -/
theorem braidColimit_stage_generated
    (b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B) :
    ∃ (n : ℕ) (x : B.obj n),
      InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.stageInjection B n x = b := by
  change ∃ (n : ℕ) (x : B.obj n),
    MonCat.FilteredColimits.M.mk (B ⋙ forget₂ GrpCat MonCat)
      ⟨n, x⟩ = b
  exact MonCat.FilteredColimits.M.mk_surjective
    (B ⋙ forget₂ GrpCat MonCat) b

/-- The supplied finite-stage action maps each source grade into the declared
target grade. -/
theorem stage_maps_grade_apply
    (n : ℕ) (b : B.obj n) (i : ι) {x : V}
    (hx : x ∈ G.grade i) :
    ((A.stages.app n b : LinearAut 𝕜 V).toLinearMap x) ∈
      G.grade (G.perm n b i) := by
  exact G.stage_maps_grade n b () i hx

/-- The descended action agrees with the same grade transport on canonical
stage injections.  This is the strongest conclusion available without an
additional generation/descent theorem for the grade family. -/
theorem action_stage_maps_grade
    (n : ℕ) (b : B.obj n) (i : ι) {x : V}
    (hx : x ∈ G.grade i) :
    (action A
      (InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.stageInjection B n b)) x ∈
        G.grade (G.perm n b i) := by
  rw [CompatibleStageAction.action_stage A n b]
  exact G.stage_maps_grade_apply n b i hx

/-! The categorical colimit exposes its generators through the stage
injections.  The following lifting lemma isolates the only additional fact
needed to turn the stage calculation above into a global statement: an
explicit generation equality for the chosen colimit.  No surjectivity is
silently inferred from the word `colimit`. -/
theorem action_maps_grade_of_stage_generated
    (stage : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B → ℕ)
    (lift : ∀ b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B,
      B.obj (stage b))
    (hgen : ∀ b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B,
      InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.stageInjection
          B (stage b) (lift b) = b) :
    MapsToGrade G.grade
      (fun b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B => fun v =>
        (action A b).toLinearMap v)
      (fun b i => G.perm (stage b) (lift b) i) := by
  intro b i v hv
  have hstage := CompatibleStageGradeAction.action_stage_maps_grade
    G (stage b) (lift b) i hv
  rw [hgen b] at hstage
  exact hstage

/-- The preceding stage-generated theorem applies to the whole specialised
group colimit: Mathlib supplies a representative for each colimit element.
The statement keeps the representatives existential, so no arbitrary choice
of a stage or lift is exposed as part of the grade interface. -/
theorem exists_action_maps_grade_of_colimit :
    ∃ (stage : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B → ℕ)
      (lift : ∀ b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B,
        B.obj (stage b)),
      (∀ b, InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.stageInjection
          B (stage b) (lift b) = b) ∧
      MapsToGrade G.grade
        (fun b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B =>
          fun v => (action A b).toLinearMap v)
        (fun b i => G.perm (stage b) (lift b) i) := by
  classical
  choose stage lift hgen using
    (fun b => braidColimit_stage_generated (B := B) b)
  exact ⟨stage, lift, hgen, G.action_maps_grade_of_stage_generated stage lift hgen⟩

/-! When the finite-stage permutations are known to be trivial, the
existential representative transport collapses to genuine global preservation.
The hypothesis is explicit because a filtered colimit alone does not make a
stage-wise permutation independent of its representative. -/
theorem action_preserves_grade_of_identity_perm
    (hperm : ∀ (n : ℕ) (b : B.obj n) (i : ι), G.perm n b i = i) :
    PreservesGrade G.grade
      (fun b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B =>
        fun v => (action A b).toLinearMap v) := by
  obtain ⟨stage, lift, hgen, hmaps⟩ := G.exists_action_maps_grade_of_colimit
  intro b i v hv
  have h := hmaps b i hv
  simpa [hperm] using h

/-! The same descent works for a nontrivial, but stage-independent,
    permutation of the grade labels.  This is the canonical permutation form
    for a braid action which transports sectors rather than fixing them. -/
theorem action_maps_grade_of_constant_perm
    (π : ι → ι)
    (hperm : ∀ (n : ℕ) (b : B.obj n) (i : ι), G.perm n b i = π i) :
    MapsToGrade G.grade
      (fun b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B =>
        fun v => (action A b).toLinearMap v)
      (fun _ i => π i) := by
  obtain ⟨stage, lift, hgen, hmaps⟩ := G.exists_action_maps_grade_of_colimit
  intro b i v hv
  have h := hmaps b i hv
  simpa [hperm] using h

theorem action_grade_image_eq_of_constant_perm
    (π πinv : ι → ι)
    (hperm : ∀ (n : ℕ) (c : B.obj n) (i : ι), G.perm n c i = π i)
    (hinv : ∀ (n : ℕ) (c : B.obj n) (i : ι),
      G.perm n c⁻¹ i = πinv i)
    (hleft : ∀ i, πinv (π i) = i)
    (b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B)
    (i : ι) :
    (action A b).toLinearMap '' G.grade i = G.grade (π i) := by
  have hforward : Set.MapsTo (action A b).toLinearMap
      (G.grade i) (G.grade (π i)) := by
    exact G.action_maps_grade_of_constant_perm π hperm b i
  have hbackward : Set.MapsTo (action A b).symm.toLinearMap
      (G.grade (π i)) (G.grade i) := by
    intro x hx
    have hinv' : ∀ (n : ℕ) (c : B.obj n) (j : ι),
        G.perm n c j = πinv j := by
      intro n c j
      simpa using hinv n c⁻¹ j
    have h := G.action_maps_grade_of_constant_perm πinv hinv' b⁻¹ (π i) hx
    have haction : action A b⁻¹ = (action A b).symm := by
      apply LinearEquiv.ext
      intro y
      apply (action A b).injective
      calc
        (action A b) ((action A b⁻¹) y) =
            (action A (b * b⁻¹)) y := by
              rw [CompatibleStageAction.action_mul]
              rfl
        _ = y := by
          rw [mul_inv_cancel]
          change (action A (1 :
            InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B)) y = y
          simpa [action] using congrArg (fun T : LinearAut 𝕜 V => T y)
            (map_one (CompatibleStageAction.descendedAction A))
        _ = (action A b) ((action A b).symm y) := by
          simp
    rw [← haction]
    simpa [hleft i] using h
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hforward hx
  · intro hy
    refine ⟨(action A b).symm y, ?_, (action A b).apply_symm_apply y⟩
    exact hbackward hy

/-- The two independent colimit compatibilities can be exposed together when
the same finite-stage action carries both structures: it preserves the grade
family and commutes with every Virasoro commutator. -/
theorem action_grade_and_virasoro_packet
    (hperm : ∀ (n : ℕ) (b : B.obj n) (i : ι), G.perm n b i = i) :
    PreservesGrade G.grade
        (fun b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B =>
          fun v => (action A b).toLinearMap v) ∧
      (∀ (b : InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.BraidGroupColimit B)
        (m n : ℤ),
        Commute ((action A b : LinearAut 𝕜 V).toLinearMap)
          (BraidVirasoroIntertwiner.commutator (A.L m) (A.L n))) := by
  constructor
  · exact G.action_preserves_grade_of_identity_perm hperm
  · intro b m n
    exact A.action_commutes_with_vira_commutator b m n

end CompatibleStageGradeAction

end InfoGeometry.Categorical.BraidColimitGradeTransport
