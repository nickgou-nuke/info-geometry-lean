/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ChiralOperatorChargeFiltration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.FreeAlgebra

/-!
# Colimit of finite chiral operator-word stages

The stage `n` is the `ℝ`-submodule of the free associative chiral envelope
spanned by evaluated words of length at most `n`.  These stages are modules,
not algebras: a finite length window is not closed under multiplication.
Their genuine filtered colimit is therefore an operator-module colimit.  The
word-level cyclotomic readout is retained separately; no charge is assigned
to an arbitrary linear combination in a stage or in the colimit.

#### BUCKET 1: CLOSED FINITE THEOREMS

Stage inclusions, word representatives, append readout, and the ambient
countable-rank theorem are proved below.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None; the declarations below are unconditional over the stated carriers.

#### BUCKET 3: OPEN CLOSURE DEBT

Identifying this module colimit with the ambient envelope and transporting its
algebra multiplication through that equivalence remain open in this owner.
-/

namespace InfoGeometry.Algebra

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

/-- The submodule spanned by chiral operator words of length at most `n`. -/
def chiralWordStage (n : ℕ) :
    Submodule ℝ (InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope ℝ) :=
  Submodule.span ℝ {x | ∃ w : List ChiralGenerator,
    w.length ≤ n ∧ x = word (R := ℝ) w}

/-- Each fixed word-length cutoff is a finite-dimensional head module. -/
theorem chiralWordStage_finite (n : ℕ) :
    Module.Finite ℝ (chiralWordStage n) := by
  have hwords : {w : List ChiralGenerator | w.length ≤ n}.Finite :=
    List.finite_length_le ChiralGenerator n
  have hgens : {x : ChiralOperatorEnvelope ℝ | ∃ w : List ChiralGenerator,
      w.length ≤ n ∧ x = word (R := ℝ) w}.Finite := by
    apply (hwords.image (word (R := ℝ))).subset
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  exact Module.Finite.span_of_finite ℝ hgens

/-- Increasing the length cutoff gives an inclusion of stage submodules. -/
theorem chiralWordStage_subset {n m : ℕ} (h : n ≤ m) :
    chiralWordStage n ≤ chiralWordStage m := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with ⟨w, hw, rfl⟩
  apply Submodule.subset_span (R := ℝ)
  exact ⟨w, hw.trans h, rfl⟩

/-- A stage embeds into its successor, which also contains all boundary words
whose length is exactly the new cutoff. -/
theorem chiralWordStage_subset_succ (n : ℕ) :
    chiralWordStage n ≤ chiralWordStage (n + 1) ∧
    ∀ w : List ChiralGenerator, w.length = n + 1 →
      word (R := ℝ) w ∈ chiralWordStage (n + 1) := by
  constructor
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    apply Submodule.subset_span (R := ℝ)
    exact ⟨w, hw.trans (Nat.le_succ n), rfl⟩
  · intro w hw
    apply Submodule.subset_span (R := ℝ)
    exact ⟨w, by simp [hw], rfl⟩

/-! The span proof above is the only place where the finite-window inclusion
is constructed; all later maps are the native categorical morphisms. -/

/-- A word belongs to the stage whose cutoff equals its length. -/
private theorem chiralWordStage_mem_of_length
    (w : List ChiralGenerator) :
    word (R := ℝ) w ∈ chiralWordStage w.length := by
  apply Submodule.subset_span (R := ℝ)
  exact ⟨w, le_rfl, rfl⟩

/-- The directed system of word-length submodules and their inclusions. -/
def chiralWordStageFunctor : ℕ ⥤ ModuleCat ℝ where
  obj n := ModuleCat.of ℝ (chiralWordStage n)
  map f := ModuleCat.ofHom
    (Submodule.inclusion
      (chiralWordStage_subset (leOfHom f)))
  map_id n := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

noncomputable abbrev ChiralOperatorColimit :=
  colimit chiralWordStageFunctor

/-- The ambient free operator envelope has countably infinite `ℝ`-module rank.
The word stages cut off word length; they do not bound the dimension of the
operator carrier. -/
theorem chiralOperatorEnvelope_rank_aleph0 :
    Module.rank ℝ (InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope ℝ) =
      Cardinal.aleph0.{0} := by
  rw [FreeAlgebra.rank_eq]
  simpa only [Cardinal.lift_id] using
    (Cardinal.mk_list_eq_aleph0.{0} ChiralGenerator)

/-- The canonical linear map from a stage into its categorical colimit. -/
noncomputable def chiralWordStageInjection (n : ℕ) :
  chiralWordStage n →ₗ[ℝ] ChiralOperatorColimit :=
  (colimit.ι chiralWordStageFunctor n).hom

@[simp] theorem chiralWordStageInjection_map
    {n m : ℕ} (f : n ⟶ m) (x : chiralWordStage n) :
    chiralWordStageInjection m (chiralWordStageFunctor.map f x) =
      chiralWordStageInjection n x := by
  exact congrArg (fun q => q.hom x) (colimit.w chiralWordStageFunctor f)

/-- Every word has a representative at its length stage, and this representative
has the same colimit image at every later cutoff. -/
theorem chiralWord_mem_stage (w : List ChiralGenerator) :
    ∃ x : chiralWordStage w.length,
      x.1 = word (R := ℝ) w ∧
      ∀ m : ℕ, ∀ (hm : w.length ≤ m),
        chiralWordStageInjection m
          (chiralWordStageFunctor.map (homOfLE hm) x) =
          chiralWordStageInjection w.length x := by
  let x : chiralWordStage w.length :=
    ⟨word (R := ℝ) w, chiralWordStage_mem_of_length w⟩
  refine ⟨x, rfl, ?_⟩
  intro m hm
  simp [x]

/-- The colimit class represented by a formal chiral generator word. -/
noncomputable def chiralWordColimitOperator
    (w : List ChiralGenerator) : ChiralOperatorColimit :=
  chiralWordStageInjection w.length
    ⟨word (R := ℝ) w, chiralWordStage_mem_of_length w⟩

/-- Concatenating words adds their cyclotomic charges and represents the
operator product at the concatenated word's exact length stage. -/
theorem chiralWordColimitOperator_append_readout
    (u v : List ChiralGenerator) :
    chiralWordCyclotomicCharge (u ++ v) =
      chiralWordCyclotomicCharge u + chiralWordCyclotomicCharge v ∧
    chiralWordColimitOperator (u ++ v) =
      chiralWordStageInjection (u ++ v).length
        ⟨word (R := ℝ) u * word (R := ℝ) v, by
          rw [← word_append]
          exact chiralWordStage_mem_of_length (u ++ v)⟩ := by
  constructor
  · exact chiralWordCyclotomicCharge_append u v
  · have hstage :
        (⟨word (R := ℝ) (u ++ v), by
          exact chiralWordStage_mem_of_length (u ++ v)⟩ :
          chiralWordStage (u ++ v).length) =
        ⟨word (R := ℝ) u * word (R := ℝ) v, by
          rw [← word_append]
          exact chiralWordStage_mem_of_length (u ++ v)⟩ := by
      apply Subtype.ext
      exact word_append u v
    simpa [chiralWordColimitOperator] using
      congrArg (chiralWordStageInjection (u ++ v).length) hstage

end InfoGeometry.Algebra
