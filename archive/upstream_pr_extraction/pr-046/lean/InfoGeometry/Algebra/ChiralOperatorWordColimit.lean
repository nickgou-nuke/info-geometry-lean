import InfoGeometry.Algebra.ChiralOperatorChargeFiltration
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Colimit of finite chiral operator-word stages

The stage `n` is the `ℝ`-submodule of the free associative chiral envelope
spanned by evaluated words of length at most `n`.  These stages are modules,
not algebras: a finite length window is not closed under multiplication.
Their genuine filtered colimit is therefore an operator-module colimit.  The
word-level cyclotomic readout is retained separately; no charge is assigned
to an arbitrary linear combination in a stage or in the colimit.
-/

namespace InfoGeometry.Algebra

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

def chiralWordStage (n : ℕ) :
    Submodule ℝ (InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope ℝ) :=
  Submodule.span ℝ {x | ∃ w : List ChiralGenerator,
    w.length ≤ n ∧ x = word (R := ℝ) w}

theorem chiralWordStage_subset {n m : ℕ} (h : n ≤ m) :
    chiralWordStage n ≤ chiralWordStage m := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with ⟨w, hw, rfl⟩
  apply Submodule.subset_span (R := ℝ)
  exact ⟨w, hw.trans h, rfl⟩

theorem chiralWordStage_subset_succ (n : ℕ) :
    chiralWordStage n ≤ chiralWordStage (n + 1) := by
  exact chiralWordStage_subset (Nat.le_succ n)

/-! The span proof above is the only place where the finite-window inclusion
is constructed; all later maps are the native categorical morphisms. -/

private theorem chiralWordStage_mem_of_length
    (w : List ChiralGenerator) :
    word (R := ℝ) w ∈ chiralWordStage w.length := by
  apply Submodule.subset_span (R := ℝ)
  exact ⟨w, le_rfl, rfl⟩

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

noncomputable def chiralWordStageInjection (n : ℕ) :
  chiralWordStage n →ₗ[ℝ] ChiralOperatorColimit :=
  (colimit.ι chiralWordStageFunctor n).hom

@[simp] theorem chiralWordStageInjection_map
    {n m : ℕ} (f : n ⟶ m) (x : chiralWordStage n) :
    chiralWordStageInjection m (chiralWordStageFunctor.map f x) =
      chiralWordStageInjection n x := by
  exact congrArg (fun q => q.hom x) (colimit.w chiralWordStageFunctor f)

theorem chiralWord_mem_stage (w : List ChiralGenerator) :
    ∃ x : chiralWordStage w.length, x.1 = word (R := ℝ) w := by
  exact ⟨⟨word (R := ℝ) w, chiralWordStage_mem_of_length w⟩, rfl⟩

noncomputable def chiralWordColimitOperator
    (w : List ChiralGenerator) : ChiralOperatorColimit :=
  chiralWordStageInjection w.length
    ⟨word (R := ℝ) w, chiralWordStage_mem_of_length w⟩

theorem chiralWordColimitOperator_append_readout
    (u v : List ChiralGenerator) :
    chiralWordCyclotomicCharge (u ++ v) =
      chiralWordCyclotomicCharge u + chiralWordCyclotomicCharge v :=
  chiralWordCyclotomicCharge_append u v

end InfoGeometry.Algebra
