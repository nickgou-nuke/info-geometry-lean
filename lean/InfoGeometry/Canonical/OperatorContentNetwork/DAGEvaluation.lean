/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorContentNetwork.Programs

/-!
# Ranked evaluation of operator-valued dependency programs

Internal keys and external inputs are distinct generators of a native free
algebra. A natural-number rank makes internal recursion well founded. External
inputs and values at absent keys are arbitrary full real matrices. Support in
an adjoined subalgebra supplies the exact locality condition needed to remove
the recursion guard. Closure of stored dependencies gives uniqueness on the
stored domain, independence of absent-key values, and preservation by extension.
-/

namespace InfoGeometry.Canonical.OperatorContentNetwork.RankedDAG

variable {κ ι n : Type*} [Fintype n] [DecidableEq n]

/-- A node may use its declared internal dependencies and any external input. -/
def dependencyGenerators (D : Set κ) : Set (κ ⊕ ι) :=
  Sum.inl '' D ∪ Set.range Sum.inr

/-- Every stored program evaluates to the matrix assigned to its key. -/
def Satisfies (S : κ → Option (Program (κ ⊕ ι))) (ν : ι → Operator n)
    (ρ : κ → Operator n) : Prop :=
  ∀ k p, S k = some p → ρ k = FreeAlgebra.lift ℝ (Sum.elim ρ ν) p

/-- Agreement on dependencies suffices when the external inputs are fixed. -/
theorem evaluation_eq_of_dependency_agreement {D : Set κ} {p : Program (κ ⊕ ι)}
    (ν : ι → Operator n) {ρ η : κ → Operator n}
    (hp : p ∈ Algebra.adjoin ℝ (FreeAlgebra.ι ℝ '' dependencyGenerators D))
    (h : ∀ d ∈ D, ρ d = η d) :
    FreeAlgebra.lift ℝ (Sum.elim ρ ν) p =
      FreeAlgebra.lift ℝ (Sum.elim η ν) p := by
  apply evaluation_locality _ _ ?_ hp
  intro x hx
  rcases hx with ⟨d, hd, rfl⟩ | ⟨i, rfl⟩
  · exact h d hd
  · rfl

/-- Preserving each existing entry preserves each of its evaluation equations. -/
theorem satisfies_restrict {S T : κ → Option (Program (κ ⊕ ι))}
    (hExt : ∀ k p, S k = some p → T k = some p)
    {ν : ι → Operator n} {ρ : κ → Operator n} (hρ : Satisfies T ν ρ) :
    Satisfies S ν ρ :=
  fun k p hp => hρ k p (hExt k p hp)

/-- Well-founded evaluation, with explicit values for absent or unguarded keys. -/
noncomputable def resolve (S : κ → Option (Program (κ ⊕ ι))) (rank : κ → ℕ)
    (ν : ι → Operator n) (fallback : κ → Operator n) : κ → Operator n :=
  (measure rank).wf.fix fun k rec =>
    match S k with
    | none => fallback k
    | some p =>
        FreeAlgebra.lift ℝ
          (Sum.elim (fun d => if h : rank d < rank k then rec d h else fallback d) ν) p

/-- The resolver obeys its guarded recursive equation. -/
theorem resolve_eq (S : κ → Option (Program (κ ⊕ ι))) (rank : κ → ℕ)
    (ν : ι → Operator n) (fallback : κ → Operator n) (k : κ) :
    resolve S rank ν fallback k =
      match S k with
      | none => fallback k
      | some p =>
          FreeAlgebra.lift ℝ
            (Sum.elim
              (fun d => if _h : rank d < rank k then resolve S rank ν fallback d
                else fallback d) ν) p := by
  exact (measure rank).wf.fix_eq _ k

theorem resolve_of_none (S : κ → Option (Program (κ ⊕ ι))) (rank : κ → ℕ)
    (ν : ι → Operator n) (fallback : κ → Operator n) {k : κ} (hk : S k = none) :
    resolve S rank ν fallback k = fallback k := by
  simpa only [hk] using resolve_eq S rank ν fallback k

theorem resolve_of_some (S : κ → Option (Program (κ ⊕ ι))) (rank : κ → ℕ)
    (ν : ι → Operator n) (fallback : κ → Operator n) {k : κ}
    {p : Program (κ ⊕ ι)} (hk : S k = some p) :
    resolve S rank ν fallback k =
      FreeAlgebra.lift ℝ
        (Sum.elim
          (fun d => if _h : rank d < rank k then resolve S rank ν fallback d
            else fallback d) ν) p := by
  simpa only [hk] using resolve_eq S rank ν fallback k

/-- An external generator retains its supplied matrix without a scalar restriction. -/
theorem resolve_external_input (S : κ → Option (Program (κ ⊕ ι))) (rank : κ → ℕ)
    (ν : ι → Operator n) (fallback : κ → Operator n) {k : κ} {i : ι}
    (hk : S k = some (FreeAlgebra.ι ℝ (Sum.inr i))) :
    resolve S rank ν fallback k = ν i := by
  simpa using resolve_of_some S rank ν fallback hk

/-- Stored external generators preserve noncommutation of arbitrary input operators. -/
theorem resolve_external_pair_noncommutes
    (S : κ → Option (Program (κ ⊕ ι))) (rank : κ → ℕ)
    (ν : ι → Operator n) (fallback : κ → Operator n) {k l : κ} {i j : ι}
    (hk : S k = some (FreeAlgebra.ι ℝ (Sum.inr i)))
    (hl : S l = some (FreeAlgebra.ι ℝ (Sum.inr j)))
    (hν : ¬ Commute (ν i) (ν j)) :
    ¬ Commute (resolve S rank ν fallback k) (resolve S rank ν fallback l) := by
  rw [resolve_external_input S rank ν fallback hk,
    resolve_external_input S rank ν fallback hl]
  exact hν

/-- Two distinct keys can store and retain any supplied noncommuting matrix pair. -/
theorem exists_store_with_noncommuting_results
    (k l : κ) (hkl : k ≠ l) (i j : ι)
    (ν : ι → Operator n) (fallback : κ → Operator n)
    (hν : ¬ Commute (ν i) (ν j)) :
    ∃ S : κ → Option (Program (κ ⊕ ι)),
      S k = some (FreeAlgebra.ι ℝ (Sum.inr i)) ∧
      S l = some (FreeAlgebra.ι ℝ (Sum.inr j)) ∧
      ¬ Commute (resolve S (fun _ => 0) ν fallback k)
        (resolve S (fun _ => 0) ν fallback l) := by
  classical
  let S : κ → Option (Program (κ ⊕ ι)) := fun a =>
    if a = k then some (FreeAlgebra.ι ℝ (Sum.inr i))
    else if a = l then some (FreeAlgebra.ι ℝ (Sum.inr j)) else none
  have hk : S k = some (FreeAlgebra.ι ℝ (Sum.inr i)) := by simp [S]
  have hl : S l = some (FreeAlgebra.ι ℝ (Sum.inr j)) := by simp [S, Ne.symm hkl]
  exact ⟨S, hk, hl, resolve_external_pair_noncommutes S (fun _ => 0) ν fallback hk hl hν⟩


section Supported

variable (S : κ → Option (Program (κ ⊕ ι))) (deps : κ → Set κ) (rank : κ → ℕ)
variable (hRank : ∀ k d, d ∈ deps k → rank d < rank k)
variable (hSupported : ∀ k p, S k = some p →
  p ∈ Algebra.adjoin ℝ (FreeAlgebra.ι ℝ '' dependencyGenerators (deps k)))

include hRank hSupported

/-- Declared support removes the guard, so the construction solves every stored equation. -/
theorem resolve_satisfies (ν : ι → Operator n) (fallback : κ → Operator n) :
    Satisfies S ν (resolve S rank ν fallback) := by
  intro k p hk
  rw [resolve_of_some S rank ν fallback hk]
  apply evaluation_eq_of_dependency_agreement ν (hSupported k p hk)
  intro d hd
  simp only [dite_eq_left (hRank k d hd)]

variable (hClosed : ∀ k p, S k = some p →
  ∀ d ∈ deps k, ∃ q, S d = some q)

include hClosed

/-- Rank induction determines every stored value from the fixed external inputs. -/
theorem satisfies_unique_on_store (ν : ι → Operator n) {ρ η : κ → Operator n}
    (hρ : Satisfies S ν ρ) (hη : Satisfies S ν η) :
    ∀ k p, S k = some p → ρ k = η k := by
  intro k
  refine (measure rank).wf.induction
    (C := fun k => ∀ p, S k = some p → ρ k = η k) k ?_
  intro k ih p hk
  rw [hρ k p hk, hη k p hk]
  apply evaluation_eq_of_dependency_agreement ν (hSupported k p hk)
  intro d hd
  obtain ⟨q, hq⟩ := hClosed k p hk d hd
  exact ih d (hRank k d hd) q hq

/-- Values at absent keys cannot affect a stored, dependency-closed program. -/
theorem resolve_fallback_independent (ν : ι → Operator n)
    (fallback₁ fallback₂ : κ → Operator n) :
    ∀ k p, S k = some p →
      resolve S rank ν fallback₁ k = resolve S rank ν fallback₂ k := by
  exact satisfies_unique_on_store S deps rank hRank hSupported hClosed ν
    (resolve_satisfies S deps rank hRank hSupported ν fallback₁)
    (resolve_satisfies S deps rank hRank hSupported ν fallback₂)

/-- Extension preserves old results, even with different valid ranks and dependencies. -/
theorem resolve_extension (T : κ → Option (Program (κ ⊕ ι)))
    (depsT : κ → Set κ) (rankT : κ → ℕ)
    (hRankT : ∀ k d, d ∈ depsT k → rankT d < rankT k)
    (hSupportedT : ∀ k p, T k = some p →
      p ∈ Algebra.adjoin ℝ (FreeAlgebra.ι ℝ '' dependencyGenerators (depsT k)))
    (hExt : ∀ k p, S k = some p → T k = some p)
    (ν : ι → Operator n) (fallbackS fallbackT : κ → Operator n) :
    ∀ k p, S k = some p →
      resolve S rank ν fallbackS k = resolve T rankT ν fallbackT k := by
  apply satisfies_unique_on_store S deps rank hRank hSupported hClosed ν
  · exact resolve_satisfies S deps rank hRank hSupported ν fallbackS
  · exact satisfies_restrict hExt
      (resolve_satisfies T depsT rankT hRankT hSupportedT ν fallbackT)

end Supported

end InfoGeometry.Canonical.OperatorContentNetwork.RankedDAG
