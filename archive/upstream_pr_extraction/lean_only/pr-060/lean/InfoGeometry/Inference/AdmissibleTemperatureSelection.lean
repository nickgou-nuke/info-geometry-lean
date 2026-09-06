/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

/-!
# Stability-constrained finite temperature selection

Selection is performed only over an explicitly admissible finite subset. The
nonemptiness property is intentional: an empty admissible set is reported as
an unresolved fit rather than silently replaced by an unstable temperature.
-/

namespace InfoGeometry.Inference

variable {α : Type*}

theorem exists_filtered_schedule_max
    (S : Finset α) (P : α → Prop) [DecidablePred P]
    (score : α → ℝ) (hP : (S.filter P).Nonempty) :
    ∃ x ∈ S, P x ∧
      ∀ y ∈ S, P y → score y ≤ score x := by
  classical
  let admissible : Finset α := S.filter P
  have hadmissible : admissible.Nonempty := by
    simpa [admissible] using hP
  let scores : Finset ℝ := admissible.image score
  have hscores : scores.Nonempty := hadmissible.image score
  have hmax_mem : scores.max' hscores ∈ scores :=
    Finset.max'_mem scores hscores
  rcases Finset.mem_image.mp hmax_mem with ⟨x, hx, hxmax⟩
  have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
  have hxP : P x := (Finset.mem_filter.mp hx).2
  refine ⟨x, hxS, hxP, ?_⟩
  intro y hyS hyP
  have hymem : y ∈ admissible := Finset.mem_filter.mpr ⟨hyS, hyP⟩
  have hymem_score : score y ∈ scores :=
    Finset.mem_image.mpr ⟨y, hymem, rfl⟩
  have hyle : score y ≤ scores.max' hscores :=
    Finset.le_max' scores _ hymem_score
  simpa [hxmax] using hyle

end InfoGeometry.Inference
