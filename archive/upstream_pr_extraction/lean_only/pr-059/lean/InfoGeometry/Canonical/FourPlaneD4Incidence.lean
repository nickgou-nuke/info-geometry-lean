import Mathlib
import InfoGeometry.Canonical.PauliJungTrialityD4Synthesis
import InfoGeometry.Canonical.SplitOctonionKleinFourTriality

namespace InfoGeometry.Canonical

/-! The existing `FourPlaneVertex`/`d4StarGraph` owner records the incidence
shadow of one neutral vertex and three coloured vertices.  This file supplies
the concrete `Fin 4` presentation and the sector labels.  The result is a
graph-level `D₄` correspondence only: no root system or full Spin triality is
asserted here. -/

def fourPlaneSector (v : FourPlaneVertex) : Submodule ℤ StandardIntegralSplitOctonion :=
  match v with
  | Sum.inr _ => planeComponent (0, 0)
  | Sum.inl .red => planeComponent (1, 0)
  | Sum.inl .green => planeComponent (0, 1)
  | Sum.inl .blue => planeComponent (1, 1)

@[simp] theorem fourPlaneSector_centre :
    fourPlaneSector (Sum.inr ()) = planeComponent (0, 0) := rfl

@[simp] theorem fourPlaneSector_red :
    fourPlaneSector (Sum.inl ColorChannel.red) = planeComponent (1, 0) := rfl

@[simp] theorem fourPlaneSector_green :
    fourPlaneSector (Sum.inl ColorChannel.green) = planeComponent (0, 1) := rfl

@[simp] theorem fourPlaneSector_blue :
    fourPlaneSector (Sum.inl ColorChannel.blue) = planeComponent (1, 1) := rfl

@[simp] theorem planeComponent_red_ne_zero :
    planeComponent (1, 0) ≠ planeComponent (0, 0) := by
  intro h
  have h1 : iOct ∈ planeComponent (1, 0) := Submodule.subset_span (by simp [gradeGenerators])
  rw [h] at h1
  have h2 : ∀ x ∈ planeComponent (0, 0), x .i = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      simp [gradeGenerators] at hy
      rcases hy with rfl | rfl <;> rfl
    | zero => rfl
    | add a b ha hb iha ihb => simp [iha, ihb]
    | smul r a ha iha => simp [iha]
  have h3 := h2 iOct h1
  revert h3
  decide

@[simp] theorem planeComponent_green_ne_zero :
    planeComponent (0, 1) ≠ planeComponent (0, 0) := by
  intro h
  have h1 : jOct ∈ planeComponent (0, 1) := Submodule.subset_span (by simp [gradeGenerators])
  rw [h] at h1
  have h2 : ∀ x ∈ planeComponent (0, 0), x .j = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      simp [gradeGenerators] at hy
      rcases hy with rfl | rfl <;> rfl
    | zero => rfl
    | add a b ha hb iha ihb => simp [iha, ihb]
    | smul r a ha iha => simp [iha]
  have h3 := h2 jOct h1
  revert h3
  decide

@[simp] theorem planeComponent_blue_ne_zero :
    planeComponent (1, 1) ≠ planeComponent (0, 0) := by
  intro h
  have h1 : kOct ∈ planeComponent (1, 1) := Submodule.subset_span (by simp [gradeGenerators])
  rw [h] at h1
  have h2 : ∀ x ∈ planeComponent (0, 0), x .k = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      simp [gradeGenerators] at hy
      rcases hy with rfl | rfl <;> rfl
    | zero => rfl
    | add a b ha hb iha ihb => simp [iha, ihb]
    | smul r a ha iha => simp [iha]
  have h3 := h2 kOct h1
  revert h3
  decide

def d4FinStarAdj : Fin 4 → Fin 4 → Prop :=
  fun i j => (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)

instance : DecidableRel d4FinStarAdj :=
  fun i j => inferInstanceAs (Decidable ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)))

def d4FinStarGraph : SimpleGraph (Fin 4) where
  Adj := d4FinStarAdj
  symm := by
    intro i j
    simp only [d4FinStarAdj]
    tauto
  loopless := by
    exact ⟨fun i => by simp [d4FinStarAdj]⟩

def fourPlaneVertexFinEquiv : FourPlaneVertex ≃ Fin 4 where
  toFun
    | Sum.inr _ => 0
    | Sum.inl .red => 1
    | Sum.inl .green => 2
    | Sum.inl .blue => 3
  invFun
    | 0 => Sum.inr ()
    | 1 => Sum.inl ColorChannel.red
    | 2 => Sum.inl ColorChannel.green
    | 3 => Sum.inl ColorChannel.blue
  left_inv := by
    intro v
    cases v with
    | inl c => cases c <;> rfl
    | inr u => cases u; rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

set_option linter.unusedSimpArgs false in
def fourPlaneIncidence_iso_d4Star :
    d4StarGraph ≃g d4FinStarGraph :=
  { toEquiv := fourPlaneVertexFinEquiv
    map_rel_iff' := by
      intro v w
      rcases v with (c | u)
      · rcases w with (d | t)
        · cases c <;> cases d <;>
            simp [d4StarGraph, d4FinStarGraph, d4FinStarAdj,
              fourPlaneVertexFinEquiv, fourPlaneSector, planeComponent_red_ne_zero, planeComponent_green_ne_zero, planeComponent_blue_ne_zero] <;> decide
        · cases c <;>
            simp [d4StarGraph, d4FinStarGraph, d4FinStarAdj,
              fourPlaneVertexFinEquiv, fourPlaneSector, planeComponent_red_ne_zero, planeComponent_green_ne_zero, planeComponent_blue_ne_zero] <;> decide
      · rcases w with (d | t)
        · cases d <;>
            simp [d4StarGraph, d4FinStarGraph, d4FinStarAdj,
              fourPlaneVertexFinEquiv, fourPlaneSector, planeComponent_red_ne_zero, planeComponent_green_ne_zero, planeComponent_blue_ne_zero] <;> decide
        · simp [d4StarGraph, d4FinStarGraph, d4FinStarAdj,
            fourPlaneVertexFinEquiv, fourPlaneSector, planeComponent_red_ne_zero, planeComponent_green_ne_zero, planeComponent_blue_ne_zero] <;> decide }

theorem fourPlane_centre_adj_red :
    d4StarGraph.Adj (Sum.inr ()) (Sum.inl ColorChannel.red) := by
  simp [d4StarGraph]

theorem fourPlane_centre_adj_green :
    d4StarGraph.Adj (Sum.inr ()) (Sum.inl ColorChannel.green) := by
  simp [d4StarGraph]

theorem fourPlane_centre_adj_blue :
    d4StarGraph.Adj (Sum.inr ()) (Sum.inl ColorChannel.blue) := by
  simp [d4StarGraph]

theorem fourPlane_not_adj_colors (c d : ColorChannel) :
    ¬ d4StarGraph.Adj (Sum.inl c) (Sum.inl d) := by
  simp [d4StarGraph]

set_option linter.unusedSimpArgs false in
theorem fourPlane_adj_iff_sector_ne (v w : FourPlaneVertex) :
    d4StarGraph.Adj v w ↔ (fourPlaneSector v = planeComponent (0,0) ∧ fourPlaneSector w ≠ planeComponent (0,0)) ∨
                        (fourPlaneSector w = planeComponent (0,0) ∧ fourPlaneSector v ≠ planeComponent (0,0)) := by
  rcases v with (c | u) <;> rcases w with (d | t)
  · cases c <;> cases d <;> simp [d4StarGraph, fourPlaneSector,
      planeComponent_red_ne_zero, planeComponent_green_ne_zero, planeComponent_blue_ne_zero]
  · cases c <;> simp [d4StarGraph, fourPlaneSector,
      planeComponent_red_ne_zero, planeComponent_green_ne_zero, planeComponent_blue_ne_zero]
  · cases d <;> simp [d4StarGraph, fourPlaneSector,
      planeComponent_red_ne_zero, planeComponent_green_ne_zero, planeComponent_blue_ne_zero]
  · simp [d4StarGraph, fourPlaneSector]

end InfoGeometry.Canonical
