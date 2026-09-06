import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathEndpoints

namespace InfoGeometry.Topology

/-!
# Half-interval restrictions of symbolic latent paths

These maps are the continuous reparametrizations needed before constructing a
path concatenation.  This file intentionally stops before the piecewise gluing
step, whose continuity requires an endpoint compatibility proof.
-/

noncomputable def symbolicFirstHalfValue (t : SymbolicPathDomain) :
    SymbolicPathDomain := by
  refine ⟨(t : ℝ) / 2, ?_⟩
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  constructor
  · change 0 ≤ (t : ℝ) / 2
    nlinarith
  · change (t : ℝ) / 2 ≤ 1
    nlinarith

noncomputable def symbolicFirstHalfParameter :
    C(SymbolicPathDomain, SymbolicPathDomain) :=
    ⟨symbolicFirstHalfValue,
      (continuous_subtype_val.div_const 2).subtype_mk (by
        intro t
        have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
        have ht1 : (t : ℝ) ≤ 1 := t.property.2
        constructor
        · change 0 ≤ (t : ℝ) / 2
          nlinarith
        · change (t : ℝ) / 2 ≤ 1
          nlinarith)⟩

noncomputable def symbolicSecondHalfValue (t : SymbolicPathDomain) :
    SymbolicPathDomain := by
  refine ⟨(1 + (t : ℝ)) / 2, ?_⟩
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  constructor
  · change 0 ≤ (1 + (t : ℝ)) / 2
    nlinarith
  · change (1 + (t : ℝ)) / 2 ≤ 1
    nlinarith

noncomputable def symbolicSecondHalfParameter :
    C(SymbolicPathDomain, SymbolicPathDomain) :=
    ⟨symbolicSecondHalfValue,
      ((continuous_const.add continuous_subtype_val).div_const 2).subtype_mk
        (by
          intro t
          have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
          have ht1 : (t : ℝ) ≤ 1 := t.property.2
          constructor
          · change 0 ≤ (1 + (t : ℝ)) / 2
            nlinarith
          · change (1 + (t : ℝ)) / 2 ≤ 1
            nlinarith)⟩

theorem symbolicFirstHalfParameter_zero :
    symbolicFirstHalfParameter 0 = (0 : SymbolicPathDomain) := by
  apply Subtype.ext
  norm_num [symbolicFirstHalfParameter, symbolicFirstHalfValue]

theorem symbolicFirstHalfParameter_one :
    symbolicFirstHalfParameter 1 =
      (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : SymbolicPathDomain) := by
  apply Subtype.ext
  norm_num [symbolicFirstHalfParameter, symbolicFirstHalfValue]

theorem symbolicSecondHalfParameter_zero :
    symbolicSecondHalfParameter 0 =
      (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : SymbolicPathDomain) := by
  apply Subtype.ext
  norm_num [symbolicSecondHalfParameter, symbolicSecondHalfValue]

theorem symbolicSecondHalfParameter_one :
    symbolicSecondHalfParameter 1 = (1 : SymbolicPathDomain) := by
  apply Subtype.ext
  norm_num [symbolicSecondHalfParameter, symbolicSecondHalfValue]

noncomputable def symbolicFirstHalfPath
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) : SymbolicLatentPath X :=
  γ.comp symbolicFirstHalfParameter

noncomputable def symbolicSecondHalfPath
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) : SymbolicLatentPath X :=
  γ.comp symbolicSecondHalfParameter

theorem symbolicFirstHalfPath_apply
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    symbolicFirstHalfPath γ t = γ (symbolicFirstHalfParameter t) := rfl

theorem symbolicSecondHalfPath_apply
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    symbolicSecondHalfPath γ t = γ (symbolicSecondHalfParameter t) := rfl

theorem symbolicFirstHalfPath_start
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (symbolicFirstHalfPath γ).start = γ.start := by
  change γ (symbolicFirstHalfParameter 0) = γ 0
  rw [symbolicFirstHalfParameter_zero]

theorem symbolicFirstHalfPath_finish
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (symbolicFirstHalfPath γ).finish =
      γ (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : SymbolicPathDomain) := by
  change γ (symbolicFirstHalfParameter 1) =
    γ (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : SymbolicPathDomain)
  rw [symbolicFirstHalfParameter_one]

theorem symbolicFirstHalfPath_endpoints
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (symbolicFirstHalfPath γ).endpoints =
      (γ.start,
        γ (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : SymbolicPathDomain)) := by
  ext
  · simpa [SymbolicLatentPath.start] using (symbolicFirstHalfPath_start (γ := γ))
  · simpa [SymbolicLatentPath.finish] using (symbolicFirstHalfPath_finish (γ := γ))

theorem symbolicSecondHalfPath_finish
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (symbolicSecondHalfPath γ).finish = γ.finish := by
  change γ (symbolicSecondHalfParameter 1) = γ 1
  rw [symbolicSecondHalfParameter_one]

theorem symbolicSecondHalfPath_start
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (symbolicSecondHalfPath γ).start =
      γ (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : SymbolicPathDomain) := by
  change γ (symbolicSecondHalfParameter 0) =
    γ (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : SymbolicPathDomain)
  rw [symbolicSecondHalfParameter_zero]

theorem symbolicSecondHalfPath_endpoints
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (symbolicSecondHalfPath γ).endpoints =
      (γ (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : SymbolicPathDomain),
        γ.finish) := by
  ext
  · simpa [SymbolicLatentPath.start] using (symbolicSecondHalfPath_start (γ := γ))
  · simpa [SymbolicLatentPath.finish] using (symbolicSecondHalfPath_finish (γ := γ))

end InfoGeometry.Topology
