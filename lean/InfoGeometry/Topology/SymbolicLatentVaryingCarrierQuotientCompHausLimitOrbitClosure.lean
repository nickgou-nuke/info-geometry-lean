import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausLimitActionIso

/-!
# Orbits and orbit closures for varying-carrier quotient limits

This owner keeps the orbit construction on the actual inverse-limit carrier.
The action is the native `lim.map` action from the preceding owner; no flow
structure or recurrence property is introduced here.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

def compactIndexedObservationQuotientCompHausLimitOrbit
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) : Set
      (compactIndexedObservationQuotientCompHausLimit D) :=
  Set.range (fun t : ℝ =>
    compactIndexedObservationQuotientCompHausLimitAction D α t x)

def compactIndexedObservationQuotientCompHausLimitOrbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) : Set
      (compactIndexedObservationQuotientCompHausLimit D) :=
  closure (compactIndexedObservationQuotientCompHausLimitOrbit D α x)

theorem compactIndexedObservationQuotientCompHausLimit_isClosed_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    IsClosed (compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x) := by
  exact isClosed_closure

theorem compactIndexedObservationQuotientCompHausLimit_orbit_subset_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientCompHausLimitOrbit D α x ⊆
      compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x := by
  exact subset_closure

theorem compactIndexedObservationQuotientCompHausLimit_initial_mem_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    x ∈ compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x := by
  apply compactIndexedObservationQuotientCompHausLimit_orbit_subset_orbitClosure D α x
  refine ⟨0, ?_⟩
  change (compactIndexedObservationQuotientCompHausLimitAction D α 0) x = x
  rw [compactIndexedObservationQuotientCompHausLimitAction_zero D α hα0]
  rfl

theorem compactIndexedObservationQuotientCompHausLimit_isCompact_orbitClosure
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (x : compactIndexedObservationQuotientCompHausLimit D) :
    IsCompact (compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (compactIndexedObservationQuotientCompHausLimit_isClosed_orbitClosure D α x)
    (Set.subset_univ _)

theorem compactIndexedObservationQuotientCompHausLimit_action_image_orbit
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientCompHausLimitAction D α s ''
        compactIndexedObservationQuotientCompHausLimitOrbit D α x =
      compactIndexedObservationQuotientCompHausLimitOrbit D α
        (compactIndexedObservationQuotientCompHausLimitAction D α s x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    change
      (compactIndexedObservationQuotientCompHausLimitAction D α t)
          (compactIndexedObservationQuotientCompHausLimitAction D α s x) =
        (compactIndexedObservationQuotientCompHausLimitAction D α s)
          (compactIndexedObservationQuotientCompHausLimitAction D α t x)
    have hst := congrArg (fun f => f x)
      (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd s t)
    have hts := congrArg (fun f => f x)
      (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd t s)
    calc
      (compactIndexedObservationQuotientCompHausLimitAction D α t)
          (compactIndexedObservationQuotientCompHausLimitAction D α s x) =
          (compactIndexedObservationQuotientCompHausLimitAction D α (s + t)) x := by
            simpa using hst.symm
      _ = (compactIndexedObservationQuotientCompHausLimitAction D α (t + s)) x := by
            rw [add_comm]
      _ = (compactIndexedObservationQuotientCompHausLimitAction D α s)
          (compactIndexedObservationQuotientCompHausLimitAction D α t x) := by
            simpa using hts
  · rintro ⟨t, rfl⟩
    refine ⟨compactIndexedObservationQuotientCompHausLimitAction D α t x,
      ⟨t, rfl⟩, ?_⟩
    change
      (compactIndexedObservationQuotientCompHausLimitAction D α s)
          (compactIndexedObservationQuotientCompHausLimitAction D α t x) =
        (compactIndexedObservationQuotientCompHausLimitAction D α t)
          (compactIndexedObservationQuotientCompHausLimitAction D α s x)
    have hst := congrArg (fun f => f x)
      (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd s t)
    have hts := congrArg (fun f => f x)
      (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd t s)
    calc
      (compactIndexedObservationQuotientCompHausLimitAction D α s)
          (compactIndexedObservationQuotientCompHausLimitAction D α t x) =
          (compactIndexedObservationQuotientCompHausLimitAction D α (t + s)) x := by
            simpa using hts.symm
      _ = (compactIndexedObservationQuotientCompHausLimitAction D α (s + t)) x := by
            rw [add_comm]
      _ = (compactIndexedObservationQuotientCompHausLimitAction D α t)
          (compactIndexedObservationQuotientCompHausLimitAction D α s x) := by
            simpa using hst

theorem compactIndexedObservationQuotientCompHausLimit_orbitClosure_mono
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    {x y : compactIndexedObservationQuotientCompHausLimit D}
    (h : compactIndexedObservationQuotientCompHausLimitOrbit D α x ⊆
      compactIndexedObservationQuotientCompHausLimitOrbit D α y) :
    compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x ⊆
      compactIndexedObservationQuotientCompHausLimitOrbitClosure D α y := by
  exact closure_mono h

end InfoGeometry.Topology
