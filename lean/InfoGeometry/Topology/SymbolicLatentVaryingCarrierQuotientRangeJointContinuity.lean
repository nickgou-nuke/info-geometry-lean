import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientRangeOrbitClosureCompHausNaturality

/-!
# Joint-continuity transport between quotient and range limits

The canonical quotient-range Homeomorph transports a jointly continuous
time action in both directions.  The proof uses the already established
pointwise action naturality; no joint-continuity ax!om is manufactured.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem continuous_compactIndexedObservationRangeCompHausLimitAction_joint_of_quotient
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hquotient : Continuous (fun p : ℝ ×
      compactIndexedObservationQuotientCompHausLimit D =>
        compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2)) :
    Continuous (fun p : ℝ × compactIndexedObservationRangeCompHausLimit D =>
      compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2) := by
  let e := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
  let f : ℝ × compactIndexedObservationRangeCompHausLimit D →
      ℝ × compactIndexedObservationQuotientCompHausLimit D :=
    fun p => (p.1, e.symm p.2)
  have hf : Continuous f := by
    have hsecond : Continuous (fun p : ℝ ×
        compactIndexedObservationRangeCompHausLimit D => e.symm p.2) :=
      e.symm.continuous.comp continuous_snd
    exact continuous_fst.prodMk hsecond
  have htransport : ∀ p : ℝ × compactIndexedObservationRangeCompHausLimit D,
      compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2 =
        e (compactIndexedObservationQuotientCompHausLimitAction D α p.1
          (e.symm p.2)) := by
    intro p
    have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd p.1 (e.symm p.2)
    simpa [e] using h.symm
  rw [show (fun p : ℝ × compactIndexedObservationRangeCompHausLimit D =>
      compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2) =
      (fun p => e (compactIndexedObservationQuotientCompHausLimitAction D α p.1
        (e.symm p.2))) by
      funext p
      exact htransport p]
  have hcomp := hquotient.comp hf
  have houter := e.continuous.comp hcomp
  simpa only [Function.comp_apply] using houter

theorem continuous_compactIndexedObservationQuotientCompHausLimitAction_joint_of_range
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (hrange : Continuous (fun p : ℝ ×
      compactIndexedObservationRangeCompHausLimit D =>
        compactIndexedObservationRangeCompHausLimitAction D α p.1 p.2)) :
    Continuous (fun p : ℝ × compactIndexedObservationQuotientCompHausLimit D =>
      compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2) := by
  let e := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph D
  let f : ℝ × compactIndexedObservationQuotientCompHausLimit D →
      ℝ × compactIndexedObservationRangeCompHausLimit D :=
    fun p => (p.1, e p.2)
  have hf : Continuous f := by
    have hsecond : Continuous (fun p : ℝ ×
        compactIndexedObservationQuotientCompHausLimit D => e p.2) :=
      e.continuous.comp continuous_snd
    exact continuous_fst.prodMk hsecond
  have htransport : ∀ p : ℝ × compactIndexedObservationQuotientCompHausLimit D,
      compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2 =
        e.symm (compactIndexedObservationRangeCompHausLimitAction D α p.1
          (e p.2)) := by
    intro p
    have h := compactIndexedObservationQuotientRangeCompHausLimitHomeomorph_action
      D α hα0 hαadd p.1 p.2
    calc
      compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2 =
          e.symm (e (compactIndexedObservationQuotientCompHausLimitAction
            D α p.1 p.2)) := by rw [e.symm_apply_apply]
      _ = e.symm (compactIndexedObservationRangeCompHausLimitAction D α p.1
          (e p.2)) := congrArg (fun z => e.symm z) h
  rw [show (fun p : ℝ × compactIndexedObservationQuotientCompHausLimit D =>
      compactIndexedObservationQuotientCompHausLimitAction D α p.1 p.2) =
      (fun p => e.symm (compactIndexedObservationRangeCompHausLimitAction D α p.1
        (e p.2))) by
      funext p
      exact htransport p]
  exact e.symm.continuous.comp (hrange.comp hf)

end InfoGeometry.Topology
