import Mathlib

/-!
# Compact-to-Hausdorff quotient bridge

A continuous surjection from a compact space to a Hausdorff space is a
quotient map.  This is the topological mechanism used by binary readouts;
the concrete readout and its quotient relation remain owned by the Canonical
layer.
-/

namespace InfoGeometry.Topology.CantorFractalContinuumColimit

theorem compact_to_t2_isClosedMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    (f : X → Y) (hf_cont : Continuous f) :
    IsClosedMap f := by
  intro s hs
  exact IsCompact.isClosed ((IsClosed.isCompact hs).image hf_cont)

theorem compact_t2_surjection_is_quotient
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    (f : X → Y) (hf_cont : Continuous f)
    (hf_surj : Function.Surjective f) :
    Topology.IsQuotientMap f := by
  refine .mk hf_surj ?_
  apply TopologicalSpace.ext_iff.mpr
  intro s
  constructor
  · intro hs
    exact hf_cont.isOpen_preimage s hs
  · intro hs
    change IsOpen (f ⁻¹' s) at hs
    have hclosed : IsClosed (f ⁻¹' s)ᶜ :=
      isClosed_compl_iff.mpr hs
    have himage : IsClosed (f '' (f ⁻¹' s)ᶜ) :=
      compact_to_t2_isClosedMap f hf_cont (f ⁻¹' s)ᶜ hclosed
    have h_eq : f '' (f ⁻¹' s)ᶜ = sᶜ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [Set.mem_compl_iff] at hx ⊢
        intro hy
        exact hx hy
      · intro hy
        obtain ⟨x, hx⟩ := hf_surj y
        refine ⟨x, ?_, hx⟩
        simp only [Set.mem_compl_iff] at hy ⊢
        intro hxs
        exact hy (by simpa [hx] using hxs)
    have hsclosed : IsClosed sᶜ := by
      rw [← h_eq]
      exact himage
    exact isClosed_compl_iff.mp hsclosed

theorem cantor_fractal_continuum_synthesis
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    (f : X → Y) (hf_cont : Continuous f)
    (hf_surj : Function.Surjective f) :
    Topology.IsQuotientMap f :=
  compact_t2_surjection_is_quotient f hf_cont hf_surj

end InfoGeometry.Topology.CantorFractalContinuumColimit
