import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHausLimitOrbitClosureCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentVaryingCarrierCompHausLimitOrbitClosureCompHaus

/-!
# Orbit invariance of quotient and range orbit closures

An orbit closure does not depend on the chosen base point along the orbit.
The proof is explicit: the additive action law reparametrizes the orbit by
translation of the real parameter.  The result is proved independently for
the quotient and observation-range inverse-limit carriers.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

theorem compactIndexedObservationQuotientCompHausLimit_orbit_eq_of_action
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientCompHausLimitOrbit D α
        (compactIndexedObservationQuotientCompHausLimitAction D α s x) =
      compactIndexedObservationQuotientCompHausLimitOrbit D α x := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨s + t, ?_⟩
    have h := congrArg (fun f => f x)
      (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd s t)
    simpa using h
  · rintro ⟨t, rfl⟩
    refine ⟨t - s, ?_⟩
    have h := congrArg (fun f => f x)
      (compactIndexedObservationQuotientCompHausLimitAction_add D α hαadd s (t - s))
    calc
      compactIndexedObservationQuotientCompHausLimitAction D α (t - s)
          (compactIndexedObservationQuotientCompHausLimitAction D α s x) =
          compactIndexedObservationQuotientCompHausLimitAction D α (s + (t - s)) x := by
        simpa using h.symm
      _ = compactIndexedObservationQuotientCompHausLimitAction D α t x := by
        rw [show s + (t - s) = t by abel]

theorem compactIndexedObservationQuotientCompHausLimit_orbitClosure_eq_of_action
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientCompHausLimitOrbitClosure D α
        (compactIndexedObservationQuotientCompHausLimitAction D α s x) =
      compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x := by
  exact congrArg closure
    (compactIndexedObservationQuotientCompHausLimit_orbit_eq_of_action
      D α hαadd s x)

theorem compactIndexedObservationQuotientCompHausLimitActionHomeomorph_image_orbitClosure_eq
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationQuotientCompHausLimit D) :
    compactIndexedObservationQuotientCompHausLimitActionHomeomorph
        D α hα0 hαadd s ''
        compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x =
      compactIndexedObservationQuotientCompHausLimitOrbitClosure D α x := by
  rw [compactIndexedObservationQuotientCompHausLimitActionHomeomorph_image_orbitClosure
    D α hα0 hαadd s x]
  exact compactIndexedObservationQuotientCompHausLimit_orbitClosure_eq_of_action
    D α hαadd s x

theorem compactIndexedObservationRangeCompHausLimit_orbit_eq_of_action
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationRangeCompHausLimit D) :
    compactIndexedObservationRangeCompHausLimitOrbit D α
        (compactIndexedObservationRangeCompHausLimitAction D α s x) =
      compactIndexedObservationRangeCompHausLimitOrbit D α x := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨s + t, ?_⟩
    have h := congrArg (fun f => f x)
      (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd s t)
    simpa using h
  · rintro ⟨t, rfl⟩
    refine ⟨t - s, ?_⟩
    have h := congrArg (fun f => f x)
      (compactIndexedObservationRangeCompHausLimitAction_add D α hαadd s (t - s))
    calc
      compactIndexedObservationRangeCompHausLimitAction D α (t - s)
          (compactIndexedObservationRangeCompHausLimitAction D α s x) =
          compactIndexedObservationRangeCompHausLimitAction D α (s + (t - s)) x := by
        simpa using h.symm
      _ = compactIndexedObservationRangeCompHausLimitAction D α t x := by
        rw [show s + (t - s) = t by abel]

theorem compactIndexedObservationRangeCompHausLimit_orbitClosure_eq_of_action
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationRangeCompHausLimit D) :
    compactIndexedObservationRangeCompHausLimitOrbitClosure D α
        (compactIndexedObservationRangeCompHausLimitAction D α s x) =
      compactIndexedObservationRangeCompHausLimitOrbitClosure D α x := by
  exact congrArg closure
    (compactIndexedObservationRangeCompHausLimit_orbit_eq_of_action
      D α hαadd s x)

theorem compactIndexedObservationRangeCompHausLimitActionHomeomorph_image_orbitClosure_eq
    {J : Type} [Category J]
    (D : Jᵒᵖ ⥤ CompactSymbolicLatentSystemObject ι)
    (α : ℝ → (D ⟶ D))
    (hα0 : α 0 = 𝟙 D)
    (hαadd : ∀ s t, α (s + t) = α s ≫ α t)
    (s : ℝ) (x : compactIndexedObservationRangeCompHausLimit D) :
    compactIndexedObservationRangeCompHausLimitActionHomeomorph
        D α hα0 hαadd s ''
        compactIndexedObservationRangeCompHausLimitOrbitClosure D α x =
      compactIndexedObservationRangeCompHausLimitOrbitClosure D α x := by
  rw [compactIndexedObservationRangeCompHausLimitActionHomeomorph_image_orbitClosure
    D α hα0 hαadd s x]
  exact compactIndexedObservationRangeCompHausLimit_orbitClosure_eq_of_action
    D α hαadd s x

end InfoGeometry.Topology
