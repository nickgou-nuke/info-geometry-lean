import InfoGeometry.Topology.SymbolicLatentObservationQuotientFlowTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosureFlowTopCatIso

/-!
# Observation-quotient bridge for orbit-closure flow

The observation quotient already supplies a `SymbolicLatentFlowQuotient`.
This owner exposes the generic restricted orbit-closure transport under the
observation-specific names, so the observation branch of the topology DAG
shares the same Homeomorph/TopCat/IsIso construction.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

def SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureFlowHomeomorph
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) (t : ℝ) :
    SymbolicLatentOrbitClosure
        (symbolicLatentObservationQuotientFlow Φ h_cont) q ≃ₜ
      SymbolicLatentOrbitClosure
        (symbolicLatentObservationQuotientFlow Φ h_cont)
        (descendedSymbolicLatentObservationFlow Φ t q) :=
  (symbolicLatentObservationQuotientFlow Φ h_cont).orbitClosureFlowHomeomorph q t

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureFlowHomeomorph_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) (t : ℝ)
    (y : SymbolicLatentOrbitClosure
      (symbolicLatentObservationQuotientFlow Φ h_cont) q) :
    Φ.observationQuotientOrbitClosureFlowHomeomorph h_cont q t y =
      ⟨descendedSymbolicLatentObservationFlow Φ t y.1, by
        exact (symbolicLatentObservationQuotientFlow Φ h_cont).actHomeomorph_image_orbitClosure
          t q ▸ ⟨y.1, y.2, rfl⟩⟩ := by
  apply Subtype.ext
  rfl

def SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureFlowTopCatHom
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) (t : ℝ) :
    TopCat.of (SymbolicLatentOrbitClosure
        (symbolicLatentObservationQuotientFlow Φ h_cont) q) ⟶
      TopCat.of (SymbolicLatentOrbitClosure
        (symbolicLatentObservationQuotientFlow Φ h_cont)
        (descendedSymbolicLatentObservationFlow Φ t q)) :=
  (symbolicLatentObservationQuotientFlow Φ h_cont).orbitClosureFlowTopCatHom q t

theorem SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureFlowTopCatHom_isIso
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) (t : ℝ) :
    IsIso (Φ.observationQuotientOrbitClosureFlowTopCatHom h_cont q t) := by
  exact (TopCat.isIso_iff_isHomeomorph
    (Φ.observationQuotientOrbitClosureFlowTopCatHom h_cont q t)).2
      (Φ.observationQuotientOrbitClosureFlowHomeomorph h_cont q t).isHomeomorph

theorem SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureFlowHomeomorph_comp_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) (s t : ℝ)
    (y : SymbolicLatentOrbitClosure
      (symbolicLatentObservationQuotientFlow Φ h_cont) q) :
    ((Φ.observationQuotientOrbitClosureFlowHomeomorph h_cont q s).trans
      (Φ.observationQuotientOrbitClosureFlowHomeomorph h_cont
        (descendedSymbolicLatentObservationFlow Φ s q) t) y).1 =
      (Φ.observationQuotientOrbitClosureFlowHomeomorph h_cont q (t + s) y).1 := by
  change descendedSymbolicLatentObservationFlow Φ t
      (descendedSymbolicLatentObservationFlow Φ s y.1) =
    descendedSymbolicLatentObservationFlow Φ (t + s) y.1
  simpa [add_comm] using
    ((symbolicLatentObservationQuotientFlow Φ h_cont).act_add t s y.1).symm

theorem SymbolicLatentObservableModularFlow.observationQuotientOrbitClosureFlowTopCatHom_comp_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (q : SymbolicLatentObservationQuotient S) (s t : ℝ)
    (y : SymbolicLatentOrbitClosure
      (symbolicLatentObservationQuotientFlow Φ h_cont) q) :
    ((Φ.observationQuotientOrbitClosureFlowTopCatHom h_cont q s ≫
        Φ.observationQuotientOrbitClosureFlowTopCatHom h_cont
          (descendedSymbolicLatentObservationFlow Φ s q) t) y).1 =
      (Φ.observationQuotientOrbitClosureFlowTopCatHom h_cont q (t + s) y).1 := by
  change descendedSymbolicLatentObservationFlow Φ t
      (descendedSymbolicLatentObservationFlow Φ s y.1) =
    descendedSymbolicLatentObservationFlow Φ (t + s) y.1
  simpa [add_comm] using
    ((symbolicLatentObservationQuotientFlow Φ h_cont).act_add t s y.1).symm

end
end InfoGeometry.Topology
