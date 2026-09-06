import Mathlib
import InfoGeometry.Topology.SymbolicLatentObservationQuotientReversal
import InfoGeometry.Topology.SymbolicLatentObservationQuotientFlowTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` readout of observational symbolic-latent reversal

The quotient reversal is already constructed and proved involutive in the
observation-quotient owner.  This file exposes that same map categorically and
records its flow-reversal law as an equality of `TopCat` morphisms.
-/

def SymbolicLatentObservableModularReversal.toQuotientTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R)) :
    TopCat.of (SymbolicLatentObservationQuotient S) ⟶
      TopCat.of (SymbolicLatentObservationQuotient S) :=
  (R.toQuotientInvolution h_cont).toTopCatHom

@[simp] theorem SymbolicLatentObservableModularReversal.toQuotientTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R))
    (q : SymbolicLatentObservationQuotient S) :
    R.toQuotientTopCatHom h_cont q =
      descendedSymbolicLatentObservationInvolution R q :=
  rfl

theorem SymbolicLatentObservableModularReversal.toQuotientTopCatHom_square
    {X : Type} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R)) :
    R.toQuotientTopCatHom h_cont ≫ R.toQuotientTopCatHom h_cont =
      𝟙 (TopCat.of (SymbolicLatentObservationQuotient S)) := by
  exact SymbolicLatentInvolution.toTopCatHom_square
    (R.toQuotientInvolution h_cont)

theorem SymbolicLatentObservableModularReversal.flowTopCat_reversal
    {X : Type} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (h_involution : Continuous (descendedSymbolicLatentObservationInvolution R))
    (t : ℝ) :
    Φ.observationQuotientFlowTopCatHom h_flow t ≫
        R.toQuotientTopCatHom h_involution =
      R.toQuotientTopCatHom h_involution ≫
        Φ.observationQuotientFlowTopCatHom h_flow (-t) := by
  ext q
  change descendedSymbolicLatentObservationInvolution R
      (descendedSymbolicLatentObservationFlow Φ t q) =
    descendedSymbolicLatentObservationFlow Φ (-t)
      (descendedSymbolicLatentObservationInvolution R q)
  exact SymbolicLatentObservableModularReversal.toQuotientInvolution_reverses_flow
    R h_flow h_involution t q

end InfoGeometry.Topology
