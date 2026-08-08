import Mathlib
import InfoGeometry.Topology.SymbolicLatentObservationQuotientFlowTopCat
import InfoGeometry.Topology.SymbolicLatentInvolutionTopCat

namespace InfoGeometry.Topology

/-!
# Reversal descent to the observational symbolic-latent quotient

An ambient modular reversal descends through an observational quotient only
when it preserves the observation map.  Continuity of the descended map is
kept as an explicit quotient-topology property.
-/

structure SymbolicLatentObservableModularReversal
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S) where
  reversal : SymbolicLatentModularReversal Φ.toSymbolicLatentModularFlow
  preserves_observation : ∀ x : X,
    S.obs (reversal.involution x) = S.obs x

def descendedSymbolicLatentObservationInvolution
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ) :
    SymbolicLatentObservationQuotient S →
      SymbolicLatentObservationQuotient S :=
  Quotient.lift
    (fun x => symbolicLatentObservationQuotientMap S
      (R.reversal.involution x))
    (by
      intro x y hxy
      apply Quotient.sound
      exact (R.preserves_observation x).trans (hxy.trans (R.preserves_observation y).symm))

@[simp] theorem descendedSymbolicLatentObservationInvolution_mk
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ) (x : X) :
    descendedSymbolicLatentObservationInvolution R
      (symbolicLatentObservationQuotientMap S x) =
        symbolicLatentObservationQuotientMap S (R.reversal.involution x) :=
  rfl

theorem descendedSymbolicLatentObservationInvolution_involutive
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ) (q :
      SymbolicLatentObservationQuotient S) :
    descendedSymbolicLatentObservationInvolution R
      (descendedSymbolicLatentObservationInvolution R q) = q := by
  refine Quotient.inductionOn q ?_
  intro x
  change symbolicLatentObservationQuotientMap S
      (R.reversal.involution (R.reversal.involution x)) =
    symbolicLatentObservationQuotientMap S x
  rw [R.reversal.twice]

def SymbolicLatentObservableModularReversal.toQuotientInvolution
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R)) :
    SymbolicLatentInvolution (SymbolicLatentObservationQuotient S) where
  toFun := descendedSymbolicLatentObservationInvolution R
  continuous_toFun := h_cont
  involutive := descendedSymbolicLatentObservationInvolution_involutive R

theorem SymbolicLatentObservableModularReversal.toQuotientInvolution_commutes_with_projection
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R))
    (x : X) :
    R.toQuotientInvolution h_cont
      (symbolicLatentObservationQuotientMap S x) =
        symbolicLatentObservationQuotientMap S (R.reversal.involution x) :=
  descendedSymbolicLatentObservationInvolution_mk R x

theorem SymbolicLatentObservableModularReversal.toQuotientInvolution_reverses_flow
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (h_involution : Continuous (descendedSymbolicLatentObservationInvolution R))
    (t : ℝ) (q : SymbolicLatentObservationQuotient S) :
    R.toQuotientInvolution h_involution
      (descendedSymbolicLatentObservationFlow Φ t q) =
      descendedSymbolicLatentObservationFlow Φ (-t)
        (R.toQuotientInvolution h_involution q) := by
  refine Quotient.inductionOn q ?_
  intro x
  change symbolicLatentObservationQuotientMap S
      (R.reversal.involution (Φ.act t x)) =
    symbolicLatentObservationQuotientMap S
      (Φ.act (-t) (R.reversal.involution x))
  exact congrArg (symbolicLatentObservationQuotientMap S)
    (R.reversal.reverses_flow t x)

end InfoGeometry.Topology
