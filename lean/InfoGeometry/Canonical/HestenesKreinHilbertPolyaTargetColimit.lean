import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.MajoranaPolyaHilbert.HilbertPolya
import InfoGeometry.Arithmetic.MajoranaPolyaHilbert.RelativeDeterminant
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Hilbert--Pólya target readouts on the Hestenes--Krein colimit

This owner translates the two remaining target packets: a self-adjoint
operator target and the relative determinant/scattering target.  The channel
equalities are explicit premises.  No self-adjointness, determinant identity,
or RH implication is constructed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinHilbertPolyaTargetColimit

open InfoGeometry.Arithmetic.MajoranaPolyaHilbert
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein

def relativeMBKRealChannelReadout
    (D : RelativeMBKDeterminantScatteringData ℝ ℝ ℝ) : Fin 4 → ℝ :=
  ![D.diracCutoff, D.diracFree, D.relativeDeterminant, D.scatteringPhase]

theorem relativeMBKRealChannelReadout_injective
    {D E : RelativeMBKDeterminantScatteringData ℝ ℝ ℝ}
    (h : relativeMBKRealChannelReadout D =
      relativeMBKRealChannelReadout E) :
    D = E := by
  cases D with
  | mk d₀ d₁ d₂ d₃ =>
    cases E with
    | mk e₀ e₁ e₂ e₃ =>
      simp only [relativeMBKRealChannelReadout] at h
      have h₀ := congrFun h 0
      have h₁ := congrFun h 1
      have h₂ := congrFun h 2
      have h₃ := congrFun h 3
      simp at h₀ h₁ h₂ h₃
      subst e₀
      subst e₁
      subst e₂
      subst e₃
      rfl

def hilbertPolyaRealReadout
    (D : CompletedXiHilbertPolyaReduction ℝ) : ℝ :=
  D.selfAdjointOperator

theorem hilbertPolyaRealReadout_injective
    {D E : CompletedXiHilbertPolyaReduction ℝ}
    (h : hilbertPolyaRealReadout D = hilbertPolyaRealReadout E) :
    D = E := by
  cases D with
  | mk d =>
    cases E with
    | mk e =>
      simp only [hilbertPolyaRealReadout] at h
      cases h
      rfl

def stageRelativeMBKReadout
    {C : HestenesKreinCone}
    (readout : ∀ n, Fin 4 → DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (channel : Fin 4) (x : DoubledSpace (C.Base n)) : ℝ :=
  readout n channel x

def limitRelativeMBKReadout
    {C : HestenesKreinCone}
    (readout : Fin 4 → DoubledSpace C.LimitBase → ℝ)
    (channel : Fin 4) (x : DoubledSpace C.LimitBase) : ℝ :=
  readout channel x

theorem stageRelativeMBKReadout_eq_limit_of_components
    {C : HestenesKreinCone}
    (stageData : ∀ n, RelativeMBKDeterminantScatteringData ℝ ℝ ℝ)
    (limitData : RelativeMBKDeterminantScatteringData ℝ ℝ ℝ)
    (hcutoff : ∀ n, (stageData n).diracCutoff = limitData.diracCutoff)
    (hfree : ∀ n, (stageData n).diracFree = limitData.diracFree)
    (hdeterminant : ∀ n,
      (stageData n).relativeDeterminant = limitData.relativeDeterminant)
    (hscattering : ∀ n,
      (stageData n).scatteringPhase = limitData.scatteringPhase)
    (n : ℕ) (channel : Fin 4) (x : DoubledSpace (C.Base n)) :
    stageRelativeMBKReadout
        (fun n channel _ => relativeMBKRealChannelReadout (stageData n) channel)
        n channel x =
      limitRelativeMBKReadout
        (fun channel _ => relativeMBKRealChannelReadout limitData channel)
        channel (C.ι n x) := by
  unfold stageRelativeMBKReadout limitRelativeMBKReadout
  fin_cases channel <;>
    simp [relativeMBKRealChannelReadout, hcutoff, hfree, hdeterminant,
      hscattering]

theorem stageRelativeMBKReadout_bondIterate_eq
    {C : HestenesKreinCone}
    (readout : ∀ n, Fin 4 → DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m channel x,
      readout (n + m) channel (C.toFilteredPhaseCone.bondIterate n m x) =
        readout n channel x)
    (n m : ℕ) (channel : Fin 4) (x : DoubledSpace (C.Base n)) :
    stageRelativeMBKReadout readout (n + m) channel
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageRelativeMBKReadout readout n channel x := by
  unfold stageRelativeMBKReadout
  exact hreadout n m channel x

def stageHilbertPolyaReadout
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  readout n x

def limitHilbertPolyaReadout
    {C : HestenesKreinCone}
    (readout : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  readout x

theorem stageHilbertPolyaReadout_eq_limit_of_components
    {C : HestenesKreinCone}
    (stageData : ∀ n, CompletedXiHilbertPolyaReduction ℝ)
    (limitData : CompletedXiHilbertPolyaReduction ℝ)
    (hoperator : ∀ n,
      (stageData n).selfAdjointOperator = limitData.selfAdjointOperator)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageHilbertPolyaReadout
        (fun n _ => hilbertPolyaRealReadout (stageData n)) n x =
      limitHilbertPolyaReadout
        (fun _ => hilbertPolyaRealReadout limitData) (C.ι n x) := by
  unfold stageHilbertPolyaReadout limitHilbertPolyaReadout
  exact hoperator n

theorem stageHilbertPolyaReadout_bondIterate_eq
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m x,
      readout (n + m) (C.toFilteredPhaseCone.bondIterate n m x) =
        readout n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageHilbertPolyaReadout readout (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageHilbertPolyaReadout readout n x := by
  unfold stageHilbertPolyaReadout
  exact hreadout n m x

end InfoGeometry.Canonical.HestenesKreinHilbertPolyaTargetColimit

end noncomputable section
