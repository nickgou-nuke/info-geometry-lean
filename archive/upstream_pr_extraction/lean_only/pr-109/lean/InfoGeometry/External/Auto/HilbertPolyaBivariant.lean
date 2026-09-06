import Mathlib.Tactic
import InfoGeometry.External.Auto.ZetaCoordinateSymmetry
import InfoGeometry.External.Auto.AnomalousKMSFlow
import InfoGeometry.External.Auto.KasparovKreinCategory
import InfoGeometry.External.Auto.UnifiedAnomalyArchitecture

noncomputable section

namespace InfoGeometry.Canonical.HilbertPolyaBivariant

open Complex
open Set


/--
A typed, two-branch statement of the Hilbert–Pólya extraction inside this repository:
- a KK-factorized O₂ channel is identified with the anomaly index,
- Connes/KK-topology collapses the anomaly,
- strict convexity/axis symmetry locks the thermodynamic axis,
- CPT thermodynamics normalizes to one.
-/
theorem bivariant_hilbert_polya_extraction
    (f : ℝ → ℝ)
    (hConvex : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) f)
    (hSymm : ∀ σ ∈ Ioo (0 : ℝ) 1, f (1 - σ) = f σ)
    (σ : ℝ)
    (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (hσ_ne : σ ≠ InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.criticalAxis)
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (hFaith : AnomalousKMSFlow.TraceFaithful H C.tr)
    (S0 c : ℝ) (hc : 0 < c)
    {K1 : Type*} [AddCommGroup K1]
    {A Ctxt : Type}
    [InfoGeometry.Canonical.KasparovKreinCategory.KasparovKreinData]
    (k : CuntzKTheoryPairing.TrivialK0Model) (x : K1)
    (chain : InfoGeometry.Canonical.KasparovKreinCategory.KKProductChain (A := A) (C := Ctxt))
    (hPair :
      AnomalousKMSFlow.anomalousIndex H C =
        InfoGeometry.Canonical.KasparovKreinCategory.kkBoundaryPairing H chain.left chain.right k x)
    (β : ℝ) (S : Finset ℕ)
    (hβ : 0 < β) (hS : ∀ p ∈ S, 1 < p) :
    C.δK = 0 ∧
      (ConnesSpectralAction.connesSpectralAction (H := H) C C.δK S0 c = S0) ∧
      (∀ δ : Module.End ℂ H,
        ConnesSpectralAction.connesSpectralAction (H := H) C δ S0 c =
          ConnesSpectralAction.connesSpectralAction (H := H) C C.δK S0 c ↔ δ = C.δK) ∧
      (∀ s, AnomalousKMSFlow.anomalousLineLeak (AnomalousKMSFlow.anomalousIndexLeakProfile H C) s = 0) ∧
      (f InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.criticalAxis < f σ) ∧
      (PrimonSuperThermo.totalCPTPartition β S = 1) := by
  have hPair' :
      AnomalousKMSFlow.anomalousIndex H C =
        (inferInstance : CuntzKTheoryPairing.ConnesChernPairing
          CuntzKTheoryPairing.TrivialK0Model K1).pair k x := by
    simpa [InfoGeometry.Canonical.KasparovKreinCategory.kkBoundaryPairing] using hPair
  exact InfoGeometry.Canonical.UnifiedAnomalyArchitecture.unified_architecture_of_anomaly_proof
    (f := f) hConvex hSymm σ hσ hσ_ne
    (H := H) C hFaith S0 c hc k x hPair' β S hβ hS

/--
If the KK channel is constrained by KK-contractibility at `O₂`, no nontrivial
Kasparov product chain can exist through the boundary.
-/
theorem bivariant_boundary_forbids_off_axis_factorization
    {A Ctxt : Type}
    [InfoGeometry.Canonical.KasparovKreinCategory.KasparovKreinData]
    (hK : InfoGeometry.Canonical.KasparovKreinCategory.KKContractibleBoundary
      InfoGeometry.Canonical.KasparovKreinCategory.O2Boundary)
    (chain : InfoGeometry.Canonical.KasparovKreinCategory.KKProductChain (A := A) (C := Ctxt)) :
    False := by
  exact InfoGeometry.Canonical.KasparovKreinCategory.kasparov_krein_product_chain_contractibility_forbids hK chain

/--
A tiny definitional bridge: in this model, ‘critical axis trapping’ is exactly the
statement `Re(s)=1/2`.
-/
def HilbertPolyaCriticalAxis (s : ℂ) : Prop := s.re = InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.criticalAxis

/--
An explicit factorization through a KK-contractible O₂ boundary is impossible.

This is deliberately only the categorical firewall theorem.  It does not claim
that an off-axis complex number produces such a Kasparov product chain.
-/
theorem HilbertPolya_o2_factorization_forbidden_by_contractibility
    {A Ctxt : Type}
    [InfoGeometry.Canonical.KasparovKreinCategory.KasparovKreinData]
    (hK : InfoGeometry.Canonical.KasparovKreinCategory.KKContractibleBoundary
      InfoGeometry.Canonical.KasparovKreinCategory.O2Boundary)
    (chain : InfoGeometry.Canonical.KasparovKreinCategory.KKProductChain (A := A) (C := Ctxt))
    (_s : ℂ) :
    False := by
  exact bivariant_boundary_forbids_off_axis_factorization (A := A) (Ctxt := Ctxt) hK chain

end InfoGeometry.Canonical.HilbertPolyaBivariant
