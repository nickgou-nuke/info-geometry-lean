import proofs.FibonacciCliffordBridge
import proofs.QuadricConf3BraidingCooperadBridge
import proofs.LogCFTGeneratingPotential
import proofs.NonIsoConf3LightConeQuadricSummary
import proofs.NonIsoConf3DeRhamCooperad
import proofs.NonIsoConf3DeRhamCohomologyFormula
import proofs.QuadraticConfiguration3

/-!
# Anyonic baryon / Gibbs-Wilson bridge

This module composes three finite layers:

* Fibonacci fusion: `τ ⊗ τ ⊗ τ = τ ⊕ 1 ⊕ τ` as a finite channel list;
* Gibbs/log-ratio exactness: detailed balance kills Wilson entropy cycles;
* quadric `Conf₃`: the rank-32 product/Leray cooperad branch.

The baryon analogy, physical parafermion realization, and continuum
gravity/TKK interpretation are not claimed here; this file keeps the finite
fusion, boundary-complex, and edge-cocycle statements explicit.
-/

noncomputable section

namespace AnyonicBaryonGibbsWilsonBridge

open InfoGeometry.GrandUnification.FibonacciCliffordBridge
open QuadricConf3BraidingCooperadBridge
open LightConeConf3DeRhamCooperad
open NonIsoConf3DeRhamCooperad
open NonIsoConf3LightConeQuadricSummary
open NonIsoConf3DeRhamCohomologyFormula
open VacuumCohomology
open VertexAlgebraBraidingCocycle
open VertexAlgebraBraidingCocycle.EdgeSystem

/-- The finite fusion-channel list for three Fibonacci anyons. -/
def threeTauFusionChannels : List FibSector :=
  fibFuse FibSector.one FibSector.tau ++
    fibFuse FibSector.tau FibSector.tau

/-- Three τ anyons decompose as `τ ⊕ 1 ⊕ τ` at the channel-list level. -/
theorem threeTauFusionChannels_eq :
    threeTauFusionChannels =
      [FibSector.tau, FibSector.one, FibSector.tau] := by
  rfl

/-- Multiplicity of the vacuum/singlet channel in a finite Fibonacci channel list. -/
def singletMultiplicity : List FibSector → ℕ
  | [] => 0
  | FibSector.one :: xs => singletMultiplicity xs + 1
  | FibSector.tau :: xs => singletMultiplicity xs

/-- Multiplicity of the τ channel in a finite Fibonacci channel list. -/
def tauMultiplicity : List FibSector → ℕ
  | [] => 0
  | FibSector.one :: xs => tauMultiplicity xs
  | FibSector.tau :: xs => tauMultiplicity xs + 1

/-- There is exactly one vacuum/singlet channel in the three-τ channel list. -/
theorem threeTauFusion_singlet_count :
    singletMultiplicity threeTauFusionChannels = 1 := by
  rfl

/-- There are two τ channels in the three-τ channel list. -/
theorem threeTauFusion_tau_count :
    tauMultiplicity threeTauFusionChannels = 2 := by
  rfl

/-- Finite synthesis: three-τ fusion has one singlet channel; exact Gibbs
log-ratios kill both Conf3 triangle Wilson cycles; and the quadric/cooperad
finite branch has rank `32` versus the OS reference rank `24`. -/
theorem anyonic_baryon_gibbs_wilson_synthesis
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {D : ℕ} (bnd : BoundaryOperator V) (state : V)
    (S : EdgeSystem Vertex3) (potential : Vertex3 → ℝ)
    (hExact : IsExact S potential) :
    threeTauFusionChannels =
      [FibSector.tau, FibSector.one, FibSector.tau] ∧
    singletMultiplicity threeTauFusionChannels = 1 ∧
    tauMultiplicity threeTauFusionChannels = 2 ∧
    Fintype.card LightConeProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    cycleEntropyProduction S triangle012 = 0 ∧
    cycleEntropyProduction S triangle021 = 0 := by
  rcases quadric_conf3_deRham_cooperad_braiding_synthesis D bnd state S potential hExact with
    ⟨h32, h24, _, _, _, h012, h021, _, _, _, _, _⟩
  exact ⟨threeTauFusionChannels_eq,
    threeTauFusion_singlet_count,
    threeTauFusion_tau_count,
    h32,
    h24,
    h012,
    h021⟩

/-- Export of the rank-32 pair-`12` environmental split for downstream finite
  use in the anyonic/Gibbs/Wilson chain.
-/
theorem anyonic_pair12_environmental_split_preserves_rank32
    {D : ℕ}
    (S : ConcreteDeRhamCooperadData D)
    (hchoice : S.relationChoice = ModelChoice.productLeray) :
    (NonIsoConf3DeRhamCohomologyFormula.arityThreeInternalEdges
      QuadraticConfiguration3.BlockDecomp3.pair12_3).card = 1 ∧
    (NonIsoConf3DeRhamCohomologyFormula.arityThreeOuterEdges
      QuadraticConfiguration3.BlockDecomp3.pair12_3).card = 2 := by
  have h := lightCone_pair12_environmental_decomposition_preserves_quadric_rank32 (D := D) S hchoice
  exact ⟨h.2.2.1, h.2.2.2⟩

end AnyonicBaryonGibbsWilsonBridge

end noncomputable section
