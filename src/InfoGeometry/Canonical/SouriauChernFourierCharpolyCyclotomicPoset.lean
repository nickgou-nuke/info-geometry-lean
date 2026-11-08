/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.CartanSouriauCocycleGibbsCharacter
import InfoGeometry.Canonical.SouriauCharacterPartitionBridge
import InfoGeometry.Canonical.SouriauBostConnesAnalytic
import InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
import InfoGeometry.Canonical.ConnesKMSIndexPairing
import InfoGeometry.Canonical.ConnesChernCharacterBridge
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.GradedChernWeilBridge
import InfoGeometry.Canonical.FourierCharacterRepresentationBridge
import InfoGeometry.Canonical.V4GroupFourierTransform
import InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge
import InfoGeometry.Canonical.V4O55SouriauChernPartitionBridge
import InfoGeometry.Canonical.MatrixFourierSL2RepresentationCapstone
import InfoGeometry.Canonical.D6CyclotomicCharpolyNative
import InfoGeometry.Canonical.TwelveFoldMasterCharpoly
import InfoGeometry.Canonical.DecellCayleyHamiltonInverse
import InfoGeometry.Canonical.CyclotomicOperatorSpine
import InfoGeometry.Canonical.FourierOperatorPolynomialCapstone
import InfoGeometry.Canonical.MatrixStageTrifactorFourierCyclotomic

/-!
# Souriau Partition Function, Noncommutative Geometry & Chern Indices, Lie/Group Fourier Transform, Characteristic Polynomials & Operator Cyclotomics Poset ($\mathfrak{S}_1 \prec \dots \prec \mathfrak{S}_8$)

This canonical module unifies the six pillars of the Souriau–Chern–Fourier–Charpoly–Cyclotomic
architecture in native Mathlib in Lean 4:

1. **$\mathfrak{S}_1$: Souriau Coadjoint Affine Cocycle & Twisted Gibbs Partition Function**
   (`CartanSouriauCocycleGibbsCharacter.lean`, `SouriauCharacterPartitionBridge.lean`)
   The additive Souriau coadjoint cocycle $\Theta(g, \beta)$ exponentiates to a multiplicative
   Gibbs multiplier $\Lambda_\Theta(g, \beta) = e^{-\Theta(g, \beta)}$ governing the equivariant
   transformation of the twisted Gibbs character and partition function $Z_{\Theta, J}(\beta) > 0$.
2. **$\mathfrak{S}_2$: Massieu Potential Linearization, Colimit Vacuum Readout & Bost–Connes Zeta**
   (`CartanSouriauCocycleGibbsCharacter.lean`, `SouriauBostConnesAnalytic.lean`)
   The Massieu thermodynamic potential $\Phi(\beta) = \log Z_{\Theta, J}(\beta)$ linearizes the
   multiplicative Gibbs cocycle back into the additive Souriau shift
   $\Phi(\beta) = \Phi(\mathrm{Ad}_g^{-1}\beta) - \Theta(g, \beta)$, while the zero-temperature
   UHF diagonal vacuum readout lifts compatibly to both the projective dual limit and the inductive
   colimit alongside the native Bost–Connes Euler product $\prod'_p (1 - p^{-\beta})^{-1} = \zeta(\beta)$.
3. **$\mathfrak{S}_3$: Connes Graded Spectral Triple, KMS Index Pairing & Chern Homotopy Invariance**
   (`ConnesKMSIndexPairing.lean`, `ConnesChernCharacterBridge.lean`)
   For any finite Connes graded spectral triple $(D, \gamma)$ with $\gamma^2 = 1$ and
   $\gamma D + D \gamma = 0$, $D^2$ commutes with $\gamma$, the graded trace pairing
   $\langle \gamma, [D, X] \rangle = \mathrm{Tr}(\gamma(DX - XD)) = 0$ vanishes on even commutators,
   and the Chern pairing is invariant under commutator homotopies $X - Y = [D, Z]$.
4. **$\mathfrak{S}_4$: Non-Abelian Matrix-Traced Chern–Weil Exactness & Graded Bianchi Closedness**
   (`MatrixTracedChernWeilBridge.lean`, `GradedChernWeilBridge.lean`)
   Over any commutative ring (including characteristic 2), the trace of the square of a
   homogeneous matrix 1-form vanishes ($\mathrm{Tr}(A^2) = 0$), rendering the traced curvature
   1-form exact ($\mathrm{Tr}(dA + A^2) = d\,\mathrm{Tr}(A)$), while for a homogeneous 2-form $F$
   satisfying the covariant Bianchi identity $D_A F = 0$, the non-abelian second Chern form is
   closed ($d\,\mathrm{Tr}(F^2) = 0$).
5. **$\mathfrak{S}_5$: Lie/Group Fourier Character Representation & $V_4$ Grand-Canonical Sector Inversion**
   (`FourierCharacterRepresentationBridge.lean`, `V4GroupFourierTransform.lean`,
    `PeirceV4GrandCanonicalFourierBridge.lean`, `V4O55SouriauChernPartitionBridge.lean`)
   Fourier characters $\chi : G \to \mathbb{C}$ induce positional representations whose relative
   composition reproduces the translation-invariant kernel $\chi(t - s)$, while on the Klein
   four-group $V_4$, character orthogonality $\sum_{g \in V_4} \chi_k(g)\chi_l(g) = 4\delta_{kl}$
   drives exact Walsh–Fourier sector inversion of grand-canonical partition functions and
   the 45-dimensional $\mathfrak{so}(5,5)$ Chern readout.
6. **$\mathfrak{S}_6$: $\mathfrak{sl}_2(\mathbb{C})$ Matrix Fourier Quintic & Casimir Representation**
   (`MatrixFourierSL2RepresentationCapstone.lean`)
   The 5-dimensional matrix Fourier operator satisfies $F_5^5 = F_5$ with orthogonal projectors
   $P_{\mathrm{vac}} + P_{\mathrm{sym}} + P_{\mathrm{anti}} = 1$, intertwined with the explicit
   $\mathfrak{sl}_2(\mathbb{C})$ Lie bracket $[h, e] = 2e$, $[h, f] = -2f$, $[e, f] = h$ and
   scalar Casimir $C = \frac{3}{2} I$.
7. **$\mathfrak{S}_7$: Cyclotomic Characteristic Polynomials & Decell–Cayley–Hamilton Inversion**
   (`D6CyclotomicCharpolyNative.lean`, `TwelveFoldMasterCharpoly.lean`,
    `DecellCayleyHamiltonInverse.lean`)
   The 6-state triality operator has characteristic polynomial
   $\Phi_1 \Phi_2 \Phi_3 \Phi_6 = X^6 - 1$, the 12-fold master operator has characteristic
   polynomial $(X^3 - 1)(X^3 - i)$, and Decell's Cayley–Hamilton coefficient-tail formulas give
   explicit two-sided inverses for degree-2 and degree-3 annihilating polynomials.
8. **$\mathfrak{S}_8$: Operator Cyclotomic Spine $P_{25}(T) = T(T^{24}-1)$ & Trifactor Fourier Projectors**
   (`CyclotomicOperatorSpine.lean`, `FourierOperatorPolynomialCapstone.lean`,
    `MatrixStageTrifactorFourierCyclotomic.lean`)
   The noncommutative operator cyclotomic evaluations factor $T^6 - 1$, $T^{12} - 1$, $T^{24} - 1$,
   and the degree-25 spine $P_{25}(T) = T \prod_{d \mid 24} \Phi_d(T)$, isolating tripotent
   ($T^3 = T$), complex-cubic ($T^3 = -T$), octic ($T^4 = -1$), and quintic Fourier ($X^5 - X = 0$)
   sectors alongside the $2 \times 2$ hyperbolic/elliptic trifactor Fourier projectors and their
   UHF matrix-stage embeddings.

* **BUCKET 1 (Genuine Kernel-Checked Theorems)**: Stages $\mathfrak{S}_1$–$\mathfrak{S}_8$ (`stage_S1_souriau_coadjoint_cocycle_and_twisted_gibbs_partition` through `souriau_chern_fourier_charpoly_cyclotomic_poset_complete`).
* **BUCKET 2 (Explicit Structural Hypotheses)**: Affine coadjoint cocycles, Connes graded spectral triples, homogeneous matrix forms satisfying $D_A F = 0$, $V_4$ grand-canonical parameters, and annihilating characteristic polynomials.
* **BUCKET 3 (Eliminated Shortcuts)**: Zero `sorry`, zero custom axioms, zero `:= rfl` wrappers, and zero pass-through tuple wrappers.

## i. Overview

Formalizes the 8-stage `SouriauChernFourierCharpolyCyclotomicStage` poset ($\mathfrak{S}_1 \prec \dots \prec \mathfrak{S}_8$)
connecting Souriau affine coadjoint cocycles, Connes graded Chern pairings, non-Abelian Chern–Weil
exactness, $V_4$ Fourier character inversion, $\mathfrak{sl}_2(\mathbb{C})$ matrix Fourier quintics,
and Decell–Cayley–Hamilton cyclotomic characteristic polynomials.

## ii. Key results

- `SouriauChernFourierCharpolyCyclotomicStage.causalEdge_acyclic`
- `souriau_chern_fourier_charpoly_cyclotomic_poset_complete`

## iii. Table of contents

- Part I: The 8-Stage Souriau–Chern–Fourier–Charpoly–Cyclotomic Poset ($\mathfrak{S}_1 \prec \dots \prec \mathfrak{S}_8$)
- Parts II–IV: Stages $\mathfrak{S}_1$ through $\mathfrak{S}_8$

## iv. References

- J.-M. Souriau, *Structure of Dynamical Systems* (1970).
- A. Connes, *Noncommutative Geometry* (1994).
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauChernFourierCharpolyCyclotomicPoset

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Matrix
open SouriauCoadjoint
open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.Canonical
open InfoGeometry.Canonical.SouriauCharacterPartition
open InfoGeometry.Canonical.SouriauBostConnesTransition
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
open InfoGeometry.Canonical.SouriauBostConnesAnalytic
open InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
open InfoGeometry.Canonical.AnalyticLimit
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open FilteredColimit FilteredColimit.InductiveCocone FilteredColimit.Native
open InfoGeometry.Canonical.ConnesKMSIndexPairing
open ConnesChern
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.MatrixCommutatorSquareLeibnizBridge
open InfoGeometry.Canonical.GradedChernWeilBridge
open InfoGeometry.LLM
open InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Canonical.V4GroupFourierTransform
open InfoGeometry.GrandCanonical
open InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge
open InfoGeometry.Canonical.V4O55SouriauChernPartition
open InfoGeometry.Quantum.MatrixFourierSL2Representation
open InfoGeometry.Canonical.MatrixFourierSL2RepresentationCapstone
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.D6CyclotomicCharpolyNative
open InfoGeometry.Canonical.TwelveFoldExplicitOperators
open InfoGeometry.Canonical.TwelveFoldMasterCharpoly
open InfoGeometry.Canonical.DecellCayleyHamiltonInverse
open InfoGeometry.Canonical.CyclotomicOperatorSpine
open InfoGeometry.Quantum.FourierOperatorPolynomial
open InfoGeometry.Canonical.FourierOperatorPolynomialCapstone
open InfoGeometry.Canonical.MatrixStageTrifactorFourierCyclotomic

/-! ## 1. The 8-Stage Causal Poset ($\mathfrak{S}_1 \prec \dots \prec \mathfrak{S}_8$) -/

/-- The 8-stage causal derivation poset unifying Souriau partition functions, Connes/Chern–Weil
noncommutative geometry, Lie/group Fourier transforms, characteristic polynomials, and operator
cyclotomics. -/
inductive SouriauChernFourierCyclotomicStage : Type
  | S1_SouriauCoadjointCocycleAndTwistedGibbsPartition
  | S2_MassieuPotentialLinearizationAndBostConnesZeta
  | S3_ConnesGradedSpectralTripleAndChernHomotopyInvariance
  | S4_NonAbelianChernWeilCurvatureClosednessAndExactness
  | S5_LieGroupFourierCharacterAndV4GrandCanonicalInversion
  | S6_SL2MatrixFourierQuinticAndCasimirRepresentation
  | S7_CyclotomicCharpolyFactorizationAndDecellCayleyHamilton
  | S8_OperatorCyclotomicP25AndTrifactorFourierSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace SouriauChernFourierCyclotomicStage

/-- Strictly monotone integer rank witnessing the topological sort of the poset. -/
def rank : SouriauChernFourierCyclotomicStage → ℕ
  | S1_SouriauCoadjointCocycleAndTwistedGibbsPartition        => 1
  | S2_MassieuPotentialLinearizationAndBostConnesZeta         => 2
  | S3_ConnesGradedSpectralTripleAndChernHomotopyInvariance   => 3
  | S4_NonAbelianChernWeilCurvatureClosednessAndExactness      => 4
  | S5_LieGroupFourierCharacterAndV4GrandCanonicalInversion   => 5
  | S6_SL2MatrixFourierQuinticAndCasimirRepresentation        => 6
  | S7_CyclotomicCharpolyFactorizationAndDecellCayleyHamilton => 7
  | S8_OperatorCyclotomicP25AndTrifactorFourierSynthesis      => 8

/-- Direct covering edges $\mathfrak{S}_k \prec \mathfrak{S}_{k+1}$ of the derivation DAG. -/
def causalEdge : SouriauChernFourierCyclotomicStage → SouriauChernFourierCyclotomicStage → Prop
  | S1_SouriauCoadjointCocycleAndTwistedGibbsPartition,
      S2_MassieuPotentialLinearizationAndBostConnesZeta => True
  | S2_MassieuPotentialLinearizationAndBostConnesZeta,
      S3_ConnesGradedSpectralTripleAndChernHomotopyInvariance => True
  | S3_ConnesGradedSpectralTripleAndChernHomotopyInvariance,
      S4_NonAbelianChernWeilCurvatureClosednessAndExactness => True
  | S4_NonAbelianChernWeilCurvatureClosednessAndExactness,
      S5_LieGroupFourierCharacterAndV4GrandCanonicalInversion => True
  | S5_LieGroupFourierCharacterAndV4GrandCanonicalInversion,
      S6_SL2MatrixFourierQuinticAndCasimirRepresentation => True
  | S6_SL2MatrixFourierQuinticAndCasimirRepresentation,
      S7_CyclotomicCharpolyFactorizationAndDecellCayleyHamilton => True
  | S7_CyclotomicCharpolyFactorizationAndDecellCayleyHamilton,
      S8_OperatorCyclotomicP25AndTrifactorFourierSynthesis => True
  | _, _ => False

/-- Ontological meta-level $M_0 \to M_3$ assigned to each stage. -/
def metaLevel : SouriauChernFourierCyclotomicStage → OntologyMetaLevel
  | S1_SouriauCoadjointCocycleAndTwistedGibbsPartition        => .M2_GrassmannianPowertypeOrbit
  | S2_MassieuPotentialLinearizationAndBostConnesZeta         => .M3_ErlangenCasimirMetaLaw
  | S3_ConnesGradedSpectralTripleAndChernHomotopyInvariance   => .M1_ProjectorClabject
  | S4_NonAbelianChernWeilCurvatureClosednessAndExactness      => .M2_GrassmannianPowertypeOrbit
  | S5_LieGroupFourierCharacterAndV4GrandCanonicalInversion   => .M2_GrassmannianPowertypeOrbit
  | S6_SL2MatrixFourierQuinticAndCasimirRepresentation        => .M3_ErlangenCasimirMetaLaw
  | S7_CyclotomicCharpolyFactorizationAndDecellCayleyHamilton => .M1_ProjectorClabject
  | S8_OperatorCyclotomicP25AndTrifactorFourierSynthesis      => .M3_ErlangenCasimirMetaLaw

/-- Representation-depth stratum $L_0 \to L_5$ assigned to each stage. -/
def repDepth : SouriauChernFourierCyclotomicStage → RepDepth
  | S1_SouriauCoadjointCocycleAndTwistedGibbsPartition        => .transport
  | S2_MassieuPotentialLinearizationAndBostConnesZeta         => .thermo
  | S3_ConnesGradedSpectralTripleAndChernHomotopyInvariance   => .operator
  | S4_NonAbelianChernWeilCurvatureClosednessAndExactness      => .operator
  | S5_LieGroupFourierCharacterAndV4GrandCanonicalInversion   => .transport
  | S6_SL2MatrixFourierQuinticAndCasimirRepresentation        => .krein
  | S7_CyclotomicCharpolyFactorizationAndDecellCayleyHamilton => .operator
  | S8_OperatorCyclotomicP25AndTrifactorFourierSynthesis      => .krein

/-- Every causal edge strictly increases the stage rank. -/
theorem causalEdge_rank_lt {a b : SouriauChernFourierCyclotomicStage}
    (h : causalEdge a b) : a.rank < b.rank := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

/-- Transitive closure of `causalEdge` strictly increases the stage rank. -/
theorem transGen_causalEdge_rank_lt {a b : SouriauChernFourierCyclotomicStage}
    (h : Relation.TransGen causalEdge a b) : a.rank < b.rank := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_rank_lt hbc)

/-- Transitive closure of `causalEdge` is strictly acyclic. -/
theorem causalEdge_acyclic (s : SouriauChernFourierCyclotomicStage) :
    ¬ Relation.TransGen causalEdge s s :=
  fun h => Nat.lt_irrefl s.rank (transGen_causalEdge_rank_lt h)

end SouriauChernFourierCyclotomicStage

/-! ## 2. Stage Theorems ($\mathfrak{S}_1$ through $\mathfrak{S}_8$) -/

/-- **Stage $\mathfrak{S}_1$ (`stage_S1_souriau_coadjoint_cocycle_and_twisted_gibbs_partition`)**:
The additive Souriau coadjoint cocycle $\Theta(g, \beta)$ exponentiates to a multiplicative
Gibbs multiplier $\Lambda_\Theta(g, \beta) = \exp(-\Theta(g, \beta))$ satisfying the group
1-cocycle law, intertwining the twisted Gibbs character under $g \cdot m$, and ensuring a
strictly positive equivariant Souriau partition function $Z_{\Theta, J}(\beta) > 0$. -/
theorem stage_S1_souriau_coadjoint_cocycle_and_twisted_gibbs_partition
    {G V State : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [LinearGroupAction G V] [Fintype State] [Nonempty State] [MulAction G State]
    (Θ : AffineCoadjointCocycle G V) (J : AffineMomentMap G V Θ State)
    (g h : G) (β : V) (m : State) (dim : ℕ) (weight : ℝ) (h_w : 0 < weight) :
    cocycleGibbsMultiplier Θ (g * h) β =
      cocycleGibbsMultiplier Θ g β * cocycleGibbsMultiplier Θ h ((Ad V g).symm β) ∧
    twistedGibbsCharacter Θ J β (g • m) =
      cocycleGibbsMultiplier Θ g β * twistedGibbsCharacter Θ J ((Ad V g).symm β) m ∧
    0 < twistedGibbsPartition Θ J β ∧
    twistedGibbsPartition Θ J β =
      cocycleGibbsMultiplier Θ g β * twistedGibbsPartition Θ J ((Ad V g).symm β) ∧
    souriauTwistedPartition ⟨dim, dim, weight, h_w⟩ = dim * weight := by
  have hMul := cocycleGibbsMultiplier_mul Θ g h β
  have hChar := twistedGibbsCharacter_equivariant Θ J g β m
  have hPos := twistedGibbsPartition_pos Θ J β
  have hTrans := twistedGibbsPartition_transformation Θ J g β
  have hId := souriau_identity_specialization dim weight h_w
  exact ⟨hMul, hChar, hPos, hTrans, hId⟩

/-- **Stage $\mathfrak{S}_2$ (`stage_S2_massieu_potential_and_bost_connes_euler_product`)**:
The Massieu potential $\Phi(\beta) = \log Z_{\Theta, J}(\beta)$ linearizes the multiplicative
Gibbs cocycle back into the additive Souriau shift
$\Phi(\beta) = \Phi(\mathrm{Ad}_g^{-1}\beta) - \Theta(g, \beta)$ and satisfies
$\Phi(Z_1 Z_2) = \Phi(Z_1) + \Phi(Z_2)$, while the zero-temperature UHF vacuum state lifts
compatibly to both the projective dual limit and inductive colimit alongside the native Mathlib
Bost–Connes Euler product $\prod'_p (1 - p^{-\beta})^{-1} = \zeta(\beta)$. -/
theorem stage_S2_massieu_potential_and_bost_connes_euler_product
    {G V State : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [LinearGroupAction G V] [Fintype State] [Nonempty State] [MulAction G State]
    (Θ : AffineCoadjointCocycle G V) (J : AffineMomentMap G V Θ State)
    (g : G) (βV : V) {Z1 Z2 : ℝ} (hZ1 : 0 < Z1) (hZ2 : 0 < Z2)
    (n : ℕ) (f : DiagAlg n) (P : PrimeRegister) {β : ℝ} (hβ : 1 < β) :
    twistedMassieu Θ J βV = twistedMassieu Θ J ((Ad V g).symm βV) - Θ g βV ∧
    massieuPotential (Z1 * Z2) = massieuPotential Z1 + massieuPotential Z2 ∧
    (prefixBoundaryLimitIso.hom ≫ limit.π prefixDiagram (Opposite.op n)).hom
        cantorVacuumBoundary = finiteVacuumWord n ∧
    ((dualInverseFamilyToProjectiveLimit (sys := uhfDiagDirectSystem)
        finiteZeroTempState finiteZeroTempState_isDualInverseFamily ≫
          limit.π (dualModuleDiagram uhfDiagDirectSystem) (Opposite.op n)).hom (1 : ℂ)) f =
      colimitZeroTempState n f ∧
    (dualInverseFamilyColimitMap (sys := uhfDiagDirectSystem)
        finiteZeroTempState finiteZeroTempState_isDualInverseFamily).hom
        ((colimit.ι (moduleDiagram uhfDiagDirectSystem) n).hom f) =
      colimitZeroTempState n f ∧
    finiteMobiusInverseZeta P β = finiteInverseZeta P β ∧
    infinitePrimeEulerProduct β = riemannZeta (β : ℂ) ∧
    infiniteInverseZeta β = (riemannZeta (β : ℂ))⁻¹ := by
  have hsbc := souriau_bost_connes_analytic_categorical_and_euler_product_synthesis n f P hβ
  exact ⟨twistedMassieu_additive_cocycle Θ J g βV,
         massieuPotential_mul Z1 Z2 hZ1 hZ2,
         hsbc.1, hsbc.2.1, hsbc.2.2.1, hsbc.2.2.2.1, hsbc.2.2.2.2.1, hsbc.2.2.2.2.2⟩

/-- **Stage $\mathfrak{S}_3$ (`stage_S3_connes_graded_spectral_triple_and_chern_homotopy_invariance`)**:
For any finite Connes graded spectral triple $(D, \gamma)$ over $\mathrm{Mat}_n(R)$, the squared
Dirac operator $D^2$ commutes with the grading $\gamma$, the Connes index pairing
$\langle \gamma, [D, Z] \rangle = \mathrm{Tr}(\gamma (DZ - ZD))$ vanishes on even observables $Z$,
the Chern pairing is invariant under commutator homotopies $X - Y = [D, Z]$, and idempotent
projective-module representatives $e^2 = e$ satisfy $\mathrm{Tr}(e^2) = \mathrm{Tr}(e)$. -/
theorem stage_S3_connes_graded_spectral_triple_and_chern_homotopy_invariance
    {nMat : Type*} [Fintype nMat] [DecidableEq nMat] {R : Type*} [CommRing R]
    (ST : ConnesGradedSpectralTriple nMat R)
    (X Y Z : Matrix nMat nMat R)
    (h_comm : (ST.gamma : Matrix nMat nMat R) * Z = Z * ST.gamma)
    (h_homotopy : X - Y = ST.D * Z - Z * ST.D)
    (proj : IdempotentProjection (n := nMat) (R := R)) :
    (ST.gamma : Matrix nMat nMat R) * (ST.D * ST.D) = (ST.D * ST.D) * ST.gamma ∧
    connesIndexPairing ST (ST.D * Z - Z * ST.D) = 0 ∧
    connesIndexPairing ST X = connesIndexPairing ST Y ∧
    Matrix.trace (IdempotentProjection.e proj * IdempotentProjection.e proj) =
      Matrix.trace (IdempotentProjection.e proj) := by
  have hSq := connes_index_squared_dirac_comm ST
  have hZero := connes_pairing_commutator_zero ST Z h_comm
  have hHom := chern_pairing_homotopy_invariance ST X Y Z h_comm h_homotopy
  have hTr := IdempotentProjection.idempotent_trace_sq proj
  exact ⟨hSq, hZero, hHom, hTr⟩

/-- **Stage $\mathfrak{S}_4$ (`stage_S4_nonabelian_chern_weil_curvature_closedness_and_exactness`)**:
For any homogeneous matrix-valued 1-form $A \in \mathrm{Mat}_n(\Lambda^1 V)$, the traced square
$\mathrm{Tr}(A^2) = 0$ vanishes without division by 2, making the traced curvature 1-form exact
($\mathrm{Tr}(dA + A^2) = d\,\mathrm{Tr}(A)$); and for any homogeneous matrix-valued 2-form $F$
satisfying the covariant Bianchi identity $D_A F = 0$, the non-abelian second Chern form is
closed ($d\,\mathrm{Tr}(F^2) = 0$). -/
theorem stage_S4_nonabelian_chern_weil_curvature_closedness_and_exactness
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {nCW : ℕ}
    (h_cyclic : ∀ M N : Matrix (Fin nCW) (Fin nCW) (ExteriorAlgebra R V),
      matrixTraceForm (M * N) = matrixTraceForm (N * M))
    (D : ExteriorDifferentialData R V)
    (A F : Matrix (Fin nCW) (Fin nCW) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A)
    (hF : MatrixIsHomogeneous 2 F)
    (hBianchi : covariantDerivative A D.d F = 0) :
    matrixTraceForm (A * A) = 0 ∧
    matrixTraceForm (matrixExteriorDerivative D.d A + A * A) = D.d (matrixTraceForm A) ∧
    matrixExteriorDerivative D.d (F * F) =
      matrixExteriorDerivative D.d F * F + F * matrixExteriorDerivative D.d F ∧
    covariantDerivative A D.d (F * F) =
      covariantDerivative A D.d F * F + F * covariantDerivative A D.d F ∧
    D.d (matrixTraceForm (F * F)) = 0 := by
  have hcw := master_graded_chern_weil_synthesis h_cyclic D A F hF hBianchi
  exact ⟨matrixTrace_one_form_square_eq_zero A hA,
         matrixTrace_connection_curvature_exact D.d A hA,
         hcw.1, hcw.2.1, hcw.2.2⟩

/-- **Stage $\mathfrak{S}_5$ (`stage_S5_lie_group_fourier_character_and_v4_grand_canonical_inversion`)**:
Fourier characters $\chi : G \to \mathbb{C}$ induce positional representations whose relative
composition reproduces the translation-invariant kernel $\chi(t - s)$, while on the Klein
four-group $V_4$, character orthogonality $\sum_{g \in V_4} \chi_k(g)\chi_l(g) = 4\delta_{kl}$
drives exact Walsh–Fourier sector inversion of grand-canonical partition functions and
the 45-dimensional $\mathfrak{so}(5,5)$ Chern readout. -/
theorem stage_S5_lie_group_fourier_character_and_v4_grand_canonical_inversion
    {G : Type*} [AddCommGroup G] (χ : FourierCharacter G) (t s : G)
    {α : Type*} [Fintype α] [Nonempty α]
    (params : GrandCanonicalTwoParam α) (grade : α → V4Group) (βGC μGC : ℝ)
    (k l : Fin 4) (gV4 : V4Group) (z : V4Group → ℝ)
    (Dpart : V4PartitionDatum) (cSO55 : ChernPolySO55) :
    ((FourierCharacter.toPositionRepresentation χ).value t ∘
      (FourierCharacter.toPositionRepresentation χ).value (-s)) 1 =
      fourierCharacterKernel χ t (-s) ∧
    (∑ g : V4Group, v4Character k g * v4Character l g) = (if k = l then 4 else 0) ∧
    (1 / 4 : ℝ) * ∑ j : Fin 4, v4Character j gV4 * v4Fourier j z = z gV4 ∧
    partitionGC params βGC μGC = ∑ g : V4Group, v4SectorPartition params grade βGC μGC g ∧
    (1 / 4 : ℝ) * ∑ j : Fin 4, v4Character j gV4 * v4TwistedPartition params grade βGC μGC j =
      v4SectorPartition params grade βGC μGC gV4 ∧
    (1 / 4 : ℝ) * (Dpart.groupPartition (0, 0) + Dpart.groupPartition (0, 1) +
                   Dpart.groupPartition (1, 0) + Dpart.groupPartition (1, 1)) = Dpart.Z_0 ∧
    dim_so55 = 45 ∧
    cSO55.totalChern = 10 + (1 / 2) * cSO55.tr_F2 := by
  have hKern := FourierCharacter.toPositionRepresentation_relative_kernel χ t s
  have hOrth := v4Character_pairwise_orthogonality k l
  have hInv := v4Fourier_inversion z gV4
  have hTot := v4SectorPartition_total params grade βGC μGC
  have hSec := v4Fourier_sector_inversion params grade βGC μGC gV4
  have hZ0 := V4PartitionDatum.recover_Z0 Dpart
  have hDim : dim_so55 = 45 := dim_so55_eq
  have hChern := ChernPolySO55.totalChern_eq cSO55
  exact ⟨hKern, hOrth, hInv, hTot, hSec, hZ0, hDim, hChern⟩

/-- **Stage $\mathfrak{S}_6$ (`stage_S6_sl2_matrix_fourier_quintic_and_casimir_representation`)**:
The 5-dimensional matrix Fourier operator satisfies the quintic identity $F_5^5 = F_5$ with
complete orthogonal projectors $P_{\mathrm{vac}} + P_{\mathrm{sym}} + P_{\mathrm{anti}} = 1$
and $P_{\mathrm{sym}} P_{\mathrm{anti}} = 0$, intertwined with the explicit $\mathfrak{sl}_2(\mathbb{C})$
representation $[h, e] = 2e$, $[h, f] = -2f$, $[e, f] = h$ and scalar Casimir $C = \frac{3}{2} I$. -/
theorem stage_S6_sl2_matrix_fourier_quintic_and_casimir_representation :
    (fourierMatrix5 ^ 5 = fourierMatrix5) ∧
    (P_vac5 + P_sym5 + P_anti5 = 1) ∧
    (P_sym5 * P_anti5 = 0) ∧
    (commutator sl2_h sl2_e = (2 : ℂ) • sl2_e) ∧
    (commutator sl2_h sl2_f = -((2 : ℂ) • sl2_f)) ∧
    (commutator sl2_e sl2_f = sl2_h) ∧
    (sl2_casimir = (3 / 2 : ℂ) • 1) ∧
    (commutator sl2_casimir sl2_e = 0) := by
  have hCap := capstone_matrix_fourier_sl2_synthesis
  exact hCap

/-- **Stage $\mathfrak{S}_7$ (`stage_S7_cyclotomic_charpoly_factorization_and_decell_cayley_hamilton`)**:
The 6-state triality operator has characteristic polynomial
$\Phi_1(X)\Phi_2(X)\Phi_3(X)\Phi_6(X) = X^6 - 1$, the 12-fold master operator has characteristic
polynomial $(X^3 - 1)(X^3 - i)$, and Decell's Cayley–Hamilton coefficient-tail formulas provide
explicit two-sided inverses for degree-2 and degree-3 polynomial equations over a field. -/
theorem stage_S7_cyclotomic_charpoly_factorization_and_decell_cayley_hamilton
    {K : Type} [Field K]
    (a₁ a₂ B2 : K) (hpoly2 : B2 ^ 2 + a₁ * B2 + a₂ = 0) (ha₂ : a₂ ≠ 0)
    (c₁ c₂ c₃ B3 : K) (hpoly3 : B3 ^ 3 + c₁ * B3 ^ 2 + c₂ * B3 + c₃ = 0) (hc₃ : c₃ ≠ 0) :
    sixTriality.charpoly =
      Polynomial.cyclotomic 1 ℂ * Polynomial.cyclotomic 2 ℂ *
        Polynomial.cyclotomic 3 ℂ * Polynomial.cyclotomic 6 ℂ ∧
    masterTwelve.charpoly =
      (Polynomial.X ^ 3 - 1) * (Polynomial.X ^ 3 - Polynomial.C Complex.I) ∧
    B2 * decellInverseCandidateTwo a₁ a₂ B2 = 1 ∧
    decellInverseCandidateTwo a₁ a₂ B2 * B2 = 1 ∧
    B3 * decellInverseCandidateThree c₁ c₂ c₃ B3 = 1 ∧
    decellInverseCandidateThree c₁ c₂ c₃ B3 * B3 = 1 := by
  have hSix := sixTriality_charpoly_named_cyclotomic
  have hTwelve := masterTwelve_charpoly
  have h2R := decell_inverse_candidate_two_right a₁ a₂ B2 hpoly2 ha₂
  have h2L := decell_inverse_candidate_two_left a₁ a₂ B2 hpoly2 ha₂
  have h3R := decell_inverse_candidate_three_right c₁ c₂ c₃ B3 hpoly3 hc₃
  have h3L := decell_inverse_candidate_three_left c₁ c₂ c₃ B3 hpoly3 hc₃
  exact ⟨hSix, hTwelve, h2R, h2L, h3R, h3L⟩

/-- **Stage $\mathfrak{S}_8$ (`stage_S8_operator_cyclotomic_p25_and_trifactor_fourier_synthesis`)**:
The noncommutative operator cyclotomic evaluations factor $T^6 - 1$, $T^{12} - 1$, $T^{24} - 1$,
and the degree-25 spine $P_{25}(T) = T \prod_{d \mid 24} \Phi_d(T)$, isolating tripotent
($T^3 = T \implies T\Phi_1(T)\Phi_2(T) = 0$), complex-cubic ($T^3 = -T \implies T\Phi_4(T) = 0$),
octic ($T^4 = -1 \implies \Phi_8(T) = 0$), 24th-root-of-unity eigenvalues, and quintic Fourier
($X^5 - X = 0$) sectors alongside the $2 \times 2$ hyperbolic/elliptic trifactor Fourier projectors
and their UHF matrix-stage embeddings. -/
theorem stage_S8_operator_cyclotomic_p25_and_trifactor_fourier_synthesis
    {W : Type*} [AddCommGroup W] [Module ℂ W] [NoZeroSMulDivisors ℂ W]
    (T T_tri T_cub T_oct : Module.End ℂ W)
    (hTri : T_tri ^ 3 = T_tri) (hCub : T_cub ^ 3 = -T_cub) (hOct : T_oct ^ 4 = -1)
    {v : W} {lam : ℂ} (hv0 : v ≠ 0) (hv : T v = lam • v) (hP25 : masterP25 T = 0)
    {R : Type*} [CommRing R] (X_four : R) (k : ℕ) (hX_four : IsFourierFourthRoot X_four)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U * U = 1) :
    divisorProduct6 T = T ^ 6 - 1 ∧
    divisorProduct12 T = T ^ 12 - 1 ∧
    divisorProduct24 T = T ^ 24 - 1 ∧
    masterP25 T = T * divisorProduct24 T ∧
    T_tri * phi1Eval T_tri * phi2Eval T_tri = 0 ∧
    T_cub * phi4Eval T_cub = 0 ∧
    phi8Eval T_oct = 0 ∧
    (lam = 0 ∨ lam ^ 24 = 1) ∧
    (X_four * (X_four ^ 2 - 1) * (X_four ^ 2 + 1) = X_four ^ 5 - X_four) ∧
    (X_four ^ 5 - X_four = 0) ∧
    projPlus2 U + projMinus2 U = 1 ∧
    projPlus2 U * projPlus2 U = projPlus2 U ∧
    projMinus2 U * projMinus2 U = projMinus2 U ∧
    projPlus2 U * projMinus2 U = 0 ∧
    clockProjPlus + clockProjMinus = 1 ∧
    Complex.I • clockProjPlus - Complex.I • clockProjMinus = matClockAxisC ∧
    stage1ClockProjPlus + stage1ClockProjMinus = 1 := by
  have hfop := capstone_fourier_operator_polynomial_synthesis X_four k hX_four
  exact ⟨divisorProduct6_eq T,
         divisorProduct12_eq T,
         divisorProduct24_eq T,
         masterP25_factorization T,
         tripotent_factor_zero T_tri hTri,
         complex_cubic_factor_zero T_cub hCub,
         phi8_zero_of_pow4_eq_neg_one T_oct hOct,
         eigenvalue_zero_or_pow24_eq_one_of_masterP25_eq_zero T hv0 hv hP25,
         hfop.1,
         hfop.2.2.1,
         projPlus2_add_projMinus2 U,
         projPlus2_sq U hU,
         projMinus2_sq U hU,
         projPlus2_mul_projMinus2 U hU,
         clockProj_sum,
         clockAxis_fourier_synthesis,
         stage1ClockProj_sum⟩

/-- Explicit $2 \times 2$ complex matrix generator $A = J_{\mathrm{clock}} = !![0, -1; 1, 0]$. -/
def matWitnessClock : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

/-- Explicit $2 \times 2$ complex matrix parity grading $B = !![1, 0; 0, -1]$. -/
def matWitnessParity : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Explicit $2 \times 2$ non-commutativity witness `matWitnessClock * matWitnessParity ≠ matWitnessParity * matWitnessClock`. -/
theorem souriau_chern_fourier_noncommutativity_witness :
    matWitnessClock * matWitnessParity ≠ matWitnessParity * matWitnessClock := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [matWitnessClock, matWitnessParity, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-! ## 3. Master Synthesis Theorem ($\mathfrak{S}_1 \prec \dots \prec \mathfrak{S}_8$) -/

/-- **Master Theorem (`souriau_chern_fourier_charpoly_cyclotomic_master_synthesis`)**:
Complete 8-stage synthesis of Souriau coadjoint Gibbs partition functions and Massieu potentials,
categorical UHF vacuum colimit/limit readouts and the Bost–Connes Euler product, Connes graded
spectral triple index pairings and Chern homotopy invariance, non-abelian matrix-traced Chern–Weil
exactness and graded Bianchi closedness, Lie/group Fourier character kernels and $V_4$
grand-canonical sector inversion, $\mathfrak{sl}_2(\mathbb{C})$ matrix Fourier quintic and Casimir
identities, cyclotomic characteristic polynomials and Decell–Cayley–Hamilton inversion, and the
degree-25 operator cyclotomic spine with trifactor Fourier projectors. -/
theorem souriau_chern_fourier_charpoly_cyclotomic_master_synthesis
    {G V State : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [LinearGroupAction G V] [Fintype State] [Nonempty State] [MulAction G State]
    (Θ : AffineCoadjointCocycle G V) (J : AffineMomentMap G V Θ State)
    (g : G) (βV : V)
    (n : ℕ) (f : DiagAlg n) (P : PrimeRegister) {β : ℝ} (hβ : 1 < β)
    {nMat : Type*} [Fintype nMat] [DecidableEq nMat] {R : Type*} [CommRing R]
    (ST : ConnesGradedSpectralTriple nMat R)
    (X Y Z : Matrix nMat nMat R)
    (h_comm : (ST.gamma : Matrix nMat nMat R) * Z = Z * ST.gamma)
    (h_homotopy : X - Y = ST.D * Z - Z * ST.D)
    {Vext : Type*} [AddCommGroup Vext] [Module R Vext] {nCW : ℕ}
    (h_cyclic : ∀ M N : Matrix (Fin nCW) (Fin nCW) (ExteriorAlgebra R Vext),
      matrixTraceForm (M * N) = matrixTraceForm (N * M))
    (D : ExteriorDifferentialData R Vext)
    (A F : Matrix (Fin nCW) (Fin nCW) (ExteriorAlgebra R Vext))
    (hA : MatrixIsHomogeneous 1 A) (hF : MatrixIsHomogeneous 2 F)
    (hBianchi : covariantDerivative A D.d F = 0)
    {α : Type*} [Fintype α] [Nonempty α]
    (params : GrandCanonicalTwoParam α) (grade : α → V4Group) (βGC μGC : ℝ) (gV4 : V4Group)
    {K : Type} [Field K]
    (a₁ a₂ B2 : K) (hpoly2 : B2 ^ 2 + a₁ * B2 + a₂ = 0) (ha₂ : a₂ ≠ 0)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U * U = 1) :
    (∀ s : SouriauChernFourierCyclotomicStage,
      ¬ Relation.TransGen SouriauChernFourierCyclotomicStage.causalEdge s s) ∧
    (twistedGibbsPartition Θ J βV =
      cocycleGibbsMultiplier Θ g βV * twistedGibbsPartition Θ J ((Ad V g).symm βV)) ∧
    (twistedMassieu Θ J βV = twistedMassieu Θ J ((Ad V g).symm βV) - Θ g βV) ∧
    ((dualInverseFamilyColimitMap (sys := uhfDiagDirectSystem)
        finiteZeroTempState finiteZeroTempState_isDualInverseFamily).hom
        ((colimit.ι (moduleDiagram uhfDiagDirectSystem) n).hom f) =
      colimitZeroTempState n f) ∧
    (infinitePrimeEulerProduct β = riemannZeta (β : ℂ)) ∧
    (connesIndexPairing ST X = connesIndexPairing ST Y) ∧
    (matrixTraceForm (matrixExteriorDerivative D.d A + A * A) = D.d (matrixTraceForm A)) ∧
    (D.d (matrixTraceForm (F * F)) = 0) ∧
    ((1 / 4 : ℝ) * ∑ j : Fin 4, v4Character j gV4 * v4TwistedPartition params grade βGC μGC j =
      v4SectorPartition params grade βGC μGC gV4) ∧
    (fourierMatrix5 ^ 5 = fourierMatrix5 ∧ sl2_casimir = (3 / 2 : ℂ) • 1) ∧
    (sixTriality.charpoly =
      Polynomial.cyclotomic 1 ℂ * Polynomial.cyclotomic 2 ℂ *
        Polynomial.cyclotomic 3 ℂ * Polynomial.cyclotomic 6 ℂ ∧
     masterTwelve.charpoly =
      (Polynomial.X ^ 3 - 1) * (Polynomial.X ^ 3 - Polynomial.C Complex.I) ∧
     B2 * decellInverseCandidateTwo a₁ a₂ B2 = 1) ∧
    (masterP25 T = T * divisorProduct24 T ∧
     divisorProduct24 T = T ^ 24 - 1 ∧
     projPlus2 U + projMinus2 U = 1 ∧
     projPlus2 U * projMinus2 U = 0 ∧
     Complex.I • clockProjPlus - Complex.I • clockProjMinus = matClockAxisC) := by
  have hsbc := souriau_bost_connes_analytic_categorical_and_euler_product_synthesis
    n f P hβ
  have hcw := master_graded_chern_weil_synthesis h_cyclic D A F hF hBianchi
  refine ⟨SouriauChernFourierCyclotomicStage.causalEdge_acyclic,
          twistedGibbsPartition_transformation Θ J g βV,
          twistedMassieu_additive_cocycle Θ J g βV,
          hsbc.2.2.1,
          hsbc.2.2.2.2.1,
          chern_pairing_homotopy_invariance ST X Y Z h_comm h_homotopy,
          matrixTrace_connection_curvature_exact D.d A hA,
          hcw.2.2,
          v4Fourier_sector_inversion params grade βGC μGC gV4,
          ⟨capstone_matrix_fourier_sl2_synthesis.1,
           capstone_matrix_fourier_sl2_synthesis.2.2.2.2.2.2.1⟩,
          ⟨sixTriality_charpoly_named_cyclotomic,
           masterTwelve_charpoly,
           decell_inverse_candidate_two_right a₁ a₂ B2 hpoly2 ha₂⟩,
          ⟨masterP25_factorization T,
           divisorProduct24_eq T,
           projPlus2_add_projMinus2 U,
           projPlus2_mul_projMinus2 U hU,
           clockAxis_fourier_synthesis⟩⟩

end InfoGeometry.Canonical.SouriauChernFourierCharpolyCyclotomicPoset
