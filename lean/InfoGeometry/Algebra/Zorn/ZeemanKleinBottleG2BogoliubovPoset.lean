/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.TetractysZeemanZornAssociatorBridge
import InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset
import InfoGeometry.Algebra.Zorn.SplitOctonionDerivationConjugation
import InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge
import InfoGeometry.Algebra.Zorn.SplitOctonionRindlerBoost
import InfoGeometry.Physics.BogoliubovWeylChemicalPotential

/-!
# Klein-Bottle Semidirect Quotient, Split-$G_2$ Derivation Equivariance, Rindler Mirror Boost,
  Bogoliubov–Weyl Cascade Poset ($\mathfrak{KB}_1 \prec \dots \prec \mathfrak{KB}_5$)

## i. Overview

This module formalizes the 5-stage **Klein-Bottle / Split-$G_2$ / Bogoliubov–Weyl Zorn Cascade Poset**
($\mathfrak{KB}_1 \prec \mathfrak{KB}_2 \prec \mathfrak{KB}_3 \prec \mathfrak{KB}_4 \prec \mathfrak{KB}_5$),
proving that the chiral gauge structure underlying the beta-gated Zorn cascade is the
**non-orientable Klein-bottle semidirect quotient** ($\tau \circ T_t \circ \tau^{-1} = T_{t^{-1}}$)
rather than an abelian Cartan 2-torus,
  extending the cascade to split-$G_2$ automorphisms/derivations,
continuous Rindler hyperbolic boosts, and the Bogoliubov–Weyl chemical-potential log-clock:

1. **Stage $\mathfrak{KB}_1$ (DeWitt Tetractys & $\mathcal{C}\ell(1,1)$ Non-Orientable Klein-Bottle Presentation):**
   In any associative ring `B` with a Peirce idempotent $P^2 = P$ and a normalized off-diagonal
   DeWitt bridge $\Phi = \mathrm{genPhi}(P, W, W)$ ($\Phi^2 = 1$), conjugation by $\Phi$ swaps
   the two Peirce sheets ($\Phi P \Phi = 1 - P$) and inverts both the Cartan grading
   $S_P = \mathrm{invS}(P)$ and the endogenous complex bivector $J = \mathrm{genJ}(P, W, W)$:
   $$\Phi S_P \Phi = -S_P, \qquad \Phi J \Phi = -J, \qquad S_P J S_P = -J.$$
   In $\mathrm{Mat}_2(K)$ (`KitaevABSCliffordExtensionMassDichotomyPoset.Mat2`), the adjoint
   involutions `kleinAdjointA`, `kleinAdjointB`, and `kleinAdjointAB` form the projective
   Klein four-group $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$ with orientation-reversing
   holonomy $\det(\sigma_z) = \det(\sigma_x) = -1$ and $\det(\sigma_z^2) = +1$.
2. **Stage $\mathfrak{KB}_2$ (Zorn Klein-Bottle Semidirect Quotient $\tau_{\mathrm{Klein}} \circ T_t
  = T_{t^{-1}} \circ \tau_{\mathrm{Klein}}$ & Refutation of Abelian Torus Commutativity):**
   On `CanonicalZorn` (`InfoGeometry.Canonical.ZornMatrix ℝ`), the orientation-reversing chiral
   involution `canonicalKleinSwap` and the 1-parameter subgroup `torusMap t` satisfy the exact
   Klein-bottle semidirect relation
   $$\tau_{\mathrm{Klein}}\big(\mathrm{torusMap}_t(X)\big)
  = \mathrm{torusMap}_{t^{-1}}\big(\tau_{\mathrm{Klein}}(X)\big).$$
   For $t = 2$ on the first upper chiral basis vector $U_0$,
   $\tau_{\mathrm{Klein}}(\mathrm{torusMap}_2(U_0)) \ne \mathrm{torusMap}_2(\tau_{\mathrm{Klein}}(U_0))$
   (since $2 \ne \frac{1}{2}$), refuting abelian torus commutativity. On the ungated Klein-bottle
   orbit, the chiral supertrace of `canonicalZornAssociator` cancels to zero, whereas beta-gating
   lifts to a single oriented Peirce sheet where `torusMap t` ($t \ne 0$) preserves the Nambu
   supertrace.
3. **Stage $\mathfrak{KB}_3$ (Continuous Rindler Hyperbolic Boost & Mirror Klein-Bottle Inversion on Split Octonions):**
   On the canonical split-octonion carrier (`InfoGeometry.Algebra.Zorn.SplitOctonionRindlerBoost`),
   the 1-parameter hyperbolic boost $\mathrm{splitOctonionBoost}(\eta)
  = \cosh(\eta)\,1 + \sinh(\eta)\,\ell$
   satisfies the 1-parameter group law $\mathrm{splitOctonionBoost}(s + t)
  = \mathrm{zMul}(\mathrm{splitOctonionBoost}(s), \mathrm{splitOctonionBoost}(t))$,
   and any mirror involution $J$ fixing $1$ and reversing $\ell$ ($J(\ell) = -\ell$) exchanges
   the two chiral Witt idempotents $\mathrm{chiralNull}_0(+1) \leftrightarrow \mathrm{chiralNull}_0(-1)$
   and inverts the boost parameter:
   $$J\big(\mathrm{splitOctonionBoost}(\eta)\big) = \mathrm{splitOctonionBoost}(-\eta).$$
4. **Stage $\mathfrak{KB}_4$ (Split-$G_2$ Automorphism Equivariance & Leibniz Derivation Transport of the Zorn Associator):**
   Every real split-octonion automorphism $\varphi \in \mathrm{RealSplitOctonionAut}$ preserves the
   ordered Zorn associator (`nativeAut_map_associator`),
  composes multiplicatively (`nativeAut_mul`),
   and transports native Zorn derivations injectively to Leibniz derivations on `CanonicalZorn`
   (`toCanonicalEnd_leibniz`, `toCanonicalEnd_bracket`).
5. **Stage $\mathfrak{KB}_5$ (Bogoliubov–Weyl Grand-Canonical Chemical-Potential Gauge & Master Synthesis):**
   Connects the Bogoliubov inertial/thermodynamic frame log-clock
   `frameWeylLogClock { F with θ := F.θ + δθ, μ
  := F.μ + δμ } = frameWeylLogClock F + δθ + F.β * δμ * F.Q`,
   charge shift `grandCanonicalRapidity_charge_shift`,
  non-vanishing Weyl gauge `frameWeylQ F ≠ 0`
   with Stages $\mathfrak{KB}_1 \prec \dots \prec \mathfrak{KB}_4$.

## ii. Three-Bucket Audit Classification

- **BUCKET 1 (Genuine Constructive Owner Declarations Kept & Proved):**
  - `ZeemanKleinBottleCascadeStage` ($\mathfrak{KB}_1 \prec \dots \prec \mathfrak{KB}_5$), `rank`,
  `coverEdge`, `instDecidableRelCoverEdge`, `rank_injective`, `coverEdge_rank_step`, `coverEdge_strictMono`, `coverEdge_acyclic`, `poset_covering_chain`
  - `dewitt_tetractys_klein_bottle_sheet_swap_and_inversion`,
  `kb1_dewitt_and_cl11_klein_bottle_nonorientable_holonomy`
  - `canonicalKleinSwap_torusMap_semidirect`, `klein_bottle_not_abelian_torus_witness`,
  `klein_bottle_orbit_associator_superTrace_cancel`, `kb2_zorn_klein_bottle_semidirect_quotient_and_orbit_cancellation`
  - `kb3_rindler_boost_klein_mirror_inversion_and_chiral_witt_swap`
  - `kb4_split_g2_automorphism_associator_and_leibniz_derivation_bridge`
  - `kb5_bogoliubov_weyl_chemical_potential_and_charge_gauge`,
  `kb5_master_klein_bottle_zorn_g2_bogoliubov_cascade_synthesis`
- **BUCKET 2 (Conditional Ring & Mirror Hypotheses):**
  - Ring-level theorems take explicit `hP : P * P = P`
  `hPhi : genPhi P W W * genPhi P W W
  = 1`; Rindler mirror theorems take explicit `hJ_one : J 1 = 1` and `hJ_l : J lUnit = -lUnit`.
- **BUCKET 3 (Open Closure Debt):**
  - None (`0` `sorry`, `0` `admit`, `0` custom axioms, `0` vacuous wrappers).

## iii. Key results

- `ZeemanKleinBottleCascadeStage` ($\mathfrak{KB}_1 \prec \dots \prec \mathfrak{KB}_5$)
- `kb1_dewitt_and_cl11_klein_bottle_nonorientable_holonomy`
- `klein_bottle_not_abelian_torus_witness`
- `kb2_zorn_klein_bottle_semidirect_quotient_and_orbit_cancellation`
- `kb3_rindler_boost_klein_mirror_inversion_and_chiral_witt_swap`
- `kb4_split_g2_automorphism_associator_and_leibniz_derivation_bridge`
- `kb5_master_klein_bottle_zorn_g2_bogoliubov_cascade_synthesis`

## iv. Table of contents

- Section 0: The 5-Stage Klein-Bottle / Split-$G_2$ / Bogoliubov Poset ($\mathfrak{KB}_1 \prec \dots \prec \mathfrak{KB}_5$)
- Section 1 ($\mathfrak{KB}_1$): DeWitt Tetractys & $\mathcal{C}\ell(1,1)$ Non-Orientable Klein-Bottle Presentation
- Section 2 ($\mathfrak{KB}_2$): Zorn Klein-Bottle Semidirect Quotient $\tau_{\mathrm{Klein}} \circ T_t = T_{t^{-1}} \circ \tau_{\mathrm{Klein}}$ & Non-Abelian Witness
- Section 3 ($\mathfrak{KB}_3$): Rindler Hyperbolic Boost & Mirror Klein-Bottle Inversion on Split Octonions
- Section 4 ($\mathfrak{KB}_4$): Split-$G_2$ Automorphism Equivariance & Leibniz Derivation Transport
- Section 5 ($\mathfrak{KB}_5$): Bogoliubov–Weyl Grand-Canonical Gauge & Master Synthesis
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.ZeemanKleinBottleG2BogoliubovPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra.Zorn.SplitIdempotentTorus
open InfoGeometry.Algebra.Zorn.ZeemanChiralGatedAssociatorPoset
open InfoGeometry.Algebra.Zorn.TetractysZeemanZornAssociatorBridge
open InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge
open InfoGeometry.Algebra.Zorn.SplitOctonionRindlerBoost
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Physics.SupergradedCuntzBdG
open InfoGeometry.Physics.BogoliubovWeylChemicalPotential
open InfoGeometry.Canonical

/-!
## Section 0: The 5-Stage Klein-Bottle / Split-$G_2$ / Bogoliubov Poset ($\mathfrak{KB}_1 \prec \dots \prec \mathfrak{KB}_5$)
-/

/-- The 5-stage causal poset governing the Klein-bottle semidirect quotient, Rindler mirror boost,
split-$G_2$ automorphism/derivation equivariance, and Bogoliubov–Weyl chemical-potential gauge. -/
inductive ZeemanKleinBottleCascadeStage : Type
  | kb1_cl11_dewitt_klein_bottle
  | kb2_zorn_klein_semidirect_quotient
  | kb3_rindler_mirror_boost_inversion
  | kb4_split_g2_derivation_transport
  | kb5_bogoliubov_weyl_cascade_synthesis
  deriving DecidableEq, Repr

namespace ZeemanKleinBottleCascadeStage

/-- Strict integer rank $\mathfrak{KB}_1 < \mathfrak{KB}_2 < \mathfrak{KB}_3 < \mathfrak{KB}_4 < \mathfrak{KB}_5$. -/
def rank : ZeemanKleinBottleCascadeStage → ℕ
  | .kb1_cl11_dewitt_klein_bottle => 1
  | .kb2_zorn_klein_semidirect_quotient => 2
  | .kb3_rindler_mirror_boost_inversion => 3
  | .kb4_split_g2_derivation_transport => 4
  | .kb5_bogoliubov_weyl_cascade_synthesis => 5

/-- Covering edges of the 5-stage Hasse chain $\mathfrak{KB}_1 \prec \dots \prec \mathfrak{KB}_5$. -/
def coverEdge : ZeemanKleinBottleCascadeStage → ZeemanKleinBottleCascadeStage → Prop
  | .kb1_cl11_dewitt_klein_bottle, .kb2_zorn_klein_semidirect_quotient => True
  | .kb2_zorn_klein_semidirect_quotient, .kb3_rindler_mirror_boost_inversion => True
  | .kb3_rindler_mirror_boost_inversion, .kb4_split_g2_derivation_transport => True
  | .kb4_split_g2_derivation_transport, .kb5_bogoliubov_weyl_cascade_synthesis => True
  | _, _ => False

/-- Decidability of `coverEdge`. -/
instance instDecidableRelCoverEdge : DecidableRel coverEdge := fun a b => by
  cases a <;> cases b <;> unfold coverEdge <;> infer_instance

/-- The stage rank map is strictly injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge advances `rank` by $1$. -/
theorem coverEdge_rank_step {a b : ZeemanKleinBottleCascadeStage} (h : coverEdge a b) :
    rank b = rank a + 1 := by
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge is strictly monotone in `rank`. -/
theorem coverEdge_strictMono {a b : ZeemanKleinBottleCascadeStage} (h : coverEdge a b) :
    rank a < rank b := by
  have hstep := coverEdge_rank_step h
  omega

/-- No stage covers itself. -/
theorem coverEdge_acyclic (a : ZeemanKleinBottleCascadeStage) : ¬ coverEdge a a := by
  intro h
  have hlt := coverEdge_strictMono h
  omega

/-- Complete 4-edge covering chain $\mathfrak{KB}_1 \prec \mathfrak{KB}_2 \prec \mathfrak{KB}_3 \prec \mathfrak{KB}_4 \prec \mathfrak{KB}_5$. -/
theorem poset_covering_chain :
    coverEdge .kb1_cl11_dewitt_klein_bottle .kb2_zorn_klein_semidirect_quotient ∧
    coverEdge .kb2_zorn_klein_semidirect_quotient .kb3_rindler_mirror_boost_inversion ∧
    coverEdge .kb3_rindler_mirror_boost_inversion .kb4_split_g2_derivation_transport ∧
    coverEdge .kb4_split_g2_derivation_transport .kb5_bogoliubov_weyl_cascade_synthesis := by
  decide

end ZeemanKleinBottleCascadeStage

/-!
## Section 1 ($\mathfrak{KB}_1$): DeWitt Tetractys & $\mathcal{C}\ell(1,1)$ Non-Orientable Klein-Bottle Presentation
-/

/-- **DeWitt Tetractys Klein-Bottle Sheet Swap & Grading Inversion:**
In any associative ring `B` with idempotent $P^2 = P$ and normalized DeWitt bridge
$\Phi = \mathrm{genPhi}(P, W, W)$ ($\Phi^2 = 1$), conjugation by $\Phi$ exchanges the two
Peirce sheets ($\Phi P \Phi = 1 - P$) and reverses the sign of both the Cartan grading
$S_P = \mathrm{invS}(P)$ ($\Phi S_P \Phi = -S_P$) and the complex bivector
$J = \mathrm{genJ}(P, W, W)$ ($\Phi J \Phi = -J$). -/
theorem dewitt_tetractys_klein_bottle_sheet_swap_and_inversion
    {B : Type*} [Ring B] {P W : B}
    (hP : P * P = P) (hPhi : genPhi P W W * genPhi P W W = 1) :
    genPhi P W W * P * genPhi P W W = 1 - P ∧
    genPhi P W W * invS P * genPhi P W W = -invS P ∧
    genPhi P W W * genJ P W W * genPhi P W W = -genJ P W W ∧
    invS P * genJ P W W * invS P = -genJ P W W := by
  have hUnif :=
    InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset.dewitt_tetractys_peirce_spine_unification
      P W hP hPhi
  have hPhiP : genPhi P W W * P = (1 - P) * genPhi P W W := by
    dsimp [genPhi]
    peirce_nf hP
  have hSheet : genPhi P W W * P * genPhi P W W = 1 - P := by
    calc
      genPhi P W W * P * genPhi P W W =
          (1 - P) * (genPhi P W W * genPhi P W W) := by
        rw [hPhiP, mul_assoc]
      _ = 1 - P := by rw [hPhi, mul_one]
  have hSInv : genPhi P W W * invS P * genPhi P W W = -invS P := by
    have hAnti : invS P * genPhi P W W + genPhi P W W * invS P = 0 := hUnif.2.2.1
    have hPhiS : genPhi P W W * invS P = -(invS P * genPhi P W W) :=
      eq_neg_of_add_eq_zero_right hAnti
    calc
      genPhi P W W * invS P * genPhi P W W =
          -(invS P * (genPhi P W W * genPhi P W W)) := by
        rw [hPhiS, neg_mul, mul_assoc]
      _ = -invS P := by rw [hPhi, mul_one]
  exact ⟨hSheet, hSInv, hUnif.2.2.2.2.2.2.1, hUnif.2.2.2.2.2.1⟩

/-- **Stage $\mathfrak{KB}_1$ Theorem:**
Combines the universal `[Ring B]` DeWitt Klein-bottle sheet swap and grading inversion with the
$\mathcal{C}\ell(1,1) \cong \mathrm{Mat}_2(K)$ projective Klein four-group $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$
and orientation-reversing determinant holonomy ($\det \sigma_z = \det \sigma_x
  = -1$, $\det(\sigma_z^2) = +1$). -/
theorem kb1_dewitt_and_cl11_klein_bottle_nonorientable_holonomy
    {B : Type*} [Ring B] {P W : B}
    (hP : P * P = P) (hPhi : genPhi P W W * genPhi P W W = 1)
    {K : Type*} [CommRing K] (X : Mat2 K) :
    (genPhi P W W * P * genPhi P W W = 1 - P ∧
     genPhi P W W * invS P * genPhi P W W = -invS P ∧
     genPhi P W W * genJ P W W * genPhi P W W = -genJ P W W ∧
     invS P * genJ P W W * invS P = -genJ P W W) ∧
    (Mat2.kleinAdjointA (Mat2.kleinAdjointA X) = X ∧
     Mat2.kleinAdjointB (Mat2.kleinAdjointB X) = X ∧
     Mat2.kleinAdjointA (Mat2.kleinAdjointB X) = Mat2.kleinAdjointAB X ∧
     Mat2.kleinAdjointB (Mat2.kleinAdjointA X) = Mat2.kleinAdjointAB X) ∧
    (Matrix.det (Mat2.sigmaZ : Mat2 K) = -1 ∧
     Matrix.det (Mat2.sigmaX : Mat2 K) = -1 ∧
     Matrix.det ((Mat2.sigmaZ : Mat2 K) * Mat2.sigmaZ) = 1) := by
  have hDW := dewitt_tetractys_klein_bottle_sheet_swap_and_inversion hP hPhi
  have hKL17 := Mat2.kl17_cl11_klein_four_group_adjoint_and_unorientable_holonomy X
  exact ⟨hDW,
    ⟨hKL17.2.1.1, hKL17.2.1.2.1, hKL17.2.1.2.2.2.1, hKL17.2.1.2.2.2.2⟩,
    ⟨hKL17.2.2.1, hKL17.2.2.2.1, hKL17.2.2.2.2.2⟩⟩

/-!
## Section 2 ($\mathfrak{KB}_2$): Zorn Klein-Bottle Semidirect Quotient $\tau_{\mathrm{Klein}} \circ T_t = T_{t^{-1}} \circ \tau_{\mathrm{Klein}}$ & Non-Abelian Witness
-/

local notation "CanonicalZorn" => InfoGeometry.Canonical.ZornMatrix ℝ
local notation "polePlus" => InfoGeometry.Canonical.ZornMatrix.zornPlus (R := ℝ)
local notation "poleMinus" => InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ)
local notation "U0" => InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0

/-- **Klein-Bottle Semidirect Commutation Law ($\tau_{\mathrm{Klein}} \circ T_t
  = T_{t^{-1}} \circ \tau_{\mathrm{Klein}}$):**
Interchanging `canonicalKleinSwap` and `torusMap t` inverts the parameter $t \mapsto t^{-1}$. -/
theorem canonicalKleinSwap_torusMap_semidirect (t : ℝ) (X : CanonicalZorn) :
    canonicalKleinSwap (torusMap t X) = torusMap t⁻¹ (canonicalKleinSwap X) := by
  have h := canonicalKleinSwap_torusMap_inversion t (canonicalKleinSwap X)
  rw [canonicalKleinSwap_involutive] at h
  exact h

/-- **Explicit Non-Abelian Klein-Bottle Quotient Witness:**
At $t = 2$ on the first upper chiral basis element $U_0$, `canonicalKleinSwap` and `torusMap 2`
do **not** commute:
$$\tau_{\mathrm{Klein}}\big(\mathrm{torusMap}_2(U_0)\big) \ne \mathrm{torusMap}_2\big(\tau_{\mathrm{Klein}}(U_0)\big),$$
proving that the chiral Zorn gauge group is the non-abelian **Klein-bottle semidirect quotient**
rather than a commutative 2-torus. -/
theorem klein_bottle_not_abelian_torus_witness :
    canonicalKleinSwap (torusMap 2 U0) ≠
      torusMap 2 (canonicalKleinSwap U0) := by
  intro h
  have hy0 : (canonicalKleinSwap (torusMap 2 U0)).y 0 =
      (torusMap 2 (canonicalKleinSwap U0)).y 0 :=
    congrFun (congrArg (fun W : CanonicalZorn => W.y) h) 0
  norm_num [canonicalKleinSwap, SplitIdempotentTorus.torusMap,
    InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
    Pi.single_apply, Matrix.cons_val_zero] at hy0

/-- **Klein-Bottle Orbit Cancellation vs. Single-Sheet Preservation:**
Along the ungated Klein-bottle glide-reflection pair
$\big([T_t U, T_t V, T_t W],\, \tau_{\mathrm{Klein}}([T_t U, T_t V, T_t W])\big)$,
the chiral supertrace cancels identically to zero, whereas on the beta-gated single sheet
`torusMap t` ($t \ne 0$) preserves `canonicalZornSuperTrace ([U, V, W])`. -/
theorem klein_bottle_orbit_associator_superTrace_cancel
    (t : ℝ) (ht : t ≠ 0) (U V W : CanonicalZorn) :
    canonicalZornSuperTrace
      (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W)) +
    canonicalZornSuperTrace
      (canonicalKleinSwap
        (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W))) = 0 ∧
    canonicalZornSuperTrace
      (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W)) =
      canonicalZornSuperTrace (canonicalZornAssociator U V W) := by
  have hflip :=
    canonicalZornSuperTrace_kleinSwap
      (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W))
  have hinv :=
    (torusMap_associator_diagonal_and_superTrace_invariant t ht U V W).2.2
  refine ⟨?_, hinv⟩
  rw [hflip, add_neg_cancel]

/-- **Stage $\mathfrak{KB}_2$ Theorem:**
Unifies the Klein-bottle pole swap, the semidirect inversion law
$\tau_{\mathrm{Klein}} \circ T_t = T_{t^{-1}} \circ \tau_{\mathrm{Klein}}$, the explicit
non-commutativity witness at $t = 2$, and the Klein-bottle orbit supertrace cancellation. -/
theorem kb2_zorn_klein_bottle_semidirect_quotient_and_orbit_cancellation
    (t : ℝ) (ht : t ≠ 0) (X U V W : CanonicalZorn) :
    (canonicalKleinSwap polePlus = poleMinus ∧
     canonicalKleinSwap poleMinus = polePlus) ∧
    canonicalKleinSwap (torusMap t X) = torusMap t⁻¹ (canonicalKleinSwap X) ∧
    canonicalKleinSwap (torusMap 2 U0) ≠ torusMap 2 (canonicalKleinSwap U0) ∧
    canonicalZornSuperTrace
      (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W)) +
    canonicalZornSuperTrace
      (canonicalKleinSwap
        (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W))) = 0 ∧
    canonicalZornSuperTrace
      (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W)) =
      canonicalZornSuperTrace (canonicalZornAssociator U V W) := by
  have hpoles := canonicalKleinSwap_exchanges_poles
  have hsemi := canonicalKleinSwap_torusMap_semidirect t X
  have horb := klein_bottle_orbit_associator_superTrace_cancel t ht U V W
  exact ⟨hpoles, hsemi, klein_bottle_not_abelian_torus_witness, horb.1, horb.2⟩

/-!
## Section 3 ($\mathfrak{KB}_3$): Rindler Hyperbolic Boost & Mirror Klein-Bottle Inversion on Split Octonions
-/

/-- **Stage $\mathfrak{KB}_3$ Theorem:**
On the canonical split-octonion carrier (`SplitOctonionRindlerBoost`), the 1-parameter hyperbolic
boost `splitOctonionBoost η` satisfies the additive group law
`splitOctonionBoost (s + t) = zMul (splitOctonionBoost s) (splitOctonionBoost t)`,
`zMul (splitOctonionBoost η) (splitOctonionBoost (-η)) = 1`, and any linear mirror involution
$J$ fixing $1$ and reversing $\ell$ ($J(\ell) = -\ell$) swaps the chiral Witt idempotents
$\mathrm{chiralNull}_0(+1) \leftrightarrow \mathrm{chiralNull}_0(-1)$ and inverts the boost
according to the continuous Klein-bottle law $J(\mathrm{splitOctonionBoost}(\eta))
  = \mathrm{splitOctonionBoost}(-\eta)$. -/
theorem kb3_rindler_boost_klein_mirror_inversion_and_chiral_witt_swap
    (J : InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ →ₗ[ℝ]
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ)
    (hJ_one : J 1 = 1) (hJ_l : J lUnit = -lUnit) (s t η : ℝ) :
    splitOctonionBoost (s + t) =
      zMul (splitOctonionBoost s) (splitOctonionBoost t) ∧
    zMul (splitOctonionBoost η) (splitOctonionBoost (-η)) = 1 ∧
    J (chiralNull ⟨0, by decide⟩ 1) = chiralNull ⟨0, by decide⟩ (-1) ∧
    J (chiralNull ⟨0, by decide⟩ (-1)) = chiralNull ⟨0, by decide⟩ 1 ∧
    J (splitOctonionBoost η) = splitOctonionBoost (-η) := by
  have hadd := splitOctonionBoost_add s t
  have hinv := splitOctonionBoost_neg_mul η
  have hmir := linearMirror_splitOctonionBoost_neg J hJ_one hJ_l η
  exact ⟨hadd,
    hinv,
    linearMirror_chiral_plus_to_minus J hJ_one hJ_l,
    linearMirror_chiral_minus_to_plus J hJ_one hJ_l,
    hmir⟩

/-!
## Section 4 ($\mathfrak{KB}_4$): Split-$G_2$ Automorphism Equivariance & Leibniz Derivation Transport
-/

/-- **Stage $\mathfrak{KB}_4$ Theorem:**
Every real split-octonion automorphism $\varphi \in \mathrm{RealSplitOctonionAut}$ preserves the
nonassociative Zorn associator (`nativeAut_map_associator`), composes multiplicatively
(`nativeAut_mul`), and every native Zorn derivation $D \in \mathrm{VectorDerivation}$ transports
injectively to a canonical Zorn Leibniz derivation satisfying both the nonassociative product rule
and commutator Lie bracket compatibility. -/
theorem kb4_split_g2_automorphism_associator_and_leibniz_derivation_bridge
    (φ ψ : RealSplitOctonionAut)
    (X Y Z : InfoGeometry.Algebra.ZornVectorMatrix ℝ)
    (D E : VectorDerivation) (U V : CanonicalZorn) :
    nativeAut φ (_root_.associator X Y Z) =
      _root_.associator (nativeAut φ X) (nativeAut φ Y) (nativeAut φ Z) ∧
    nativeAut (φ * ψ) = nativeAut φ * nativeAut ψ ∧
    toCanonicalEnd D (U * V) = toCanonicalEnd D U * V + U * toCanonicalEnd D V ∧
    toCanonicalEnd (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket D E) =
      toCanonicalEnd D * toCanonicalEnd E - toCanonicalEnd E * toCanonicalEnd D ∧
    Function.Injective canonicalDerivationLieHom := by
  have hassoc := nativeAut_map_associator φ X Y Z
  have hmul := nativeAut_mul φ ψ
  have hleib := toCanonicalEnd_leibniz D U V
  have hbrack := toCanonicalEnd_bracket D E
  exact ⟨hassoc, hmul, hleib, hbrack, canonicalDerivationLieHom_injective⟩

/-!
## Section 5 ($\mathfrak{KB}_5$): Bogoliubov–Weyl Grand-Canonical Gauge & Master Synthesis
-/

/-- **Stage $\mathfrak{KB}_5$ Theorem:**
In a Bogoliubov inertial/thermodynamic frame `F : BogoliubovInertialFrame`, the Weyl log-clock
equals the log of the positive real Weyl scale, generates a non-vanishing complex $q$-gauge
`frameWeylQ F ≠ 0`, and shifts linearly under simultaneous inertial-rapidity ($\delta\theta$),
chemical-potential ($\delta\mu$), and charge ($\delta Q$) variations. -/
theorem kb5_bogoliubov_weyl_chemical_potential_and_charge_gauge
    (F : BogoliubovInertialFrame) (δθ δμ δQ : ℝ) :
    logScaleParam (frameWeylRealScale F) = frameWeylLogClock F ∧
    frameWeylQ F = qRapidity (frameWeylLogClock F) ∧
    frameWeylQ F ≠ 0 ∧
    frameWeylLogClock { F with θ := F.θ + δθ, μ := F.μ + δμ } =
      frameWeylLogClock F + δθ + F.β * δμ * F.Q ∧
    grandCanonicalRapidity F.β F.E F.μ (F.Q + δQ) =
      grandCanonicalRapidity F.β F.E F.μ F.Q + F.β * F.μ * δQ := by
  have hlog := frame_logScale_eq_logClock F
  have hq := frameWeylQ_eq_qRapidity_logClock F
  have hshift := frameWeylLogClock_theta_mu_shift F δθ δμ
  have hcharge := grandCanonicalRapidity_charge_shift F.β F.E F.μ F.Q δQ
  exact ⟨hlog, hq, frameWeylQ_ne_zero F, hshift, hcharge⟩

/-- **Master Klein-Bottle / Split-$G_2$ / Bogoliubov–Weyl Zorn Cascade Synthesis ($\mathfrak{KB}_1 \prec \dots \prec \mathfrak{KB}_5$):**
Unifies all five stages of the non-orientable Klein-bottle Zorn cascade:
1. ($\mathfrak{KB}_1$) DeWitt Tetractys Klein-bottle sheet swap $\Phi P \Phi
  = 1 - P$
  grading inversion $\Phi S_P \Phi = -S_P$;
2. ($\mathfrak{KB}_2$) Zorn Klein-bottle semidirect quotient $\tau_{\mathrm{Klein}} \circ T_t
  = T_{t^{-1}} \circ \tau_{\mathrm{Klein}}$, explicit $t = 2$ non-commutativity witness, and orbit supertrace cancellation;
3. ($\mathfrak{KB}_3$) Rindler hyperbolic boost mirror inversion $J(\mathrm{splitOctonionBoost}(\eta)) = \mathrm{splitOctonionBoost}(-\eta)$;
4. ($\mathfrak{KB}_4$) Split-$G_2$ automorphism equivariance of the Zorn associator
  Leibniz derivation transport;
5. ($\mathfrak{KB}_5$) Bogoliubov–Weyl chemical-potential and inertial-rapidity gauge shift. -/
theorem kb5_master_klein_bottle_zorn_g2_bogoliubov_cascade_synthesis
    {B : Type*} [Ring B] {P W : B}
    (hP : P * P = P) (hPhi : genPhi P W W * genPhi P W W = 1)
    (t : ℝ) (ht : t ≠ 0) (U V Z : CanonicalZorn)
    (J : InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ →ₗ[ℝ]
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ)
    (hJ_one : J 1 = 1) (hJ_l : J lUnit = -lUnit) (η : ℝ)
    (φ : RealSplitOctonionAut) (X₁ X₂ X₃ : InfoGeometry.Algebra.ZornVectorMatrix ℝ)
    (D : VectorDerivation)
    (F : BogoliubovInertialFrame) (δθ δμ : ℝ) :
    (ZeemanKleinBottleCascadeStage.coverEdge .kb1_cl11_dewitt_klein_bottle .kb2_zorn_klein_semidirect_quotient ∧
     ZeemanKleinBottleCascadeStage.coverEdge .kb2_zorn_klein_semidirect_quotient .kb3_rindler_mirror_boost_inversion ∧
     ZeemanKleinBottleCascadeStage.coverEdge .kb3_rindler_mirror_boost_inversion .kb4_split_g2_derivation_transport ∧
     ZeemanKleinBottleCascadeStage.coverEdge .kb4_split_g2_derivation_transport .kb5_bogoliubov_weyl_cascade_synthesis) ∧
    (genPhi P W W * P * genPhi P W W = 1 - P ∧
     genPhi P W W * invS P * genPhi P W W = -invS P) ∧
    (canonicalKleinSwap (torusMap t U) = torusMap t⁻¹ (canonicalKleinSwap U) ∧
     canonicalKleinSwap (torusMap 2 U0) ≠ torusMap 2 (canonicalKleinSwap U0) ∧
     canonicalZornSuperTrace
       (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t Z)) +
     canonicalZornSuperTrace
       (canonicalKleinSwap
         (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t Z))) = 0) ∧
    (J (splitOctonionBoost η) = splitOctonionBoost (-η) ∧
     zMul (splitOctonionBoost η) (splitOctonionBoost (-η)) = 1) ∧
    (nativeAut φ (_root_.associator X₁ X₂ X₃) =
       _root_.associator (nativeAut φ X₁) (nativeAut φ X₂) (nativeAut φ X₃) ∧
     toCanonicalEnd D (U * V) = toCanonicalEnd D U * V + U * toCanonicalEnd D V) ∧
    (frameWeylQ F ≠ 0 ∧
     frameWeylLogClock { F with θ := F.θ + δθ, μ := F.μ + δμ } =
       frameWeylLogClock F + δθ + F.β * δμ * F.Q) := by
  have hposet := ZeemanKleinBottleCascadeStage.poset_covering_chain
  have hdw := dewitt_tetractys_klein_bottle_sheet_swap_and_inversion hP hPhi
  have hkb2 := kb2_zorn_klein_bottle_semidirect_quotient_and_orbit_cancellation t ht U U V Z
  have hkb3 := kb3_rindler_boost_klein_mirror_inversion_and_chiral_witt_swap J hJ_one hJ_l η (-η) η
  have hkb4
  := kb4_split_g2_automorphism_associator_and_leibniz_derivation_bridge φ φ X₁ X₂ X₃ D D U V
  have hkb5 := kb5_bogoliubov_weyl_chemical_potential_and_charge_gauge F δθ δμ 0
  exact ⟨hposet,
    ⟨hdw.1, hdw.2.1⟩,
    ⟨hkb2.2.1, hkb2.2.2.1, hkb2.2.2.2.1⟩,
    ⟨hkb3.2.2.2.2, hkb3.2.1⟩,
    ⟨hkb4.1, hkb4.2.2.1⟩,
    ⟨hkb5.2.2.1, hkb5.2.2.2.1⟩⟩

end InfoGeometry.Algebra.Zorn.ZeemanKleinBottleG2BogoliubovPoset
