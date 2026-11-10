/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NoncommutativeZornNambuAssociator
import InfoGeometry.Algebra.ChiralZornBasisSoldering
import InfoGeometry.Algebra.SteinbergMoebiusProjectiveLine
import InfoGeometry.Algebra.Zorn.SplitIdempotentTorus
import InfoGeometry.Algebra.Zorn.QuadraticCayleyDomain

/-!
# Zeeman Cartan Gauge, Chiral Beta-Gating Cut, Racemic Cancellation,
  the Zorn Associator–Cayley Poset ($\mathfrak{ZG}_1 \prec \dots \prec \mathfrak{ZG}_5$)

## i. Overview

This module formalizes the constructive algebraic spine deconfabulating the
5-stage **Zeeman-Gated Zorn Cascade Poset** ($\mathfrak{ZG}_1 \prec \mathfrak{ZG}_2 \prec \mathfrak{ZG}_3 \prec \mathfrak{ZG}_4 \prec \mathfrak{ZG}_5$).
Every vacuous `Prop`-witness field from the exploratory intake is eliminated and
replaced by kernel-checked theorems over the repository's native Zorn and Peirce
operator carriers (`ZornNC R`, `SplitZornC`, `InfoGeometry.Canonical.ZornMatrix ℝ`,
`SplitCarrier`, and `PureNonCommutativeOperatorSpine`):

1. **Stage $\mathfrak{ZG}_1$ (Cartan Torus Gauge & Chiral Pole Decomposition):**
   In `SplitZornC` (`InfoGeometry.Algebra.ChiralZornBasisSoldering`), the hyperbolic grading
   operator `chiralL = chiralUPlus - chiralUMinus` satisfies `chiralL * chiralL = chiralOne`
   and reconstructs the complementary chiral idempotents `chiralUPlus` (`E11`) and
   `chiralUMinus` (`E22`). In `InfoGeometry.Algebra.Zorn.SplitIdempotentTorus`, the 1-parameter
   real split Cartan torus `torusMap t` fixes both diagonal Peirce poles (`polePlus`, `poleMinus`)
   while acting as an algebra automorphism of the full nonassociative Zorn product for every
   $t \ne 0$.
2. **Stage $\mathfrak{ZG}_2$ (Chiral Beta-Gating Idempotent Projections on `ZornNC R`):**
   Defines the upper and lower chiral sector projections `chiralUpperProj` and `chiralLowerProj`
   on the noncommutative Zorn carrier `ZornNC R` over an arbitrary associative ring `R`,
   establishing idempotency ($P_+^2 = P_+$, $P_-^2 = P_-$), mutual orthogonality
   ($P_+ \circ P_- = 0$, $P_- \circ P_+ = 0$), Hodge parity conjugation
   ($\mathrm{swap} \circ P_+ = P_- \circ \mathrm{swap}$), and exact selection of the pure upper
   and lower vector cones from a symmetric state `psiCov a p`.
3. **Stage $\mathfrak{ZG}_3$ (Ungated Racemic Cancellation vs. Chiral-Gated Nambu Associator Volume):**
   Proves why an ungated (parity-symmetric / racemic) ensemble has zero diagonal Zorn associator
   readout while chiral gating exposes the cubic Nambu volume:
   - For any Hodge-symmetric state (`hodgeSectorSwap A = A`, including every covariant state
     `psiCov a p`), both diagonal entries and the diagonal supertrace of the self-associator
     `associator A A A` vanish identically.
   - For *every* state `A : ZornNC R`, the parity-paired ensemble sum of `associator A A A` and
     its Hodge partner `associator (hodgeSectorSwap A) (hodgeSectorSwap A) (hodgeSectorSwap A)`
     has identically zero diagonal components and zero supertrace.
   - After applying the chiral projection `chiralUpperProj` to `psiCov a p`, the self-associator
     equals `⟨nambu p, 0, 0, -nambu p⟩` with `superTrace = 2 * nambu p`.
   - Exhibits a concrete noncommutative $2 \times 2$ integer matrix witness (`ChiralNambuMatrixWitness`)
     where the ungated racemic state has zero diagonal associator while the chiral-gated state has
     non-vanishing diagonal Nambu associator `!![2, 0; 0, 1] ≠ 0`.
4. **Stage $\mathfrak{ZG}_4$ (Projective Cross-Ratio & Klein-Bottle Quotient Semidirect Twist on the Associator Readout):**
   Connects the noncommutative operator cross-ratio (`PureNonCommutativeOperatorSpine.operatorCrossRatio`)
   shift
  Peirce-cone conjugation invariances with the **Klein-bottle semidirect quotient** on `CanonicalZorn`:
   the orientation-reversing chiral swap `canonicalKleinSwap` exchanges the two Peirce poles (`polePlus ↔ poleMinus`),
   inverts the 1-parameter subgroup `torusMap t` via the Klein-bottle glide-reflection law
   $$\tau_{\mathrm{Klein}}\big(\mathrm{torusMap}_t(\tau_{\mathrm{Klein}}(X))\big)
  = \mathrm{torusMap}_{t^{-1}}(X),$$

  flips the sign of `canonicalZornSuperTrace`,
  whereas on a single chiral-gated sheet `torusMap t` ($t \ne 0$)
   preserves both diagonal entries and the chiral supertrace of `canonicalZornAssociator`.
5. **Stage $\mathfrak{ZG}_5$ (Native Zorn Cayley Transform & Chiral Polarization Equivalence):**
   On the regular locus `CayleyRegular (diagonal a b)` ($a + 1 \ne 0 \land b + 1 \ne 0$) of
   `InfoGeometry.Algebra.Zorn.QuadraticCayleyDomain`, the native Zorn Cayley transform
   `nativeCayley (diagonal a b)` has chiral supertrace asymmetry
   $$\mathrm{superTrace}\big(\mathcal{C}(\mathrm{diag}(a, b))\big)
     = \frac{a - 1}{a + 1} - \frac{b - 1}{b + 1}
     = \frac{2(a - b)}{(a + 1)(b + 1)},$$
   which vanishes if and only if the diagonal Cartan state is unpolarized ($a = b$).

## ii. Three-Bucket Audit Classification

- **BUCKET 1 (Genuine Constructive Owner Declarations Kept & Proved):**
  - `ZeemanChiralCascadeStage` ($\mathfrak{ZG}_1 \prec \dots \prec \mathfrak{ZG}_5$), `rank`,
  `coverEdge`, `instDecidableRelCoverEdge`, `rank_injective`, `coverEdge_rank_step`, `coverEdge_strictMono`, `coverEdge_acyclic`, `poset_covering_chain`
  - `zg1_cartan_chiral_soldering_and_split_torus_stabilizer`
  - `chiralUpperProj`, `chiralLowerProj`, `chiralVectorProj`, `chiralUpperProj_idem`,
  `chiralLowerProj_idem`, `chiralUpperProj_chiralLowerProj`, `chiralLowerProj_chiralUpperProj`, `hodgeSectorSwap_chiralUpperProj`, `hodgeSectorSwap_chiralLowerProj`, `chiralVectorProj_eq`, `chiralProj_psiCov_pair`, `zg2_chiral_cut_projections_idempotent_orthogonal_and_hodge_dual`
  - `superTrace_self_associator`, `racemic_equal_sectors_self_associator_diagonal_zero`,
  `psiCov_ungated_self_associator_diagonal_zero`, `ungated_parity_pair_self_associator_cancel`, `chiralGated_psiCov_self_associator`, `chiralLowerGated_psiCov_self_associator`, `zg3_racemic_associator_cancellation_and_chiral_nambu_activation`
  - `ChiralNambuMatrixWitness.pChiral`, `nambu_pChiral_diagonal_entries`, `nambu_pChiral_ne_zero`,
  `superTrace_chiralGated_pChiral_ne_zero`, `zg3_concrete_matrix_witness_racemic_zero_vs_chiral_nonzero`
  - `canonicalZornAssociator`, `canonicalZornSuperTrace`, `canonicalKleinSwap`,
  `canonicalKleinSwap_involutive`, `canonicalKleinSwap_exchanges_poles`, `canonicalKleinSwap_torusMap_inversion`, `canonicalZornSuperTrace_kleinSwap`, `torusMap_sub`, `torusMap_canonicalZornAssociator`, `torusMap_associator_diagonal_and_superTrace_invariant`, `zg4_cross_ratio_and_split_torus_associator_diagonal_invariance`
  - `zornChiralSuperTrace`, `zornChiralSuperTrace_diagonal`,
  `nativeCayley_diagonal_chiralSuperTrace`, `nativeCayley_diagonal_chiralSuperTrace_eq_zero_iff`, `zg5_native_cayley_chiral_supertrace_asymmetry_and_polarization_iff`, `zg5_master_zeeman_chiral_gated_zorn_cascade_synthesis`
- **BUCKET 2 (Replaced / Upgraded Surfaces):**
  - Replaced the intake's proposed vacuous `ZeemanGatedZornCascadePacket` (`zeemanIsCartanGaugeWitness : Prop`, `betaActsAsChiralCutWitness : Prop`, `volumeRequiresGatingWitness : Prop`) with constructive, hypothesis-explicit theorems over `ZornNC R`, `SplitZornC`, `CanonicalZorn`, and `SplitCarrier`.
- **BUCKET 3 (Eliminated Vacuous Wrappers):**
  - Eliminated `ZeemanGatedZornCascadeTarget : Prop
  := Nonempty (ZeemanGatedZornCascadePacket V A)`
  `zeemanGatedZornCascadeTarget_holds (P) : ⟨P⟩` (`0` `Prop` witness fields, `0` `Nonempty` packet wrappers).

## iii. Key results

- `ZeemanChiralCascadeStage` ($\mathfrak{ZG}_1 \prec \dots \prec \mathfrak{ZG}_5$), `rank_injective`,
  `coverEdge_strictMono`, `coverEdge_acyclic`
- `zg1_cartan_chiral_soldering_and_split_torus_stabilizer`
- `zg2_chiral_cut_projections_idempotent_orthogonal_and_hodge_dual`
- `zg3_racemic_associator_cancellation_and_chiral_nambu_activation`
- `zg3_concrete_matrix_witness_racemic_zero_vs_chiral_nonzero`
- `zg4_cross_ratio_and_split_torus_associator_diagonal_invariance`
- `zg5_native_cayley_chiral_supertrace_asymmetry_and_polarization_iff`
- `zg5_master_zeeman_chiral_gated_zorn_cascade_synthesis`

## iv. Table of contents

- Section 0: The 5-Stage Zeeman Chiral-Gated Zorn Poset ($\mathfrak{ZG}_1 \prec \dots \prec \mathfrak{ZG}_5$)
- Section 1 ($\mathfrak{ZG}_1$): Cartan Torus Gauge & Chiral Pole Decomposition
- Section 2 ($\mathfrak{ZG}_2$): Chiral Beta-Gating Idempotent Projections on `ZornNC R`
- Section 3 ($\mathfrak{ZG}_3$): Ungated Racemic Cancellation vs. Chiral-Gated Nambu Associator Volume
- Section 4 ($\mathfrak{ZG}_4$): Operator Cross-Ratio & Split-Torus Invariance of the Zorn Associator Readout
- Section 5 ($\mathfrak{ZG}_5$): Native Zorn Cayley Transform Chiral Asymmetry & Master Synthesis
- Section 6: Klein–Nishina Coincidence Cross-Ratio, Cayley Derivation Coordinates,
  & the 5-Node $^{60}\text{Co}$ / $^{60}\text{Ni}^*$ Zorn Cascade Time-Reversal Anomaly
- Section 7: Peirce Error-Correction, Scalar Identity Noise Invariance, Coplanar Crosstalk Rejection,
  & $\mathrm{SL}(3)$ Scaling Invariance
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.ZeemanChiralGatedAssociatorPoset

open InfoGeometry.Algebra
open InfoGeometry.Algebra.NoncommutativeZornNambu
open InfoGeometry.Algebra.Zorn.SplitIdempotentTorus
open InfoGeometry.Algebra.Zorn.QuadraticCayleyDomain
open PureNonCommutativeOperatorSpine

/-!
## Section 0: The 5-Stage Zeeman Chiral-Gated Zorn Poset ($\mathfrak{ZG}_1 \prec \dots \prec \mathfrak{ZG}_5$)
-/

/-- The 5-stage causal poset governing the Zeeman Cartan gauge, chiral beta-cut
projection, racemic vs. gated Nambu associator volume, projective/torus invariance,
and the native Zorn Cayley chiral readout. -/
inductive ZeemanChiralCascadeStage : Type
  | zg1_cartan_zeeman_gauge
  | zg2_chiral_beta_cut
  | zg3_nambu_associator_gating
  | zg4_cross_ratio_torus_invariance
  | zg5_cayley_chiral_readout
  deriving DecidableEq, Repr

namespace ZeemanChiralCascadeStage

/-- Monotone integer rank embedding $\mathfrak{ZG}_1 < \mathfrak{ZG}_2 < \mathfrak{ZG}_3 < \mathfrak{ZG}_4 < \mathfrak{ZG}_5$. -/
def rank : ZeemanChiralCascadeStage → ℕ
  | .zg1_cartan_zeeman_gauge => 1
  | .zg2_chiral_beta_cut => 2
  | .zg3_nambu_associator_gating => 3
  | .zg4_cross_ratio_torus_invariance => 4
  | .zg5_cayley_chiral_readout => 5

/-- Covering edges of the 5-stage Hasse chain $\mathfrak{ZG}_1 \prec \dots \prec \mathfrak{ZG}_5$. -/
def coverEdge : ZeemanChiralCascadeStage → ZeemanChiralCascadeStage → Prop
  | .zg1_cartan_zeeman_gauge, .zg2_chiral_beta_cut => True
  | .zg2_chiral_beta_cut, .zg3_nambu_associator_gating => True
  | .zg3_nambu_associator_gating, .zg4_cross_ratio_torus_invariance => True
  | .zg4_cross_ratio_torus_invariance, .zg5_cayley_chiral_readout => True
  | _, _ => False

/-- Decidability of the covering relation `coverEdge`. -/
instance instDecidableRelCoverEdge : DecidableRel coverEdge := fun a b => by
  cases a <;> cases b <;> unfold coverEdge <;> infer_instance

/-- The stage rank map is strictly injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge advances the stage rank by exactly $1$. -/
theorem coverEdge_rank_step {a b : ZeemanChiralCascadeStage} (h : coverEdge a b) :
    rank b = rank a + 1 := by
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge is strictly monotone in `rank`. -/
theorem coverEdge_strictMono {a b : ZeemanChiralCascadeStage} (h : coverEdge a b) :
    rank a < rank b := by
  have hstep := coverEdge_rank_step h
  omega

/-- No stage covers itself (irreflexivity / 1-step acyclicity). -/
theorem coverEdge_acyclic (a : ZeemanChiralCascadeStage) : ¬ coverEdge a a := by
  intro h
  have hlt := coverEdge_strictMono h
  omega

/-- Complete 4-edge covering spine $\mathfrak{ZG}_1 \prec \mathfrak{ZG}_2 \prec \mathfrak{ZG}_3 \prec \mathfrak{ZG}_4 \prec \mathfrak{ZG}_5$. -/
theorem poset_covering_chain :
    coverEdge .zg1_cartan_zeeman_gauge .zg2_chiral_beta_cut ∧
    coverEdge .zg2_chiral_beta_cut .zg3_nambu_associator_gating ∧
    coverEdge .zg3_nambu_associator_gating .zg4_cross_ratio_torus_invariance ∧
    coverEdge .zg4_cross_ratio_torus_invariance .zg5_cayley_chiral_readout := by
  decide

end ZeemanChiralCascadeStage

/-!
## Section 1 ($\mathfrak{ZG}_1$): Cartan Torus Gauge & Chiral Pole Decomposition
-/

local notation "CanonicalZorn" => InfoGeometry.Canonical.ZornMatrix ℝ
local notation "polePlus" => InfoGeometry.Canonical.ZornMatrix.zornPlus (R := ℝ)
local notation "poleMinus" => InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ)

/-- **Stage $\mathfrak{ZG}_1$ Theorem:**
In the split Zorn algebra, the hyperbolic Cartan grading element `chiralL
  = chiralUPlus - chiralUMinus`
squares to `chiralOne`, the chiral poles `chiralUPlus` and `chiralUMinus` sum to `chiralOne` and
are reconstructed by $\frac{1}{2}(1 \pm \ell)$, and the 1-parameter real split Cartan torus
`torusMap t` fixes both diagonal Peirce poles while preserving the full nonassociative Zorn
product for every $t \ne 0$. -/
theorem zg1_cartan_chiral_soldering_and_split_torus_stabilizer
    (t : ℝ) (ht : t ≠ 0) (X Y : CanonicalZorn) :
    chiralUPlus + chiralUMinus = chiralOne ∧
    chiralL = chiralUPlus - chiralUMinus ∧
    chiralL * chiralL = chiralOne ∧
    chiralUPlus = (1 / 2 : ℂ) • (chiralOne + chiralL) ∧
    chiralUMinus = (1 / 2 : ℂ) • (chiralOne - chiralL) ∧
    (torusMap t polePlus = polePlus ∧ torusMap t poleMinus = poleMinus) ∧
    torusMap t (X * Y) = torusMap t X * torusMap t Y := by
  have hpoles := torusMap_fixes_poles t
  have hmul := torusMap_mul t ht X Y
  exact ⟨chiral_diagonal_soldering,
    chiralL_difference,
    chiralL_sq,
    chiralUPlus_reconstruction,
    chiralUMinus_reconstruction,
    hpoles,
    hmul⟩

/-!
## Section 2 ($\mathfrak{ZG}_2$): Chiral Beta-Gating Idempotent Projections on `ZornNC R`
-/

section ChiralBetaGating

variable {R : Type*} [Ring R]

/-- The zero element of the four-sector noncommutative Zorn carrier `ZornNC R`. -/
def zeroZornNC : ZornNC R := ⟨0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 0⟩

/-- Upper chiral beta-gating projection $P_+(A) = \mathrm{pureUpper}(A.x) = (0, A.x, 0, 0)$,
corresponding to the Peirce off-diagonal selection $E_{11} A E_{22}$. -/
def chiralUpperProj (A : ZornNC R) : ZornNC R :=
  pureUpper A.x

/-- Lower chiral gating projection $P_-(A) = \mathrm{pureLower}(A.y) = (0, 0, A.y, 0)$,
corresponding to the complementary Peirce off-diagonal selection $E_{22} A E_{11}$. -/
def chiralLowerProj (A : ZornNC R) : ZornNC R :=
  pureLower A.y

/-- Pure vector-sector projection $P_{\mathrm{vec}}(A) = P_+(A) + P_-(A) = (0, A.x, A.y, 0)$. -/
def chiralVectorProj (A : ZornNC R) : ZornNC R :=
  add (chiralUpperProj A) (chiralLowerProj A)

/-- Upper chiral projection is strictly idempotent: $P_+(P_+(A)) = P_+(A)$. -/
@[simp] theorem chiralUpperProj_idem (A : ZornNC R) :
    chiralUpperProj (chiralUpperProj A) = chiralUpperProj A := by
  cases A
  simp [chiralUpperProj, pureUpper]

/-- Lower chiral projection is strictly idempotent: $P_-(P_-(A)) = P_-(A)$. -/
@[simp] theorem chiralLowerProj_idem (A : ZornNC R) :
    chiralLowerProj (chiralLowerProj A) = chiralLowerProj A := by
  cases A
  simp [chiralLowerProj, pureLower]

/-- Upper and lower chiral projections are mutually orthogonal: $P_+(P_-(A)) = 0$. -/
@[simp] theorem chiralUpperProj_chiralLowerProj (A : ZornNC R) :
    chiralUpperProj (chiralLowerProj A) = (zeroZornNC : ZornNC R) := by
  cases A
  simp [chiralUpperProj, chiralLowerProj, pureUpper, pureLower, zeroZornNC]

/-- Lower and upper chiral projections are mutually orthogonal: $P_-(P_+(A)) = 0$. -/
@[simp] theorem chiralLowerProj_chiralUpperProj (A : ZornNC R) :
    chiralLowerProj (chiralUpperProj A) = (zeroZornNC : ZornNC R) := by
  cases A
  simp [chiralUpperProj, chiralLowerProj, pureUpper, pureLower, zeroZornNC]

/-- The Hodge parity swap conjugates the upper chiral projection into the lower chiral projection:
$\mathrm{swap}(P_+(A)) = P_-(\mathrm{swap}(A))$. -/
theorem hodgeSectorSwap_chiralUpperProj (A : ZornNC R) :
    hodgeSectorSwap (chiralUpperProj A) = chiralLowerProj (hodgeSectorSwap A) := by
  cases A
  simp [hodgeSectorSwap, chiralUpperProj, chiralLowerProj, pureUpper, pureLower]

/-- The Hodge parity swap conjugates the lower chiral projection into the upper chiral projection:
$\mathrm{swap}(P_-(A)) = P_+(\mathrm{swap}(A))$. -/
theorem hodgeSectorSwap_chiralLowerProj (A : ZornNC R) :
    hodgeSectorSwap (chiralLowerProj A) = chiralUpperProj (hodgeSectorSwap A) := by
  cases A
  simp [hodgeSectorSwap, chiralUpperProj, chiralLowerProj, pureUpper, pureLower]

/-- The sum of the two chiral projections reconstructs both off-diagonal vector sectors. -/
theorem chiralVectorProj_eq (A : ZornNC R) :
    chiralVectorProj A = ⟨0, A.x, A.y, 0⟩ := by
  cases A with
  | mk α x y β =>
    cases x
    cases y
    simp [chiralVectorProj, chiralUpperProj, chiralLowerProj, pureUpper, pureLower,
      NoncommutativeZornNambu.add]

/-- On a symmetric covariant state `psiCov a p = ⟨a, p, p, a⟩`, the upper and lower chiral cuts
extract the pure upper cone `pureUpper p` and pure lower cone `pureLower p`. -/
theorem chiralProj_psiCov_pair (a : R) (p : NoncommutativeZornNambu.Vec3 R) :
    chiralUpperProj (psiCov a p) = pureUpper p ∧
    chiralLowerProj (psiCov a p) = pureLower p := by
  have hup : chiralUpperProj (psiCov a p) = pureUpper p := by
    simp [chiralUpperProj, psiCov, pureUpper]
  have hlo : chiralLowerProj (psiCov a p) = pureLower p := by
    simp [chiralLowerProj, psiCov, pureLower]
  exact ⟨hup, hlo⟩

/-- **Stage $\mathfrak{ZG}_2$ Theorem:**
The chiral beta-gating projections `chiralUpperProj` and `chiralLowerProj` form a pair of
idempotent, mutually orthogonal projections intertwined by the parity/Hodge involution
`hodgeSectorSwap`,
  mapping `psiCov a p` onto the pure chiral cones `pureUpper p`
  `pureLower p`. -/
theorem zg2_chiral_cut_projections_idempotent_orthogonal_and_hodge_dual
    (A : ZornNC R) (a : R) (p : NoncommutativeZornNambu.Vec3 R) :
    chiralUpperProj (chiralUpperProj A) = chiralUpperProj A ∧
    chiralLowerProj (chiralLowerProj A) = chiralLowerProj A ∧
    chiralUpperProj (chiralLowerProj A) = (zeroZornNC : ZornNC R) ∧
    chiralLowerProj (chiralUpperProj A) = (zeroZornNC : ZornNC R) ∧
    hodgeSectorSwap (chiralUpperProj A) = chiralLowerProj (hodgeSectorSwap A) ∧
    chiralUpperProj (psiCov a p) = pureUpper p ∧
    chiralLowerProj (psiCov a p) = pureLower p := by
  have hidemU := chiralUpperProj_idem A
  have hidemL := chiralLowerProj_idem A
  have hpair := chiralProj_psiCov_pair a p
  exact ⟨hidemU,
    hidemL,
    chiralUpperProj_chiralLowerProj A,
    chiralLowerProj_chiralUpperProj A,
    hodgeSectorSwap_chiralUpperProj A,
    hpair.1,
    hpair.2⟩

/-!
## Section 3 ($\mathfrak{ZG}_3$): Ungated Racemic Cancellation vs. Chiral-Gated Nambu Associator Volume
-/

/-- The diagonal supertrace of the self-associator of any four-sector element `A : ZornNC R`
equals twice the difference of its upper and lower Nambu cubics:
$\mathrm{superTrace}([A, A, A]) = (N(A.x) - N(A.y)) - (N(A.y) - N(A.x))$. -/
theorem superTrace_self_associator (A : ZornNC R) :
    superTrace (associator A A A) =
      (nambu A.x - nambu A.y) - (nambu A.y - nambu A.x) := by
  obtain ⟨hα, hβ⟩ := self_associator_diagonal_nambu A
  unfold superTrace
  rw [hα, hβ]

/-- **Ungated Racemic Cancellation (Equal Vector Sectors):**
Whenever `A.x = A.y` (in particular, whenever `hodgeSectorSwap A = A`), both diagonal entries
and the diagonal supertrace of the self-associator `associator A A A` vanish identically. -/
theorem racemic_equal_sectors_self_associator_diagonal_zero
    (A : ZornNC R) (hxy : A.x = A.y) :
    (associator A A A).α = 0 ∧
    (associator A A A).β = 0 ∧
    superTrace (associator A A A) = 0 := by
  obtain ⟨hα, hβ⟩ := self_associator_diagonal_nambu A
  have hα0 : (associator A A A).α = 0 := by
    rw [hα, hxy, sub_self]
  have hβ0 : (associator A A A).β = 0 := by
    rw [hβ, hxy, sub_self]
  refine ⟨hα0, hβ0, ?_⟩
  unfold superTrace
  rw [hα0, hβ0, sub_zero]

/-- **Ungated Covariant State Cancellation:**
For every symmetric covariant state `psiCov a p = ⟨a, p, p, a⟩`, the ungated self-associator
has identically zero diagonal components and zero supertrace. -/
theorem psiCov_ungated_self_associator_diagonal_zero
    (a : R) (p : NoncommutativeZornNambu.Vec3 R) :
    (associator (psiCov a p) (psiCov a p) (psiCov a p)).α = 0 ∧
    (associator (psiCov a p) (psiCov a p) (psiCov a p)).β = 0 ∧
    superTrace (associator (psiCov a p) (psiCov a p) (psiCov a p)) = 0 := by
  have hxy : (psiCov a p).x = (psiCov a p).y := rfl
  exact racemic_equal_sectors_self_associator_diagonal_zero (psiCov a p) hxy

/-- **Ungated Parity-Pair Ensemble Cancellation:**
For *every* state `A : ZornNC R`, averaging `A` with its parity/Hodge partner `hodgeSectorSwap A`
cancels the diagonal self-associator components
  the self-associator supertrace identically to zero. -/
theorem ungated_parity_pair_self_associator_cancel (A : ZornNC R) :
    (associator A A A).α +
      (associator (hodgeSectorSwap A) (hodgeSectorSwap A) (hodgeSectorSwap A)).α = 0 ∧
    (associator A A A).β +
      (associator (hodgeSectorSwap A) (hodgeSectorSwap A) (hodgeSectorSwap A)).β = 0 ∧
    superTrace (associator A A A) +
      superTrace (associator (hodgeSectorSwap A) (hodgeSectorSwap A) (hodgeSectorSwap A)) = 0 := by
  obtain ⟨hα, hβ⟩ := self_associator_diagonal_nambu A
  obtain ⟨hα', hβ'⟩ := self_associator_diagonal_nambu (hodgeSectorSwap A)
  refine ⟨?_, ?_, ?_⟩
  · rw [hα, hα']
    dsimp [hodgeSectorSwap]
    abel
  · rw [hβ, hβ']
    dsimp [hodgeSectorSwap]
    abel
  · rw [← hodgeSectorSwap_associator, superTrace_hodgeSectorSwap]
    exact add_neg_cancel (superTrace (associator A A A))

/-- **Chiral-Gated Nambu Associator Activation:**
Applying the upper chiral beta-cut `chiralUpperProj` to the symmetric state `psiCov a p`
isolates the pure upper cone `pureUpper p`, whose self-associator is purely diagonal with
entries `+nambu p` and `-nambu p` and whose supertrace is `nambu p + nambu p`. -/
theorem chiralGated_psiCov_self_associator (a : R) (p : NoncommutativeZornNambu.Vec3 R) :
    associator (chiralUpperProj (psiCov a p))
      (chiralUpperProj (psiCov a p))
      (chiralUpperProj (psiCov a p)) =
      ⟨nambu p, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -nambu p⟩ ∧
    superTrace
      (associator (chiralUpperProj (psiCov a p))
        (chiralUpperProj (psiCov a p))
        (chiralUpperProj (psiCov a p))) = nambu p + nambu p := by
  rw [(chiralProj_psiCov_pair a p).1]
  have hassoc := pureUpper_self_associator p
  refine ⟨hassoc, ?_⟩
  rw [hassoc]
  simp [superTrace, sub_neg_eq_add]

/-- Dual lower chiral cut: applying `chiralLowerProj` to `psiCov a p` produces the opposite-sign
diagonal Nambu self-associator `⟨-nambu p, 0, 0, nambu p⟩`. -/
theorem chiralLowerGated_psiCov_self_associator (a : R) (p : NoncommutativeZornNambu.Vec3 R) :
    associator (chiralLowerProj (psiCov a p))
      (chiralLowerProj (psiCov a p))
      (chiralLowerProj (psiCov a p)) =
      ⟨-nambu p, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, nambu p⟩ := by
  rw [(chiralProj_psiCov_pair a p).2, ← hodgeSectorSwap_pureUpper, ← hodgeSectorSwap_associator,
    pureUpper_self_associator]
  rfl

/-- **Stage $\mathfrak{ZG}_3$ Theorem:**
Contrasts the ungated racemic cancellation of the Zorn self-associator with its chiral-gated
Nambu activation over any associative ring `R`. -/
theorem zg3_racemic_associator_cancellation_and_chiral_nambu_activation
    (A : ZornNC R) (a : R) (p : NoncommutativeZornNambu.Vec3 R) :
    ((associator (psiCov a p) (psiCov a p) (psiCov a p)).α = 0 ∧
     (associator (psiCov a p) (psiCov a p) (psiCov a p)).β = 0 ∧
     superTrace (associator (psiCov a p) (psiCov a p) (psiCov a p)) = 0) ∧
    (superTrace (associator A A A) +
      superTrace (associator (hodgeSectorSwap A) (hodgeSectorSwap A) (hodgeSectorSwap A)) = 0) ∧
    (associator (chiralUpperProj (psiCov a p))
      (chiralUpperProj (psiCov a p))
      (chiralUpperProj (psiCov a p)) =
      ⟨nambu p, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -nambu p⟩) ∧
    (superTrace
      (associator (chiralUpperProj (psiCov a p))
        (chiralUpperProj (psiCov a p))
        (chiralUpperProj (psiCov a p))) = nambu p + nambu p) := by
  have hungated := psiCov_ungated_self_associator_diagonal_zero a p
  have hpair := (ungated_parity_pair_self_associator_cancel A).2.2
  have hgated := chiralGated_psiCov_self_associator a p
  exact ⟨hungated, hpair, hgated.1, hgated.2⟩

end ChiralBetaGating

/-!
### Concrete Noncommutative $2 \times 2$ Integer Matrix Witness for Stage $\mathfrak{ZG}_3$
-/

namespace ChiralNambuMatrixWitness

open InfoGeometry.Algebra.NoncommutativeZornNambu.InsertionMatrixWitness

/-- Noncommuting operator triad $p_{\mathrm{chiral}}
  = (e_{12}, e_{21}, e_{11})$ in $\mathrm{Mat}_2(\mathbb{Z})$. -/
def pChiral : NoncommutativeZornNambu.Vec3 Mat₂ :=
  ⟨e₁₂, e₂₁, e₁₁⟩

/-- The diagonal $(0,0)$
  $(1,1)$ entries of `nambu pChiral` evaluate to $2$
  $1$ in $\mathbb{Z}$. -/
theorem nambu_pChiral_diagonal_entries :
    (nambu pChiral) 0 0 = 2 ∧ (nambu pChiral) 1 1 = 1 := by
  have h00 : (nambu pChiral) 0 0 = 2 := by decide
  have h11 : (nambu pChiral) 1 1 = 1 := by decide
  exact ⟨h00, h11⟩

/-- The cubic Nambu volume `nambu pChiral` is strictly non-zero in $\mathrm{Mat}_2(\mathbb{Z})$. -/
theorem nambu_pChiral_ne_zero : nambu pChiral ≠ 0 := by
  intro h
  have h00 : (nambu pChiral) 0 0 = (0 : Mat₂) 0 0 := congrFun (congrFun h 0) 0
  revert h00
  decide

/-- The supertrace of the chiral-gated self-associator has $(0,0)$ entry $4 \in \mathbb{Z}$
  is non-zero. -/
theorem superTrace_chiralGated_pChiral_ne_zero :
    superTrace
      (associator (chiralUpperProj (psiCov e₁₁ pChiral))
        (chiralUpperProj (psiCov e₁₁ pChiral))
        (chiralUpperProj (psiCov e₁₁ pChiral))) ≠ 0 := by
  rw [(chiralGated_psiCov_self_associator e₁₁ pChiral).2]
  intro h
  have h00 : (nambu pChiral + nambu pChiral) 0 0 = (0 : Mat₂) 0 0 :=
    congrFun (congrFun h 0) 0
  revert h00
  decide

/-- **Stage $\mathfrak{ZG}_3$ Concrete Operator Witness Theorem:**
For the explicit $2 \times 2$ integer matrix configuration `psiCov e₁₁ pChiral`, the ungated
racemic state has identically zero diagonal self-associator and zero supertrace, whereas its
chiral beta-gated projection `chiralUpperProj (psiCov e₁₁ pChiral)` has a strictly non-zero
diagonal Nambu self-associator (`nambu pChiral ≠ 0`) and strictly non-zero supertrace. -/
theorem zg3_concrete_matrix_witness_racemic_zero_vs_chiral_nonzero :
    (associator (psiCov e₁₁ pChiral) (psiCov e₁₁ pChiral) (psiCov e₁₁ pChiral)).α = 0 ∧
    superTrace (associator (psiCov e₁₁ pChiral) (psiCov e₁₁ pChiral) (psiCov e₁₁ pChiral)) = 0 ∧
    (associator (chiralUpperProj (psiCov e₁₁ pChiral))
      (chiralUpperProj (psiCov e₁₁ pChiral))
      (chiralUpperProj (psiCov e₁₁ pChiral))).α = nambu pChiral ∧
    nambu pChiral ≠ 0 ∧
    superTrace
      (associator (chiralUpperProj (psiCov e₁₁ pChiral))
        (chiralUpperProj (psiCov e₁₁ pChiral))
        (chiralUpperProj (psiCov e₁₁ pChiral))) ≠ 0 := by
  refine ⟨(psiCov_ungated_self_associator_diagonal_zero e₁₁ pChiral).1,
    (psiCov_ungated_self_associator_diagonal_zero e₁₁ pChiral).2.2,
    ?_,
    nambu_pChiral_ne_zero,
    superTrace_chiralGated_pChiral_ne_zero⟩
  rw [(chiralGated_psiCov_self_associator e₁₁ pChiral).1]

end ChiralNambuMatrixWitness

/-!
## Section 4 ($\mathfrak{ZG}_4$): Operator Cross-Ratio & Klein-Bottle Quotient Semidirect Action on the Zorn Associator
-/

/-- The native associator `(X * Y) * Z - X * (Y * Z)` on `InfoGeometry.Canonical.ZornMatrix ℝ`. -/
def canonicalZornAssociator (X Y Z : CanonicalZorn) : CanonicalZorn :=
  (X * Y) * Z - X * (Y * Z)

/-- The chiral supertrace $Z.a - Z.b$ on `InfoGeometry.Canonical.ZornMatrix ℝ`. -/
def canonicalZornSuperTrace (Z : CanonicalZorn) : ℝ :=
  Z.a - Z.b

/-- Orientation-reversing Klein-bottle involution $\tau_{\mathrm{Klein}}(a, b, x, y) = (b, a, y, x)$
on `CanonicalZorn`, exchanging the two Peirce poles $E_{11} \leftrightarrow E_{22}$ and swapping the
upper and lower chiral vector sectors $x \leftrightarrow y$. -/
def canonicalKleinSwap (X : CanonicalZorn) : CanonicalZorn where
  a := X.b
  b := X.a
  x := X.y
  y := X.x

/-- `canonicalKleinSwap` is an involution ($\tau_{\mathrm{Klein}}^2 = \mathrm{id}$). -/
theorem canonicalKleinSwap_involutive (X : CanonicalZorn) :
    canonicalKleinSwap (canonicalKleinSwap X) = X := by
  cases X
  simp [canonicalKleinSwap]

/-- `canonicalKleinSwap` exchanges the two diagonal Peirce poles `polePlus` and `poleMinus`. -/
theorem canonicalKleinSwap_exchanges_poles :
    canonicalKleinSwap polePlus = poleMinus ∧
    canonicalKleinSwap poleMinus = polePlus := by
  constructor <;> apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [canonicalKleinSwap, InfoGeometry.Canonical.ZornMatrix.zornPlus,
    InfoGeometry.Canonical.ZornMatrix.zornMinus]

/-- **Klein-Bottle Semidirect Quotient Law ($\tau_{\mathrm{Klein}} \circ T_t \circ \tau_{\mathrm{Klein}} = T_{t^{-1}}$):**
Conjugating the 1-parameter subgroup `torusMap t` by the orientation-reversing chiral swap
`canonicalKleinSwap` inverts the parameter $t \mapsto t^{-1}$, realizing the non-orientable
Klein-bottle quotient relation rather than an abelian 2-torus. -/
theorem canonicalKleinSwap_torusMap_inversion (t : ℝ) (X : CanonicalZorn) :
    canonicalKleinSwap (torusMap t (canonicalKleinSwap X)) = torusMap t⁻¹ X := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [canonicalKleinSwap, SplitIdempotentTorus.torusMap]

/-- `canonicalKleinSwap` reverses the sign of `canonicalZornSuperTrace`. -/
theorem canonicalZornSuperTrace_kleinSwap (Z : CanonicalZorn) :
    canonicalZornSuperTrace (canonicalKleinSwap Z) = -canonicalZornSuperTrace Z := by
  unfold canonicalZornSuperTrace canonicalKleinSwap
  ring

/-- `torusMap t` commutes with subtraction on `CanonicalZorn`. -/
theorem torusMap_sub (t : ℝ) (X Y : CanonicalZorn) :
    torusMap t (X - Y) = torusMap t X - torusMap t Y := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [SplitIdempotentTorus.torusMap, mul_sub]

/-- For every $t \ne 0$, the split Cartan torus action `torusMap t` commutes with the
nonassociative Zorn associator:
$\mathrm{torusMap}_t([X, Y, Z])
  = [\mathrm{torusMap}_t(X), \mathrm{torusMap}_t(Y), \mathrm{torusMap}_t(Z)]$. -/
theorem torusMap_canonicalZornAssociator (t : ℝ) (ht : t ≠ 0) (X Y Z : CanonicalZorn) :
    torusMap t (canonicalZornAssociator X Y Z) =
      canonicalZornAssociator (torusMap t X) (torusMap t Y) (torusMap t Z) := by
  unfold canonicalZornAssociator
  rw [torusMap_sub, torusMap_mul t ht, torusMap_mul t ht,
    torusMap_mul t ht, torusMap_mul t ht]

/-- **Split-Torus Gauge Invariance of the Diagonal Associator Readout:**
Because `torusMap t` fixes both diagonal Peirce coordinates (`.a` and `.b`) while acting as a
multiplication automorphism for $t \ne 0$, both diagonal entries and the chiral supertrace of
`canonicalZornAssociator` are strictly invariant under `torusMap t`. -/
theorem torusMap_associator_diagonal_and_superTrace_invariant
    (t : ℝ) (ht : t ≠ 0) (X Y Z : CanonicalZorn) :
    (canonicalZornAssociator (torusMap t X) (torusMap t Y) (torusMap t Z)).a =
      (canonicalZornAssociator X Y Z).a ∧
    (canonicalZornAssociator (torusMap t X) (torusMap t Y) (torusMap t Z)).b =
      (canonicalZornAssociator X Y Z).b ∧
    canonicalZornSuperTrace
      (canonicalZornAssociator (torusMap t X) (torusMap t Y) (torusMap t Z)) =
      canonicalZornSuperTrace (canonicalZornAssociator X Y Z) := by
  have h := (torusMap_canonicalZornAssociator t ht X Y Z).symm
  have ha : (canonicalZornAssociator (torusMap t X) (torusMap t Y) (torusMap t Z)).a =
      (canonicalZornAssociator X Y Z).a := by
    simpa [SplitIdempotentTorus.torusMap] using congrArg (fun W : CanonicalZorn => W.a) h
  have hb : (canonicalZornAssociator (torusMap t X) (torusMap t Y) (torusMap t Z)).b =
      (canonicalZornAssociator X Y Z).b := by
    simpa [SplitIdempotentTorus.torusMap] using congrArg (fun W : CanonicalZorn => W.b) h
  refine ⟨ha, hb, ?_⟩
  unfold canonicalZornSuperTrace
  rw [ha, hb]

/-- **Stage $\mathfrak{ZG}_4$ Theorem:**
Combines the noncommutative operator cross-ratio shift and Peirce-cone conjugation invariances
(`crossRatio_eq_genV`, `crossRatio_shift`, `conjPlus_crossRatio`, `conjMinus_crossRatio`)
over any unital associative ring `B` with the exact split-torus gauge invariance of the diagonal
Zorn associator and chiral supertrace on `CanonicalZorn`. -/
theorem zg4_cross_ratio_and_split_torus_associator_diagonal_invariance
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (X Z Y C A : B)
    (t : ℝ) (ht : t ≠ 0) (U V W : CanonicalZorn) :
    operatorCrossRatio P X Z Y 0 = genV P (X - Z) Y ∧
    operatorCrossRatio P (X + A) (Z + A) (Y + C) (0 + C) = operatorCrossRatio P X Z Y 0 ∧
    conjPlus P (X - Z) (operatorCrossRatio P X Z Y 0) = operatorCrossRatio P X Z Y 0 ∧
    conjMinus P (Y - 0) (operatorCrossRatio P X Z Y 0) = operatorCrossRatio P X Z Y 0 ∧
    (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W)).a =
      (canonicalZornAssociator U V W).a ∧
    (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W)).b =
      (canonicalZornAssociator U V W).b ∧
    canonicalZornSuperTrace
      (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W)) =
      canonicalZornSuperTrace (canonicalZornAssociator U V W) := by
  have hcr0 : operatorCrossRatio P X Z Y 0 = genV P (X - Z) Y := by
    simpa using crossRatio_eq_genV hP X Z Y 0
  have htor := torusMap_associator_diagonal_and_superTrace_invariant t ht U V W
  exact ⟨hcr0,
    crossRatio_shift hP X Z Y C A,
    conjPlus_crossRatio hP X Z Y,
    conjMinus_crossRatio hP X Z Y,
    htor.1,
    htor.2.1,
    htor.2.2⟩

/-!
## Section 5 ($\mathfrak{ZG}_5$): Native Zorn Cayley Transform Chiral Asymmetry & Master Synthesis
-/

open InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation

/-- Chiral supertrace readout $X.a - X.b$ on `SplitCarrier` (`ZornMatrix ℝ`). -/
def zornChiralSuperTrace (X : SplitCarrier) : ℝ :=
  X.a - X.b

/-- On the diagonal Peirce plane `diagonal a b
  = a • E11 + b • E22`, the chiral supertrace is $a - b$. -/
@[simp] theorem zornChiralSuperTrace_diagonal (a b : ℝ) :
    zornChiralSuperTrace (diagonal a b) = a - b := by
  unfold zornChiralSuperTrace diagonal
  simp [ZornMatrix.E11, ZornMatrix.E22]

/-- **Cayley Chiral Asymmetry Rational Identity:**
On the regular locus `ha : a + 1 ≠ 0`, `hb : b + 1 ≠ 0`, the chiral supertrace of the native
Zorn Cayley transform `nativeCayley (diagonal a b)` satisfies
$$\mathrm{zornChiralSuperTrace}\big(\mathrm{nativeCayley}(\mathrm{diagonal}(a, b))\big)
  = \frac{a - 1}{a + 1} - \frac{b - 1}{b + 1}
  = \frac{2(a - b)}{(a + 1)(b + 1)}.$$ -/
theorem nativeCayley_diagonal_chiralSuperTrace
    (a b : ℝ) (ha : a + 1 ≠ 0) (hb : b + 1 ≠ 0) :
    zornChiralSuperTrace (nativeCayley (diagonal a b)) =
      2 * (a - b) / ((a + 1) * (b + 1)) := by
  rw [nativeCayley_diagonal a b ha hb, zornChiralSuperTrace_diagonal]
  field_simp [ha, hb]
  ring

/-- **Cayley Chiral Polarization Equivalence:**
On the regular locus (`ha : a + 1 ≠ 0`, `hb : b + 1 ≠ 0`), the chiral supertrace of
`nativeCayley (diagonal a b)` vanishes if and only if $a = b$ (unpolarized racemic state),
and is non-zero if and only if $a \ne b$ (Zeeman/chiral-polarized state). -/
theorem nativeCayley_diagonal_chiralSuperTrace_eq_zero_iff
    (a b : ℝ) (ha : a + 1 ≠ 0) (hb : b + 1 ≠ 0) :
    zornChiralSuperTrace (nativeCayley (diagonal a b)) = 0 ↔ a = b := by
  rw [nativeCayley_diagonal_chiralSuperTrace a b ha hb]
  have hden : (a + 1) * (b + 1) ≠ 0 := mul_ne_zero ha hb
  rw [div_eq_zero_iff]
  constructor
  · rintro (hnum | hfalse)
    · linarith
    · exact False.elim (hden hfalse)
  · intro hab
    left
    linarith

/-- **Stage $\mathfrak{ZG}_5$ Theorem:**
Collects the two-sided quadratic denominator inverse law, the diagonal Cayley formula, the
exact chiral supertrace rational identity $\frac{2(a - b)}{(a + 1)(b + 1)}$, and the
chiral polarization equivalence on `SplitCarrier`. -/
theorem zg5_native_cayley_chiral_supertrace_asymmetry_and_polarization_iff
    (a b : ℝ) (ha : a + 1 ≠ 0) (hb : b + 1 ≠ 0) :
    CayleyRegular (diagonal a b) ∧
    ((diagonal a b + ZornMatrix.I) * quadraticInverse (diagonal a b + ZornMatrix.I) =
      ZornMatrix.I ∧
     quadraticInverse (diagonal a b + ZornMatrix.I) * (diagonal a b + ZornMatrix.I) =
      ZornMatrix.I) ∧
    nativeCayley (diagonal a b) =
      diagonal ((a - 1) / (a + 1)) ((b - 1) / (b + 1)) ∧
    zornChiralSuperTrace (nativeCayley (diagonal a b)) =
      2 * (a - b) / ((a + 1) * (b + 1)) ∧
    (zornChiralSuperTrace (nativeCayley (diagonal a b)) = 0 ↔ a = b) := by
  have hreg : CayleyRegular (diagonal a b) :=
    (diagonal_cayley_regular_iff a b).mpr ⟨ha, hb⟩
  exact ⟨hreg,
    cayley_denominator_inverse (diagonal a b) hreg,
    nativeCayley_diagonal a b ha hb,
    nativeCayley_diagonal_chiralSuperTrace a b ha hb,
    nativeCayley_diagonal_chiralSuperTrace_eq_zero_iff a b ha hb⟩

/-- **Master Zeeman Chiral-Gated Zorn Cascade Theorem ($\mathfrak{ZG}_1 \prec \dots \prec \mathfrak{ZG}_5$):**
Unifies the 5-stage covering poset with:
1. ($\mathfrak{ZG}_1$) Cartan chiral pole soldering and split-torus pole stabilization;
2. ($\mathfrak{ZG}_2$) Chiral beta-cut idempotent projections and Hodge parity duality;
3. ($\mathfrak{ZG}_3$) Ungated racemic cancellation vs. chiral-gated Nambu associator volume,
   together with the concrete $2 \times 2$ integer matrix witness;
4. ($\mathfrak{ZG}_4$) Operator cross-ratio
  split-torus invariance of the diagonal associator readout;
5. ($\mathfrak{ZG}_5$) Native Zorn Cayley transform chiral asymmetry
  polarization equivalence. -/
theorem zg5_master_zeeman_chiral_gated_zorn_cascade_synthesis
    {R : Type*} [Ring R] (A : ZornNC R) (r : R) (p : NoncommutativeZornNambu.Vec3 R)
    (t : ℝ) (ht : t ≠ 0) (U V W : CanonicalZorn)
    (a b : ℝ) (ha : a + 1 ≠ 0) (hb : b + 1 ≠ 0) :
    (ZeemanChiralCascadeStage.coverEdge .zg1_cartan_zeeman_gauge .zg2_chiral_beta_cut ∧
     ZeemanChiralCascadeStage.coverEdge .zg2_chiral_beta_cut .zg3_nambu_associator_gating ∧
     ZeemanChiralCascadeStage.coverEdge .zg3_nambu_associator_gating .zg4_cross_ratio_torus_invariance ∧
     ZeemanChiralCascadeStage.coverEdge .zg4_cross_ratio_torus_invariance .zg5_cayley_chiral_readout) ∧
    (chiralUPlus + chiralUMinus = chiralOne ∧
     chiralL * chiralL = chiralOne ∧
     (torusMap t polePlus = polePlus ∧ torusMap t poleMinus = poleMinus)) ∧
    (chiralUpperProj (chiralUpperProj A) = chiralUpperProj A ∧
     chiralUpperProj (chiralLowerProj A) = (zeroZornNC : ZornNC R) ∧
     hodgeSectorSwap (chiralUpperProj A) = chiralLowerProj (hodgeSectorSwap A)) ∧
    (superTrace (associator (psiCov r p) (psiCov r p) (psiCov r p)) = 0 ∧
     superTrace (associator A A A) +
       superTrace (associator (hodgeSectorSwap A) (hodgeSectorSwap A) (hodgeSectorSwap A)) = 0 ∧
     associator (chiralUpperProj (psiCov r p))
       (chiralUpperProj (psiCov r p))
       (chiralUpperProj (psiCov r p)) =
       ⟨nambu p, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -nambu p⟩ ∧
     nambu ChiralNambuMatrixWitness.pChiral ≠ 0) ∧
    (canonicalZornSuperTrace
      (canonicalZornAssociator (torusMap t U) (torusMap t V) (torusMap t W)) =
      canonicalZornSuperTrace (canonicalZornAssociator U V W)) ∧
    (zornChiralSuperTrace (nativeCayley (diagonal a b)) =
      2 * (a - b) / ((a + 1) * (b + 1)) ∧
     (zornChiralSuperTrace (nativeCayley (diagonal a b)) = 0 ↔ a = b)) := by
  have hposet := ZeemanChiralCascadeStage.poset_covering_chain
  have htor := (torusMap_associator_diagonal_and_superTrace_invariant t ht U V W).2.2
  have hcay := nativeCayley_diagonal_chiralSuperTrace a b ha hb
  exact ⟨hposet,
    ⟨chiral_diagonal_soldering, chiralL_sq, torusMap_fixes_poles t⟩,
    ⟨chiralUpperProj_idem A, chiralUpperProj_chiralLowerProj A, hodgeSectorSwap_chiralUpperProj A⟩,
    ⟨(psiCov_ungated_self_associator_diagonal_zero r p).2.2,
     (ungated_parity_pair_self_associator_cancel A).2.2,
     (chiralGated_psiCov_self_associator r p).1,
     ChiralNambuMatrixWitness.nambu_pChiral_ne_zero⟩,
    htor,
    ⟨hcay, nativeCayley_diagonal_chiralSuperTrace_eq_zero_iff a b ha hb⟩⟩

/-!
## Section 6: Klein–Nishina Coincidence Cross-Ratio, Cayley Derivation Coordinates,
  & the 5-Node $^{60}\text{Co}$ / $^{60}\text{Ni}^*$ Zorn Cascade Time-Reversal Anomaly

This section formalizes the constructive data-analysis and nonassociative Zorn-cascade spine:
1. **Klein–Nishina Coincidence Cross-Ratio & Multiplicative Detector Efficiency Cancellation:**
   In a coincidence detector array where raw sector counts factor as $N_{ij}
  = \epsilon_i \eta_j M_{ij}$,
   all single-crystal detector efficiencies $\epsilon_1, \epsilon_3, \eta_2, \eta_4 \ne 0$ cancel
   identically in both the projective coincidence cross-ratio
   $$CR = \frac{N_{12} N_{34}}{N_{14} N_{23}} = \frac{M_{12} M_{34}}{M_{14} M_{23}}$$
   and the chiral coincidence asymmetry
   $$\mathcal{A}_{\mathrm{chiral}}
  = \frac{N_{12} N_{34} - N_{14} N_{23}}{N_{12} N_{34} + N_{14} N_{23}}
     = \frac{CR - 1}{CR + 1}
     = \mathrm{zornChiralSuperTrace}\big(\mathrm{nativeCayley}(\mathrm{diagonal}(CR, 1))\big).$$
2. **Universal Operator Cayley Transform & 3D Skew-Symmetric Derivation Dual $S(\vec{\omega})$:**
   In any `[Ring B]`, if $U = (1 - S) R$ with $R(1 + S) = 1$, then $(1 + U)(1 + S) = 2$ and
   $(1 - U)(1 + S)
  = 2 S$. On $\mathrm{Vec3}\,R$ over `[CommRing R]`, the $3 \times 3$ skew-symmetric
   derivation matrix `skewCrossMatrix ω` satisfies $S(\vec{\omega})^T = -S(\vec{\omega})$, acts on
   any vector $\vec{v}$ as the cross product $\vec{\omega} \times \vec{v}$, and contracts with the
   nuclear spin $\vec{s}$ to produce the scalar triple product $\vec{s} \cdot (\vec{\omega} \times \vec{v})$.
3. **Deconfabulated 5-Node $^{60}\text{Co}$ / $^{60}\text{Ni}^*$ Zorn Cascade Poset ($\text{Node A} \prec \dots \prec \text{Node E}$):**
   Eliminates all `structure` wrappers (`TripleProductExpectation`, `ZornCascadeExperiment`, and
   the postulated `volume_is_associator` field) by proving `volume_is_associator` constructively on
   `ZornNC R`: for three distinct vectors $\vec{s}, \vec{e}_1, \vec{e}_2 \in \mathrm{Vec3}\,R$,
   the ungated covariant 3-state associator has zero supertrace, whereas the chiral beta-gated
   3-vector Zorn associator has upper-left Peirce component $\vec{s} \cdot (\vec{e}_1 \times \vec{e}_2)$
   and chiral supertrace $2\,\vec{s} \cdot (\vec{e}_1 \times \vec{e}_2)$, so any non-zero Zorn
   associator readout strictly breaks Time-Reversal symmetry ($\Omega(-\vec{s}, \vec{e}_1,
  \vec{e}_2) \ne \Omega(\vec{s}, \vec{e}_1, \vec{e}_2)$).
-/

/-- Coincidence cross-ratio $CR
  = \frac{N_{12} N_{34}}{N_{14} N_{23}}$ of four detector sector counts. -/
def coincidenceCrossRatio (N12 N34 N14 N23 : ℝ) : ℝ :=
  (N12 * N34) / (N14 * N23)

/-- Chiral coincidence asymmetry $\mathcal{A}_{\mathrm{chiral}}
  = \frac{N_{12} N_{34} - N_{14} N_{23}}{N_{12} N_{34} + N_{14} N_{23}}$. -/
def chiralCoincidenceAsymmetry (N12 N34 N14 N23 : ℝ) : ℝ :=
  (N12 * N34 - N14 * N23) / (N12 * N34 + N14 * N23)

/-- Universal commutative-ring factorization of the coincidence cross-ratio numerator
  denominator
under multiplicative single-detector efficiencies $N_{ij} = \epsilon_i \eta_j M_{ij}$. -/
theorem coincidenceCrossRatio_factorization {R : Type*} [CommRing R]
    (ε1 ε3 η2 η4 M12 M34 M14 M23 : R) :
    (ε1 * η2 * M12) * (ε3 * η4 * M34) = (ε1 * ε3 * η2 * η4) * (M12 * M34) ∧
    (ε1 * η4 * M14) * (ε3 * η2 * M23) = (ε1 * ε3 * η2 * η4) * (M14 * M23) := by
  have hnum : (ε1 * η2 * M12) * (ε3 * η4 * M34) = (ε1 * ε3 * η2 * η4) * (M12 * M34) := by
    ring
  have hden : (ε1 * η4 * M14) * (ε3 * η2 * M23) = (ε1 * ε3 * η2 * η4) * (M14 * M23) := by
    ring
  exact ⟨hnum, hden⟩

/-- **Klein–Nishina Coincidence Cross-Ratio Efficiency Cancellation:**
For any non-zero single-detector efficiencies $\epsilon_1, \epsilon_3, \eta_2, \eta_4 \ne 0$,
the multiplicative efficiency factors cancel identically in both `coincidenceCrossRatio` and
`chiralCoincidenceAsymmetry`. -/
theorem coincidenceCrossRatio_efficiency_cancellation
    (ε1 ε3 η2 η4 M12 M34 M14 M23 : ℝ)
    (hε1 : ε1 ≠ 0) (hε3 : ε3 ≠ 0) (hη2 : η2 ≠ 0) (hη4 : η4 ≠ 0) :
    coincidenceCrossRatio
      (ε1 * η2 * M12) (ε3 * η4 * M34) (ε1 * η4 * M14) (ε3 * η2 * M23) =
      coincidenceCrossRatio M12 M34 M14 M23 ∧
    chiralCoincidenceAsymmetry
      (ε1 * η2 * M12) (ε3 * η4 * M34) (ε1 * η4 * M14) (ε3 * η2 * M23) =
      chiralCoincidenceAsymmetry M12 M34 M14 M23 := by
  let E : ℝ := ε1 * ε3 * η2 * η4
  have hE : E ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hε1 hε3) hη2) hη4
  obtain ⟨hnum, hden⟩ := coincidenceCrossRatio_factorization ε1 ε3 η2 η4 M12 M34 M14 M23
  refine ⟨?_, ?_⟩
  · unfold coincidenceCrossRatio
    rw [hnum, hden]
    exact mul_div_mul_left (M12 * M34) (M14 * M23) hE
  · unfold chiralCoincidenceAsymmetry
    rw [hnum, hden, ← mul_sub E (M12 * M34) (M14 * M23), ← mul_add E (M12 * M34) (M14 * M23)]
    exact mul_div_mul_left (M12 * M34 - M14 * M23) (M12 * M34 + M14 * M23) hE

/-- **Chiral Coincidence Asymmetry as the Native Zorn Cayley Transform of the Cross-Ratio:**
Whenever $N_{14} N_{23} \ne 0$ and $CR + 1 \ne 0$, the chiral coincidence asymmetry
$\mathcal{A}_{\mathrm{chiral}}
  = \frac{N_{12} N_{34} - N_{14} N_{23}}{N_{12} N_{34} + N_{14} N_{23}}$
equals the scalar Cayley transform $\frac{CR - 1}{CR + 1}$ of $CR
  = \mathrm{coincidenceCrossRatio}(N_{12}, N_{34}, N_{14}, N_{23})$,
equals the chiral supertrace `zornChiralSuperTrace (nativeCayley (diagonal CR 1))`, and vanishes
if and only if $CR = 1$. -/
theorem chiralCoincidenceAsymmetry_eq_cayley_of_crossRatio
    (N12 N34 N14 N23 : ℝ) (hden : N14 * N23 ≠ 0)
    (hCR : coincidenceCrossRatio N12 N34 N14 N23 + 1 ≠ 0) :
    let CR := coincidenceCrossRatio N12 N34 N14 N23
    chiralCoincidenceAsymmetry N12 N34 N14 N23 = (CR - 1) / (CR + 1) ∧
    zornChiralSuperTrace (nativeCayley (diagonal CR 1)) =
      chiralCoincidenceAsymmetry N12 N34 N14 N23 ∧
    (chiralCoincidenceAsymmetry N12 N34 N14 N23 = 0 ↔ CR = 1) := by
  dsimp only
  have hcay :
      chiralCoincidenceAsymmetry N12 N34 N14 N23 =
        (coincidenceCrossRatio N12 N34 N14 N23 - 1) /
          (coincidenceCrossRatio N12 N34 N14 N23 + 1) := by
    unfold chiralCoincidenceAsymmetry coincidenceCrossRatio
    have hsub : N12 * N34 / (N14 * N23) - 1 = (N12 * N34 - N14 * N23) / (N14 * N23) :=
      div_sub_one hden
    have hadd : N12 * N34 / (N14 * N23) + 1 = (N12 * N34 + N14 * N23) / (N14 * N23) :=
      div_add_one hden
    rw [hsub, hadd, div_div_div_cancel_right₀ hden]
  have h1 : (1 : ℝ) + 1 ≠ 0 := by norm_num
  have htr :
      zornChiralSuperTrace (nativeCayley (diagonal (coincidenceCrossRatio N12 N34 N14 N23) 1)) =
        chiralCoincidenceAsymmetry N12 N34 N14 N23 := by
    rw [nativeCayley_diagonal_chiralSuperTrace _ 1 hCR h1, hcay]
    have h2 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h2, mul_comm (coincidenceCrossRatio N12 N34 N14 N23 + 1) 2]
    exact mul_div_mul_left (coincidenceCrossRatio N12 N34 N14 N23 - 1)
      (coincidenceCrossRatio N12 N34 N14 N23 + 1) two_ne_zero
  refine ⟨hcay, htr, ?_⟩
  rw [← htr]
  exact nativeCayley_diagonal_chiralSuperTrace_eq_zero_iff
    (coincidenceCrossRatio N12 N34 N14 N23) 1 hCR h1

/-- **Universal Operator Cayley Transform Inversion:**
In any associative ring `B`, if $R(1 + S) = 1$ and $U = (1 - S)R$, then $(1 + U)(1 + S) = 1 + 1$
and $(1 - U)(1 + S) = S + S$, recovering the Lie/derivation generator $2S
  = (1 - U)(1 + S)$ without division. -/
theorem operator_cayley_transform_recovery {B : Type*} [Ring B]
    (S R : B) (hR : R * (1 + S) = 1) :
    let U := (1 - S) * R
    (1 - S) * (1 + S) = 1 - S * S ∧
    U * (1 + S) = 1 - S ∧
    (1 + U) * (1 + S) = 1 + 1 ∧
    (1 - U) * (1 + S) = S + S := by
  dsimp only
  have hU : (1 - S) * R * (1 + S) = 1 - S := by
    rw [mul_assoc, hR, mul_one]
  refine ⟨by noncomm_ring, hU, ?_, ?_⟩
  · rw [add_mul, one_mul, hU]
    abel
  · rw [sub_mul, one_mul, hU]
    abel

/-- The $3 \times 3$ skew-symmetric derivation matrix $S(\vec{\omega}) \in \mathfrak{so}(3)$
associated to an axial 3-vector $\vec{\omega} = (\omega_0, \omega_1, \omega_2)$. -/
def skewCrossMatrix {R : Type*} [Ring R] (ω : NoncommutativeZornNambu.Vec3 R) :
    Matrix (Fin 3) (Fin 3) R :=
  !![0, -ω.x2, ω.x1;
     ω.x2, 0, -ω.x0;
     -ω.x1, ω.x0, 0]

/-- Coordinate embedding of `Vec3 R` into `Fin 3 → R`. -/
def vec3ToFin3 {R : Type*} (v : NoncommutativeZornNambu.Vec3 R) : Fin 3 → R :=
  ![v.x0, v.x1, v.x2]

/-- `skewCrossMatrix ω` is strictly skew-symmetric: $S(\vec{\omega})^T = -S(\vec{\omega})$. -/
theorem skewCrossMatrix_transpose {R : Type*} [Ring R]
    (ω : NoncommutativeZornNambu.Vec3 R) :
    (skewCrossMatrix ω).transpose = -skewCrossMatrix ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewCrossMatrix]

/-- **Cayley Skew-Symmetric Generator to Cross-Product and Scalar Triple Product:**
Over any ring `[Ring R]`, the $3 \times 3$ skew-symmetric matrix `skewCrossMatrix ω` acts on
any 3-vector `v` as the cross product `cross ω v`, and its bilinear contraction with the nuclear
spin vector `s` equals the scalar triple product `dot s (cross ω v)`. -/
theorem skewCrossMatrix_mulVec_and_triple_product {R : Type*} [Ring R]
    (ω s v : NoncommutativeZornNambu.Vec3 R) :
    Matrix.mulVec (skewCrossMatrix ω) (vec3ToFin3 v) = vec3ToFin3 (cross ω v) ∧
    dotProduct (vec3ToFin3 s) (Matrix.mulVec (skewCrossMatrix ω) (vec3ToFin3 v)) =
      dot s (cross ω v) := by
  have hmv : Matrix.mulVec (skewCrossMatrix ω) (vec3ToFin3 v) = vec3ToFin3 (cross ω v) := by
    funext i
    fin_cases i <;>
      simp [skewCrossMatrix, vec3ToFin3, cross, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      noncomm_ring
  refine ⟨hmv, ?_⟩
  rw [hmv]
  simp [vec3ToFin3, dot, cross, dotProduct, Fin.sum_univ_three]

/-- The 5-node causal poset of the $^{60}\text{Co} \to {}^{60}\text{Ni}^*$ Zorn cascade
Time-Reversal breaking theorem ($\text{Node A} \prec \text{Node B} \prec \text{Node C} \prec \text{Node D} \prec \text{Node E}$). -/
inductive ZornCascadeNode : Type
  | nodeA_macroscopic_triple_product
  | nodeB_time_reversal_nullification
  | nodeC_nonassociative_zorn_associator
  | nodeD_constructive_volume_associator_bridge
  | nodeE_time_reversal_breaking_discovery
  deriving DecidableEq, Repr

namespace ZornCascadeNode

/-- Monotone integer rank $\text{Node A} < \text{Node B} < \text{Node C} < \text{Node D} < \text{Node E}$. -/
def rank : ZornCascadeNode → ℕ
  | .nodeA_macroscopic_triple_product => 1
  | .nodeB_time_reversal_nullification => 2
  | .nodeC_nonassociative_zorn_associator => 3
  | .nodeD_constructive_volume_associator_bridge => 4
  | .nodeE_time_reversal_breaking_discovery => 5

/-- Covering edges of the 5-node Hasse chain $\text{Node A} \prec \dots \prec \text{Node E}$. -/
def coverEdge : ZornCascadeNode → ZornCascadeNode → Prop
  | .nodeA_macroscopic_triple_product, .nodeB_time_reversal_nullification => True
  | .nodeB_time_reversal_nullification, .nodeC_nonassociative_zorn_associator => True
  | .nodeC_nonassociative_zorn_associator, .nodeD_constructive_volume_associator_bridge => True
  | .nodeD_constructive_volume_associator_bridge, .nodeE_time_reversal_breaking_discovery => True
  | _, _ => False

/-- Decidability of `coverEdge`. -/
instance instDecidableRelCoverEdge : DecidableRel coverEdge := fun a b => by
  cases a <;> cases b <;> unfold coverEdge <;> infer_instance

/-- The node rank map is strictly injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge increments `rank` by $1$. -/
theorem coverEdge_rank_step {a b : ZornCascadeNode} (h : coverEdge a b) :
    rank b = rank a + 1 := by
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge is strictly monotone in `rank`. -/
theorem coverEdge_strictMono {a b : ZornCascadeNode} (h : coverEdge a b) :
    rank a < rank b := by
  have hstep := coverEdge_rank_step h
  omega

/-- No node covers itself. -/
theorem coverEdge_acyclic (a : ZornCascadeNode) : ¬ coverEdge a a := by
  intro h
  have hlt := coverEdge_strictMono h
  omega

/-- Complete 4-edge covering chain $\text{Node A} \prec \text{Node B} \prec \text{Node C} \prec \text{Node D} \prec \text{Node E}$. -/
theorem poset_covering_chain :
    coverEdge .nodeA_macroscopic_triple_product .nodeB_time_reversal_nullification ∧
    coverEdge .nodeB_time_reversal_nullification .nodeC_nonassociative_zorn_associator ∧
    coverEdge .nodeC_nonassociative_zorn_associator .nodeD_constructive_volume_associator_bridge ∧
    coverEdge .nodeD_constructive_volume_associator_bridge .nodeE_time_reversal_breaking_discovery
  := by
  decide

end ZornCascadeNode

/-- Componentwise negation $-v = (-v_0, -v_1, -v_2)$ on `Vec3 R`. -/
def negVec3 {R : Type*} [Ring R] (v : NoncommutativeZornNambu.Vec3 R) :
    NoncommutativeZornNambu.Vec3 R :=
  ⟨-v.x0, -v.x1, -v.x2⟩

/-- **Node A Observable:** Volumetric scalar triple product
$\Omega_{\mathrm{vol}}(\vec{s}, \vec{e}_1, \vec{e}_2) = \vec{s} \cdot (\vec{e}_1 \times \vec{e}_2)$
of a nuclear spin $\vec{s}$
  two cascade photon propagation/polarization vectors $\vec{e}_1,
  \vec{e}_2$. -/
def cascadeTripleVolume {R : Type*} [Ring R]
    (s e1 e2 : NoncommutativeZornNambu.Vec3 R) : R :=
  dot s (cross e1 e2)

/-- **Non-Commutative Spin & Photon Sign-Reversal Oddness (`[Ring R]`):**
Over any non-commutative ring `R`, `cascadeTripleVolume s e1 e2` is strictly odd under reversal
of any of its three vector arguments (`negVec3`). -/
theorem cascadeTripleVolume_odd_in_all_slots {R : Type*} [Ring R]
    (s e1 e2 : NoncommutativeZornNambu.Vec3 R) :
    cascadeTripleVolume (negVec3 s) e1 e2 = -cascadeTripleVolume s e1 e2 ∧
    cascadeTripleVolume s (negVec3 e1) e2 = -cascadeTripleVolume s e1 e2 ∧
    cascadeTripleVolume s e1 (negVec3 e2) = -cascadeTripleVolume s e1 e2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [cascadeTripleVolume, negVec3, dot, cross] <;>
    noncomm_ring

/-- **Non-Commutative Photon Exchange Commutator Defect (`[Ring R]`):**
Over a general non-commutative ring `R`, the symmetric sum under photon exchange `e1 ↔ e2`
equals the contraction of `s` with the commutator cross defect of `e1` and `e2`. -/
theorem cascadeTripleVolume_photon_exchange_noncomm {R : Type*} [Ring R]
    (s e1 e2 : NoncommutativeZornNambu.Vec3 R) :
    cascadeTripleVolume s e1 e2 + cascadeTripleVolume s e2 e1 =
      dot s ⟨NoncommutativeZornNambu.comm e1.x1 e2.x2 - NoncommutativeZornNambu.comm e1.x2 e2.x1,
             NoncommutativeZornNambu.comm e1.x2 e2.x0 - NoncommutativeZornNambu.comm e1.x0 e2.x2,
             NoncommutativeZornNambu.comm e1.x0 e2.x1 - NoncommutativeZornNambu.comm e1.x1 e2.x0⟩ := by
  simp [cascadeTripleVolume, dot, cross, NoncommutativeZornNambu.comm]
  noncomm_ring

/-- **Node A Theorem (Spin-Odd Parity & Photon Exchange Antisymmetry):**
Over any commutative ring `R`, `cascadeTripleVolume s e1 e2` is strictly odd under reversal of
any argument (`negVec3`) and strictly antisymmetric under photon exchange $e_1 \leftrightarrow e_2$. -/
theorem cascadeTripleVolume_odd_and_antisymmetric {R : Type*} [CommRing R]
    (s e1 e2 : NoncommutativeZornNambu.Vec3 R) :
    cascadeTripleVolume (negVec3 s) e1 e2 = -cascadeTripleVolume s e1 e2 ∧
    cascadeTripleVolume s (negVec3 e1) e2 = -cascadeTripleVolume s e1 e2 ∧
    cascadeTripleVolume s e1 (negVec3 e2) = -cascadeTripleVolume s e1 e2 ∧
    cascadeTripleVolume s e2 e1 = -cascadeTripleVolume s e1 e2 := by
  have hodd := cascadeTripleVolume_odd_in_all_slots s e1 e2
  refine ⟨hodd.1, hodd.2.1, hodd.2.2, ?_⟩
  simp [cascadeTripleVolume, dot, cross]
  ring

/-- **Node B Theorem (Universal Group-Theoretic T-Symmetry Nullification):**
For any spin-odd observable `vol : V → V → V → G` (`vol (-s) e1 e2 = -vol s e1 e2`),
Time-Reversal symmetry (`vol (-s) e1 e2 = vol s e1 e2`) forces `(2 : ℤ) • vol s e1 e2 = 0`. -/
theorem odd_spin_time_reversal_forces_two_zsmul_zero
    {V G : Type*} [Neg V] [AddCommGroup G]
    (vol : V → V → V → G)
    (h_odd : ∀ s e1 e2, vol (-s) e1 e2 = -vol s e1 e2)
    (h_tsym : ∀ s e1 e2, vol (-s) e1 e2 = vol s e1 e2)
    (s e1 e2 : V) :
    (2 : ℤ) • vol s e1 e2 = 0 := by
  have h1 : vol s e1 e2 = -vol s e1 e2 := by
    calc
      vol s e1 e2 = vol (-s) e1 e2 := (h_tsym s e1 e2).symm
      _ = -vol s e1 e2 := h_odd s e1 e2
  have h2 : vol s e1 e2 + vol s e1 e2 = 0 := by
    calc
      vol s e1 e2 + vol s e1 e2 = vol s e1 e2 + (-vol s e1 e2) := by
        nth_rw 2 [h1]
      _ = 0 := add_neg_cancel (vol s e1 e2)
  rwa [two_zsmul]

/-- **Exact torsion criterion for time-reversal invariance of a spin-odd observable:**
For an additive-group-valued observable that changes sign when its first argument is
negated, invariance under that same reversal holds exactly when every value is killed
by multiplication by two. The real-valued zero conclusion is the torsion-free special
case; over groups with nontrivial 2-torsion, zero need not follow. -/
theorem odd_observable_time_reversal_iff_two_torsion
    {V G : Type*} [Neg V] [AddCommGroup G]
    (vol : V → V → V → G)
    (h_odd : ∀ s e1 e2, vol (-s) e1 e2 = -vol s e1 e2) :
    (∀ s e1 e2, vol (-s) e1 e2 = vol s e1 e2) ↔
      ∀ s e1 e2, (2 : ℤ) • vol s e1 e2 = 0 := by
  constructor
  · intro h_invariant s e1 e2
    exact odd_spin_time_reversal_forces_two_zsmul_zero
      vol h_odd h_invariant s e1 e2
  · intro h_two_torsion s e1 e2
    have hdouble : vol s e1 e2 + vol s e1 e2 = 0 := by
      simpa only [two_zsmul] using h_two_torsion s e1 e2
    have hneg : -vol s e1 e2 = vol s e1 e2 := by
      calc
        -vol s e1 e2 = -vol s e1 e2 + 0 := by simp
        _ = -vol s e1 e2 + (vol s e1 e2 + vol s e1 e2) := by
          rw [← hdouble]
        _ = (-vol s e1 e2 + vol s e1 e2) + vol s e1 e2 := by
          rw [add_assoc]
        _ = 0 + vol s e1 e2 := by rw [neg_add_cancel]
        _ = vol s e1 e2 := by simp
    calc
      vol (-s) e1 e2 = -vol s e1 e2 := h_odd s e1 e2
      _ = vol s e1 e2 := hneg

/-- **Node B Real Corollary:** Over `ℝ`, Time-Reversal symmetry forces `cascadeTripleVolume s e1 e2
  = 0`. -/
theorem cascadeTripleVolume_time_reversal_forces_zero
    (s e1 e2 : NoncommutativeZornNambu.Vec3 ℝ)
    (h_tsym : cascadeTripleVolume (negVec3 s) e1 e2 = cascadeTripleVolume s e1 e2) :
    cascadeTripleVolume s e1 e2 = 0 := by
  have hodd := (cascadeTripleVolume_odd_and_antisymmetric s e1 e2).1
  rw [h_tsym] at hodd
  linarith

/-- **Node C Definition:** The associator $[a, b, c] = (a b) c - a (b c)$ in any
nonassociative ring `[NonAssocRing A]`. -/
def nonAssocAssociator {A : Type*} [NonAssocRing A] (a b c : A) : A :=
  (a * b) * c - a * (b * c)

/-- **Node C Theorem (Odd Parity of the Nonassociative Associator in Every Slot):**
In any `[NonAssocRing A]`,
  negating any of the three arguments negates `nonAssocAssociator a b c`. -/
theorem nonAssocAssociator_odd_in_all_slots {A : Type*} [NonAssocRing A] (a b c : A) :
    nonAssocAssociator (-a) b c = -nonAssocAssociator a b c ∧
    nonAssocAssociator a (-b) c = -nonAssocAssociator a b c ∧
    nonAssocAssociator a b (-c) = -nonAssocAssociator a b c := by
  refine ⟨?_, ?_, ?_⟩ <;>
    unfold nonAssocAssociator <;>
    simp [neg_mul, mul_neg, neg_sub] <;>
    abel

/-- **Node C / D Core Identity (Distinct 3-Vector Pure Upper Zorn Associator):**
Over any associative ring `R`, the Zorn associator of three distinct pure upper-cone vectors
`pureUpper s`, `pureUpper e1`, `pureUpper e2` in `ZornNC R` is purely diagonal with upper-left
entry `dot s (cross e1 e2)` and lower-right entry `-dot (cross s e1) e2`. -/
theorem pureUpper_three_vector_associator {R : Type*} [Ring R]
    (s e1 e2 : NoncommutativeZornNambu.Vec3 R) :
    associator (pureUpper s) (pureUpper e1) (pureUpper e2) =
      ⟨dot s (cross e1 e2), ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -dot (cross s e1) e2⟩ := by
  cases s
  cases e1
  cases e2
  simp [NoncommutativeZornNambu.associator, NoncommutativeZornNambu.mul,
    NoncommutativeZornNambu.sub, pureUpper, dot, cross]

/-- Over any associative ring `[Ring R]`, `dot (cross s e1) e2 = cascadeTripleVolume s e1 e2`
because every monomial preserves the left-to-right factor order `s * e1 * e2`. -/
theorem dot_cross_eq_cascadeTripleVolume {R : Type*} [Ring R]
    (s e1 e2 : NoncommutativeZornNambu.Vec3 R) :
    dot (cross s e1) e2 = cascadeTripleVolume s e1 e2 := by
  cases s
  cases e1
  cases e2
  simp [cascadeTripleVolume, dot, cross]
  noncomm_ring

/-- Over any associative ring `[Ring R]`, the chiral-gated 3-vector Zorn associator
has upper-left entry `cascadeTripleVolume s e1 e2`, lower-right entry
`-cascadeTripleVolume s e1 e2`, and chiral supertrace `2 * cascadeTripleVolume s e1 e2`. -/
theorem chiralGated_three_vector_associator_noncomm {R : Type*} [Ring R]
    (a b c : R) (s e1 e2 : NoncommutativeZornNambu.Vec3 R) :
    associator
      (chiralUpperProj (psiCov a s))
      (chiralUpperProj (psiCov b e1))
      (chiralUpperProj (psiCov c e2)) =
      ⟨cascadeTripleVolume s e1 e2, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -cascadeTripleVolume s e1 e2⟩ ∧
    (associator
      (chiralUpperProj (psiCov a s))
      (chiralUpperProj (psiCov b e1))
      (chiralUpperProj (psiCov c e2))).α = cascadeTripleVolume s e1 e2 ∧
    superTrace
      (associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))) = 2 * cascadeTripleVolume s e1 e2 := by
  rw [(chiralProj_psiCov_pair a s).1, (chiralProj_psiCov_pair b e1).1,
    (chiralProj_psiCov_pair c e2).1]
  have hassoc :
      associator (pureUpper s) (pureUpper e1) (pureUpper e2) =
        ⟨cascadeTripleVolume s e1 e2, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -cascadeTripleVolume s e1 e2⟩ := by
    rw [pureUpper_three_vector_associator, dot_cross_eq_cascadeTripleVolume]
    rfl
  refine ⟨hassoc, ?_, ?_⟩
  · rw [hassoc]
  · rw [hassoc]
    simp [superTrace]
    noncomm_ring

/-- **Node D Theorem (Constructive Proof of `volume_is_associator` on `ZornNC R`):**
Over any commutative ring `R`, for any three covariant states `psiCov a s`, `psiCov b e1`,
`psiCov c e2`:
1. The **ungated** 3-state associator has identically zero chiral supertrace;
2. The **chiral beta-gated** 3-vector associator has upper-left Peirce component equal to
   `cascadeTripleVolume s e1 e2`,
  lower-right Peirce component equal to `-cascadeTripleVolume s e1 e2`,
   and chiral supertrace equal to `2 * cascadeTripleVolume s e1 e2`.
This proves the `volume_is_associator` law constructively from the Zorn multiplication table
without any `structure` wrapper or postulated field. -/
theorem chiralGated_three_vector_associator_eq_triple_volume {R : Type*} [CommRing R]
    (a b c : R) (s e1 e2 : NoncommutativeZornNambu.Vec3 R) :
    superTrace (associator (psiCov a s) (psiCov b e1) (psiCov c e2)) = 0 ∧
    associator
      (chiralUpperProj (psiCov a s))
      (chiralUpperProj (psiCov b e1))
      (chiralUpperProj (psiCov c e2)) =
      ⟨cascadeTripleVolume s e1 e2, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -cascadeTripleVolume s e1 e2⟩ ∧
    (associator
      (chiralUpperProj (psiCov a s))
      (chiralUpperProj (psiCov b e1))
      (chiralUpperProj (psiCov c e2))).α = cascadeTripleVolume s e1 e2 ∧
    superTrace
      (associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))) = 2 * cascadeTripleVolume s e1 e2 := by
  have hungated : superTrace (associator (psiCov a s) (psiCov b e1) (psiCov c e2)) = 0 := by
    cases s
    cases e1
    cases e2
    simp [superTrace, NoncommutativeZornNambu.associator, psiCov,
      NoncommutativeZornNambu.mul, NoncommutativeZornNambu.sub, dot, cross]
  rw [(chiralProj_psiCov_pair a s).1, (chiralProj_psiCov_pair b e1).1,
    (chiralProj_psiCov_pair c e2).1]
  have hcyc : dot (cross s e1) e2 = cascadeTripleVolume s e1 e2 := by
    cases s
    cases e1
    cases e2
    simp [cascadeTripleVolume, dot, cross]
    ring
  have hassoc :
      associator (pureUpper s) (pureUpper e1) (pureUpper e2) =
        ⟨cascadeTripleVolume s e1 e2, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -cascadeTripleVolume s e1 e2⟩ := by
    rw [pureUpper_three_vector_associator, hcyc]
    rfl
  refine ⟨hungated, hassoc, ?_, ?_⟩
  · rw [hassoc]
  · rw [hassoc]
    simp [superTrace]
    ring

/-- Standard orthonormal $^{60}\text{Co} \to {}^{60}\text{Ni}^*$ cascade witness vectors:
nuclear spin $\vec{s} = \hat{e}_x$, first photon $\vec{e}_1 = \hat{e}_y$, second photon $\vec{e}_2
  = \hat{e}_z$. -/
def spinEx : NoncommutativeZornNambu.Vec3 ℝ := ⟨1, 0, 0⟩

/-- First cascade photon direction $\hat{e}_y = (0, 1, 0)$. -/
def photonEy : NoncommutativeZornNambu.Vec3 ℝ := ⟨0, 1, 0⟩

/-- Second cascade photon direction $\hat{e}_z = (0, 0, 1)$. -/
def photonEz : NoncommutativeZornNambu.Vec3 ℝ := ⟨0, 0, 1⟩

/-- **Node E Discovery Theorem (Non-Zero Zorn Associator Anomaly Breaks Time-Reversal Symmetry):**
Unifies the 5-node Hasse chain ($\text{Node A} \prec \dots \prec \text{Node E}$) with:
1. Spin-reversal negation of the chiral-gated 3-vector Zorn associator readout;
2. Constructive proof that any non-zero chiral-gated Zorn associator trace (or `superTrace`)
   strictly breaks Time-Reversal symmetry ($\Omega(-\vec{s}, \vec{e}_1,
  \vec{e}_2) \ne \Omega(\vec{s}, \vec{e}_1, \vec{e}_2)$);
3. Concrete orthogonal $^{60}\text{Co} \to {}^{60}\text{Ni}^*$ cascade witness (`spinEx`, `photonEy`,
  `photonEz`)
   with unit triple-product volume $\Omega = 1$, Zorn associator `superTrace = 2 ≠ 0`, and broken
   Time-Reversal symmetry $\Omega(-\hat{e}_x, \hat{e}_y, \hat{e}_z) = -1 \ne 1
  = \Omega(\hat{e}_x, \hat{e}_y, \hat{e}_z)$. -/
theorem zorn_cascade_associator_anomaly_breaks_time_reversal
    (a b c : ℝ) (s e1 e2 : NoncommutativeZornNambu.Vec3 ℝ) :
    (ZornCascadeNode.coverEdge .nodeA_macroscopic_triple_product .nodeB_time_reversal_nullification ∧
     ZornCascadeNode.coverEdge .nodeB_time_reversal_nullification .nodeC_nonassociative_zorn_associator ∧
     ZornCascadeNode.coverEdge .nodeC_nonassociative_zorn_associator .nodeD_constructive_volume_associator_bridge ∧
     ZornCascadeNode.coverEdge .nodeD_constructive_volume_associator_bridge .nodeE_time_reversal_breaking_discovery) ∧
    ((associator
        (chiralUpperProj (psiCov a (negVec3 s)))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))).α =
      -(associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))).α) ∧
    ((associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))).α ≠ 0 →
      cascadeTripleVolume (negVec3 s) e1 e2 ≠ cascadeTripleVolume s e1 e2) ∧
    (superTrace
      (associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))) ≠ 0 →
      cascadeTripleVolume (negVec3 s) e1 e2 ≠ cascadeTripleVolume s e1 e2) ∧
    (cascadeTripleVolume spinEx photonEy photonEz = 1 ∧
     superTrace
      (associator
        (chiralUpperProj (psiCov a spinEx))
        (chiralUpperProj (psiCov b photonEy))
        (chiralUpperProj (psiCov c photonEz))) = 2 ∧
     cascadeTripleVolume (negVec3 spinEx) photonEy photonEz ≠
       cascadeTripleVolume spinEx photonEy photonEz) := by
  have hposet := ZornCascadeNode.poset_covering_chain
  have hvol_s := (chiralGated_three_vector_associator_eq_triple_volume a b c s e1 e2).2.2.1
  have hstr_s := (chiralGated_three_vector_associator_eq_triple_volume a b c s e1 e2).2.2.2
  have hvol_ns
  := (chiralGated_three_vector_associator_eq_triple_volume a b c (negVec3 s) e1 e2).2.2.1
  have hodd := (cascadeTripleVolume_odd_and_antisymmetric s e1 e2).1
  have hspin_neg :
      (associator
        (chiralUpperProj (psiCov a (negVec3 s)))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))).α =
      -(associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))).α := by
    rw [hvol_ns, hvol_s, hodd]
  have hbreak_α :
      (associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))).α ≠ 0 →
      cascadeTripleVolume (negVec3 s) e1 e2 ≠ cascadeTripleVolume s e1 e2 := by
    intro hne htsym
    apply hne
    rw [hvol_s]
    exact cascadeTripleVolume_time_reversal_forces_zero s e1 e2 htsym
  have hbreak_str :
      superTrace
        (associator
          (chiralUpperProj (psiCov a s))
          (chiralUpperProj (psiCov b e1))
          (chiralUpperProj (psiCov c e2))) ≠ 0 →
      cascadeTripleVolume (negVec3 s) e1 e2 ≠ cascadeTripleVolume s e1 e2 := by
    intro hne htsym
    apply hne
    rw [hstr_s, cascadeTripleVolume_time_reversal_forces_zero s e1 e2 htsym, mul_zero]
  have hwit_vol : cascadeTripleVolume spinEx photonEy photonEz = 1 := by
    simp [cascadeTripleVolume, spinEx, photonEy, photonEz, dot, cross]
  have hwit_str :
      superTrace
        (associator
          (chiralUpperProj (psiCov a spinEx))
          (chiralUpperProj (psiCov b photonEy))
          (chiralUpperProj (psiCov c photonEz))) = 2 := by
    rw [(chiralGated_three_vector_associator_eq_triple_volume a b c spinEx photonEy photonEz).2.2.2,
      hwit_vol]
    ring
  have hwit_break :
      cascadeTripleVolume (negVec3 spinEx) photonEy photonEz ≠
        cascadeTripleVolume spinEx photonEy photonEz := by
    simp [cascadeTripleVolume, negVec3, spinEx, photonEy, photonEz, dot, cross]
    norm_num
  exact ⟨hposet, hspin_neg, hbreak_α, hbreak_str, ⟨hwit_vol, hwit_str, hwit_break⟩⟩

/-!
## Section 7: Peirce Error-Correction, Scalar Identity Noise Invariance,
  Coplanar Crosstalk Rejection, & $\mathrm{SL}(3)$ Scaling Invariance

This section formalizes the 5-layer algebraic error-correction and decoherence-free subspace
mechanism of the Peirce-gated Zorn associator:
1. **Four-Sector Peirce Resolution of Identity (`zorn_peirce_idempotent_orthogonal_decomposition`):**
   Decomposes every `A : ZornNC R` into four mutually orthogonal idempotent Peirce sectors
   ($E_{11} A E_{11}$, $E_{11} A E_{22}$, $E_{22} A E_{11}$, $E_{22} A E_{22}$).
2. **Scalar Identity / Isotropic Background Noise Invariance (`zornAssociator_invariant_under_scalar_identity_noise`):**
   Adding arbitrary scalar multiples of the identity `scalarIdZorn c = ⟨c, 0, 0, c⟩` to any of the
   three Zorn states is annihilated by `chiralUpperProj` / `chiralLowerProj` and leaves the full
   four-sector Zorn associator `[A + c₁ I, B + c₂ I, C + c₃ I] = [A, B, C]` strictly invariant.
3. **Coplanar Crosstalk & Duplication Error-Correction (`zorn_peirce_coplanar_crosstalk_and_duplication_error_correction`):**
   Any duplicated or collinear vector channel vanishes identically (`[pureUpper u, pureUpper u,
  pureUpper v] = 0`, etc.),
   and adding any coplanar linear combination $\alpha\vec{e}_1 + \beta\vec{e}_2$ to $\vec{s}$ (or
   $\gamma\vec{e}_2$ to $\vec{e}_1$) leaves the 3-vector Zorn associator strictly unchanged.
4. **Racemic Cancellation vs. Opposite-Chirality Peirce Gating (`zorn_racemic_cancellation_vs_peirce_gating`):**
   Contrasts the ungated zero supertrace with the opposite-sign diagonal readouts of `chiralUpperProj`
   and `chiralLowerProj`, whose sum vanishes identically.
5. **Split-Torus Peirce Gauge Invariance & $\mathrm{SL}(3)$ Determinant-1 Scaling Invariance
   (`zorn_split_torus_peirce_gauge_invariance` & `zorn_sl3_det_one_scaling_invariance`):**
   Under anisotropic 3-axis calibration scaling $\vec{v} \mapsto (d_0 v_0, d_1 v_1, d_2 v_2)$,
   the 3-vector Zorn associator scales by the determinant $d_0 d_1 d_2$, and is strictly invariant
   whenever $d_0 d_1 d_2 = 1$ ($\mathrm{SL}(3)$ unimodular scaling).
-/

/-- Upper-left diagonal Peirce projection $E_{11} A E_{11}
  = \langle A.\alpha, 0, 0, 0 \rangle$ on `ZornNC R`. -/
def peirceUpperDiagProj {R : Type*} [Ring R] (A : ZornNC R) : ZornNC R :=
  ⟨A.α, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 0⟩

/-- Lower-right diagonal Peirce projection $E_{22} A E_{22}
  = \langle 0, 0, 0, A.\beta \rangle$ on `ZornNC R`. -/
def peirceLowerDiagProj {R : Type*} [Ring R] (A : ZornNC R) : ZornNC R :=
  ⟨0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, A.β⟩

/-- Scalar multiple of the Zorn identity $c \cdot I_2
  = \langle c, 0, 0, c \rangle$ in `ZornNC R`. -/
def scalarIdZorn {R : Type*} [Ring R] (c : R) : ZornNC R :=
  ⟨c, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, c⟩

/-- Componentwise addition on `Vec3 R`. -/
def addVec3 {R : Type*} [Ring R] (u v : NoncommutativeZornNambu.Vec3 R) :
    NoncommutativeZornNambu.Vec3 R :=
  ⟨u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2⟩

/-- Scalar multiplication on `Vec3 R`. -/
def smulVec3 {R : Type*} [Ring R] (c : R) (u : NoncommutativeZornNambu.Vec3 R) :
    NoncommutativeZornNambu.Vec3 R :=
  ⟨c * u.x0, c * u.x1, c * u.x2⟩

/-- Anisotropic 3-axis diagonal scaling $(d_0 v_0, d_1 v_1, d_2 v_2)$ on `Vec3 R`. -/
def scaleVec3 {R : Type*} [Ring R] (d v : NoncommutativeZornNambu.Vec3 R) :
    NoncommutativeZornNambu.Vec3 R :=
  ⟨d.x0 * v.x0, d.x1 * v.x1, d.x2 * v.x2⟩

/-- Determinant $d_0 d_1 d_2$ of the 3-axis diagonal scaling `scaleVec3 d`. -/
def detScaleVec3 {R : Type*} [Ring R] (d : NoncommutativeZornNambu.Vec3 R) : R :=
  d.x0 * d.x1 * d.x2

/-- **Layer 1 (`zorn_peirce_idempotent_orthogonal_decomposition`):**
The four Peirce sector projections (`peirceUpperDiagProj`, `chiralUpperProj`, `chiralLowerProj`,
`peirceLowerDiagProj`) are idempotent, pairwise orthogonal,
  sum to the identity on `ZornNC R`. -/
theorem zorn_peirce_idempotent_orthogonal_decomposition {R : Type*} [Ring R] (A : ZornNC R) :
    peirceUpperDiagProj (peirceUpperDiagProj A) = peirceUpperDiagProj A ∧
    peirceLowerDiagProj (peirceLowerDiagProj A) = peirceLowerDiagProj A ∧
    chiralUpperProj (peirceUpperDiagProj A) = (zeroZornNC : ZornNC R) ∧
    chiralUpperProj (peirceLowerDiagProj A) = (zeroZornNC : ZornNC R) ∧
    chiralLowerProj (peirceUpperDiagProj A) = (zeroZornNC : ZornNC R) ∧
    chiralLowerProj (peirceLowerDiagProj A) = (zeroZornNC : ZornNC R) ∧
    NoncommutativeZornNambu.add
      (NoncommutativeZornNambu.add (peirceUpperDiagProj A) (chiralUpperProj A))
      (NoncommutativeZornNambu.add (chiralLowerProj A) (peirceLowerDiagProj A)) = A := by
  cases A with
  | mk α x y β =>
    cases x
    cases y
    simp [peirceUpperDiagProj, peirceLowerDiagProj, chiralUpperProj, chiralLowerProj,
      pureUpper, pureLower, zeroZornNC, NoncommutativeZornNambu.add]

/-- **Layer 2 (`zornAssociator_invariant_under_scalar_identity_noise`):**
Over any commutative ring `R`, adding scalar identity noise `scalarIdZorn c` is completely
rejected by both off-diagonal Peirce projections (`chiralUpperProj`, `chiralLowerProj`) and leaves
the full four-sector Zorn associator strictly invariant. -/
theorem zornAssociator_invariant_under_scalar_identity_noise {R : Type*} [CommRing R]
    (A B C : ZornNC R) (c1 c2 c3 : R) :
    chiralUpperProj (NoncommutativeZornNambu.add A (scalarIdZorn c1)) = chiralUpperProj A ∧
    chiralLowerProj (NoncommutativeZornNambu.add A (scalarIdZorn c1)) = chiralLowerProj A ∧
    associator
      (NoncommutativeZornNambu.add A (scalarIdZorn c1))
      (NoncommutativeZornNambu.add B (scalarIdZorn c2))
      (NoncommutativeZornNambu.add C (scalarIdZorn c3)) =
      associator A B C := by
  cases A with
  | mk αA xA yA βA =>
    cases B with
    | mk αB xB yB βB =>
      cases C with
      | mk αC xC yC βC =>
        cases xA; cases yA; cases xB; cases yB; cases xC; cases yC
        refine ⟨?_, ?_, ?_⟩
        · simp [chiralUpperProj, pureUpper, scalarIdZorn, NoncommutativeZornNambu.add]
        · simp [chiralLowerProj, pureLower, scalarIdZorn, NoncommutativeZornNambu.add]
        · simp [NoncommutativeZornNambu.associator, NoncommutativeZornNambu.mul,
            NoncommutativeZornNambu.sub, NoncommutativeZornNambu.add, scalarIdZorn, dot, cross]
          refine ⟨by ring, ⟨by ring, by ring, by ring⟩, ⟨by ring, by ring, by ring⟩, by ring⟩

/-- **Layer 3 (`zorn_peirce_coplanar_crosstalk_and_duplication_error_correction`):**
Over any commutative ring `R`, the Peirce-gated 3-vector Zorn associator annihilates any
duplicated vector channel (`u, u, v`, `u, v, u`, or `v, u, u`) and is strictly invariant under
coplanar crosstalk $\vec{s} \mapsto \vec{s} + \alpha\vec{e}_1 + \beta\vec{e}_2$,
$\vec{e}_1 \mapsto \vec{e}_1 + \gamma\vec{e}_2$. -/
theorem zorn_peirce_coplanar_crosstalk_and_duplication_error_correction {R : Type*} [CommRing R]
    (u v s e1 e2 : NoncommutativeZornNambu.Vec3 R) (α β γ : R) :
    associator (pureUpper u) (pureUpper u) (pureUpper v) = (zeroZornNC : ZornNC R) ∧
    associator (pureUpper u) (pureUpper v) (pureUpper u) = (zeroZornNC : ZornNC R) ∧
    associator (pureUpper v) (pureUpper u) (pureUpper u) = (zeroZornNC : ZornNC R) ∧
    associator
      (pureUpper (addVec3 s (addVec3 (smulVec3 α e1) (smulVec3 β e2))))
      (pureUpper (addVec3 e1 (smulVec3 γ e2)))
      (pureUpper e2) =
      associator (pureUpper s) (pureUpper e1) (pureUpper e2) := by
  cases u; cases v; cases s; cases e1; cases e2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [pureUpper_three_vector_associator, zeroZornNC, dot, cross]
    constructor <;> ring
  · simp [pureUpper_three_vector_associator, zeroZornNC, dot, cross]
    constructor <;> ring
  · simp [pureUpper_three_vector_associator, zeroZornNC, dot, cross]
    constructor <;> ring
  · simp [pureUpper_three_vector_associator, addVec3, smulVec3, dot, cross]
    constructor <;> ring

/-- **Layer 4 (`zorn_racemic_cancellation_vs_peirce_gating`):**
Over any commutative ring `R`, for any three covariant states `psiCov a s`, `psiCov b e1`,
`psiCov c e2`:
1. The ungated 3-state associator has zero supertrace;
2. The upper Peirce-gated associator has diagonal `(Ω, -Ω)` and supertrace `2Ω`;
3. The lower Peirce-gated associator has opposite diagonal `(-Ω, Ω)` and supertrace `-2Ω`;
4. The sum of the upper
  lower Peirce-gated 3-vector associators cancels identically to `zeroZornNC`. -/
theorem zorn_racemic_cancellation_vs_peirce_gating {R : Type*} [CommRing R]
    (a b c : R) (s e1 e2 : NoncommutativeZornNambu.Vec3 R) :
    superTrace (associator (psiCov a s) (psiCov b e1) (psiCov c e2)) = 0 ∧
    associator
      (chiralUpperProj (psiCov a s))
      (chiralUpperProj (psiCov b e1))
      (chiralUpperProj (psiCov c e2)) =
      ⟨cascadeTripleVolume s e1 e2, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -cascadeTripleVolume s e1 e2⟩ ∧
    associator
      (chiralLowerProj (psiCov a s))
      (chiralLowerProj (psiCov b e1))
      (chiralLowerProj (psiCov c e2)) =
      ⟨-cascadeTripleVolume s e1 e2, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, cascadeTripleVolume s e1 e2⟩ ∧
    NoncommutativeZornNambu.add
      (associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2)))
      (associator
        (chiralLowerProj (psiCov a s))
        (chiralLowerProj (psiCov b e1))
        (chiralLowerProj (psiCov c e2))) = (zeroZornNC : ZornNC R) := by
  have hup := chiralGated_three_vector_associator_eq_triple_volume a b c s e1 e2
  have hlow :
      associator
        (chiralLowerProj (psiCov a s))
        (chiralLowerProj (psiCov b e1))
        (chiralLowerProj (psiCov c e2)) =
        ⟨-cascadeTripleVolume s e1 e2, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, cascadeTripleVolume s e1 e2⟩ := by
    rw [(chiralProj_psiCov_pair a s).2, (chiralProj_psiCov_pair b e1).2,
      (chiralProj_psiCov_pair c e2).2]
    cases s; cases e1; cases e2
    simp [NoncommutativeZornNambu.associator, NoncommutativeZornNambu.mul,
      NoncommutativeZornNambu.sub, pureLower, cascadeTripleVolume, dot, cross]
    ring
  refine ⟨hup.1, hup.2.1, hlow, ?_⟩
  rw [hup.2.1, hlow]
  simp [NoncommutativeZornNambu.add, zeroZornNC]

/-- **Layer 5A (`zorn_split_torus_peirce_gauge_invariance`):**
Combines the split Cartan torus gauge invariance of `canonicalZornAssociator` on `CanonicalZorn`
with the Klein-bottle orientation-reversing glide-reflection law $\tau_{\mathrm{Klein}} \circ T_t \circ \tau_{\mathrm{Klein}} = T_{t^{-1}}$. -/
theorem zorn_split_torus_peirce_gauge_invariance
    (t : ℝ) (ht : t ≠ 0) (X Y Z : CanonicalZorn) :
    canonicalKleinSwap (torusMap t (canonicalKleinSwap X)) = torusMap t⁻¹ X ∧
    (canonicalZornAssociator (torusMap t X) (torusMap t Y) (torusMap t Z)).a =
      (canonicalZornAssociator X Y Z).a ∧
    (canonicalZornAssociator (torusMap t X) (torusMap t Y) (torusMap t Z)).b =
      (canonicalZornAssociator X Y Z).b ∧
    canonicalZornSuperTrace
      (canonicalZornAssociator (torusMap t X) (torusMap t Y) (torusMap t Z)) =
      canonicalZornSuperTrace (canonicalZornAssociator X Y Z) := by
  have htor := torusMap_associator_diagonal_and_superTrace_invariant t ht X Y Z
  exact ⟨canonicalKleinSwap_torusMap_inversion t X, htor.1, htor.2.1, htor.2.2⟩

/-- **Layer 5B (`zorn_sl3_det_one_scaling_invariance`):**
Over any commutative ring `R`, under 3-axis diagonal scaling `scaleVec3 d`, the scalar triple
product `cascadeTripleVolume` and the upper Peirce-gated Zorn associator scale by the determinant
`detScaleVec3 d = d.x0 * d.x1 * d.x2`. Consequently, for any unimodular scaling matrix in
$\mathrm{SL}(3, R)$ (`hdet : detScaleVec3 d = 1`), the upper Peirce-gated Zorn associator and its
chiral supertrace are strictly invariant. -/
theorem zorn_sl3_det_one_scaling_invariance {R : Type*} [CommRing R]
    (d s e1 e2 : NoncommutativeZornNambu.Vec3 R) (hdet : detScaleVec3 d = 1) :
    cascadeTripleVolume (scaleVec3 d s) (scaleVec3 d e1) (scaleVec3 d e2) =
      detScaleVec3 d * cascadeTripleVolume s e1 e2 ∧
    cascadeTripleVolume (scaleVec3 d s) (scaleVec3 d e1) (scaleVec3 d e2) =
      cascadeTripleVolume s e1 e2 ∧
    associator
      (pureUpper (scaleVec3 d s))
      (pureUpper (scaleVec3 d e1))
      (pureUpper (scaleVec3 d e2)) =
      associator (pureUpper s) (pureUpper e1) (pureUpper e2) ∧
    superTrace
      (associator
        (pureUpper (scaleVec3 d s))
        (pureUpper (scaleVec3 d e1))
        (pureUpper (scaleVec3 d e2))) =
      superTrace (associator (pureUpper s) (pureUpper e1) (pureUpper e2)) := by
  have hscale :
      cascadeTripleVolume (scaleVec3 d s) (scaleVec3 d e1) (scaleVec3 d e2) =
        detScaleVec3 d * cascadeTripleVolume s e1 e2 := by
    cases d; cases s; cases e1; cases e2
    simp [cascadeTripleVolume, scaleVec3, detScaleVec3, dot, cross]
    ring
  have hvol1 :
      cascadeTripleVolume (scaleVec3 d s) (scaleVec3 d e1) (scaleVec3 d e2) =
        cascadeTripleVolume s e1 e2 := by
    rw [hscale, hdet, one_mul]
  have hassoc :
      associator
        (pureUpper (scaleVec3 d s))
        (pureUpper (scaleVec3 d e1))
        (pureUpper (scaleVec3 d e2)) =
        associator (pureUpper s) (pureUpper e1) (pureUpper e2) := by
    have hup1 :=
      (chiralGated_three_vector_associator_eq_triple_volume 0 0 0
        (scaleVec3 d s) (scaleVec3 d e1) (scaleVec3 d e2)).2.1
    have hup2 :=
      (chiralGated_three_vector_associator_eq_triple_volume 0 0 0 s e1 e2).2.1
    simp only [chiralProj_psiCov_pair] at hup1 hup2
    rw [hup1, hup2, hvol1]
  refine ⟨hscale, hvol1, hassoc, ?_⟩
  rw [hassoc]

end InfoGeometry.Algebra.Zorn.ZeemanChiralGatedAssociatorPoset
