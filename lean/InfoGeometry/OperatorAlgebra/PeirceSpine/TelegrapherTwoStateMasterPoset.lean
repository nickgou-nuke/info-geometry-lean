/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorBogoliubovSpinePoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.OperatorTimeArchetypes
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorFifthChargeClosure
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorCrossGradeBrackets
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceTetradPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.CayleyDicksonHopfPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.GolayLeechMOGSheetPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ConeSheetBraiding
import InfoGeometry.OperatorAlgebra.PeirceSpine.PhaseConjugateSteinberg
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParityDoubleDerivation
import InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator
import InfoGeometry.OperatorAlgebra.PeirceSpine.HomogenizedKernels
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectLevelExclusions
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradedDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.WilsonPlaquette
import InfoGeometry.OperatorAlgebra.PeirceSpine.LogarithmicPullback
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdealChartPairing
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlockTriangularIntervention
import InfoGeometry.OperatorAlgebra.PeirceSpine.PlabicKleinActionBridge

set_option maxHeartbeats 2000000

/-!
# Archetypes `A₇₀ → A₈₂` & Unified 82-Stage Master Causal Poset (`A₁ → A₈₂`)

This module extends the 58-stage non-commutative Peirce–Kantor–Bogoliubov spine
(`NonCommutativeSpineStage : A₁ → A₅₈`) across:
- **`A₅₉–A₆₀` (`ZornPeirceTetradPoset`):** Oliveira–Maia split Cayley / Zorn–Peirce matrix algebra,
  block multiplication, Zorn quadratic norm, and complex tetrad symmetric/skew decomposition;
- **`A₆₁–A₆₉` (`GolayLeechMOGSheetPoset`, `KantorFifthChargeClosure`, `KantorCrossGradeBrackets`):**
  Scale-12/24 Kantor–Peirce charge frames, fifth-order charge closure `Δ_P⁵ - 5 Δ_P³ + 4 Δ_P = 0`,
  cross-grade brackets, Scale-144/576 bilateral compressions, all-scale `(k, n) ∈ ℕ × ℕ` single-sheet
  decoders (`mog24SheetPlus`, `mog24SheetMinus`), and all-mode Virasoro–Sugawara ladder;
- **Tier 1 (`A₇₀ → A₇₆`):**
  - `A₇₀`: Defect-scaled cone nilpotency, handshake sum, cubic relations for `Φ δ^[n](V)` and
    `J δ^[n](V)`, and multipass `sandwichSame` defect isolation;
  - `A₇₁`: Single-pass and double-pass unipotent shear conjugation of `Φ`, parity-conjugate
    round-trip cancellation, and `sandwichSame` invariance under even `V + Σ` shifts;
  - `A₇₂`: Dual Steinberg braid parity conjugation, palindromic Steinberg round-trip, and Bruhat
    two-factor parity conjugation;
  - `A₇₃`: Parity-derivation intertwining of `derivSqPhi` and `derivSqJ` and all-depth
    commutator-product factorization `comm P (Φ δ^[n](V)) * (Φ δ^[n](V)) = Σ (δ^[n](V))²`;
  - `A₇₄`: Second-order telegrapher relation `(L² + 4 V L - 4 V²)(Φ) = 0` and
    `(L² + 4 V L - 4 V²)(J) = 0` for `L = curvatureDoubleCommutator P A C`, plus right-multiplication
    equivariance by `δ^[n](V)`;
  - `A₇₅`: All-depth action of `curvatureDoubleCommutator` on even defect iterates (`δ^[n](V)` and
    `qgtDefectDiff P A C n`) and chiral eigenvalue splitting;
  - `A₇₆`: All-depth telegrapher quadratic relation for odd defect modes `Φ δ^[n](V)` and
    `J δ^[n](V)`, 4th-order master metriplectic polynomial `metriplecticMasterPoly4Op P_k A C` across
    all `(k, n) ∈ ℕ × ℕ`, and all-mode `r ∈ ℕ` single-sheet Drinfeld–Virasoro decoding under
    `golay24G0`, `mog24SheetPlus`, and `mog24SheetMinus`;
- **Tier 2 (`A₇₇ → A₈₂`):**
  - `A₇₇`: Non-injectivity of the four homogenized channels (`hProjV`, `hProjPhi`, `hProjJ`,
    `hProjSig`) on any `[Nontrivial B]` and unit-defect level-set exclusions;
  - `A₇₈`: Graded idempotency defect split, odd perturbation square-zero criterion, and ordered
    parity-product commutator identity;
  - `A₇₉`: Ordered Peirce Wilson plaquette expansions (`wilsonPlaquette`, `wilsonPlaquetteRev`) with
    symmetric even part `-V²`, and logarithmic Bruhat corner pullbacks;
  - `A₈₀`: All-depth two-state local chart sandwiches `(P - N_+) · (P + N_-)` on single-sheet
    iterates `δ^[n](Q_±)` and odd defect modes `Φ δ^[n](V)` and `J δ^[n](V)`;
  - `A₈₁`: Star-reversal and grading-twisted anti-involution `X ↦ S X^⋆ S`, principal-ideal Peirce
    splittings, and opposite graph chart triple products;
  - `A₈₂`: All-depth two-state local chart sandwiches on `δ^[n](V)` and `qgtDefectDiff P A C n`,
    Euler-compression residual, and all-depth block-lower triangular closure `tcrDecoderFullOp`
    with orthogonal idempotent compression.

All statements are ring and star-ring identities with zero `sorry`s and zero custom axioms.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

/-! ### Part 1: Unified 124-Stage Master Causal Poset (`A₁ → A₁₂₄`) -/

/-- The 124 canonical non-commutative operator archetypes (`A₁` through `A₁₂₄`), ordered in a
strictly rank-monotone causal poset extending `NonCommutativeSpineStage` (`A₁ → A₅₈`). -/
inductive MasterSpineStage : Type
  | A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8 | A9 | A10
  | A11 | A12 | A13 | A14 | A15 | A16 | A17 | A18 | A19 | A20
  | A21 | A22 | A23 | A24 | A25 | A26 | A27 | A28 | A29 | A30
  | A31 | A32 | A33 | A34 | A35 | A36 | A37 | A38 | A39 | A40
  | A41 | A42 | A43 | A44 | A45 | A46 | A47 | A48 | A49 | A50
  | A51 | A52 | A53 | A54 | A55 | A56 | A57 | A58
  | A59 | A60 | A61 | A62 | A63 | A64 | A65 | A66 | A67 | A68 | A69
  | A70 | A71 | A72 | A73 | A74 | A75 | A76
  | A77 | A78 | A79 | A80 | A81 | A82
  | A83 | A84 | A85 | A86 | A87 | A88
  | A89 | A90 | A91 | A92 | A93 | A94
  | A95 | A96 | A97 | A98 | A99
  | A100 | A101 | A102 | A103 | A104
  | A105 | A106 | A107 | A108 | A109
  | A110 | A111 | A112 | A113 | A114
  | A115 | A116 | A117 | A118 | A119
  | A120 | A121 | A122 | A123 | A124
  deriving DecidableEq, Repr

namespace MasterSpineStage

/-- Topological rank `1..124` of each archetype stage in `MasterSpineStage`. -/
def rank : MasterSpineStage → ℕ
  | A1 => 1   | A2 => 2   | A3 => 3   | A4 => 4   | A5 => 5
  | A6 => 6   | A7 => 7   | A8 => 8   | A9 => 9   | A10 => 10
  | A11 => 11 | A12 => 12 | A13 => 13 | A14 => 14 | A15 => 15
  | A16 => 16 | A17 => 17 | A18 => 18 | A19 => 19 | A20 => 20
  | A21 => 21 | A22 => 22 | A23 => 23 | A24 => 24 | A25 => 25
  | A26 => 26 | A27 => 27 | A28 => 28 | A29 => 29 | A30 => 30
  | A31 => 31 | A32 => 32 | A33 => 33 | A34 => 34 | A35 => 35
  | A36 => 36 | A37 => 37 | A38 => 38 | A39 => 39 | A40 => 40
  | A41 => 41 | A42 => 42 | A43 => 43 | A44 => 44 | A45 => 45
  | A46 => 46 | A47 => 47 | A48 => 48 | A49 => 49 | A50 => 50
  | A51 => 51 | A52 => 52 | A53 => 53 | A54 => 54 | A55 => 55
  | A56 => 56 | A57 => 57 | A58 => 58
  | A59 => 59 | A60 => 60 | A61 => 61 | A62 => 62 | A63 => 63
  | A64 => 64 | A65 => 65 | A66 => 66 | A67 => 67 | A68 => 68 | A69 => 69
  | A70 => 70 | A71 => 71 | A72 => 72 | A73 => 73 | A74 => 74
  | A75 => 75 | A76 => 76
  | A77 => 77 | A78 => 78 | A79 => 79 | A80 => 80 | A81 => 81 | A82 => 82
  | A83 => 83 | A84 => 84 | A85 => 85 | A86 => 86 | A87 => 87 | A88 => 88
  | A89 => 89 | A90 => 90 | A91 => 91 | A92 => 92 | A93 => 93 | A94 => 94
  | A95 => 95 | A96 => 96 | A97 => 97 | A98 => 98 | A99 => 99
  | A100 => 100 | A101 => 101 | A102 => 102 | A103 => 103 | A104 => 104
  | A105 => 105 | A106 => 106 | A107 => 107 | A108 => 108 | A109 => 109
  | A110 => 110 | A111 => 111 | A112 => 112 | A113 => 113 | A114 => 114
  | A115 => 115 | A116 => 116 | A117 => 117 | A118 => 118 | A119 => 119
  | A120 => 120 | A121 => 121 | A122 => 122 | A123 => 123 | A124 => 124

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

instance : LinearOrder MasterSpineStage :=
  LinearOrder.lift' rank rank_injective

/-- Canonical order-embedding of the 58-stage spine `NonCommutativeSpineStage` (`A₁ → A₅₈`)
into the 82-stage master poset `MasterSpineStage` (`A₁ → A₈₂`). -/
def ofSpine58 : NonCommutativeSpineStage → MasterSpineStage
  | .A1 => A1   | .A2 => A2   | .A3 => A3   | .A4 => A4   | .A5 => A5
  | .A6 => A6   | .A7 => A7   | .A8 => A8   | .A9 => A9   | .A10 => A10
  | .A11 => A11 | .A12 => A12 | .A13 => A13 | .A14 => A14 | .A15 => A15
  | .A16 => A16 | .A17 => A17 | .A18 => A18 | .A19 => A19 | .A20 => A20
  | .A21 => A21 | .A22 => A22 | .A23 => A23 | .A24 => A24 | .A25 => A25
  | .A26 => A26 | .A27 => A27 | .A28 => A28 | .A29 => A29 | .A30 => A30
  | .A31 => A31 | .A32 => A32 | .A33 => A33 | .A34 => A34 | .A35 => A35
  | .A36 => A36 | .A37 => A37 | .A38 => A38 | .A39 => A39 | .A40 => A40
  | .A41 => A41 | .A42 => A42 | .A43 => A43 | .A44 => A44 | .A45 => A45
  | .A46 => A46 | .A47 => A47 | .A48 => A48 | .A49 => A49 | .A50 => A50
  | .A51 => A51 | .A52 => A52 | .A53 => A53 | .A54 => A54 | .A55 => A55
  | .A56 => A56 | .A57 => A57 | .A58 => A58

theorem rank_ofSpine58 (s : NonCommutativeSpineStage) :
    (ofSpine58 s).rank = s.rank + 1 := by
  cases s <;> rfl

theorem ofSpine58_strictMono : StrictMono ofSpine58 := by
  intro a b hab
  change (ofSpine58 a).rank < (ofSpine58 b).rank
  rw [rank_ofSpine58, rank_ofSpine58]
  change a.rank < b.rank at hab
  omega

/-- Directed causal dependency edges of the 82-stage master poset `A₁ → A₈₂`. -/
def causalEdge (a b : MasterSpineStage) : Prop :=
  a.rank < b.rank

theorem causalEdge_strict_rank_mono {a b : MasterSpineStage}
    (h : causalEdge a b) : rank a < rank b := h

theorem causalEdge_irrefl (a : MasterSpineStage) : ¬ causalEdge a a :=
  Nat.lt_irrefl a.rank

theorem transGen_causalEdge_strict_rank_mono {a b : MasterSpineStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact hab
  | tail _ hbc ih => exact lt_trans ih hbc

theorem causalEdge_acyclic (a : MasterSpineStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl a.rank (transGen_causalEdge_strict_rank_mono h)

end MasterSpineStage

/-! ### Part 2: Tier 1 Canonical Synthesis Theorems (`A₇₀ → A₇₆`) -/

section Tier1

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

/-- **Archetype `A₇₀` (`archetype_A70_defect_cone_echo_cubic_and_multipass_sandwich`):**
At every defect depth `n : ℕ`:
1. The defect-scaled Peirce cones `N_+ δ^[n](V)` and `N_- δ^[n](V)` are square-zero and satisfy
   the handshake sum `(N_+ δ^[n](V)) N_- + (N_- δ^[n](V)) N_+ = V δ^[n](V)`;
2. The odd defect-scaled generators `Φ δ^[n](V)` and `J δ^[n](V)` satisfy the cubic identities
   `(Φ δ^[n](V))³ = (V Φ) (δ^[n](V))³` and `(J δ^[n](V))³ = -(V J) (δ^[n](V))³`;
3. Multipass evaluation of `sandwichSame P A C` on `N_+`, `N_-`, and `Φ` isolates the
   idempotency defect `-idempotencyDefect (genV P A C)`. -/
theorem archetype_A70_defect_cone_echo_cubic_and_multipass_sandwich
    (A C : B) (n : ℕ) :
    ((conePlus P A * idempotencyDefect^[n] (genV P A C)) *
        (conePlus P A * idempotencyDefect^[n] (genV P A C)) = 0 ∧
     (coneMinus P C * idempotencyDefect^[n] (genV P A C)) *
        (coneMinus P C * idempotencyDefect^[n] (genV P A C)) = 0 ∧
     (conePlus P A * idempotencyDefect^[n] (genV P A C)) * coneMinus P C +
        (coneMinus P C * idempotencyDefect^[n] (genV P A C)) * conePlus P A =
      genV P A C * idempotencyDefect^[n] (genV P A C) ∧
     (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
        (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
        (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
      (genV P A C * genPhi P A C) *
        (idempotencyDefect^[n] (genV P A C) *
          idempotencyDefect^[n] (genV P A C) *
          idempotencyDefect^[n] (genV P A C)) ∧
     (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
        (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
        (genJ P A C * idempotencyDefect^[n] (genV P A C)) =
      -((genV P A C * genJ P A C) *
        (idempotencyDefect^[n] (genV P A C) *
          idempotencyDefect^[n] (genV P A C) *
          idempotencyDefect^[n] (genV P A C)))) ∧
    (sandwichSame P A C (coneMinus P C) -
        sandwichSame P A C (sandwichSame P A C (conePlus P A)) =
      -(idempotencyDefect (genV P A C) * conePlus P A) ∧
     sandwichSame P A C (conePlus P A) -
        sandwichSame P A C (sandwichSame P A C (coneMinus P C)) =
      -(idempotencyDefect (genV P A C) * coneMinus P C) ∧
     sandwichSame P A C (genPhi P A C) -
        sandwichSame P A C (sandwichSame P A C (genPhi P A C)) =
      -(idempotencyDefect (genV P A C) * genPhi P A C)) :=
  ⟨qgt_defect_iterates_cone_echo_and_cubic hP A C n,
   sandwichSame_multipass_idempotencyDefect hP A C⟩

/-- **Archetype `A₇₁` (`archetype_A71_unipotent_double_pass_and_parity_round_trip`):**
Single-pass and double-pass upper unipotent shear conjugation of `genPhi`, parity-conjugate
round-trip cancellation for upper and lower unipotent shears, and invariance of `sandwichSame`
under even `genV + genSig` shifts. -/
theorem archetype_A71_unipotent_double_pass_and_parity_round_trip
    (A C X : B) :
    (1 + conePlus P A) * genPhi P A C * (1 - conePlus P A) =
      genPhi P A C + genSig P A C -
        conePlus P A * coneMinus P C * conePlus P A ∧
    (1 + conePlus P A) *
        ((1 + conePlus P A) * genPhi P A C * (1 - conePlus P A)) *
        (1 - conePlus P A) =
      genPhi P A C + (2 : ℤ) • genSig P A C -
        (4 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A) ∧
    parityConj P
      ((1 + conePlus P A) *
        parityConj P ((1 + conePlus P A) * X * (1 - conePlus P A)) *
        (1 - conePlus P A)) = X ∧
    parityConj P
      ((1 + coneMinus P C) *
        parityConj P ((1 + coneMinus P C) * X * (1 - coneMinus P C)) *
        (1 - coneMinus P C)) = X ∧
    sandwichSame P A C (X + genV P A C + genSig P A C) =
      sandwichSame P A C X :=
  unipotentPlus_double_pass_and_parityConj_round_trip hP A C X

/-- **Archetype `A₇₂` (`archetype_A72_dual_steinberg_braid_and_bruhat_parity`):**
Parity conjugation of the upper and dual Steinberg braids to their inverses, palindromic
Steinberg braid round-trip cancellation, and Bruhat two-factor parity conjugation. -/
theorem archetype_A72_dual_steinberg_braid_and_bruhat_parity
    (A C X : B) :
    parityConj P (steinbergBraid P A C) = steinbergBraidInv P A C ∧
    parityConj P
      (steinbergBraid P A C *
        parityConj P (steinbergBraid P A C * X * steinbergBraidInv P A C) *
        steinbergBraidInv P A C) = X ∧
    parityConj P (steinbergBraidDual P A C) = steinbergBraidDualInv P A C ∧
    parityConj P ((1 + conePlus P A) * (1 - coneMinus P C)) =
      (1 - conePlus P A) * (1 + coneMinus P C) ∧
    parityConj P ((1 + coneMinus P C) * (1 - conePlus P A)) =
      (1 - coneMinus P C) * (1 + conePlus P A) := by
  rcases parityConj_steinbergBraidDual_and_bruhat_factors hP A C with ⟨hD, hB1, hB2⟩
  exact ⟨parityConj_steinbergBraid hP A C,
         parityConj_steinberg_round_trip hP A C X,
         hD, hB1, hB2⟩

/-- **Archetype `A₇₃` (`archetype_A73_parity_double_derivation_intertwining_and_vorticity_factorization`):**
1. The Peirce grading commutator `comm P` intertwines the signed second derivations `derivSqPhi`
   and `derivSqJ` across all `X : B`;
2. At every defect depth `n : ℕ`, `comm P` exchanges `Φ δ^[n](V)` and `J δ^[n](V)` and satisfies
   the commutator-product factorization `comm P (Φ δ^[n](V)) * (Φ δ^[n](V)) = Σ (δ^[n](V))²`. -/
theorem archetype_A73_parity_double_derivation_intertwining_and_vorticity_factorization
    (A C X : B) (n : ℕ) :
    comm P (derivSqPhi P A C X) = derivSqJ P A C (comm P X) ∧
    comm P (derivSqJ P A C X) = derivSqPhi P A C (comm P X) ∧
    comm P (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
      genJ P A C * idempotencyDefect^[n] (genV P A C) ∧
    comm P (genJ P A C * idempotencyDefect^[n] (genV P A C)) =
      genPhi P A C * idempotencyDefect^[n] (genV P A C) ∧
    comm P (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
        (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
      genSig P A C *
        (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) := by
  rcases madelung_vorticity_factorization_defect_iterates hP A C n with ⟨h1, h2, h3⟩
  exact ⟨peirce_comm_derivSqPhi_intertwines_J hP A C X,
         peirce_comm_derivSqJ_intertwines_Phi hP A C X,
         h1, h2, h3⟩

/-- **Archetype `A₇₄` (`archetype_A74_telegrapher_quadratic_curvature_double_commutator`):**
The curvature double commutator `L(X) = curvatureDoubleCommutator P A C X = [Σ, X] + derivSqPhi(X)`
satisfies:
1. The second-order telegrapher relation `(L² + 4 V L - 4 V²)(Φ) = 0` and
   `(L² + 4 V L - 4 V²)(J) = 0`;
2. Right-multiplication equivariance `L(X * δ^[n](V)) = L(X) * δ^[n](V)` and
   `metriplecticMasterPoly4Op P A C (X * δ^[n](V)) = metriplecticMasterPoly4Op P A C X * δ^[n](V)`
   for every `X : B` and defect depth `n : ℕ`. -/
theorem archetype_A74_telegrapher_quadratic_curvature_double_commutator
    (A C X : B) (n : ℕ) :
    metriplecticTelegrapher P A C (genPhi P A C) = 0 ∧
    metriplecticTelegrapher P A C (genJ P A C) = 0 ∧
    curvatureDoubleCommutator P A C (X * idempotencyDefect^[n] (genV P A C)) =
      curvatureDoubleCommutator P A C X * idempotencyDefect^[n] (genV P A C) ∧
    metriplecticMasterPoly4Op P A C (X * idempotencyDefect^[n] (genV P A C)) =
      metriplecticMasterPoly4Op P A C X * idempotencyDefect^[n] (genV P A C) :=
  ⟨curvatureDoubleCommutator_quadratic_phi hP A C,
   curvatureDoubleCommutator_quadratic_j hP A C,
   curvatureDoubleCommutator_mul_genV_defect_iterate hP A C X n,
   metriplecticMasterPoly4Op_mul_genV_defect_iterate hP A C X n⟩

/-- **Archetype `A₇₅` (`archetype_A75_even_defect_telegrapher_and_chiral_eigenvalues`):**
At every defect depth `n : ℕ`:
1. `curvatureDoubleCommutator P A C` annihilates `δ^[n](V)` and acts on `qgtDefectDiff P A C n`
   by `-4 V`;
2. `genSig P A C` and `genV P A C` satisfy the chiral eigenvalue and sheet-annihilation identities
   on `δ^[n](Q_+)`, `δ^[n](Q_-)`, `δ^[n](V)`, and `qgtDefectDiff P A C n`;
3. `sandwichCross P A C` swaps the upper and lower defect sheets (`δ^[n](Q_±) ↦ V δ^[n](Q_∓)`)
   and acts by `+V` on `δ^[n](V)` and `-V` on `qgtDefectDiff P A C n`. -/
theorem archetype_A75_even_defect_telegrapher_and_chiral_eigenvalues
    (A C : B) (n : ℕ) :
    (curvatureDoubleCommutator P A C (idempotencyDefect^[n] (genV P A C)) = 0 ∧
     curvatureDoubleCommutator P A C (qgtDefectDiff P A C n) +
       (4 : ℤ) • (genV P A C * qgtDefectDiff P A C n) = 0) ∧
    (genSig P A C * idempotencyDefect^[n] (qgtPlus P A C) =
       genV P A C * idempotencyDefect^[n] (qgtPlus P A C) ∧
     genSig P A C * idempotencyDefect^[n] (qgtMinus P A C) =
       -(genV P A C * idempotencyDefect^[n] (qgtMinus P A C)) ∧
     (genV P A C - genSig P A C) * idempotencyDefect^[n] (qgtPlus P A C) = 0 ∧
     (genV P A C + genSig P A C) * idempotencyDefect^[n] (qgtMinus P A C) = 0 ∧
     genSig P A C * qgtDefectDiff P A C n =
       genV P A C * idempotencyDefect^[n] (genV P A C) ∧
     genSig P A C * idempotencyDefect^[n] (genV P A C) =
       genV P A C * qgtDefectDiff P A C n) ∧
    (sandwichCross P A C (idempotencyDefect^[n] (qgtPlus P A C)) =
       genV P A C * idempotencyDefect^[n] (qgtMinus P A C) ∧
     sandwichCross P A C (idempotencyDefect^[n] (qgtMinus P A C)) =
       genV P A C * idempotencyDefect^[n] (qgtPlus P A C) ∧
     sandwichCross P A C (idempotencyDefect^[n] (genV P A C)) =
       genV P A C * idempotencyDefect^[n] (genV P A C) ∧
     sandwichCross P A C (qgtDefectDiff P A C n) =
       -(genV P A C * qgtDefectDiff P A C n)) :=
  ⟨curvatureDoubleCommutator_even_defect_iterates hP A C n,
   qgt_defect_iterates_chiral_eigenvalues hP A C n,
   qgt_defect_iterates_sandwichCross hP A C n⟩

/-- Right-multiplication by `opPow r (genV P A C)` commutes with `golay24G0`, `mog24V`, `mog24Sig`,
`mog24SheetPlus`, and `mog24SheetMinus` for every mode index `r : ℕ`. -/
theorem golay24_and_mog24_sheet_mul_opPow_genV
    (A C X : B) (r : ℕ) :
    let Z := opPow r (genV P A C)
    golay24G0 P A C (X * Z) = golay24G0 P A C X * Z ∧
    mog24V P A C (X * Z) = mog24V P A C X * Z ∧
    mog24Sig P A C (X * Z) = mog24Sig P A C X * Z ∧
    mog24SheetPlus P A C (X * Z) = mog24SheetPlus P A C X * Z ∧
    mog24SheetMinus P A C (X * Z) = mog24SheetMinus P A C X * Z := by
  intro Z
  rcases opPow_genV_comm_invS_and_cones hP A C r with ⟨_, hCp, hCm⟩
  have hPhi : genPhi P A C * Z = Z * genPhi P A C := by
    unfold genPhi; rw [add_mul, mul_add, hCp, hCm]
  have hJ : genJ P A C * Z = Z * genJ P A C := by
    unfold genJ; rw [sub_mul, mul_sub, hCp, hCm]
  have hSig : genSig P A C * Z = Z * genSig P A C := by
    have hJP : genSig P A C = genJ P A C * genPhi P A C := by peirce_nf hP
    rw [hJP, mul_assoc, hPhi, ← mul_assoc, hJ, mul_assoc]
  have hComm : ∀ G : B, G * Z = Z * G → ∀ Y : B, comm G (Y * Z) = comm G Y * Z := by
    intro G hGZ Y
    unfold comm
    calc G * (Y * Z) - (Y * Z) * G
      _ = (G * Y) * Z - Y * (Z * G) := by simp only [mul_assoc]
      _ = (G * Y) * Z - Y * (G * Z) := by rw [← hGZ]
      _ = (G * Y - Y * G) * Z := by simp only [sub_mul, mul_assoc]
  have hDPhi : derivSqPhi P A C (X * Z) = derivSqPhi P A C X * Z := by
    unfold derivSqPhi
    rw [hComm (genPhi P A C) hPhi X, hComm (genPhi P A C) hPhi (comm (genPhi P A C) X), neg_mul]
  have hDJ : derivSqJ P A C (X * Z) = derivSqJ P A C X * Z := by
    unfold derivSqJ
    rw [hComm (genJ P A C) hJ X, hComm (genJ P A C) hJ (comm (genJ P A C) X)]
  have hDSig : derivSqSig P A C (X * Z) = derivSqSig P A C X * Z := by
    unfold derivSqSig
    rw [hComm (genSig P A C) hSig X, hComm (genSig P A C) hSig (comm (genSig P A C) X), neg_mul]
  have hHV : hProjV P A C (X * Z) = hProjV P A C X * Z := by
    unfold hProjV
    rw [hDPhi, hDJ, hDSig]
    simp only [add_mul, smul_mul_assoc, mul_assoc]
  have hHSig : hProjSig P A C (X * Z) = hProjSig P A C X * Z := by
    unfold hProjSig
    rw [hDPhi, hDJ, hDSig]
    simp only [sub_mul, mul_assoc]
  have hMV : mog24V P A C (X * Z) = mog24V P A C X * Z := by
    unfold mog24V; rw [hHV, smul_mul_assoc]
  have hMSig : mog24Sig P A C (X * Z) = mog24Sig P A C X * Z := by
    unfold mog24Sig; rw [hHSig, smul_mul_assoc]
  have hG0 : golay24G0 P A C (X * Z) = golay24G0 P A C X * Z := by
    have hA61_XZ := (archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hP A C (X * Z)).2.2.2.2.2.1
    have hA61_X := (archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hP A C X).2.2.2.2.2.1
    have hK0 : kantorG0 P A C (X * Z) = kantorG0 P A C X * Z := by
      unfold kantorG0 kantorTriple
      calc conePlus P A * (X * Z) * coneMinus P C + coneMinus P C * (X * Z) * conePlus P A
        _ = (conePlus P A * X) * (Z * coneMinus P C) +
            (coneMinus P C * X) * (Z * conePlus P A) := by simp only [mul_assoc]
        _ = (conePlus P A * X) * (coneMinus P C * Z) +
            (coneMinus P C * X) * (conePlus P A * Z) := by rw [← hCm, ← hCp]
        _ = (conePlus P A * X * coneMinus P C + coneMinus P C * X * conePlus P A) * Z := by
            simp only [add_mul, mul_assoc]
    rw [hA61_XZ, hA61_X, hK0, smul_mul_assoc]
  refine ⟨hG0, hMV, hMSig, ?_, ?_⟩
  · unfold mog24SheetPlus
    rw [hMV, hMSig, add_mul, mul_assoc, mul_assoc]
  · unfold mog24SheetMinus
    rw [hMV, hMSig, sub_mul, mul_assoc, mul_assoc]

/-- **Archetype `A₇₆` (`archetype_A76_odd_defect_telegrapher_metriplectic_poly4_and_single_sheet_virasoro_decoders`):**
Synthesizes:
1. All-depth telegrapher quadratic relations for the odd defect modes `Φ δ^[n](V)` and `J δ^[n](V)`;
2. The 4th-order master metriplectic polynomial `metriplecticMasterPoly4Op P_k A C` annihilating
   all four fractal Tetraktys states across every scale `(k, n) ∈ ℕ × ℕ`;
3. **All-Mode Single-Sheet Drinfeld–Virasoro–MOG Decoders (`r ∈ ℕ`):**
   - `drinfeldPhiPlus r P A C + drinfeldPhiMinus r P A C = virasoroModeEven r P A C`,
   - `drinfeldPhiPlus r P A C - drinfeldPhiMinus r P A C = virasoroModeChiral r P A C`,
   - `golay24G0 P A C (drinfeldPhiPlus r P A C) = (24 : ℤ) • drinfeldPhiMinus (r + 1) P A C`,
   - `golay24G0 P A C (drinfeldPhiMinus r P A C) = (24 : ℤ) • drinfeldPhiPlus (r + 1) P A C`,
   - `mog24SheetPlus P A C (drinfeldPhiPlus r P A C) = (24 : ℤ) • virasoroModeEven (r + 3) P A C`,
   - `mog24SheetPlus P A C (drinfeldPhiMinus r P A C) = 0`,
   - `mog24SheetMinus P A C (drinfeldPhiPlus r P A C) = 0`,
   - `mog24SheetMinus P A C (drinfeldPhiMinus r P A C) = (24 : ℤ) • virasoroModeEven (r + 3) P A C`. -/
theorem archetype_A76_odd_defect_telegrapher_metriplectic_poly4_and_single_sheet_virasoro_decoders
    (A C : B) (k n r : ℕ) :
    let P_k := daughterIdemTower k P A
    let V_k := genV P_k A C
    let V_kn := idempotencyDefect^[n] V_k
    let Sig_kn := qgtDefectDiff P_k A C n
    -- 1. All-depth odd defect telegrapher quadratic relations:
    (metriplecticTelegrapher P A C (genPhi P A C * idempotencyDefect^[n] (genV P A C)) = 0 ∧
     metriplecticTelegrapher P A C (genJ P A C * idempotencyDefect^[n] (genV P A C)) = 0) ∧
    -- 2. All-scale (k, n) 4th-order master metriplectic polynomial annihilation:
    (metriplecticMasterPoly4Op P_k A C V_kn = 0 ∧
     metriplecticMasterPoly4Op P_k A C (genPhi P_k A C * V_kn) = 0 ∧
     metriplecticMasterPoly4Op P_k A C (genJ P_k A C * V_kn) = 0 ∧
     metriplecticMasterPoly4Op P_k A C (V_k * Sig_kn) = 0) ∧
    -- 3. All-mode r ∈ ℕ single-sheet Drinfeld–Virasoro–MOG decoders:
    (drinfeldPhiPlus r P A C + drinfeldPhiMinus r P A C = virasoroModeEven r P A C ∧
     drinfeldPhiPlus r P A C - drinfeldPhiMinus r P A C = virasoroModeChiral r P A C ∧
     golay24G0 P A C (drinfeldPhiPlus r P A C) = (24 : ℤ) • drinfeldPhiMinus (r + 1) P A C ∧
     golay24G0 P A C (drinfeldPhiMinus r P A C) = (24 : ℤ) • drinfeldPhiPlus (r + 1) P A C ∧
     mog24SheetPlus P A C (drinfeldPhiPlus r P A C) = (24 : ℤ) • virasoroModeEven (r + 3) P A C ∧
     mog24SheetPlus P A C (drinfeldPhiMinus r P A C) = 0 ∧
     mog24SheetMinus P A C (drinfeldPhiPlus r P A C) = 0 ∧
     mog24SheetMinus P A C (drinfeldPhiMinus r P A C) = (24 : ℤ) • virasoroModeEven (r + 3) P A C) := by
  intro P_k V_k V_kn Sig_kn
  have hOddTel := curvatureDoubleCommutator_quadratic_odd_defect_iterates hP A C n
  rcases stage_M9_all_scale_fractal_braiding_instanton_duality_and_master_metriplectic_poly4
      hP A C k n with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hM1, hM2, hM3, hM4⟩
  rcases opPow_genV_comm_invS_and_cones hP A C r with ⟨_, hCp, hCm⟩
  have hQpComm : qgtPlus P A C * opPow r (genV P A C) = drinfeldPhiPlus r P A C := by
    unfold qgtPlus drinfeldPhiPlus
    calc (conePlus P A * coneMinus P C) * opPow r (genV P A C)
      _ = conePlus P A * (coneMinus P C * opPow r (genV P A C)) := by rw [mul_assoc]
      _ = (conePlus P A * opPow r (genV P A C)) * coneMinus P C := by
          rw [hCm, ← mul_assoc]
      _ = opPow r (genV P A C) * (conePlus P A * coneMinus P C) := by
          rw [hCp, mul_assoc]
  have hQmComm : qgtMinus P A C * opPow r (genV P A C) = drinfeldPhiMinus r P A C := by
    unfold qgtMinus drinfeldPhiMinus
    calc (coneMinus P C * conePlus P A) * opPow r (genV P A C)
      _ = coneMinus P C * (conePlus P A * opPow r (genV P A C)) := by rw [mul_assoc]
      _ = (coneMinus P C * opPow r (genV P A C)) * conePlus P A := by
          rw [hCp, ← mul_assoc]
      _ = opPow r (genV P A C) * (coneMinus P C * conePlus P A) := by
          rw [hCm, mul_assoc]
  have hSum : drinfeldPhiPlus r P A C + drinfeldPhiMinus r P A C = virasoroModeEven r P A C := by
    unfold drinfeldPhiPlus drinfeldPhiMinus virasoroModeEven
    rw [← mul_add]
    rfl
  have hDiff : drinfeldPhiPlus r P A C - drinfeldPhiMinus r P A C = virasoroModeChiral r P A C :=
    (heisenbergSinkMode_eq_drinfeldXMinus_and_virasoroChiral_eq hP A C 0 r).2.1.symm
  rcases golay24_and_mog24_sheet_mul_opPow_genV hP A C (qgtPlus P A C) r with
    ⟨hG0P, _, _, hShPP, hShMP⟩
  rcases golay24_and_mog24_sheet_mul_opPow_genV hP A C (qgtMinus P A C) r with
    ⟨hG0M, _, _, hShPM, hShMM⟩
  have hSwapPM0 : golay24G0 P A C (qgtPlus P A C) = (24 : ℤ) • (genV P A C * qgtMinus P A C) := by
    rw [(archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hP A C (qgtPlus P A C)).2.2.2.2.2.1]
    congr 1
    unfold kantorG0 kantorTriple qgtPlus qgtMinus
    peirce_nf hP
  have hSwapMP0 : golay24G0 P A C (qgtMinus P A C) = (24 : ℤ) • (genV P A C * qgtPlus P A C) := by
    rw [(archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hP A C (qgtMinus P A C)).2.2.2.2.2.1]
    congr 1
    unfold kantorG0 kantorTriple qgtPlus qgtMinus
    peirce_nf hP
  have hMV_P : mog24V P A C (qgtPlus P A C) =
      (12 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
    peirce_abel_golay hP
  have hMSig_P : mog24Sig P A C (qgtPlus P A C) =
      (12 : ℤ) • (genV P A C * genV P A C * genSig P A C) := by
    peirce_abel_golay hP
  have hMV_M : mog24V P A C (qgtMinus P A C) =
      (12 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
    peirce_abel_golay hP
  have hMSig_M : mog24Sig P A C (qgtMinus P A C) =
      -((12 : ℤ) • (genV P A C * genV P A C * genSig P A C)) := by
    peirce_abel_golay hP
  have hSigV3 : genSig P A C * (genV P A C * genV P A C * genSig P A C) =
      (genV P A C * genV P A C * genV P A C) * genV P A C := by
    peirce_nf hP
  have hVV3 : genV P A C * (genV P A C * genV P A C * genV P A C) =
      (genV P A C * genV P A C * genV P A C) * genV P A C := by
    simp only [mul_assoc]
  have hDecPP0 : mog24SheetPlus P A C (qgtPlus P A C) =
      (24 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genV P A C) := by
    unfold mog24SheetPlus
    rw [hMV_P, hMSig_P, mul_smul_comm, mul_smul_comm, hVV3, hSigV3, ← add_smul]
    rfl
  have hDecPM0 : mog24SheetPlus P A C (qgtMinus P A C) = 0 := by
    unfold mog24SheetPlus
    rw [hMV_M, hMSig_M, mul_neg, mul_smul_comm, mul_smul_comm, hVV3, hSigV3, add_neg_cancel]
  have hDecMP0 : mog24SheetMinus P A C (qgtPlus P A C) = 0 := by
    unfold mog24SheetMinus
    rw [hMV_P, hMSig_P, mul_smul_comm, mul_smul_comm, hVV3, hSigV3, sub_self]
  have hDecMM0 : mog24SheetMinus P A C (qgtMinus P A C) =
      (24 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genV P A C) := by
    unfold mog24SheetMinus
    rw [hMV_M, hMSig_M, mul_neg, mul_smul_comm, mul_smul_comm, hVV3, hSigV3,
        sub_neg_eq_add, ← add_smul]
    rfl
  have hVMulQm :
      ((24 : ℤ) • (genV P A C * qgtMinus P A C)) * opPow r (genV P A C) =
        (24 : ℤ) • drinfeldPhiMinus (r + 1) P A C := by
    rw [smul_mul_assoc, mul_assoc, hQmComm]
    unfold drinfeldPhiMinus
    rw [← mul_assoc, mul_opPow_comm r (genV P A C)]
    rfl
  have hVMulQp :
      ((24 : ℤ) • (genV P A C * qgtPlus P A C)) * opPow r (genV P A C) =
        (24 : ℤ) • drinfeldPhiPlus (r + 1) P A C := by
    rw [smul_mul_assoc, mul_assoc, hQpComm]
    unfold drinfeldPhiPlus
    rw [← mul_assoc, mul_opPow_comm r (genV P A C)]
    rfl
  have hV4Mul :
      ((24 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genV P A C)) * opPow r (genV P A C) =
        (24 : ℤ) • virasoroModeEven (r + 3) P A C := by
    rw [smul_mul_assoc]
    congr 1
    have hComm1 := mul_opPow_comm r (genV P A C)
    have hComm2 := mul_opPow_comm (r + 1) (genV P A C)
    have hComm3 := mul_opPow_comm (r + 2) (genV P A C)
    have hComm4 := mul_opPow_comm (r + 3) (genV P A C)
    calc ((genV P A C * genV P A C * genV P A C) * genV P A C) * opPow r (genV P A C)
      _ = (genV P A C * genV P A C * genV P A C) * (genV P A C * opPow r (genV P A C)) := by
          rw [mul_assoc]
      _ = (genV P A C * genV P A C * genV P A C) * opPow (r + 1) (genV P A C) := by
          rw [hComm1]; rfl
      _ = (genV P A C * genV P A C) * (genV P A C * opPow (r + 1) (genV P A C)) := by
          rw [mul_assoc]
      _ = (genV P A C * genV P A C) * opPow (r + 2) (genV P A C) := by
          rw [hComm2]; rfl
      _ = genV P A C * (genV P A C * opPow (r + 2) (genV P A C)) := by
          rw [mul_assoc]
      _ = genV P A C * opPow (r + 3) (genV P A C) := by
          rw [hComm3]; rfl
      _ = virasoroModeEven (r + 3) P A C := hComm4
  refine ⟨hOddTel, ⟨hM1, hM2, hM3, hM4⟩, hSum, hDiff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hQpComm, hG0P, hSwapPM0, hVMulQm]
  · rw [← hQmComm, hG0M, hSwapMP0, hVMulQp]
  · rw [← hQpComm, hShPP, hDecPP0, hV4Mul]
  · rw [← hQmComm, hShPM, hDecPM0, zero_mul]
  · rw [← hQpComm, hShMP, hDecMP0, zero_mul]
  · rw [← hQmComm, hShMM, hDecMM0, hV4Mul]

end Tier1

/-! ### Part 3: Tier 2 Canonical Synthesis Theorems (`A₇₇ → A₈₂`) -/

section Tier2

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)

/-- **Archetype `A₇₇` (`archetype_A77_homogenized_channel_kernels_and_unit_defect_exclusions`):**
On any nontrivial ring `[Nontrivial B]`:
1. All four homogenized channels `hProjV`, `hProjPhi`, `hProjJ`, and `hProjSig` are non-injective,
   with `hProjV P A C 1 = 8 • V²` and `hProjPhi P A C 1 = hProjJ P A C 1 = hProjSig P A C 1 = 0`;
2. On the unit defect level set `idempotencyDefect (genV P A C) = 1`, `genV P A C ≠ 0`, and both
   the false cubic recurrence and false 3-term geometric truncation are excluded. -/
theorem archetype_A77_homogenized_channel_kernels_and_unit_defect_exclusions
    [Nontrivial B] (hP : P * P = P) (A C : B) :
    (hProjV P A C 1 = (8 : ℤ) • (genV P A C * genV P A C) ∧
     hProjPhi P A C 1 = 0 ∧
     hProjJ P A C 1 = 0 ∧
     hProjSig P A C 1 = 0 ∧
     ¬ Function.Injective (hProjV P A C) ∧
     ¬ Function.Injective (hProjPhi P A C) ∧
     ¬ Function.Injective (hProjJ P A C) ∧
     ¬ Function.Injective (hProjSig P A C)) ∧
    (idempotencyDefect (genV P A C) = 1 →
      genV P A C ≠ 0 ∧
      genV P A C * genV P A C * genV P A C - genV P A C * genV P A C -
        genV P A C ≠ genV P A C * idempotencyDefect (genV P A C) ∧
      (1 - genV P A C) * (1 + genV P A C + genV P A C * genV P A C) - 1 ≠
        -((1 + genV P A C) * idempotencyDefect (genV P A C))) := by
  rcases hProj_one P A C with ⟨h1, h2, h3, h4⟩
  refine ⟨⟨h1, h2, h3, h4,
           hProjV_not_injective hP A C,
           hProjPhi_not_injective P A C,
           hProjJ_not_injective P A C,
           hProjSig_not_injective P A C⟩, ?_⟩
  intro hUnit
  exact ⟨genV_ne_zero_of_unit_defect hUnit,
         unit_defect_excludes_submitted_cubic hUnit,
         unit_defect_excludes_submitted_geometric_remainder hUnit⟩

include hP

/-- **Archetype `A₇₈` (`archetype_A78_graded_defect_perturbation_and_parity_product`):**
Graded idempotency defect split, odd perturbation idempotency criterion
`(P + oddGrade P X)² = P + oddGrade P X ↔ (oddGrade P X)² = 0`, and ordered parity-product
identity `(P + oddGrade P X) * parityConj P (P + oddGrade P X) = P - (oddGrade P X)² - comm P (oddGrade P X)`. -/
theorem archetype_A78_graded_defect_perturbation_and_parity_product
    (X : B) :
    idempotencyDefect (P + oddGrade P X) = oddGrade P X * oddGrade P X ∧
    ((P + oddGrade P X) * (P + oddGrade P X) = P + oddGrade P X ↔
      oddGrade P X * oddGrade P X = 0) ∧
    (P + oddGrade P X) * parityConj P (P + oddGrade P X) =
      P - oddGrade P X * oddGrade P X - comm P (oddGrade P X) :=
  ⟨odd_perturbation_defect hP X,
   add_oddGrade_idempotent_iff hP X,
   add_oddGrade_mul_parityConj hP X⟩

/-- **Archetype `A₇₉` (`archetype_A79_wilson_plaquette_and_logarithmic_corner_pullbacks`):**
1. Ordered Peirce Wilson plaquette expansions `wilsonPlaquette P A C = 1 + Σ - V J + Q_+²` and
   `wilsonPlaquetteRev P A C = 1 - Σ + V J + Q_-²`, with symmetric even part `-V²`;
2. Logarithmic Bruhat corner pullbacks `leftCornerPullback P A C = Φ - Σ - V N_-` and
   `rightCornerPullback P A C = Φ + Σ - V N_+`, transporting `P` to an idempotent
   `P + leftCornerPullback P A C`. -/
theorem archetype_A79_wilson_plaquette_and_logarithmic_corner_pullbacks
    (A C : B) :
    (wilsonPlaquette P A C =
       1 + genSig P A C - genV P A C * genJ P A C +
         qgtPlus P A C * qgtPlus P A C ∧
     wilsonPlaquetteRev P A C =
       1 - genSig P A C + genV P A C * genJ P A C +
         qgtMinus P A C * qgtMinus P A C ∧
     evenGrade P ((1 - wilsonPlaquette P A C) + (1 - wilsonPlaquetteRev P A C)) =
       -(genV P A C * genV P A C)) ∧
    (leftCornerPullback P A C =
       genPhi P A C - genSig P A C - genV P A C * coneMinus P C ∧
     rightCornerPullback P A C =
       genPhi P A C + genSig P A C - genV P A C * conePlus P A ∧
     idempotencyDefect (P + leftCornerPullback P A C) = 0) := by
  rcases wilsonPlaquette_ordered_expansions hP A C with ⟨hW1, hW2⟩
  exact ⟨⟨hW1, hW2, wilsonPlaquette_symmetric_even_part hP A C⟩,
         ⟨leftCornerPullback_eq hP A C,
          rightCornerPullback_eq hP A C,
          leftCornerPullback_idempotency hP A C⟩⟩

/-- **Archetype `A₈₀` (`archetype_A80_two_state_chart_single_sheet_and_odd_defect_sandwiches`):**
At every defect depth `n : ℕ`, the two-state local chart sandwich `(P - N_+) · (P + N_-)`:
1. Fixes the upper-cycle iterate `δ^[n](Q_+)` and maps the lower-cycle iterate `δ^[n](Q_-)` to
   `-V * δ^[n](Q_+)`;
2. Annihilates the odd symmetric mode `Φ δ^[n](V)` and maps `J δ^[n](V)` to `2 • (V * δ^[n](Q_+))`;
3. Satisfies `chartBruhatConj P A C (genV P A C) = genV P A C`. -/
theorem archetype_A80_two_state_chart_single_sheet_and_odd_defect_sandwiches
    (A C : B) (n : ℕ) :
    (P - conePlus P A) * idempotencyDefect^[n] (qgtPlus P A C) * (P + coneMinus P C) =
      idempotencyDefect^[n] (qgtPlus P A C) ∧
    (P - conePlus P A) * idempotencyDefect^[n] (qgtMinus P A C) * (P + coneMinus P C) =
      -(genV P A C * idempotencyDefect^[n] (qgtPlus P A C)) ∧
    (P - conePlus P A) * (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
        (P + coneMinus P C) = 0 ∧
    (P - conePlus P A) * (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
        (P + coneMinus P C) =
      (2 : ℤ) • (genV P A C * idempotencyDefect^[n] (qgtPlus P A C)) ∧
    chartBruhatConj P A C (genV P A C) = genV P A C := by
  rcases chart_two_state_odd_defect_iterates hP A C n with ⟨hPhi, hJ⟩
  exact ⟨chart_two_state_qgtPlus_defect_iterate hP A C n,
         chart_two_state_qgtMinus_defect_iterate hP A C n,
         hPhi, hJ, chartBruhatConj_genV hP A C⟩

/-- **Archetype `A₈₁` (`archetype_A81_star_grading_anti_involution_and_ideal_chart_pairing`):**
In any `[StarRing B]` with self-adjoint idempotent `P` (`P * P = P`, `star P = P`):
1. The grading-twisted star map `X ↦ invS P * star X * invS P` is an involutive anti-automorphism
   swapping the upper and lower charts `P - N_+(A)` and `P + N_-(A^⋆)` and negating `Φ(A, A^⋆)`
   while fixing `J(A, A^⋆)`, `V(A, A^⋆)`, and `Σ(A, A^⋆)`;
2. The opposite graph charts satisfy the triple-product identities
   `(P - N_+)(P + N_-)(P - N_+) = (1 - V)(P - N_+)` and
   `(P + N_-)(P - N_+)(P + N_-) = (P + N_-)(1 - V)` and difference square
   `((P - N_+) - (P + N_-))² = V`. -/
theorem archetype_A81_star_grading_anti_involution_and_ideal_chart_pairing
    [StarRing B] (hPs : star P = P) (A C X Y : B) :
    (invS P * star (invS P * star X * invS P) * invS P = X ∧
     invS P * star (X * Y) * invS P =
       (invS P * star Y * invS P) * (invS P * star X * invS P) ∧
     invS P * star (P - conePlus P A) * invS P = P + coneMinus P (star A) ∧
     invS P * star (P + coneMinus P A) * invS P = P - conePlus P (star A) ∧
     invS P * star (genPhi P A (star A)) * invS P = -genPhi P A (star A) ∧
     invS P * star (genJ P A (star A)) * invS P = genJ P A (star A) ∧
     invS P * star (genV P A (star A)) * invS P = genV P A (star A) ∧
     invS P * star (genSig P A (star A)) * invS P = genSig P A (star A)) ∧
    ((P - conePlus P A) * (P + coneMinus P C) * (P - conePlus P A) =
       (1 - genV P A C) * (P - conePlus P A) ∧
     (P + coneMinus P C) * (P - conePlus P A) * (P + coneMinus P C) =
       (P + coneMinus P C) * (1 - genV P A C) ∧
     ((P - conePlus P A) - (P + coneMinus P C)) *
       ((P - conePlus P A) - (P + coneMinus P C)) = genV P A C) :=
  ⟨⟨grading_star_involutive hPs hP X,
    grading_star_mul hP X Y,
    grading_star_upper_chart hPs hP A,
    grading_star_lower_chart hPs hP A,
    grading_star_genPhi hPs hP A,
    grading_star_genJ hPs hP A,
    grading_star_genV hPs hP A,
    grading_star_genSig hPs hP A⟩,
   ⟨chart_pairing_upper_triple hP A C,
    chart_pairing_lower_triple hP A C,
    chart_pairing_difference_square hP A C⟩⟩

/-- **Archetype `A₈₂` (`archetype_A82_two_state_chart_defect_difference_and_block_lower_decoder`):**
At every defect depth `n, m : ℕ`:
1. The two-state chart sandwich maps `δ^[n](V)` to `(1 - V) δ^[n](Q_+)` and `qgtDefectDiff P A C n`
   to `(1 + V) δ^[n](Q_+)`, with exact difference `2 • (V * δ^[n](Q_+))`, and satisfies the
   depth-zero Euler-compression residual `(P - N_+) Σ (P + N_-) - (1 - V) Q_+ = 2 • Q_+²`;
2. The three-corner block-lower operator `tcrDecoderFullOp P A C n` equals
   `(1 + N_-) δ^[n](V)`, has vanishing upper-right corner `P * T * (1 - P) = 0`, recovers
   `δ^[n](Q_+)` and `δ^[n](Q_-)` in its `(1, 1)` and `(0, 0)` blocks, and is closed under
   multiplication across arbitrary depths `(n, m)`. -/
theorem archetype_A82_two_state_chart_defect_difference_and_block_lower_decoder
    (A C : B) (n m : ℕ) :
    ((P - conePlus P A) * idempotencyDefect^[n] (genV P A C) * (P + coneMinus P C) =
       (1 - genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) ∧
     (P - conePlus P A) * qgtDefectDiff P A C n * (P + coneMinus P C) =
       (1 + genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) ∧
     (P - conePlus P A) * qgtDefectDiff P A C n * (P + coneMinus P C) -
       (1 - genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) =
         (2 : ℤ) • (genV P A C * idempotencyDefect^[n] (qgtPlus P A C)) ∧
     (P - conePlus P A) * genSig P A C * (P + coneMinus P C) -
       (1 - genV P A C) * (conePlus P A * coneMinus P C) =
         (2 : ℤ) • ((conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C))) ∧
    (tcrDecoderFullOp P A C n =
       (1 + coneMinus P C) * idempotencyDefect^[n] (genV P A C) ∧
     P * tcrDecoderFullOp P A C n * (1 - P) = 0 ∧
     peirce11 P (tcrDecoderFullOp P A C n) = idempotencyDefect^[n] (qgtPlus P A C) ∧
     peirce00 P (tcrDecoderFullOp P A C n) = idempotencyDefect^[n] (qgtMinus P A C) ∧
     P * (tcrDecoderFullOp P A C n * tcrDecoderFullOp P A C m) * (1 - P) = 0) := by
  rcases chart_two_state_genV_and_qgtDefectDiff_iterates hP A C n with ⟨hC1, hC2, hC3⟩
  rcases all_scale_tcr_decoder_full_block_triangular_closure hP A C n m with
    ⟨hT1, _, hT3, hT4, hT5, _, hT7⟩
  exact ⟨⟨hC1, hC2, hC3, chart_sigma_euler_compression_residual hP A C⟩,
         ⟨hT1, hT3, hT4, hT5, hT7⟩⟩

end Tier2

/-! ### Part 4: Tier 3 Canonical Synthesis Theorems (`A₈₃ → A₈₈`, Archetypes `Z₁ → Z₆`) -/

private theorem opPow_genV_comm_genSig_explicit
    {B₀ : Type*} [Ring B₀] (P₀ A₀ C₀ : B₀) (m : ℕ)
    (hP₀ : P₀ * P₀ = P₀) :
    genSig P₀ A₀ C₀ * opPow m (genV P₀ A₀ C₀) =
      opPow m (genV P₀ A₀ C₀) * genSig P₀ A₀ C₀ := by
  rcases opPow_genV_comm_invS_and_cones hP₀ A₀ C₀ m with ⟨_, hPlus, hMinus⟩
  have hPhi : genPhi P₀ A₀ C₀ * opPow m (genV P₀ A₀ C₀) =
      opPow m (genV P₀ A₀ C₀) * genPhi P₀ A₀ C₀ := by
    unfold genPhi; rw [add_mul, mul_add, hPlus, hMinus]
  have hJ : genJ P₀ A₀ C₀ * opPow m (genV P₀ A₀ C₀) =
      opPow m (genV P₀ A₀ C₀) * genJ P₀ A₀ C₀ := by
    unfold genJ; rw [sub_mul, mul_sub, hPlus, hMinus]
  have hSig : genSig P₀ A₀ C₀ = genJ P₀ A₀ C₀ * genPhi P₀ A₀ C₀ := by peirce_nf hP₀
  calc genSig P₀ A₀ C₀ * opPow m (genV P₀ A₀ C₀)
      = (genJ P₀ A₀ C₀ * genPhi P₀ A₀ C₀) * opPow m (genV P₀ A₀ C₀) := by rw [hSig]
    _ = genJ P₀ A₀ C₀ * (genPhi P₀ A₀ C₀ * opPow m (genV P₀ A₀ C₀)) := by rw [mul_assoc]
    _ = genJ P₀ A₀ C₀ * (opPow m (genV P₀ A₀ C₀) * genPhi P₀ A₀ C₀) := by rw [hPhi]
    _ = (genJ P₀ A₀ C₀ * opPow m (genV P₀ A₀ C₀)) * genPhi P₀ A₀ C₀ := by rw [← mul_assoc]
    _ = (opPow m (genV P₀ A₀ C₀) * genJ P₀ A₀ C₀) * genPhi P₀ A₀ C₀ := by rw [hJ]
    _ = opPow m (genV P₀ A₀ C₀) * (genJ P₀ A₀ C₀ * genPhi P₀ A₀ C₀) := by rw [mul_assoc]
    _ = opPow m (genV P₀ A₀ C₀) * genSig P₀ A₀ C₀ := by rw [← hSig]

section Tier3

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

/-- **Archetype `A₈₃` (`Z₁`, `archetype_A83_zorn_wedge_jordan_cancellation_and_parity_grading`):**
In any associative ring `B` with idempotent `P * P = P` and cross-cut bridge `M : B`:
1. **Strict Odd-Corner Support & Parity Derivation Eigenvalues of `zornWedgePlus` and `zornWedgeMinus`:**
   - `P * zornWedgePlus P M y w * (1 - P) = zornWedgePlus P M y w` and
     `(1 - P) * zornWedgeMinus P M x z * P = zornWedgeMinus P M x z`,
   - `comm (invS P) (zornWedgePlus P M y w) = (2 : ℤ) • zornWedgePlus P M y w` and
     `comm (invS P) (zornWedgeMinus P M x z) = -((2 : ℤ) • zornWedgeMinus P M x z)`,
   - `evenGrade P (zornWedgePlus P M y w) = 0`, `oddGrade P (zornWedgePlus P M y w) = zornWedgePlus P M y w`,
     `evenGrade P (zornWedgeMinus P M x z) = 0`, and `oddGrade P (zornWedgeMinus P M x z) = zornWedgeMinus P M x z`;
2. **Exact Wedge Cancellation in the Symmetric Jordan Anticommutator:**
   `zornNonAssocMul P M a b x y c d z w + zornNonAssocMul P M c d z w a b x y =`
   `anticomm (zornMatrix P a b x y) (zornMatrix P c d z w)`;
3. **Doubled Wedge Residual in the Skew Non-Associative Commutator:**
   `zornNonAssocMul P M a b x y c d z w - zornNonAssocMul P M c d z w a b x y =`
   `comm (zornMatrix P a b x y) (zornMatrix P c d z w) - (2 : ℤ) • zornWedgePlus P M y w + (2 : ℤ) • zornWedgeMinus P M x z`;
4. **Odd-Grade Decomposition of `zornNonAssocMul`:**
   `oddGrade P (zornNonAssocMul P M a b x y c d z w) =`
   `oddGrade P (zornMatrix P a b x y * zornMatrix P c d z w) - zornWedgePlus P M y w + zornWedgeMinus P M x z`. -/
theorem archetype_A83_zorn_wedge_jordan_cancellation_and_parity_grading
    (M a b x y c d z w : B) :
    (P * zornWedgePlus P M y w * (1 - P) = zornWedgePlus P M y w ∧
     (1 - P) * zornWedgeMinus P M x z * P = zornWedgeMinus P M x z ∧
     comm (invS P) (zornWedgePlus P M y w) = (2 : ℤ) • zornWedgePlus P M y w ∧
     comm (invS P) (zornWedgeMinus P M x z) = -((2 : ℤ) • zornWedgeMinus P M x z) ∧
     evenGrade P (zornWedgePlus P M y w) = 0 ∧
     oddGrade P (zornWedgePlus P M y w) = zornWedgePlus P M y w ∧
     evenGrade P (zornWedgeMinus P M x z) = 0 ∧
     oddGrade P (zornWedgeMinus P M x z) = zornWedgeMinus P M x z) ∧
    zornNonAssocMul P M a b x y c d z w + zornNonAssocMul P M c d z w a b x y =
      anticomm (zornMatrix P a b x y) (zornMatrix P c d z w) ∧
    zornNonAssocMul P M a b x y c d z w - zornNonAssocMul P M c d z w a b x y =
      comm (zornMatrix P a b x y) (zornMatrix P c d z w) -
        (2 : ℤ) • zornWedgePlus P M y w + (2 : ℤ) • zornWedgeMinus P M x z ∧
    oddGrade P (zornNonAssocMul P M a b x y c d z w) =
      oddGrade P (zornMatrix P a b x y * zornMatrix P c d z w) -
        zornWedgePlus P M y w + zornWedgeMinus P M x z := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · unfold zornWedgePlus; peirce_nf hP
  · unfold zornWedgeMinus; peirce_nf hP
  · unfold zornWedgePlus; peirce_nf hP
  · unfold zornWedgeMinus; peirce_nf hP
  · unfold zornWedgePlus evenGrade; peirce_nf hP
  · unfold zornWedgePlus oddGrade; peirce_nf hP
  · unfold zornWedgeMinus evenGrade; peirce_nf hP
  · unfold zornWedgeMinus oddGrade; peirce_nf hP
  · unfold zornNonAssocMul zornWedgePlus zornWedgeMinus conePlus coneMinus anticomm
    noncomm_ring
  · unfold zornNonAssocMul zornWedgePlus zornWedgeMinus conePlus coneMinus comm
    noncomm_ring
  · unfold zornNonAssocMul zornWedgePlus zornWedgeMinus oddGrade
    peirce_nf hP

/-- **Archetype `A₈₄` (`Z₂`, `archetype_A84_zorn_wedge_cone_selectivity_and_induced_tetraktys`):**
In any associative ring `B` with idempotent `P * P = P` and cross-cut bridge `M : B`:
1. **Opposite-Cone & Opposite-Cycle Vanishing:**
   - `zornWedgePlus P M (coneMinus P y) (coneMinus P w) = 0`,
   - `zornWedgeMinus P M (conePlus P x) (conePlus P z) = 0`,
   - `zornWedgePlus P M (qgtMinus P a₁ c₁) (qgtMinus P a₂ c₂) = 0`,
   - `zornWedgeMinus P M (qgtPlus P a₁ c₁) (qgtPlus P a₂ c₂) = 0`;
2. **Same-Cone Cross-Cut Triple Product Factorization:**
   - `zornWedgePlus P M (conePlus P x) (conePlus P z) =`
     `conePlus P x * coneMinus P M * conePlus P z - conePlus P z * coneMinus P M * conePlus P x`,
   - `zornWedgeMinus P M (coneMinus P y) (coneMinus P w) =`
     `coneMinus P y * conePlus P M * coneMinus P w - coneMinus P w * conePlus P M * coneMinus P y`;
3. **Nilpotency & Induced Wedge Tetraktys (`genV`, `genSig`):**
   - `zornWedgePlus P M y w * zornWedgePlus P M x z = 0`,
   - `zornWedgeMinus P M x z * zornWedgeMinus P M y w = 0`,
   - `anticomm (zornWedgePlus P M y w) (zornWedgeMinus P M x z) =`
     `genV P (y * M * w - w * M * y) (x * M * z - z * M * x)`,
   - `comm (zornWedgePlus P M y w) (zornWedgeMinus P M x z) =`
     `genSig P (y * M * w - w * M * y) (x * M * z - z * M * x)`. -/
theorem archetype_A84_zorn_wedge_cone_selectivity_and_induced_tetraktys
    (M x y z w a₁ c₁ a₂ c₂ : B) :
    (zornWedgePlus P M (coneMinus P y) (coneMinus P w) = 0 ∧
     zornWedgeMinus P M (conePlus P x) (conePlus P z) = 0 ∧
     zornWedgePlus P M (qgtMinus P a₁ c₁) (qgtMinus P a₂ c₂) = 0 ∧
     zornWedgeMinus P M (qgtPlus P a₁ c₁) (qgtPlus P a₂ c₂) = 0) ∧
    (zornWedgePlus P M (conePlus P x) (conePlus P z) =
       conePlus P x * coneMinus P M * conePlus P z -
         conePlus P z * coneMinus P M * conePlus P x ∧
     zornWedgeMinus P M (coneMinus P y) (coneMinus P w) =
       coneMinus P y * conePlus P M * coneMinus P w -
         coneMinus P w * conePlus P M * coneMinus P y) ∧
    (zornWedgePlus P M y w * zornWedgePlus P M x z = 0 ∧
     zornWedgeMinus P M x z * zornWedgeMinus P M y w = 0 ∧
     anticomm (zornWedgePlus P M y w) (zornWedgeMinus P M x z) =
       genV P (y * M * w - w * M * y) (x * M * z - z * M * x) ∧
     comm (zornWedgePlus P M y w) (zornWedgeMinus P M x z) =
       genSig P (y * M * w - w * M * y) (x * M * z - z * M * x)) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, rfl, rfl⟩⟩
  · dsimp only [zornWedgePlus, zornWedgeMinus, conePlus, coneMinus, qgtPlus, qgtMinus]; peirce_nf hP
  · dsimp only [zornWedgePlus, zornWedgeMinus, conePlus, coneMinus, qgtPlus, qgtMinus]; peirce_nf hP
  · dsimp only [zornWedgePlus, zornWedgeMinus, conePlus, coneMinus, qgtPlus, qgtMinus]; peirce_nf hP
  · dsimp only [zornWedgePlus, zornWedgeMinus, conePlus, coneMinus, qgtPlus, qgtMinus]; peirce_nf hP
  · dsimp only [zornWedgePlus, zornWedgeMinus, conePlus, coneMinus, qgtPlus, qgtMinus]; peirce_nf hP
  · dsimp only [zornWedgePlus, zornWedgeMinus, conePlus, coneMinus, qgtPlus, qgtMinus]; peirce_nf hP
  · dsimp only [zornWedgePlus, zornWedgeMinus, conePlus, coneMinus, qgtPlus, qgtMinus]; peirce_nf hP
  · dsimp only [zornWedgePlus, zornWedgeMinus, conePlus, coneMinus, qgtPlus, qgtMinus]; peirce_nf hP

/-- Right-multiplication by `opPow m (genV P A C)` commutes with `derivSqPhi`, `derivSqJ`,
and `derivSqSig`. -/
theorem derivSq_mul_opPow_genV (A C X : B) (m : ℕ) :
    derivSqPhi P A C (X * opPow m (genV P A C)) =
      derivSqPhi P A C X * opPow m (genV P A C) ∧
    derivSqJ P A C (X * opPow m (genV P A C)) =
      derivSqJ P A C X * opPow m (genV P A C) ∧
    derivSqSig P A C (X * opPow m (genV P A C)) =
      derivSqSig P A C X * opPow m (genV P A C) := by
  rcases opPow_genV_comm_invS_and_cones hP A C m with ⟨_, hPlus, hMinus⟩
  have hPhi : genPhi P A C * opPow m (genV P A C) =
      opPow m (genV P A C) * genPhi P A C := by
    unfold genPhi; rw [add_mul, mul_add, hPlus, hMinus]
  have hJ : genJ P A C * opPow m (genV P A C) =
      opPow m (genV P A C) * genJ P A C := by
    unfold genJ; rw [sub_mul, mul_sub, hPlus, hMinus]
  have hSig := opPow_genV_comm_genSig_explicit P A C m hP
  have hPhi' : genPhi P A C * opPow m (genV P A C) = opPow m (genV P A C) * genPhi P A C := hPhi
  have hJ' : genJ P A C * opPow m (genV P A C) = opPow m (genV P A C) * genJ P A C := hJ
  have hSig' : genSig P A C * opPow m (genV P A C) = opPow m (genV P A C) * genSig P A C := hSig
  have hComm : ∀ G : B, G * opPow m (genV P A C) = opPow m (genV P A C) * G →
      ∀ Y : B, comm G (Y * opPow m (genV P A C)) = comm G Y * opPow m (genV P A C) := by
    intro G hG Y
    unfold comm
    calc G * (Y * opPow m (genV P A C)) - (Y * opPow m (genV P A C)) * G
      _ = (G * Y) * opPow m (genV P A C) - Y * (opPow m (genV P A C) * G) := by
          simp only [mul_assoc]
      _ = (G * Y) * opPow m (genV P A C) - Y * (G * opPow m (genV P A C)) := by
          rw [← hG]
      _ = (G * Y - Y * G) * opPow m (genV P A C) := by noncomm_ring
  refine ⟨?_, ?_, ?_⟩
  · unfold derivSqPhi
    rw [hComm (genPhi P A C) hPhi' X, hComm (genPhi P A C) hPhi' (comm (genPhi P A C) X), neg_mul]
  · unfold derivSqJ
    rw [hComm (genJ P A C) hJ' X, hComm (genJ P A C) hJ' (comm (genJ P A C) X)]
  · unfold derivSqSig
    rw [hComm (genSig P A C) hSig' X, hComm (genSig P A C) hSig' (comm (genSig P A C) X), neg_mul]

/-- **Archetype `A₈₅` (`Z₃`, `archetype_A85_all_mode_double_derivation_virasoro_dichotomy_and_projection`):**
For every mode index `m : ℕ` and any integers `α, β, γ : ℤ`:
1. **Kernel on All Even Virasoro Modes `virasoroModeEven m P A C` and Symmetric Odd Modes:**
   - `derivSqPhi P A C (virasoroModeEven m P A C) = 0`,
   - `derivSqJ P A C (virasoroModeEven m P A C) = 0`,
   - `derivSqSig P A C (virasoroModeEven m P A C) = 0`,
   - `derivSqPhi P A C (genPhi P A C * opPow m (genV P A C)) = 0`,
   - `derivSqJ P A C (genJ P A C * opPow m (genV P A C)) = 0`,
   - `derivSqSig P A C (virasoroModeChiral m P A C) = 0`;
2. **Exact `-4 V` Eigen-Scaling on All Skew Odd Modes and Chiral Virasoro Modes `virasoroModeChiral m P A C`:**
   - `derivSqPhi P A C (genJ P A C * opPow m (genV P A C)) =`
     `-((4 : ℤ) • (genV P A C * (genJ P A C * opPow m (genV P A C))))`,
   - `derivSqPhi P A C (virasoroModeChiral m P A C) = -((4 : ℤ) • virasoroModeChiral (m + 1) P A C)`,
   - `derivSqJ P A C (genPhi P A C * opPow m (genV P A C)) =`
     `-((4 : ℤ) • (genV P A C * (genPhi P A C * opPow m (genV P A C))))`,
   - `derivSqJ P A C (virasoroModeChiral m P A C) = -((4 : ℤ) • virasoroModeChiral (m + 1) P A C)`;
3. **All-Mode Linear Combination Projections:**
   - `derivSqPhi P A C (α • (genPhi P A C * opPow m (genV P A C)) + β • virasoroModeEven m P A C + γ • (genJ P A C * opPow m (genV P A C))) =`
     `γ • (-((4 : ℤ) • (genV P A C * (genJ P A C * opPow m (genV P A C)))))`,
   - `derivSqPhi P A C (α • virasoroModeEven m P A C + β • virasoroModeChiral m P A C) =`
     `β • (-((4 : ℤ) • virasoroModeChiral (m + 1) P A C))`. -/
theorem archetype_A85_all_mode_double_derivation_virasoro_dichotomy_and_projection
    (A C : B) (m : ℕ) (α β γ : ℤ) :
    (derivSqPhi P A C (virasoroModeEven m P A C) = 0 ∧
     derivSqJ P A C (virasoroModeEven m P A C) = 0 ∧
     derivSqSig P A C (virasoroModeEven m P A C) = 0 ∧
     derivSqPhi P A C (genPhi P A C * opPow m (genV P A C)) = 0 ∧
     derivSqJ P A C (genJ P A C * opPow m (genV P A C)) = 0 ∧
     derivSqSig P A C (virasoroModeChiral m P A C) = 0) ∧
    (derivSqPhi P A C (genJ P A C * opPow m (genV P A C)) =
       -((4 : ℤ) • (genV P A C * (genJ P A C * opPow m (genV P A C)))) ∧
     derivSqPhi P A C (virasoroModeChiral m P A C) =
       -((4 : ℤ) • virasoroModeChiral (m + 1) P A C) ∧
     derivSqJ P A C (genPhi P A C * opPow m (genV P A C)) =
       -((4 : ℤ) • (genV P A C * (genPhi P A C * opPow m (genV P A C)))) ∧
     derivSqJ P A C (virasoroModeChiral m P A C) =
       -((4 : ℤ) • virasoroModeChiral (m + 1) P A C)) ∧
    (derivSqPhi P A C
        (α • (genPhi P A C * opPow m (genV P A C)) +
         β • virasoroModeEven m P A C +
         γ • (genJ P A C * opPow m (genV P A C))) =
       γ • (-((4 : ℤ) • (genV P A C * (genJ P A C * opPow m (genV P A C))))) ∧
     derivSqPhi P A C
        (α • virasoroModeEven m P A C + β • virasoroModeChiral m P A C) =
       β • (-((4 : ℤ) • virasoroModeChiral (m + 1) P A C))) := by
  have hEvenEq : virasoroModeEven m P A C = genV P A C * opPow m (genV P A C) :=
    (mul_opPow_comm m (genV P A C)).symm
  have hChiralEq : virasoroModeChiral m P A C = genSig P A C * opPow m (genV P A C) := by
    unfold virasoroModeChiral
    rw [show sugawaraTensor P A C = genV P A C by rfl,
      show chiralSchwinger P A C = genSig P A C by rfl,
      (opPow_genV_comm_genSig_explicit P A C m hP).symm]
  have hPhiV0 : derivSqPhi P A C (genV P A C) = 0 := by unfold derivSqPhi; peirce_nf hP
  have hJV0 : derivSqJ P A C (genV P A C) = 0 := by unfold derivSqJ; peirce_nf hP
  have hSigV0 : derivSqSig P A C (genV P A C) = 0 := by unfold derivSqSig; peirce_nf hP
  have hPhiPhi0 : derivSqPhi P A C (genPhi P A C) = 0 := by unfold derivSqPhi; peirce_nf hP
  have hJJ0 : derivSqJ P A C (genJ P A C) = 0 := by unfold derivSqJ; peirce_nf hP
  have hSigSig0 : derivSqSig P A C (genSig P A C) = 0 := by unfold derivSqSig; peirce_nf hP
  have hPhiJ0 : derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) := by
    unfold derivSqPhi; peirce_nf hP
  have hPhiSig0 : derivSqPhi P A C (genSig P A C) = -((4 : ℤ) • (genV P A C * genSig P A C)) := by
    unfold derivSqPhi; peirce_nf hP
  have hJPhi0 : derivSqJ P A C (genPhi P A C) = -((4 : ℤ) • (genV P A C * genPhi P A C)) := by
    unfold derivSqJ; peirce_nf hP
  have hJSig0 : derivSqJ P A C (genSig P A C) = -((4 : ℤ) • (genV P A C * genSig P A C)) := by
    unfold derivSqJ; peirce_nf hP
  rcases derivSq_mul_opPow_genV hP A C (genV P A C) m with ⟨hEV_Phi, hEV_J, hEV_Sig⟩
  rcases derivSq_mul_opPow_genV hP A C (genPhi P A C) m with ⟨hEPhi_Phi, hEPhi_J, _⟩
  rcases derivSq_mul_opPow_genV hP A C (genJ P A C) m with ⟨hEJ_Phi, hEJ_J, _⟩
  rcases derivSq_mul_opPow_genV hP A C (genSig P A C) m with ⟨hESig_Phi, hESig_J, hESig_Sig⟩
  have h1 : derivSqPhi P A C (virasoroModeEven m P A C) = 0 := by
    rw [hEvenEq, hEV_Phi, hPhiV0, zero_mul]
  have h2 : derivSqJ P A C (virasoroModeEven m P A C) = 0 := by
    rw [hEvenEq, hEV_J, hJV0, zero_mul]
  have h3 : derivSqSig P A C (virasoroModeEven m P A C) = 0 := by
    rw [hEvenEq, hEV_Sig, hSigV0, zero_mul]
  have h4 : derivSqPhi P A C (genPhi P A C * opPow m (genV P A C)) = 0 := by
    rw [hEPhi_Phi, hPhiPhi0, zero_mul]
  have h5 : derivSqJ P A C (genJ P A C * opPow m (genV P A C)) = 0 := by
    rw [hEJ_J, hJJ0, zero_mul]
  have h6 : derivSqSig P A C (virasoroModeChiral m P A C) = 0 := by
    rw [hChiralEq, hESig_Sig, hSigSig0, zero_mul]
  have h7 : derivSqPhi P A C (genJ P A C * opPow m (genV P A C)) =
      -((4 : ℤ) • (genV P A C * (genJ P A C * opPow m (genV P A C)))) := by
    rw [hEJ_Phi, hPhiJ0]
    noncomm_ring
  have hVSigPow :
      (genV P A C * genSig P A C) * opPow m (genV P A C) =
        virasoroModeChiral (m + 1) P A C := by
    have hVSigComm : genV P A C * genSig P A C = genSig P A C * genV P A C := by peirce_nf hP
    have hChiralNext : virasoroModeChiral (m + 1) P A C =
        genSig P A C * opPow (m + 1) (genV P A C) := by
      unfold virasoroModeChiral
      rw [show sugawaraTensor P A C = genV P A C by rfl,
        show chiralSchwinger P A C = genSig P A C by rfl,
        (opPow_genV_comm_genSig_explicit P A C (m + 1) hP).symm]
    calc (genV P A C * genSig P A C) * opPow m (genV P A C)
        = genSig P A C * (genV P A C * opPow m (genV P A C)) := by rw [hVSigComm, mul_assoc]
      _ = genSig P A C * (opPow m (genV P A C) * genV P A C) := by
        rw [(mul_opPow_comm m (genV P A C))]
      _ = genSig P A C * opPow (m + 1) (genV P A C) := by rw [← opPow_succ]
      _ = virasoroModeChiral (m + 1) P A C := by rw [← hChiralNext]
  have h8 : derivSqPhi P A C (virasoroModeChiral m P A C) =
      -((4 : ℤ) • virasoroModeChiral (m + 1) P A C) := by
    rw [hChiralEq, hESig_Phi, hPhiSig0, neg_mul, smul_mul_assoc, hVSigPow]
  have h9 : derivSqJ P A C (genPhi P A C * opPow m (genV P A C)) =
      -((4 : ℤ) • (genV P A C * (genPhi P A C * opPow m (genV P A C)))) := by
    rw [hEPhi_J, hJPhi0]
    noncomm_ring
  have h10 : derivSqJ P A C (virasoroModeChiral m P A C) =
      -((4 : ℤ) • virasoroModeChiral (m + 1) P A C) := by
    rw [hChiralEq, hESig_J, hJSig0, neg_mul, smul_mul_assoc, hVSigPow]
  have hLin : ∀ X Y : B, ∀ a b : ℤ,
      derivSqPhi P A C (a • X + b • Y) =
        a • derivSqPhi P A C X + b • derivSqPhi P A C Y := by
    intro X Y a b
    unfold derivSqPhi comm
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
               smul_sub, neg_sub]
    abel
  refine ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10⟩, ⟨?_, ?_⟩⟩
  · have hStep1 :=
      hLin (α • (genPhi P A C * opPow m (genV P A C)) + β • virasoroModeEven m P A C)
           (genJ P A C * opPow m (genV P A C)) 1 γ
    rw [one_smul, one_smul] at hStep1
    rw [hStep1, hLin, h4, h1, h7, smul_zero, smul_zero, add_zero, zero_add]
  · rw [hLin, h1, h8, smul_zero, zero_add]

/-- **Archetype `A₈₆` (`Z₄`, `archetype_A86_all_mode_chiral_virasoro_golay_leech_mog_and_sheet_ladder`):**
For every mode index `m : ℕ`:
1. **Scale-12 Golay and Scale-24 Leech Chiral Sign-Flip Ladders on `virasoroModeChiral m P A C`:**
   - `golay12Core P A C (virasoroModeChiral m P A C) = -((12 : ℤ) • virasoroModeChiral (m + 1) P A C)`,
   - `golay24G0 P A C (virasoroModeChiral m P A C) = -((24 : ℤ) • virasoroModeChiral (m + 1) P A C)`;
2. **Scale-24 MOG Chiral Isolation (`mog24V = 0` vs. `mog24Sig` Mode-Shift by `+2`):**
   - `mog24V P A C (virasoroModeChiral m P A C) = 0`,
   - `mog24Sig P A C (virasoroModeChiral m P A C) = (24 : ℤ) • virasoroModeChiral (m + 2) P A C`;
3. **All-Mode Single-Sheet MOG Decoding of `virasoroModeEven m P A C` and `virasoroModeChiral m P A C`:**
   - `mog24SheetPlus P A C (virasoroModeEven m P A C) = (24 : ℤ) • virasoroModeEven (m + 3) P A C`,
   - `mog24SheetMinus P A C (virasoroModeEven m P A C) = (24 : ℤ) • virasoroModeEven (m + 3) P A C`,
   - `mog24SheetPlus P A C (virasoroModeChiral m P A C) = (24 : ℤ) • virasoroModeEven (m + 3) P A C`,
   - `mog24SheetMinus P A C (virasoroModeChiral m P A C) = -((24 : ℤ) • virasoroModeEven (m + 3) P A C)`. -/
theorem archetype_A86_all_mode_chiral_virasoro_golay_leech_mog_and_sheet_ladder
    (A C : B) (m : ℕ) :
    (golay12Core P A C (virasoroModeChiral m P A C) =
       -((12 : ℤ) • virasoroModeChiral (m + 1) P A C) ∧
     golay24G0 P A C (virasoroModeChiral m P A C) =
       -((24 : ℤ) • virasoroModeChiral (m + 1) P A C)) ∧
    (mog24V P A C (virasoroModeChiral m P A C) = 0 ∧
     mog24Sig P A C (virasoroModeChiral m P A C) =
       (24 : ℤ) • virasoroModeChiral (m + 2) P A C) ∧
    (mog24SheetPlus P A C (virasoroModeEven m P A C) =
       (24 : ℤ) • virasoroModeEven (m + 3) P A C ∧
     mog24SheetMinus P A C (virasoroModeEven m P A C) =
       (24 : ℤ) • virasoroModeEven (m + 3) P A C ∧
     mog24SheetPlus P A C (virasoroModeChiral m P A C) =
       (24 : ℤ) • virasoroModeEven (m + 3) P A C ∧
     mog24SheetMinus P A C (virasoroModeChiral m P A C) =
       -((24 : ℤ) • virasoroModeEven (m + 3) P A C)) := by
  have hChiralEq : ∀ k : ℕ, virasoroModeChiral k P A C =
      genSig P A C * opPow k (genV P A C) := by
    intro k
    unfold virasoroModeChiral
    rw [show sugawaraTensor P A C = genV P A C by rfl,
      show chiralSchwinger P A C = genSig P A C by rfl,
      (opPow_genV_comm_genSig_explicit P A C k hP).symm]
  have hEvenEq : virasoroModeEven m P A C = genV P A C * opPow m (genV P A C) :=
    (mul_opPow_comm m (genV P A C)).symm
  rcases golay24_and_mog24_sheet_mul_opPow_genV hP A C (genSig P A C) m with
    ⟨hG0_Sig, hMV_Sig, hMSig_Sig, hShP_Sig, hShM_Sig⟩
  rcases golay24_and_mog24_sheet_mul_opPow_genV hP A C (genV P A C) m with
    ⟨_, _, _, hShP_V, hShM_V⟩
  have hG0_0 : golay24G0 P A C (genSig P A C) = -((24 : ℤ) • (genV P A C * genSig P A C)) := by
    rw [(archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hP A C (genSig P A C)).2.2.2.2.2.1]
    unfold kantorG0 kantorTriple
    peirce_nf hP
  have hG12_eq : ∀ X : B, (2 : ℤ) • golay12Core P A C X = golay24G0 P A C X := by
    intro X
    unfold golay12Core golay24G0
    abel
  have hG12_Sig :
      golay12Core P A C (genSig P A C * opPow m (genV P A C)) =
        golay12Core P A C (genSig P A C) * opPow m (genV P A C) := by
    let Z := opPow m (genV P A C)
    have hP' : P * Z = Z * P := (opPow_genV_comm_idem hP A C m).1
    have hCp' : conePlus P A * Z = Z * conePlus P A :=
      (opPow_genV_comm_invS_and_cones hP A C m).2.1
    have hCm' : coneMinus P C * Z = Z * coneMinus P C :=
      (opPow_genV_comm_invS_and_cones hP A C m).2.2
    have hK : ∀ X : B, kantorTotal P A C (X * Z) = kantorTotal P A C X * Z := by
      intro X
      unfold kantorTotal kantorGp2 kantorGp1 kantorG0 kantorGm1 kantorGm2
        kantorTriple comm
      have hPlusComm : conePlus P A * (X * Z) - (X * Z) * conePlus P A =
          (conePlus P A * X - X * conePlus P A) * Z := by
        calc conePlus P A * (X * Z) - (X * Z) * conePlus P A
            = conePlus P A * X * Z - X * (Z * conePlus P A) := by noncomm_ring
          _ = conePlus P A * X * Z - X * (conePlus P A * Z) := by rw [hCp'.symm]
          _ = (conePlus P A * X - X * conePlus P A) * Z := by noncomm_ring
      have hMinusComm : coneMinus P C * (X * Z) - (X * Z) * coneMinus P C =
          (coneMinus P C * X - X * coneMinus P C) * Z := by
        calc coneMinus P C * (X * Z) - (X * Z) * coneMinus P C
            = coneMinus P C * X * Z - X * (Z * coneMinus P C) := by noncomm_ring
          _ = coneMinus P C * X * Z - X * (coneMinus P C * Z) := by rw [hCm'.symm]
          _ = (coneMinus P C * X - X * coneMinus P C) * Z := by noncomm_ring
      have hPlusSand : conePlus P A * (X * Z) * conePlus P A =
          (conePlus P A * X * conePlus P A) * Z := by
        calc conePlus P A * (X * Z) * conePlus P A
            = conePlus P A * X * (Z * conePlus P A) := by noncomm_ring
          _ = conePlus P A * X * (conePlus P A * Z) := by rw [hCp'.symm]
          _ = (conePlus P A * X * conePlus P A) * Z := by noncomm_ring
      have hMinusSand : coneMinus P C * (X * Z) * coneMinus P C =
          (coneMinus P C * X * coneMinus P C) * Z := by
        calc coneMinus P C * (X * Z) * coneMinus P C
            = coneMinus P C * X * (Z * coneMinus P C) := by noncomm_ring
          _ = coneMinus P C * X * (coneMinus P C * Z) := by rw [hCm'.symm]
          _ = (coneMinus P C * X * coneMinus P C) * Z := by noncomm_ring
      have hTriple : conePlus P A * (X * Z) * coneMinus P C +
          coneMinus P C * (X * Z) * conePlus P A =
          (conePlus P A * X * coneMinus P C +
            coneMinus P C * X * conePlus P A) * Z := by
        have h₁ : conePlus P A * (X * Z) * coneMinus P C =
            (conePlus P A * X * coneMinus P C) * Z := by
          calc conePlus P A * (X * Z) * coneMinus P C
              = conePlus P A * X * (Z * coneMinus P C) := by noncomm_ring
            _ = conePlus P A * X * (coneMinus P C * Z) := by rw [hCm'.symm]
            _ = (conePlus P A * X * coneMinus P C) * Z := by noncomm_ring
        have h₂ : coneMinus P C * (X * Z) * conePlus P A =
            (coneMinus P C * X * conePlus P A) * Z := by
          calc coneMinus P C * (X * Z) * conePlus P A
              = coneMinus P C * X * (Z * conePlus P A) := by noncomm_ring
            _ = coneMinus P C * X * (conePlus P A * Z) := by rw [hCp'.symm]
            _ = (coneMinus P C * X * conePlus P A) * Z := by noncomm_ring
        rw [h₁, h₂]
        noncomm_ring
      rw [hPlusSand, hPlusComm, hTriple, hMinusComm, hMinusSand]
      noncomm_ring
    have hDelta : ∀ (K : B → B), (∀ X : B, K (X * Z) = K X * Z) →
        ∀ X : B, superChargeP K P (X * Z) = superChargeP K P X * Z := by
      intro K hK X
      change comm P (K (X * Z)) - K (comm P (X * Z)) =
        (comm P (K X) - K (comm P X)) * Z
      have hComm : comm P (X * Z) = comm P X * Z := by
        unfold comm
        rw [mul_assoc, ← hP']
        noncomm_ring
      have hKcomm : comm P (K X * Z) = comm P (K X) * Z := by
        unfold comm
        rw [mul_assoc, ← hP']
        noncomm_ring
      rw [hK X, hKcomm, hComm, hK (comm P X)]
      rw [sub_mul]
    have hD1 : ∀ X : B, kantorDelta1 P A C (X * Z) = kantorDelta1 P A C X * Z := by
      intro X
      exact hDelta _ hK X
    have hD2 : ∀ X : B, kantorDelta2 P A C (X * Z) = kantorDelta2 P A C X * Z := by
      intro X
      exact hDelta _ hD1 X
    have hD3 : ∀ X : B, kantorDelta3 P A C (X * Z) = kantorDelta3 P A C X * Z := by
      intro X
      exact hDelta _ hD2 X
    have hD4 : ∀ X : B, kantorDelta4 P A C (X * Z) = kantorDelta4 P A C X * Z := by
      intro X
      exact hDelta _ hD3 X
    unfold golay12Core
    rw [hD4, hD2, hK]
    noncomm_ring
  have hG12_0 : golay12Core P A C (genSig P A C) = -((12 : ℤ) • (genV P A C * genSig P A C)) := by
    rw [(archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hP A C (genSig P A C)).2.1]
    unfold sandwichCross
    peirce_nf hP
  have hPhiSig0 : derivSqPhi P A C (genSig P A C) = -((4 : ℤ) • (genV P A C * genSig P A C)) := by
    unfold derivSqPhi; peirce_nf hP
  have hJSig0 : derivSqJ P A C (genSig P A C) = -((4 : ℤ) • (genV P A C * genSig P A C)) := by
    unfold derivSqJ; peirce_nf hP
  have hSigSig0 : derivSqSig P A C (genSig P A C) = 0 := by unfold derivSqSig; peirce_nf hP
  have hMV_0 : mog24V P A C (genSig P A C) = 0 := by
    unfold mog24V hProjV
    rw [hPhiSig0, hJSig0, hSigSig0]
    noncomm_ring
  have hMSig_0 : mog24Sig P A C (genSig P A C) =
      (24 : ℤ) • (genV P A C * genV P A C * genSig P A C) := by
    unfold mog24Sig hProjSig
    rw [hPhiSig0, hJSig0, hSigSig0]
    noncomm_ring
  have hMV_V0 : mog24V P A C (genV P A C) =
      (24 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
    peirce_abel_golay hP
  have hMSig_V0 : mog24Sig P A C (genV P A C) = 0 := by
    peirce_abel_golay hP
  have hSigV3 : genSig P A C * (genV P A C * genV P A C * genSig P A C) =
      (genV P A C * genV P A C * genV P A C) * genV P A C := by
    peirce_nf hP
  have hVV3 : genV P A C * (genV P A C * genV P A C * genV P A C) =
      (genV P A C * genV P A C * genV P A C) * genV P A C := by
    simp only [mul_assoc]
  have hShP_V0 : mog24SheetPlus P A C (genV P A C) =
      (24 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genV P A C) := by
    unfold mog24SheetPlus
    rw [hMV_V0, hMSig_V0, mul_zero, add_zero, mul_smul_comm, hVV3]
  have hShM_V0 : mog24SheetMinus P A C (genV P A C) =
      (24 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genV P A C) := by
    unfold mog24SheetMinus
    rw [hMV_V0, hMSig_V0, mul_zero, sub_zero, mul_smul_comm, hVV3]
  have hShP_Sig0 : mog24SheetPlus P A C (genSig P A C) =
      (24 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genV P A C) := by
    unfold mog24SheetPlus
    rw [hMV_0, hMSig_0, mul_zero, zero_add, mul_smul_comm, hSigV3]
  have hShM_Sig0 : mog24SheetMinus P A C (genSig P A C) =
      -((24 : ℤ) • ((genV P A C * genV P A C * genV P A C) * genV P A C)) := by
    unfold mog24SheetMinus
    rw [hMV_0, hMSig_0, mul_zero, zero_sub, Algebra.mul_smul_comm, hSigV3]
  have hVSigPow :
      (genV P A C * genSig P A C) * opPow m (genV P A C) =
        virasoroModeChiral (m + 1) P A C := by
    have hVSigComm : genV P A C * genSig P A C = genSig P A C * genV P A C := by peirce_nf hP
    calc (genV P A C * genSig P A C) * opPow m (genV P A C)
        = genSig P A C * (genV P A C * opPow m (genV P A C)) := by rw [hVSigComm, mul_assoc]
      _ = genSig P A C * (opPow m (genV P A C) * genV P A C) := by
        rw [mul_opPow_comm m (genV P A C)]
      _ = genSig P A C * opPow (m + 1) (genV P A C) := by rw [← opPow_succ]
      _ = virasoroModeChiral (m + 1) P A C := (hChiralEq (m + 1)).symm
  have hV2SigPow :
      (genV P A C * genV P A C * genSig P A C) * opPow m (genV P A C) =
        virasoroModeChiral (m + 2) P A C := by
    have hVSigComm : genV P A C * genSig P A C = genSig P A C * genV P A C := by peirce_nf hP
    have hV2SigComm : (genV P A C * genV P A C) * genSig P A C =
        genSig P A C * (genV P A C * genV P A C) := by
      rw [mul_assoc, hVSigComm, ← mul_assoc, hVSigComm, mul_assoc]
    calc (genV P A C * genV P A C * genSig P A C) * opPow m (genV P A C)
        = genSig P A C * (genV P A C * (genV P A C * opPow m (genV P A C))) := by
          rw [hV2SigComm]; simp only [mul_assoc]
      _ = genSig P A C * (genV P A C * opPow (m + 1) (genV P A C)) := by
          rw [mul_opPow_comm m (genV P A C), ← opPow_succ]
      _ = genSig P A C * opPow (m + 2) (genV P A C) := by
          rw [mul_opPow_comm (m + 1) (genV P A C), ← opPow_succ]
      _ = virasoroModeChiral (m + 2) P A C := (hChiralEq (m + 2)).symm
  have hV3Pow :
      (genV P A C * genV P A C * genV P A C) * opPow m (genV P A C) =
        virasoroModeEven (m + 2) P A C := by
    have hComm1 := mul_opPow_comm m (genV P A C)
    have hComm2 := mul_opPow_comm (m + 1) (genV P A C)
    have hComm3 := mul_opPow_comm (m + 2) (genV P A C)
    calc (genV P A C * genV P A C * genV P A C) * opPow m (genV P A C)
      _ = (genV P A C * genV P A C) * (genV P A C * opPow m (genV P A C)) := by rw [mul_assoc]
      _ = (genV P A C * genV P A C) * opPow (m + 1) (genV P A C) := by rw [hComm1]; rfl
      _ = genV P A C * (genV P A C * opPow (m + 1) (genV P A C)) := by rw [mul_assoc]
      _ = genV P A C * opPow (m + 2) (genV P A C) := by rw [hComm2]; rfl
      _ = virasoroModeEven (m + 2) P A C := by rw [hComm3]; rfl
  have hV4Pow :
      ((genV P A C * genV P A C * genV P A C) * genV P A C) * opPow m (genV P A C) =
        virasoroModeEven (m + 3) P A C := by
    have hComm1 := mul_opPow_comm m (genV P A C)
    rw [mul_assoc, hComm1]
    change (genV P A C * genV P A C * genV P A C) * opPow (m + 1) (genV P A C) =
      virasoroModeEven (m + 3) P A C
    have hComm2 := mul_opPow_comm (m + 1) (genV P A C)
    have hComm3 := mul_opPow_comm (m + 2) (genV P A C)
    have hComm4 := mul_opPow_comm (m + 3) (genV P A C)
    calc (genV P A C * genV P A C * genV P A C) * opPow (m + 1) (genV P A C)
      _ = (genV P A C * genV P A C) * (genV P A C * opPow (m + 1) (genV P A C)) := by rw [mul_assoc]
      _ = (genV P A C * genV P A C) * opPow (m + 2) (genV P A C) := by rw [hComm2]; rfl
      _ = genV P A C * (genV P A C * opPow (m + 2) (genV P A C)) := by rw [mul_assoc]
      _ = genV P A C * opPow (m + 3) (genV P A C) := by rw [hComm3]; rfl
      _ = virasoroModeEven (m + 3) P A C := by rw [hComm4]; rfl
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hChiralEq m, hG12_Sig, hG12_0, neg_mul, smul_mul_assoc, hVSigPow]
  · rw [hChiralEq m, hG0_Sig, hG0_0, neg_mul, smul_mul_assoc, hVSigPow]
  · rw [hChiralEq m, hMV_Sig, hMV_0, zero_mul]
  · rw [hChiralEq m, hMSig_Sig, hMSig_0, smul_mul_assoc, hV2SigPow]
  · rw [hEvenEq, hShP_V, hShP_V0, smul_mul_assoc, hV4Pow]
  · rw [hEvenEq, hShM_V, hShM_V0, smul_mul_assoc, hV4Pow]
  · rw [hChiralEq m, hShP_Sig, hShP_Sig0, smul_mul_assoc, hV4Pow]
  · rw [hChiralEq m, hShM_Sig, hShM_Sig0, neg_mul, smul_mul_assoc, hV4Pow]

/-- **Archetype `A₈₇` (`Z₅`, `archetype_A87_all_mode_hopf_coordinates_mog_sheet_and_double_derivation`):**
In any `[StarRing B]` with self-adjoint idempotent `P` (`P * P = P`, `star P = P`), for any
`A : B` and mode index `r : ℕ`, let `J_p := heisenbergSourceMode r P A (star A)` and
`J_m := heisenbergSinkMode r P A (star A)`:
1. **All-Mode Single-Sheet MOG & Leech Decoding of `hopfRadiusSq J_p J_m` and `hopfCoordZ J_p J_m`:**
   - `mog24SheetPlus P A (star A) (hopfRadiusSq J_p J_m) = (24 : ℤ) • virasoroModeEven (r + r + 3) P A (star A)`,
   - `mog24SheetMinus P A (star A) (hopfRadiusSq J_p J_m) = (24 : ℤ) • virasoroModeEven (r + r + 3) P A (star A)`,
   - `mog24SheetPlus P A (star A) (hopfCoordZ J_p J_m) = (24 : ℤ) • virasoroModeEven (r + r + 3) P A (star A)`,
   - `mog24SheetMinus P A (star A) (hopfCoordZ J_p J_m) = -((24 : ℤ) • virasoroModeEven (r + r + 3) P A (star A))`,
   - `golay24G0 P A (star A) (hopfCoordZ J_p J_m) = (24 : ℤ) • virasoroModeChiral (r + r + 1) P A (star A)`;
2. **All-Mode Double-Derivation (`derivSqPhi`, `derivSqJ`, `derivSqSig`) Dichotomy on the Hopf Coordinates:**
   - `derivSqPhi P A (star A) (hopfRadiusSq J_p J_m) = 0`,
   - `derivSqPhi P A (star A) (hopfCoordZ J_p J_m) = -((4 : ℤ) • virasoroModeChiral (r + r + 1) P A (star A))`,
   - `derivSqJ P A (star A) (hopfCoordZ J_p J_m) = -((4 : ℤ) • virasoroModeChiral (r + r + 1) P A (star A))`,
   - `derivSqSig P A (star A) (hopfCoordZ J_p J_m) = 0`. -/
theorem archetype_A87_all_mode_hopf_coordinates_mog_sheet_and_double_derivation
    [StarRing B] (hPs : star P = P) (A : B) (r : ℕ) :
    let J_p := heisenbergSourceMode r P A (star A)
    let J_m := heisenbergSinkMode r P A (star A)
    (mog24SheetPlus P A (star A) (hopfRadiusSq J_p J_m) =
       (24 : ℤ) • virasoroModeEven (r + r + 3) P A (star A) ∧
     mog24SheetMinus P A (star A) (hopfRadiusSq J_p J_m) =
       (24 : ℤ) • virasoroModeEven (r + r + 3) P A (star A) ∧
     mog24SheetPlus P A (star A) (hopfCoordZ J_p J_m) =
       (24 : ℤ) • virasoroModeEven (r + r + 3) P A (star A) ∧
     mog24SheetMinus P A (star A) (hopfCoordZ J_p J_m) =
       -((24 : ℤ) • virasoroModeEven (r + r + 3) P A (star A)) ∧
     golay24G0 P A (star A) (hopfCoordZ J_p J_m) =
       -((24 : ℤ) • virasoroModeChiral (r + r + 1) P A (star A))) ∧
    (derivSqPhi P A (star A) (hopfRadiusSq J_p J_m) = 0 ∧
     derivSqPhi P A (star A) (hopfCoordZ J_p J_m) =
       -((4 : ℤ) • virasoroModeChiral (r + r + 1) P A (star A)) ∧
     derivSqJ P A (star A) (hopfCoordZ J_p J_m) =
       -((4 : ℤ) • virasoroModeChiral (r + r + 1) P A (star A)) ∧
     derivSqSig P A (star A) (hopfCoordZ J_p J_m) = 0) := by
  intro J_p J_m
  rcases all_mode_heisenberg_virasoro_hopf_coordinate_identity_and_furey_tower hP hPs A r with
    ⟨_, _, hHopfZ, _, hHopfRad, _, _⟩
  rcases archetype_A86_all_mode_chiral_virasoro_golay_leech_mog_and_sheet_ladder
      hP A (star A) (r + r) with
    ⟨⟨_, hG0_Z⟩, _, ⟨hShP_Rad, hShM_Rad, hShP_Z, hShM_Z⟩⟩
  rcases archetype_A85_all_mode_double_derivation_virasoro_dichotomy_and_projection
      hP A (star A) (r + r) 0 0 0 with
    ⟨⟨hDPhi_Rad, _, _, _, _, hDSig_Z⟩, ⟨_, hDPhi_Z, _, hDJ_Z⟩, _⟩
  rw [hHopfRad, hHopfZ]
  exact ⟨⟨hShP_Rad, hShM_Rad, hShP_Z, hShM_Z, hG0_Z⟩,
         ⟨hDPhi_Rad, hDPhi_Z, hDJ_Z, hDSig_Z⟩⟩

/-- **Archetype `A₈₈` (`Z₆`, `archetype_A88_all_mode_zorn_drinfeld_nonassoc_associativity_and_norm_ladder`):**
For any cross-cut bridge `M : B`, any `A, C : B`, and any mode indices `r, s : ℕ`:
1. **Universal Wedge Vanishing on All Drinfeld Currents and Heisenberg Currents:**
   - `zornWedgePlus P M (drinfeldPhiMinus r P A C) (drinfeldPhiMinus s P A C) = 0`,
   - `zornWedgeMinus P M (drinfeldPhiPlus r P A C) (drinfeldPhiPlus s P A C) = 0`,
   - `zornWedgePlus P M (heisenbergSinkMode r P A C) (heisenbergSinkMode s P A C) = 0`,
   - `zornWedgeMinus P M (heisenbergSourceMode r P A C) (heisenbergSourceMode s P A C) = 0`;
2. **All-Mode `(r, s)` Associative Reduction of `zornNonAssocMul` on Zorn–Drinfeld Matrices:**
   `zornNonAssocMul P M (opPow r (genV P A C)) (opPow r (genV P A C))`
   `  (drinfeldPhiPlus r P A C) (drinfeldPhiMinus r P A C)`
   `  (opPow s (genV P A C)) (opPow s (genV P A C))`
   `  (drinfeldPhiPlus s P A C) (drinfeldPhiMinus s P A C) =`
   `zornDrinfeldMatrix r r P A C * zornDrinfeldMatrix s s P A C`;
3. **Scale-12 Golay, Scale-24 Leech, Scale-24 MOG, & Double-Derivation Ladders on the Zorn–Drinfeld Norm:**
   - `golay12Core P A C (zornNorm P (zornDrinfeldMatrix (r + 1) (r + 1) P A C)) =`
     `(12 : ℤ) • (virasoroModeEven (r + 1 + (r + 1)) P A C - virasoroModeEven (r + 1 + (r + 1) + 1) P A C)`,
   - `golay24G0 P A C (zornNorm P (zornDrinfeldMatrix (r + 1) (r + 1) P A C)) =`
     `(24 : ℤ) • (virasoroModeEven (r + 1 + (r + 1)) P A C - virasoroModeEven (r + 1 + (r + 1) + 1) P A C)`,
   - `derivSqPhi P A C (zornNorm P (zornDrinfeldMatrix (r + 1) (r + 1) P A C)) = 0`. -/
theorem archetype_A88_all_mode_zorn_drinfeld_nonassoc_associativity_and_norm_ladder
    (M A C : B) (r s : ℕ) :
    (zornWedgePlus P M (drinfeldPhiMinus r P A C) (drinfeldPhiMinus s P A C) = 0 ∧
     zornWedgeMinus P M (drinfeldPhiPlus r P A C) (drinfeldPhiPlus s P A C) = 0 ∧
     zornWedgePlus P M (heisenbergSinkMode r P A C) (heisenbergSinkMode s P A C) = 0 ∧
     zornWedgeMinus P M (heisenbergSourceMode r P A C) (heisenbergSourceMode s P A C) = 0) ∧
    zornNonAssocMul P M
        (opPow r (genV P A C)) (opPow r (genV P A C))
        (-heisenbergSourceMode r P A C) (heisenbergSinkMode r P A C)
        (opPow s (genV P A C)) (opPow s (genV P A C))
        (-heisenbergSourceMode s P A C) (heisenbergSinkMode s P A C) =
      zornDrinfeldMatrix r r P A C * zornDrinfeldMatrix s s P A C ∧
    (golay12Core P A C (zornNorm P (zornDrinfeldMatrix (r + 1) (r + 1) P A C)) =
       (12 : ℤ) • (virasoroModeEven (r + 1 + (r + 1)) P A C -
         virasoroModeEven (r + 1 + (r + 1) + 1) P A C) ∧
     golay24G0 P A C (zornNorm P (zornDrinfeldMatrix (r + 1) (r + 1) P A C)) =
       (24 : ℤ) • (virasoroModeEven (r + 1 + (r + 1)) P A C -
         virasoroModeEven (r + 1 + (r + 1) + 1) P A C) ∧
     derivSqPhi P A C (zornNorm P (zornDrinfeldMatrix (r + 1) (r + 1) P A C)) = 0) := by
  have hP_Qm : ∀ k : ℕ, P * drinfeldPhiMinus k P A C = 0 := by
    intro k
    unfold drinfeldPhiMinus
    rw [← mul_assoc, (opPow_genV_comm_idem hP A C k).1, mul_assoc]
    have hPQm0 : P * qgtMinus P A C = 0 := by
      unfold qgtMinus coneMinus conePlus
      peirce_nf hP
    rw [hPQm0, mul_zero]
  have hComp_Qp : ∀ k : ℕ, (1 - P) * drinfeldPhiPlus k P A C = 0 := by
    intro k
    unfold drinfeldPhiPlus
    have hCompPow : (1 - P) * opPow k (genV P A C) = opPow k (genV P A C) * (1 - P) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, (opPow_genV_comm_idem hP A C k).1]
    rw [← mul_assoc, hCompPow, mul_assoc]
    have hCompQp0 : (1 - P) * qgtPlus P A C = 0 := by
      unfold qgtPlus conePlus coneMinus
      peirce_nf hP
    rw [hCompQp0, mul_zero]
  have hP_Snk : ∀ k : ℕ, P * heisenbergSinkMode k P A C = 0 := by
    intro k
    change P * (coneMinus P C * opPow k (genV P A C)) = 0
    have hPCm0 : P * coneMinus P C = 0 := by peirce_nf hP
    rw [← mul_assoc, hPCm0, zero_mul]
  have hComp_Src : ∀ k : ℕ, (1 - P) * heisenbergSourceMode k P A C = 0 := by
    intro k
    change (1 - P) * (opPow k (genV P A C) * conePlus P A) = 0
    have hCompPow : (1 - P) * opPow k (genV P A C) =
        opPow k (genV P A C) * (1 - P) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, (opPow_genV_comm_idem hP A C k).1]
    rw [← mul_assoc, hCompPow, mul_assoc]
    have hCompCp0 : (1 - P) * conePlus P A = 0 := by
      unfold conePlus
      peirce_nf hP
    rw [hCompCp0, mul_zero]
  have hW1 : zornWedgePlus P M (drinfeldPhiMinus r P A C) (drinfeldPhiMinus s P A C) = 0 := by
    unfold zornWedgePlus conePlus
    have hr : P * (drinfeldPhiMinus r P A C * M * drinfeldPhiMinus s P A C) = 0 := by
      calc P * (drinfeldPhiMinus r P A C * M * drinfeldPhiMinus s P A C)
          = ((P * drinfeldPhiMinus r P A C) * M) * drinfeldPhiMinus s P A C := by noncomm_ring
        _ = 0 := by rw [hP_Qm r]; simp
    have hs : P * (drinfeldPhiMinus s P A C * M * drinfeldPhiMinus r P A C) = 0 := by
      calc P * (drinfeldPhiMinus s P A C * M * drinfeldPhiMinus r P A C)
          = ((P * drinfeldPhiMinus s P A C) * M) * drinfeldPhiMinus r P A C := by noncomm_ring
        _ = 0 := by rw [hP_Qm s]; simp
    change P * (drinfeldPhiMinus r P A C * M * drinfeldPhiMinus s P A C -
      drinfeldPhiMinus s P A C * M * drinfeldPhiMinus r P A C) * (1 - P) = 0
    calc P * (drinfeldPhiMinus r P A C * M * drinfeldPhiMinus s P A C -
          drinfeldPhiMinus s P A C * M * drinfeldPhiMinus r P A C) * (1 - P)
        = (P * (drinfeldPhiMinus r P A C * M * drinfeldPhiMinus s P A C)) * (1 - P) -
          (P * (drinfeldPhiMinus s P A C * M * drinfeldPhiMinus r P A C)) * (1 - P) := by noncomm_ring
      _ = 0 := by rw [hr, hs]; simp
  have hW2 : zornWedgeMinus P M (drinfeldPhiPlus r P A C) (drinfeldPhiPlus s P A C) = 0 := by
    unfold zornWedgeMinus coneMinus
    have hr : (1 - P) * (drinfeldPhiPlus r P A C * M * drinfeldPhiPlus s P A C) = 0 := by
      calc (1 - P) * (drinfeldPhiPlus r P A C * M * drinfeldPhiPlus s P A C)
          = (((1 - P) * drinfeldPhiPlus r P A C) * M) * drinfeldPhiPlus s P A C := by noncomm_ring
        _ = 0 := by rw [hComp_Qp r]; simp
    have hs : (1 - P) * (drinfeldPhiPlus s P A C * M * drinfeldPhiPlus r P A C) = 0 := by
      calc (1 - P) * (drinfeldPhiPlus s P A C * M * drinfeldPhiPlus r P A C)
          = (((1 - P) * drinfeldPhiPlus s P A C) * M) * drinfeldPhiPlus r P A C := by noncomm_ring
        _ = 0 := by rw [hComp_Qp s]; simp
    change (1 - P) * (drinfeldPhiPlus r P A C * M * drinfeldPhiPlus s P A C -
      drinfeldPhiPlus s P A C * M * drinfeldPhiPlus r P A C) * P = 0
    calc (1 - P) * (drinfeldPhiPlus r P A C * M * drinfeldPhiPlus s P A C -
          drinfeldPhiPlus s P A C * M * drinfeldPhiPlus r P A C) * P
        = ((1 - P) * (drinfeldPhiPlus r P A C * M * drinfeldPhiPlus s P A C)) * P -
          ((1 - P) * (drinfeldPhiPlus s P A C * M * drinfeldPhiPlus r P A C)) * P := by noncomm_ring
      _ = 0 := by rw [hr, hs]; simp
  have hW3 : zornWedgePlus P M (heisenbergSinkMode r P A C) (heisenbergSinkMode s P A C) = 0 := by
    unfold zornWedgePlus conePlus
    have hr : P * (heisenbergSinkMode r P A C * M * heisenbergSinkMode s P A C) = 0 := by
      calc P * (heisenbergSinkMode r P A C * M * heisenbergSinkMode s P A C)
          = ((P * heisenbergSinkMode r P A C) * M) * heisenbergSinkMode s P A C := by noncomm_ring
        _ = 0 := by rw [hP_Snk r]; simp
    have hs : P * (heisenbergSinkMode s P A C * M * heisenbergSinkMode r P A C) = 0 := by
      calc P * (heisenbergSinkMode s P A C * M * heisenbergSinkMode r P A C)
          = ((P * heisenbergSinkMode s P A C) * M) * heisenbergSinkMode r P A C := by noncomm_ring
        _ = 0 := by rw [hP_Snk s]; simp
    change P * (heisenbergSinkMode r P A C * M * heisenbergSinkMode s P A C -
      heisenbergSinkMode s P A C * M * heisenbergSinkMode r P A C) * (1 - P) = 0
    calc P * (heisenbergSinkMode r P A C * M * heisenbergSinkMode s P A C -
          heisenbergSinkMode s P A C * M * heisenbergSinkMode r P A C) * (1 - P)
        = (P * (heisenbergSinkMode r P A C * M * heisenbergSinkMode s P A C)) * (1 - P) -
          (P * (heisenbergSinkMode s P A C * M * heisenbergSinkMode r P A C)) * (1 - P) := by noncomm_ring
      _ = 0 := by rw [hr, hs]; simp
  have hW4 : zornWedgeMinus P M (heisenbergSourceMode r P A C) (heisenbergSourceMode s P A C) = 0 := by
    unfold zornWedgeMinus coneMinus
    have hr : (1 - P) * (heisenbergSourceMode r P A C * M * heisenbergSourceMode s P A C) = 0 := by
      calc (1 - P) * (heisenbergSourceMode r P A C * M * heisenbergSourceMode s P A C)
          = (((1 - P) * heisenbergSourceMode r P A C) * M) * heisenbergSourceMode s P A C := by noncomm_ring
        _ = 0 := by rw [hComp_Src r]; simp
    have hs : (1 - P) * (heisenbergSourceMode s P A C * M * heisenbergSourceMode r P A C) = 0 := by
      calc (1 - P) * (heisenbergSourceMode s P A C * M * heisenbergSourceMode r P A C)
          = (((1 - P) * heisenbergSourceMode s P A C) * M) * heisenbergSourceMode r P A C := by noncomm_ring
        _ = 0 := by rw [hComp_Src s]; simp
    change (1 - P) * (heisenbergSourceMode r P A C * M * heisenbergSourceMode s P A C -
      heisenbergSourceMode s P A C * M * heisenbergSourceMode r P A C) * P = 0
    calc (1 - P) * (heisenbergSourceMode r P A C * M * heisenbergSourceMode s P A C -
          heisenbergSourceMode s P A C * M * heisenbergSourceMode r P A C) * P
        = ((1 - P) * (heisenbergSourceMode r P A C * M * heisenbergSourceMode s P A C)) * P -
          ((1 - P) * (heisenbergSourceMode s P A C * M * heisenbergSourceMode r P A C)) * P := by noncomm_ring
      _ = 0 := by rw [hr, hs]; simp
  have hW4_neg : zornWedgeMinus P M (-heisenbergSourceMode r P A C) (-heisenbergSourceMode s P A C) = 0 := by
    unfold zornWedgeMinus coneMinus
    simp only [neg_mul, mul_neg, neg_neg]
    exact hW4
  have hZornMul :
      zornNonAssocMul P M
          (opPow r (genV P A C)) (opPow r (genV P A C))
          (-heisenbergSourceMode r P A C) (heisenbergSinkMode r P A C)
          (opPow s (genV P A C)) (opPow s (genV P A C))
          (-heisenbergSourceMode s P A C) (heisenbergSinkMode s P A C) =
        zornDrinfeldMatrix r r P A C * zornDrinfeldMatrix s s P A C := by
    unfold zornNonAssocMul zornDrinfeldMatrix
    rw [hW3, hW4_neg, sub_zero, add_zero]
  have hNormEq :
      zornNorm P (zornDrinfeldMatrix (r + 1) (r + 1) P A C) =
        virasoroModeEven (r + 1 + r) P A C - virasoroModeEven (r + 1 + (r + 1)) P A C := by
    have hNorm := (zornDrinfeldMatrix_eq_and_zornNorm hP A C (r + 1)).2.2
    rw [hNorm]
    rfl
  rcases stage_D40_all_mode_virasoro_golay_leech_mog_ladder hP A C (r + 1 + r) with
    ⟨hG12_a, _, _, hG24_a, _⟩
  rcases stage_D40_all_mode_virasoro_golay_leech_mog_ladder hP A C (r + 1 + (r + 1)) with
    ⟨hG12_b, _, _, hG24_b, _⟩
  have hG12_sub : ∀ X Y : B,
      golay12Core P A C (X - Y) = golay12Core P A C X - golay12Core P A C Y := by
    intro X Y
    have hLin : ∀ (K : B → B), (∀ X Y : B, K (X - Y) = K X - K Y) →
        ∀ X Y : B, superChargeP K P (X - Y) = superChargeP K P X - superChargeP K P Y := by
      intro K hK X Y
      have hComm : ∀ U V : B, comm P (U - V) = comm P U - comm P V := by
        intro U V
        unfold comm
        noncomm_ring
      change comm P (K (X - Y)) - K (comm P (X - Y)) =
        (comm P (K X) - K (comm P X)) - (comm P (K Y) - K (comm P Y))
      rw [hK X Y, hComm (K X) (K Y), hComm X Y,
        hK (comm P X) (comm P Y)]
      abel
    have hTot : ∀ X Y : B, kantorTotal P A C (X - Y) =
        kantorTotal P A C X - kantorTotal P A C Y := by
      intro X Y
      unfold kantorTotal kantorGp2 kantorGp1 kantorG0 kantorGm1 kantorGm2 kantorTriple comm
      noncomm_ring
    have hD1 : ∀ X Y : B, kantorDelta1 P A C (X - Y) =
        kantorDelta1 P A C X - kantorDelta1 P A C Y := by
      intro X Y
      change superChargeP (kantorTotal P A C) P (X - Y) = _
      exact hLin _ hTot X Y
    have hD2 : ∀ X Y : B, kantorDelta2 P A C (X - Y) =
        kantorDelta2 P A C X - kantorDelta2 P A C Y := by
      intro X Y
      change superChargeP (kantorDelta1 P A C) P (X - Y) = _
      exact hLin _ hD1 X Y
    have hD3 : ∀ X Y : B, kantorDelta3 P A C (X - Y) =
        kantorDelta3 P A C X - kantorDelta3 P A C Y := by
      intro X Y
      change superChargeP (kantorDelta2 P A C) P (X - Y) = _
      exact hLin _ hD2 X Y
    have hD4 : ∀ X Y : B, kantorDelta4 P A C (X - Y) =
        kantorDelta4 P A C X - kantorDelta4 P A C Y := by
      intro X Y
      change superChargeP (kantorDelta3 P A C) P (X - Y) = _
      exact hLin _ hD3 X Y
    unfold golay12Core
    rw [hD4, hD2, hTot]
    simp only [smul_sub]
    abel
  have hG24_sub : ∀ X Y : B,
      golay24G0 P A C (X - Y) = golay24G0 P A C X - golay24G0 P A C Y := by
    intro X Y
    have hEq : ∀ Z : B, (2 : ℤ) • golay12Core P A C Z = golay24G0 P A C Z := by
      intro Z
      unfold golay12Core golay24G0
      abel
    calc golay24G0 P A C (X - Y)
        = (2 : ℤ) • golay12Core P A C (X - Y) := (hEq (X - Y)).symm
      _ = (2 : ℤ) • (golay12Core P A C X - golay12Core P A C Y) := by rw [hG12_sub]
      _ = (2 : ℤ) • golay12Core P A C X - (2 : ℤ) • golay12Core P A C Y := by
        rw [two_zsmul]; abel
      _ = golay24G0 P A C X - golay24G0 P A C Y := by rw [hEq X, hEq Y]
  have hDPhi_sub : ∀ X Y : B,
      derivSqPhi P A C (X - Y) = derivSqPhi P A C X - derivSqPhi P A C Y := by
    intro X Y
    unfold derivSqPhi comm
    noncomm_ring
  have hDPhi_a :=
    (archetype_A85_all_mode_double_derivation_virasoro_dichotomy_and_projection
      hP A C (r + 1 + r) 0 0 0).1.1
  have hDPhi_b :=
    (archetype_A85_all_mode_double_derivation_virasoro_dichotomy_and_projection
      hP A C (r + 1 + (r + 1)) 0 0 0).1.1
  refine ⟨⟨hW1, hW2, hW3, hW4⟩, hZornMul, ⟨?_, ?_, ?_⟩⟩
  · rw [hNormEq, hG12_sub, hG12_a, hG12_b, ← smul_sub]
    rfl
  · rw [hNormEq, hG24_sub, hG24_a, hG24_b, ← smul_sub]
    rfl
  · rw [hNormEq, hDPhi_sub, hDPhi_a, hDPhi_b, sub_self]

end Tier3

/-! ### Part 5: Tier 4 Canonical Synthesis Theorems (`A₈₉ → A₉₄` / `M₁ → M₆`) -/

section Tier4

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

/-- **Archetype `A₈₉` (`M₁`, `archetype_A89_peirce_bdg_square_commutator_anomaly_and_grading_symmetrization`):**
For any non-commutative ring `B`, idempotent `P² = P`, seeds `A, C : B`, and mode index `r : ℕ`:
1. **Unperturbed Chiral-Grading Square (`invS P + genPhi P A C * V^r`):**
   Since the grading involution `invS P = P - (1 - P)` anticommutes with every odd mode
   `genPhi P A C * opPow r (genV P A C)`, the square of `invS P + genPhi P A C * opPow r (genV P A C)`
   has zero off-diagonal anomaly and equals `1 + virasoroModeEven (r + r) P A C`:
   - `anticomm (invS P) (genPhi P A C * opPow r (genV P A C)) = 0`,
   - `comm (invS P) (genPhi P A C * opPow r (genV P A C)) =`
     `(2 : ℤ) • (genJ P A C * opPow r (genV P A C))`,
   - `(invS P + genPhi P A C * opPow r (genV P A C)) * (invS P + genPhi P A C * opPow r (genV P A C)) =`
     `1 + virasoroModeEven (r + r) P A C`,
   - `(invS P + genJ P A C * opPow r (genV P A C)) * (invS P + genJ P A C * opPow r (genV P A C)) =`
     `1 - virasoroModeEven (r + r) P A C`;
2. **Idempotent-Perturbed Square Anomaly (`P + genPhi P A C * V^r`) & Grading Symmetrization:**
   Replacing `invS P` by the idempotent `P` introduces an odd off-diagonal anomaly
   `anticomm P (genPhi P A C * opPow r (genV P A C)) = genPhi P A C * opPow r (genV P A C)`,
   which is negated under grading conjugation `invS P * (·) * invS P` and canceled by
   symmetrization or complementary-idempotent averaging:
   - `comm P (genPhi P A C * opPow r (genV P A C)) = genJ P A C * opPow r (genV P A C)`,
   - `anticomm P (genPhi P A C * opPow r (genV P A C)) = genPhi P A C * opPow r (genV P A C)`,
   - `(P + genPhi P A C * opPow r (genV P A C)) * (P + genPhi P A C * opPow r (genV P A C)) =`
     `P + genPhi P A C * opPow r (genV P A C) + virasoroModeEven (r + r) P A C`,
   - `(P + genPhi P A C * opPow r (genV P A C)) * (P + genPhi P A C * opPow r (genV P A C)) +`
     `  invS P * ((P + genPhi P A C * opPow r (genV P A C)) * (P + genPhi P A C * opPow r (genV P A C))) * invS P =`
     `(2 : ℤ) • (P + virasoroModeEven (r + r) P A C)`,
   - `(P + genPhi P A C * opPow r (genV P A C)) * (P + genPhi P A C * opPow r (genV P A C)) +`
     `  ((1 - P) - genPhi P A C * opPow r (genV P A C)) * ((1 - P) - genPhi P A C * opPow r (genV P A C)) =`
     `1 + (2 : ℤ) • virasoroModeEven (r + r) P A C`. -/
theorem archetype_A89_peirce_bdg_square_commutator_anomaly_and_grading_symmetrization
    (A C : B) (r : ℕ) :
    (anticomm (invS P) (genPhi P A C * opPow r (genV P A C)) = 0 ∧
     comm (invS P) (genPhi P A C * opPow r (genV P A C)) =
       (2 : ℤ) • (genJ P A C * opPow r (genV P A C)) ∧
     (invS P + genPhi P A C * opPow r (genV P A C)) *
         (invS P + genPhi P A C * opPow r (genV P A C)) =
       1 + virasoroModeEven (r + r) P A C ∧
     (invS P + genJ P A C * opPow r (genV P A C)) *
         (invS P + genJ P A C * opPow r (genV P A C)) =
       1 - virasoroModeEven (r + r) P A C) ∧
    (comm P (genPhi P A C * opPow r (genV P A C)) = genJ P A C * opPow r (genV P A C) ∧
     anticomm P (genPhi P A C * opPow r (genV P A C)) = genPhi P A C * opPow r (genV P A C) ∧
     (P + genPhi P A C * opPow r (genV P A C)) *
         (P + genPhi P A C * opPow r (genV P A C)) =
       P + genPhi P A C * opPow r (genV P A C) + virasoroModeEven (r + r) P A C ∧
     (P + genPhi P A C * opPow r (genV P A C)) *
         (P + genPhi P A C * opPow r (genV P A C)) +
       invS P *
         ((P + genPhi P A C * opPow r (genV P A C)) *
           (P + genPhi P A C * opPow r (genV P A C))) *
         invS P =
       (2 : ℤ) • (P + virasoroModeEven (r + r) P A C) ∧
     (P + genPhi P A C * opPow r (genV P A C)) *
         (P + genPhi P A C * opPow r (genV P A C)) +
       ((1 - P) - genPhi P A C * opPow r (genV P A C)) *
         ((1 - P) - genPhi P A C * opPow r (genV P A C)) =
       1 + (2 : ℤ) • virasoroModeEven (r + r) P A C) := by
  have hVP : ∀ k : ℕ, opPow k (genV P A C) * P = P * opPow k (genV P A C) :=
    fun k => (opPow_genV_comm_idem hP A C k).1.symm
  have hVS : ∀ k : ℕ, opPow k (genV P A C) * invS P = invS P * opPow k (genV P A C) :=
    fun k => (opPow_genV_comm_invS_and_cones hP A C k).1.symm
  have hVPhi : ∀ k : ℕ, opPow k (genV P A C) * genPhi P A C = genPhi P A C * opPow k (genV P A C) := by
    intro k
    rcases opPow_genV_comm_invS_and_cones hP A C k with ⟨_, hCp, hCm⟩
    unfold genPhi
    rw [mul_add, add_mul, hCp, hCm]
  have hVJ : ∀ k : ℕ, opPow k (genV P A C) * genJ P A C = genJ P A C * opPow k (genV P A C) := by
    intro k
    rcases opPow_genV_comm_invS_and_cones hP A C k with ⟨_, hCp, hCm⟩
    unfold genJ
    rw [mul_sub, sub_mul, hCp, hCm]
  have hS_sq : invS P * invS P = 1 := by peirce_nf hP
  have hS_P_S : invS P * P * invS P = P := by peirce_nf hP
  have hS_Phi_anti : invS P * genPhi P A C + genPhi P A C * invS P = 0 := by peirce_nf hP
  have hS_J_anti : invS P * genJ P A C + genJ P A C * invS P = 0 := by peirce_nf hP
  have hS_Phi_comm : invS P * genPhi P A C - genPhi P A C * invS P = (2 : ℤ) • genJ P A C := by
    peirce_nf hP
  have hP_Phi_comm : P * genPhi P A C - genPhi P A C * P = genJ P A C := by peirce_nf hP
  have hP_Phi_anti : P * genPhi P A C + genPhi P A C * P = genPhi P A C := by peirce_nf hP
  have hPhi_sq : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
  have hJ_sq : genJ P A C * genJ P A C = -genV P A C := by peirce_nf hP
  have hS_Phi_conj : invS P * genPhi P A C * invS P = -genPhi P A C := by peirce_nf hP
  have hAntiS_Phi : anticomm (invS P) (genPhi P A C * opPow r (genV P A C)) = 0 := by
    unfold anticomm
    calc invS P * (genPhi P A C * opPow r (genV P A C)) +
           (genPhi P A C * opPow r (genV P A C)) * invS P
        = (invS P * genPhi P A C) * opPow r (genV P A C) +
          genPhi P A C * (opPow r (genV P A C) * invS P) := by noncomm_ring
      _ = (invS P * genPhi P A C) * opPow r (genV P A C) +
          genPhi P A C * (invS P * opPow r (genV P A C)) := by rw [hVS r]
      _ = (invS P * genPhi P A C + genPhi P A C * invS P) * opPow r (genV P A C) := by noncomm_ring
      _ = 0 := by rw [hS_Phi_anti, zero_mul]
  have hAntiS_J : anticomm (invS P) (genJ P A C * opPow r (genV P A C)) = 0 := by
    unfold anticomm
    calc invS P * (genJ P A C * opPow r (genV P A C)) +
           (genJ P A C * opPow r (genV P A C)) * invS P
        = (invS P * genJ P A C) * opPow r (genV P A C) +
          genJ P A C * (opPow r (genV P A C) * invS P) := by noncomm_ring
      _ = (invS P * genJ P A C) * opPow r (genV P A C) +
          genJ P A C * (invS P * opPow r (genV P A C)) := by rw [hVS r]
      _ = (invS P * genJ P A C + genJ P A C * invS P) * opPow r (genV P A C) := by noncomm_ring
      _ = 0 := by rw [hS_J_anti, zero_mul]
  have hCommS_Phi :
      comm (invS P) (genPhi P A C * opPow r (genV P A C)) =
        (2 : ℤ) • (genJ P A C * opPow r (genV P A C)) := by
    unfold comm
    calc invS P * (genPhi P A C * opPow r (genV P A C)) -
           (genPhi P A C * opPow r (genV P A C)) * invS P
        = (invS P * genPhi P A C) * opPow r (genV P A C) -
          genPhi P A C * (opPow r (genV P A C) * invS P) := by noncomm_ring
      _ = (invS P * genPhi P A C) * opPow r (genV P A C) -
          genPhi P A C * (invS P * opPow r (genV P A C)) := by rw [hVS r]
      _ = (invS P * genPhi P A C - genPhi P A C * invS P) * opPow r (genV P A C) := by noncomm_ring
      _ = ((2 : ℤ) • genJ P A C) * opPow r (genV P A C) := by rw [hS_Phi_comm]
      _ = (2 : ℤ) • (genJ P A C * opPow r (genV P A C)) := by rw [two_zsmul, two_zsmul]; noncomm_ring
  have hCommP_Phi :
      comm P (genPhi P A C * opPow r (genV P A C)) =
        genJ P A C * opPow r (genV P A C) := by
    unfold comm
    calc P * (genPhi P A C * opPow r (genV P A C)) -
           (genPhi P A C * opPow r (genV P A C)) * P
        = (P * genPhi P A C) * opPow r (genV P A C) -
          genPhi P A C * (opPow r (genV P A C) * P) := by noncomm_ring
      _ = (P * genPhi P A C) * opPow r (genV P A C) -
          genPhi P A C * (P * opPow r (genV P A C)) := by rw [hVP r]
      _ = (P * genPhi P A C - genPhi P A C * P) * opPow r (genV P A C) := by noncomm_ring
      _ = genJ P A C * opPow r (genV P A C) := by rw [hP_Phi_comm]
  have hAntiP_Phi :
      anticomm P (genPhi P A C * opPow r (genV P A C)) =
        genPhi P A C * opPow r (genV P A C) := by
    unfold anticomm
    calc P * (genPhi P A C * opPow r (genV P A C)) +
           (genPhi P A C * opPow r (genV P A C)) * P
        = (P * genPhi P A C) * opPow r (genV P A C) +
          genPhi P A C * (opPow r (genV P A C) * P) := by noncomm_ring
      _ = (P * genPhi P A C) * opPow r (genV P A C) +
          genPhi P A C * (P * opPow r (genV P A C)) := by rw [hVP r]
      _ = (P * genPhi P A C + genPhi P A C * P) * opPow r (genV P A C) := by noncomm_ring
      _ = genPhi P A C * opPow r (genV P A C) := by rw [hP_Phi_anti]
  have hPhiMode_sq :
      (genPhi P A C * opPow r (genV P A C)) * (genPhi P A C * opPow r (genV P A C)) =
        virasoroModeEven (r + r) P A C := by
    calc (genPhi P A C * opPow r (genV P A C)) * (genPhi P A C * opPow r (genV P A C))
        = genPhi P A C * (opPow r (genV P A C) * genPhi P A C) * opPow r (genV P A C) := by noncomm_ring
      _ = (genPhi P A C * genPhi P A C) * (opPow r (genV P A C) * opPow r (genV P A C)) := by
          rw [hVPhi r]; noncomm_ring
      _ = genV P A C * opPow (r + r) (genV P A C) := by
          rw [hPhi_sq, ← opPow_add r r (genV P A C)]
      _ = virasoroModeEven (r + r) P A C := mul_opPow_comm (r + r) (genV P A C)
  have hJMode_sq :
      (genJ P A C * opPow r (genV P A C)) * (genJ P A C * opPow r (genV P A C)) =
        -virasoroModeEven (r + r) P A C := by
    calc (genJ P A C * opPow r (genV P A C)) * (genJ P A C * opPow r (genV P A C))
        = genJ P A C * (opPow r (genV P A C) * genJ P A C) * opPow r (genV P A C) := by noncomm_ring
      _ = (genJ P A C * genJ P A C) * (opPow r (genV P A C) * opPow r (genV P A C)) := by
          rw [hVJ r]; noncomm_ring
      _ = -(genV P A C * opPow (r + r) (genV P A C)) := by
          rw [hJ_sq, ← opPow_add r r (genV P A C), neg_mul]
      _ = -virasoroModeEven (r + r) P A C :=
          congrArg Neg.neg (mul_opPow_comm (r + r) (genV P A C))
  have hSq_S_Phi :
      (invS P + genPhi P A C * opPow r (genV P A C)) *
          (invS P + genPhi P A C * opPow r (genV P A C)) =
        1 + virasoroModeEven (r + r) P A C := by
    calc (invS P + genPhi P A C * opPow r (genV P A C)) *
           (invS P + genPhi P A C * opPow r (genV P A C))
        = invS P * invS P + anticomm (invS P) (genPhi P A C * opPow r (genV P A C)) +
          (genPhi P A C * opPow r (genV P A C)) * (genPhi P A C * opPow r (genV P A C)) := by
          unfold anticomm; noncomm_ring
      _ = 1 + virasoroModeEven (r + r) P A C := by
          rw [hS_sq, hAntiS_Phi, hPhiMode_sq]; abel
  have hSq_S_J :
      (invS P + genJ P A C * opPow r (genV P A C)) *
          (invS P + genJ P A C * opPow r (genV P A C)) =
        1 - virasoroModeEven (r + r) P A C := by
    calc (invS P + genJ P A C * opPow r (genV P A C)) *
           (invS P + genJ P A C * opPow r (genV P A C))
        = invS P * invS P + anticomm (invS P) (genJ P A C * opPow r (genV P A C)) +
          (genJ P A C * opPow r (genV P A C)) * (genJ P A C * opPow r (genV P A C)) := by
          unfold anticomm; noncomm_ring
      _ = 1 - virasoroModeEven (r + r) P A C := by
          rw [hS_sq, hAntiS_J, hJMode_sq]; abel
  have hSq_P_Phi :
      (P + genPhi P A C * opPow r (genV P A C)) *
          (P + genPhi P A C * opPow r (genV P A C)) =
        P + genPhi P A C * opPow r (genV P A C) + virasoroModeEven (r + r) P A C := by
    calc (P + genPhi P A C * opPow r (genV P A C)) *
           (P + genPhi P A C * opPow r (genV P A C))
        = P * P + anticomm P (genPhi P A C * opPow r (genV P A C)) +
          (genPhi P A C * opPow r (genV P A C)) * (genPhi P A C * opPow r (genV P A C)) := by
          unfold anticomm; noncomm_ring
      _ = P + genPhi P A C * opPow r (genV P A C) + virasoroModeEven (r + r) P A C := by
          rw [hP, hAntiP_Phi, hPhiMode_sq]
  have hS_PhiMode_S :
      invS P * (genPhi P A C * opPow r (genV P A C)) * invS P =
        -(genPhi P A C * opPow r (genV P A C)) := by
    calc invS P * (genPhi P A C * opPow r (genV P A C)) * invS P
        = invS P * genPhi P A C * (opPow r (genV P A C) * invS P) := by noncomm_ring
      _ = (invS P * genPhi P A C * invS P) * opPow r (genV P A C) := by
          rw [hVS r]; noncomm_ring
      _ = -(genPhi P A C * opPow r (genV P A C)) := by
          rw [hS_Phi_conj, neg_mul]
  have hS_VMode_S :
      invS P * virasoroModeEven (r + r) P A C * invS P =
        virasoroModeEven (r + r) P A C := by
    change invS P * opPow (r + r + 1) (genV P A C) * invS P = opPow (r + r + 1) (genV P A C)
    rw [← hVS (r + r + 1), mul_assoc, hS_sq, mul_one]
  have hSym_S :
      (P + genPhi P A C * opPow r (genV P A C)) *
          (P + genPhi P A C * opPow r (genV P A C)) +
        invS P *
          ((P + genPhi P A C * opPow r (genV P A C)) *
            (P + genPhi P A C * opPow r (genV P A C))) *
          invS P =
        (2 : ℤ) • (P + virasoroModeEven (r + r) P A C) := by
    rw [hSq_P_Phi]
    have hConj :
        invS P * (P + genPhi P A C * opPow r (genV P A C) + virasoroModeEven (r + r) P A C) * invS P =
          invS P * P * invS P +
            invS P * (genPhi P A C * opPow r (genV P A C)) * invS P +
            invS P * virasoroModeEven (r + r) P A C * invS P := by noncomm_ring
    rw [hConj, hS_P_S, hS_PhiMode_S, hS_VMode_S, two_zsmul]
    abel
  have hComp_idem : (1 - P) * (1 - P) = 1 - P := by peirce_nf hP
  have hAntiComp_Phi :
      anticomm (1 - P) (genPhi P A C * opPow r (genV P A C)) =
        genPhi P A C * opPow r (genV P A C) := by
    have hSum : anticomm P (genPhi P A C * opPow r (genV P A C)) +
        anticomm (1 - P) (genPhi P A C * opPow r (genV P A C)) =
          (2 : ℤ) • (genPhi P A C * opPow r (genV P A C)) := by
      unfold anticomm
      rw [two_zsmul]
      noncomm_ring
    rw [hAntiP_Phi, two_zsmul] at hSum
    exact add_left_cancel hSum
  have hSq_Comp_Phi :
      ((1 - P) - genPhi P A C * opPow r (genV P A C)) *
          ((1 - P) - genPhi P A C * opPow r (genV P A C)) =
        (1 - P) - genPhi P A C * opPow r (genV P A C) + virasoroModeEven (r + r) P A C := by
    calc ((1 - P) - genPhi P A C * opPow r (genV P A C)) *
           ((1 - P) - genPhi P A C * opPow r (genV P A C))
        = (1 - P) * (1 - P) - anticomm (1 - P) (genPhi P A C * opPow r (genV P A C)) +
          (genPhi P A C * opPow r (genV P A C)) * (genPhi P A C * opPow r (genV P A C)) := by
          unfold anticomm; noncomm_ring
      _ = (1 - P) - genPhi P A C * opPow r (genV P A C) + virasoroModeEven (r + r) P A C := by
          rw [hComp_idem, hAntiComp_Phi, hPhiMode_sq]
  have hSym_Comp :
      (P + genPhi P A C * opPow r (genV P A C)) *
          (P + genPhi P A C * opPow r (genV P A C)) +
        ((1 - P) - genPhi P A C * opPow r (genV P A C)) *
          ((1 - P) - genPhi P A C * opPow r (genV P A C)) =
        1 + (2 : ℤ) • virasoroModeEven (r + r) P A C := by
    rw [hSq_P_Phi, hSq_Comp_Phi, two_zsmul]
    abel
  exact ⟨⟨hAntiS_Phi, hCommS_Phi, hSq_S_Phi, hSq_S_J⟩,
         ⟨hCommP_Phi, hAntiP_Phi, hSq_P_Phi, hSym_S, hSym_Comp⟩⟩

/-- **Archetype `A₉₀` (`M₂`, `archetype_A90_all_mode_chiral_charge_defect_brackets_and_virasoro_duality`):**
For every mode pair `(r, s) ∈ ℕ × ℕ`:
1. **Cross-Mode Anticommutator & Commutator Duality of Odd Modes (`Φ V^r` vs `J V^s`):**
   - `anticomm (genPhi P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) =`
     `(2 : ℤ) • virasoroModeEven (r + s) P A C`,
   - `comm (genPhi P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) = 0`,
   - `anticomm (genJ P A C * opPow r (genV P A C)) (genJ P A C * opPow s (genV P A C)) =`
     `-((2 : ℤ) • virasoroModeEven (r + s) P A C)`,
   - `comm (genJ P A C * opPow r (genV P A C)) (genJ P A C * opPow s (genV P A C)) = 0`,
   - `anticomm (genJ P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) = 0`,
   - `comm (genJ P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) =`
     `(2 : ℤ) • virasoroModeChiral (r + s) P A C`;
2. **Idempotent-Commutator Recovery of the Chiral Virasoro Algebra:**
   Since `comm P (genPhi P A C * opPow r (genV P A C)) = genJ P A C * opPow r (genV P A C)`,
   anticommuting the idempotent commutator defect with `genPhi P A C * opPow s (genV P A C)`
   vanishes (`= 0`), while commuting it recovers `(2 : ℤ) • virasoroModeChiral (r + s) P A C`:
   - `anticomm (comm P (genPhi P A C * opPow r (genV P A C))) (genPhi P A C * opPow s (genV P A C)) = 0`,
   - `comm (comm P (genPhi P A C * opPow r (genV P A C))) (genPhi P A C * opPow s (genV P A C)) =`
     `(2 : ℤ) • virasoroModeChiral (r + s) P A C`. -/
theorem archetype_A90_all_mode_chiral_charge_defect_brackets_and_virasoro_duality
    (A C : B) (r s : ℕ) :
    (anticomm (genPhi P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) =
       (2 : ℤ) • virasoroModeEven (r + s) P A C ∧
     comm (genPhi P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) = 0 ∧
     anticomm (genJ P A C * opPow r (genV P A C)) (genJ P A C * opPow s (genV P A C)) =
       -((2 : ℤ) • virasoroModeEven (r + s) P A C) ∧
     comm (genJ P A C * opPow r (genV P A C)) (genJ P A C * opPow s (genV P A C)) = 0 ∧
     anticomm (genJ P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) = 0 ∧
     comm (genJ P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) =
       (2 : ℤ) • virasoroModeChiral (r + s) P A C) ∧
    (anticomm (comm P (genPhi P A C * opPow r (genV P A C))) (genPhi P A C * opPow s (genV P A C)) = 0 ∧
     comm (comm P (genPhi P A C * opPow r (genV P A C))) (genPhi P A C * opPow s (genV P A C)) =
       (2 : ℤ) • virasoroModeChiral (r + s) P A C) := by
  have hVPhi : ∀ k : ℕ, opPow k (genV P A C) * genPhi P A C = genPhi P A C * opPow k (genV P A C) := by
    intro k
    rcases opPow_genV_comm_invS_and_cones hP A C k with ⟨_, hCp, hCm⟩
    unfold genPhi
    rw [mul_add, add_mul, hCp, hCm]
  have hVJ : ∀ k : ℕ, opPow k (genV P A C) * genJ P A C = genJ P A C * opPow k (genV P A C) := by
    intro k
    rcases opPow_genV_comm_invS_and_cones hP A C k with ⟨_, hCp, hCm⟩
    unfold genJ
    rw [mul_sub, sub_mul, hCp, hCm]
  have hPhi_sq : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
  have hJ_sq : genJ P A C * genJ P A C = -genV P A C := by peirce_nf hP
  have hJPhi_anti : genJ P A C * genPhi P A C + genPhi P A C * genJ P A C = 0 := by
    peirce_nf hP
  have hJPhi_comm : genJ P A C * genPhi P A C - genPhi P A C * genJ P A C = (2 : ℤ) • genSig P A C := by
    peirce_nf hP
  have hPhiPhi_prod : ∀ a b : ℕ,
      (genPhi P A C * opPow a (genV P A C)) * (genPhi P A C * opPow b (genV P A C)) =
        virasoroModeEven (a + b) P A C := by
    intro a b
    calc (genPhi P A C * opPow a (genV P A C)) * (genPhi P A C * opPow b (genV P A C))
        = genPhi P A C * (opPow a (genV P A C) * genPhi P A C) * opPow b (genV P A C) := by noncomm_ring
      _ = (genPhi P A C * genPhi P A C) * (opPow a (genV P A C) * opPow b (genV P A C)) := by
          rw [hVPhi a]; noncomm_ring
      _ = genV P A C * opPow (a + b) (genV P A C) := by
          rw [hPhi_sq, ← opPow_add a b (genV P A C)]
      _ = virasoroModeEven (a + b) P A C := mul_opPow_comm (a + b) (genV P A C)
  have hJJ_prod : ∀ a b : ℕ,
      (genJ P A C * opPow a (genV P A C)) * (genJ P A C * opPow b (genV P A C)) =
        -virasoroModeEven (a + b) P A C := by
    intro a b
    calc (genJ P A C * opPow a (genV P A C)) * (genJ P A C * opPow b (genV P A C))
        = genJ P A C * (opPow a (genV P A C) * genJ P A C) * opPow b (genV P A C) := by noncomm_ring
      _ = (genJ P A C * genJ P A C) * (opPow a (genV P A C) * opPow b (genV P A C)) := by
          rw [hVJ a]; noncomm_ring
      _ = -(genV P A C * opPow (a + b) (genV P A C)) := by
          rw [hJ_sq, ← opPow_add a b (genV P A C), neg_mul]
      _ = -virasoroModeEven (a + b) P A C :=
          congrArg Neg.neg (mul_opPow_comm (a + b) (genV P A C))
  have hJPhi_prod :
      (genJ P A C * opPow r (genV P A C)) * (genPhi P A C * opPow s (genV P A C)) =
        (genJ P A C * genPhi P A C) * opPow (r + s) (genV P A C) := by
    calc (genJ P A C * opPow r (genV P A C)) * (genPhi P A C * opPow s (genV P A C))
        = genJ P A C * (opPow r (genV P A C) * genPhi P A C) * opPow s (genV P A C) := by noncomm_ring
      _ = (genJ P A C * genPhi P A C) * (opPow r (genV P A C) * opPow s (genV P A C)) := by
          rw [hVPhi r]; noncomm_ring
      _ = (genJ P A C * genPhi P A C) * opPow (r + s) (genV P A C) := by
          rw [← opPow_add r s (genV P A C)]
  have hPhiJ_prod :
      (genPhi P A C * opPow s (genV P A C)) * (genJ P A C * opPow r (genV P A C)) =
        (genPhi P A C * genJ P A C) * opPow (r + s) (genV P A C) := by
    calc (genPhi P A C * opPow s (genV P A C)) * (genJ P A C * opPow r (genV P A C))
        = genPhi P A C * (opPow s (genV P A C) * genJ P A C) * opPow r (genV P A C) := by noncomm_ring
      _ = (genPhi P A C * genJ P A C) * (opPow s (genV P A C) * opPow r (genV P A C)) := by
          rw [hVJ s]; noncomm_ring
      _ = (genPhi P A C * genJ P A C) * opPow (r + s) (genV P A C) := by
          rw [← opPow_add s r (genV P A C), Nat.add_comm s r]
  have hChiralEq : virasoroModeChiral (r + s) P A C = genSig P A C * opPow (r + s) (genV P A C) := by
    unfold virasoroModeChiral
    rw [show sugawaraTensor P A C = genV P A C by rfl,
      show chiralSchwinger P A C = genSig P A C by rfl,
      (opPow_genV_comm_genSig_explicit P A C (r + s) hP).symm]
  have h1 : anticomm (genPhi P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) =
      (2 : ℤ) • virasoroModeEven (r + s) P A C := by
    unfold anticomm
    rw [hPhiPhi_prod r s, hPhiPhi_prod s r, Nat.add_comm s r, two_zsmul]
  have h2 : comm (genPhi P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) = 0 := by
    unfold comm
    rw [hPhiPhi_prod r s, hPhiPhi_prod s r, Nat.add_comm s r, sub_self]
  have h3 : anticomm (genJ P A C * opPow r (genV P A C)) (genJ P A C * opPow s (genV P A C)) =
      -((2 : ℤ) • virasoroModeEven (r + s) P A C) := by
    unfold anticomm
    rw [hJJ_prod r s, hJJ_prod s r, Nat.add_comm s r, two_zsmul]
    abel
  have h4 : comm (genJ P A C * opPow r (genV P A C)) (genJ P A C * opPow s (genV P A C)) = 0 := by
    unfold comm
    rw [hJJ_prod r s, hJJ_prod s r, Nat.add_comm s r, sub_self]
  have h5 : anticomm (genJ P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) = 0 := by
    unfold anticomm
    rw [hJPhi_prod, hPhiJ_prod]
    calc (genJ P A C * genPhi P A C) * opPow (r + s) (genV P A C) +
           (genPhi P A C * genJ P A C) * opPow (r + s) (genV P A C)
        = (genJ P A C * genPhi P A C + genPhi P A C * genJ P A C) * opPow (r + s) (genV P A C) := by
          noncomm_ring
      _ = 0 := by rw [hJPhi_anti, zero_mul]
  have h6 : comm (genJ P A C * opPow r (genV P A C)) (genPhi P A C * opPow s (genV P A C)) =
      (2 : ℤ) • virasoroModeChiral (r + s) P A C := by
    unfold comm
    rw [hJPhi_prod, hPhiJ_prod]
    calc (genJ P A C * genPhi P A C) * opPow (r + s) (genV P A C) -
           (genPhi P A C * genJ P A C) * opPow (r + s) (genV P A C)
        = (genJ P A C * genPhi P A C - genPhi P A C * genJ P A C) * opPow (r + s) (genV P A C) := by
          noncomm_ring
      _ = ((2 : ℤ) • genSig P A C) * opPow (r + s) (genV P A C) := by rw [hJPhi_comm]
      _ = (2 : ℤ) • virasoroModeChiral (r + s) P A C := by
          rw [hChiralEq, two_zsmul, two_zsmul]; noncomm_ring
  have hCommP_Phi :=
    (archetype_A89_peirce_bdg_square_commutator_anomaly_and_grading_symmetrization hP A C r).2.1
  refine ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨?_, ?_⟩⟩
  · rw [hCommP_Phi, h5]
  · rw [hCommP_Phi, h6]

/-- **Archetype `A₉₁` (`M₃`, `archetype_A91_source_sink_car_ccr_mode_duality_and_hopf_norm_splitting`):**
For every mode pair `(r, s) ∈ ℕ × ℕ` on the Peirce source and sink modes
`J_r^+ = heisenbergSourceMode r P A C = V^r N_+` and `J_s^- = heisenbergSinkMode s P A C = N_- V^s`:
1. **Same-Cone Nilpotency (`(J_r^+)(J_s^+) = 0`, `(J_r^-)(J_s^-) = 0`):**
   - `heisenbergSourceMode r P A C * heisenbergSourceMode s P A C = 0`,
   - `heisenbergSinkMode r P A C * heisenbergSinkMode s P A C = 0`;
2. **CAR Anticommutator vs. CCR Commutator Mode Duality:**
   The anticommutator `{J_r^+, J_s^-}` is the even Sugawara–Virasoro mode `virasoroModeEven (r + s) P A C`,
   whereas the commutator `[J_r^+, J_s^-]` is the chiral Schwinger–Virasoro mode `virasoroModeChiral (r + s) P A C`:
   - `anticomm (heisenbergSourceMode r P A C) (heisenbergSinkMode s P A C) = virasoroModeEven (r + s) P A C`,
   - `comm (heisenbergSourceMode r P A C) (heisenbergSinkMode s P A C) = virasoroModeChiral (r + s) P A C`;
3. **Cross-Mode Sum & Difference Squares (`(J_r^+ ± J_s^-)^2`):**
   - `(heisenbergSourceMode r P A C + heisenbergSinkMode s P A C) *`
     `  (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C) = virasoroModeEven (r + s) P A C`,
   - `(heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) *`
     `  (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) = -virasoroModeEven (r + s) P A C`,
   - `comm (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C)`
     `  (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) =`
     `-((2 : ℤ) • virasoroModeChiral (r + s) P A C)`. -/
theorem archetype_A91_source_sink_car_ccr_mode_duality_and_hopf_norm_splitting
    (A C : B) (r s : ℕ) :
    (heisenbergSourceMode r P A C * heisenbergSourceMode s P A C = 0 ∧
     heisenbergSinkMode r P A C * heisenbergSinkMode s P A C = 0) ∧
    (anticomm (heisenbergSourceMode r P A C) (heisenbergSinkMode s P A C) =
       virasoroModeEven (r + s) P A C ∧
     comm (heisenbergSourceMode r P A C) (heisenbergSinkMode s P A C) =
       virasoroModeChiral (r + s) P A C) ∧
    ((heisenbergSourceMode r P A C + heisenbergSinkMode s P A C) *
         (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C) =
       virasoroModeEven (r + s) P A C ∧
     (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) *
         (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) =
       -virasoroModeEven (r + s) P A C ∧
     comm (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C)
         (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) =
       -((2 : ℤ) • virasoroModeChiral (r + s) P A C)) := by
  have hVNp : ∀ k : ℕ, opPow k (genV P A C) * conePlus P A = conePlus P A * opPow k (genV P A C) :=
    fun k => (opPow_genV_comm_invS_and_cones hP A C k).2.1.symm
  have hVNm : ∀ k : ℕ, opPow k (genV P A C) * coneMinus P C = coneMinus P C * opPow k (genV P A C) :=
    fun k => (opPow_genV_comm_invS_and_cones hP A C k).2.2.symm
  have hNp_sq : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have hNm_sq : coneMinus P C * coneMinus P C = 0 := by peirce_nf hP
  have hSrc_sq : heisenbergSourceMode r P A C * heisenbergSourceMode s P A C = 0 := by
    change (opPow r (genV P A C) * conePlus P A) * (opPow s (genV P A C) * conePlus P A) = 0
    calc (opPow r (genV P A C) * conePlus P A) * (opPow s (genV P A C) * conePlus P A)
        = opPow r (genV P A C) * (conePlus P A * opPow s (genV P A C)) * conePlus P A := by noncomm_ring
      _ = opPow r (genV P A C) * opPow s (genV P A C) * (conePlus P A * conePlus P A) := by
          rw [← hVNp s]; noncomm_ring
      _ = 0 := by rw [hNp_sq, mul_zero]
  have hSnk_sq : heisenbergSinkMode r P A C * heisenbergSinkMode s P A C = 0 := by
    change (coneMinus P C * opPow r (genV P A C)) * (coneMinus P C * opPow s (genV P A C)) = 0
    calc (coneMinus P C * opPow r (genV P A C)) * (coneMinus P C * opPow s (genV P A C))
        = coneMinus P C * (opPow r (genV P A C) * coneMinus P C) * opPow s (genV P A C) := by noncomm_ring
      _ = (coneMinus P C * coneMinus P C) * (opPow r (genV P A C) * opPow s (genV P A C)) := by
          rw [hVNm r]; noncomm_ring
      _ = 0 := by rw [hNm_sq, zero_mul]
  have hProd_PM :
      heisenbergSourceMode r P A C * heisenbergSinkMode s P A C =
        opPow (r + s) (genV P A C) * (conePlus P A * coneMinus P C) := by
    change (opPow r (genV P A C) * conePlus P A) * (coneMinus P C * opPow s (genV P A C)) =
      opPow (r + s) (genV P A C) * (conePlus P A * coneMinus P C)
    calc (opPow r (genV P A C) * conePlus P A) * (coneMinus P C * opPow s (genV P A C))
        = opPow r (genV P A C) * conePlus P A * (opPow s (genV P A C) * coneMinus P C) := by
          rw [hVNm s]
      _ = opPow r (genV P A C) * (conePlus P A * opPow s (genV P A C)) * coneMinus P C := by noncomm_ring
      _ = (opPow r (genV P A C) * opPow s (genV P A C)) * (conePlus P A * coneMinus P C) := by
          rw [← hVNp s]; noncomm_ring
      _ = opPow (r + s) (genV P A C) * (conePlus P A * coneMinus P C) := by
          rw [← opPow_add r s (genV P A C)]
  have hProd_MP :
      heisenbergSinkMode s P A C * heisenbergSourceMode r P A C =
        opPow (r + s) (genV P A C) * (coneMinus P C * conePlus P A) := by
    change (coneMinus P C * opPow s (genV P A C)) * (opPow r (genV P A C) * conePlus P A) =
      opPow (r + s) (genV P A C) * (coneMinus P C * conePlus P A)
    calc (coneMinus P C * opPow s (genV P A C)) * (opPow r (genV P A C) * conePlus P A)
        = (coneMinus P C * opPow (s + r) (genV P A C)) * conePlus P A := by
          rw [mul_assoc (coneMinus P C), ← mul_assoc (opPow s (genV P A C)),
              ← opPow_add s r (genV P A C), mul_assoc]
      _ = (opPow (r + s) (genV P A C) * coneMinus P C) * conePlus P A := by
          rw [Nat.add_comm s r, hVNm (r + s)]
      _ = opPow (r + s) (genV P A C) * (coneMinus P C * conePlus P A) := by noncomm_ring
  have hAnti :
      anticomm (heisenbergSourceMode r P A C) (heisenbergSinkMode s P A C) =
        virasoroModeEven (r + s) P A C := by
    unfold anticomm
    rw [hProd_PM, hProd_MP]
    calc opPow (r + s) (genV P A C) * (conePlus P A * coneMinus P C) +
           opPow (r + s) (genV P A C) * (coneMinus P C * conePlus P A)
        = opPow (r + s) (genV P A C) * genV P A C := by
          unfold genV anticomm; noncomm_ring
      _ = virasoroModeEven (r + s) P A C := rfl
  have hComm :
      comm (heisenbergSourceMode r P A C) (heisenbergSinkMode s P A C) =
        virasoroModeChiral (r + s) P A C := by
    unfold comm
    rw [hProd_PM, hProd_MP]
    calc opPow (r + s) (genV P A C) * (conePlus P A * coneMinus P C) -
           opPow (r + s) (genV P A C) * (coneMinus P C * conePlus P A)
        = opPow (r + s) (genV P A C) * genSig P A C := by
          unfold genSig comm; noncomm_ring
      _ = virasoroModeChiral (r + s) P A C := rfl
  have hSrc_self : heisenbergSourceMode r P A C * heisenbergSourceMode r P A C = 0 := by
    change (opPow r (genV P A C) * conePlus P A) * (opPow r (genV P A C) * conePlus P A) = 0
    calc (opPow r (genV P A C) * conePlus P A) * (opPow r (genV P A C) * conePlus P A)
        = opPow r (genV P A C) * (conePlus P A * opPow r (genV P A C)) * conePlus P A := by noncomm_ring
      _ = opPow r (genV P A C) * opPow r (genV P A C) * (conePlus P A * conePlus P A) := by
          rw [← hVNp r]; noncomm_ring
      _ = 0 := by rw [hNp_sq, mul_zero]
  have hSnk_self : heisenbergSinkMode s P A C * heisenbergSinkMode s P A C = 0 := by
    change (coneMinus P C * opPow s (genV P A C)) * (coneMinus P C * opPow s (genV P A C)) = 0
    calc (coneMinus P C * opPow s (genV P A C)) * (coneMinus P C * opPow s (genV P A C))
        = coneMinus P C * (opPow s (genV P A C) * coneMinus P C) * opPow s (genV P A C) := by noncomm_ring
      _ = (coneMinus P C * coneMinus P C) * (opPow s (genV P A C) * opPow s (genV P A C)) := by
          rw [hVNm s]; noncomm_ring
      _ = 0 := by rw [hNm_sq, zero_mul]
  have hSum_sq :
      (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C) *
          (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C) =
        virasoroModeEven (r + s) P A C := by
    calc (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C) *
           (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C)
        = heisenbergSourceMode r P A C * heisenbergSourceMode r P A C +
          anticomm (heisenbergSourceMode r P A C) (heisenbergSinkMode s P A C) +
          heisenbergSinkMode s P A C * heisenbergSinkMode s P A C := by
          unfold anticomm; noncomm_ring
      _ = virasoroModeEven (r + s) P A C := by
          rw [hSrc_self, hSnk_self, hAnti]; abel
  have hDiff_sq :
      (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) *
          (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) =
        -virasoroModeEven (r + s) P A C := by
    calc (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) *
           (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C)
        = heisenbergSourceMode r P A C * heisenbergSourceMode r P A C -
          anticomm (heisenbergSourceMode r P A C) (heisenbergSinkMode s P A C) +
          heisenbergSinkMode s P A C * heisenbergSinkMode s P A C := by
          unfold anticomm; noncomm_ring
      _ = -virasoroModeEven (r + s) P A C := by
          rw [hSrc_self, hSnk_self, hAnti]; abel
  have hSumDiff_comm :
      comm (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C)
          (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C) =
        -((2 : ℤ) • virasoroModeChiral (r + s) P A C) := by
    calc comm (heisenbergSourceMode r P A C + heisenbergSinkMode s P A C)
           (heisenbergSourceMode r P A C - heisenbergSinkMode s P A C)
        = -((2 : ℤ) • comm (heisenbergSourceMode r P A C) (heisenbergSinkMode s P A C)) := by
          unfold comm; rw [two_zsmul]; noncomm_ring
      _ = -((2 : ℤ) • virasoroModeChiral (r + s) P A C) := by rw [hComm]
  exact ⟨⟨hSrc_sq, hSnk_sq⟩, ⟨hAnti, hComm⟩, ⟨hSum_sq, hDiff_sq, hSumDiff_comm⟩⟩

/-- **Archetype `A₉₂` (`M₄`, `archetype_A92_orthogonal_peirce_diagonal_sector_isolation_and_additivity`):**
For any non-commutative ring `B`, idempotent `P² = P`, arbitrary elements `X, Y, A, C : B`,
and mode indices `r, s : ℕ`:
1. **Orthogonal Diagonal Peirce Corners (`peirce11 P X` vs `peirce00 P Y`):**
   - `peirce11 P X * peirce00 P Y = 0` and `peirce00 P Y * peirce11 P X = 0`,
   - `comm (peirce11 P X) (peirce00 P Y) = 0` and `anticomm (peirce11 P X) (peirce00 P Y) = 0`,
   - `(peirce11 P X + peirce00 P Y) * (peirce11 P X + peirce00 P Y) =`
     `peirce11 P X * peirce11 P X + peirce00 P Y * peirce00 P Y`,
   - `evenGrade P X * evenGrade P Y =`
     `peirce11 P X * peirce11 P Y + peirce00 P X * peirce00 P Y`;
2. **Disjoint Sector Decomposition of Even & Chiral Virasoro Modes:**
   Every even Virasoro mode `virasoroModeEven r P A C` and chiral Virasoro mode
   `virasoroModeChiral r P A C` splits into orthogonal `(1,1)` and `(0,0)` Peirce sectors whose
   cross-sector products vanish and whose product decomposes additively:
   - `peirce11 P (virasoroModeEven r P A C) * peirce00 P (virasoroModeEven s P A C) = 0`,
   - `peirce00 P (virasoroModeEven s P A C) * peirce11 P (virasoroModeEven r P A C) = 0`,
   - `peirce11 P (virasoroModeEven r P A C) + peirce00 P (virasoroModeEven r P A C) =`
     `virasoroModeEven r P A C`,
   - `peirce11 P (virasoroModeChiral r P A C) = P * virasoroModeEven r P A C`,
   - `peirce00 P (virasoroModeChiral r P A C) = -((1 - P) * virasoroModeEven r P A C)`,
   - `peirce11 P (virasoroModeChiral r P A C) + peirce00 P (virasoroModeChiral r P A C) =`
     `virasoroModeChiral r P A C`. -/
theorem archetype_A92_orthogonal_peirce_diagonal_sector_isolation_and_additivity
    (X Y A C : B) (r s : ℕ) :
    (peirce11 P X * peirce00 P Y = 0 ∧
     peirce00 P Y * peirce11 P X = 0 ∧
     comm (peirce11 P X) (peirce00 P Y) = 0 ∧
     anticomm (peirce11 P X) (peirce00 P Y) = 0 ∧
     (peirce11 P X + peirce00 P Y) * (peirce11 P X + peirce00 P Y) =
       peirce11 P X * peirce11 P X + peirce00 P Y * peirce00 P Y ∧
     evenGrade P X * evenGrade P Y =
       peirce11 P X * peirce11 P Y + peirce00 P X * peirce00 P Y) ∧
    (peirce11 P (virasoroModeEven r P A C) * peirce00 P (virasoroModeEven s P A C) = 0 ∧
     peirce00 P (virasoroModeEven s P A C) * peirce11 P (virasoroModeEven r P A C) = 0 ∧
     peirce11 P (virasoroModeEven r P A C) + peirce00 P (virasoroModeEven r P A C) =
       virasoroModeEven r P A C ∧
     peirce11 P (virasoroModeChiral r P A C) = P * virasoroModeEven r P A C ∧
     peirce00 P (virasoroModeChiral r P A C) = -((1 - P) * virasoroModeEven r P A C) ∧
     peirce11 P (virasoroModeChiral r P A C) + peirce00 P (virasoroModeChiral r P A C) =
       virasoroModeChiral r P A C) := by
  have h11_00 : ∀ U V : B, peirce11 P U * peirce00 P V = 0 := by
    intro U V
    unfold peirce11 peirce00
    have hPComp : P * (1 - P) = 0 := by peirce_nf hP
    calc (P * U * P) * ((1 - P) * V * (1 - P))
        = (P * U) * (P * (1 - P)) * (V * (1 - P)) := by noncomm_ring
      _ = 0 := by rw [hPComp]; simp
  have h00_11 : ∀ U V : B, peirce00 P V * peirce11 P U = 0 := by
    intro U V
    unfold peirce11 peirce00
    have hCompP : (1 - P) * P = 0 := by peirce_nf hP
    calc ((1 - P) * V * (1 - P)) * (P * U * P)
        = ((1 - P) * V) * ((1 - P) * P) * (U * P) := by noncomm_ring
      _ = 0 := by rw [hCompP]; simp
  have hComm : comm (peirce11 P X) (peirce00 P Y) = 0 := by
    unfold comm
    rw [h11_00 X Y, h00_11 X Y, sub_self]
  have hAnti : anticomm (peirce11 P X) (peirce00 P Y) = 0 := by
    unfold anticomm
    rw [h11_00 X Y, h00_11 X Y, add_zero]
  have hSq :
      (peirce11 P X + peirce00 P Y) * (peirce11 P X + peirce00 P Y) =
        peirce11 P X * peirce11 P X + peirce00 P Y * peirce00 P Y := by
    calc (peirce11 P X + peirce00 P Y) * (peirce11 P X + peirce00 P Y)
        = peirce11 P X * peirce11 P X +
          (peirce11 P X * peirce00 P Y + peirce00 P Y * peirce11 P X) +
          peirce00 P Y * peirce00 P Y := by noncomm_ring
      _ = peirce11 P X * peirce11 P X + peirce00 P Y * peirce00 P Y := by
          rw [h11_00 X Y, h00_11 X Y]; abel
  have hEvenMul :
      evenGrade P X * evenGrade P Y =
        peirce11 P X * peirce11 P Y + peirce00 P X * peirce00 P Y := by
    change (peirce11 P X + peirce00 P X) * (peirce11 P Y + peirce00 P Y) =
      peirce11 P X * peirce11 P Y + peirce00 P X * peirce00 P Y
    calc (peirce11 P X + peirce00 P X) * (peirce11 P Y + peirce00 P Y)
        = peirce11 P X * peirce11 P Y +
          (peirce11 P X * peirce00 P Y + peirce00 P X * peirce11 P Y) +
          peirce00 P X * peirce00 P Y := by noncomm_ring
      _ = peirce11 P X * peirce11 P Y + peirce00 P X * peirce00 P Y := by
          rw [h11_00 X Y, h00_11 Y X]; abel
  have hVP : ∀ k : ℕ, P * opPow k (genV P A C) = opPow k (genV P A C) * P :=
    fun k => (opPow_genV_comm_idem hP A C k).1
  have hVComp : ∀ k : ℕ, (1 - P) * opPow k (genV P A C) = opPow k (genV P A C) * (1 - P) := by
    intro k
    rw [sub_mul, mul_sub, one_mul, mul_one, hVP k]
  have hComp_idem : (1 - P) * (1 - P) = 1 - P := by peirce_nf hP
  have hP11_Even : peirce11 P (virasoroModeEven r P A C) = P * virasoroModeEven r P A C := by
    unfold peirce11
    change P * opPow (r + 1) (genV P A C) * P = P * opPow (r + 1) (genV P A C)
    rw [mul_assoc, ← hVP (r + 1), ← mul_assoc, hP]
  have hP00_Even : peirce00 P (virasoroModeEven r P A C) = (1 - P) * virasoroModeEven r P A C := by
    unfold peirce00
    change (1 - P) * opPow (r + 1) (genV P A C) * (1 - P) = (1 - P) * opPow (r + 1) (genV P A C)
    rw [mul_assoc, ← hVComp (r + 1), ← mul_assoc, hComp_idem]
  have hSum_Even :
      peirce11 P (virasoroModeEven r P A C) + peirce00 P (virasoroModeEven r P A C) =
        virasoroModeEven r P A C := by
    rw [hP11_Even, hP00_Even]
    noncomm_ring
  have hPSig : P * genSig P A C = P * genV P A C := by peirce_nf hP
  have hCompSig : (1 - P) * genSig P A C = -((1 - P) * genV P A C) := by peirce_nf hP
  have hSigP : genSig P A C * P = genSig P A C * P := rfl
  have hChiral_P :
      P * virasoroModeChiral r P A C = P * virasoroModeEven r P A C := by
    change P * (opPow r (genV P A C) * genSig P A C) =
      P * (opPow r (genV P A C) * genV P A C)
    calc P * (opPow r (genV P A C) * genSig P A C)
        = (P * opPow r (genV P A C)) * genSig P A C := by noncomm_ring
      _ = opPow r (genV P A C) * (P * genSig P A C) := by rw [hVP r, mul_assoc]
      _ = opPow r (genV P A C) * (P * genV P A C) := by rw [hPSig]
      _ = (P * opPow r (genV P A C)) * genV P A C := by rw [← mul_assoc, ← hVP r]
      _ = P * (opPow r (genV P A C) * genV P A C) := by noncomm_ring
  have hChiral_Comp :
      (1 - P) * virasoroModeChiral r P A C = -((1 - P) * virasoroModeEven r P A C) := by
    change (1 - P) * (opPow r (genV P A C) * genSig P A C) =
      -((1 - P) * (opPow r (genV P A C) * genV P A C))
    calc (1 - P) * (opPow r (genV P A C) * genSig P A C)
        = ((1 - P) * opPow r (genV P A C)) * genSig P A C := by noncomm_ring
      _ = opPow r (genV P A C) * ((1 - P) * genSig P A C) := by rw [hVComp r, mul_assoc]
      _ = opPow r (genV P A C) * (-((1 - P) * genV P A C)) := by rw [hCompSig]
      _ = -(((1 - P) * opPow r (genV P A C)) * genV P A C) := by
          rw [mul_neg, ← mul_assoc, ← hVComp r]
      _ = -((1 - P) * (opPow r (genV P A C) * genV P A C)) := by noncomm_ring
  have hP11_Chiral :
      peirce11 P (virasoroModeChiral r P A C) = P * virasoroModeEven r P A C := by
    unfold peirce11
    rw [hChiral_P]
    exact hP11_Even
  have hP00_Chiral :
      peirce00 P (virasoroModeChiral r P A C) = -((1 - P) * virasoroModeEven r P A C) := by
    unfold peirce00
    rw [hChiral_Comp, neg_mul]
    exact congrArg Neg.neg hP00_Even
  have hSum_Chiral :
      peirce11 P (virasoroModeChiral r P A C) + peirce00 P (virasoroModeChiral r P A C) =
        virasoroModeChiral r P A C := by
    rw [hP11_Chiral, hP00_Chiral, ← hChiral_P, ← hChiral_Comp]
    noncomm_ring
  exact ⟨⟨h11_00 X Y, h00_11 X Y, hComm, hAnti, hSq, hEvenMul⟩,
         ⟨h11_00 (virasoroModeEven r P A C) (virasoroModeEven s P A C),
          h00_11 (virasoroModeEven r P A C) (virasoroModeEven s P A C),
          hSum_Even, hP11_Chiral, hP00_Chiral, hSum_Chiral⟩⟩

/-- **Archetype `A₉₃` (`M₅`, `archetype_A93_all_mode_golay_leech_mog_decoding_of_bdg_symmetrized_squares`):**
For every mode index `r : ℕ`, let
`H_S(r) = invS P + genPhi P A C * opPow r (genV P A C)` and
`H_P(r) = P + genPhi P A C * opPow r (genV P A C)`:
1. **Golay–Leech–MOG & Double-Derivation Decoding of the Unperturbed Square `H_S(r)²`:**
   - `golay12Core P A C (H_S(r) * H_S(r)) = (12 : ℤ) • genV P A C + (12 : ℤ) • virasoroModeEven (r + r + 1) P A C`,
   - `golay24G0 P A C (H_S(r) * H_S(r)) = (24 : ℤ) • genV P A C + (24 : ℤ) • virasoroModeEven (r + r + 1) P A C`,
   - `mog24V P A C (H_S(r) * H_S(r)) = (24 : ℤ) • (genV P A C * genV P A C) + (24 : ℤ) • virasoroModeEven (r + r + 2) P A C`,
   - `derivSqPhi P A C (H_S(r) * H_S(r)) = 0`;
2. **Golay–Leech & Double-Derivation Decoding of the Complementary-Symmetrized Square:**
   - `golay12Core P A C (H_P(r) * H_P(r) + ((1 - P) - genPhi P A C * opPow r (genV P A C)) * ((1 - P) - genPhi P A C * opPow r (genV P A C))) =`
     `(12 : ℤ) • genV P A C + (24 : ℤ) • virasoroModeEven (r + r + 1) P A C`,
   - `golay24G0 P A C (H_P(r) * H_P(r) + ((1 - P) - genPhi P A C * opPow r (genV P A C)) * ((1 - P) - genPhi P A C * opPow r (genV P A C))) =`
     `(24 : ℤ) • genV P A C + (48 : ℤ) • virasoroModeEven (r + r + 1) P A C`,
   - `derivSqPhi P A C (H_P(r) * H_P(r) + ((1 - P) - genPhi P A C * opPow r (genV P A C)) * ((1 - P) - genPhi P A C * opPow r (genV P A C))) = 0`,
   - `derivSqPhi P A C (H_P(r) * H_P(r)) = -((2 : ℤ) • genSig P A C)`. -/
theorem archetype_A93_all_mode_golay_leech_mog_decoding_of_bdg_symmetrized_squares
    (A C : B) (r : ℕ) :
    let H_S := invS P + genPhi P A C * opPow r (genV P A C)
    let H_P := P + genPhi P A C * opPow r (genV P A C)
    let H_Comp := (1 - P) - genPhi P A C * opPow r (genV P A C)
    (golay12Core P A C (H_S * H_S) =
       (12 : ℤ) • genV P A C + (12 : ℤ) • virasoroModeEven (r + r + 1) P A C ∧
     golay24G0 P A C (H_S * H_S) =
       (24 : ℤ) • genV P A C + (24 : ℤ) • virasoroModeEven (r + r + 1) P A C ∧
     mog24V P A C (H_S * H_S) =
       (24 : ℤ) • (genV P A C * genV P A C) +
         (24 : ℤ) • virasoroModeEven (r + r + 2) P A C ∧
     derivSqPhi P A C (H_S * H_S) = 0) ∧
    (golay12Core P A C (H_P * H_P + H_Comp * H_Comp) =
       (12 : ℤ) • genV P A C + (24 : ℤ) • virasoroModeEven (r + r + 1) P A C ∧
     golay24G0 P A C (H_P * H_P + H_Comp * H_Comp) =
       (24 : ℤ) • genV P A C + (48 : ℤ) • virasoroModeEven (r + r + 1) P A C ∧
     derivSqPhi P A C (H_P * H_P + H_Comp * H_Comp) = 0 ∧
     derivSqPhi P A C (H_P * H_P) = -((2 : ℤ) • genSig P A C)) := by
  intro H_S H_P H_Comp
  rcases archetype_A89_peirce_bdg_square_commutator_anomaly_and_grading_symmetrization hP A C r with
    ⟨⟨_, _, hSq_S, _⟩, ⟨_, _, hSq_P, _, hSym_Comp⟩⟩
  have hStageD40 := stage_D40_all_mode_virasoro_golay_leech_mog_ladder hP A C (r + r)
  have hG12_V : golay12Core P A C (virasoroModeEven (r + r) P A C) =
      (12 : ℤ) • virasoroModeEven (r + r + 1) P A C := hStageD40.1
  have hG24_V : golay24G0 P A C (virasoroModeEven (r + r) P A C) =
      (24 : ℤ) • virasoroModeEven (r + r + 1) P A C := hStageD40.2.2.2.1
  have hM24_V : mog24V P A C (virasoroModeEven (r + r) P A C) =
      (24 : ℤ) • virasoroModeEven (r + r + 2) P A C := hStageD40.2.2.2.2.2.2.2.2.1
  have hLin : ∀ (K : B → B), (∀ X Y : B, K (X + Y) = K X + K Y) →
      ∀ X Y : B, superChargeP K P (X + Y) = superChargeP K P X + superChargeP K P Y := by
    intro K hK X Y
    have hComm : ∀ U V : B, comm P (U + V) = comm P U + comm P V := by
      intro U V
      unfold comm
      noncomm_ring
    change comm P (K (X + Y)) - K (comm P (X + Y)) =
      (comm P (K X) - K (comm P X)) + (comm P (K Y) - K (comm P Y))
    rw [hK X Y, hComm (K X) (K Y), hComm X Y, hK (comm P X) (comm P Y)]
    abel
  have hTot_add : ∀ X Y : B, kantorTotal P A C (X + Y) =
      kantorTotal P A C X + kantorTotal P A C Y := by
    intro X Y
    unfold kantorTotal kantorGp2 kantorGp1 kantorG0 kantorGm1 kantorGm2 kantorTriple comm
    noncomm_ring
  have hD1_add : ∀ X Y : B, kantorDelta1 P A C (X + Y) =
      kantorDelta1 P A C X + kantorDelta1 P A C Y :=
    hLin _ hTot_add
  have hD2_add : ∀ X Y : B, kantorDelta2 P A C (X + Y) =
      kantorDelta2 P A C X + kantorDelta2 P A C Y :=
    hLin _ hD1_add
  have hD3_add : ∀ X Y : B, kantorDelta3 P A C (X + Y) =
      kantorDelta3 P A C X + kantorDelta3 P A C Y :=
    hLin _ hD2_add
  have hD4_add : ∀ X Y : B, kantorDelta4 P A C (X + Y) =
      kantorDelta4 P A C X + kantorDelta4 P A C Y :=
    hLin _ hD3_add
  have hG12_add : ∀ X Y : B, golay12Core P A C (X + Y) =
      golay12Core P A C X + golay12Core P A C Y := by
    intro X Y
    unfold golay12Core
    rw [hD4_add, hD2_add, hTot_add]
    simp only [smul_add]
    abel
  have hG24_add : ∀ X Y : B, golay24G0 P A C (X + Y) =
      golay24G0 P A C X + golay24G0 P A C Y := by
    intro X Y
    have hEq : ∀ Z : B, (2 : ℤ) • golay12Core P A C Z = golay24G0 P A C Z := by
      intro Z; unfold golay12Core golay24G0; abel
    calc golay24G0 P A C (X + Y)
        = (2 : ℤ) • golay12Core P A C (X + Y) := (hEq (X + Y)).symm
      _ = (2 : ℤ) • (golay12Core P A C X + golay12Core P A C Y) := by rw [hG12_add]
      _ = (2 : ℤ) • golay12Core P A C X + (2 : ℤ) • golay12Core P A C Y := by
          rw [two_zsmul]; abel
      _ = golay24G0 P A C X + golay24G0 P A C Y := by rw [hEq X, hEq Y]
  have hM24V_add : ∀ X Y : B, mog24V P A C (X + Y) =
      mog24V P A C X + mog24V P A C Y := by
    intro X Y
    unfold mog24V hProjV derivSqPhi derivSqJ derivSqSig comm
    noncomm_ring
  have hDPhi_add : ∀ X Y : B, derivSqPhi P A C (X + Y) =
      derivSqPhi P A C X + derivSqPhi P A C Y := by
    intro X Y
    unfold derivSqPhi comm
    noncomm_ring
  have hG12_one : golay12Core P A C 1 = (12 : ℤ) • genV P A C := by
    rw [(archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hP A C 1).2.1]
    unfold sandwichCross
    peirce_nf hP
  have hG24_one : golay24G0 P A C 1 = (24 : ℤ) • genV P A C := by
    have hEq : (2 : ℤ) • golay12Core P A C 1 = golay24G0 P A C 1 := by
      unfold golay12Core golay24G0; abel
    rw [← hEq, hG12_one, smul_smul]
    rfl
  have hDPhi_one : derivSqPhi P A C 1 = 0 := by
    unfold derivSqPhi comm; noncomm_ring
  have hDJ_one : derivSqJ P A C 1 = 0 := by
    unfold derivSqJ comm; noncomm_ring
  have hDSig_one : derivSqSig P A C 1 = 0 := by
    unfold derivSqSig comm; noncomm_ring
  have hM24V_one : mog24V P A C 1 = (24 : ℤ) • (genV P A C * genV P A C) := by
    unfold mog24V hProjV
    rw [hDPhi_one, hDJ_one, hDSig_one, mul_one, mul_zero, add_zero, add_zero, add_zero, smul_smul]
    rfl
  have hDPhi_P : derivSqPhi P A C P = -((2 : ℤ) • genSig P A C) := by
    unfold derivSqPhi comm; peirce_nf hP
  rcases (archetype_A85_all_mode_double_derivation_virasoro_dichotomy_and_projection
      hP A C (r + r) 0 0 0).1 with
    ⟨hDPhi_V, _, _, _, _, _⟩
  have hDPhi_Phi : derivSqPhi P A C (genPhi P A C * opPow r (genV P A C)) = 0 :=
    (archetype_A85_all_mode_double_derivation_virasoro_dichotomy_and_projection
      hP A C r 0 0 0).1.2.2.2.1
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hSq_S, hG12_add, hG12_one, hG12_V]
  · rw [hSq_S, hG24_add, hG24_one, hG24_V]
  · rw [hSq_S, hM24V_add, hM24V_one, hM24_V]
  · rw [hSq_S, hDPhi_add, hDPhi_one, hDPhi_V, add_zero]
  · rw [hSym_Comp, hG12_add, hG12_one, two_zsmul, hG12_add, hG12_V]
    have h24 : (12 : ℤ) • virasoroModeEven (r + r + 1) P A C +
        (12 : ℤ) • virasoroModeEven (r + r + 1) P A C =
          (24 : ℤ) • virasoroModeEven (r + r + 1) P A C := by
      calc (12 : ℤ) • virasoroModeEven (r + r + 1) P A C +
             (12 : ℤ) • virasoroModeEven (r + r + 1) P A C
          = ((12 : ℤ) + (12 : ℤ)) • virasoroModeEven (r + r + 1) P A C :=
            (add_smul (12 : ℤ) (12 : ℤ) _).symm
        _ = (24 : ℤ) • virasoroModeEven (r + r + 1) P A C := by rfl
    rw [h24]
  · rw [hSym_Comp, hG24_add, hG24_one, two_zsmul, hG24_add, hG24_V]
    have h48 : (24 : ℤ) • virasoroModeEven (r + r + 1) P A C +
        (24 : ℤ) • virasoroModeEven (r + r + 1) P A C =
          (48 : ℤ) • virasoroModeEven (r + r + 1) P A C := by
      calc (24 : ℤ) • virasoroModeEven (r + r + 1) P A C +
             (24 : ℤ) • virasoroModeEven (r + r + 1) P A C
          = ((24 : ℤ) + (24 : ℤ)) • virasoroModeEven (r + r + 1) P A C :=
            (add_smul (24 : ℤ) (24 : ℤ) _).symm
        _ = (48 : ℤ) • virasoroModeEven (r + r + 1) P A C := by rfl
    rw [h48]
  · rw [hSym_Comp, hDPhi_add, hDPhi_one, two_zsmul, hDPhi_add, hDPhi_V]
    simp
  · rw [hSq_P, hDPhi_add, hDPhi_add, hDPhi_P, hDPhi_Phi, hDPhi_V, add_zero, add_zero]

/-- **Archetype `A₉₄` (`M₆`, `archetype_A94_star_self_adjointness_gram_coercivity_and_modular_grading_duality`):**
Over any star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent `P² = P`, `star P = P`,
seed `A : B`, and mode index `r : ℕ`, let
`J_r^+ = heisenbergSourceMode r P A (star A)` and `J_r^- = heisenbergSinkMode r P A (star A)`:
1. **Star-Adjoint Conjugation & Self-Adjoint / Skew-Adjoint Mode Duality:**
   - `star (invS P) = invS P`,
   - `star J_r^+ = J_r^-` and `star J_r^- = J_r^+`,
   - `star (genPhi P A (star A) * opPow r (genV P A (star A))) =`
     `genPhi P A (star A) * opPow r (genV P A (star A))`,
   - `star (genJ P A (star A) * opPow r (genV P A (star A))) =`
     `-(genJ P A (star A) * opPow r (genV P A (star A)))`;
2. **All-Mode Gram Coercivity Decomposition into Positive Star-Squares:**
   The even Sugawara–Virasoro mode `virasoroModeEven (r + r) P A (star A)` and the unperturbed
   BdG square `(invS P + genPhi P A (star A) * V^r)^2` are sums of manifestly non-negative
   operator star-squares `X * star X + star X * X`:
   - `J_r^+ * star J_r^+ + star J_r^+ * J_r^+ = virasoroModeEven (r + r) P A (star A)`,
   - `J_r^+ * star J_r^+ - star J_r^+ * J_r^+ = virasoroModeChiral (r + r) P A (star A)`,
   - `(invS P + genPhi P A (star A) * opPow r (genV P A (star A))) *`
     `  star (invS P + genPhi P A (star A) * opPow r (genV P A (star A))) =`
     `1 + (J_r^+ * star J_r^+ + star J_r^+ * J_r^+)`,
   - `(genJ P A (star A) * opPow r (genV P A (star A))) *`
     `  star (genJ P A (star A) * opPow r (genV P A (star A))) =`
     `J_r^+ * star J_r^+ + star J_r^+ * J_r^+`. -/
theorem archetype_A94_star_self_adjointness_gram_coercivity_and_modular_grading_duality
    [StarRing B] (hPs : star P = P)
    (A : B) (r : ℕ) :
    let J_p := heisenbergSourceMode r P A (star A)
    let J_m := heisenbergSinkMode r P A (star A)
    let Phi_r := genPhi P A (star A) * opPow r (genV P A (star A))
    let J_r := genJ P A (star A) * opPow r (genV P A (star A))
    (star (invS P) = invS P ∧
     star J_p = J_m ∧
     star J_m = J_p ∧
     star Phi_r = Phi_r ∧
     star J_r = -J_r) ∧
    (J_p * star J_p + star J_p * J_p = virasoroModeEven (r + r) P A (star A) ∧
     J_p * star J_p - star J_p * J_p = virasoroModeChiral (r + r) P A (star A) ∧
     (invS P + Phi_r) * star (invS P + Phi_r) =
       1 + (J_p * star J_p + star J_p * J_p) ∧
     J_r * star J_r = J_p * star J_p + star J_p * J_p) := by
  intro J_p J_m Phi_r J_r
  have hStarS : star (invS P) = invS P := by
    unfold invS
    rw [star_sub, star_sub, star_one, hPs]
  rcases all_mode_heisenberg_virasoro_hopf_coordinate_identity_and_furey_tower hP hPs A r with
    ⟨hStarJp, hStarJm, hCoordZ, _, hRad, _, _⟩
  have hVNp : opPow r (genV P A (star A)) * conePlus P A =
      conePlus P A * opPow r (genV P A (star A)) :=
    (opPow_genV_comm_invS_and_cones hP A (star A) r).2.1.symm
  have hPhi_eq : Phi_r = J_p + J_m := by
    change (conePlus P A + coneMinus P (star A)) * opPow r (genV P A (star A)) =
      opPow r (genV P A (star A)) * conePlus P A + coneMinus P (star A) * opPow r (genV P A (star A))
    rw [add_mul, ← hVNp]
  have hJ_eq : J_r = J_p - J_m := by
    change (conePlus P A - coneMinus P (star A)) * opPow r (genV P A (star A)) =
      opPow r (genV P A (star A)) * conePlus P A - coneMinus P (star A) * opPow r (genV P A (star A))
    rw [sub_mul, ← hVNp]
  have hStarPhi : star Phi_r = Phi_r := by
    rw [hPhi_eq, star_add, hStarJp, hStarJm, add_comm]
  have hStarJ : star J_r = -J_r := by
    rw [hJ_eq, star_sub, hStarJp, hStarJm]
    abel
  have hGramAdd : J_p * star J_p + star J_p * J_p = virasoroModeEven (r + r) P A (star A) := by
    calc J_p * star J_p + star J_p * J_p
        = J_p * star J_p + J_m * star J_m := by rw [hStarJp, hStarJm]
      _ = hopfRadiusSq J_p J_m := rfl
      _ = virasoroModeEven (r + r) P A (star A) := hRad
  have hGramSub : J_p * star J_p - star J_p * J_p = virasoroModeChiral (r + r) P A (star A) := by
    calc J_p * star J_p - star J_p * J_p
        = J_p * star J_p - J_m * star J_m := by rw [hStarJp, hStarJm]
      _ = hopfCoordZ J_p J_m := rfl
      _ = virasoroModeChiral (r + r) P A (star A) := hCoordZ
  rcases archetype_A89_peirce_bdg_square_commutator_anomaly_and_grading_symmetrization
      hP A (star A) r with
    ⟨⟨_, _, hSq_S, _⟩, _⟩
  have hBdG_Gram :
      (invS P + Phi_r) * star (invS P + Phi_r) =
        1 + (J_p * star J_p + star J_p * J_p) := by
    rw [star_add, hStarS, hStarPhi, hGramAdd]
    exact hSq_S
  have hJ_Gram : J_r * star J_r = J_p * star J_p + star J_p * J_p := by
    rw [hStarJ, mul_neg, hGramAdd]
    have hJMode_sq : J_r * J_r = -virasoroModeEven (r + r) P A (star A) := by
      calc J_r * J_r = (J_p - J_m) * (J_p - J_m) := by rw [hJ_eq]
        _ = -virasoroModeEven (r + r) P A (star A) :=
          (archetype_A91_source_sink_car_ccr_mode_duality_and_hopf_norm_splitting
            hP A (star A) r r).2.2.2.1
    rw [hJMode_sq, neg_neg]
  exact ⟨⟨hStarS, hStarJp, hStarJm, hStarPhi, hStarJ⟩,
         ⟨hGramAdd, hGramSub, hBdG_Gram, hJ_Gram⟩⟩

end Tier4

/-! ### Part 5: Tier 5 Archetypes (`A₉₅ → A₉₉`): Steinberg Cross-Stage, Klein–Plabic Transport & All-Mode Fourier Characters -/

section Tier5

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

/-- **Archetype `A₉₅` (`archetype_A95_dual_steinberg_braid_weyl_decomposition_and_cross_defect_chains`):**
Over any non-commutative ring `[Ring B]` with idempotent `P² = P` and seeds `A C : B`:
1. **Dual Steinberg Braid Weyl Decomposition & Yang–Baxter Shear Defects (`A₁₇` Cross-Strand):**
   - `steinbergBraid P A C = weylJ P A C + (1 - genV P A C) * conePlus P A`,
   - `steinbergBraidDual P A C = weylJ P A C - (1 - genV P A C) * coneMinus P C`,
   - `steinbergBraid P A C - steinbergBraidDual P A C = (1 - genV P A C) * genPhi P A C`,
   - `steinbergBraidInv P A C = weylJInv P A C - (1 - genV P A C) * conePlus P A`,
   - `steinbergBraidDualInv P A C = weylJInv P A C + (1 - genV P A C) * coneMinus P C`,
   - `steinbergBraidDualInv P A C - steinbergBraidInv P A C = (1 - genV P A C) * genPhi P A C`;
2. **Exact 11-Chain Cross-Product Defects (`B₊ B₋' - 1` and `B₋ B₊' - 1`, `A₁₈` Cross-Stage):**
   - `steinbergBraid P A C * steinbergBraidDualInv P A C - 1` equals the 11-term alternating
     cone-word expansion,
   - `steinbergBraidDual P A C * steinbergBraidInv P A C - 1` equals the sign-mirrored 11-term
     alternating cone-word expansion. -/
theorem archetype_A95_dual_steinberg_braid_weyl_decomposition_and_cross_defect_chains
    (A C : B) :
    (steinbergBraid P A C = weylJ P A C + (1 - genV P A C) * conePlus P A ∧
     steinbergBraidDual P A C = weylJ P A C - (1 - genV P A C) * coneMinus P C ∧
     steinbergBraid P A C - steinbergBraidDual P A C =
       (1 - genV P A C) * genPhi P A C ∧
     steinbergBraidInv P A C = weylJInv P A C - (1 - genV P A C) * conePlus P A ∧
     steinbergBraidDualInv P A C = weylJInv P A C + (1 - genV P A C) * coneMinus P C ∧
     steinbergBraidDualInv P A C - steinbergBraidInv P A C =
       (1 - genV P A C) * genPhi P A C) ∧
    (steinbergBraid P A C * steinbergBraidDualInv P A C - 1 =
       conePlus P A + coneMinus P C
         + (2 : ℤ) • (conePlus P A * coneMinus P C)
         - coneMinus P C * conePlus P A
         - (2 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A)
         - (2 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C)
         - (3 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A * coneMinus P C)
         + coneMinus P C * conePlus P A * coneMinus P C * conePlus P A
         + conePlus P A * coneMinus P C * conePlus P A * coneMinus P C * conePlus P A
         + coneMinus P C * conePlus P A * coneMinus P C * conePlus P A * coneMinus P C
         + conePlus P A * coneMinus P C * conePlus P A * coneMinus P C * conePlus P A
             * coneMinus P C ∧
     steinbergBraidDual P A C * steinbergBraidInv P A C - 1 =
       -(conePlus P A) - coneMinus P C
         - conePlus P A * coneMinus P C
         + (2 : ℤ) • (coneMinus P C * conePlus P A)
         + (2 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A)
         + (2 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C)
         + conePlus P A * coneMinus P C * conePlus P A * coneMinus P C
         - (3 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C * conePlus P A)
         - conePlus P A * coneMinus P C * conePlus P A * coneMinus P C * conePlus P A
         - coneMinus P C * conePlus P A * coneMinus P C * conePlus P A * coneMinus P C
         + coneMinus P C * conePlus P A * coneMinus P C * conePlus P A * coneMinus P C
             * conePlus P A) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    (simp only [steinbergBraid, steinbergBraidDual, steinbergBraidInv, steinbergBraidDualInv,
       weylJ, weylJInv];
     peirce_nf hP)

/-- **Archetype `A₉₆` (`archetype_A96_tetraktys_sandwich_covariance_and_center_commutant`):**
Over any non-commutative ring `[Ring B]` with idempotent `P² = P` and seeds `A C : B`:
1. **Nine Off-Shell Tetraktys Sandwich Covariances under `J` and `Φ` Braid Reflections:**
   - `genJ P A C * genV P A C * -(genJ P A C) = genV P A C * genV P A C`,
   - `-(genJ P A C) * genV P A C * genJ P A C = genV P A C * genV P A C`,
   - `genPhi P A C * genV P A C * genPhi P A C = genV P A C * genV P A C`,
   - `genJ P A C * genJ P A C * -(genJ P A C) = genV P A C * genJ P A C`,
   - `genPhi P A C * genJ P A C * genPhi P A C = -(genV P A C * genJ P A C)`,
   - `genJ P A C * genPhi P A C * -(genJ P A C) = -(genV P A C * genPhi P A C)`,
   - `genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C`,
   - `genJ P A C * genSig P A C * -(genJ P A C) = -(genV P A C * genSig P A C)`,
   - `genPhi P A C * genSig P A C * genPhi P A C = -(genV P A C * genSig P A C)`;
2. **Tetraktys Center Commutant (`V` Commutes with All Principal Axes `J, Φ, Σ`):**
   - `comm (genJ P A C) (genV P A C) = 0`,
   - `comm (genPhi P A C) (genV P A C) = 0`,
   - `comm (genSig P A C) (genV P A C) = 0`. -/
theorem archetype_A96_tetraktys_sandwich_covariance_and_center_commutant
    (A C : B) :
    (genJ P A C * genV P A C * -(genJ P A C) = genV P A C * genV P A C ∧
     -(genJ P A C) * genV P A C * genJ P A C = genV P A C * genV P A C ∧
     genPhi P A C * genV P A C * genPhi P A C = genV P A C * genV P A C ∧
     genJ P A C * genJ P A C * -(genJ P A C) = genV P A C * genJ P A C ∧
     genPhi P A C * genJ P A C * genPhi P A C = -(genV P A C * genJ P A C) ∧
     genJ P A C * genPhi P A C * -(genJ P A C) = -(genV P A C * genPhi P A C) ∧
     genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C ∧
     genJ P A C * genSig P A C * -(genJ P A C) = -(genV P A C * genSig P A C) ∧
     genPhi P A C * genSig P A C * genPhi P A C = -(genV P A C * genSig P A C)) ∧
    (comm (genJ P A C) (genV P A C) = 0 ∧
     comm (genPhi P A C) (genV P A C) = 0 ∧
     comm (genSig P A C) (genV P A C) = 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> peirce_nf hP

/-- **Archetype `A₉₇` (`archetype_A97_klein_four_sandwich_channel_realization_and_plabic_parity_transport`):**
Over any non-commutative ring `[Ring B]` with idempotent `P² = P`, seeds `A C : B`, and elements
`X Z : B`:
1. **On-Shell Klein-Four Ring Automorphism Realization (`hV : genV P A C = 1`):**
   When `genV P A C = 1`, the four sandwich character channels `grpId, grpPhi, grpJ, grpSig`
   coincide with the four automorphisms of the Peirce Klein-four action:
   - `grpId P A C X = X`,
   - `grpPhi P A C X = phiUnitSquareEquiv hP A C hV X`,
   - `grpJ P A C X = phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X)`,
   - `grpSig P A C X = parityConjRingEquiv hP X`;
2. **Off-Shell Plabic Boundary Idempotent & Null-Space Twistor Parity Transport:**
   - `parityConj P (plabicBoundaryOp P A C) = plabicBoundaryOp P (-A) (-C)`,
   - `parityConj P (plabicTwistorSol P A C Z) = plabicTwistorSol P (-A) (-C) (parityConj P Z)`. -/
theorem archetype_A97_klein_four_sandwich_channel_realization_and_plabic_parity_transport
    (A C X Z : B) :
    (∀ hV : genV P A C = 1,
      grpId P A C X = X ∧
      grpPhi P A C X = phiUnitSquareEquiv hP A C hV X ∧
      grpJ P A C X = phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X) ∧
      grpSig P A C X = parityConjRingEquiv hP X) ∧
    (parityConj P (plabicBoundaryOp P A C) =
       plabicBoundaryOp P (-A) (-C) ∧
     parityConj P (plabicTwistorSol P A C Z) =
       plabicTwistorSol P (-A) (-C) (parityConj P Z)) :=
  ⟨fun hV => tetraktys_sandwich_channels_are_peirce_klein_action hP A C hV X,
   parity_transports_plabic_boundary_and_nullspace hP A C Z⟩

/-- **Archetype `A₉₈` (`archetype_A98_all_mode_tetraktys_sandwich_covariance_and_center_commutant`):**
Over any non-commutative ring `[Ring B]` with idempotent `P² = P`, seeds `A C : B`, and mode index
`r : ℕ`, let:
- `L_r^+ = virasoroModeEven r P A C`,
- `L_r^- = virasoroModeChiral r P A C`,
- `Phi_r = genPhi P A C * opPow r (genV P A C)`,
- `J_r = genJ P A C * opPow r (genV P A C)`:
1. **All-Mode Center Commutant (`V` Commutes with Every Even, Chiral, and Odd Mode):**
   - `comm L_r^+ (genV P A C) = 0`,
   - `comm L_r^- (genV P A C) = 0`,
   - `comm Phi_r (genV P A C) = 0`,
   - `comm J_r (genV P A C) = 0`;
2. **All-Mode `J`- and `Φ`-Sandwich Covariance (`V`-Scaling of `L_r^±, Phi_r, J_r`):**
   - `genJ P A C * L_r^+ * -(genJ P A C) = genV P A C * L_r^+`,
   - `genPhi P A C * L_r^+ * genPhi P A C = genV P A C * L_r^+`,
   - `genJ P A C * L_r^- * -(genJ P A C) = -(genV P A C * L_r^-)`,
   - `genPhi P A C * L_r^- * genPhi P A C = -(genV P A C * L_r^-)`,
   - `genJ P A C * Phi_r * -(genJ P A C) = -(genV P A C * Phi_r)`,
   - `genPhi P A C * Phi_r * genPhi P A C = genV P A C * Phi_r`,
   - `genJ P A C * J_r * -(genJ P A C) = genV P A C * J_r`,
   - `genPhi P A C * J_r * genPhi P A C = -(genV P A C * J_r)`. -/
theorem archetype_A98_all_mode_tetraktys_sandwich_covariance_and_center_commutant
    (A C : B) (r : ℕ) :
    let L_p := virasoroModeEven r P A C
    let L_m := virasoroModeChiral r P A C
    let Phi_r := genPhi P A C * opPow r (genV P A C)
    let J_r := genJ P A C * opPow r (genV P A C)
    (comm L_p (genV P A C) = 0 ∧
     comm L_m (genV P A C) = 0 ∧
     comm Phi_r (genV P A C) = 0 ∧
     comm J_r (genV P A C) = 0) ∧
    (genJ P A C * L_p * -(genJ P A C) = genV P A C * L_p ∧
     genPhi P A C * L_p * genPhi P A C = genV P A C * L_p ∧
     genJ P A C * L_m * -(genJ P A C) = -(genV P A C * L_m) ∧
     genPhi P A C * L_m * genPhi P A C = -(genV P A C * L_m) ∧
     genJ P A C * Phi_r * -(genJ P A C) = -(genV P A C * Phi_r) ∧
     genPhi P A C * Phi_r * genPhi P A C = genV P A C * Phi_r ∧
     genJ P A C * J_r * -(genJ P A C) = genV P A C * J_r ∧
     genPhi P A C * J_r * genPhi P A C = -(genV P A C * J_r)) := by
  intro L_p L_m Phi_r J_r
  rcases archetype_A96_tetraktys_sandwich_covariance_and_center_commutant hP A C with
    ⟨⟨hJV, _, hPhiV, hJJ, hPhiJ, hJPhi, hPhiPhi, hJSig, hPhiSig⟩,
     ⟨hCommJV0, hCommPhiV0, hCommSigV0⟩⟩
  have hJV_eq : genJ P A C * genV P A C = genV P A C * genJ P A C :=
    sub_eq_zero.mp hCommJV0
  have hPhiV_eq : genPhi P A C * genV P A C = genV P A C * genPhi P A C :=
    sub_eq_zero.mp hCommPhiV0
  have hSigV_eq : genSig P A C * genV P A C = genV P A C * genSig P A C :=
    sub_eq_zero.mp hCommSigV0
  have hVV : opPow r (genV P A C) * genV P A C = genV P A C * opPow r (genV P A C) :=
    (mul_opPow_comm r (genV P A C)).symm
  have hVPhi : opPow r (genV P A C) * genPhi P A C = genPhi P A C * opPow r (genV P A C) := by
    rcases opPow_genV_comm_invS_and_cones hP A C r with ⟨_, hCp, hCm⟩
    unfold genPhi
    rw [mul_add, add_mul, hCp, hCm]
  have hVJ : opPow r (genV P A C) * genJ P A C = genJ P A C * opPow r (genV P A C) := by
    rcases opPow_genV_comm_invS_and_cones hP A C r with ⟨_, hCp, hCm⟩
    unfold genJ
    rw [mul_sub, sub_mul, hCp, hCm]
  have hVSig : opPow r (genV P A C) * genSig P A C = genSig P A C * opPow r (genV P A C) := by
    have hSig_eq : genSig P A C = invS P * genV P A C := by peirce_nf hP
    rw [hSig_eq, ← mul_assoc, ← (opPow_genV_comm_invS_and_cones hP A C r).1,
        mul_assoc, hVV, ← mul_assoc]
  have hLp_eq : L_p = genV P A C * opPow r (genV P A C) := by
    change opPow r (genV P A C) * genV P A C = genV P A C * opPow r (genV P A C)
    exact hVV
  have hLm_eq : L_m = genSig P A C * opPow r (genV P A C) := by
    change opPow r (genV P A C) * genSig P A C = genSig P A C * opPow r (genV P A C)
    exact hVSig
  have hCommLp : comm L_p (genV P A C) = 0 := by
    rw [hLp_eq]
    unfold comm
    calc (genV P A C * opPow r (genV P A C)) * genV P A C -
           genV P A C * (genV P A C * opPow r (genV P A C))
        = genV P A C * (opPow r (genV P A C) * genV P A C) -
          genV P A C * (genV P A C * opPow r (genV P A C)) := by rw [mul_assoc]
      _ = 0 := by rw [hVV, sub_self]
  have hCommLm : comm L_m (genV P A C) = 0 := by
    rw [hLm_eq]
    unfold comm
    calc (genSig P A C * opPow r (genV P A C)) * genV P A C -
           genV P A C * (genSig P A C * opPow r (genV P A C))
        = (genSig P A C * genV P A C) * opPow r (genV P A C) -
          (genV P A C * genSig P A C) * opPow r (genV P A C) := by
          rw [mul_assoc, hVV, ← mul_assoc, ← mul_assoc]
      _ = 0 := by rw [hSigV_eq, sub_self]
  have hCommPhi : comm Phi_r (genV P A C) = 0 := by
    unfold comm
    calc (genPhi P A C * opPow r (genV P A C)) * genV P A C -
           genV P A C * (genPhi P A C * opPow r (genV P A C))
        = (genPhi P A C * genV P A C) * opPow r (genV P A C) -
          (genV P A C * genPhi P A C) * opPow r (genV P A C) := by
          rw [mul_assoc, hVV, ← mul_assoc, ← mul_assoc]
      _ = 0 := by rw [hPhiV_eq, sub_self]
  have hCommJ : comm J_r (genV P A C) = 0 := by
    unfold comm
    calc (genJ P A C * opPow r (genV P A C)) * genV P A C -
           genV P A C * (genJ P A C * opPow r (genV P A C))
        = (genJ P A C * genV P A C) * opPow r (genV P A C) -
          (genV P A C * genJ P A C) * opPow r (genV P A C) := by
          rw [mul_assoc, hVV, ← mul_assoc, ← mul_assoc]
      _ = 0 := by rw [hJV_eq, sub_self]
  have hSandJ (Y : B) :
      genJ P A C * (Y * opPow r (genV P A C)) * -(genJ P A C) =
        (genJ P A C * Y * -(genJ P A C)) * opPow r (genV P A C) := by
    calc genJ P A C * (Y * opPow r (genV P A C)) * -(genJ P A C)
        = -(genJ P A C * Y * (opPow r (genV P A C) * genJ P A C)) := by noncomm_ring
      _ = -(genJ P A C * Y * (genJ P A C * opPow r (genV P A C))) := by rw [hVJ]
      _ = (genJ P A C * Y * -(genJ P A C)) * opPow r (genV P A C) := by noncomm_ring
  have hSandPhi (Y : B) :
      genPhi P A C * (Y * opPow r (genV P A C)) * genPhi P A C =
        (genPhi P A C * Y * genPhi P A C) * opPow r (genV P A C) := by
    calc genPhi P A C * (Y * opPow r (genV P A C)) * genPhi P A C
        = genPhi P A C * Y * (opPow r (genV P A C) * genPhi P A C) := by noncomm_ring
      _ = genPhi P A C * Y * (genPhi P A C * opPow r (genV P A C)) := by rw [hVPhi]
      _ = (genPhi P A C * Y * genPhi P A C) * opPow r (genV P A C) := by noncomm_ring
  refine ⟨⟨hCommLp, hCommLm, hCommPhi, hCommJ⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hLp_eq, hSandJ, hJV, mul_assoc]
  · rw [hLp_eq, hSandPhi, hPhiV, mul_assoc]
  · rw [hLm_eq, hSandJ, hJSig, neg_mul, mul_assoc]
  · rw [hLm_eq, hSandPhi, hPhiSig, neg_mul, mul_assoc]
  · change genJ P A C * (genPhi P A C * opPow r (genV P A C)) * -(genJ P A C) =
      -(genV P A C * (genPhi P A C * opPow r (genV P A C)))
    rw [hSandJ, hJPhi, neg_mul, mul_assoc]
  · change genPhi P A C * (genPhi P A C * opPow r (genV P A C)) * genPhi P A C =
      genV P A C * (genPhi P A C * opPow r (genV P A C))
    rw [hSandPhi, hPhiPhi, mul_assoc]
  · change genJ P A C * (genJ P A C * opPow r (genV P A C)) * -(genJ P A C) =
      genV P A C * (genJ P A C * opPow r (genV P A C))
    rw [hSandJ, hJJ, mul_assoc]
  · change genPhi P A C * (genJ P A C * opPow r (genV P A C)) * genPhi P A C =
      -(genV P A C * (genJ P A C * opPow r (genV P A C)))
    rw [hSandPhi, hPhiJ, neg_mul, mul_assoc]

/-- **Archetype `A₉₉` (`archetype_A99_all_mode_group_sandwich_fourier_character_eigenspaces`):**
Over any non-commutative ring `[Ring B]` with idempotent `P² = P`, seeds `A C : B`, and mode index
`r : ℕ`, let:
- `L_r^+ = virasoroModeEven r P A C`,
- `L_r^- = virasoroModeChiral r P A C`,
- `Phi_r = genPhi P A C * opPow r (genV P A C)`,
- `J_r = genJ P A C * opPow r (genV P A C)`:
1. **All-Mode Group-Sandwich Character Table (`grpPhi, grpJ, grpSig` vs `grpId`):**
   - `grpPhi P A C L_r^+ = grpId P A C L_r^+`, `grpPhi P A C Phi_r = grpId P A C Phi_r`,
     `grpPhi P A C J_r = -grpId P A C J_r`, `grpPhi P A C L_r^- = -grpId P A C L_r^-`,
   - `grpJ P A C L_r^+ = grpId P A C L_r^+`, `grpJ P A C Phi_r = -grpId P A C Phi_r`,
     `grpJ P A C J_r = grpId P A C J_r`, `grpJ P A C L_r^- = -grpId P A C L_r^-`,
   - `grpSig P A C L_r^+ = grpId P A C L_r^+`, `grpSig P A C Phi_r = -grpId P A C Phi_r`,
     `grpSig P A C J_r = -grpId P A C J_r`, `grpSig P A C L_r^- = grpId P A C L_r^-`;
2. **All-Mode Klein–Fourier Orthogonal Character Eigenvalue Isolation (`8 V²` Eigenvalue & Cross-Channel Annihilation):**
   - `fourierV P A C L_r^+ = (8 : ℤ) • grpId P A C L_r^+` and
     `fourierPhi P A C L_r^+ = 0` and `fourierJ P A C L_r^+ = 0` and `fourierSig P A C L_r^+ = 0`,
   - `fourierPhi P A C Phi_r = (8 : ℤ) • grpId P A C Phi_r` and
     `fourierV P A C Phi_r = 0` and `fourierJ P A C Phi_r = 0` and `fourierSig P A C Phi_r = 0`,
   - `fourierJ P A C J_r = (8 : ℤ) • grpId P A C J_r` and
     `fourierV P A C J_r = 0` and `fourierPhi P A C J_r = 0` and `fourierSig P A C J_r = 0`,
   - `fourierSig P A C L_r^- = (8 : ℤ) • grpId P A C L_r^-` and
     `fourierV P A C L_r^- = 0` and `fourierPhi P A C L_r^- = 0` and `fourierJ P A C L_r^- = 0`. -/
theorem archetype_A99_all_mode_group_sandwich_fourier_character_eigenspaces
    (A C : B) (r : ℕ) :
    let L_p := virasoroModeEven r P A C
    let L_m := virasoroModeChiral r P A C
    let Phi_r := genPhi P A C * opPow r (genV P A C)
    let J_r := genJ P A C * opPow r (genV P A C)
    (grpPhi P A C L_p = grpId P A C L_p ∧
     grpPhi P A C Phi_r = grpId P A C Phi_r ∧
     grpPhi P A C J_r = -grpId P A C J_r ∧
     grpPhi P A C L_m = -grpId P A C L_m ∧
     grpJ P A C L_p = grpId P A C L_p ∧
     grpJ P A C Phi_r = -grpId P A C Phi_r ∧
     grpJ P A C J_r = grpId P A C J_r ∧
     grpJ P A C L_m = -grpId P A C L_m ∧
     grpSig P A C L_p = grpId P A C L_p ∧
     grpSig P A C Phi_r = -grpId P A C Phi_r ∧
     grpSig P A C J_r = -grpId P A C J_r ∧
     grpSig P A C L_m = grpId P A C L_m) ∧
    ((fourierV P A C L_p = (8 : ℤ) • grpId P A C L_p ∧
      fourierPhi P A C L_p = 0 ∧
      fourierJ P A C L_p = 0 ∧
      fourierSig P A C L_p = 0) ∧
     (fourierPhi P A C Phi_r = (8 : ℤ) • grpId P A C Phi_r ∧
      fourierV P A C Phi_r = 0 ∧
      fourierJ P A C Phi_r = 0 ∧
      fourierSig P A C Phi_r = 0) ∧
     (fourierJ P A C J_r = (8 : ℤ) • grpId P A C J_r ∧
      fourierV P A C J_r = 0 ∧
      fourierPhi P A C J_r = 0 ∧
      fourierSig P A C J_r = 0) ∧
     (fourierSig P A C L_m = (8 : ℤ) • grpId P A C L_m ∧
      fourierV P A C L_m = 0 ∧
      fourierPhi P A C L_m = 0 ∧
      fourierJ P A C L_m = 0)) := by
  intro L_p L_m Phi_r J_r
  rcases archetype_A17_group_sandwich_character_table hP A C with
    ⟨hPhiV, hPhiPhi, hPhiJ, hPhiSig,
     hJV, hJPhi, hJJ, hJSig,
     hSigV, hSigPhi, hSigJ, hSigSig, _, _, _, _⟩
  have hVV : opPow r (genV P A C) * genV P A C = genV P A C * opPow r (genV P A C) :=
    (mul_opPow_comm r (genV P A C)).symm
  have hVPhi : opPow r (genV P A C) * genPhi P A C = genPhi P A C * opPow r (genV P A C) := by
    rcases opPow_genV_comm_invS_and_cones hP A C r with ⟨_, hCp, hCm⟩
    unfold genPhi
    rw [mul_add, add_mul, hCp, hCm]
  have hVJ : opPow r (genV P A C) * genJ P A C = genJ P A C * opPow r (genV P A C) := by
    rcases opPow_genV_comm_invS_and_cones hP A C r with ⟨_, hCp, hCm⟩
    unfold genJ
    rw [mul_sub, sub_mul, hCp, hCm]
  have hVSig : opPow r (genV P A C) * genSig P A C = genSig P A C * opPow r (genV P A C) := by
    have hSig_eq : genSig P A C = invS P * genV P A C := by peirce_nf hP
    rw [hSig_eq, ← mul_assoc, ← (opPow_genV_comm_invS_and_cones hP A C r).1,
        mul_assoc, hVV, ← mul_assoc]
  have hId_mul (Y : B) :
      grpId P A C (Y * opPow r (genV P A C)) = grpId P A C Y * opPow r (genV P A C) := by
    unfold grpId
    noncomm_ring
  have hPhi_mul (Y : B) :
      grpPhi P A C (Y * opPow r (genV P A C)) = grpPhi P A C Y * opPow r (genV P A C) := by
    unfold grpPhi
    calc genV P A C * (genPhi P A C * (Y * opPow r (genV P A C)) * genPhi P A C)
        = genV P A C * (genPhi P A C * Y * (opPow r (genV P A C) * genPhi P A C)) := by noncomm_ring
      _ = genV P A C * (genPhi P A C * Y * (genPhi P A C * opPow r (genV P A C))) := by rw [hVPhi]
      _ = (genV P A C * (genPhi P A C * Y * genPhi P A C)) * opPow r (genV P A C) := by noncomm_ring
  have hJ_mul (Y : B) :
      grpJ P A C (Y * opPow r (genV P A C)) = grpJ P A C Y * opPow r (genV P A C) := by
    unfold grpJ
    calc -(genV P A C * (genJ P A C * (Y * opPow r (genV P A C)) * genJ P A C))
        = -(genV P A C * (genJ P A C * Y * (opPow r (genV P A C) * genJ P A C))) := by noncomm_ring
      _ = -(genV P A C * (genJ P A C * Y * (genJ P A C * opPow r (genV P A C)))) := by rw [hVJ]
      _ = -(genV P A C * (genJ P A C * Y * genJ P A C)) * opPow r (genV P A C) := by noncomm_ring
  have hSig_mul (Y : B) :
      grpSig P A C (Y * opPow r (genV P A C)) = grpSig P A C Y * opPow r (genV P A C) := by
    unfold grpSig
    calc genSig P A C * (Y * opPow r (genV P A C)) * genSig P A C
        = genSig P A C * Y * (opPow r (genV P A C) * genSig P A C) := by noncomm_ring
      _ = genSig P A C * Y * (genSig P A C * opPow r (genV P A C)) := by rw [hVSig]
      _ = (genSig P A C * Y * genSig P A C) * opPow r (genV P A C) := by noncomm_ring
  have hLp_eq : L_p = genV P A C * opPow r (genV P A C) := hVV
  have hLm_eq : L_m = genSig P A C * opPow r (genV P A C) := hVSig
  have h1 : grpPhi P A C L_p = grpId P A C L_p := by
    rw [hLp_eq, hPhi_mul, hPhiV, hId_mul]
  have h2 : grpPhi P A C Phi_r = grpId P A C Phi_r := by
    change grpPhi P A C (genPhi P A C * opPow r (genV P A C)) =
      grpId P A C (genPhi P A C * opPow r (genV P A C))
    rw [hPhi_mul, hPhiPhi, hId_mul]
  have h3 : grpPhi P A C J_r = -grpId P A C J_r := by
    change grpPhi P A C (genJ P A C * opPow r (genV P A C)) =
      -grpId P A C (genJ P A C * opPow r (genV P A C))
    rw [hPhi_mul, hPhiJ, neg_mul, hId_mul]
  have h4 : grpPhi P A C L_m = -grpId P A C L_m := by
    rw [hLm_eq, hPhi_mul, hPhiSig, neg_mul, hId_mul]
  have h5 : grpJ P A C L_p = grpId P A C L_p := by
    rw [hLp_eq, hJ_mul, hJV, hId_mul]
  have h6 : grpJ P A C Phi_r = -grpId P A C Phi_r := by
    change grpJ P A C (genPhi P A C * opPow r (genV P A C)) =
      -grpId P A C (genPhi P A C * opPow r (genV P A C))
    rw [hJ_mul, hJPhi, neg_mul, hId_mul]
  have h7 : grpJ P A C J_r = grpId P A C J_r := by
    change grpJ P A C (genJ P A C * opPow r (genV P A C)) =
      grpId P A C (genJ P A C * opPow r (genV P A C))
    rw [hJ_mul, hJJ, hId_mul]
  have h8 : grpJ P A C L_m = -grpId P A C L_m := by
    rw [hLm_eq, hJ_mul, hJSig, neg_mul, hId_mul]
  have h9 : grpSig P A C L_p = grpId P A C L_p := by
    rw [hLp_eq, hSig_mul, hSigV, hId_mul]
  have h10 : grpSig P A C Phi_r = -grpId P A C Phi_r := by
    change grpSig P A C (genPhi P A C * opPow r (genV P A C)) =
      -grpId P A C (genPhi P A C * opPow r (genV P A C))
    rw [hSig_mul, hSigPhi, neg_mul, hId_mul]
  have h11 : grpSig P A C J_r = -grpId P A C J_r := by
    change grpSig P A C (genJ P A C * opPow r (genV P A C)) =
      -grpId P A C (genJ P A C * opPow r (genV P A C))
    rw [hSig_mul, hSigJ, neg_mul, hId_mul]
  have h12 : grpSig P A C L_m = grpId P A C L_m := by
    rw [hLm_eq, hSig_mul, hSigSig, hId_mul]
  have hFour (G : B) : (2 : ℤ) • (G + G + G + G) = (8 : ℤ) • G := by
    module
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩,
          ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩⟩
  · unfold fourierV; rw [h1, h5, h9]; exact hFour _
  · unfold fourierPhi; rw [h1, h5, h9]; module
  · unfold fourierJ; rw [h1, h5, h9]; module
  · unfold fourierSig; rw [h1, h5, h9]; module
  · unfold fourierPhi; rw [h2, h6, h10]; module
  · unfold fourierV; rw [h2, h6, h10]; module
  · unfold fourierJ; rw [h2, h6, h10]; module
  · unfold fourierSig; rw [h2, h6, h10]; module
  · unfold fourierJ; rw [h3, h7, h11]; module
  · unfold fourierV; rw [h3, h7, h11]; module
  · unfold fourierPhi; rw [h3, h7, h11]; module
  · unfold fourierSig; rw [h3, h7, h11]; module
  · unfold fourierSig; rw [h4, h8, h12]; module
  · unfold fourierV; rw [h4, h8, h12]; module
  · unfold fourierPhi; rw [h4, h8, h12]; module
  · unfold fourierJ; rw [h4, h8, h12]; module

end Tier5

/-! ### Part 6: Tier 6 Archetypes (`A₁₀₀ → A₁₀₄` / Causal Poset `K₁ → K₅` & Stage `D₃₂`):
Krein Fundamental Symmetry as the `Ξ` Critical Reflection, Critical Seam Fixed Locus vs. Off-Seam
Chiral Deviation, Centered Wallpaper Glide Reflection, All-Mode `Ξ` Zero-Reflection Transport, and
Explicit Half-Height Wallpaper Glide Obstruction Defect -/

section Tier6Defs

variable {B : Type*} [Ring B]

/-- **Krein Fundamental Critical Reflection (`kreinReflect`):**
`kreinReflect P X = invS P * star X * invS P`. -/
def kreinReflect [Star B] (P X : B) : B :=
  invS P * star X * invS P

/-- **Zorn / Parity Reflection (`zornReflect`):**
Alias for the multiplicative grading conjugation `parityConj P X = invS P * X * invS P`. -/
abbrev zornReflect (P X : B) : B :=
  parityConj P X

/-- **Centered-Zeta Coordinate Chart (`centeredZetaChart`):**
Maps a carrier spectral parameter `S_carrier` to its centered coordinate `S_carrier - P`. -/
def centeredZetaChart (P S_carrier : B) : B :=
  S_carrier - P

/-- **Inverse Centered-Zeta Coordinate Chart (`carrierFromCentered`):**
Maps a centered coordinate `X_cent` back to the carrier parameter `P + X_cent`. -/
def carrierFromCentered (P X_cent : B) : B :=
  P + X_cent

/-- **Carrier-Space Krein Critical Reflection (`carrierKreinReflect`):**
Induced by `kreinReflect P` via `centeredZetaChart P` and `carrierFromCentered P`. -/
def carrierKreinReflect [Star B] (P S_carrier : B) : B :=
  carrierFromCentered P (kreinReflect P (centeredZetaChart P S_carrier))

/-- **Krein-Symmetric Critical Seam Component (`seamPart`):**
`seamPart P X = X + kreinReflect P X`. -/
def seamPart [Star B] (P X : B) : B :=
  X + kreinReflect P X

/-- **Krein-Skew Off-Seam Deviation Component (`offSeamPart`):**
`offSeamPart P X = X - kreinReflect P X`. -/
def offSeamPart [Star B] (P X : B) : B :=
  X - kreinReflect P X

/-- **Centered Wallpaper Glide Reflection (`wallpaperGlide`):**
Combines the Krein critical reflection `kreinReflect P X` with a half-period seam translation `T_step`. -/
def wallpaperGlide [Star B] (P T_step X : B) : B :=
  kreinReflect P X + T_step

/-- **Carrier-Space Wallpaper Glide (`carrierGlide`):**
Induced by `wallpaperGlide P T_step` via `centeredZetaChart P` and `carrierFromCentered P`. -/
def carrierGlide [Star B] (P T_step S_carrier : B) : B :=
  carrierFromCentered P (wallpaperGlide P T_step (centeredZetaChart P S_carrier))

/-- **Non-Commutative Centered `Ξ`-Operator (`xiCenteredOp`):**
`xiCenteredOp X = 1 - X * X` (which evaluates on `Φ(A, C)` to the Euler–Bergman factor `1 - V(A, C)`). -/
def xiCenteredOp (X : B) : B :=
  1 - X * X

/-- **Non-Commutative Carrier `Ξ`-Operator (`xiCarrierOp`):**
`xiCarrierOp P S_carrier = xiCenteredOp (centeredZetaChart P S_carrier)`. -/
def xiCarrierOp (P S_carrier : B) : B :=
  xiCenteredOp (centeredZetaChart P S_carrier)

end Tier6Defs

section Tier6

variable {B : Type*} [Ring B] [StarRing B] {P : B} (hP : P * P = P) (hPsym : star P = P)
include hP hPsym

/-- **Archetype `A₁₀₀` (`K₁`, `archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, and elements `S_carrier X Y : B`:
1. **Centered-Zeta Chart Bijection & Krein Reflection Intertwining:**
   - `centeredZetaChart P (carrierFromCentered P X) = X`,
   - `carrierFromCentered P (centeredZetaChart P S_carrier) = S_carrier`,
   - `centeredZetaChart P (carrierKreinReflect P S_carrier) = kreinReflect P (centeredZetaChart P S_carrier)`,
   - `carrierKreinReflect P (carrierFromCentered P X) = carrierFromCentered P (kreinReflect P X)`;
2. **Exact Involutivity, Star-Parity Commuting Factorization & Anti-Multiplicativity:**
   - `kreinReflect P (kreinReflect P X) = X`,
   - `zornReflect P (zornReflect P X) = X`,
   - `kreinReflect P X = zornReflect P (star X)`,
   - `kreinReflect P X = star (zornReflect P X)`,
   - `kreinReflect P (X * Y) = kreinReflect P Y * kreinReflect P X`. -/
theorem archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection
    (S_carrier X Y : B) :
    (centeredZetaChart P (carrierFromCentered P X) = X ∧
     carrierFromCentered P (centeredZetaChart P S_carrier) = S_carrier ∧
     centeredZetaChart P (carrierKreinReflect P S_carrier) =
       kreinReflect P (centeredZetaChart P S_carrier) ∧
     carrierKreinReflect P (carrierFromCentered P X) =
       carrierFromCentered P (kreinReflect P X)) ∧
    (kreinReflect P (kreinReflect P X) = X ∧
     zornReflect P (zornReflect P X) = X ∧
     kreinReflect P X = zornReflect P (star X) ∧
     kreinReflect P X = star (zornReflect P X) ∧
     kreinReflect P (X * Y) = kreinReflect P Y * kreinReflect P X) := by
  have hSsq : invS P * invS P = 1 := by peirce_nf hP
  have hStarS : star (invS P) = invS P := by
    unfold invS; rw [star_sub, star_sub, star_one, hPsym]
  have hC1 : centeredZetaChart P (carrierFromCentered P X) = X := by
    unfold centeredZetaChart carrierFromCentered; abel
  have hC2 : carrierFromCentered P (centeredZetaChart P S_carrier) = S_carrier := by
    unfold centeredZetaChart carrierFromCentered; abel
  have hC3 : centeredZetaChart P (carrierKreinReflect P S_carrier) =
      kreinReflect P (centeredZetaChart P S_carrier) := by
    unfold centeredZetaChart carrierKreinReflect carrierFromCentered; abel
  have hC4 : carrierKreinReflect P (carrierFromCentered P X) =
      carrierFromCentered P (kreinReflect P X) := by
    unfold carrierKreinReflect; rw [hC1]
  have hZornInv : ∀ U : B, zornReflect P (zornReflect P U) = U := by
    intro U
    unfold zornReflect parityConj
    calc invS P * (invS P * U * invS P) * invS P
        = (invS P * invS P) * U * (invS P * invS P) := by noncomm_ring
      _ = U := by rw [hSsq, one_mul, mul_one]
  have hFact1 : ∀ U : B, kreinReflect P U = zornReflect P (star U) := fun _ => rfl
  have hFact2 : ∀ U : B, kreinReflect P U = star (zornReflect P U) := by
    intro U
    unfold kreinReflect zornReflect parityConj
    rw [star_mul, star_mul, hStarS, mul_assoc]
  have hKreinInv : kreinReflect P (kreinReflect P X) = X := by
    rw [hFact2 (kreinReflect P X), hFact1 X, hZornInv (star X), star_star]
  have hKreinMul : kreinReflect P (X * Y) = kreinReflect P Y * kreinReflect P X := by
    unfold kreinReflect
    rw [star_mul]
    calc invS P * (star Y * star X) * invS P
        = invS P * star Y * (invS P * invS P) * star X * invS P := by
          rw [hSsq, mul_one]; noncomm_ring
      _ = (invS P * star Y * invS P) * (invS P * star X * invS P) := by noncomm_ring
  exact ⟨⟨hC1, hC2, hC3, hC4⟩,
         ⟨hKreinInv, hZornInv X, rfl, hFact2 X, hKreinMul⟩⟩

/-- **Archetype `A₁₀₁` (`K₂`, `archetype_A101_all_mode_critical_seam_fixed_locus_vs_off_seam_chiral_deviation`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, elements `X A B_im : B`, and mode index `r : ℕ`:
1. **Critical Seam Fixed-Locus & Off-Seam Skew-Locus Characterizations:**
   - `kreinReflect P X = X ↔ offSeamPart P X = 0`,
   - `kreinReflect P X = -X ↔ seamPart P X = 0`,
   - `kreinReflect P (seamPart P X) = seamPart P X`,
   - `kreinReflect P (offSeamPart P X) = -offSeamPart P X`;
2. **Base Tetraktys Generators (`r = 0`):**
   - `kreinReflect P (genJ P B_im (star B_im)) = genJ P B_im (star B_im)` and
     `offSeamPart P (genJ P B_im (star B_im)) = 0` (`J` lies strictly on the critical seam),
   - `kreinReflect P (genPhi P A (star A)) = -genPhi P A (star A)` and
     `seamPart P (genPhi P A (star A)) = 0` (`Φ` is purely off-seam),
   - `kreinReflect P (genV P A (star A)) = genV P A (star A)`,
   - `kreinReflect P (genSig P A (star A)) = genSig P A (star A)`;
3. **All-Mode (`r : ℕ`) Critical Seam vs. Off-Seam Classification of the Virasoro & Odd Mode Tower:**
   - `kreinReflect P (virasoroModeEven r P A (star A)) = virasoroModeEven r P A (star A)`,
   - `kreinReflect P (virasoroModeChiral r P A (star A)) = virasoroModeChiral r P A (star A)`,
   - `kreinReflect P (genJ P B_im (star B_im) * opPow r (genV P B_im (star B_im))) =`
     `genJ P B_im (star B_im) * opPow r (genV P B_im (star B_im))`,
   - `kreinReflect P (genPhi P A (star A) * opPow r (genV P A (star A))) =`
     `-(genPhi P A (star A) * opPow r (genV P A (star A)))`. -/
theorem archetype_A101_all_mode_critical_seam_fixed_locus_vs_off_seam_chiral_deviation
    (X A B_im : B) (r : ℕ) :
    ((kreinReflect P X = X ↔ offSeamPart P X = 0) ∧
     (kreinReflect P X = -X ↔ seamPart P X = 0) ∧
     kreinReflect P (seamPart P X) = seamPart P X ∧
     kreinReflect P (offSeamPart P X) = -offSeamPart P X) ∧
    (kreinReflect P (genJ P B_im (star B_im)) = genJ P B_im (star B_im) ∧
     offSeamPart P (genJ P B_im (star B_im)) = 0 ∧
     kreinReflect P (genPhi P A (star A)) = -genPhi P A (star A) ∧
     seamPart P (genPhi P A (star A)) = 0 ∧
     kreinReflect P (genV P A (star A)) = genV P A (star A) ∧
     kreinReflect P (genSig P A (star A)) = genSig P A (star A)) ∧
    (kreinReflect P (virasoroModeEven r P A (star A)) =
       virasoroModeEven r P A (star A) ∧
     kreinReflect P (virasoroModeChiral r P A (star A)) =
       virasoroModeChiral r P A (star A) ∧
     kreinReflect P (genJ P B_im (star B_im) * opPow r (genV P B_im (star B_im))) =
       genJ P B_im (star B_im) * opPow r (genV P B_im (star B_im)) ∧
     kreinReflect P (genPhi P A (star A) * opPow r (genV P A (star A))) =
       -(genPhi P A (star A) * opPow r (genV P A (star A)))) := by
  have hInv : ∀ U : B, kreinReflect P (kreinReflect P U) = U :=
    fun U => (archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection
      hP hPsym 0 U 0).2.1
  have hAdd : ∀ U V : B, kreinReflect P (U + V) = kreinReflect P U + kreinReflect P V := by
    intro U V; unfold kreinReflect; rw [star_add, mul_add, add_mul]
  have hSub : ∀ U V : B, kreinReflect P (U - V) = kreinReflect P U - kreinReflect P V := by
    intro U V; unfold kreinReflect; rw [star_sub, mul_sub, sub_mul]
  have hFixed : kreinReflect P X = X ↔ offSeamPart P X = 0 := by
    unfold offSeamPart
    constructor
    · intro h; rw [h, sub_self]
    · intro h; exact (sub_eq_zero.mp h).symm
  have hSkew : kreinReflect P X = -X ↔ seamPart P X = 0 := by
    unfold seamPart
    constructor
    · intro h; rw [h, add_neg_cancel]
    · intro h; exact eq_neg_of_add_eq_zero_right h
  have hSeamFixed : kreinReflect P (seamPart P X) = seamPart P X := by
    unfold seamPart; rw [hAdd, hInv X, add_comm]
  have hOffSkew : kreinReflect P (offSeamPart P X) = -offSeamPart P X := by
    unfold offSeamPart; rw [hSub, hInv X, neg_sub]
  have hStarCone : ∀ W : B, star (conePlus P W) = coneMinus P (star W) := by
    intro W; unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hStarConeM : ∀ W : B, star (coneMinus P (star W)) = conePlus P W := by
    intro W; rw [← hStarCone W, star_star]
  have hStarJ0 : ∀ W : B, star (genJ P W (star W)) = -genJ P W (star W) := by
    intro W; unfold genJ; rw [star_sub, hStarCone W, hStarConeM W, neg_sub]
  have hStarPhi0 : ∀ W : B, star (genPhi P W (star W)) = genPhi P W (star W) := by
    intro W; unfold genPhi; rw [star_add, hStarCone W, hStarConeM W, add_comm]
  have hStarV0 : ∀ W : B, star (genV P W (star W)) = genV P W (star W) := by
    intro W; unfold genV anticomm
    rw [star_add, star_mul, star_mul, hStarCone W, hStarConeM W, add_comm]
  have hStarSig0 : ∀ W : B, star (genSig P W (star W)) = genSig P W (star W) := by
    intro W; unfold genSig comm
    rw [star_sub, star_mul, star_mul, hStarCone W, hStarConeM W]
  have hKreinJ0 : ∀ W : B, kreinReflect P (genJ P W (star W)) = genJ P W (star W) := by
    intro W; unfold kreinReflect; rw [hStarJ0 W]; peirce_nf hP
  have hKreinPhi0 : ∀ W : B, kreinReflect P (genPhi P W (star W)) = -genPhi P W (star W) := by
    intro W; unfold kreinReflect; rw [hStarPhi0 W]; peirce_nf hP
  have hKreinV0 : ∀ W : B, kreinReflect P (genV P W (star W)) = genV P W (star W) := by
    intro W; unfold kreinReflect; rw [hStarV0 W]; peirce_nf hP
  have hKreinSig0 : ∀ W : B, kreinReflect P (genSig P W (star W)) = genSig P W (star W) := by
    intro W; unfold kreinReflect; rw [hStarSig0 W]; peirce_nf hP
  have hOffJ0 : offSeamPart P (genJ P B_im (star B_im)) = 0 := by
    unfold offSeamPart; rw [hKreinJ0 B_im, sub_self]
  have hSeamPhi0 : seamPart P (genPhi P A (star A)) = 0 := by
    unfold seamPart; rw [hKreinPhi0 A, add_neg_cancel]
  have hKreinMul : ∀ U V : B, kreinReflect P (U * V) = kreinReflect P V * kreinReflect P U :=
    fun U V => (archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection
      hP hPsym 0 U V).2.2.2.2.2
  have hKreinOpPow : ∀ (W : B) (k : ℕ),
      kreinReflect P (opPow k (genV P W (star W))) = opPow k (genV P W (star W)) := by
    intro W k
    induction k with
    | zero =>
      change invS P * star (1 : B) * invS P = 1
      rw [star_one, mul_one]
      peirce_nf hP
    | succ m ih =>
      rw [opPow_succ, hKreinMul, ih, hKreinV0 W, mul_opPow_comm, ← opPow_succ]
  have hKreinEven : kreinReflect P (virasoroModeEven r P A (star A)) =
      virasoroModeEven r P A (star A) :=
    hKreinOpPow A (r + 1)
  have hVSig : opPow r (genV P A (star A)) * genSig P A (star A) =
      genSig P A (star A) * opPow r (genV P A (star A)) := by
    have hSig_eq : genSig P A (star A) = invS P * genV P A (star A) := by peirce_nf hP
    have hVV : opPow r (genV P A (star A)) * genV P A (star A) =
        genV P A (star A) * opPow r (genV P A (star A)) :=
      (mul_opPow_comm r (genV P A (star A))).symm
    rw [hSig_eq, ← mul_assoc, ← (opPow_genV_comm_invS_and_cones hP A (star A) r).1,
        mul_assoc, hVV, ← mul_assoc]
  have hKreinChiral : kreinReflect P (virasoroModeChiral r P A (star A)) =
      virasoroModeChiral r P A (star A) := by
    change kreinReflect P (opPow r (genV P A (star A)) * genSig P A (star A)) =
      opPow r (genV P A (star A)) * genSig P A (star A)
    rw [hKreinMul, hKreinSig0 A, hKreinOpPow A r, hVSig]
  have hVJ : opPow r (genV P B_im (star B_im)) * genJ P B_im (star B_im) =
      genJ P B_im (star B_im) * opPow r (genV P B_im (star B_im)) := by
    rcases opPow_genV_comm_invS_and_cones hP B_im (star B_im) r with ⟨_, hCp, hCm⟩
    unfold genJ
    rw [mul_sub, sub_mul, hCp, hCm]
  have hKreinJr :
      kreinReflect P (genJ P B_im (star B_im) * opPow r (genV P B_im (star B_im))) =
        genJ P B_im (star B_im) * opPow r (genV P B_im (star B_im)) := by
    rw [hKreinMul, hKreinOpPow B_im r, hKreinJ0 B_im, hVJ]
  have hVPhi : opPow r (genV P A (star A)) * genPhi P A (star A) =
      genPhi P A (star A) * opPow r (genV P A (star A)) := by
    rcases opPow_genV_comm_invS_and_cones hP A (star A) r with ⟨_, hCp, hCm⟩
    unfold genPhi
    rw [mul_add, add_mul, hCp, hCm]
  have hKreinPhir :
      kreinReflect P (genPhi P A (star A) * opPow r (genV P A (star A))) =
        -(genPhi P A (star A) * opPow r (genV P A (star A))) := by
    rw [hKreinMul, hKreinOpPow A r, hKreinPhi0 A, mul_neg, hVPhi]
  exact ⟨⟨hFixed, hSkew, hSeamFixed, hOffSkew⟩,
         ⟨hKreinJ0 B_im, hOffJ0, hKreinPhi0 A, hSeamPhi0, hKreinV0 A, hKreinSig0 A⟩,
         ⟨hKreinEven, hKreinChiral, hKreinJr, hKreinPhir⟩⟩

/-- **Archetype `A₁₀₂` (`K₃`, `archetype_A102_carrier_glide_wallpaper_glide_intertwining_and_double_glide_translation`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, elements `S_carrier X A B_im : B`, and a critical-seam translation step
`T_step : B` (`hSeamT : kreinReflect P T_step = T_step`):
1. **Chart Intertwining Between `carrierGlide` and `wallpaperGlide`:**
   - `centeredZetaChart P (carrierGlide P T_step S_carrier) =`
     `wallpaperGlide P T_step (centeredZetaChart P S_carrier)`,
   - `carrierGlide P T_step (carrierFromCentered P X) =`
     `carrierFromCentered P (wallpaperGlide P T_step X)`;
2. **Double-Glide Pure Vertical Translation (Centered & Carrier Coordinates):**
   - `wallpaperGlide P T_step (wallpaperGlide P T_step X) = X + (2 : ℤ) • T_step`,
   - `carrierGlide P T_step (carrierGlide P T_step S_carrier) = S_carrier + (2 : ℤ) • T_step`;
3. **Transverse Off-Seam Sign Reversal & Action on Mixed Seam/Off-Seam States:**
   - `offSeamPart P (wallpaperGlide P T_step X) = -offSeamPart P X`,
   - `wallpaperGlide P T_step (genJ P B_im (star B_im) + genPhi P A (star A)) =`
     `genJ P B_im (star B_im) - genPhi P A (star A) + T_step`. -/
theorem archetype_A102_carrier_glide_wallpaper_glide_intertwining_and_double_glide_translation
    {T_step : B} (hSeamT : kreinReflect P T_step = T_step)
    (S_carrier X A B_im : B) :
    (centeredZetaChart P (carrierGlide P T_step S_carrier) =
       wallpaperGlide P T_step (centeredZetaChart P S_carrier) ∧
     carrierGlide P T_step (carrierFromCentered P X) =
       carrierFromCentered P (wallpaperGlide P T_step X)) ∧
    (wallpaperGlide P T_step (wallpaperGlide P T_step X) =
       X + (2 : ℤ) • T_step ∧
     carrierGlide P T_step (carrierGlide P T_step S_carrier) =
       S_carrier + (2 : ℤ) • T_step) ∧
    (offSeamPart P (wallpaperGlide P T_step X) = -offSeamPart P X ∧
     wallpaperGlide P T_step (genJ P B_im (star B_im) + genPhi P A (star A)) =
       genJ P B_im (star B_im) - genPhi P A (star A) + T_step) := by
  have hInv : ∀ U : B, kreinReflect P (kreinReflect P U) = U :=
    fun U => (archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection
      hP hPsym 0 U 0).2.1
  have hKreinAdd : ∀ U V : B, kreinReflect P (U + V) = kreinReflect P U + kreinReflect P V := by
    intro U V; unfold kreinReflect; rw [star_add, mul_add, add_mul]
  have hC1 : centeredZetaChart P (carrierGlide P T_step S_carrier) =
      wallpaperGlide P T_step (centeredZetaChart P S_carrier) := by
    unfold centeredZetaChart carrierGlide carrierFromCentered; abel
  have hC2 : carrierGlide P T_step (carrierFromCentered P X) =
      carrierFromCentered P (wallpaperGlide P T_step X) := by
    unfold carrierGlide centeredZetaChart carrierFromCentered
    rw [add_sub_cancel_left]
  have hDbl : ∀ U : B,
      wallpaperGlide P T_step (wallpaperGlide P T_step U) = U + (2 : ℤ) • T_step := by
    intro U
    unfold wallpaperGlide
    rw [hKreinAdd, hInv U, hSeamT, add_assoc, ← two_zsmul]
  have hDblCarrier :
      carrierGlide P T_step (carrierGlide P T_step S_carrier) =
        S_carrier + (2 : ℤ) • T_step := by
    unfold carrierGlide
    have hInner : centeredZetaChart P (carrierFromCentered P
        (wallpaperGlide P T_step (centeredZetaChart P S_carrier))) =
        wallpaperGlide P T_step (centeredZetaChart P S_carrier) := by
      unfold centeredZetaChart carrierFromCentered; abel
    rw [hInner, hDbl (centeredZetaChart P S_carrier)]
    unfold carrierFromCentered centeredZetaChart
    abel
  have hOffGlide : offSeamPart P (wallpaperGlide P T_step X) = -offSeamPart P X := by
    unfold offSeamPart wallpaperGlide
    rw [hKreinAdd, hInv X, hSeamT]
    abel
  rcases archetype_A101_all_mode_critical_seam_fixed_locus_vs_off_seam_chiral_deviation
      hP hPsym X A B_im 0 with
    ⟨_, ⟨hKreinJ, _, hKreinPhi, _, _, _⟩, _⟩
  have hMixed :
      wallpaperGlide P T_step (genJ P B_im (star B_im) + genPhi P A (star A)) =
        genJ P B_im (star B_im) - genPhi P A (star A) + T_step := by
    unfold wallpaperGlide
    rw [hKreinAdd, hKreinJ, hKreinPhi, sub_eq_add_neg]
  exact ⟨⟨hC1, hC2⟩, ⟨hDbl X, hDblCarrier⟩, ⟨hOffGlide, hMixed⟩⟩

/-- **Archetype `A₁₀₃` (`K₄`, `archetype_A103_all_mode_xi_euler_bergman_evaluation_and_zero_reflection_transport`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, elements `S_carrier X A C : B`, and mode index `r : ℕ`:
1. **Euler–Bergman & All-Mode Virasoro Evaluation of `xiCenteredOp`:**
   - `xiCenteredOp (genPhi P A C) = 1 - genV P A C`,
   - `xiCenteredOp (genJ P A C) = 1 + genV P A C`,
   - `xiCenteredOp (genPhi P A C * opPow r (genV P A C)) = 1 - virasoroModeEven (r + r) P A C`,
   - `xiCenteredOp (genJ P A C * opPow r (genV P A C)) = 1 + virasoroModeEven (r + r) P A C`;
2. **Multiplicative Reflection Equivariance of `xiCenteredOp`:**
   - `zornReflect P (xiCenteredOp X) = xiCenteredOp (zornReflect P X)`,
   - `kreinReflect P (xiCenteredOp X) = xiCenteredOp (kreinReflect P X)`;
3. **Exact `Ξ` Zero-Reflection Transport in Centered and Carrier Coordinates:**
   - `xiCenteredOp X = 0 → xiCenteredOp (zornReflect P X) = 0`,
   - `xiCenteredOp (star X) = 0 → xiCenteredOp (kreinReflect P X) = 0`,
   - `xiCarrierOp P S_carrier = 0 →`
     `xiCarrierOp P (carrierFromCentered P (zornReflect P (centeredZetaChart P S_carrier))) = 0`,
   - `xiCenteredOp (star (centeredZetaChart P S_carrier)) = 0 →`
     `xiCarrierOp P (carrierKreinReflect P S_carrier) = 0`. -/
theorem archetype_A103_all_mode_xi_euler_bergman_evaluation_and_zero_reflection_transport
    (S_carrier X A C : B) (r : ℕ) :
    (xiCenteredOp (genPhi P A C) = 1 - genV P A C ∧
     xiCenteredOp (genJ P A C) = 1 + genV P A C ∧
     xiCenteredOp (genPhi P A C * opPow r (genV P A C)) =
       1 - virasoroModeEven (r + r) P A C ∧
     xiCenteredOp (genJ P A C * opPow r (genV P A C)) =
       1 + virasoroModeEven (r + r) P A C) ∧
    (zornReflect P (xiCenteredOp X) = xiCenteredOp (zornReflect P X) ∧
     kreinReflect P (xiCenteredOp X) = xiCenteredOp (kreinReflect P X)) ∧
    ((xiCenteredOp X = 0 → xiCenteredOp (zornReflect P X) = 0) ∧
     (xiCenteredOp (star X) = 0 → xiCenteredOp (kreinReflect P X) = 0) ∧
     (xiCarrierOp P S_carrier = 0 →
       xiCarrierOp P (carrierFromCentered P (zornReflect P (centeredZetaChart P S_carrier))) = 0) ∧
     (xiCenteredOp (star (centeredZetaChart P S_carrier)) = 0 →
       xiCarrierOp P (carrierKreinReflect P S_carrier) = 0)) := by
  have hXiPhi0 : xiCenteredOp (genPhi P A C) = 1 - genV P A C := by
    unfold xiCenteredOp; peirce_nf hP
  have hXiJ0 : xiCenteredOp (genJ P A C) = 1 + genV P A C := by
    unfold xiCenteredOp; peirce_nf hP
  have hVNp : opPow r (genV P A C) * conePlus P A = conePlus P A * opPow r (genV P A C) :=
    (opPow_genV_comm_invS_and_cones hP A C r).2.1.symm
  have hPhi_eq : genPhi P A C * opPow r (genV P A C) =
      heisenbergSourceMode r P A C + heisenbergSinkMode r P A C := by
    change (conePlus P A + coneMinus P C) * opPow r (genV P A C) =
      opPow r (genV P A C) * conePlus P A + coneMinus P C * opPow r (genV P A C)
    rw [add_mul, ← hVNp]
  have hJ_eq : genJ P A C * opPow r (genV P A C) =
      heisenbergSourceMode r P A C - heisenbergSinkMode r P A C := by
    change (conePlus P A - coneMinus P C) * opPow r (genV P A C) =
      opPow r (genV P A C) * conePlus P A - coneMinus P C * opPow r (genV P A C)
    rw [sub_mul, ← hVNp]
  rcases archetype_A91_source_sink_car_ccr_mode_duality_and_hopf_norm_splitting hP A C r r with
    ⟨_, _, ⟨hSumSq, hDiffSq, _⟩⟩
  have hXiPhir : xiCenteredOp (genPhi P A C * opPow r (genV P A C)) =
      1 - virasoroModeEven (r + r) P A C := by
    unfold xiCenteredOp
    rw [hPhi_eq, hSumSq]
  have hXiJr : xiCenteredOp (genJ P A C * opPow r (genV P A C)) =
      1 + virasoroModeEven (r + r) P A C := by
    unfold xiCenteredOp
    rw [hJ_eq, hDiffSq, sub_neg_eq_add]
  have hSsq : invS P * invS P = 1 := by peirce_nf hP
  have hZornEq : ∀ U : B, zornReflect P (xiCenteredOp U) = xiCenteredOp (zornReflect P U) := by
    intro U
    unfold zornReflect parityConj xiCenteredOp
    rw [mul_sub, sub_mul, mul_one, hSsq]
    congr 1
    calc invS P * (U * U) * invS P
        = (invS P * U * (invS P * invS P)) * U * invS P := by
          rw [hSsq, mul_one]; noncomm_ring
      _ = (invS P * U * invS P) * (invS P * U * invS P) := by noncomm_ring
  have hStarXi : ∀ U : B, star (xiCenteredOp U) = xiCenteredOp (star U) := by
    intro U
    unfold xiCenteredOp
    rw [star_sub, star_one, star_mul]
  have hKreinEq : ∀ U : B,
      kreinReflect P (xiCenteredOp U) = xiCenteredOp (kreinReflect P U) := by
    intro U
    change zornReflect P (star (xiCenteredOp U)) = xiCenteredOp (zornReflect P (star U))
    rw [hStarXi U, hZornEq (star U)]
  have hZeroZorn : xiCenteredOp X = 0 → xiCenteredOp (zornReflect P X) = 0 := by
    intro h0
    rw [← hZornEq X, h0]
    unfold zornReflect parityConj
    rw [mul_zero, zero_mul]
  have hZeroKrein : ∀ U : B, xiCenteredOp (star U) = 0 → xiCenteredOp (kreinReflect P U) = 0 := by
    intro U h0
    have hXi : xiCenteredOp U = 0 := by
      have h := congrArg star h0
      simpa [xiCenteredOp, star_sub, star_one, star_mul] using h
    rw [← hKreinEq U, hXi]
    unfold kreinReflect
    rw [star_zero, mul_zero, zero_mul]
  have hChart1 : ∀ U : B, centeredZetaChart P (carrierFromCentered P U) = U :=
    fun U => (archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection
      hP hPsym 0 U 0).1.1
  have hZeroCarrierZorn :
      xiCarrierOp P S_carrier = 0 →
        xiCarrierOp P (carrierFromCentered P (zornReflect P (centeredZetaChart P S_carrier))) = 0 := by
    intro h0
    unfold xiCarrierOp at *
    rw [hChart1, ← hZornEq (centeredZetaChart P S_carrier), h0]
    unfold zornReflect parityConj
    rw [mul_zero, zero_mul]
  have hZeroCarrierKrein :
      xiCenteredOp (star (centeredZetaChart P S_carrier)) = 0 →
        xiCarrierOp P (carrierKreinReflect P S_carrier) = 0 := by
    intro h0
    unfold xiCarrierOp carrierKreinReflect
    rw [hChart1]
    exact hZeroKrein (centeredZetaChart P S_carrier) h0
  exact ⟨⟨hXiPhi0, hXiJ0, hXiPhir, hXiJr⟩,
         ⟨hZornEq X, hKreinEq X⟩,
         ⟨hZeroZorn, hZeroKrein X, hZeroCarrierZorn, hZeroCarrierKrein⟩⟩

/-- **Archetype `A₁₀₄` (`K₅` & Stage `D₃₂`, `archetype_A104_wallpaper_glide_obstruction_defect_and_same_seed_virasoro_shift`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, elements `X T_step A : B`, and mode indices `r s : ℕ`:
1. **Explicit Single-Glide Obstruction Defect for `xiCenteredOp` (`K₅`):**
   - `xiCenteredOp (wallpaperGlide P T_step X) - kreinReflect P (xiCenteredOp X) =`
     `-anticomm (kreinReflect P X) T_step - T_step * T_step`;
2. **Explicit Double-Glide Obstruction Defect Along Any Critical-Seam Step (`kreinReflect P T_step = T_step`):**
   - `∀ hSeamT : kreinReflect P T_step = T_step,`
     `xiCenteredOp (wallpaperGlide P T_step (wallpaperGlide P T_step X)) - xiCenteredOp X =`
     `-((2 : ℤ) • anticomm X T_step) - (4 : ℤ) • (T_step * T_step)`;
3. **Same-Seed `(Φ_r, J_s)` Chiral Anticommutator Cancellation & Exact Sugawara–Virasoro Glide Shift:**
   Let `Phi_r = genPhi P A (star A) * opPow r (genV P A (star A))` and
   `J_s = genJ P A (star A) * opPow s (genV P A (star A))`:
   - `anticomm Phi_r J_s = 0` and `anticomm (kreinReflect P Phi_r) J_s = 0`,
   - `xiCenteredOp (wallpaperGlide P J_s Phi_r) - kreinReflect P (xiCenteredOp Phi_r) =`
     `virasoroModeEven (s + s) P A (star A)`. -/
theorem archetype_A104_wallpaper_glide_obstruction_defect_and_same_seed_virasoro_shift
    (X T_step A : B) (r s : ℕ) :
    let Phi_r := genPhi P A (star A) * opPow r (genV P A (star A))
    let J_s := genJ P A (star A) * opPow s (genV P A (star A))
    (xiCenteredOp (wallpaperGlide P T_step X) - kreinReflect P (xiCenteredOp X) =
       -anticomm (kreinReflect P X) T_step - T_step * T_step) ∧
    (∀ _hSeamT : kreinReflect P T_step = T_step,
      xiCenteredOp (wallpaperGlide P T_step (wallpaperGlide P T_step X)) - xiCenteredOp X =
        -((2 : ℤ) • anticomm X T_step) - (4 : ℤ) • (T_step * T_step)) ∧
    (anticomm Phi_r J_s = 0 ∧
     anticomm (kreinReflect P Phi_r) J_s = 0 ∧
     xiCenteredOp (wallpaperGlide P J_s Phi_r) - kreinReflect P (xiCenteredOp Phi_r) =
       virasoroModeEven (s + s) P A (star A)) := by
  intro Phi_r J_s
  have hKreinEq : ∀ U : B,
      kreinReflect P (xiCenteredOp U) = xiCenteredOp (kreinReflect P U) :=
    fun U => (archetype_A103_all_mode_xi_euler_bergman_evaluation_and_zero_reflection_transport
      hP hPsym 0 U A A 0).2.1.2
  have hObs1 : ∀ U T : B,
      xiCenteredOp (wallpaperGlide P T U) - kreinReflect P (xiCenteredOp U) =
        -anticomm (kreinReflect P U) T - T * T := by
    intro U T
    rw [hKreinEq U]
    unfold xiCenteredOp wallpaperGlide anticomm
    noncomm_ring
  have hObs2 : ∀ hSeamT : kreinReflect P T_step = T_step,
      xiCenteredOp (wallpaperGlide P T_step (wallpaperGlide P T_step X)) - xiCenteredOp X =
        -((2 : ℤ) • anticomm X T_step) - (4 : ℤ) • (T_step * T_step) := by
    intro hSeamT
    have hDbl := (archetype_A102_carrier_glide_wallpaper_glide_intertwining_and_double_glide_translation
      hP hPsym hSeamT 0 X A A).2.1.1
    rw [hDbl]
    unfold xiCenteredOp anticomm
    noncomm_ring
  have hVJ : opPow r (genV P A (star A)) * genJ P A (star A) =
      genJ P A (star A) * opPow r (genV P A (star A)) := by
    rcases opPow_genV_comm_invS_and_cones hP A (star A) r with ⟨_, hCp, hCm⟩
    unfold genJ
    rw [mul_sub, sub_mul, hCp, hCm]
  have hVPhi : opPow s (genV P A (star A)) * genPhi P A (star A) =
      genPhi P A (star A) * opPow s (genV P A (star A)) := by
    rcases opPow_genV_comm_invS_and_cones hP A (star A) s with ⟨_, hCp, hCm⟩
    unfold genPhi
    rw [mul_add, add_mul, hCp, hCm]
  have hPhiJ0 : genPhi P A (star A) * genJ P A (star A) +
      genJ P A (star A) * genPhi P A (star A) = 0 := by
    peirce_nf hP
  have hAntiPhiJ : anticomm Phi_r J_s = 0 := by
    change (genPhi P A (star A) * opPow r (genV P A (star A))) *
        (genJ P A (star A) * opPow s (genV P A (star A))) +
      (genJ P A (star A) * opPow s (genV P A (star A))) *
        (genPhi P A (star A) * opPow r (genV P A (star A))) = 0
    have h1 : (genPhi P A (star A) * opPow r (genV P A (star A))) *
        (genJ P A (star A) * opPow s (genV P A (star A))) =
        (genPhi P A (star A) * genJ P A (star A)) *
          opPow (r + s) (genV P A (star A)) := by
      calc (genPhi P A (star A) * opPow r (genV P A (star A))) *
              (genJ P A (star A) * opPow s (genV P A (star A)))
          = genPhi P A (star A) * (opPow r (genV P A (star A)) * genJ P A (star A)) *
              opPow s (genV P A (star A)) := by noncomm_ring
        _ = genPhi P A (star A) * (genJ P A (star A) * opPow r (genV P A (star A))) *
              opPow s (genV P A (star A)) := by rw [hVJ]
        _ = (genPhi P A (star A) * genJ P A (star A)) *
              (opPow r (genV P A (star A)) * opPow s (genV P A (star A))) := by noncomm_ring
        _ = (genPhi P A (star A) * genJ P A (star A)) *
              opPow (r + s) (genV P A (star A)) := by rw [← opPow_add]
    have h2 : (genJ P A (star A) * opPow s (genV P A (star A))) *
        (genPhi P A (star A) * opPow r (genV P A (star A))) =
        (genJ P A (star A) * genPhi P A (star A)) *
          opPow (r + s) (genV P A (star A)) := by
      calc (genJ P A (star A) * opPow s (genV P A (star A))) *
              (genPhi P A (star A) * opPow r (genV P A (star A)))
          = genJ P A (star A) * (opPow s (genV P A (star A)) * genPhi P A (star A)) *
              opPow r (genV P A (star A)) := by noncomm_ring
        _ = genJ P A (star A) * (genPhi P A (star A) * opPow s (genV P A (star A))) *
              opPow r (genV P A (star A)) := by rw [hVPhi]
        _ = (genJ P A (star A) * genPhi P A (star A)) *
              (opPow s (genV P A (star A)) * opPow r (genV P A (star A))) := by noncomm_ring
        _ = (genJ P A (star A) * genPhi P A (star A)) *
              opPow (s + r) (genV P A (star A)) := by rw [← opPow_add]
        _ = (genJ P A (star A) * genPhi P A (star A)) *
              opPow (r + s) (genV P A (star A)) := by rw [Nat.add_comm s r]
    rw [h1, h2, ← add_mul, hPhiJ0, zero_mul]
  have hKreinPhir : kreinReflect P Phi_r = -Phi_r :=
    (archetype_A101_all_mode_critical_seam_fixed_locus_vs_off_seam_chiral_deviation
      hP hPsym X A A r).2.2.2.2.2
  have hAntiKrein : anticomm (kreinReflect P Phi_r) J_s = 0 := by
    rw [hKreinPhir]
    have hNeg : anticomm (-Phi_r) J_s = -anticomm Phi_r J_s := by
      unfold anticomm; noncomm_ring
    rw [hNeg, hAntiPhiJ, neg_zero]
  have hJsSq : J_s * J_s = -virasoroModeEven (s + s) P A (star A) := by
    have hVNp_s : opPow s (genV P A (star A)) * conePlus P A =
        conePlus P A * opPow s (genV P A (star A)) :=
      (opPow_genV_comm_invS_and_cones hP A (star A) s).2.1.symm
    have hJ_eq_s : J_s = heisenbergSourceMode s P A (star A) -
        heisenbergSinkMode s P A (star A) := by
      change (conePlus P A - coneMinus P (star A)) * opPow s (genV P A (star A)) =
        opPow s (genV P A (star A)) * conePlus P A -
          coneMinus P (star A) * opPow s (genV P A (star A))
      rw [sub_mul, ← hVNp_s]
    rw [hJ_eq_s]
    exact (archetype_A91_source_sink_car_ccr_mode_duality_and_hopf_norm_splitting
      hP A (star A) s s).2.2.2.1
  have hObsSameSeed :
      xiCenteredOp (wallpaperGlide P J_s Phi_r) - kreinReflect P (xiCenteredOp Phi_r) =
        virasoroModeEven (s + s) P A (star A) := by
    rw [hObs1 Phi_r J_s, hAntiKrein, neg_zero, zero_sub, hJsSq, neg_neg]
  exact ⟨hObs1 X T_step, hObs2, ⟨hAntiPhiJ, hAntiKrein, hObsSameSeed⟩⟩

end Tier6

/-! ### Part 7: Tier 7 Archetypes (`A₁₀₅ → A₁₀₉` / Causal Poset `N₁ → N₅`):
Tomita–KMS Winding Strip & Half-Shift Krein Centering, Nilpotent Cone Exponential & Compactified
Two-Endpoint Möbius Folding, Modular–Krein Klein Four-Group Belt Topology, the `ℤ₄` Helical
Quarter-Twist Operator, and the Compactified "Ring of the Nibelung" -/

section Tier7Defs

variable {B : Type*} [Ring B]

/-- **Discrete `ℤ`-Winding KMS Shift (`kmsWindingShift`):**
Translates a centered operator `X` by `n` winding periods along a critical-seam generator `T_step`. -/
def kmsWindingShift (T_step : B) (n : ℤ) (X : B) : B :=
  X + n • T_step

/-- **Upper-Right Nilpotent Peirce Cone Exponential (`coneExpPlus`):**
`coneExpPlus P A = 1 + conePlus P A`. -/
def coneExpPlus (P A : B) : B :=
  1 + conePlus P A

/-- **Lower-Left Nilpotent Peirce Cone Exponential (`coneExpMinus`):**
`coneExpMinus P C = 1 + coneMinus P C`. -/
def coneExpMinus (P C : B) : B :=
  1 + coneMinus P C

/-- **Non-Commutative `ℤ₄` Helical Quarter-Twist Step (`nibelungHelixStep`):**
`nibelungHelixStep P X = -invS P * kreinReflect P X`
(rotates off-seam `Φ_r` onto critical-seam `J_r` and squares to `zornReflect P`). -/
def nibelungHelixStep [Star B] (P X : B) : B :=
  -invS P * kreinReflect P X

/-- **Compactified 4-Quarter Helical Ring Sum (`nibelungRingSum`):**
Sums an operator `X` over all four quarters of the compactified Nibelung helix. -/
def nibelungRingSum [Star B] (P X : B) : B :=
  X + nibelungHelixStep P X +
    nibelungHelixStep P (nibelungHelixStep P X) +
    nibelungHelixStep P (nibelungHelixStep P (nibelungHelixStep P X))

/-- **Symmetric Quadratic Helical Casimir (`nibelungHelixCasimir`):**
`nibelungHelixCasimir P X = X * X + nibelungHelixStep P X * nibelungHelixStep P X`. -/
def nibelungHelixCasimir [Star B] (P X : B) : B :=
  X * X + nibelungHelixStep P X * nibelungHelixStep P X

/-- **Alternating Krein Helical Energy (`nibelungKreinEnergy`):**
`nibelungKreinEnergy P X = X * X - nibelungHelixStep P X * nibelungHelixStep P X`. -/
def nibelungKreinEnergy [Star B] (P X : B) : B :=
  X * X - nibelungHelixStep P X * nibelungHelixStep P X

end Tier7Defs

section Tier7

variable {B : Type*} [Ring B] [StarRing B] {P : B} (hP : P * P = P) (hPsym : star P = P)
include hP hPsym

/-- **Archetype `A₁₀₅` (`N₁`, `archetype_A105_tomita_kms_winding_strip_and_half_shift_krein_centering`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, critical-seam KMS period `T_step : B` (`hSeamT : kreinReflect P T_step = T_step`),
element `X : B`, and winding numbers `m n : ℤ`:
1. **Half-Shift Critical-Strip Centering Identity (`s = P + X ↔ 2s - 1 = S_P + 2X`):**
   - `(2 : ℤ) • carrierFromCentered P X - 1 = invS P + (2 : ℤ) • X`,
   - `(2 : ℤ) • carrierFromCentered P 0 - 1 = invS P`,
   - `((2 : ℤ) • carrierFromCentered P 0 - 1) * ((2 : ℤ) • carrierFromCentered P 0 - 1) = 1`;
2. **Additive `ℤ`-Winding Group Law & Winding Number Extraction:**
   - `kmsWindingShift T_step 0 X = X`,
   - `kmsWindingShift T_step m (kmsWindingShift T_step n X) = kmsWindingShift T_step (m + n) X`,
   - `kmsWindingShift T_step (-n) (kmsWindingShift T_step n X) = X`,
   - `kmsWindingShift T_step n X - X = n • T_step`;
3. **All-Winding Transverse Off-Seam Invariance & Double-Glide Realization:**
   - `kreinReflect P (kmsWindingShift T_step n X) = kmsWindingShift T_step n (kreinReflect P X)`,
   - `offSeamPart P (kmsWindingShift T_step n X) = offSeamPart P X`,
   - `wallpaperGlide P T_step (wallpaperGlide P T_step X) = kmsWindingShift T_step 2 X`. -/
theorem archetype_A105_tomita_kms_winding_strip_and_half_shift_krein_centering
    {T_step : B} (hSeamT : kreinReflect P T_step = T_step)
    (X : B) (m n : ℤ) :
    ((2 : ℤ) • carrierFromCentered P X - 1 = invS P + (2 : ℤ) • X ∧
     (2 : ℤ) • carrierFromCentered P 0 - 1 = invS P ∧
     ((2 : ℤ) • carrierFromCentered P 0 - 1) *
       ((2 : ℤ) • carrierFromCentered P 0 - 1) = 1) ∧
    (kmsWindingShift T_step 0 X = X ∧
     kmsWindingShift T_step m (kmsWindingShift T_step n X) =
       kmsWindingShift T_step (m + n) X ∧
     kmsWindingShift T_step (-n) (kmsWindingShift T_step n X) = X ∧
     kmsWindingShift T_step n X - X = n • T_step) ∧
    (kreinReflect P (kmsWindingShift T_step n X) =
       kmsWindingShift T_step n (kreinReflect P X) ∧
     offSeamPart P (kmsWindingShift T_step n X) = offSeamPart P X ∧
     wallpaperGlide P T_step (wallpaperGlide P T_step X) =
       kmsWindingShift T_step 2 X) := by
  have hShift1 : (2 : ℤ) • carrierFromCentered P X - 1 = invS P + (2 : ℤ) • X := by
    unfold carrierFromCentered invS
    rw [two_zsmul, two_zsmul]
    abel
  have hShift0 : (2 : ℤ) • carrierFromCentered P 0 - 1 = invS P := by
    unfold carrierFromCentered invS
    rw [two_zsmul]
    abel
  have hShiftSq :
      ((2 : ℤ) • carrierFromCentered P 0 - 1) *
        ((2 : ℤ) • carrierFromCentered P 0 - 1) = 1 := by
    rw [hShift0]
    peirce_nf hP
  have hW0 : kmsWindingShift T_step 0 X = X := by
    unfold kmsWindingShift; rw [zero_smul, add_zero]
  have hWAdd : ∀ a b : ℤ,
      kmsWindingShift T_step a (kmsWindingShift T_step b X) =
        kmsWindingShift T_step (a + b) X := by
    intro a b
    unfold kmsWindingShift
    rw [add_smul]
    abel
  have hWNeg : kmsWindingShift T_step (-n) (kmsWindingShift T_step n X) = X := by
    rw [hWAdd (-n) n, neg_add_cancel, hW0]
  have hWExt : kmsWindingShift T_step n X - X = n • T_step := by
    unfold kmsWindingShift; abel
  have hKreinZsmul : ∀ (k : ℤ) (U : B),
      kreinReflect P (k • U) = k • kreinReflect P U := by
    intro k U
    unfold kreinReflect
    rw [star_zsmul, mul_smul_comm, smul_mul_assoc]
  have hKreinW :
      kreinReflect P (kmsWindingShift T_step n X) =
        kmsWindingShift T_step n (kreinReflect P X) := by
    unfold kmsWindingShift
    have hAdd : ∀ U V : B, kreinReflect P (U + V) = kreinReflect P U + kreinReflect P V := by
      intro U V; unfold kreinReflect; rw [star_add, mul_add, add_mul]
    rw [hAdd, hKreinZsmul, hSeamT]
  have hOffW : offSeamPart P (kmsWindingShift T_step n X) = offSeamPart P X := by
    unfold offSeamPart
    rw [hKreinW]
    unfold kmsWindingShift
    abel
  have hDbl :
      wallpaperGlide P T_step (wallpaperGlide P T_step X) =
        kmsWindingShift T_step 2 X :=
    (archetype_A102_carrier_glide_wallpaper_glide_intertwining_and_double_glide_translation
      hP hPsym hSeamT 0 X 0 0).2.1.1
  exact ⟨⟨hShift1, hShift0, hShiftSq⟩,
         ⟨hW0, hWAdd m n, hWNeg, hWExt⟩,
         ⟨hKreinW, hOffW, hDbl⟩⟩

/-- **Archetype `A₁₀₆` (`N₂`, `archetype_A106_nilpotent_cone_exponential_and_moebius_idempotency_defect_folding`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, elements `X A₁ A₂ A C : B`, and mode index `r : ℕ`:
1. **Nilpotent Peirce Cone Exponential Group Law & Star/Krein Sheet Duality:**
   - `coneExpPlus P 0 = 1` and `coneExpMinus P 0 = 1`,
   - `coneExpPlus P A₁ * coneExpPlus P A₂ = coneExpPlus P (A₁ + A₂)`,
   - `coneExpMinus P A₁ * coneExpMinus P A₂ = coneExpMinus P (A₁ + A₂)`,
   - `coneExpPlus P A * coneExpPlus P (-A) = 1` and `coneExpMinus P C * coneExpMinus P (-C) = 1`,
   - `star (coneExpPlus P A) = coneExpMinus P (star A)` and
     `kreinReflect P (coneExpPlus P A) = coneExpMinus P (-star A)`;
2. **Compactified Two-Endpoint Möbius Folding via `idempotencyDefect` (`δ(X) = X² - X`):**
   - `idempotencyDefect (0 : B) = 0` and `idempotencyDefect (1 : B) = 0`
     (glues the two boundary endpoints `0` and `1` to the same pinched origin `0`),
   - `idempotencyDefect P = 0` and `idempotencyDefect (1 - P) = 0`,
   - `idempotencyDefect (1 - X) = idempotencyDefect X`
     (folds `1 - X` back onto `X` with zero commutative assumptions),
   - `idempotencyDefect (P + genPhi P A C * opPow r (genV P A C)) +`
     `  idempotencyDefect ((1 - P) - genPhi P A C * opPow r (genV P A C)) =`
     `(2 : ℤ) • virasoroModeEven (r + r) P A C`. -/
theorem archetype_A106_nilpotent_cone_exponential_and_moebius_idempotency_defect_folding
    (X A₁ A₂ A C : B) (r : ℕ) :
    (coneExpPlus P 0 = 1 ∧
     coneExpMinus P 0 = 1 ∧
     coneExpPlus P A₁ * coneExpPlus P A₂ = coneExpPlus P (A₁ + A₂) ∧
     coneExpMinus P A₁ * coneExpMinus P A₂ = coneExpMinus P (A₁ + A₂) ∧
     coneExpPlus P A * coneExpPlus P (-A) = 1 ∧
     coneExpMinus P C * coneExpMinus P (-C) = 1 ∧
     star (coneExpPlus P A) = coneExpMinus P (star A) ∧
     kreinReflect P (coneExpPlus P A) = coneExpMinus P (-star A)) ∧
    (idempotencyDefect (0 : B) = 0 ∧
     idempotencyDefect (1 : B) = 0 ∧
     idempotencyDefect P = 0 ∧
     idempotencyDefect (1 - P) = 0 ∧
     idempotencyDefect (1 - X) = idempotencyDefect X ∧
     idempotencyDefect (P + genPhi P A C * opPow r (genV P A C)) +
         idempotencyDefect ((1 - P) - genPhi P A C * opPow r (genV P A C)) =
       (2 : ℤ) • virasoroModeEven (r + r) P A C) := by
  have hE1 : coneExpPlus P 0 = 1 := by unfold coneExpPlus; peirce_nf hP
  have hE2 : coneExpMinus P 0 = 1 := by unfold coneExpMinus; peirce_nf hP
  have hE3 : coneExpPlus P A₁ * coneExpPlus P A₂ = coneExpPlus P (A₁ + A₂) := by
    unfold coneExpPlus; peirce_nf hP
  have hE4 : coneExpMinus P A₁ * coneExpMinus P A₂ = coneExpMinus P (A₁ + A₂) := by
    unfold coneExpMinus; peirce_nf hP
  have hE5 : coneExpPlus P A * coneExpPlus P (-A) = 1 := by
    unfold coneExpPlus; peirce_nf hP
  have hE6 : coneExpMinus P C * coneExpMinus P (-C) = 1 := by
    unfold coneExpMinus; peirce_nf hP
  have hStarCone : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hE7 : star (coneExpPlus P A) = coneExpMinus P (star A) := by
    unfold coneExpPlus coneExpMinus
    rw [star_add, star_one, hStarCone]
  have hE8 : kreinReflect P (coneExpPlus P A) = coneExpMinus P (-star A) := by
    unfold kreinReflect
    rw [hE7]
    unfold coneExpMinus
    peirce_nf hP
  have hD0 : idempotencyDefect (0 : B) = 0 := by unfold idempotencyDefect; noncomm_ring
  have hD1 : idempotencyDefect (1 : B) = 0 := by unfold idempotencyDefect; noncomm_ring
  have hDP : idempotencyDefect P = 0 := by unfold idempotencyDefect; peirce_nf hP
  have hDComp : idempotencyDefect (1 - P) = 0 := by unfold idempotencyDefect; peirce_nf hP
  have hDFold : idempotencyDefect (1 - X) = idempotencyDefect X := by
    unfold idempotencyDefect; noncomm_ring
  rcases archetype_A89_peirce_bdg_square_commutator_anomaly_and_grading_symmetrization
      hP A C r with
    ⟨_, ⟨_, _, _, _, hSymComp⟩⟩
  have hDSym :
      idempotencyDefect (P + genPhi P A C * opPow r (genV P A C)) +
          idempotencyDefect ((1 - P) - genPhi P A C * opPow r (genV P A C)) =
        (2 : ℤ) • virasoroModeEven (r + r) P A C := by
    let Phi_r := genPhi P A C * opPow r (genV P A C)
    change idempotencyDefect (P + Phi_r) + idempotencyDefect ((1 - P) - Phi_r) =
      (2 : ℤ) • virasoroModeEven (r + r) P A C
    have h1 : idempotencyDefect (P + Phi_r) + idempotencyDefect ((1 - P) - Phi_r) =
        ((P + Phi_r) * (P + Phi_r) + ((1 - P) - Phi_r) * ((1 - P) - Phi_r)) - 1 := by
      unfold idempotencyDefect; noncomm_ring
    rw [h1, hSymComp]
    abel
  exact ⟨⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7, hE8⟩,
         ⟨hD0, hD1, hDP, hDComp, hDFold, hDSym⟩⟩

/-- **Archetype `A₁₀₇` (`N₃`, `archetype_A107_modular_krein_klein_four_group_and_folded_ring_equivariance`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, and element `X : B`:
1. **Closed Multiplication Table of the Modular–Krein Klein Four-Group `V₄ = {id, zornReflect, kreinReflect, star}`:**
   - `zornReflect P (zornReflect P X) = X`, `kreinReflect P (kreinReflect P X) = X`, `star (star X) = X`,
   - `zornReflect P (star X) = kreinReflect P X` and `star (zornReflect P X) = kreinReflect P X`,
   - `zornReflect P (kreinReflect P X) = star X` and `kreinReflect P (zornReflect P X) = star X`,
   - `kreinReflect P (star X) = zornReflect P X` and `star (kreinReflect P X) = zornReflect P X`;
2. **Simultaneous `V₄`-Equivariance of the Folded Ring Map `idempotencyDefect` and `xiCenteredOp`:**
   - `zornReflect P (idempotencyDefect X) = idempotencyDefect (zornReflect P X)`,
   - `kreinReflect P (idempotencyDefect X) = idempotencyDefect (kreinReflect P X)`,
   - `star (idempotencyDefect X) = idempotencyDefect (star X)`,
   - `star (xiCenteredOp X) = xiCenteredOp (star X)`. -/
theorem archetype_A107_modular_krein_klein_four_group_and_folded_ring_equivariance
    (X : B) :
    (zornReflect P (zornReflect P X) = X ∧
     kreinReflect P (kreinReflect P X) = X ∧
     star (star X) = X ∧
     zornReflect P (star X) = kreinReflect P X ∧
     star (zornReflect P X) = kreinReflect P X ∧
     zornReflect P (kreinReflect P X) = star X ∧
     kreinReflect P (zornReflect P X) = star X ∧
     kreinReflect P (star X) = zornReflect P X ∧
     star (kreinReflect P X) = zornReflect P X) ∧
    (zornReflect P (idempotencyDefect X) = idempotencyDefect (zornReflect P X) ∧
     kreinReflect P (idempotencyDefect X) = idempotencyDefect (kreinReflect P X) ∧
     star (idempotencyDefect X) = idempotencyDefect (star X) ∧
     star (xiCenteredOp X) = xiCenteredOp (star X)) := by
  have hZornInv : ∀ U : B, zornReflect P (zornReflect P U) = U :=
    fun U => (archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection
      hP hPsym 0 U 0).2.2.1
  have hKreinInv : kreinReflect P (kreinReflect P X) = X :=
    (archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection
      hP hPsym 0 X 0).2.1
  have hFact1 : ∀ U : B, zornReflect P (star U) = kreinReflect P U := fun _ => rfl
  have hFact2 : ∀ U : B, star (zornReflect P U) = kreinReflect P U :=
    fun U => ((archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection
      hP hPsym 0 U 0).2.2.2.2.1).symm
  have hZK : zornReflect P (kreinReflect P X) = star X := by
    rw [← hFact1 X, hZornInv (star X)]
  have hKZ : kreinReflect P (zornReflect P X) = star X := by
    rw [← hFact2 (zornReflect P X), hZornInv X]
  have hKS : kreinReflect P (star X) = zornReflect P X := by
    rw [← hFact1 (star X), star_star]
  have hSK : star (kreinReflect P X) = zornReflect P X := by
    rw [← hFact2 X, star_star]
  have hSsq : invS P * invS P = 1 := by peirce_nf hP
  have hZornDef : ∀ U : B,
      zornReflect P (idempotencyDefect U) = idempotencyDefect (zornReflect P U) := by
    intro U
    unfold zornReflect parityConj idempotencyDefect
    rw [mul_sub, sub_mul]
    congr 1
    calc invS P * (U * U) * invS P
        = (invS P * U * (invS P * invS P)) * U * invS P := by
          rw [hSsq, mul_one]; noncomm_ring
      _ = (invS P * U * invS P) * (invS P * U * invS P) := by noncomm_ring
  have hStarDef : ∀ U : B, star (idempotencyDefect U) = idempotencyDefect (star U) := by
    intro U
    unfold idempotencyDefect
    rw [star_sub, star_mul]
  have hKreinDef : kreinReflect P (idempotencyDefect X) = idempotencyDefect (kreinReflect P X) := by
    rw [← hFact1 (idempotencyDefect X), hStarDef X, hZornDef (star X), hFact1 X]
  have hStarXi : star (xiCenteredOp X) = xiCenteredOp (star X) := by
    unfold xiCenteredOp
    rw [star_sub, star_one, star_mul]
  exact ⟨⟨hZornInv X, hKreinInv, star_star X, rfl, hFact2 X, hZK, hKZ, hKS, hSK⟩,
         ⟨hZornDef X, hKreinDef, hStarDef X, hStarXi⟩⟩

/-- **Archetype `A₁₀₈` (`N₄`, `archetype_A108_nibelung_helical_quarter_twist_z4_action_and_all_mode_cycle`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, elements `X A : B`, and mode index `r : ℕ`, let
`Phi_r = genPhi P A (star A) * opPow r (genV P A (star A))`,
`J_r = genJ P A (star A) * opPow r (genV P A (star A))`,
`L_p = virasoroModeEven r P A (star A)`, and
`L_m = virasoroModeChiral r P A (star A)`:
1. **Exact `ℤ₄` Helical Quarter-Twist Operator `nibelungHelixStep P` on All of `B`:**
   - `nibelungHelixStep P X = -(star X) * invS P`,
   - `nibelungHelixStep P (nibelungHelixStep P X) = zornReflect P X`
     (2 quarter-twists = Zorn parity reflection `S_P X S_P`),
   - `nibelungHelixStep P (nibelungHelixStep P (nibelungHelixStep P X)) = -kreinReflect P X * invS P`,
   - `nibelungHelixStep P (nibelungHelixStep P (nibelungHelixStep P (nibelungHelixStep P X))) = X`
     (4 quarter-twists = identity on all of `B`, closing the 4-twist helix into a ring);
2. **All-Mode 4-Quarter Helical Cycle on `(Φ_r, J_r)` & 2-Step Swap on `(L_r^+, L_r^-)`:**
   - `nibelungHelixStep P Phi_r = J_r`,
   - `nibelungHelixStep P J_r = -Phi_r`,
   - `nibelungHelixStep P (-Phi_r) = -J_r`,
   - `nibelungHelixStep P (-J_r) = Phi_r`,
   - `nibelungHelixStep P L_p = -L_m` and `nibelungHelixStep P L_m = -L_p`. -/
theorem archetype_A108_nibelung_helical_quarter_twist_z4_action_and_all_mode_cycle
    (X A : B) (r : ℕ) :
    let Phi_r := genPhi P A (star A) * opPow r (genV P A (star A))
    let J_r := genJ P A (star A) * opPow r (genV P A (star A))
    let L_p := virasoroModeEven r P A (star A)
    let L_m := virasoroModeChiral r P A (star A)
    (nibelungHelixStep P X = -(star X) * invS P ∧
     nibelungHelixStep P (nibelungHelixStep P X) = zornReflect P X ∧
     nibelungHelixStep P (nibelungHelixStep P (nibelungHelixStep P X)) =
       -kreinReflect P X * invS P ∧
     nibelungHelixStep P (nibelungHelixStep P
       (nibelungHelixStep P (nibelungHelixStep P X))) = X) ∧
    (nibelungHelixStep P Phi_r = J_r ∧
     nibelungHelixStep P J_r = -Phi_r ∧
     nibelungHelixStep P (-Phi_r) = -J_r ∧
     nibelungHelixStep P (-J_r) = Phi_r ∧
     nibelungHelixStep P L_p = -L_m ∧
     nibelungHelixStep P L_m = -L_p) := by
  intro Phi_r J_r L_p L_m
  have hSsq : invS P * invS P = 1 := by peirce_nf hP
  have hStarS : star (invS P) = invS P := by
    unfold invS; rw [star_sub, star_sub, star_one, hPsym]
  have hCompact : ∀ U : B, nibelungHelixStep P U = -(star U) * invS P := by
    intro U
    unfold nibelungHelixStep kreinReflect
    calc -invS P * (invS P * star U * invS P)
        = -((invS P * invS P) * star U * invS P) := by noncomm_ring
      _ = -(star U) * invS P := by rw [hSsq, one_mul, neg_mul]
  have hStep2 : ∀ U : B,
      nibelungHelixStep P (nibelungHelixStep P U) = zornReflect P U := by
    intro U
    rw [hCompact (nibelungHelixStep P U), hCompact U]
    rw [star_mul, star_neg, star_star, hStarS, mul_neg, neg_neg]
    rfl
  have hStep3 :
      nibelungHelixStep P (nibelungHelixStep P (nibelungHelixStep P X)) =
        -kreinReflect P X * invS P := by
    rw [hStep2 X, hCompact (zornReflect P X)]
    have hStarZ : star (zornReflect P X) = kreinReflect P X :=
      (archetype_A107_modular_krein_klein_four_group_and_folded_ring_equivariance
        hP hPsym X).1.2.2.2.2.1
    rw [hStarZ]
  have hStep4 :
      nibelungHelixStep P (nibelungHelixStep P
        (nibelungHelixStep P (nibelungHelixStep P X))) = X := by
    rw [hStep2 (nibelungHelixStep P (nibelungHelixStep P X)), hStep2 X]
    exact (archetype_A107_modular_krein_klein_four_group_and_folded_ring_equivariance
      hP hPsym X).1.1
  rcases archetype_A101_all_mode_critical_seam_fixed_locus_vs_off_seam_chiral_deviation
      hP hPsym X A A r with
    ⟨_, _, ⟨hKreinLp, hKreinLm, hKreinJr, hKreinPhir⟩⟩
  have hSPhi0 : invS P * genPhi P A (star A) = genJ P A (star A) := by peirce_nf hP
  have hSJ0 : invS P * genJ P A (star A) = genPhi P A (star A) := by peirce_nf hP
  have hHPhi : nibelungHelixStep P Phi_r = J_r := by
    unfold nibelungHelixStep
    rw [hKreinPhir, mul_neg, neg_mul, neg_neg]
    change invS P * (genPhi P A (star A) * opPow r (genV P A (star A))) =
      genJ P A (star A) * opPow r (genV P A (star A))
    rw [← mul_assoc, hSPhi0]
  have hHJ : nibelungHelixStep P J_r = -Phi_r := by
    unfold nibelungHelixStep
    rw [hKreinJr, neg_mul]
    congr 1
    change invS P * (genJ P A (star A) * opPow r (genV P A (star A))) =
      genPhi P A (star A) * opPow r (genV P A (star A))
    rw [← mul_assoc, hSJ0]
  have hHNeg : ∀ U : B, nibelungHelixStep P (-U) = -nibelungHelixStep P U := by
    intro U
    rw [hCompact (-U), hCompact U, star_neg, neg_neg, neg_mul, neg_neg]
  have hHNegPhi : nibelungHelixStep P (-Phi_r) = -J_r := by
    rw [hHNeg Phi_r, hHPhi]
  have hHNegJ : nibelungHelixStep P (-J_r) = Phi_r := by
    rw [hHNeg J_r, hHJ, neg_neg]
  have hSV0 : invS P * genV P A (star A) = genSig P A (star A) := by peirce_nf hP
  have hSSig0 : invS P * genSig P A (star A) = genV P A (star A) := by peirce_nf hP
  have hSOpPow : invS P * opPow r (genV P A (star A)) =
      opPow r (genV P A (star A)) * invS P :=
    (opPow_genV_comm_invS_and_cones hP A (star A) r).1
  have hHLp : nibelungHelixStep P L_p = -L_m := by
    unfold nibelungHelixStep
    rw [hKreinLp, neg_mul]
    congr 1
    change invS P * (opPow r (genV P A (star A)) * genV P A (star A)) =
      opPow r (genV P A (star A)) * genSig P A (star A)
    calc invS P * (opPow r (genV P A (star A)) * genV P A (star A))
        = (invS P * opPow r (genV P A (star A))) * genV P A (star A) := by noncomm_ring
      _ = opPow r (genV P A (star A)) * (invS P * genV P A (star A)) := by
          rw [hSOpPow, mul_assoc]
      _ = opPow r (genV P A (star A)) * genSig P A (star A) := by rw [hSV0]
  have hHLm : nibelungHelixStep P L_m = -L_p := by
    unfold nibelungHelixStep
    rw [hKreinLm, neg_mul]
    congr 1
    change invS P * (opPow r (genV P A (star A)) * genSig P A (star A)) =
      opPow r (genV P A (star A)) * genV P A (star A)
    calc invS P * (opPow r (genV P A (star A)) * genSig P A (star A))
        = (invS P * opPow r (genV P A (star A))) * genSig P A (star A) := by noncomm_ring
      _ = opPow r (genV P A (star A)) * (invS P * genSig P A (star A)) := by
          rw [hSOpPow, mul_assoc]
      _ = opPow r (genV P A (star A)) * genV P A (star A) := by rw [hSSig0]
  exact ⟨⟨hCompact X, hStep2 X, hStep3, hStep4⟩,
         ⟨hHPhi, hHJ, hHNegPhi, hHNegJ, hHLp, hHLm⟩⟩

/-- **Archetype `A₁₀₉` (`N₅`, `archetype_A109_compactified_nibelung_ring_sum_conformal_casimir_and_krein_energy`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, elements `X A : B`, and mode index `r : ℕ`, let
`Phi_r = genPhi P A (star A) * opPow r (genV P A (star A))`,
`J_r = genJ P A (star A) * opPow r (genV P A (star A))`,
`L_p = virasoroModeEven r P A (star A)`, and
`L_m = virasoroModeChiral r P A (star A)`:
1. **Compactified 4-Quarter Nibelung Ring Sum Invariance & Closed-Loop Mode Evaluation:**
   - `nibelungHelixStep P (nibelungRingSum P X) = nibelungRingSum P X`,
   - `zornReflect P (nibelungRingSum P X) = nibelungRingSum P X`,
   - `nibelungRingSum P Phi_r = 0` and `nibelungRingSum P J_r = 0`
     (zero net odd boundary charge around the compactified 4-quarter ring),
   - `nibelungRingSum P L_p = (2 : ℤ) • (L_p - L_m)` and
     `nibelungRingSum P L_m = (2 : ℤ) • (L_m - L_p)`;
2. **All-Mode Conformal Harmonic Balance, Symplectic Krein Helical Energy & Quarter-Turn `Ξ`-Average:**
   - `nibelungHelixCasimir P Phi_r = 0` and `nibelungHelixCasimir P J_r = 0`
     (`Φ_r² + J_r² = 0`),
   - `nibelungKreinEnergy P Phi_r = (2 : ℤ) • virasoroModeEven (r + r) P A (star A)`,
   - `nibelungKreinEnergy P J_r = -((2 : ℤ) • virasoroModeEven (r + r) P A (star A))`,
   - `xiCenteredOp Phi_r + xiCenteredOp (nibelungHelixStep P Phi_r) = (2 : ℤ) • (1 : B)`,
   - `xiCenteredOp (nibelungHelixStep P Phi_r) - xiCenteredOp Phi_r =`
     `(2 : ℤ) • virasoroModeEven (r + r) P A (star A)`. -/
theorem archetype_A109_compactified_nibelung_ring_sum_conformal_casimir_and_krein_energy
    (X A : B) (r : ℕ) :
    let Phi_r := genPhi P A (star A) * opPow r (genV P A (star A))
    let J_r := genJ P A (star A) * opPow r (genV P A (star A))
    let L_p := virasoroModeEven r P A (star A)
    let L_m := virasoroModeChiral r P A (star A)
    (nibelungHelixStep P (nibelungRingSum P X) = nibelungRingSum P X ∧
     zornReflect P (nibelungRingSum P X) = nibelungRingSum P X ∧
     nibelungRingSum P Phi_r = 0 ∧
     nibelungRingSum P J_r = 0 ∧
     nibelungRingSum P L_p = (2 : ℤ) • (L_p - L_m) ∧
     nibelungRingSum P L_m = (2 : ℤ) • (L_m - L_p)) ∧
    (nibelungHelixCasimir P Phi_r = 0 ∧
     nibelungHelixCasimir P J_r = 0 ∧
     nibelungKreinEnergy P Phi_r =
       (2 : ℤ) • virasoroModeEven (r + r) P A (star A) ∧
     nibelungKreinEnergy P J_r =
       -((2 : ℤ) • virasoroModeEven (r + r) P A (star A)) ∧
     xiCenteredOp Phi_r + xiCenteredOp (nibelungHelixStep P Phi_r) =
       (2 : ℤ) • (1 : B) ∧
     xiCenteredOp (nibelungHelixStep P Phi_r) - xiCenteredOp Phi_r =
       (2 : ℤ) • virasoroModeEven (r + r) P A (star A)) := by
  intro Phi_r J_r L_p L_m
  rcases archetype_A108_nibelung_helical_quarter_twist_z4_action_and_all_mode_cycle
      hP hPsym X A r with
    ⟨⟨_, hStep2X, _, hStep4X⟩, ⟨hHPhi, hHJ, hHNegPhi, hHNegJ, hHLp, hHLm⟩⟩
  have hHAdd : ∀ U V : B,
      nibelungHelixStep P (U + V) = nibelungHelixStep P U + nibelungHelixStep P V := by
    intro U V
    unfold nibelungHelixStep kreinReflect
    rw [star_add, mul_add, add_mul, mul_add]
  have hHNeg : ∀ U : B, nibelungHelixStep P (-U) = -nibelungHelixStep P U := by
    intro U
    have hC1 := (archetype_A108_nibelung_helical_quarter_twist_z4_action_and_all_mode_cycle
      hP hPsym (-U) A r).1.1
    have hC2 := (archetype_A108_nibelung_helical_quarter_twist_z4_action_and_all_mode_cycle
      hP hPsym U A r).1.1
    rw [hC1, hC2, star_neg, neg_neg, neg_mul, neg_neg]
  have hRingInv : nibelungHelixStep P (nibelungRingSum P X) = nibelungRingSum P X := by
    unfold nibelungRingSum
    rw [hHAdd, hHAdd, hHAdd, hStep4X]
    abel
  have hRingZorn : zornReflect P (nibelungRingSum P X) = nibelungRingSum P X := by
    have hStep2Ring := (archetype_A108_nibelung_helical_quarter_twist_z4_action_and_all_mode_cycle
      hP hPsym (nibelungRingSum P X) A r).1.2.1
    rw [← hStep2Ring, hRingInv, hRingInv]
  have hRingPhi : nibelungRingSum P Phi_r = 0 := by
    unfold nibelungRingSum
    rw [hHPhi, hHJ, hHNegPhi]
    abel
  have hRingJ : nibelungRingSum P J_r = 0 := by
    unfold nibelungRingSum
    rw [hHJ, hHNegPhi, hHNegJ]
    abel
  have hRingLp : nibelungRingSum P L_p = (2 : ℤ) • (L_p - L_m) := by
    unfold nibelungRingSum
    rw [hHLp, hHNeg L_m, hHLm, neg_neg, hHLp, two_zsmul]
    abel
  have hRingLm : nibelungRingSum P L_m = (2 : ℤ) • (L_m - L_p) := by
    unfold nibelungRingSum
    rw [hHLm, hHNeg L_p, hHLp, neg_neg, hHLm, two_zsmul]
    abel
  rcases archetype_A103_all_mode_xi_euler_bergman_evaluation_and_zero_reflection_transport
      hP hPsym 0 X A (star A) r with
    ⟨⟨_, _, hXiPhir, hXiJr⟩, _, _⟩
  have hPhirSq : Phi_r * Phi_r = virasoroModeEven (r + r) P A (star A) := by
    have h := congrArg (fun Y => 1 - Y) hXiPhir
    dsimp [xiCenteredOp] at h
    calc Phi_r * Phi_r = 1 - (1 - Phi_r * Phi_r) := by abel
      _ = 1 - (1 - virasoroModeEven (r + r) P A (star A)) := by rw [h]
      _ = virasoroModeEven (r + r) P A (star A) := by abel
  have hJrSq : J_r * J_r = -virasoroModeEven (r + r) P A (star A) := by
    have h := congrArg (fun Y => Y - 1) hXiJr
    dsimp [xiCenteredOp] at h
    calc J_r * J_r = -((1 - J_r * J_r) - 1) := by abel
      _ = -((1 + virasoroModeEven (r + r) P A (star A)) - 1) := by rw [h]
      _ = -virasoroModeEven (r + r) P A (star A) := by abel
  have hCasPhi : nibelungHelixCasimir P Phi_r = 0 := by
    unfold nibelungHelixCasimir
    rw [hHPhi, hPhirSq, hJrSq, add_neg_cancel]
  have hCasJ : nibelungHelixCasimir P J_r = 0 := by
    unfold nibelungHelixCasimir
    rw [hHJ, neg_mul_neg, hJrSq, hPhirSq, neg_add_cancel]
  have hEnPhi : nibelungKreinEnergy P Phi_r =
      (2 : ℤ) • virasoroModeEven (r + r) P A (star A) := by
    unfold nibelungKreinEnergy
    rw [hHPhi, hPhirSq, hJrSq, sub_neg_eq_add, ← two_zsmul]
  have hEnJ : nibelungKreinEnergy P J_r =
      -((2 : ℤ) • virasoroModeEven (r + r) P A (star A)) := by
    unfold nibelungKreinEnergy
    rw [hHJ, neg_mul_neg, hJrSq, hPhirSq, two_zsmul]
    abel
  have hXiSum :
      xiCenteredOp Phi_r + xiCenteredOp (nibelungHelixStep P Phi_r) =
        (2 : ℤ) • (1 : B) := by
    rw [hHPhi]
    change xiCenteredOp Phi_r + xiCenteredOp J_r = (2 : ℤ) • (1 : B)
    rw [hXiPhir, hXiJr, two_zsmul]
    abel
  have hXiDiff :
      xiCenteredOp (nibelungHelixStep P Phi_r) - xiCenteredOp Phi_r =
        (2 : ℤ) • virasoroModeEven (r + r) P A (star A) := by
    rw [hHPhi]
    change xiCenteredOp J_r - xiCenteredOp Phi_r =
      (2 : ℤ) • virasoroModeEven (r + r) P A (star A)
    rw [hXiJr, hXiPhir, two_zsmul]
    abel
  exact ⟨⟨hRingInv, hRingZorn, hRingPhi, hRingJ, hRingLp, hRingLm⟩,
         ⟨hCasPhi, hCasJ, hEnPhi, hEnJ, hXiSum, hXiDiff⟩⟩

end Tier7

/-! ### Part 9: Tier 8 Canonical Synthesis Theorems (`A₁₁₀ → A₁₁₄` / `M₁ → M₅` & Stage `D₃₄`: Non-Commutative KMS-to-Zeta Operator Chart, Period-2 Peirce Edge Winding Monodromy, Logistic Graph Idempotents & Midline Virasoro Defect, and Brillouin–KMS Functional Parity & `Ξ`-Zero Invariance) -/

section Tier8Defs

variable {B : Type*} [Ring B]

/-- Non-commutative KMS-to-Carrier operator chart `K ↦ 1 - K` exchanging the lower KMS
boundary `0` with `1` and the KMS midline `1 - P` with the critical-line idempotent `P`. -/
def kmsToCarrierOp (K : B) : B :=
  1 - K

/-- Inverse Carrier-to-KMS operator chart `S ↦ 1 - S`. -/
def carrierToKmsOp (S : B) : B :=
  1 - S

/-- Non-commutative KMS-to-Centered-Zeta operator chart `K ↦ (1 - P) - K`, sending the
KMS midline idempotent `K_mid = 1 - P` directly to the centered critical-line origin `0`. -/
def kmsToCenteredOp (P K : B) : B :=
  (1 - P) - K

/-- Inverse Centered-Zeta-to-KMS operator chart `X ↦ (1 - P) - X`. -/
def centeredToKmsOp (P X : B) : B :=
  (1 - P) - X

/-- Iterated non-commutative Peirce edge transport across `n ∈ ℕ` oriented KMS boundary
crossings via the involutive Zorn parity automorphism `zornReflect P`. -/
def peirceEdgeWinding (P : B) : ℕ → B → B
  | 0, X => X
  | n + 1, X => zornReflect P (peirceEdgeWinding P n X)

/-- All-mode lower KMS boundary operator `P + Φ_r` at mode `r ∈ ℕ`. -/
def peirceLowerBoundary (r : ℕ) (P A C : B) : B :=
  P + genPhi P A C * opPow r (genV P A C)

/-- All-mode upper KMS boundary operator `P - Φ_r` at mode `r ∈ ℕ`, obtained by transporting
`peirceLowerBoundary` across the KMS edge via `zornReflect P`. -/
def peirceUpperBoundary (r : ℕ) (P A C : B) : B :=
  P - genPhi P A C * opPow r (genV P A C)

/-- Upper-sheet non-commutative logistic graph idempotent
`E_+(-A) · P · E_+(A) = P + P A (1 - P)`. -/
def logisticGraphPlus (P A : B) : B :=
  coneExpPlus P (-A) * P * coneExpPlus P A

/-- Lower-sheet non-commutative logistic graph idempotent
`E_-(-C) · (1 - P) · E_-(C) = (1 - P) + (1 - P) C P`. -/
def logisticGraphMinus (P C : B) : B :=
  coneExpMinus P (-C) * (1 - P) * coneExpMinus P C

/-- Carrier-chart functional reflection `S ↦ 2P - τ_Krein(S)` corresponding to the centered
functional reflection `X ↦ -τ_Krein(X)`. -/
def carrierFunctionalReflect [StarRing B] (P S : B) : B :=
  (2 : ℤ) • P - kreinReflect P S

/-- KMS/Brillouin-chart functional reflection `K ↦ 2(1 - P) - τ_Krein(K)` conjugated from
`carrierFunctionalReflect` via `carrierToKmsOp`. -/
def kmsFunctionalReflect [StarRing B] (P K : B) : B :=
  (2 : ℤ) • (1 - P) - kreinReflect P K

/-- Completed `Ξ`-operator pulled back to the KMS/Brillouin chart `K = (1 - P) - X`. -/
def xiKmsOp (P K : B) : B :=
  xiCenteredOp (kmsToCenteredOp P K)

/-- **Archetype `T₂` (`cayleyStripForward`):** Forward unipotent Bruhat–Cayley strip operator
`W_+ = (1 + N_+)(1 - N_-)`. -/
def cayleyStripForward (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C)

/-- **Archetype `T₂` (`cayleyStripFolded`):** Folded inverse unipotent Bruhat–Cayley strip operator
`W_+⁻¹ = (1 + N_-)(1 - N_+)`. -/
def cayleyStripFolded (P A C : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A)

/-- **Archetype `T₂` (`foldedStripSum`):** Symmetrized Cayley–Möbius folded strip sum
`W_+ + W_+⁻¹ = 2 - V(A, C)`. -/
def foldedStripSum (P A C : B) : B :=
  cayleyStripForward P A C + cayleyStripFolded P A C

/-- **Archetype `T₄` (`helixWindingOp`):** Unipotent helical belt winding operator
`U_w = 1 + w • N_+(A)` for integer winding number `w : ℤ`. -/
def helixWindingOp (w : ℤ) (P A : B) : B :=
  1 + w • conePlus P A

/-- **Archetype `T₄` (`helixWindingOpInv`):** Inverse helical belt winding operator
`U_w⁻¹ = 1 - w • N_+(A)` for integer winding number `w : ℤ`. -/
def helixWindingOpInv (w : ℤ) (P A : B) : B :=
  1 - w • conePlus P A

/-- **Archetype `T₄` (`windingNumberExtractor`):** Non-commutative logarithmic-derivative
winding number extractor `{U⁻¹ [P, U], N_-(C)}`. -/
def windingNumberExtractor (P C U U_inv : B) : B :=
  anticomm (U_inv * comm P U) (coneMinus P C)

/-- **Archetype `T₅` (`nibelungRingOp`):** Compactified toroidal Krein ring operator
`(W_+ - 1)(W_+⁻¹ - 1) = V(A, C) - δ(V(A, C))`. -/
def nibelungRingOp (P A C : B) : B :=
  (cayleyStripForward P A C - 1) * (cayleyStripFolded P A C - 1)

end Tier8Defs

section Tier8

variable {B : Type*} [Ring B] [StarRing B] {P : B} (hP : P * P = P) (hPsym : star P = P)
include hP hPsym

/-- **Archetype `A₁₁₀` (`M₁`, `archetype_A110_kms_to_zeta_operator_chart_midline_and_reflection_transport`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, and elements `K S X : B`:
1. **Exact Mutual Inverses & Composition of the KMS, Carrier, and Centered-Zeta Operator Charts:**
   - `kmsToCarrierOp (carrierToKmsOp S) = S` and `carrierToKmsOp (kmsToCarrierOp K) = K`,
   - `centeredZetaChart P (kmsToCarrierOp K) = kmsToCenteredOp P K`,
   - `kmsToCenteredOp P (centeredToKmsOp P X) = X` and
     `centeredToKmsOp P (kmsToCenteredOp P K) = K`;
2. **Non-Commutative KMS Midline (`K_mid = 1 - P`) and Strip Boundary (`0`, `1`) Correspondence:**
   - `kmsToCarrierOp (1 - P) = P` (the KMS midline `1 - P` maps to the critical-line idempotent `P`),
   - `kmsToCenteredOp P (1 - P) = 0` (the KMS midline maps to the centered origin `0`),
   - `kmsToCenteredOp P 0 = 1 - P` and `kmsToCenteredOp P 1 = -P`,
   - `kmsToCenteredOp P (1 - K) + kmsToCenteredOp P K = -invS P`;
3. **Exact Transport of the Three `V₄` Reflections (`star`, `zornReflect P`, `kreinReflect P`):**
   - `kmsToCenteredOp P (star K) = star (kmsToCenteredOp P K)`,
   - `kmsToCenteredOp P (zornReflect P K) = zornReflect P (kmsToCenteredOp P K)`,
   - `kmsToCenteredOp P (kreinReflect P K) = kreinReflect P (kmsToCenteredOp P K)`. -/
theorem archetype_A110_kms_to_zeta_operator_chart_midline_and_reflection_transport
    (K S X : B) :
    (kmsToCarrierOp (carrierToKmsOp S) = S ∧
     carrierToKmsOp (kmsToCarrierOp K) = K ∧
     centeredZetaChart P (kmsToCarrierOp K) = kmsToCenteredOp P K ∧
     kmsToCenteredOp P (centeredToKmsOp P X) = X ∧
     centeredToKmsOp P (kmsToCenteredOp P K) = K) ∧
    (kmsToCarrierOp (1 - P) = P ∧
     kmsToCenteredOp P (1 - P) = 0 ∧
     kmsToCenteredOp P 0 = 1 - P ∧
     kmsToCenteredOp P 1 = -P ∧
     kmsToCenteredOp P (1 - K) + kmsToCenteredOp P K = -invS P) ∧
    (kmsToCenteredOp P (star K) = star (kmsToCenteredOp P K) ∧
     kmsToCenteredOp P (zornReflect P K) = zornReflect P (kmsToCenteredOp P K) ∧
     kmsToCenteredOp P (kreinReflect P K) = kreinReflect P (kmsToCenteredOp P K)) := by
  have hInv1 : kmsToCarrierOp (carrierToKmsOp S) = S := by
    unfold kmsToCarrierOp carrierToKmsOp; abel
  have hInv2 : carrierToKmsOp (kmsToCarrierOp K) = K := by
    unfold carrierToKmsOp kmsToCarrierOp; abel
  have hComp : centeredZetaChart P (kmsToCarrierOp K) = kmsToCenteredOp P K := by
    unfold centeredZetaChart kmsToCarrierOp kmsToCenteredOp; abel
  have hInv3 : kmsToCenteredOp P (centeredToKmsOp P X) = X := by
    unfold kmsToCenteredOp centeredToKmsOp; abel
  have hInv4 : centeredToKmsOp P (kmsToCenteredOp P K) = K := by
    unfold centeredToKmsOp kmsToCenteredOp; abel
  have hMid1 : kmsToCarrierOp (1 - P) = P := by
    unfold kmsToCarrierOp; abel
  have hMid2 : kmsToCenteredOp P (1 - P) = 0 := by
    unfold kmsToCenteredOp; abel
  have hBnd0 : kmsToCenteredOp P 0 = 1 - P := by
    unfold kmsToCenteredOp; abel
  have hBnd1 : kmsToCenteredOp P 1 = -P := by
    unfold kmsToCenteredOp; abel
  have hBndSum : kmsToCenteredOp P (1 - K) + kmsToCenteredOp P K = -invS P := by
    unfold kmsToCenteredOp invS; abel
  have hStar : kmsToCenteredOp P (star K) = star (kmsToCenteredOp P K) := by
    unfold kmsToCenteredOp
    rw [star_sub, star_sub, star_one, hPsym]
  have hZornComp : zornReflect P (1 - P) = 1 - P := by
    unfold zornReflect parityConj; peirce_nf hP
  have hZorn : kmsToCenteredOp P (zornReflect P K) = zornReflect P (kmsToCenteredOp P K) := by
    unfold kmsToCenteredOp
    have hZSub : ∀ U V : B, zornReflect P (U - V) = zornReflect P U - zornReflect P V := by
      intro U V; unfold zornReflect parityConj; rw [mul_sub, sub_mul]
    rw [hZSub (1 - P) K, hZornComp]
  have hKreinComp : kreinReflect P (1 - P) = 1 - P := by
    unfold kreinReflect
    rw [star_sub, star_one, hPsym]
    peirce_nf hP
  have hKrein : kmsToCenteredOp P (kreinReflect P K) = kreinReflect P (kmsToCenteredOp P K) := by
    unfold kmsToCenteredOp
    have hKSub : ∀ U V : B, kreinReflect P (U - V) = kreinReflect P U - kreinReflect P V := by
      intro U V; unfold kreinReflect; rw [star_sub, mul_sub, sub_mul]
    rw [hKSub (1 - P) K, hKreinComp]
  exact ⟨⟨hInv1, hInv2, hComp, hInv3, hInv4⟩,
         ⟨hMid1, hMid2, hBnd0, hBnd1, hBndSum⟩,
         ⟨hStar, hZorn, hKrein⟩⟩

omit [StarRing B] hPsym in
/-- **Archetype `A₁₁₁` (`M₂`, `archetype_A111_peirce_edge_winding_monodromy_and_operator_boundary_gluing`):**
Over any non-commutative ring `[Ring B]` with idempotent `P * P = P`, elements `X Y A C : B`,
winding numbers `m n : ℕ`, and mode index `r : ℕ`:
1. **Ring Automorphism Structure of `peirceEdgeWinding P n` at Every Winding Number `n ∈ ℕ`:**
   - `peirceEdgeWinding P 0 X = X`,
   - `peirceEdgeWinding P n (X + Y) = peirceEdgeWinding P n X + peirceEdgeWinding P n Y`,
   - `peirceEdgeWinding P n (X * Y) = peirceEdgeWinding P n X * peirceEdgeWinding P n Y`,
   - `peirceEdgeWinding P n 1 = 1`;
2. **Additive Winding Composition & Period-2 Monodromy Cancellation:**
   - `peirceEdgeWinding P (m + n) X = peirceEdgeWinding P m (peirceEdgeWinding P n X)`,
   - `peirceEdgeWinding P 2 X = X` (two edge crossings cancel),
   - `peirceEdgeWinding P (n + 2) X = peirceEdgeWinding P n X` (period-2 parity monodromy);
3. **All-Mode Operator Boundary Gluing & Non-Triviality Witness:**
   - `peirceUpperBoundary r P A C = zornReflect P (peirceLowerBoundary r P A C)`
     (explicit edge transition `upper = edge(lower)`),
   - `zornReflect P (peirceUpperBoundary r P A C) = peirceLowerBoundary r P A C`
     (crossing the boundary twice returns `lower`),
   - `peirceLowerBoundary r P A C + peirceUpperBoundary r P A C = (2 : ℤ) • P`,
   - `peirceLowerBoundary r P A C - peirceUpperBoundary r P A C =`
     `(2 : ℤ) • (genPhi P A C * opPow r (genV P A C))`
     (exact off-diagonal obstruction to naive untransported periodicity). -/
theorem archetype_A111_peirce_edge_winding_monodromy_and_operator_boundary_gluing
    (X Y A C : B) (m n r : ℕ) :
    (peirceEdgeWinding P 0 X = X ∧
     peirceEdgeWinding P n (X + Y) = peirceEdgeWinding P n X + peirceEdgeWinding P n Y ∧
     peirceEdgeWinding P n (X * Y) = peirceEdgeWinding P n X * peirceEdgeWinding P n Y ∧
     peirceEdgeWinding P n 1 = 1) ∧
    (peirceEdgeWinding P (m + n) X = peirceEdgeWinding P m (peirceEdgeWinding P n X) ∧
     peirceEdgeWinding P 2 X = X ∧
     peirceEdgeWinding P (n + 2) X = peirceEdgeWinding P n X) ∧
    (peirceUpperBoundary r P A C = zornReflect P (peirceLowerBoundary r P A C) ∧
     zornReflect P (peirceUpperBoundary r P A C) = peirceLowerBoundary r P A C ∧
     peirceLowerBoundary r P A C + peirceUpperBoundary r P A C = (2 : ℤ) • P ∧
     peirceLowerBoundary r P A C - peirceUpperBoundary r P A C =
       (2 : ℤ) • (genPhi P A C * opPow r (genV P A C))) := by
  have hSsq : invS P * invS P = 1 := by peirce_nf hP
  have hZAdd : ∀ U V : B, zornReflect P (U + V) = zornReflect P U + zornReflect P V := by
    intro U V; unfold zornReflect parityConj; rw [mul_add, add_mul]
  have hZMul : ∀ U V : B, zornReflect P (U * V) = zornReflect P U * zornReflect P V := by
    intro U V
    unfold zornReflect parityConj
    calc invS P * (U * V) * invS P
        = (invS P * U * (invS P * invS P)) * V * invS P := by
          rw [hSsq, mul_one]; noncomm_ring
      _ = (invS P * U * invS P) * (invS P * V * invS P) := by noncomm_ring
  have hZOne : zornReflect P 1 = 1 := by unfold zornReflect parityConj; peirce_nf hP
  have hZInv : ∀ U : B, zornReflect P (zornReflect P U) = U := by
    intro U; unfold zornReflect parityConj; peirce_nf hP
  have hWAddMap : ∀ k : ℕ,
      peirceEdgeWinding P k (X + Y) = peirceEdgeWinding P k X + peirceEdgeWinding P k Y := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change zornReflect P (peirceEdgeWinding P k (X + Y)) =
        zornReflect P (peirceEdgeWinding P k X) + zornReflect P (peirceEdgeWinding P k Y)
      rw [ih, hZAdd]
  have hWMulMap : ∀ k : ℕ,
      peirceEdgeWinding P k (X * Y) = peirceEdgeWinding P k X * peirceEdgeWinding P k Y := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change zornReflect P (peirceEdgeWinding P k (X * Y)) =
        zornReflect P (peirceEdgeWinding P k X) * zornReflect P (peirceEdgeWinding P k Y)
      rw [ih, hZMul]
  have hWOneMap : ∀ k : ℕ, peirceEdgeWinding P k 1 = 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change zornReflect P (peirceEdgeWinding P k 1) = 1
      rw [ih, hZOne]
  have hWComp : ∀ a : ℕ,
      peirceEdgeWinding P (a + n) X = peirceEdgeWinding P a (peirceEdgeWinding P n X) := by
    intro a
    induction a with
    | zero => rw [Nat.zero_add]; rfl
    | succ a ih =>
      rw [Nat.succ_add]
      exact congrArg (zornReflect P) ih
  have hW2 : peirceEdgeWinding P 2 X = X := hZInv X
  have hWPer : peirceEdgeWinding P (n + 2) X = peirceEdgeWinding P n X :=
    hZInv (peirceEdgeWinding P n X)
  have hZP : zornReflect P P = P := by unfold zornReflect parityConj; peirce_nf hP
  have hSPhi : invS P * genPhi P A C = -genPhi P A C * invS P := by peirce_nf hP
  have hSOp : opPow r (genV P A C) * invS P = invS P * opPow r (genV P A C) :=
    ((opPow_genV_comm_invS_and_cones hP A C r).1).symm
  have hZPhi :
      zornReflect P (genPhi P A C * opPow r (genV P A C)) =
        -(genPhi P A C * opPow r (genV P A C)) := by
    unfold zornReflect parityConj
    calc invS P * (genPhi P A C * opPow r (genV P A C)) * invS P
        = (invS P * genPhi P A C) * (opPow r (genV P A C) * invS P) := by noncomm_ring
      _ = (-genPhi P A C * invS P) * (invS P * opPow r (genV P A C)) := by rw [hSPhi, hSOp]
      _ = -genPhi P A C * (invS P * invS P) * opPow r (genV P A C) := by noncomm_ring
      _ = -(genPhi P A C * opPow r (genV P A C)) := by rw [hSsq, mul_one, neg_mul]
  have hEdge1 : peirceUpperBoundary r P A C = zornReflect P (peirceLowerBoundary r P A C) := by
    unfold peirceUpperBoundary peirceLowerBoundary
    rw [hZAdd, hZP, hZPhi]
    abel
  have hEdge2 : zornReflect P (peirceUpperBoundary r P A C) = peirceLowerBoundary r P A C := by
    rw [hEdge1, hZInv]
  have hEdgeSum : peirceLowerBoundary r P A C + peirceUpperBoundary r P A C = (2 : ℤ) • P := by
    unfold peirceLowerBoundary peirceUpperBoundary
    rw [two_zsmul]
    abel
  have hEdgeDiff :
      peirceLowerBoundary r P A C - peirceUpperBoundary r P A C =
        (2 : ℤ) • (genPhi P A C * opPow r (genV P A C)) := by
    unfold peirceLowerBoundary peirceUpperBoundary
    rw [two_zsmul]
    abel
  exact ⟨⟨rfl, hWAddMap n, hWMulMap n, hWOneMap n⟩,
         ⟨hWComp m, hW2, hWPer⟩,
         ⟨hEdge1, hEdge2, hEdgeSum, hEdgeDiff⟩⟩

/-- **Archetype `A₁₁₂` (`M₃`, `archetype_A112_logistic_graph_idempotents_and_all_mode_midline_defect_virasoro_identity`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, elements `A C : B`, and mode index `r : ℕ`, let
`Phi_r = genPhi P A C * opPow r (genV P A C)` and `J_r = genJ P A C * opPow r (genV P A C)`:
1. **Non-Commutative Logistic Graph Idempotents & Coupled Two-Sheet Decomposition:**
   - `logisticGraphPlus P A = P + conePlus P A` and
     `logisticGraphMinus P C = (1 - P) + coneMinus P C`,
   - `idempotencyDefect (logisticGraphPlus P A) = 0` and
     `idempotencyDefect (logisticGraphMinus P C) = 0`
     (each single-sheet logistic graph operator is an exact idempotent),
   - `logisticGraphPlus P A + logisticGraphMinus P C = 1 + genPhi P A C`,
   - `logisticGraphPlus P A * logisticGraphMinus P C = conePlus P A + qgtPlus P A C` and
     `logisticGraphMinus P C * logisticGraphPlus P A = coneMinus P C + qgtMinus P A C`;
2. **All-Mode Midline Idempotency Defect = Exact Even Virasoro Mode `L_{2r}^+`:**
   - `idempotencyDefect (P + Phi_r) = virasoroModeEven (r + r) P A C`,
   - `idempotencyDefect ((1 - P) - Phi_r) = virasoroModeEven (r + r) P A C`
     (the KMS-reflected partner `(1 - P) - Φ_r` has the exact same Virasoro defect `L_{2r}^+`),
   - `idempotencyDefect (P + J_r) = -virasoroModeEven (r + r) P A C`,
   - `idempotencyDefect ((1 - P) - J_r) = -virasoroModeEven (r + r) P A C`,
   - `idempotencyDefect (P + Phi_r) + idempotencyDefect (P + J_r) = 0`
     (exact conformal harmonic cancellation of the real and imaginary midline defects). -/
theorem archetype_A112_logistic_graph_idempotents_and_all_mode_midline_defect_virasoro_identity
    (A C : B) (r : ℕ) :
    let Phi_r := genPhi P A C * opPow r (genV P A C)
    let J_r := genJ P A C * opPow r (genV P A C)
    (logisticGraphPlus P A = P + conePlus P A ∧
     logisticGraphMinus P C = (1 - P) + coneMinus P C ∧
     idempotencyDefect (logisticGraphPlus P A) = 0 ∧
     idempotencyDefect (logisticGraphMinus P C) = 0 ∧
     logisticGraphPlus P A + logisticGraphMinus P C = 1 + genPhi P A C ∧
     logisticGraphPlus P A * logisticGraphMinus P C = conePlus P A + qgtPlus P A C ∧
     logisticGraphMinus P C * logisticGraphPlus P A = coneMinus P C + qgtMinus P A C) ∧
    (idempotencyDefect (P + Phi_r) = virasoroModeEven (r + r) P A C ∧
     idempotencyDefect ((1 - P) - Phi_r) = virasoroModeEven (r + r) P A C ∧
     idempotencyDefect (P + J_r) = -virasoroModeEven (r + r) P A C ∧
     idempotencyDefect ((1 - P) - J_r) = -virasoroModeEven (r + r) P A C ∧
     idempotencyDefect (P + Phi_r) + idempotencyDefect (P + J_r) = 0) := by
  intro Phi_r J_r
  have hLP : logisticGraphPlus P A = P + conePlus P A := by
    unfold logisticGraphPlus coneExpPlus; peirce_nf hP
  have hLM : logisticGraphMinus P C = (1 - P) + coneMinus P C := by
    unfold logisticGraphMinus coneExpMinus; peirce_nf hP
  have hDefLP : idempotencyDefect (logisticGraphPlus P A) = 0 := by
    unfold idempotencyDefect logisticGraphPlus coneExpPlus; peirce_nf hP
  have hDefLM : idempotencyDefect (logisticGraphMinus P C) = 0 := by
    unfold idempotencyDefect logisticGraphMinus coneExpMinus; peirce_nf hP
  have hLSum : logisticGraphPlus P A + logisticGraphMinus P C = 1 + genPhi P A C := by
    unfold logisticGraphPlus logisticGraphMinus coneExpPlus coneExpMinus; peirce_nf hP
  have hLMul1 : logisticGraphPlus P A * logisticGraphMinus P C = conePlus P A + qgtPlus P A C := by
    unfold logisticGraphPlus logisticGraphMinus coneExpPlus coneExpMinus; peirce_nf hP
  have hLMul2 : logisticGraphMinus P C * logisticGraphPlus P A = coneMinus P C + qgtMinus P A C := by
    unfold logisticGraphPlus logisticGraphMinus coneExpPlus coneExpMinus; peirce_nf hP
  have hSqPPhi :
      (P + Phi_r) * (P + Phi_r) = P + Phi_r + virasoroModeEven (r + r) P A C :=
    (archetype_A89_peirce_bdg_square_commutator_anomaly_and_grading_symmetrization
      hP A C r).2.2.2.1
  have hDefPhi : idempotencyDefect (P + Phi_r) = virasoroModeEven (r + r) P A C := by
    unfold idempotencyDefect
    rw [hSqPPhi]
    abel
  have hFold : ∀ U : B, idempotencyDefect (1 - U) = idempotencyDefect U := by
    intro U; unfold idempotencyDefect; noncomm_ring
  have hSubPhi : (1 - P) - Phi_r = 1 - (P + Phi_r) := by abel
  have hDefPhiComp : idempotencyDefect ((1 - P) - Phi_r) = virasoroModeEven (r + r) P A C := by
    rw [hSubPhi, hFold (P + Phi_r), hDefPhi]
  have hXiJr : xiCenteredOp J_r = 1 + virasoroModeEven (r + r) P A C :=
    (archetype_A103_all_mode_xi_euler_bergman_evaluation_and_zero_reflection_transport
      hP hPsym 0 0 A C r).1.2.2.2
  have hJrSq : J_r * J_r = -virasoroModeEven (r + r) P A C := by
    have h := congrArg (fun Y => Y - 1) hXiJr
    dsimp [xiCenteredOp] at h
    calc J_r * J_r = -((1 - J_r * J_r) - 1) := by abel
      _ = -((1 + virasoroModeEven (r + r) P A C) - 1) := by rw [h]
      _ = -virasoroModeEven (r + r) P A C := by abel
  have hPJ0 : P * genJ P A C + genJ P A C * P = genJ P A C := by peirce_nf hP
  have hVP : opPow r (genV P A C) * P = P * opPow r (genV P A C) :=
    (opPow_genV_comm_idem hP A C r).1.symm
  have hAntiPJ : P * J_r + J_r * P = J_r := by
    change P * (genJ P A C * opPow r (genV P A C)) +
        (genJ P A C * opPow r (genV P A C)) * P =
      genJ P A C * opPow r (genV P A C)
    calc P * (genJ P A C * opPow r (genV P A C)) +
           (genJ P A C * opPow r (genV P A C)) * P
        = (P * genJ P A C) * opPow r (genV P A C) +
          genJ P A C * (opPow r (genV P A C) * P) := by noncomm_ring
      _ = (P * genJ P A C + genJ P A C * P) * opPow r (genV P A C) := by
          rw [hVP]; noncomm_ring
      _ = genJ P A C * opPow r (genV P A C) := by rw [hPJ0]
  have hDefJ : idempotencyDefect (P + J_r) = -virasoroModeEven (r + r) P A C := by
    unfold idempotencyDefect
    calc (P + J_r) * (P + J_r) - (P + J_r)
        = P * P + (P * J_r + J_r * P) + J_r * J_r - (P + J_r) := by noncomm_ring
      _ = -virasoroModeEven (r + r) P A C := by
          rw [hP, hAntiPJ, hJrSq]; abel
  have hSubJ : (1 - P) - J_r = 1 - (P + J_r) := by abel
  have hDefJComp : idempotencyDefect ((1 - P) - J_r) = -virasoroModeEven (r + r) P A C := by
    rw [hSubJ, hFold (P + J_r), hDefJ]
  have hDefCancel : idempotencyDefect (P + Phi_r) + idempotencyDefect (P + J_r) = 0 := by
    rw [hDefPhi, hDefJ, add_neg_cancel]
  exact ⟨⟨hLP, hLM, hDefLP, hDefLM, hLSum, hLMul1, hLMul2⟩,
         ⟨hDefPhi, hDefPhiComp, hDefJ, hDefJComp, hDefCancel⟩⟩

/-- **Archetype `A₁₁₃` (`M₄`, `archetype_A113_carrier_and_kms_brillouin_functional_reflection_and_xi_zero_invariance`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, and elements `S K : B`:
1. **Chart Conjugacy & Exact Involutivity of `carrierFunctionalReflect` and `kmsFunctionalReflect`:**
   - `kmsFunctionalReflect P (carrierToKmsOp S) = carrierToKmsOp (carrierFunctionalReflect P S)`
     (exact chart conjugacy between the carrier reflection and the KMS/Brillouin reflection),
   - `carrierFunctionalReflect P (carrierFunctionalReflect P S) = S`,
   - `kmsFunctionalReflect P (kmsFunctionalReflect P K) = K`
     (the non-commutative operator counterpart of `kreinBrillouinQuotientParity_involutive`),
   - `centeredZetaChart P (carrierFunctionalReflect P S) = -kreinReflect P (centeredZetaChart P S)` and
     `kmsToCenteredOp P (kmsFunctionalReflect P K) = -kreinReflect P (kmsToCenteredOp P K)`;
2. **Exact `Ξ`-Reflection & Zero-Locus Invariance Across Both Charts:**
   - `xiCarrierOp P (carrierFunctionalReflect P S) = kreinReflect P (xiCarrierOp P S)`,
   - `xiKmsOp P (kmsFunctionalReflect P K) = kreinReflect P (xiKmsOp P K)`,
   - `(xiCarrierOp P S = 0 ↔ xiCarrierOp P (carrierFunctionalReflect P S) = 0)`,
   - `(xiKmsOp P K = 0 ↔ xiKmsOp P (kmsFunctionalReflect P K) = 0)`
     (the non-commutative operator counterpart of `kreinBrillouinXiZeroImage_invariant_under_parity`). -/
theorem archetype_A113_carrier_and_kms_brillouin_functional_reflection_and_xi_zero_invariance
    (S K : B) :
    (kmsFunctionalReflect P (carrierToKmsOp S) =
       carrierToKmsOp (carrierFunctionalReflect P S) ∧
     carrierFunctionalReflect P (carrierFunctionalReflect P S) = S ∧
     kmsFunctionalReflect P (kmsFunctionalReflect P K) = K ∧
     centeredZetaChart P (carrierFunctionalReflect P S) =
       -kreinReflect P (centeredZetaChart P S) ∧
     kmsToCenteredOp P (kmsFunctionalReflect P K) =
       -kreinReflect P (kmsToCenteredOp P K)) ∧
    (xiCarrierOp P (carrierFunctionalReflect P S) = kreinReflect P (xiCarrierOp P S) ∧
     xiKmsOp P (kmsFunctionalReflect P K) = kreinReflect P (xiKmsOp P K) ∧
     (xiCarrierOp P S = 0 ↔ xiCarrierOp P (carrierFunctionalReflect P S) = 0) ∧
     (xiKmsOp P K = 0 ↔ xiKmsOp P (kmsFunctionalReflect P K) = 0)) := by
  have hKreinP : kreinReflect P P = P := by
    unfold kreinReflect; rw [hPsym]; peirce_nf hP
  have hKreinOne : kreinReflect P 1 = 1 := by
    unfold kreinReflect; rw [star_one]; peirce_nf hP
  have hKreinSub : ∀ U V : B, kreinReflect P (U - V) = kreinReflect P U - kreinReflect P V := by
    intro U V; unfold kreinReflect; rw [star_sub, mul_sub, sub_mul]
  have hKreinZsmul : ∀ (k : ℤ) (U : B), kreinReflect P (k • U) = k • kreinReflect P U := by
    intro k U; unfold kreinReflect; rw [star_zsmul, mul_smul_comm, smul_mul_assoc]
  have hKreinInv : ∀ U : B, kreinReflect P (kreinReflect P U) = U :=
    fun U => (archetype_A100_krein_fundamental_reflection_and_centered_chart_bijection
      hP hPsym 0 U 0).2.1
  have hKreinComp : kreinReflect P (1 - P) = 1 - P := by
    rw [hKreinSub 1 P, hKreinOne, hKreinP]
  have hConj :
      kmsFunctionalReflect P (carrierToKmsOp S) =
        carrierToKmsOp (carrierFunctionalReflect P S) := by
    unfold kmsFunctionalReflect carrierToKmsOp carrierFunctionalReflect
    rw [hKreinSub 1 S, hKreinOne, two_zsmul, two_zsmul]
    abel
  have hInvCarrier : carrierFunctionalReflect P (carrierFunctionalReflect P S) = S := by
    unfold carrierFunctionalReflect
    rw [hKreinSub ((2 : ℤ) • P) (kreinReflect P S), hKreinZsmul 2 P, hKreinP, hKreinInv S]
    abel
  have hInvKms : kmsFunctionalReflect P (kmsFunctionalReflect P K) = K := by
    unfold kmsFunctionalReflect
    rw [hKreinSub ((2 : ℤ) • (1 - P)) (kreinReflect P K),
        hKreinZsmul 2 (1 - P), hKreinComp, hKreinInv K]
    abel
  have hCentCarrier :
      centeredZetaChart P (carrierFunctionalReflect P S) =
        -kreinReflect P (centeredZetaChart P S) := by
    unfold centeredZetaChart carrierFunctionalReflect
    rw [hKreinSub S P, hKreinP, two_zsmul]
    abel
  have hCentKms :
      kmsToCenteredOp P (kmsFunctionalReflect P K) =
        -kreinReflect P (kmsToCenteredOp P K) := by
    unfold kmsToCenteredOp kmsFunctionalReflect
    rw [hKreinSub (1 - P) K, hKreinComp, two_zsmul]
    abel
  have hXiNeg : ∀ U : B, xiCenteredOp (-U) = xiCenteredOp U := by
    intro U; unfold xiCenteredOp; rw [neg_mul_neg]
  have hXiKrein : ∀ U : B, xiCenteredOp (kreinReflect P U) = kreinReflect P (xiCenteredOp U) :=
    fun U => ((archetype_A103_all_mode_xi_euler_bergman_evaluation_and_zero_reflection_transport
      hP hPsym 0 U 0 0 0).2.1.2).symm
  have hXiCarrierRefl :
      xiCarrierOp P (carrierFunctionalReflect P S) = kreinReflect P (xiCarrierOp P S) := by
    unfold xiCarrierOp
    rw [hCentCarrier, hXiNeg, hXiKrein]
  have hXiKmsRefl :
      xiKmsOp P (kmsFunctionalReflect P K) = kreinReflect P (xiKmsOp P K) := by
    unfold xiKmsOp
    rw [hCentKms, hXiNeg, hXiKrein]
  have hKreinZero : kreinReflect P 0 = 0 := by
    unfold kreinReflect; rw [star_zero, mul_zero, zero_mul]
  have hZeroCarrier :
      xiCarrierOp P S = 0 ↔ xiCarrierOp P (carrierFunctionalReflect P S) = 0 := by
    constructor
    · intro h0
      rw [hXiCarrierRefl, h0, hKreinZero]
    · intro h0
      have h1 := congrArg (kreinReflect P) h0
      rw [hXiCarrierRefl, hKreinInv, hKreinZero] at h1
      exact h1
  have hZeroKms :
      xiKmsOp P K = 0 ↔ xiKmsOp P (kmsFunctionalReflect P K) = 0 := by
    constructor
    · intro h0
      rw [hXiKmsRefl, h0, hKreinZero]
    · intro h0
      have h1 := congrArg (kreinReflect P) h0
      rw [hXiKmsRefl, hKreinInv, hKreinZero] at h1
      exact h1
  exact ⟨⟨hConj, hInvCarrier, hInvKms, hCentCarrier, hCentKms⟩,
         ⟨hXiCarrierRefl, hXiKmsRefl, hZeroCarrier, hZeroKms⟩⟩

omit [StarRing B] hPsym in
/-- **Lemma `T₂.1` (`cayley_moebius_strip_folding`):**
Over any non-commutative ring `[Ring B]` with idempotent `P * P = P` and elements `A C : B`:
1. `cayleyStripForward P A C * cayleyStripFolded P A C = 1` and
   `cayleyStripFolded P A C * cayleyStripForward P A C = 1`;
2. `foldedStripSum P A C = (2 : ℤ) • (1 : B) - genV P A C`;
3. `foldedStripSum P (-A) (-C) = foldedStripSum P A C`. -/
theorem cayley_moebius_strip_folding (A C : B) :
    cayleyStripForward P A C * cayleyStripFolded P A C = 1 ∧
    cayleyStripFolded P A C * cayleyStripForward P A C = 1 ∧
    foldedStripSum P A C = (2 : ℤ) • (1 : B) - genV P A C ∧
    foldedStripSum P (-A) (-C) = foldedStripSum P A C := by
  have h1 : cayleyStripForward P A C * cayleyStripFolded P A C = 1 := by
    unfold cayleyStripForward cayleyStripFolded; peirce_nf hP
  have h2 : cayleyStripFolded P A C * cayleyStripForward P A C = 1 := by
    unfold cayleyStripFolded cayleyStripForward; peirce_nf hP
  have h3 : foldedStripSum P A C = (2 : ℤ) • (1 : B) - genV P A C := by
    unfold foldedStripSum cayleyStripForward cayleyStripFolded; peirce_nf hP
  have h4 : foldedStripSum P (-A) (-C) = foldedStripSum P A C := by
    unfold foldedStripSum cayleyStripForward cayleyStripFolded; peirce_nf hP
  exact ⟨h1, h2, h3, h4⟩

omit [StarRing B] hPsym in
/-- **Lemma `T₄.1` (`helical_winding_group_and_extractor`):**
Over any non-commutative ring `[Ring B]` with idempotent `P * P = P`, elements `A C : B`,
and integer winding numbers `w w₁ w₂ : ℤ`:
1. `helixWindingOp w₁ P A * helixWindingOp w₂ P A = helixWindingOp (w₁ + w₂) P A` and
   `helixWindingOp w P A * helixWindingOpInv w P A = 1`;
2. `zornReflect P (helixWindingOp w P A) = helixWindingOpInv w P A`;
3. `windingNumberExtractor P C (helixWindingOp w P A) (helixWindingOpInv w P A) = w • genV P A C`. -/
theorem helical_winding_group_and_extractor (A C : B) (w w₁ w₂ : ℤ) :
    helixWindingOp w₁ P A * helixWindingOp w₂ P A =
      helixWindingOp (w₁ + w₂) P A ∧
    helixWindingOp w P A * helixWindingOpInv w P A = 1 ∧
    zornReflect P (helixWindingOp w P A) = helixWindingOpInv w P A ∧
    windingNumberExtractor P C (helixWindingOp w P A) (helixWindingOpInv w P A) =
      w • genV P A C := by
  have hConeSq : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold helixWindingOp
    rw [add_mul, one_mul, mul_add, mul_one,
        smul_mul_assoc, mul_smul_comm, hConeSq, smul_zero, smul_zero, add_zero,
        add_smul]
    abel
  · unfold helixWindingOp helixWindingOpInv
    rw [add_mul, one_mul, mul_sub, mul_one,
        smul_mul_assoc, mul_smul_comm, hConeSq, smul_zero, smul_zero, sub_zero]
    abel
  · unfold zornReflect parityConj helixWindingOp helixWindingOpInv
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    have hS1 : invS P * 1 * invS P = 1 := by peirce_nf hP
    have hSCone : invS P * conePlus P A * invS P = -conePlus P A := by peirce_nf hP
    rw [hS1, hSCone, smul_neg, ← sub_eq_add_neg]
  · unfold windingNumberExtractor helixWindingOp helixWindingOpInv comm anticomm
    have hCommP : P * (1 + w • conePlus P A) - (1 + w • conePlus P A) * P =
        w • conePlus P A := by
      rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
      have hPCone : P * conePlus P A = conePlus P A := by peirce_nf hP
      have hConeP : conePlus P A * P = 0 := by peirce_nf hP
      rw [hPCone, hConeP, smul_zero, add_zero, add_sub_cancel_left]
    rw [hCommP, sub_mul, one_mul, smul_mul_assoc, mul_smul_comm, hConeSq,
        smul_zero, smul_zero, sub_zero, smul_mul_assoc, mul_smul_comm, ← smul_add]
    rfl

omit [StarRing B] hPsym in
/-- **Lemma `T₅.1` (`nibelung_ring_toroidal_closure`):**
Over any non-commutative ring `[Ring B]` with idempotent `P * P = P` and elements `A C : B`:
1. `nibelungRingOp P A C = genV P A C` (gluing the forward and folded strip ends `(W_+ - 1)(W_+⁻¹ - 1)`
   yields the exact horizon operator `V(A, C)`);
2. `(cayleyStripForward P A C - 1) * (cayleyStripFolded P A C - 1) =`
   `(cayleyStripFolded P A C - 1) * (cayleyStripForward P A C - 1)`;
3. `nibelungRingOp P A C + (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1`
   (exact unconditional toroidal partition of unity with the Bergman–Plücker determinant). -/
theorem nibelung_ring_toroidal_closure (A C : B) :
    nibelungRingOp P A C = genV P A C ∧
    (cayleyStripForward P A C - 1) * (cayleyStripFolded P A C - 1) =
      (cayleyStripFolded P A C - 1) * (cayleyStripForward P A C - 1) ∧
    nibelungRingOp P A C + (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 := by
  have h1 : nibelungRingOp P A C = genV P A C := by
    unfold nibelungRingOp cayleyStripForward cayleyStripFolded
    peirce_nf hP
  have h2 :
      (cayleyStripForward P A C - 1) * (cayleyStripFolded P A C - 1) =
        (cayleyStripFolded P A C - 1) * (cayleyStripForward P A C - 1) := by
    unfold cayleyStripForward cayleyStripFolded
    peirce_nf hP
  have h3 :
      nibelungRingOp P A C + (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 := by
    unfold nibelungRingOp cayleyStripForward cayleyStripFolded qgtPlus qgtMinus
    peirce_nf hP
  exact ⟨h1, h2, h3⟩

/-- **Archetype `A₁₁₄` (`M₅` & Stage `D₃₄`, `archetype_A114_stage_D34_master_kms_monodromy_logistic_defect_and_brillouin_xi_synthesis`):**
Master Stage `D₃₄` synthesis unifying Archetypes `A₁₁₀ → A₁₁₃` (`M₁ → M₄`) and `T₁ → T₅` in the
114-stage causal poset `MasterSpineStage`:
1. **Strict Causal Poset Chain `A₁₀₉ < A₁₁₀ < A₁₁₁ < A₁₁₂ < A₁₁₃ < A₁₁₄`:**
   - `MasterSpineStage.A109 < MasterSpineStage.A110`,
   - `MasterSpineStage.A110 < MasterSpineStage.A111`,
   - `MasterSpineStage.A111 < MasterSpineStage.A112`,
   - `MasterSpineStage.A112 < MasterSpineStage.A113`,
   - `MasterSpineStage.A113 < MasterSpineStage.A114`;
2. **KMS-to-Zeta Operator Chart Midline & `V₄` Reflection Transport (`M₁`):**
   - `kmsToCenteredOp P (1 - P) = 0` and
     `kmsToCenteredOp P (kreinReflect P K) = kreinReflect P (kmsToCenteredOp P K)`;
3. **Period-2 Peirce Edge Winding Monodromy & Boundary Gluing (`M₂`):**
   - `peirceEdgeWinding P (n + 2) X = peirceEdgeWinding P n X`,
   - `peirceUpperBoundary r P A C = zornReflect P (peirceLowerBoundary r P A C)` and
     `peirceLowerBoundary r P A C - peirceUpperBoundary r P A C =`
     `(2 : ℤ) • (genPhi P A C * opPow r (genV P A C))`;
4. **Logistic Graph Idempotents & All-Mode Midline Virasoro Defect (`M₃`):**
   - `idempotencyDefect (logisticGraphPlus P A) = 0` and
     `idempotencyDefect (logisticGraphMinus P C) = 0`,
   - `idempotencyDefect (P + genPhi P A C * opPow r (genV P A C)) = virasoroModeEven (r + r) P A C` and
     `idempotencyDefect (P + genPhi P A C * opPow r (genV P A C)) +`
     `  idempotencyDefect (P + genJ P A C * opPow r (genV P A C)) = 0`;
5. **KMS/Brillouin Functional Parity Involutivity & `Ξ`-Zero Reflection Invariance (`M₄`):**
   - `kmsFunctionalReflect P (kmsFunctionalReflect P K) = K`,
   - `xiKmsOp P (kmsFunctionalReflect P K) = kreinReflect P (xiKmsOp P K)`,
   - `(xiKmsOp P K = 0 ↔ xiKmsOp P (kmsFunctionalReflect P K) = 0)`;
6. **Cayley–Möbius Strip Folding, Helical Winding Number Extractor & Toroidal Krein Ring Closure (`T₂ → T₅`):**
   - `cayleyStripForward P A C * cayleyStripFolded P A C = 1` and
     `foldedStripSum P A C = (2 : ℤ) • (1 : B) - genV P A C`,
   - `helixWindingOp w₁ P A * helixWindingOp w₂ P A = helixWindingOp (w₁ + w₂) P A` and
     `windingNumberExtractor P C (helixWindingOp w P A) (helixWindingOpInv w P A) = w • genV P A C`,
   - `nibelungRingOp P A C = genV P A C` and
     `nibelungRingOp P A C + (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1`. -/
theorem archetype_A114_stage_D34_master_kms_monodromy_logistic_defect_and_brillouin_xi_synthesis
    (S K X A C : B) (n r : ℕ) (w w₁ w₂ : ℤ) :
    (MasterSpineStage.A109 < MasterSpineStage.A110 ∧
     MasterSpineStage.A110 < MasterSpineStage.A111 ∧
     MasterSpineStage.A111 < MasterSpineStage.A112 ∧
     MasterSpineStage.A112 < MasterSpineStage.A113 ∧
     MasterSpineStage.A113 < MasterSpineStage.A114) ∧
    (kmsToCenteredOp P (1 - P) = 0 ∧
     kmsToCenteredOp P (kreinReflect P K) = kreinReflect P (kmsToCenteredOp P K)) ∧
    (peirceEdgeWinding P (n + 2) X = peirceEdgeWinding P n X ∧
     peirceUpperBoundary r P A C = zornReflect P (peirceLowerBoundary r P A C) ∧
     peirceLowerBoundary r P A C - peirceUpperBoundary r P A C =
       (2 : ℤ) • (genPhi P A C * opPow r (genV P A C))) ∧
    (idempotencyDefect (logisticGraphPlus P A) = 0 ∧
     idempotencyDefect (logisticGraphMinus P C) = 0 ∧
     idempotencyDefect (P + genPhi P A C * opPow r (genV P A C)) =
       virasoroModeEven (r + r) P A C ∧
     idempotencyDefect (P + genPhi P A C * opPow r (genV P A C)) +
         idempotencyDefect (P + genJ P A C * opPow r (genV P A C)) = 0) ∧
    (kmsFunctionalReflect P (kmsFunctionalReflect P K) = K ∧
     xiKmsOp P (kmsFunctionalReflect P K) = kreinReflect P (xiKmsOp P K) ∧
     (xiKmsOp P K = 0 ↔ xiKmsOp P (kmsFunctionalReflect P K) = 0)) ∧
    (cayleyStripForward P A C * cayleyStripFolded P A C = 1 ∧
     foldedStripSum P A C = (2 : ℤ) • (1 : B) - genV P A C ∧
     helixWindingOp w₁ P A * helixWindingOp w₂ P A = helixWindingOp (w₁ + w₂) P A ∧
     windingNumberExtractor P C (helixWindingOp w P A) (helixWindingOpInv w P A) =
       w • genV P A C ∧
     nibelungRingOp P A C = genV P A C ∧
     nibelungRingOp P A C + (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1) := by
  have hChain :
      MasterSpineStage.A109 < MasterSpineStage.A110 ∧
      MasterSpineStage.A110 < MasterSpineStage.A111 ∧
      MasterSpineStage.A111 < MasterSpineStage.A112 ∧
      MasterSpineStage.A112 < MasterSpineStage.A113 ∧
      MasterSpineStage.A113 < MasterSpineStage.A114 := by
    decide
  rcases archetype_A110_kms_to_zeta_operator_chart_midline_and_reflection_transport
      hP hPsym K S X with
    ⟨_, ⟨_, hMid0, _, _, _⟩, ⟨_, _, hKreinTrans⟩⟩
  rcases archetype_A111_peirce_edge_winding_monodromy_and_operator_boundary_gluing
      hP X X A C 0 n r with
    ⟨_, ⟨_, _, hWPer⟩, ⟨hEdge1, _, _, hEdgeDiff⟩⟩
  rcases archetype_A112_logistic_graph_idempotents_and_all_mode_midline_defect_virasoro_identity
      hP hPsym A C r with
    ⟨⟨_, _, hDefLP, hDefLM, _, _, _⟩, ⟨hDefPhi, _, _, _, hDefCancel⟩⟩
  rcases archetype_A113_carrier_and_kms_brillouin_functional_reflection_and_xi_zero_invariance
      hP hPsym S K with
    ⟨⟨_, _, hInvKms, _, _⟩, ⟨_, hXiKmsRefl, _, hZeroKms⟩⟩
  rcases cayley_moebius_strip_folding hP A C with ⟨hCay1, _, hCay3, _⟩
  rcases helical_winding_group_and_extractor hP A C w w₁ w₂ with ⟨hHel1, _, _, hHel4⟩
  rcases nibelung_ring_toroidal_closure hP A C with ⟨hNib1, _, hNib3⟩
  exact ⟨hChain,
         ⟨hMid0, hKreinTrans⟩,
         ⟨hWPer, hEdge1, hEdgeDiff⟩,
         ⟨hDefLP, hDefLM, hDefPhi, hDefCancel⟩,
         ⟨hInvKms, hXiKmsRefl, hZeroKms⟩,
         ⟨hCay1, hCay3, hHel1, hHel4, hNib1, hNib3⟩⟩

end Tier8

/-! ### Part 10: Tier 9 Canonical Synthesis Theorems (`A₁₁₅ → A₁₁₉` / `C₁ → C₅` & Stage `D₃₆`: The Five Faces of Time in Non-Commutative Operator Geometry—Modular Time, Relational Page–Wootters Clock Time, Causal Light-Cone Order, Thermodynamic Arrow of Time, and Discrete Cohomological Epoch Time) -/

section Tier9Defs

variable {B : Type*} [Ring B]

/-- **Archetype `C₂` (`relationalTimeEvol`):** Relational Page–Wootters time evolution
`O_rel(k, P, A, X) = U_k⁻¹ X U_k = (1 - k • N_+(A)) X (1 + k • N_+(A))` dressed by the internal
clock `helixWindingOp k P A`. -/
def relationalTimeEvol (k : ℤ) (P A X : B) : B :=
  helixWindingOpInv k P A * X * helixWindingOp k P A

/-- **Archetype `C₃` (`retardedCausalOp`):** Lower-triangular retarded causal propagator
`P F P + (1 - P) B_ret P + (1 - P) D (1 - P)` with strictly forward propagation from past `P`
to future `1 - P`. -/
def retardedCausalOp (P F B_ret D : B) : B :=
  P * F * P + (1 - P) * B_ret * P + (1 - P) * D * (1 - P)

/-- **Archetype `C₃` (`advancedCausalOp`):** Upper-triangular advanced causal propagator
`P F P + P B_adv (1 - P) + (1 - P) D (1 - P)` dual to `retardedCausalOp` under `star`. -/
def advancedCausalOp (P F B_adv D : B) : B :=
  P * F * P + P * B_adv * (1 - P) + (1 - P) * D * (1 - P)

/-- **Archetype `C₄` (`dissipativeTimeDeriv`):** Irreversible Morrison dissipative double-commutator
`M_J(X) = [J(A, C), [J(A, C), X]]`. -/
def dissipativeTimeDeriv (P A C X : B) : B :=
  comm (genJ P A C) (comm (genJ P A C) X)

/-- **Archetype `C₄` (`arrowOfTimeGen`):** Full metriplectic arrow-of-time generator
`L_arrow(X) = δ_mod(X) + M_J(X) = [Σ, X] + [J, [J, X]]`. -/
def arrowOfTimeGen (P A C X : B) : B :=
  modularTimeDeriv P A C X + dissipativeTimeDeriv P A C X

end Tier9Defs

section Tier9

variable {B : Type*} [Ring B] [StarRing B] {P : B} (hP : P * P = P) (hPsym : star P = P)
include hP hPsym

omit [StarRing B] hPsym in
/-- **Archetype `A₁₁₅` (`C₁`, `archetype_A115_all_mode_modular_time_evolution_and_virasoro_conservation`):**
Over any non-commutative ring `[Ring B]` with idempotent `P * P = P`, elements `A C : B`, and mode
index `r : ℕ`, let `Phi_r = genPhi P A C * opPow r (genV P A C)`,
`J_r = genJ P A C * opPow r (genV P A C)`, `Phi_r1 = genPhi P A C * opPow (r + 1) (genV P A C)`,
`J_r1 = genJ P A C * opPow (r + 1) (genV P A C)`, `L_p = virasoroModeEven r P A C`, and
`L_m = virasoroModeChiral r P A C`:
1. **Fundamental Modular Time Rotation & Acceleration (`r = 0`):**
   - `modularTimeDeriv P A C (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)`,
   - `modularTimeDeriv P A C (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C)`,
   - `modularTimeDeriv P A C (modularTimeDeriv P A C (genPhi P A C)) =`
     `(4 : ℤ) • (genV P A C * genV P A C * genPhi P A C)`,
   - `modularTimeDeriv P A C (genSig P A C) = 0` and `modularTimeDeriv P A C (genV P A C) = 0`;
2. **All-Mode (`r ∈ ℕ`) Modular Time Mode-Raising Ladder & Virasoro Conservation:**
   - `modularTimeDeriv P A C Phi_r = (2 : ℤ) • J_r1`,
   - `modularTimeDeriv P A C J_r = (2 : ℤ) • Phi_r1`,
   - `modularTimeDeriv P A C L_p = 0` and `modularTimeDeriv P A C L_m = 0`
     (every even and chiral Virasoro mode is conserved under modular time evolution). -/
theorem archetype_A115_all_mode_modular_time_evolution_and_virasoro_conservation
    (A C : B) (r : ℕ) :
    let Phi_r := genPhi P A C * opPow r (genV P A C)
    let J_r := genJ P A C * opPow r (genV P A C)
    let Phi_r1 := genPhi P A C * opPow (r + 1) (genV P A C)
    let J_r1 := genJ P A C * opPow (r + 1) (genV P A C)
    let L_p := virasoroModeEven r P A C
    let L_m := virasoroModeChiral r P A C
    (modularTimeDeriv P A C (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
     modularTimeDeriv P A C (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
     modularTimeDeriv P A C (modularTimeDeriv P A C (genPhi P A C)) =
       (4 : ℤ) • (genV P A C * genV P A C * genPhi P A C) ∧
     modularTimeDeriv P A C (genSig P A C) = 0 ∧
     modularTimeDeriv P A C (genV P A C) = 0) ∧
    (modularTimeDeriv P A C Phi_r = (2 : ℤ) • J_r1 ∧
     modularTimeDeriv P A C J_r = (2 : ℤ) • Phi_r1 ∧
     modularTimeDeriv P A C L_p = 0 ∧
     modularTimeDeriv P A C L_m = 0) := by
  intro Phi_r J_r Phi_r1 J_r1 L_p L_m
  have hMPhi0 : modularTimeDeriv P A C (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) := by
    unfold modularTimeDeriv; peirce_nf hP
  have hMJ0 : modularTimeDeriv P A C (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) := by
    unfold modularTimeDeriv; peirce_nf hP
  have hMPhi0Sq :
      modularTimeDeriv P A C (modularTimeDeriv P A C (genPhi P A C)) =
        (4 : ℤ) • (genV P A C * genV P A C * genPhi P A C) := by
    unfold modularTimeDeriv; peirce_nf hP
  have hMSig0 : modularTimeDeriv P A C (genSig P A C) = 0 := by
    unfold modularTimeDeriv; peirce_nf hP
  have hMV0 : modularTimeDeriv P A C (genV P A C) = 0 := by
    unfold modularTimeDeriv; peirce_nf hP
  have hSigOp : ∀ k : ℕ, genSig P A C * opPow k (genV P A C) = opPow k (genV P A C) * genSig P A C := by
    intro k
    rcases opPow_genV_comm_invS_and_cones hP A C k with ⟨_, hCp, hCm⟩
    have h1 : (conePlus P A * coneMinus P C) * opPow k (genV P A C) =
        opPow k (genV P A C) * (conePlus P A * coneMinus P C) := by
      calc (conePlus P A * coneMinus P C) * opPow k (genV P A C)
          = conePlus P A * (coneMinus P C * opPow k (genV P A C)) := mul_assoc _ _ _
        _ = conePlus P A * (opPow k (genV P A C) * coneMinus P C) := by rw [hCm]
        _ = (conePlus P A * opPow k (genV P A C)) * coneMinus P C := (mul_assoc _ _ _).symm
        _ = (opPow k (genV P A C) * conePlus P A) * coneMinus P C := by rw [hCp]
        _ = opPow k (genV P A C) * (conePlus P A * coneMinus P C) := mul_assoc _ _ _
    have h2 : (coneMinus P C * conePlus P A) * opPow k (genV P A C) =
        opPow k (genV P A C) * (coneMinus P C * conePlus P A) := by
      calc (coneMinus P C * conePlus P A) * opPow k (genV P A C)
          = coneMinus P C * (conePlus P A * opPow k (genV P A C)) := mul_assoc _ _ _
        _ = coneMinus P C * (opPow k (genV P A C) * conePlus P A) := by rw [hCp]
        _ = (coneMinus P C * opPow k (genV P A C)) * conePlus P A := (mul_assoc _ _ _).symm
        _ = (opPow k (genV P A C) * coneMinus P C) * conePlus P A := by rw [hCm]
        _ = opPow k (genV P A C) * (coneMinus P C * conePlus P A) := mul_assoc _ _ _
    unfold genSig comm
    rw [sub_mul, mul_sub, h1, h2]
  have hModRight : ∀ (U W : B), genSig P A C * W = W * genSig P A C →
      modularTimeDeriv P A C (U * W) = modularTimeDeriv P A C U * W := by
    intro U W hSW
    unfold modularTimeDeriv comm
    calc genSig P A C * (U * W) - (U * W) * genSig P A C
        = (genSig P A C * U) * W - U * (W * genSig P A C) := by noncomm_ring
      _ = (genSig P A C * U) * W - U * (genSig P A C * W) := by rw [hSW]
      _ = (genSig P A C * U - U * genSig P A C) * W := by noncomm_ring
  have hVJ : genV P A C * genJ P A C = genJ P A C * genV P A C := by peirce_nf hP
  have hVPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by peirce_nf hP
  have hVOp : genV P A C * opPow r (genV P A C) = opPow (r + 1) (genV P A C) := by
    rw [mul_opPow_comm r (genV P A C)]
    rfl
  have hMPhir : modularTimeDeriv P A C Phi_r = (2 : ℤ) • J_r1 := by
    change modularTimeDeriv P A C (genPhi P A C * opPow r (genV P A C)) =
      (2 : ℤ) • (genJ P A C * opPow (r + 1) (genV P A C))
    rw [hModRight (genPhi P A C) (opPow r (genV P A C)) (hSigOp r), hMPhi0, smul_mul_assoc]
    congr 1
    calc (genV P A C * genJ P A C) * opPow r (genV P A C)
        = genJ P A C * (genV P A C * opPow r (genV P A C)) := by rw [hVJ, mul_assoc]
      _ = genJ P A C * opPow (r + 1) (genV P A C) := by rw [hVOp]
  have hMJr : modularTimeDeriv P A C J_r = (2 : ℤ) • Phi_r1 := by
    change modularTimeDeriv P A C (genJ P A C * opPow r (genV P A C)) =
      (2 : ℤ) • (genPhi P A C * opPow (r + 1) (genV P A C))
    rw [hModRight (genJ P A C) (opPow r (genV P A C)) (hSigOp r), hMJ0, smul_mul_assoc]
    congr 1
    calc (genV P A C * genPhi P A C) * opPow r (genV P A C)
        = genPhi P A C * (genV P A C * opPow r (genV P A C)) := by rw [hVPhi, mul_assoc]
      _ = genPhi P A C * opPow (r + 1) (genV P A C) := by rw [hVOp]
  have hMLp : modularTimeDeriv P A C L_p = 0 := by
    change comm (genSig P A C) (opPow (r + 1) (genV P A C)) = 0
    unfold comm
    rw [hSigOp (r + 1), sub_self]
  have hMLm : modularTimeDeriv P A C L_m = 0 := by
    change comm (genSig P A C) (opPow r (genV P A C) * genSig P A C) = 0
    unfold comm
    rw [← mul_assoc, hSigOp r, sub_self]
  exact ⟨⟨hMPhi0, hMJ0, hMPhi0Sq, hMSig0, hMV0⟩,
         ⟨hMPhir, hMJr, hMLp, hMLm⟩⟩

omit [StarRing B] hPsym in
/-- **Archetype `A₁₁₆` (`C₂`, `archetype_A116_relational_page_wootters_clock_group_and_all_mode_virasoro_invariance`):**
Over any non-commutative ring `[Ring B]` with idempotent `P * P = P`, elements `A C X Y : B`,
integer clock ticks `k k₁ k₂ : ℤ`, and mode index `r : ℕ`:
1. **Additive 1-Parameter Relational Clock Group Law & Automorphism Structure:**
   - `relationalTimeEvol 0 P A X = X`,
   - `relationalTimeEvol k₂ P A (relationalTimeEvol k₁ P A X) = relationalTimeEvol (k₁ + k₂) P A X`,
   - `relationalTimeEvol (-k) P A (relationalTimeEvol k P A X) = X`,
   - `relationalTimeEvol k P A (X * Y) = relationalTimeEvol k P A X * relationalTimeEvol k P A Y`;
2. **Canonical Clock–Energy Commutation, Clock-Dressed Past Projector & All-Mode Virasoro Stationarity:**
   - `windingNumberExtractor P C (helixWindingOp k P A) (helixWindingOpInv k P A) = k • genV P A C`,
   - `relationalTimeEvol k P A P = P + k • conePlus P A`,
   - `relationalTimeEvol k P A (genV P A C) = genV P A C`,
   - `relationalTimeEvol k P A (virasoroModeEven r P A C) = virasoroModeEven r P A C`. -/
theorem archetype_A116_relational_page_wootters_clock_group_and_all_mode_virasoro_invariance
    (A C X Y : B) (k k₁ k₂ : ℤ) (r : ℕ) :
    (relationalTimeEvol 0 P A X = X ∧
     relationalTimeEvol k₂ P A (relationalTimeEvol k₁ P A X) =
       relationalTimeEvol (k₁ + k₂) P A X ∧
     relationalTimeEvol (-k) P A (relationalTimeEvol k P A X) = X ∧
     relationalTimeEvol k P A (X * Y) =
       relationalTimeEvol k P A X * relationalTimeEvol k P A Y) ∧
    (windingNumberExtractor P C (helixWindingOp k P A) (helixWindingOpInv k P A) =
       k • genV P A C ∧
     relationalTimeEvol k P A P = P + k • conePlus P A ∧
     relationalTimeEvol k P A (genV P A C) = genV P A C ∧
     relationalTimeEvol k P A (virasoroModeEven r P A C) = virasoroModeEven r P A C) := by
  have hConeSq : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have hHelixMul : ∀ m₁ m₂ : ℤ,
      helixWindingOp m₁ P A * helixWindingOp m₂ P A = helixWindingOp (m₁ + m₂) P A :=
    fun m₁ m₂ => (helical_winding_group_and_extractor hP A C 0 m₁ m₂).1
  have hHelixInvEq : ∀ m : ℤ, helixWindingOpInv m P A = helixWindingOp (-m) P A := by
    intro m
    unfold helixWindingOpInv helixWindingOp
    rw [neg_smul, ← sub_eq_add_neg]
  have hHelixInvMul : ∀ m₁ m₂ : ℤ,
      helixWindingOpInv m₂ P A * helixWindingOpInv m₁ P A = helixWindingOpInv (m₁ + m₂) P A := by
    intro m₁ m₂
    rw [hHelixInvEq m₂, hHelixInvEq m₁, hHelixInvEq (m₁ + m₂), hHelixMul (-m₂) (-m₁)]
    congr 1
    abel
  have hR0 : ∀ U : B, relationalTimeEvol 0 P A U = U := by
    intro U
    unfold relationalTimeEvol helixWindingOp helixWindingOpInv
    rw [zero_smul, add_zero, sub_zero, one_mul, mul_one]
  have hRAdd : ∀ m₁ m₂ : ℤ,
      relationalTimeEvol m₂ P A (relationalTimeEvol m₁ P A X) =
        relationalTimeEvol (m₁ + m₂) P A X := by
    intro m₁ m₂
    unfold relationalTimeEvol
    calc helixWindingOpInv m₂ P A * (helixWindingOpInv m₁ P A * X * helixWindingOp m₁ P A) *
           helixWindingOp m₂ P A
        = (helixWindingOpInv m₂ P A * helixWindingOpInv m₁ P A) * X *
          (helixWindingOp m₁ P A * helixWindingOp m₂ P A) := by noncomm_ring
      _ = helixWindingOpInv (m₁ + m₂) P A * X * helixWindingOp (m₁ + m₂) P A := by
          rw [hHelixInvMul m₁ m₂, hHelixMul m₁ m₂]
  have hRNeg : relationalTimeEvol (-k) P A (relationalTimeEvol k P A X) = X := by
    rw [hRAdd k (-k), add_neg_cancel, hR0 X]
  have hInvRight : helixWindingOp k P A * helixWindingOpInv k P A = 1 :=
    (helical_winding_group_and_extractor hP A C k 0 0).2.1
  have hInvLeft : helixWindingOpInv k P A * helixWindingOp k P A = 1 := by
    rw [hHelixInvEq k, hHelixMul (-k) k, neg_add_cancel]
    unfold helixWindingOp
    rw [zero_smul, add_zero]
  have hRMul :
      relationalTimeEvol k P A (X * Y) =
        relationalTimeEvol k P A X * relationalTimeEvol k P A Y := by
    unfold relationalTimeEvol
    calc helixWindingOpInv k P A * (X * Y) * helixWindingOp k P A
        = helixWindingOpInv k P A * X *
          (helixWindingOp k P A * helixWindingOpInv k P A) * Y *
          helixWindingOp k P A := by rw [hInvRight, mul_one]; noncomm_ring
      _ = (helixWindingOpInv k P A * X * helixWindingOp k P A) *
          (helixWindingOpInv k P A * Y * helixWindingOp k P A) := by noncomm_ring
  have hExt :
      windingNumberExtractor P C (helixWindingOp k P A) (helixWindingOpInv k P A) =
        k • genV P A C :=
    (helical_winding_group_and_extractor hP A C k 0 0).2.2.2
  have hRP : relationalTimeEvol k P A P = P + k • conePlus P A := by
    unfold relationalTimeEvol helixWindingOp helixWindingOpInv
    have hPCone : P * conePlus P A = conePlus P A := by peirce_nf hP
    have hConeP : conePlus P A * P = 0 := by peirce_nf hP
    rw [sub_mul, one_mul, smul_mul_assoc, hConeP, smul_zero, sub_zero,
        mul_add, mul_one, mul_smul_comm, hPCone]
  have hCommHelix : ∀ U : B, conePlus P A * U = U * conePlus P A →
      relationalTimeEvol k P A U = U := by
    intro U hCU
    have hUH : U * helixWindingOp k P A = helixWindingOp k P A * U := by
      unfold helixWindingOp
      rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hCU]
    unfold relationalTimeEvol
    calc helixWindingOpInv k P A * U * helixWindingOp k P A
        = helixWindingOpInv k P A * (U * helixWindingOp k P A) := by noncomm_ring
      _ = (helixWindingOpInv k P A * helixWindingOp k P A) * U := by
          rw [hUH]; noncomm_ring
      _ = 1 * U := by rw [hInvLeft]
      _ = U := one_mul U
  have hCV : conePlus P A * genV P A C = genV P A C * conePlus P A := by peirce_nf hP
  have hRV : relationalTimeEvol k P A (genV P A C) = genV P A C :=
    hCommHelix (genV P A C) hCV
  have hCLp : conePlus P A * virasoroModeEven r P A C = virasoroModeEven r P A C * conePlus P A :=
    (opPow_genV_comm_invS_and_cones hP A C (r + 1)).2.1
  have hRLp : relationalTimeEvol k P A (virasoroModeEven r P A C) = virasoroModeEven r P A C :=
    hCommHelix (virasoroModeEven r P A C) hCLp
  exact ⟨⟨hR0 X, hRAdd k₁ k₂, hRNeg, hRMul⟩,
         ⟨hExt, hRP, hRV, hRLp⟩⟩

/-- **Archetype `A₁₁₇` (`C₃`, `archetype_A117_causal_light_cone_order_retarded_semigroup_and_star_duality`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, and elements `F₁ B₁ D₁ F₂ B₂ D₂ : B`:
1. **Strict Light-Cone Causality (Zero Future-to-Past / Past-to-Future Acausal Leakage):**
   - `P * retardedCausalOp P F₁ B₁ D₁ * (1 - P) = 0`,
   - `(1 - P) * advancedCausalOp P F₁ B₁ D₁ * P = 0`;
2. **Exact Composition Semigroup Law of Retarded & Advanced Causal Propagators:**
   - `retardedCausalOp P F₁ B₁ D₁ * retardedCausalOp P F₂ B₂ D₂ =`
     `retardedCausalOp P (F₁ * P * F₂) (B₁ * P * F₂ + D₁ * (1 - P) * B₂) (D₁ * (1 - P) * D₂)`,
   - `advancedCausalOp P F₁ B₁ D₁ * advancedCausalOp P F₂ B₂ D₂ =`
     `advancedCausalOp P (F₁ * P * F₂) (F₁ * P * B₂ + B₁ * (1 - P) * D₂) (D₁ * (1 - P) * D₂)`;
3. **Star-Duality Reverses the Causal Light Cone (`retardedCausalOp ↔ advancedCausalOp`):**
   - `star (retardedCausalOp P F₁ B₁ D₁) = advancedCausalOp P (star F₁) (star B₁) (star D₁)`,
   - `star (advancedCausalOp P F₁ B₁ D₁) = retardedCausalOp P (star F₁) (star B₁) (star D₁)`. -/
theorem archetype_A117_causal_light_cone_order_retarded_semigroup_and_star_duality
    (F₁ B₁ D₁ F₂ B₂ D₂ : B) :
    (P * retardedCausalOp P F₁ B₁ D₁ * (1 - P) = 0 ∧
     (1 - P) * advancedCausalOp P F₁ B₁ D₁ * P = 0) ∧
    (retardedCausalOp P F₁ B₁ D₁ * retardedCausalOp P F₂ B₂ D₂ =
       retardedCausalOp P (F₁ * P * F₂) (B₁ * P * F₂ + D₁ * (1 - P) * B₂) (D₁ * (1 - P) * D₂) ∧
     advancedCausalOp P F₁ B₁ D₁ * advancedCausalOp P F₂ B₂ D₂ =
       advancedCausalOp P (F₁ * P * F₂) (F₁ * P * B₂ + B₁ * (1 - P) * D₂) (D₁ * (1 - P) * D₂)) ∧
    (star (retardedCausalOp P F₁ B₁ D₁) =
       advancedCausalOp P (star F₁) (star B₁) (star D₁) ∧
     star (advancedCausalOp P F₁ B₁ D₁) =
       retardedCausalOp P (star F₁) (star B₁) (star D₁)) := by
  have hLeak1 : P * retardedCausalOp P F₁ B₁ D₁ * (1 - P) = 0 := by
    unfold retardedCausalOp; peirce_nf hP
  have hLeak2 : (1 - P) * advancedCausalOp P F₁ B₁ D₁ * P = 0 := by
    unfold advancedCausalOp; peirce_nf hP
  have hComp1 :
      retardedCausalOp P F₁ B₁ D₁ * retardedCausalOp P F₂ B₂ D₂ =
        retardedCausalOp P (F₁ * P * F₂) (B₁ * P * F₂ + D₁ * (1 - P) * B₂) (D₁ * (1 - P) * D₂) := by
    unfold retardedCausalOp; peirce_nf hP
  have hComp2 :
      advancedCausalOp P F₁ B₁ D₁ * advancedCausalOp P F₂ B₂ D₂ =
        advancedCausalOp P (F₁ * P * F₂) (F₁ * P * B₂ + B₁ * (1 - P) * D₂) (D₁ * (1 - P) * D₂) := by
    unfold advancedCausalOp; peirce_nf hP
  have hStar1 :
      star (retardedCausalOp P F₁ B₁ D₁) =
        advancedCausalOp P (star F₁) (star B₁) (star D₁) := by
    unfold retardedCausalOp advancedCausalOp
    rw [star_add, star_add, star_mul, star_mul, star_mul, star_mul, star_mul, star_mul,
        star_sub, star_one, hPsym]
    noncomm_ring
  have hStar2 :
      star (advancedCausalOp P F₁ B₁ D₁) =
        retardedCausalOp P (star F₁) (star B₁) (star D₁) := by
    unfold advancedCausalOp retardedCausalOp
    rw [star_add, star_add, star_mul, star_mul, star_mul, star_mul, star_mul, star_mul,
        star_sub, star_one, hPsym]
    noncomm_ring
  exact ⟨⟨hLeak1, hLeak2⟩, ⟨hComp1, hComp2⟩, ⟨hStar1, hStar2⟩⟩

/-- **Archetype `A₁₁₈` (`C₄`, `archetype_A118_thermodynamic_arrow_of_time_and_all_mode_dissipative_eigenvalues`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, elements `A C X : B`, and mode index `r : ℕ`, let
`Phi_r = genPhi P A C * opPow r (genV P A C)`, `J_r = genJ P A C * opPow r (genV P A C)`, and
`Phi_r1 = genPhi P A C * opPow (r + 1) (genV P A C)`:
1. **All-Mode Dissipative Contraction vs. Critical-Seam Annihilation:**
   - `dissipativeTimeDeriv P A C (genPhi P A C) = -((4 : ℤ) • (genPhi P A C * genV P A C))`,
   - `dissipativeTimeDeriv P A C (genJ P A C) = 0`,
   - `dissipativeTimeDeriv P A C (genV P A C) = 0`,
   - `dissipativeTimeDeriv P A C Phi_r = -((4 : ℤ) • Phi_r1)`
     (dissipative time damps the transverse off-seam mode `Φ_r` with negative sign `-4 Φ_{r+1}`),
   - `dissipativeTimeDeriv P A C J_r = 0`
     (the critical-seam mode `J_r` is completely frictionless under `M_J`);
2. **The Thermodynamic Arrow of Time (Star-Odd Symplectic vs. Star-Even Dissipative):**
   - `star (modularTimeDeriv P A (star A) X) = -modularTimeDeriv P A (star A) (star X)`
     (reversible modular time reverses sign under `star`),
   - `star (dissipativeTimeDeriv P A (star A) X) = dissipativeTimeDeriv P A (star A) (star X)`
     (irreversible dissipative time keeps the same sign under `star`),
   - `star (arrowOfTimeGen P A (star A) X) + arrowOfTimeGen P A (star A) (star X) =`
     `(2 : ℤ) • dissipativeTimeDeriv P A (star A) (star X)`,
   - `star (arrowOfTimeGen P A (star A) X) - arrowOfTimeGen P A (star A) (star X) =`
     `-((2 : ℤ) • modularTimeDeriv P A (star A) (star X))`. -/
theorem archetype_A118_thermodynamic_arrow_of_time_and_all_mode_dissipative_eigenvalues
    (A C X : B) (r : ℕ) :
    let Phi_r := genPhi P A C * opPow r (genV P A C)
    let J_r := genJ P A C * opPow r (genV P A C)
    let Phi_r1 := genPhi P A C * opPow (r + 1) (genV P A C)
    (dissipativeTimeDeriv P A C (genPhi P A C) =
       -((4 : ℤ) • (genPhi P A C * genV P A C)) ∧
     dissipativeTimeDeriv P A C (genJ P A C) = 0 ∧
     dissipativeTimeDeriv P A C (genV P A C) = 0 ∧
     dissipativeTimeDeriv P A C Phi_r = -((4 : ℤ) • Phi_r1) ∧
     dissipativeTimeDeriv P A C J_r = 0) ∧
    (star (modularTimeDeriv P A (star A) X) =
       -modularTimeDeriv P A (star A) (star X) ∧
     star (dissipativeTimeDeriv P A (star A) X) =
       dissipativeTimeDeriv P A (star A) (star X) ∧
     star (arrowOfTimeGen P A (star A) X) + arrowOfTimeGen P A (star A) (star X) =
       (2 : ℤ) • dissipativeTimeDeriv P A (star A) (star X) ∧
     star (arrowOfTimeGen P A (star A) X) - arrowOfTimeGen P A (star A) (star X) =
       -((2 : ℤ) • modularTimeDeriv P A (star A) (star X))) := by
  intro Phi_r J_r Phi_r1
  have hDPhi0 :
      dissipativeTimeDeriv P A C (genPhi P A C) =
        -((4 : ℤ) • (genPhi P A C * genV P A C)) := by
    unfold dissipativeTimeDeriv; peirce_nf hP
  have hDJ0 : dissipativeTimeDeriv P A C (genJ P A C) = 0 := by
    unfold dissipativeTimeDeriv; peirce_nf hP
  have hDV0 : dissipativeTimeDeriv P A C (genV P A C) = 0 := by
    unfold dissipativeTimeDeriv; peirce_nf hP
  have hJOp : genJ P A C * opPow r (genV P A C) = opPow r (genV P A C) * genJ P A C := by
    rcases opPow_genV_comm_invS_and_cones hP A C r with ⟨_, hCp, hCm⟩
    unfold genJ
    rw [sub_mul, mul_sub, hCp, hCm]
  have hCommJRight : ∀ U : B,
      comm (genJ P A C) (U * opPow r (genV P A C)) =
        comm (genJ P A C) U * opPow r (genV P A C) := by
    intro U
    unfold comm
    calc genJ P A C * (U * opPow r (genV P A C)) - (U * opPow r (genV P A C)) * genJ P A C
        = (genJ P A C * U) * opPow r (genV P A C) - U * (opPow r (genV P A C) * genJ P A C) := by
          noncomm_ring
      _ = (genJ P A C * U) * opPow r (genV P A C) - U * (genJ P A C * opPow r (genV P A C)) := by
          rw [← hJOp]
      _ = (genJ P A C * U - U * genJ P A C) * opPow r (genV P A C) := by noncomm_ring
  have hDissRight : ∀ U : B,
      dissipativeTimeDeriv P A C (U * opPow r (genV P A C)) =
        dissipativeTimeDeriv P A C U * opPow r (genV P A C) := by
    intro U
    unfold dissipativeTimeDeriv
    rw [hCommJRight U, hCommJRight (comm (genJ P A C) U)]
  have hVOp : genV P A C * opPow r (genV P A C) = opPow (r + 1) (genV P A C) := by
    rw [mul_opPow_comm r (genV P A C)]
    rfl
  have hDPhir : dissipativeTimeDeriv P A C Phi_r = -((4 : ℤ) • Phi_r1) := by
    change dissipativeTimeDeriv P A C (genPhi P A C * opPow r (genV P A C)) =
      -((4 : ℤ) • (genPhi P A C * opPow (r + 1) (genV P A C)))
    rw [hDissRight (genPhi P A C), hDPhi0, neg_mul, smul_mul_assoc, mul_assoc, hVOp]
  have hDJr : dissipativeTimeDeriv P A C J_r = 0 := by
    change dissipativeTimeDeriv P A C (genJ P A C * opPow r (genV P A C)) = 0
    rw [hDissRight (genJ P A C), hDJ0, zero_mul]
  have hStarCone : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hStarConeM : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hStarCone, star_star]
  have hStarSig : star (genSig P A (star A)) = genSig P A (star A) := by
    unfold genSig comm
    rw [star_sub, star_mul, star_mul, hStarCone, hStarConeM]
  have hStarJ : star (genJ P A (star A)) = -genJ P A (star A) := by
    unfold genJ; rw [star_sub, hStarCone, hStarConeM, neg_sub]
  have hCommHerm : ∀ H Z : B, star H = H → star (comm H Z) = -comm H (star Z) := by
    intro H Z hH
    unfold comm
    rw [star_sub, star_mul, star_mul, hH, neg_sub]
  have hCommSkew : ∀ U Z : B, star U = -U → star (comm U Z) = comm U (star Z) := by
    intro U Z hU
    unfold comm
    rw [star_sub, star_mul, star_mul, hU, mul_neg, neg_mul]
    abel
  have hModOdd :
      star (modularTimeDeriv P A (star A) X) =
        -modularTimeDeriv P A (star A) (star X) :=
    hCommHerm (genSig P A (star A)) X hStarSig
  have hDissEven :
      star (dissipativeTimeDeriv P A (star A) X) =
        dissipativeTimeDeriv P A (star A) (star X) := by
    unfold dissipativeTimeDeriv
    rw [hCommSkew (genJ P A (star A)) (comm (genJ P A (star A)) X) hStarJ,
        hCommSkew (genJ P A (star A)) X hStarJ]
  have hArrowSum :
      star (arrowOfTimeGen P A (star A) X) + arrowOfTimeGen P A (star A) (star X) =
        (2 : ℤ) • dissipativeTimeDeriv P A (star A) (star X) := by
    unfold arrowOfTimeGen
    rw [star_add, hModOdd, hDissEven, two_zsmul]
    abel
  have hArrowDiff :
      star (arrowOfTimeGen P A (star A) X) - arrowOfTimeGen P A (star A) (star X) =
        -((2 : ℤ) • modularTimeDeriv P A (star A) (star X)) := by
    unfold arrowOfTimeGen
    rw [star_add, hModOdd, hDissEven, two_zsmul]
    abel
  exact ⟨⟨hDPhi0, hDJ0, hDV0, hDPhir, hDJr⟩,
         ⟨hModOdd, hDissEven, hArrowSum, hArrowDiff⟩⟩

/-- **Archetype `A₁₁₉` (`C₅` & Stage `D₃₆`, `archetype_A119_cohomological_epoch_time_stationarity_and_stage_D36_synthesis`):**
Master Stage `D₃₆` synthesis unifying Archetypes `A₁₁₅ → A₁₁₈` (`C₁ → C₄`) with Discrete
Cohomological Epoch Time (`C₅`) in the 119-stage causal poset `MasterSpineStage`:
1. **Strict Causal Poset Chain `A₁₁₄ < A₁₁₅ < A₁₁₆ < A₁₁₇ < A₁₁₈ < A₁₁₉`:**
   - `MasterSpineStage.A114 < MasterSpineStage.A115`,
   - `MasterSpineStage.A115 < MasterSpineStage.A116`,
   - `MasterSpineStage.A116 < MasterSpineStage.A117`,
   - `MasterSpineStage.A117 < MasterSpineStage.A118`,
   - `MasterSpineStage.A118 < MasterSpineStage.A119`;
2. **All-Epoch (`n ∈ ℕ`) Stationarity of the Cohomological Defect Tower `V_n = δ^[n](V)` (`C₅`):**
   - `conePlus P A * idempotencyDefect^[n] (genV P A C) =`
     `idempotencyDefect^[n] (genV P A C) * conePlus P A`,
   - `modularTimeDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0`,
   - `dissipativeTimeDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0`,
   - `arrowOfTimeGen P A C (idempotencyDefect^[n] (genV P A C)) = 0`,
   - `relationalTimeEvol k P A (idempotencyDefect^[n] (genV P A C)) =`
     `idempotencyDefect^[n] (genV P A C)`;
3. **Complete Five-Faces-of-Time Master Synthesis (`C₁ → C₅`):**
   - `modularTimeDeriv P A C (genPhi P A C * opPow r (genV P A C)) =`
     `(2 : ℤ) • (genJ P A C * opPow (r + 1) (genV P A C))`,
   - `relationalTimeEvol k₂ P A (relationalTimeEvol k₁ P A X) = relationalTimeEvol (k₁ + k₂) P A X`,
   - `P * retardedCausalOp P F₁ B₁ D₁ * (1 - P) = 0` and
     `star (retardedCausalOp P F₁ B₁ D₁) = advancedCausalOp P (star F₁) (star B₁) (star D₁)`,
   - `star (arrowOfTimeGen P A (star A) X) + arrowOfTimeGen P A (star A) (star X) =`
     `(2 : ℤ) • dissipativeTimeDeriv P A (star A) (star X)`. -/
theorem archetype_A119_cohomological_epoch_time_stationarity_and_stage_D36_synthesis
    (A C X F₁ B₁ D₁ : B) (k k₁ k₂ : ℤ) (n r : ℕ) :
    (MasterSpineStage.A114 < MasterSpineStage.A115 ∧
     MasterSpineStage.A115 < MasterSpineStage.A116 ∧
     MasterSpineStage.A116 < MasterSpineStage.A117 ∧
     MasterSpineStage.A117 < MasterSpineStage.A118 ∧
     MasterSpineStage.A118 < MasterSpineStage.A119) ∧
    (conePlus P A * idempotencyDefect^[n] (genV P A C) =
       idempotencyDefect^[n] (genV P A C) * conePlus P A ∧
     modularTimeDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0 ∧
     dissipativeTimeDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0 ∧
     arrowOfTimeGen P A C (idempotencyDefect^[n] (genV P A C)) = 0 ∧
     relationalTimeEvol k P A (idempotencyDefect^[n] (genV P A C)) =
       idempotencyDefect^[n] (genV P A C)) ∧
    (modularTimeDeriv P A C (genPhi P A C * opPow r (genV P A C)) =
       (2 : ℤ) • (genJ P A C * opPow (r + 1) (genV P A C)) ∧
     relationalTimeEvol k₂ P A (relationalTimeEvol k₁ P A X) =
       relationalTimeEvol (k₁ + k₂) P A X ∧
     P * retardedCausalOp P F₁ B₁ D₁ * (1 - P) = 0 ∧
     star (retardedCausalOp P F₁ B₁ D₁) =
       advancedCausalOp P (star F₁) (star B₁) (star D₁) ∧
     star (arrowOfTimeGen P A (star A) X) + arrowOfTimeGen P A (star A) (star X) =
       (2 : ℤ) • dissipativeTimeDeriv P A (star A) (star X)) := by
  have hChain :
      MasterSpineStage.A114 < MasterSpineStage.A115 ∧
      MasterSpineStage.A115 < MasterSpineStage.A116 ∧
      MasterSpineStage.A116 < MasterSpineStage.A117 ∧
      MasterSpineStage.A117 < MasterSpineStage.A118 ∧
      MasterSpineStage.A118 < MasterSpineStage.A119 := by
    decide
  have hCommDefect : ∀ U W : B, U * W = W * U →
      U * idempotencyDefect W = idempotencyDefect W * U := by
    intro U W hUW
    have hUWW : U * (W * W) = (W * W) * U := by
      calc U * (W * W)
          = (U * W) * W := (mul_assoc _ _ _).symm
        _ = (W * U) * W := by rw [hUW]
        _ = W * (U * W) := mul_assoc _ _ _
        _ = W * (W * U) := by rw [hUW]
        _ = (W * W) * U := (mul_assoc _ _ _).symm
    unfold idempotencyDefect
    rw [mul_sub, sub_mul, hUWW, hUW]
  have hConeEpoch : ∀ m : ℕ,
      conePlus P A * idempotencyDefect^[m] (genV P A C) =
        idempotencyDefect^[m] (genV P A C) * conePlus P A ∧
      coneMinus P C * idempotencyDefect^[m] (genV P A C) =
        idempotencyDefect^[m] (genV P A C) * coneMinus P C := by
    intro m
    induction m with
    | zero =>
      simp only [Function.iterate_zero, id_eq]
      exact ⟨by peirce_nf hP, by peirce_nf hP⟩
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hCommDefect _ _ ih.1, hCommDefect _ _ ih.2⟩
  rcases hConeEpoch n with ⟨hCpVn, hCmVn⟩
  have hModVn : modularTimeDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0 := by
    have h1 : (conePlus P A * coneMinus P C) * idempotencyDefect^[n] (genV P A C) =
        idempotencyDefect^[n] (genV P A C) * (conePlus P A * coneMinus P C) := by
      calc (conePlus P A * coneMinus P C) * idempotencyDefect^[n] (genV P A C)
          = conePlus P A * (coneMinus P C * idempotencyDefect^[n] (genV P A C)) := mul_assoc _ _ _
        _ = conePlus P A * (idempotencyDefect^[n] (genV P A C) * coneMinus P C) := by rw [hCmVn]
        _ = (conePlus P A * idempotencyDefect^[n] (genV P A C)) * coneMinus P C := (mul_assoc _ _ _).symm
        _ = (idempotencyDefect^[n] (genV P A C) * conePlus P A) * coneMinus P C := by rw [hCpVn]
        _ = idempotencyDefect^[n] (genV P A C) * (conePlus P A * coneMinus P C) := mul_assoc _ _ _
    have h2 : (coneMinus P C * conePlus P A) * idempotencyDefect^[n] (genV P A C) =
        idempotencyDefect^[n] (genV P A C) * (coneMinus P C * conePlus P A) := by
      calc (coneMinus P C * conePlus P A) * idempotencyDefect^[n] (genV P A C)
          = coneMinus P C * (conePlus P A * idempotencyDefect^[n] (genV P A C)) := mul_assoc _ _ _
        _ = coneMinus P C * (idempotencyDefect^[n] (genV P A C) * conePlus P A) := by rw [hCpVn]
        _ = (coneMinus P C * idempotencyDefect^[n] (genV P A C)) * conePlus P A := (mul_assoc _ _ _).symm
        _ = (idempotencyDefect^[n] (genV P A C) * coneMinus P C) * conePlus P A := by rw [hCmVn]
        _ = idempotencyDefect^[n] (genV P A C) * (coneMinus P C * conePlus P A) := mul_assoc _ _ _
    unfold modularTimeDeriv genSig comm
    rw [sub_mul, mul_sub, h1, h2, sub_self]
  have hCommJVn : comm (genJ P A C) (idempotencyDefect^[n] (genV P A C)) = 0 := by
    unfold genJ comm
    rw [sub_mul, mul_sub, hCpVn, hCmVn, sub_self]
  have hDissVn : dissipativeTimeDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0 := by
    unfold dissipativeTimeDeriv
    rw [hCommJVn]
    unfold comm
    rw [mul_zero, zero_mul, sub_self]
  have hArrowVn : arrowOfTimeGen P A C (idempotencyDefect^[n] (genV P A C)) = 0 := by
    unfold arrowOfTimeGen
    rw [hModVn, hDissVn, add_zero]
  have hInvLeft : helixWindingOpInv k P A * helixWindingOp k P A = 1 := by
    have h1 := (helical_winding_group_and_extractor hP A C 0 (-k) k).1
    have h2 : helixWindingOpInv k P A = helixWindingOp (-k) P A := by
      unfold helixWindingOpInv helixWindingOp; rw [neg_smul, ← sub_eq_add_neg]
    rw [h2, h1, neg_add_cancel]
    unfold helixWindingOp; rw [zero_smul, add_zero]
  have hRelVn :
      relationalTimeEvol k P A (idempotencyDefect^[n] (genV P A C)) =
        idempotencyDefect^[n] (genV P A C) := by
    have hUH :
        idempotencyDefect^[n] (genV P A C) * helixWindingOp k P A =
          helixWindingOp k P A * idempotencyDefect^[n] (genV P A C) := by
      unfold helixWindingOp
      rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hCpVn]
    unfold relationalTimeEvol
    calc helixWindingOpInv k P A * idempotencyDefect^[n] (genV P A C) * helixWindingOp k P A
        = helixWindingOpInv k P A * (idempotencyDefect^[n] (genV P A C) * helixWindingOp k P A) := by
          noncomm_ring
      _ = (helixWindingOpInv k P A * helixWindingOp k P A) *
          idempotencyDefect^[n] (genV P A C) := by rw [hUH]; noncomm_ring
      _ = idempotencyDefect^[n] (genV P A C) := by rw [hInvLeft, one_mul]
  rcases archetype_A115_all_mode_modular_time_evolution_and_virasoro_conservation
      hP A C r with
    ⟨_, ⟨hMPhir, _, _, _⟩⟩
  rcases archetype_A116_relational_page_wootters_clock_group_and_all_mode_virasoro_invariance
      hP A C X X k k₁ k₂ r with
    ⟨⟨_, hRAdd, _, _⟩, _⟩
  rcases archetype_A117_causal_light_cone_order_retarded_semigroup_and_star_duality
      hP hPsym F₁ B₁ D₁ F₁ B₁ D₁ with
    ⟨⟨hLeak1, _⟩, _, ⟨hStar1, _⟩⟩
  rcases archetype_A118_thermodynamic_arrow_of_time_and_all_mode_dissipative_eigenvalues
      hP hPsym A C X r with
    ⟨_, ⟨_, _, hArrowSum, _⟩⟩
  exact ⟨hChain,
         ⟨hCpVn, hModVn, hDissVn, hArrowVn, hRelVn⟩,
         ⟨hMPhir, hRAdd, hLeak1, hStar1, hArrowSum⟩⟩

end Tier9

/-! ### Part 11: Tier 10 Canonical Synthesis Theorems (`A₁₂₀ → A₁₂₄` / `I₁ → I₅` & Stage `D₃₇`: Non-Commutative Logistic Bit Variance, Nilpotent–Idempotent Peirce Split, On-Shell Bit Crystallization, Orthogonal Multi-Channel Bit Counting, and Five-Way Full-Circle Closure `D₃₇ → D₁`) -/

section Tier10Defs

variable {B : Type*} [Ring B]

/-- **Archetype `I₁` (`logisticBitPlus`):** Non-commutative soft logistic bit operator
`L_+(P, A, C) = P * (1 - Q_+(A, C)) + (1 - P) * Q_-(A, C)`. -/
def logisticBitPlus (P A C : B) : B :=
  P * (1 - qgtPlus P A C) + (1 - P) * qgtMinus P A C

/-- **Archetype `I₁` (`logisticBitMinus`):** Complementary soft logistic bit operator
`L_-(P, A, C) = (1 - P) * (1 - Q_-(A, C)) + P * Q_+(A, C) = 1 - L_+(P, A, C)`. -/
def logisticBitMinus (P A C : B) : B :=
  (1 - P) * (1 - qgtMinus P A C) + P * qgtPlus P A C

/-- **Archetype `I₁` (`logisticBitVariance`):** Non-commutative Bernoulli / logistic bit variance
`L_+(P, A, C) * L_-(P, A, C)`. -/
def logisticBitVariance (P A C : B) : B :=
  logisticBitPlus P A C * logisticBitMinus P A C

/-- **Archetype `I₅` (`cohomologyProj`):** Sheaf cohomology obstruction projector
`Π_{H¹}(P, A, C) = 1 - V(A, C)`. -/
def cohomologyProj (P A C : B) : B :=
  1 - genV P A C

/-- **Archetype `I₄` (`bitFlipGate`):** Integer-indexed unipotent bit-flip gate
`1 + k • N_+(A)` (`= helixWindingOp k P A`). -/
abbrev bitFlipGate (k : ℤ) (P A : B) : B :=
  helixWindingOp k P A

/-- **Archetype `I₄` (`bitFlipGateInv`):** Inverse integer-indexed unipotent bit-flip gate
`1 - k • N_+(A)` (`= helixWindingOpInv k P A`). -/
abbrev bitFlipGateInv (k : ℤ) (P A : B) : B :=
  helixWindingOpInv k P A

/-- **Archetype `I₄` (`bitCounterOp`):** Non-commutative bit-capacity counter
`{U⁻¹ [P, U], N_-(C)}` (`= windingNumberExtractor P C U U_inv`). -/
abbrev bitCounterOp (P C U U_inv : B) : B :=
  windingNumberExtractor P C U U_inv

end Tier10Defs

/-! ### Ring-level core of D₃₇ Archetype `I₁` -/

variable {B : Type*} [Ring B]

/-- The logistic partition and variance/defect identities are purely ring
theoretic. This separates the algebraic content of `I₁` from the additional
star-ring hypotheses used later for its self-adjointness conclusions. -/
theorem logistic_bit_variance_and_defect_duality_ring
    {P : B} (hP : P * P = P) (A C : B) :
    logisticBitPlus P A C + logisticBitMinus P A C = 1 ∧
    idempotencyDefect (logisticBitPlus P A C) = idempotencyDefect (genV P A C) ∧
    idempotencyDefect (logisticBitMinus P A C) = idempotencyDefect (genV P A C) ∧
    logisticBitVariance P A C = -idempotencyDefect (genV P A C) ∧
    logisticBitMinus P A C * logisticBitPlus P A C =
      -idempotencyDefect (genV P A C) ∧
    comm (logisticBitPlus P A C) (logisticBitMinus P A C) = 0 := by
  have hPartition : logisticBitPlus P A C + logisticBitMinus P A C = 1 := by
    unfold logisticBitPlus logisticBitMinus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hDefPlus :
      idempotencyDefect (logisticBitPlus P A C) = idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitPlus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hDefMinus :
      idempotencyDefect (logisticBitMinus P A C) = idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitMinus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hVariance :
      logisticBitVariance P A C = -idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitVariance logisticBitPlus logisticBitMinus
      qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hVarianceReverse :
      logisticBitMinus P A C * logisticBitPlus P A C =
        -idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitMinus logisticBitPlus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hComm : comm (logisticBitPlus P A C) (logisticBitMinus P A C) = 0 := by
    unfold comm
    change logisticBitVariance P A C -
      logisticBitMinus P A C * logisticBitPlus P A C = 0
    rw [hVariance, hVarianceReverse, sub_self]
  exact ⟨hPartition, hDefPlus, hDefMinus, hVariance, hVarianceReverse, hComm⟩

section Tier10

variable {B : Type*} [Ring B] [StarRing B] {P : B} (hP : P * P = P) (hPsym : star P = P)
include hP hPsym

/-- **Archetype `A₁₂₀` (`I₁`, `archetype_A120_logistic_bit_variance_partition_and_defect_duality`):**
Over any non-commutative star-ring `[Ring B] [StarRing B]` with self-adjoint idempotent
`P * P = P`, `star P = P`, and elements `X A C : B`:
1. **Universal Bernoulli Variance vs. Mandelbrot Defect (`X * (1 - X) = -δ(X)`) & Logistic Partition:**
   - `X * (1 - X) = -idempotencyDefect X`,
   - `logisticBitPlus P A C + logisticBitMinus P A C = 1`,
   - `logisticBitPlus P A C - logisticBitMinus P A C = invS P * (1 - genV P A C)`;
2. **Logistic Bit Variance Equals Minus the Horizon Metric Defect (`L_+ L_- = -δ(L_+) = -δ(V)`):**
   - `idempotencyDefect (logisticBitPlus P A C) = idempotencyDefect (genV P A C)`,
   - `idempotencyDefect (logisticBitMinus P A C) = idempotencyDefect (genV P A C)`,
   - `logisticBitVariance P A C = -idempotencyDefect (genV P A C)`,
   - `logisticBitMinus P A C * logisticBitPlus P A C = -idempotencyDefect (genV P A C)`,
   - `comm (logisticBitPlus P A C) (logisticBitMinus P A C) = 0`;
3. **Self-Adjointness on the Symmetric Horizon (`C = star A`):**
   - `star (logisticBitPlus P A (star A)) = logisticBitPlus P A (star A)`,
   - `star (logisticBitMinus P A (star A)) = logisticBitMinus P A (star A)`,
   - `star (logisticBitVariance P A (star A)) = logisticBitVariance P A (star A)`. -/
theorem archetype_A120_logistic_bit_variance_partition_and_defect_duality
    (X A C : B) :
    (X * (1 - X) = -idempotencyDefect X ∧
     logisticBitPlus P A C + logisticBitMinus P A C = 1 ∧
     logisticBitPlus P A C - logisticBitMinus P A C =
       invS P - (2 : ℤ) • genSig P A C) ∧
    (idempotencyDefect (logisticBitPlus P A C) = idempotencyDefect (genV P A C) ∧
     idempotencyDefect (logisticBitMinus P A C) = idempotencyDefect (genV P A C) ∧
     logisticBitVariance P A C = -idempotencyDefect (genV P A C) ∧
     logisticBitMinus P A C * logisticBitPlus P A C = -idempotencyDefect (genV P A C) ∧
     comm (logisticBitPlus P A C) (logisticBitMinus P A C) = 0) ∧
    (star (logisticBitPlus P A (star A)) = logisticBitPlus P A (star A) ∧
     star (logisticBitMinus P A (star A)) = logisticBitMinus P A (star A) ∧
     star (logisticBitVariance P A (star A)) = logisticBitVariance P A (star A)) := by
  have hUniv : X * (1 - X) = -idempotencyDefect X := by
    unfold idempotencyDefect; noncomm_ring
  have hPart : logisticBitPlus P A C + logisticBitMinus P A C = 1 := by
    unfold logisticBitPlus logisticBitMinus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hDiff : logisticBitPlus P A C - logisticBitMinus P A C =
      invS P - (2 : ℤ) • genSig P A C := by
    unfold logisticBitPlus logisticBitMinus qgtPlus qgtMinus genSig comm
    peirce_nf hP <;> abel_nf
  have hDefPlus : idempotencyDefect (logisticBitPlus P A C) = idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitPlus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hDefMinus : idempotencyDefect (logisticBitMinus P A C) = idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitMinus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hVar : logisticBitVariance P A C = -idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitVariance logisticBitPlus logisticBitMinus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hVarRev :
      logisticBitMinus P A C * logisticBitPlus P A C = -idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitMinus logisticBitPlus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hComm : comm (logisticBitPlus P A C) (logisticBitMinus P A C) = 0 := by
    unfold comm
    change logisticBitVariance P A C - logisticBitMinus P A C * logisticBitPlus P A C = 0
    rw [hVar, hVarRev, sub_self]
  have hStarCone : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hStarConeM : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hStarCone, star_star]
  have hStarQp : star (qgtPlus P A (star A)) = qgtPlus P A (star A) := by
    unfold qgtPlus; rw [star_mul, hStarCone, hStarConeM]
  have hStarQm : star (qgtMinus P A (star A)) = qgtMinus P A (star A) := by
    unfold qgtMinus; rw [star_mul, hStarCone, hStarConeM]
  have hPQp : P * qgtPlus P A (star A) = qgtPlus P A (star A) * P := by
    unfold qgtPlus; peirce_nf hP
  have hPQm : (1 - P) * qgtMinus P A (star A) = qgtMinus P A (star A) * (1 - P) := by
    unfold qgtMinus; peirce_nf hP
  have hStarLPlus : star (logisticBitPlus P A (star A)) = logisticBitPlus P A (star A) := by
    unfold logisticBitPlus
    rw [star_add, star_mul, star_mul, star_sub, star_sub, star_one, hPsym, hStarQp, hStarQm]
    calc (1 - qgtPlus P A (star A)) * P + qgtMinus P A (star A) * (1 - P)
        = P - qgtPlus P A (star A) * P + qgtMinus P A (star A) * (1 - P) := by noncomm_ring
      _ = P - P * qgtPlus P A (star A) + (1 - P) * qgtMinus P A (star A) := by
          rw [← hPQp, ← hPQm]
      _ = P * (1 - qgtPlus P A (star A)) + (1 - P) * qgtMinus P A (star A) := by noncomm_ring
  have hStarLMinus : star (logisticBitMinus P A (star A)) = logisticBitMinus P A (star A) := by
    unfold logisticBitMinus
    rw [star_add, star_mul, star_mul, star_sub, star_sub, star_one, hPsym, hStarQp, hStarQm]
    calc (1 - qgtMinus P A (star A)) * (1 - P) + qgtPlus P A (star A) * P
        = (1 - P) - qgtMinus P A (star A) * (1 - P) + qgtPlus P A (star A) * P := by noncomm_ring
      _ = (1 - P) - (1 - P) * qgtMinus P A (star A) + P * qgtPlus P A (star A) := by
          rw [← hPQm, ← hPQp]
      _ = (1 - P) * (1 - qgtMinus P A (star A)) + P * qgtPlus P A (star A) := by noncomm_ring
  have hStarVar : star (logisticBitVariance P A (star A)) = logisticBitVariance P A (star A) := by
    unfold logisticBitVariance
    rw [star_mul, hStarLPlus, hStarLMinus]
    have hVarStar :
        logisticBitVariance P A (star A) = -idempotencyDefect (genV P A (star A)) := by
      unfold idempotencyDefect logisticBitVariance logisticBitPlus logisticBitMinus qgtPlus qgtMinus
      peirce_nf hP <;> abel_nf
    have hVarRevStar :
        logisticBitMinus P A (star A) * logisticBitPlus P A (star A) =
          -idempotencyDefect (genV P A (star A)) := by
      unfold idempotencyDefect logisticBitMinus logisticBitPlus qgtPlus qgtMinus
      peirce_nf hP <;> abel_nf
    have hVarPlusStar : logisticBitPlus P A (star A) * logisticBitMinus P A (star A) =
        -idempotencyDefect (genV P A (star A)) := by
      change logisticBitVariance P A (star A) = _
      exact hVarStar
    have hCommStar : comm (logisticBitPlus P A (star A))
        (logisticBitMinus P A (star A)) = 0 := by
      unfold comm
      rw [hVarPlusStar, hVarRevStar]
      abel
    exact (sub_eq_zero.mp hCommStar).symm
  exact ⟨⟨hUniv, hPart, hDiff⟩,
         ⟨hDefPlus, hDefMinus, hVar, hVarRev, hComm⟩,
         ⟨hStarLPlus, hStarLMinus, hStarVar⟩⟩

omit [StarRing B] hPsym in
/-- **Archetype `A₁₂₁` (`I₂`, `archetype_A121_nilpotent_idempotent_peirce_split_and_all_mode_virasoro_emergence`):**
Over any non-commutative ring `[Ring B]` with idempotent `P * P = P`, elements `A C : B`, and mode
index `r : ℕ`, let `Phi_r = genPhi P A C * opPow r (genV P A C)` and
`J_r = genJ P A C * opPow r (genV P A C)`:
1. **Sharp Binary Bit & Single-Cone Tilted Graph Idempotents (`δ(P) = 0`, `δ(P - N_+) = 0`):**
   - `idempotencyDefect P = 0` and `idempotencyDefect (1 - P) = 0`,
   - `conePlus P A * conePlus P A = 0` and `coneMinus P C * coneMinus P C = 0`,
   - `idempotencyDefect (P - conePlus P A) = 0` and `idempotencyDefect (P + coneMinus P C) = 0`;
2. **Bilateral Bit-Flip Superposition Generates the Metric `±V` & All-Mode Virasoro Tower `±L_{2r}^+`:**
   - `idempotencyDefect (P + genPhi P A C) = genV P A C`,
   - `idempotencyDefect (P + genJ P A C) = -genV P A C`,
   - `idempotencyDefect (P + Phi_r) = virasoroModeEven (r + r) P A C`,
   - `idempotencyDefect (P + J_r) = -virasoroModeEven (r + r) P A C`,
   - `idempotencyDefect (P + Phi_r) - idempotencyDefect (P + J_r) =`
     `(2 : ℤ) • virasoroModeEven (r + r) P A C`. -/
theorem archetype_A121_nilpotent_idempotent_peirce_split_and_all_mode_virasoro_emergence
    (A C : B) (r : ℕ) :
    let Phi_r := genPhi P A C * opPow r (genV P A C)
    let J_r := genJ P A C * opPow r (genV P A C)
    (idempotencyDefect P = 0 ∧
     idempotencyDefect (1 - P) = 0 ∧
     conePlus P A * conePlus P A = 0 ∧
     coneMinus P C * coneMinus P C = 0 ∧
     idempotencyDefect (P - conePlus P A) = 0 ∧
     idempotencyDefect (P + coneMinus P C) = 0) ∧
    (idempotencyDefect (P + genPhi P A C) = genV P A C ∧
     idempotencyDefect (P + genJ P A C) = -genV P A C ∧
     idempotencyDefect (P + Phi_r) = virasoroModeEven (r + r) P A C ∧
     idempotencyDefect (P + J_r) = -virasoroModeEven (r + r) P A C ∧
     idempotencyDefect (P + Phi_r) - idempotencyDefect (P + J_r) =
       (2 : ℤ) • virasoroModeEven (r + r) P A C) := by
  intro Phi_r J_r
  have hDP : idempotencyDefect P = 0 := by
    unfold idempotencyDefect; rw [hP, sub_self]
  have hD1P : idempotencyDefect (1 - P) = 0 := by
    unfold idempotencyDefect; peirce_nf hP <;> abel_nf
  have hCpSq : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have hCmSq : coneMinus P C * coneMinus P C = 0 := by peirce_nf hP
  have hDTiltP : idempotencyDefect (P - conePlus P A) = 0 := by
    unfold idempotencyDefect; peirce_nf hP <;> abel_nf
  have hDTiltM : idempotencyDefect (P + coneMinus P C) = 0 := by
    unfold idempotencyDefect; peirce_nf hP <;> abel_nf
  have hDPhi0 : idempotencyDefect (P + genPhi P A C) = genV P A C := by
    unfold idempotencyDefect
    peirce_nf hP <;> abel_nf
  have hDJ0 : idempotencyDefect (P + genJ P A C) = -genV P A C := by
    unfold idempotencyDefect
    peirce_nf hP <;> abel_nf
  rcases opPow_genV_comm_invS_and_cones hP A C r with ⟨_, hCpOp, hCmOp⟩
  have hPPhi : P * genPhi P A C + genPhi P A C * P = genPhi P A C := by peirce_nf hP
  have hPJ : P * genJ P A C + genJ P A C * P = genJ P A C := by peirce_nf hP
  have hPOp : P * opPow r (genV P A C) = opPow r (genV P A C) * P :=
    (opPow_genV_comm_idem hP A C r).1
  have hPhiOpComm : genPhi P A C * opPow r (genV P A C) = opPow r (genV P A C) * genPhi P A C := by
    unfold genPhi
    rw [add_mul, mul_add, hCpOp, hCmOp]
  have hJOpComm : genJ P A C * opPow r (genV P A C) = opPow r (genV P A C) * genJ P A C := by
    unfold genJ
    rw [sub_mul, mul_sub, hCpOp, hCmOp]
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
  have hJSq : genJ P A C * genJ P A C = -genV P A C := by peirce_nf hP
  have hPhi_r_sq : Phi_r * Phi_r = virasoroModeEven (r + r) P A C := by
    change (genPhi P A C * opPow r (genV P A C)) * (genPhi P A C * opPow r (genV P A C)) =
      opPow (r + r + 1) (genV P A C)
    calc (genPhi P A C * opPow r (genV P A C)) * (genPhi P A C * opPow r (genV P A C))
        = genPhi P A C * (opPow r (genV P A C) * genPhi P A C) * opPow r (genV P A C) := by
          noncomm_ring
      _ = (genPhi P A C * genPhi P A C) * (opPow r (genV P A C) * opPow r (genV P A C)) := by
          rw [← hPhiOpComm]; noncomm_ring
      _ = genV P A C * opPow (r + r) (genV P A C) := by
          rw [hPhiSq, ← opPow_add r r (genV P A C)]
      _ = opPow (r + r + 1) (genV P A C) := by
          rw [mul_opPow_comm (r + r) (genV P A C)]; rfl
  have hJ_r_sq : J_r * J_r = -virasoroModeEven (r + r) P A C := by
    change (genJ P A C * opPow r (genV P A C)) * (genJ P A C * opPow r (genV P A C)) =
      -opPow (r + r + 1) (genV P A C)
    calc (genJ P A C * opPow r (genV P A C)) * (genJ P A C * opPow r (genV P A C))
        = genJ P A C * (opPow r (genV P A C) * genJ P A C) * opPow r (genV P A C) := by
          noncomm_ring
      _ = (genJ P A C * genJ P A C) * (opPow r (genV P A C) * opPow r (genV P A C)) := by
          rw [← hJOpComm]; noncomm_ring
      _ = -genV P A C * opPow (r + r) (genV P A C) := by
          rw [hJSq, ← opPow_add r r (genV P A C)]
      _ = -(genV P A C * opPow (r + r) (genV P A C)) := neg_mul _ _
      _ = -opPow (r + r + 1) (genV P A C) := by
          rw [mul_opPow_comm (r + r) (genV P A C)]; rfl
  have hAntiOdd : ∀ U : B, P * U + U * P = U →
      P * (U * opPow r (genV P A C)) + (U * opPow r (genV P A C)) * P =
        U * opPow r (genV P A C) := by
    intro U hPU
    have hUP : U * (opPow r (genV P A C) * P) = (U * P) * opPow r (genV P A C) := by
      calc U * (opPow r (genV P A C) * P)
          = U * (P * opPow r (genV P A C)) := by rw [← hPOp]
        _ = (U * P) * opPow r (genV P A C) := (mul_assoc _ _ _).symm
    calc P * (U * opPow r (genV P A C)) + (U * opPow r (genV P A C)) * P
        = (P * U) * opPow r (genV P A C) + U * (opPow r (genV P A C) * P) := by noncomm_ring
      _ = (P * U + U * P) * opPow r (genV P A C) := by rw [hUP, add_mul]
      _ = U * opPow r (genV P A C) := by rw [hPU]
  have hDefOdd : ∀ W : B, P * W + W * P = W → idempotencyDefect (P + W) = W * W := by
    intro W hPW
    unfold idempotencyDefect
    calc (P + W) * (P + W) - (P + W)
        = (P * P - P) + (P * W + W * P - W) + W * W := by noncomm_ring
      _ = W * W := by rw [hP, hPW]; noncomm_ring
  have hDPhir : idempotencyDefect (P + Phi_r) = virasoroModeEven (r + r) P A C := by
    rw [hDefOdd Phi_r (hAntiOdd (genPhi P A C) hPPhi), hPhi_r_sq]
  have hDJr : idempotencyDefect (P + J_r) = -virasoroModeEven (r + r) P A C := by
    rw [hDefOdd J_r (hAntiOdd (genJ P A C) hPJ), hJ_r_sq]
  have hDDiff :
      idempotencyDefect (P + Phi_r) - idempotencyDefect (P + J_r) =
        (2 : ℤ) • virasoroModeEven (r + r) P A C := by
    rw [hDPhir, hDJr, sub_neg_eq_add, two_zsmul]
  exact ⟨⟨hDP, hD1P, hCpSq, hCmSq, hDTiltP, hDTiltM⟩,
         ⟨hDPhi0, hDJ0, hDPhir, hDJr, hDDiff⟩⟩

omit [StarRing B] hPsym in
/-- **Archetype `A₁₂₂` (`I₃`, `archetype_A122_on_shell_bit_crystallization_and_daughter_idempotent_equivalence`):**
Over any non-commutative ring `[Ring B]` with idempotent `P * P = P` and elements `A C : B`:
1. **Four-Way On-Shell Bit Crystallization Equivalence (`L_+² = L_+ ↔ L_-² = L_- ↔ L_+ L_- = 0 ↔ δ(V) = 0`):**
   - `logisticBitPlus P A C * logisticBitPlus P A C = logisticBitPlus P A C ↔ idempotencyDefect (genV P A C) = 0`,
   - `logisticBitMinus P A C * logisticBitMinus P A C = logisticBitMinus P A C ↔ idempotencyDefect (genV P A C) = 0`,
   - `logisticBitVariance P A C = 0 ↔ idempotencyDefect (genV P A C) = 0`,
   - `genV P A C * genV P A C = genV P A C ↔ logisticBitVariance P A C = 0`;
2. **Daughter Sub-Idempotent Defect Decomposition (`δ(Q_+) + δ(Q_-) = δ(V)`):**
   - `idempotencyDefect (qgtPlus P A C) + idempotencyDefect (qgtMinus P A C) = idempotencyDefect (genV P A C)`,
   - `P * idempotencyDefect (genV P A C) = idempotencyDefect (qgtPlus P A C)`,
   - `(1 - P) * idempotencyDefect (genV P A C) = idempotencyDefect (qgtMinus P A C)`. -/
theorem archetype_A122_on_shell_bit_crystallization_and_daughter_idempotent_equivalence
    (A C : B) :
    ((logisticBitPlus P A C * logisticBitPlus P A C = logisticBitPlus P A C ↔
        idempotencyDefect (genV P A C) = 0) ∧
     (logisticBitMinus P A C * logisticBitMinus P A C = logisticBitMinus P A C ↔
        idempotencyDefect (genV P A C) = 0) ∧
     (logisticBitVariance P A C = 0 ↔
        idempotencyDefect (genV P A C) = 0) ∧
     (genV P A C * genV P A C = genV P A C ↔
        logisticBitVariance P A C = 0)) ∧
    (idempotencyDefect (qgtPlus P A C) + idempotencyDefect (qgtMinus P A C) =
       idempotencyDefect (genV P A C) ∧
     P * idempotencyDefect (genV P A C) = idempotencyDefect (qgtPlus P A C) ∧
     (1 - P) * idempotencyDefect (genV P A C) = idempotencyDefect (qgtMinus P A C)) := by
  have hDefPlus : idempotencyDefect (logisticBitPlus P A C) = idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitPlus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hDefMinus : idempotencyDefect (logisticBitMinus P A C) = idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitMinus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hVar : logisticBitVariance P A C = -idempotencyDefect (genV P A C) := by
    unfold idempotencyDefect logisticBitVariance logisticBitPlus logisticBitMinus qgtPlus qgtMinus
    peirce_nf hP <;> abel_nf
  have hEq1 :
      logisticBitPlus P A C * logisticBitPlus P A C = logisticBitPlus P A C ↔
        idempotencyDefect (genV P A C) = 0 := by
    rw [← sub_eq_zero]
    change idempotencyDefect (logisticBitPlus P A C) = 0 ↔ idempotencyDefect (genV P A C) = 0
    rw [hDefPlus]
  have hEq2 :
      logisticBitMinus P A C * logisticBitMinus P A C = logisticBitMinus P A C ↔
        idempotencyDefect (genV P A C) = 0 := by
    rw [← sub_eq_zero]
    change idempotencyDefect (logisticBitMinus P A C) = 0 ↔ idempotencyDefect (genV P A C) = 0
    rw [hDefMinus]
  have hEq3 : logisticBitVariance P A C = 0 ↔ idempotencyDefect (genV P A C) = 0 := by
    rw [hVar, neg_eq_zero]
  have hEq4 : genV P A C * genV P A C = genV P A C ↔ logisticBitVariance P A C = 0 := by
    rw [← sub_eq_zero, hEq3]
    rfl
  have hDaughterSum :
      idempotencyDefect (qgtPlus P A C) + idempotencyDefect (qgtMinus P A C) =
        idempotencyDefect (genV P A C) := by
    exact (genV_defect_cycle_split hP A C).symm
  have hQpFixed : P * idempotencyDefect (qgtPlus P A C) =
      idempotencyDefect (qgtPlus P A C) := by
    unfold idempotencyDefect qgtPlus
    peirce_nf hP <;> abel_nf
  have hQmKilled : P * idempotencyDefect (qgtMinus P A C) = 0 := by
    unfold idempotencyDefect qgtMinus
    peirce_nf hP <;> abel_nf
  have hDaughterP : P * idempotencyDefect (genV P A C) = idempotencyDefect (qgtPlus P A C) := by
    calc
      P * idempotencyDefect (genV P A C) =
          P * (idempotencyDefect (qgtPlus P A C) + idempotencyDefect (qgtMinus P A C)) := by
        rw [← hDaughterSum]
      _ = idempotencyDefect (qgtPlus P A C) := by
        rw [mul_add, hQpFixed, hQmKilled, add_zero]
  have hQmFixed : (1 - P) * idempotencyDefect (qgtMinus P A C) =
      idempotencyDefect (qgtMinus P A C) := by
    unfold idempotencyDefect qgtMinus
    peirce_nf hP <;> abel_nf
  have hQpKilled : (1 - P) * idempotencyDefect (qgtPlus P A C) = 0 := by
    unfold idempotencyDefect qgtPlus
    peirce_nf hP <;> abel_nf
  have hDaughter1P :
      (1 - P) * idempotencyDefect (genV P A C) = idempotencyDefect (qgtMinus P A C) := by
    calc
      (1 - P) * idempotencyDefect (genV P A C) =
          (1 - P) * (idempotencyDefect (qgtPlus P A C) + idempotencyDefect (qgtMinus P A C)) := by
        rw [← hDaughterSum]
      _ = idempotencyDefect (qgtMinus P A C) := by
        rw [mul_add, hQpKilled, hQmFixed, zero_add]
  exact ⟨⟨hEq1, hEq2, hEq3, hEq4⟩,
         ⟨hDaughterSum, hDaughterP, hDaughter1P⟩⟩

omit [StarRing B] hPsym in
/-- **Archetype `A₁₂₃` (`I₄`, `archetype_A123_multi_channel_bit_counting_and_orthogonal_defect_additivity`):**
Over any non-commutative ring `[Ring B]` with idempotent `P * P = P`, mutually orthogonal elements
`V₁ V₂ : B` (`V₁ * V₂ = 0`, `V₂ * V₁ = 0`), elements `A C : B`, and integer counts `k k₁ k₂ : ℤ`:
1. **Orthogonal Multi-Channel Defect, Dual-Defect & Variance Additivity:**
   - `idempotencyDefect (V₁ + V₂) = idempotencyDefect V₁ + idempotencyDefect V₂`,
   - `idempotencyDefectBar (V₁ + V₂) = idempotencyDefectBar V₁ + idempotencyDefectBar V₂`,
   - `(V₁ + V₂) * (1 - (V₁ + V₂)) = V₁ * (1 - V₁) + V₂ * (1 - V₂)`;
2. **Integer Bit-Capacity Counter & Additive Flux Group Law:**
   - `bitFlipGate k₁ P A * bitFlipGate k₂ P A = bitFlipGate (k₁ + k₂) P A`,
   - `bitCounterOp P C (bitFlipGate k P A) (bitFlipGateInv k P A) = k • genV P A C`,
   - `bitCounterOp P C (bitFlipGate k₁ P A) (bitFlipGateInv k₁ P A) +`
     `bitCounterOp P C (bitFlipGate k₂ P A) (bitFlipGateInv k₂ P A) = (k₁ + k₂) • genV P A C`. -/
theorem archetype_A123_multi_channel_bit_counting_and_orthogonal_defect_additivity
    {V₁ V₂ : B} (h12 : V₁ * V₂ = 0) (h21 : V₂ * V₁ = 0) (A C : B) (k k₁ k₂ : ℤ) :
    (idempotencyDefect (V₁ + V₂) = idempotencyDefect V₁ + idempotencyDefect V₂ ∧
     idempotencyDefectBar (V₁ + V₂) = idempotencyDefectBar V₁ + idempotencyDefectBar V₂ ∧
     (V₁ + V₂) * (1 - (V₁ + V₂)) = V₁ * (1 - V₁) + V₂ * (1 - V₂)) ∧
    (bitFlipGate k₁ P A * bitFlipGate k₂ P A = bitFlipGate (k₁ + k₂) P A ∧
     bitCounterOp P C (bitFlipGate k P A) (bitFlipGateInv k P A) = k • genV P A C ∧
     bitCounterOp P C (bitFlipGate k₁ P A) (bitFlipGateInv k₁ P A) +
       bitCounterOp P C (bitFlipGate k₂ P A) (bitFlipGateInv k₂ P A) =
       (k₁ + k₂) • genV P A C) := by
  have hDefAdd : idempotencyDefect (V₁ + V₂) = idempotencyDefect V₁ + idempotencyDefect V₂ := by
    unfold idempotencyDefect
    rw [add_mul, mul_add, mul_add, h12, h21, add_zero, zero_add]
    abel
  have hDefBarAdd :
      idempotencyDefectBar (V₁ + V₂) = idempotencyDefectBar V₁ + idempotencyDefectBar V₂ := by
    unfold idempotencyDefectBar
    rw [add_mul, mul_add, mul_add, h12, h21, add_zero, zero_add]
    abel
  have hVarAdd : (V₁ + V₂) * (1 - (V₁ + V₂)) = V₁ * (1 - V₁) + V₂ * (1 - V₂) := by
    have hU : ∀ W : B, W * (1 - W) = -idempotencyDefect W := by
      intro W; unfold idempotencyDefect; noncomm_ring
    rw [hU (V₁ + V₂), hU V₁, hU V₂, hDefAdd, neg_add]
  rcases helical_winding_group_and_extractor hP A C k k₁ k₂ with ⟨hGateMul, _, _, hCountK⟩
  have hCount1 := (helical_winding_group_and_extractor hP A C k₁ 0 0).2.2.2
  have hCount2 := (helical_winding_group_and_extractor hP A C k₂ 0 0).2.2.2
  have hCountSum :
      bitCounterOp P C (bitFlipGate k₁ P A) (bitFlipGateInv k₁ P A) +
        bitCounterOp P C (bitFlipGate k₂ P A) (bitFlipGateInv k₂ P A) =
        (k₁ + k₂) • genV P A C := by
    change windingNumberExtractor P C (helixWindingOp k₁ P A) (helixWindingOpInv k₁ P A) +
      windingNumberExtractor P C (helixWindingOp k₂ P A) (helixWindingOpInv k₂ P A) =
      (k₁ + k₂) • genV P A C
    rw [hCount1, hCount2, add_smul]
  exact ⟨⟨hDefAdd, hDefBarAdd, hVarAdd⟩,
         ⟨hGateMul, hCountK, hCountSum⟩⟩

omit [StarRing B] hPsym in
/-- **Archetype `A₁₂₄` (`I₅` & Stage `D₃₇`, `archetype_A124_five_way_full_circle_unification_and_stage_D37_synthesis`):**
Master Stage `D₃₇` synthesis unifying Archetypes `A₁₂₀ → A₁₂₃` (`I₁ → I₄`) with the Five-Way
Full-Circle Unification Identity (`I₅`) closing Stage `D₃₇` back onto Stage `D₁` (`idempotencyDefect`)
in the 124-stage causal poset `MasterSpineStage`:
1. **Strict Causal Poset Chain `A₁₁₉ < A₁₂₀ < A₁₂₁ < A₁₂₂ < A₁₂₃ < A₁₂₄`:**
   - `MasterSpineStage.A119 < MasterSpineStage.A120`,
   - `MasterSpineStage.A120 < MasterSpineStage.A121`,
   - `MasterSpineStage.A121 < MasterSpineStage.A122`,
   - `MasterSpineStage.A122 < MasterSpineStage.A123`,
   - `MasterSpineStage.A123 < MasterSpineStage.A124`;
2. **The Five-Way Full-Circle Unification Identity (`D₃₇ → D₁`):**
   - `-logisticBitVariance P A C = idempotencyDefect (genV P A C)` (Minus Logistic Bit Variance),
   - `idempotencyDefect (logisticBitPlus P A C) = idempotencyDefect (genV P A C)` (Logistic Bit Defect),
   - `-(cohomologyProj P A C * genV P A C) = idempotencyDefect (genV P A C)` (Cohomology Obstruction),
   - `zornNorm P (genV P A C + genPhi P A C) = idempotencyDefect (genV P A C)` (Zorn Quadratic Norm),
   - `idempotencyDefectBar (genPhi P A C) * idempotencyDefect (genPhi P A C) =`
     `idempotencyDefect (genV P A C)` (Goncharov Duplication Product);
3. **Complete Stage `D₃₇` Synthesis & Time-Stationarity of `logisticBitVariance`:**
   - `logisticBitPlus P A C + logisticBitMinus P A C = 1`,
   - `idempotencyDefect (P - conePlus P A) = 0` and
     `idempotencyDefect (P + genPhi P A C * opPow r (genV P A C)) = virasoroModeEven (r + r) P A C`,
   - `logisticBitPlus P A C * logisticBitPlus P A C = logisticBitPlus P A C ↔`
     `idempotencyDefect (genV P A C) = 0`,
   - `idempotencyDefect (V₁ + V₂) = idempotencyDefect V₁ + idempotencyDefect V₂` and
     `bitCounterOp P C (bitFlipGate k P A) (bitFlipGateInv k P A) = k • genV P A C`,
   - `modularTimeDeriv P A C (logisticBitVariance P A C) = 0` and
     `dissipativeTimeDeriv P A C (logisticBitVariance P A C) = 0`. -/
theorem archetype_A124_five_way_full_circle_unification_and_stage_D37_synthesis
    {V₁ V₂ : B} (h12 : V₁ * V₂ = 0) (h21 : V₂ * V₁ = 0) (A C : B) (k : ℤ) (r : ℕ) :
    (MasterSpineStage.A119 < MasterSpineStage.A120 ∧
     MasterSpineStage.A120 < MasterSpineStage.A121 ∧
     MasterSpineStage.A121 < MasterSpineStage.A122 ∧
     MasterSpineStage.A122 < MasterSpineStage.A123 ∧
     MasterSpineStage.A123 < MasterSpineStage.A124) ∧
    (-logisticBitVariance P A C = idempotencyDefect (genV P A C) ∧
     idempotencyDefect (logisticBitPlus P A C) = idempotencyDefect (genV P A C) ∧
     -(cohomologyProj P A C * genV P A C) = idempotencyDefect (genV P A C) ∧
     zornNorm P (genV P A C + genPhi P A C) = idempotencyDefect (genV P A C) ∧
     idempotencyDefectBar (genPhi P A C) * idempotencyDefect (genPhi P A C) =
       idempotencyDefect (genV P A C)) ∧
    (logisticBitPlus P A C + logisticBitMinus P A C = 1 ∧
     idempotencyDefect (P - conePlus P A) = 0 ∧
     idempotencyDefect (P + genPhi P A C * opPow r (genV P A C)) =
       virasoroModeEven (r + r) P A C ∧
     (logisticBitPlus P A C * logisticBitPlus P A C = logisticBitPlus P A C ↔
       idempotencyDefect (genV P A C) = 0) ∧
     idempotencyDefect (V₁ + V₂) = idempotencyDefect V₁ + idempotencyDefect V₂ ∧
     bitCounterOp P C (bitFlipGate k P A) (bitFlipGateInv k P A) = k • genV P A C ∧
     modularTimeDeriv P A C (logisticBitVariance P A C) = 0 ∧
     dissipativeTimeDeriv P A C (logisticBitVariance P A C) = 0) := by
  have hChain :
      MasterSpineStage.A119 < MasterSpineStage.A120 ∧
      MasterSpineStage.A120 < MasterSpineStage.A121 ∧
      MasterSpineStage.A121 < MasterSpineStage.A122 ∧
      MasterSpineStage.A122 < MasterSpineStage.A123 ∧
      MasterSpineStage.A123 < MasterSpineStage.A124 := by
    decide
  rcases logistic_bit_variance_and_defect_duality_ring hP A C with
    ⟨hPart, hDefPlus, _, hVariance, _, _⟩
  have hU1 : -logisticBitVariance P A C = idempotencyDefect (genV P A C) := by
    rw [hVariance, neg_neg]
  have hU2 :
      idempotencyDefect (logisticBitPlus P A C) = idempotencyDefect (genV P A C) :=
    hDefPlus
  have hU3 : -(cohomologyProj P A C * genV P A C) = idempotencyDefect (genV P A C) := by
    unfold cohomologyProj idempotencyDefect
    noncomm_ring
  have hU4 : zornNorm P (genV P A C + genPhi P A C) = idempotencyDefect (genV P A C) := by
    simpa [zornNorm, zornConj, parityConj] using metric_phi_parity_product hP A C
  have hU5 :
      idempotencyDefectBar (genPhi P A C) * idempotencyDefect (genPhi P A C) =
        idempotencyDefect (genV P A C) := by
    rw [idempotencyDefectBar_eq_neg]
    exact (genPhi_defect_product hP A C).1
  rcases archetype_A121_nilpotent_idempotent_peirce_split_and_all_mode_virasoro_emergence
      hP A C r with
    ⟨⟨_, _, _, _, hTiltP, _⟩, ⟨_, _, hDPhir, _, _⟩⟩
  rcases archetype_A122_on_shell_bit_crystallization_and_daughter_idempotent_equivalence
      hP A C with
    ⟨⟨hCryst, _, _, _⟩, _⟩
  rcases archetype_A123_multi_channel_bit_counting_and_orthogonal_defect_additivity
      hP h12 h21 A C k 0 0 with
    ⟨⟨hDefAdd, _, _⟩, ⟨_, hCountK, _⟩⟩
  have hModVar : modularTimeDeriv P A C (logisticBitVariance P A C) = 0 := by
    unfold modularTimeDeriv logisticBitVariance logisticBitPlus logisticBitMinus qgtPlus qgtMinus
    peirce_nf hP
  have hDissVar : dissipativeTimeDeriv P A C (logisticBitVariance P A C) = 0 := by
    unfold dissipativeTimeDeriv logisticBitVariance logisticBitPlus logisticBitMinus qgtPlus qgtMinus
    peirce_nf hP
  exact ⟨hChain,
         ⟨hU1, hU2, hU3, hU4, hU5⟩,
         ⟨hPart, hTiltP, hDPhir, hCryst, hDefAdd, hCountK, hModVar, hDissVar⟩⟩

end Tier10

/-! ### Transcript A₇₆: All-scale wave and core equations -/

/-- At every daughter scale and every Mandelbrot defect depth, the odd
Tetraktys modes satisfy the quadratic telegrapher equation. The even defect
and chiral branch satisfy its core equation, with the final `-4 V²` term
absent. This is the transcript A₇₆ claim, distinct from the existing A₇₆
decoder package above. -/
theorem archetype_A76_all_scale_fractal_telegrapher_wave_and_core_relaxation_equations
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let Pₖ := daughterIdemTower k P A
    let Vₖ := genV Pₖ A C
    let Φₖ := genPhi Pₖ A C
    let Jₖ := genJ Pₖ A C
    let Vₖₙ := mandelbrotTower n Vₖ
    let Sigₖₙ := chiralFractalBranch n Pₖ A C
    curvatureDoubleCommutator Pₖ A C
        (curvatureDoubleCommutator Pₖ A C (Φₖ * Vₖₙ)) +
      (4 : ℤ) • (Vₖ * curvatureDoubleCommutator Pₖ A C (Φₖ * Vₖₙ)) -
      (4 : ℤ) • ((Vₖ * Vₖ) * (Φₖ * Vₖₙ)) = 0 ∧
    curvatureDoubleCommutator Pₖ A C
        (curvatureDoubleCommutator Pₖ A C (Jₖ * Vₖₙ)) +
      (4 : ℤ) • (Vₖ * curvatureDoubleCommutator Pₖ A C (Jₖ * Vₖₙ)) -
      (4 : ℤ) • ((Vₖ * Vₖ) * (Jₖ * Vₖₙ)) = 0 ∧
    curvatureDoubleCommutator Pₖ A C
        (curvatureDoubleCommutator Pₖ A C Vₖₙ) +
      (4 : ℤ) • (Vₖ * curvatureDoubleCommutator Pₖ A C Vₖₙ) = 0 ∧
    curvatureDoubleCommutator Pₖ A C
        (curvatureDoubleCommutator Pₖ A C Sigₖₙ) +
      (4 : ℤ) • (Vₖ * curvatureDoubleCommutator Pₖ A C Sigₖₙ) = 0 := by
  intro Pₖ Vₖ Φₖ Jₖ Vₖₙ Sigₖₙ
  have hPₖ : Pₖ * Pₖ = Pₖ := by
    dsimp [Pₖ, daughterIdemTower]
    induction k with
    | zero => exact hP
    | succ k ih =>
        dsimp [daughterIdemTower] at *
        peirce_nf ih
  have hDepth : Vₖₙ = idempotencyDefect^[n + 1] Vₖ := by
    dsimp [Vₖₙ]
    exact mandelbrotTower_eq_idempotencyDefect_iterate n Vₖ
  have hOdd := curvatureDoubleCommutator_quadratic_odd_defect_iterates
    hPₖ A C (n + 1)
  have hEven := curvatureDoubleCommutator_even_defect_iterates
    hPₖ A C (n + 1)
  have hPull : ∀ Z : B,
      curvatureDoubleCommutator Pₖ A C (Z * Vₖₙ) =
        curvatureDoubleCommutator Pₖ A C Z * Vₖₙ := by
    intro Z
    rw [hDepth]
    exact curvatureDoubleCommutator_mul_genV_defect_iterate hPₖ A C Z (n + 1)
  have hSigDepth : Sigₖₙ = qgtDefectDiff Pₖ A C (n + 1) := by
    change mandelbrotTower n (qgtPlus Pₖ A C) -
        mandelbrotTower n (qgtMinus Pₖ A C) = _
    rw [mandelbrotTower_eq_idempotencyDefect_iterate,
        mandelbrotTower_eq_idempotencyDefect_iterate]
    rfl
  have hVcommPhi : genPhi Pₖ A C * Vₖ = Vₖ * genPhi Pₖ A C := by
    dsimp [Vₖ]
    exact sub_eq_zero.mp (by peirce_nf hPₖ)
  have hVcommSig : genSig Pₖ A C * Vₖ = Vₖ * genSig Pₖ A C := by
    dsimp [Vₖ]
    exact sub_eq_zero.mp (by peirce_nf hPₖ)
  have hLeft : ∀ Z : B,
      curvatureDoubleCommutator Pₖ A C (Vₖ * Z) =
        Vₖ * curvatureDoubleCommutator Pₖ A C Z := by
    intro Z
    have hCommLeft : ∀ (G Y : B), G * Vₖ = Vₖ * G →
        comm G (Vₖ * Y) = Vₖ * comm G Y := by
      intro G Y hG
      unfold comm
      calc
        G * (Vₖ * Y) - (Vₖ * Y) * G = (G * Vₖ) * Y - Vₖ * (Y * G) := by
          simp only [mul_assoc]
        _ = Vₖ * (G * Y - Y * G) := by
          rw [hG]
          simp only [mul_sub, mul_assoc]
    have hSig := hCommLeft (genSig Pₖ A C) Z hVcommSig
    have hPhi := hCommLeft (genPhi Pₖ A C) Z hVcommPhi
    have hPhi₂ := hCommLeft (genPhi Pₖ A C)
      (comm (genPhi Pₖ A C) Z) hVcommPhi
    unfold curvatureDoubleCommutator derivSqPhi
    rw [hSig, hPhi, hPhi₂]
    simp only [mul_add, neg_mul]
    rw [mul_neg]
  have hNegFour : ∀ Z : B,
      curvatureDoubleCommutator Pₖ A C (-((4 : ℤ) • Z)) =
        -((4 : ℤ) • curvatureDoubleCommutator Pₖ A C Z) := by
    intro Z
    have hAdd : ∀ X Y : B,
        curvatureDoubleCommutator Pₖ A C (X + Y) =
          curvatureDoubleCommutator Pₖ A C X +
            curvatureDoubleCommutator Pₖ A C Y := by
      intro X Y
      simp only [curvatureDoubleCommutator, derivSqPhi, comm,
        add_mul, mul_add, sub_mul, mul_sub, neg_add]
      abel
    let L : B →+ B := AddMonoidHom.mk'
      (curvatureDoubleCommutator Pₖ A C) hAdd
    have hPos := L.map_zsmul (4 : ℤ) Z
    change L (-((4 : ℤ) • Z)) = -((4 : ℤ) • L Z)
    calc
      L (-((4 : ℤ) • Z)) = -L ((4 : ℤ) • Z) := map_neg L _
      _ = -((4 : ℤ) • L Z) := congrArg Neg.neg hPos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hPull Φₖ, hPull (curvatureDoubleCommutator Pₖ A C Φₖ)]
    have h := curvatureDoubleCommutator_quadratic_phi hPₖ A C
    calc
      curvatureDoubleCommutator Pₖ A C
          (curvatureDoubleCommutator Pₖ A C Φₖ) * Vₖₙ +
        (4 : ℤ) • (Vₖ * (curvatureDoubleCommutator Pₖ A C Φₖ * Vₖₙ)) -
        (4 : ℤ) • ((Vₖ * Vₖ) * (Φₖ * Vₖₙ)) =
        (curvatureDoubleCommutator Pₖ A C
            (curvatureDoubleCommutator Pₖ A C Φₖ) +
          (4 : ℤ) • (Vₖ * curvatureDoubleCommutator Pₖ A C Φₖ) -
          (4 : ℤ) • ((Vₖ * Vₖ) * Φₖ)) * Vₖₙ := by
            simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc]
      _ = 0 := by rw [h]; simp
  · rw [hPull Jₖ, hPull (curvatureDoubleCommutator Pₖ A C Jₖ)]
    have h := curvatureDoubleCommutator_quadratic_j hPₖ A C
    calc
      curvatureDoubleCommutator Pₖ A C
          (curvatureDoubleCommutator Pₖ A C Jₖ) * Vₖₙ +
        (4 : ℤ) • (Vₖ * (curvatureDoubleCommutator Pₖ A C Jₖ * Vₖₙ)) -
        (4 : ℤ) • ((Vₖ * Vₖ) * (Jₖ * Vₖₙ)) =
        (curvatureDoubleCommutator Pₖ A C
            (curvatureDoubleCommutator Pₖ A C Jₖ) +
          (4 : ℤ) • (Vₖ * curvatureDoubleCommutator Pₖ A C Jₖ) -
          (4 : ℤ) • ((Vₖ * Vₖ) * Jₖ)) * Vₖₙ := by
            simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc]
      _ = 0 := by rw [h]; simp
  · rw [hDepth, hEven.1]
    simp [curvatureDoubleCommutator, derivSqPhi, comm]
  · rw [hSigDepth]
    have hEig : curvatureDoubleCommutator Pₖ A C
        (qgtDefectDiff Pₖ A C (n + 1)) =
        -((4 : ℤ) • (Vₖ * qgtDefectDiff Pₖ A C (n + 1))) :=
      eq_neg_of_add_eq_zero_left hEven.2
    calc
      curvatureDoubleCommutator Pₖ A C
          (curvatureDoubleCommutator Pₖ A C
            (qgtDefectDiff Pₖ A C (n + 1))) +
        (4 : ℤ) • (Vₖ * curvatureDoubleCommutator Pₖ A C
          (qgtDefectDiff Pₖ A C (n + 1))) =
        curvatureDoubleCommutator Pₖ A C
            (-((4 : ℤ) • (Vₖ * qgtDefectDiff Pₖ A C (n + 1)))) +
          (4 : ℤ) • (Vₖ * curvatureDoubleCommutator Pₖ A C
            (qgtDefectDiff Pₖ A C (n + 1))) := by rw [hEig]
      _ = -((4 : ℤ) • curvatureDoubleCommutator Pₖ A C
            (Vₖ * qgtDefectDiff Pₖ A C (n + 1))) +
          (4 : ℤ) • (Vₖ * curvatureDoubleCommutator Pₖ A C
            (qgtDefectDiff Pₖ A C (n + 1))) := by rw [hNegFour]
      _ = 0 := by rw [hLeft]; abel

end InfoGeometry.OperatorAlgebra.PeirceSpine
