/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.UHFHeisenbergSugawaraVirasoroPoset

set_option maxHeartbeats 2000000

/-!
# Stage `D₃₁` (Archetypes `A₆₁, A₆₃, A₆₅, A₆₆, A₆₇, A₆₈, A₆₉`): Scale-12 / Scale-24 Kantor–Peirce Charge Frames, Scale-144 / Scale-576 Bilateral Compressions, and All-Scale Single-Sheet Decoders

This module formalizes the 6-stage causal poset of non-commutative Kantor–Peirce charge-filtration
frames, quadratic bilateral compressions, and all-scale `(k, n) ∈ ℕ × ℕ` single-sheet decoders over
an arbitrary associative ring `[Ring B]`, reusing the canonical `PeirceSpine` vocabulary
(`conePlus`, `coneMinus`, `qgtPlus`, `qgtMinus`, `genPhi`, `genJ`, `genV`, `genSig`,
`sandwichCross`, `sandwichSame`, `derivSqPhi`, `derivSqJ`, `derivSqSig`, `hProjV`, `hProjPhi`,
`hProjJ`, `hProjSig`, `conjPlus`, `conjMinus`, `s3Refl1`, `s3Refl2`, `idemDefect`, `idemTrans`):

1. **Stage `G₁` (`A₆₁`, `archetype_A61_scale_12_and_24_kantor_peirce_frames`):**
   Scale-12 3-sector (`golay12Core`, `golay12Root`, `golay12Ext`) and Scale-24 5-sector
   (`golay24G0`, `golay24Gp1`, `golay24Gm1`, `golay24Gp2`, `golay24Gm2`) polynomial combinations of
   the iterated super-charge operators `kantorDelta1..kantorDelta4`, together with the `3 × 8 = 24`
   scaled homogenized channels `mog24V`, `mog24Phi`, `mog24J`, `mog24Sig`.
2. **Stage `G₂` (`A₆₃`, `archetype_A63_scale_144_and_576_bilateral_compressions`):**
   Super-charge eigenvalue equations (`superChargeP (golay24G^{(m)}) P X = m • golay24G^{(m)} X`),
   mutual orthogonality of `golay12Core` and `golay12Ext`, and the Scale-144 (`12²`) and Scale-576
   (`24²`) bilateral sandwich compressions `(144 : ℤ) • (V * X * V)`, `(144 : ℤ) • (Σ * X * Σ)`,
   `(576 : ℤ) • (V * X * V)`, and `(576 : ℤ) • (Σ * X * Σ)`.
3. **Stage `G₃` (`A₆₄–A₆₅`, `archetype_A65_all_scale_defect_tower_channel_isolation`):**
   All-scale `(k, n) ∈ ℕ × ℕ` horizontal unipotent idempotent tower `daughterIdemTower k P A` and
   vertical defect tower `mandelbrotTower n (genV P_k A C)`, proving universal commutation with
   `Φ_k, J_k, Σ_k`, vanishing of `hProjPhi`, `hProjJ`, `hProjSig`, and exact recovery under `mog24V`.
4. **Stage `G₄` (`A₆₆–A₆₇`, `archetype_A67_all_scale_chiral_branch_isolation`):**
   All-scale 6-fold cone–sheet braiding (`cone_sheet_braiding_all_scales`), grade-0 evaluation
   `golay24G0 P_k A C V_{k,n} = (24 : ℤ) • (V_k * V_{k,n})`, and chiral branch isolation
   `mog24Sig P_k A C Σ_{k,n} = (24 : ℤ) • ((V_k * V_k) * Σ_{k,n})`.
5. **Stage `G₅` (`A₆₈`, `archetype_A68_single_sheet_swap_and_half_projections`):**
   All-scale single-sheet swap `golay24G0 P_k A C X_n = (24 : ℤ) • (V_k * Y_n)` and
   `golay24G0 P_k A C Y_n = (24 : ℤ) • (V_k * X_n)`, together with the Scale-12 half-projections
   `mog24V P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * V_{k,n})` and
   `mog24Sig P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * Σ_{k,n})`.
6. **Stage `G₆` (`A₆₉`, `archetype_A69_all_scale_single_sheet_decoders`):**
   Single-sheet decoders `mog24SheetPlus` and `mog24SheetMinus` satisfying
   `mog24SheetPlus P_k A C X_n = (24 : ℤ) • ((V_k * V_k * V_k) * V_{k,n})`,
   `mog24SheetPlus P_k A C Y_n = 0`, `mog24SheetMinus P_k A C X_n = 0`, and
   `mog24SheetMinus P_k A C Y_n = (24 : ℤ) • ((V_k * V_k * V_k) * V_{k,n})`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

open InfoGeometry.Core.IdempotentGraphGrassmannian

/-! ### 1. Causal Poset of Scale-12/24 Kantor–Peirce & Single-Sheet Decoder Archetypes (`G₁ → G₆`) -/

/-- The 6-stage causal poset of Scale-12/24 Kantor–Peirce charge frames, Scale-144/576 bilateral
compressions, and all-scale single-sheet decoders (`G₁ → G₆`). -/
inductive GolayLeechMOGStage : Type
  | G1_scale_12_and_24_kantor_peirce_frames
  | G2_scale_144_and_576_bilateral_compressions
  | G3_all_scale_defect_tower_channel_isolation
  | G4_all_scale_chiral_branch_isolation
  | G5_single_sheet_swap_and_half_projections
  | G6_all_scale_single_sheet_decoders
  deriving DecidableEq, Repr

namespace GolayLeechMOGStage

/-- Numerical topological rank of each stage `G₁..G₆`. -/
def rank : GolayLeechMOGStage → ℕ
  | G1_scale_12_and_24_kantor_peirce_frames => 1
  | G2_scale_144_and_576_bilateral_compressions => 2
  | G3_all_scale_defect_tower_channel_isolation => 3
  | G4_all_scale_chiral_branch_isolation => 4
  | G5_single_sheet_swap_and_half_projections => 5
  | G6_all_scale_single_sheet_decoders => 6

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

instance : LinearOrder GolayLeechMOGStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal dependency edges of the `G₁ → G₆` poset. -/
def causalEdge : GolayLeechMOGStage → GolayLeechMOGStage → Prop
  | G1_scale_12_and_24_kantor_peirce_frames, G2_scale_144_and_576_bilateral_compressions => True
  | G1_scale_12_and_24_kantor_peirce_frames, G3_all_scale_defect_tower_channel_isolation => True
  | G3_all_scale_defect_tower_channel_isolation, G4_all_scale_chiral_branch_isolation => True
  | G4_all_scale_chiral_branch_isolation, G5_single_sheet_swap_and_half_projections => True
  | G5_single_sheet_swap_and_half_projections, G6_all_scale_single_sheet_decoders => True
  | _, _ => False

theorem causalEdge_strict_rank_mono {a b : GolayLeechMOGStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

theorem causalEdge_irrefl (a : GolayLeechMOGStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

theorem transGen_causalEdge_strict_rank_mono {a b : GolayLeechMOGStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_strict_rank_mono hbc)

theorem causalEdge_acyclic (a : GolayLeechMOGStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

end GolayLeechMOGStage

/-! ### 2. Core Kantor–Peirce Charge-Filtration & Single-Sheet Decoder Primitives -/

variable {B : Type*} [Ring B]

/-- Symmetric Kantor triple product `X Y Z + Z Y X`. -/
def kantorTriple (X Y Z : B) : B := X * Y * Z + Z * Y * X

/-- Charge `+2` Peirce corner sandwich `N₊ X N₊`. -/
def kantorGp2 (P A X : B) : B := conePlus P A * X * conePlus P A

/-- Charge `+1` Peirce corner commutator `[N₊, X]`. -/
def kantorGp1 (P A X : B) : B := comm (conePlus P A) X

/-- Charge `0` Peirce cross-corner sandwich `N₊ X N₋ + N₋ X N₊`. -/
def kantorG0 (P A C X : B) : B := kantorTriple (conePlus P A) X (coneMinus P C)

/-- Charge `-1` Peirce corner commutator `[N₋, X]`. -/
def kantorGm1 (P C X : B) : B := comm (coneMinus P C) X

/-- Charge `-2` Peirce corner sandwich `N₋ X N₋`. -/
def kantorGm2 (P C X : B) : B := coneMinus P C * X * coneMinus P C

/-- Total 5-sector Kantor–Peirce sum `K_tot(X) = K_{-2}(X) + K_{-1}(X) + K_0(X) + K_{+1}(X) + K_{+2}(X)`. -/
def kantorTotal (P A C X : B) : B :=
  kantorGm2 P C X + kantorGm1 P C X + kantorG0 P A C X + kantorGp1 P A X + kantorGp2 P A X

/-- Idempotent charge commutator `[P, K(X)] - K([P, X])`. -/
def superChargeP (K : B → B) (P X : B) : B := comm P (K X) - K (comm P X)

/-- First iterated charge commutator `Δ_P(K_tot)(X)`. -/
def kantorDelta1 (P A C X : B) : B := superChargeP (kantorTotal P A C) P X

/-- Second iterated charge commutator `Δ_P²(K_tot)(X)`. -/
def kantorDelta2 (P A C X : B) : B := superChargeP (kantorDelta1 P A C) P X

/-- Third iterated charge commutator `Δ_P³(K_tot)(X)`. -/
def kantorDelta3 (P A C X : B) : B := superChargeP (kantorDelta2 P A C) P X

/-- Fourth iterated charge commutator `Δ_P⁴(K_tot)(X)`. -/
def kantorDelta4 (P A C X : B) : B := superChargeP (kantorDelta3 P A C) P X

/-- Scale-12 charge-0 core channel `3 (Δ⁴ - 5 Δ² + 4 K_tot)`. -/
def golay12Core (P A C X : B) : B :=
  (3 : ℤ) • (kantorDelta4 P A C X - (5 : ℤ) • kantorDelta2 P A C X + (4 : ℤ) • kantorTotal P A C X)

/-- Scale-12 charge-`±1` root channel `4 (4 Δ² - Δ⁴)` (repaired Lagrange interpolant at `m = ±1`,
where `4(1²) - 1⁴ = 3` so `4 × 3 = 12`). -/
def golay12Root (P A C X : B) : B :=
  (4 : ℤ) • ((4 : ℤ) • kantorDelta2 P A C X - kantorDelta4 P A C X)

/-- Scale-12 charge-`±2` extreme channel `Δ⁴ - Δ²`. -/
def golay12Ext (P A C X : B) : B :=
  kantorDelta4 P A C X - kantorDelta2 P A C X

/-- Scale-24 charge-`0` channel `6 (Δ⁴ - 5 Δ² + 4 K_tot)`. -/
def golay24G0 (P A C X : B) : B :=
  (6 : ℤ) • (kantorDelta4 P A C X - (5 : ℤ) • kantorDelta2 P A C X + (4 : ℤ) • kantorTotal P A C X)

/-- Scale-24 charge-`+1` channel `4 (4 Δ² - Δ⁴) + 4 (4 Δ¹ - Δ³)` (repaired Lagrange interpolant at `m = +1`). -/
def golay24Gp1 (P A C X : B) : B :=
  (4 : ℤ) • ((4 : ℤ) • kantorDelta2 P A C X - kantorDelta4 P A C X) +
  (4 : ℤ) • ((4 : ℤ) • kantorDelta1 P A C X - kantorDelta3 P A C X)

/-- Scale-24 charge-`-1` channel `4 (4 Δ² - Δ⁴) - 4 (4 Δ¹ - Δ³)` (repaired Lagrange interpolant at `m = -1`). -/
def golay24Gm1 (P A C X : B) : B :=
  (4 : ℤ) • ((4 : ℤ) • kantorDelta2 P A C X - kantorDelta4 P A C X) -
  (4 : ℤ) • ((4 : ℤ) • kantorDelta1 P A C X - kantorDelta3 P A C X)

/-- Scale-24 charge-`+2` channel `(Δ⁴ - Δ²) + 2 (Δ³ - Δ¹)`. -/
def golay24Gp2 (P A C X : B) : B :=
  (kantorDelta4 P A C X - kantorDelta2 P A C X) +
  (2 : ℤ) • (kantorDelta3 P A C X - kantorDelta1 P A C X)

/-- Scale-24 charge-`-2` channel `(Δ⁴ - Δ²) - 2 (Δ³ - Δ¹)`. -/
def golay24Gm2 (P A C X : B) : B :=
  (kantorDelta4 P A C X - kantorDelta2 P A C X) -
  (2 : ℤ) • (kantorDelta3 P A C X - kantorDelta1 P A C X)

/-- Scale-24 `V`-channel `3 • hProjV P A C X` (`= scaledHProjV3 P A C X`). -/
def mog24V (P A C X : B) : B := (3 : ℤ) • hProjV P A C X

/-- Scale-24 `Φ`-channel `3 • hProjPhi P A C X` (`= scaledHProjPhi3 P A C X`). -/
def mog24Phi (P A C X : B) : B := (3 : ℤ) • hProjPhi P A C X

/-- Scale-24 `J`-channel `3 • hProjJ P A C X` (`= scaledHProjJ3 P A C X`). -/
def mog24J (P A C X : B) : B := (3 : ℤ) • hProjJ P A C X

/-- Scale-24 `Σ`-channel `3 • hProjSig P A C X` (`= scaledHProjSig3 P A C X`). -/
def mog24Sig (P A C X : B) : B := (3 : ℤ) • hProjSig P A C X

/-- Chiral defect difference branch `Σ_{k,n} = δ^{(n)}(Q_{+,k}) - δ^{(n)}(Q_{-,k})`. -/
def chiralFractalBranch (n : ℕ) (P A C : B) : B :=
  mandelbrotTower n (qgtPlus P A C) - mandelbrotTower n (qgtMinus P A C)

/-- Upper-sheet linear combination `V * mog24V(Z) + Σ * mog24Sig(Z)`. -/
def mog24SheetPlus (P A C Z : B) : B :=
  genV P A C * mog24V P A C Z + genSig P A C * mog24Sig P A C Z

/-- Lower-sheet linear combination `V * mog24V(Z) - Σ * mog24Sig(Z)`. -/
def mog24SheetMinus (P A C Z : B) : B :=
  genV P A C * mog24V P A C Z - genSig P A C * mog24Sig P A C Z

/-- Normal-form decision macro for the Scale-12/24 Kantor–Peirce and MOG channels. -/
macro "peirce_abel_golay" hP:ident : tactic =>
  `(tactic| (
    try dsimp only [mog24V, mog24Phi, mog24J, mog24Sig,
                    kantorTotal,
                    kantorGp2, kantorGp1, kantorG0, kantorGm1, kantorGm2, kantorTriple,
                    s3Refl1, s3Refl2, cubeRootOp, cubeRootOpConj,
                    idempotencyDefect, idemDefect, idemTrans, chiralSource,
                    hProjV, hProjPhi, hProjJ, hProjSig,
                    conjPlus, conjMinus,
                    derivSqPhi, derivSqJ, derivSqSig,
                    sandwichCross, sandwichSame,
                    qgtPlus, qgtMinus]
    peirce_nf $hP:ident))

/-- Charge eigenvalues of the five Kantor–Peirce sector endomorphisms `G_{-2}, G_{-1}, G_0, G_{+1}, G_{+2}`
under `superChargeP`. -/
theorem superChargeP_kantor_eigen
    {P : B} (hP : P * P = P) (A C X : B) :
    superChargeP (kantorGp2 P A) P X = (2 : ℤ) • kantorGp2 P A X ∧
    superChargeP (kantorGp1 P A) P X = kantorGp1 P A X ∧
    superChargeP (kantorG0 P A C) P X = 0 ∧
    superChargeP (kantorGm1 P C) P X = -kantorGm1 P C X ∧
    superChargeP (kantorGm2 P C) P X = -((2 : ℤ) • kantorGm2 P C X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (dsimp only [superChargeP]; peirce_abel_golay hP)

/-- Linear expansion of `kantorDelta1`, `kantorDelta2`, `kantorDelta3`, and `kantorDelta4`
in terms of the five graded Kantor–Peirce components. -/
theorem kantorDelta_expansions
    {P : B} (hP : P * P = P) (A C : B) :
    (∀ X, kantorDelta1 P A C X =
      -((2 : ℤ) • kantorGm2 P C X) - kantorGm1 P C X +
      kantorGp1 P A X + (2 : ℤ) • kantorGp2 P A X) ∧
    (∀ X, kantorDelta2 P A C X =
      (4 : ℤ) • kantorGm2 P C X + kantorGm1 P C X +
      kantorGp1 P A X + (4 : ℤ) • kantorGp2 P A X) ∧
    (∀ X, kantorDelta3 P A C X =
      -((8 : ℤ) • kantorGm2 P C X) - kantorGm1 P C X +
      kantorGp1 P A X + (8 : ℤ) • kantorGp2 P A X) ∧
    (∀ X, kantorDelta4 P A C X =
      (16 : ℤ) • kantorGm2 P C X + kantorGm1 P C X +
      kantorGp1 P A X + (16 : ℤ) • kantorGp2 P A X) := by
  have h1 : ∀ X, kantorDelta1 P A C X =
      -((2 : ℤ) • kantorGm2 P C X) - kantorGm1 P C X +
      kantorGp1 P A X + (2 : ℤ) • kantorGp2 P A X := by
    intro X
    dsimp only [kantorDelta1, superChargeP]
    peirce_abel_golay hP
  have h2 : ∀ X, kantorDelta2 P A C X =
      (4 : ℤ) • kantorGm2 P C X + kantorGm1 P C X +
      kantorGp1 P A X + (4 : ℤ) • kantorGp2 P A X := by
    intro X
    change comm P (kantorDelta1 P A C X) - kantorDelta1 P A C (comm P X) = _
    rw [h1 X, h1 (comm P X)]
    peirce_abel_golay hP
  have h3 : ∀ X, kantorDelta3 P A C X =
      -((8 : ℤ) • kantorGm2 P C X) - kantorGm1 P C X +
      kantorGp1 P A X + (8 : ℤ) • kantorGp2 P A X := by
    intro X
    change comm P (kantorDelta2 P A C X) - kantorDelta2 P A C (comm P X) = _
    rw [h2 X, h2 (comm P X)]
    peirce_abel_golay hP
  have h4 : ∀ X, kantorDelta4 P A C X =
      (16 : ℤ) • kantorGm2 P C X + kantorGm1 P C X +
      kantorGp1 P A X + (16 : ℤ) • kantorGp2 P A X := by
    intro X
    change comm P (kantorDelta3 P A C X) - kantorDelta3 P A C (comm P X) = _
    rw [h3 X, h3 (comm P X)]
    peirce_abel_golay hP
  exact ⟨h1, h2, h3, h4⟩

/-! ### 3. Stage `G₁` (`A₆₁–A₆₂`): Scale-12 & Scale-24 Kantor–Peirce Frames and Defect Recursion -/

/-- **Theorem `G₁.1` (`archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes`):**
For any idempotent `P` (`P * P = P`) and any `A, C, X : B`:
1. **Scale-12 3-Sector Resolution:**
   - `golay12Core P A C X + golay12Root P A C X + golay12Ext P A C X = (12 : ℤ) • kantorTotal P A C X`,
   - `golay12Core P A C X = (12 : ℤ) • sandwichCross P A C X`,
   - `golay12Root P A C X = (12 : ℤ) • comm (genPhi P A C) X`,
   - `golay12Ext P A C X  = (12 : ℤ) • sandwichSame P A C X`.
2. **Scale-24 5-Sector Resolution:**
   - `golay24G0 P A C X + golay24Gp1 P A C X + golay24Gm1 P A C X + golay24Gp2 P A C X + golay24Gm2 P A C X = (24 : ℤ) • kantorTotal P A C X`,
   - `golay24G0 P A C X  = (24 : ℤ) • kantorG0 P A C X`,
   - `golay24Gp1 P A C X = (24 : ℤ) • kantorGp1 P A X`,
   - `golay24Gm1 P A C X = (24 : ℤ) • kantorGm1 P C X`,
   - `golay24Gp2 P A C X = (24 : ℤ) • kantorGp2 P A X`,
   - `golay24Gm2 P A C X = (24 : ℤ) • kantorGm2 P C X`.
3. **Scale-24 Homogenized Channel Partition & Shear/Reflection Filtering:**
   - `mog24V P A C X + mog24Phi P A C X + mog24J P A C X + mog24Sig P A C X = (24 : ℤ) • ((genV P A C * genV P A C) * X)`,
   - `mog24V P A C (genV P A C + conjPlus P A (genPhi P A C) + conjMinus P C (genJ P A C) + s3Refl1 P A C + s3Refl2 P A C) = (24 : ℤ) • ((genV P A C * genV P A C) * genV P A C)`. -/
theorem archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes
    {P : B} (hP : P * P = P) (A C X : B) :
    golay12Core P A C X + golay12Root P A C X + golay12Ext P A C X =
      (12 : ℤ) • kantorTotal P A C X ∧
    golay12Core P A C X = (12 : ℤ) • sandwichCross P A C X ∧
    golay12Root P A C X = (12 : ℤ) • comm (genPhi P A C) X ∧
    golay12Ext P A C X  = (12 : ℤ) • sandwichSame P A C X ∧
    golay24G0 P A C X + golay24Gp1 P A C X + golay24Gm1 P A C X +
      golay24Gp2 P A C X + golay24Gm2 P A C X =
      (24 : ℤ) • kantorTotal P A C X ∧
    golay24G0 P A C X  = (24 : ℤ) • kantorG0 P A C X ∧
    golay24Gp1 P A C X = (24 : ℤ) • kantorGp1 P A X ∧
    golay24Gm1 P A C X = (24 : ℤ) • kantorGm1 P C X ∧
    golay24Gp2 P A C X = (24 : ℤ) • kantorGp2 P A X ∧
    golay24Gm2 P A C X = (24 : ℤ) • kantorGm2 P C X ∧
    mog24V P A C X + mog24Phi P A C X + mog24J P A C X + mog24Sig P A C X =
      (24 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    mog24V P A C
      (genV P A C + conjPlus P A (genPhi P A C) +
       conjMinus P C (genJ P A C) + s3Refl1 P A C + s3Refl2 P A C) =
      (24 : ℤ) • ((genV P A C * genV P A C) * genV P A C) := by
  rcases kantorDelta_expansions hP A C with ⟨hD1, hD2, hD3, hD4⟩
  have h12Core : golay12Core P A C X = (12 : ℤ) • sandwichCross P A C X := by
    unfold golay12Core kantorTotal
    rw [hD4 X, hD2 X]
    change (3 : ℤ) • (((16 : ℤ) • kantorGm2 P C X + kantorGm1 P C X + kantorGp1 P A X + (16 : ℤ) • kantorGp2 P A X) -
      (5 : ℤ) • ((4 : ℤ) • kantorGm2 P C X + kantorGm1 P C X + kantorGp1 P A X + (4 : ℤ) • kantorGp2 P A X) +
      (4 : ℤ) • (kantorGm2 P C X + kantorGm1 P C X + kantorG0 P A C X + kantorGp1 P A X + kantorGp2 P A X)) =
      (12 : ℤ) • kantorG0 P A C X
    abel_nf
  have h12Root : golay12Root P A C X = (12 : ℤ) • comm (genPhi P A C) X := by
    unfold golay12Root
    rw [hD4 X, hD2 X]
    have hSub : (4 : ℤ) • ((4 : ℤ) • kantorGm2 P C X + kantorGm1 P C X + kantorGp1 P A X + (4 : ℤ) • kantorGp2 P A X) -
        ((16 : ℤ) • kantorGm2 P C X + kantorGm1 P C X + kantorGp1 P A X + (16 : ℤ) • kantorGp2 P A X) =
        (3 : ℤ) • (kantorGp1 P A X + kantorGm1 P C X) := by abel_nf
    rw [hSub, smul_smul]
    have hPhi : kantorGp1 P A X + kantorGm1 P C X = comm (genPhi P A C) X := by
      dsimp only [kantorGp1, kantorGm1]; peirce_nf hP
    rw [hPhi]
    rfl
  have h12Ext : golay12Ext P A C X = (12 : ℤ) • sandwichSame P A C X := by
    unfold golay12Ext
    rw [hD4 X, hD2 X]
    have hSub : ((16 : ℤ) • kantorGm2 P C X + kantorGm1 P C X + kantorGp1 P A X + (16 : ℤ) • kantorGp2 P A X) -
        ((4 : ℤ) • kantorGm2 P C X + kantorGm1 P C X + kantorGp1 P A X + (4 : ℤ) • kantorGp2 P A X) =
        (12 : ℤ) • (kantorGp2 P A X + kantorGm2 P C X) := by abel_nf
    rw [hSub]
    rfl
  have h12Sum : golay12Core P A C X + golay12Root P A C X + golay12Ext P A C X =
      (12 : ℤ) • kantorTotal P A C X := by
    rw [h12Core, h12Root, h12Ext]
    have hPhi : comm (genPhi P A C) X = kantorGp1 P A X + kantorGm1 P C X := by
      dsimp only [kantorGp1, kantorGm1]; peirce_nf hP
    rw [hPhi]
    change (12 : ℤ) • kantorG0 P A C X + (12 : ℤ) • (kantorGp1 P A X + kantorGm1 P C X) +
      (12 : ℤ) • (kantorGp2 P A X + kantorGm2 P C X) =
      (12 : ℤ) • (kantorGm2 P C X + kantorGm1 P C X + kantorG0 P A C X + kantorGp1 P A X + kantorGp2 P A X)
    abel_nf
  have h24G0 : golay24G0 P A C X = (24 : ℤ) • kantorG0 P A C X := by
    unfold golay24G0 kantorTotal
    rw [hD4 X, hD2 X]
    abel_nf
  have h24Gp1 : golay24Gp1 P A C X = (24 : ℤ) • kantorGp1 P A X := by
    unfold golay24Gp1
    rw [hD4 X, hD3 X, hD2 X, hD1 X]
    abel_nf
  have h24Gm1 : golay24Gm1 P A C X = (24 : ℤ) • kantorGm1 P C X := by
    unfold golay24Gm1
    rw [hD4 X, hD3 X, hD2 X, hD1 X]
    abel_nf
  have h24Gp2 : golay24Gp2 P A C X = (24 : ℤ) • kantorGp2 P A X := by
    unfold golay24Gp2
    rw [hD4 X, hD3 X, hD2 X, hD1 X]
    abel_nf
  have h24Gm2 : golay24Gm2 P A C X = (24 : ℤ) • kantorGm2 P C X := by
    unfold golay24Gm2
    rw [hD4 X, hD3 X, hD2 X, hD1 X]
    abel_nf
  have h24Sum : golay24G0 P A C X + golay24Gp1 P A C X + golay24Gm1 P A C X +
      golay24Gp2 P A C X + golay24Gm2 P A C X =
      (24 : ℤ) • kantorTotal P A C X := by
    rw [h24G0, h24Gp1, h24Gm1, h24Gp2, h24Gm2]
    unfold kantorTotal
    abel_nf
  have hMogSum : mog24V P A C X + mog24Phi P A C X + mog24J P A C X + mog24Sig P A C X =
      (24 : ℤ) • ((genV P A C * genV P A C) * X) := by
    unfold mog24V mog24Phi mog24J mog24Sig
    have hH := archetype_A13_homogenized_projectors hP A C X
    calc (3 : ℤ) • hProjV P A C X + (3 : ℤ) • hProjPhi P A C X +
         (3 : ℤ) • hProjJ P A C X + (3 : ℤ) • hProjSig P A C X
      _ = (3 : ℤ) • (hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X) := by abel
      _ = (3 : ℤ) • ((8 : ℤ) • ((genV P A C * genV P A C) * X)) := by rw [hH.1]
      _ = (24 : ℤ) • ((genV P A C * genV P A C) * X) := by rw [smul_smul]; rfl
  have hMogShear : mog24V P A C
      (genV P A C + conjPlus P A (genPhi P A C) +
       conjMinus P C (genJ P A C) + s3Refl1 P A C + s3Refl2 P A C) =
      (24 : ℤ) • ((genV P A C * genV P A C) * genV P A C) := by
    unfold mog24V
    have hV : hProjV P A C
        (genV P A C + conjPlus P A (genPhi P A C) +
         conjMinus P C (genJ P A C) + s3Refl1 P A C + s3Refl2 P A C) =
        (8 : ℤ) • ((genV P A C * genV P A C) * genV P A C) := by
      peirce_abel_golay hP
    rw [hV, smul_smul]; rfl
  exact ⟨h12Sum, h12Core, h12Root, h12Ext, h24Sum, h24G0, h24Gp1, h24Gm1, h24Gp2, h24Gm2, hMogSum, hMogShear⟩

/-! ### 4. Stage `G₂` (`A₆₃`): Eigen-Superoperator Algebra & Scale-144 / Scale-576 Bilateral Compressions -/

/-- **Theorem `G₂.1` (`archetype_A63_golay_144_leech_576_quadratic_compression_and_eigen_algebra`):**
For any idempotent `P` (`P * P = P`) and any `A, C, X : B`:
1. **Charge Eigenvalue Identities (`superChargeP (golay24G^{(m)}) P X = m • golay24G^{(m)} X`):**
   `superChargeP (golay24G0 P A C) P X = 0`, `superChargeP (golay24Gp1 P A C) P X = golay24Gp1 P A C X`,
   `superChargeP (golay24Gm1 P A C) P X = -golay24Gm1 P A C X`,
   `superChargeP (golay24Gp2 P A C) P X = (2 : ℤ) • golay24Gp2 P A C X`, and
   `superChargeP (golay24Gm2 P A C) P X = (-2 : ℤ) • golay24Gm2 P A C X`.
2. **Mutual Orthogonality of `golay12Core` and `golay12Ext`:**
   `golay12Core P A C (golay12Ext P A C X) = 0` and `golay12Ext P A C (golay12Core P A C X) = 0`.
3. **Scale-144 (`12²`) and Scale-576 (`24²`) Bilateral Compressions:**
   - `golay12Core P A C (golay12Core P A C X) + golay12Ext P A C (golay12Ext P A C X) = (144 : ℤ) • (genV P A C * X * genV P A C)`,
   - `golay12Core P A C (golay12Core P A C X) - golay12Ext P A C (golay12Ext P A C X) = (144 : ℤ) • (genSig P A C * X * genSig P A C)`,
   - `golay24G0 P A C (golay24G0 P A C X) + golay24Gp2 P A C (golay24Gm2 P A C X) + golay24Gm2 P A C (golay24Gp2 P A C X) = (576 : ℤ) • (genV P A C * X * genV P A C)`,
   - `golay24G0 P A C (golay24G0 P A C X) - golay24Gp2 P A C (golay24Gm2 P A C X) - golay24Gm2 P A C (golay24Gp2 P A C X) = (576 : ℤ) • (genSig P A C * X * genSig P A C)`. -/
theorem archetype_A63_golay_144_leech_576_quadratic_compression_and_eigen_algebra
    {P : B} (hP : P * P = P) (A C X : B) :
    superChargeP (golay24G0 P A C) P X = 0 ∧
    superChargeP (golay24Gp1 P A C) P X = golay24Gp1 P A C X ∧
    superChargeP (golay24Gm1 P A C) P X = -golay24Gm1 P A C X ∧
    superChargeP (golay24Gp2 P A C) P X = (2 : ℤ) • golay24Gp2 P A C X ∧
    superChargeP (golay24Gm2 P A C) P X = (-2 : ℤ) • golay24Gm2 P A C X ∧
    golay12Core P A C (golay12Ext P A C X) = 0 ∧
    golay12Ext P A C (golay12Core P A C X) = 0 ∧
    golay24Gm1 P A C (golay24Gm1 P A C (golay24Gp2 P A C X)) =
      (-48 : ℤ) • golay24Gm2 P A C (golay24Gp2 P A C X) ∧
    golay24Gp1 P A C (golay24Gp1 P A C (golay24Gm2 P A C X)) =
      (-48 : ℤ) • golay24Gp2 P A C (golay24Gm2 P A C X) ∧
    golay12Core P A C (golay12Core P A C X) + golay12Ext P A C (golay12Ext P A C X) =
      (144 : ℤ) • (genV P A C * X * genV P A C) ∧
    golay12Core P A C (golay12Core P A C X) - golay12Ext P A C (golay12Ext P A C X) =
      (144 : ℤ) • (genSig P A C * X * genSig P A C) ∧
    golay24G0 P A C (golay24G0 P A C X) +
      golay24Gp2 P A C (golay24Gm2 P A C X) + golay24Gm2 P A C (golay24Gp2 P A C X) =
      (576 : ℤ) • (genV P A C * X * genV P A C) ∧
    golay24G0 P A C (golay24G0 P A C X) -
      golay24Gp2 P A C (golay24Gm2 P A C X) - golay24Gm2 P A C (golay24Gp2 P A C X) =
      (576 : ℤ) • (genSig P A C * X * genSig P A C) := by
  have hA61 := fun Z => archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hP A C Z
  have h12Core : ∀ Z, golay12Core P A C Z = (12 : ℤ) • sandwichCross P A C Z :=
    fun Z => (hA61 Z).2.1
  have h12Ext : ∀ Z, golay12Ext P A C Z = (12 : ℤ) • sandwichSame P A C Z :=
    fun Z => (hA61 Z).2.2.2.1
  have h24G0 : ∀ Z, golay24G0 P A C Z = (24 : ℤ) • kantorG0 P A C Z :=
    fun Z => (hA61 Z).2.2.2.2.2.1
  have h24Gp1 : ∀ Z, golay24Gp1 P A C Z = (24 : ℤ) • kantorGp1 P A Z :=
    fun Z => (hA61 Z).2.2.2.2.2.2.1
  have h24Gm1 : ∀ Z, golay24Gm1 P A C Z = (24 : ℤ) • kantorGm1 P C Z :=
    fun Z => (hA61 Z).2.2.2.2.2.2.2.1
  have h24Gp2 : ∀ Z, golay24Gp2 P A C Z = (24 : ℤ) • kantorGp2 P A Z :=
    fun Z => (hA61 Z).2.2.2.2.2.2.2.2.1
  have h24Gm2 : ∀ Z, golay24Gm2 P A C Z = (24 : ℤ) • kantorGm2 P C Z :=
    fun Z => (hA61 Z).2.2.2.2.2.2.2.2.2.1
  have hSC_smul : ∀ (n : ℤ) (K : B → B) (hK : ∀ Z, K (n • Z) = n • K Z),
      superChargeP (fun Z => n • K Z) P X = n • superChargeP K P X := by
    intro n K _
    unfold superChargeP comm
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  rcases superChargeP_kantor_eigen hP A C X with ⟨eP2, eP1, e0, eM1, eM2⟩
  have hCrossSmul : ∀ (n : ℤ) (Z : B), sandwichCross P A C (n • Z) = n • sandwichCross P A C Z := by
    intro n Z; unfold sandwichCross; simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  have hSameSmul : ∀ (n : ℤ) (Z : B), sandwichSame P A C (n • Z) = n • sandwichSame P A C Z := by
    intro n Z; unfold sandwichSame; simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  have hG0Smul : ∀ (n : ℤ) (Z : B), kantorG0 P A C (n • Z) = n • kantorG0 P A C Z := by
    intro n Z; unfold kantorG0 kantorTriple; simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  have hGp1Smul : ∀ (n : ℤ) (Z : B), kantorGp1 P A (n • Z) = n • kantorGp1 P A Z := by
    intro n Z; unfold kantorGp1 comm; simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  have hGm1Smul : ∀ (n : ℤ) (Z : B), kantorGm1 P C (n • Z) = n • kantorGm1 P C Z := by
    intro n Z; unfold kantorGm1 comm; simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  have hGp2Smul : ∀ (n : ℤ) (Z : B), kantorGp2 P A (n • Z) = n • kantorGp2 P A Z := by
    intro n Z; unfold kantorGp2; simp only [mul_smul_comm, smul_mul_assoc]
  have hGm2Smul : ∀ (n : ℤ) (Z : B), kantorGm2 P C (n • Z) = n • kantorGm2 P C Z := by
    intro n Z; unfold kantorGm2; simp only [mul_smul_comm, smul_mul_assoc]
  have c1 : superChargeP (golay24G0 P A C) P X = 0 := by
    change comm P (golay24G0 P A C X) - golay24G0 P A C (comm P X) = 0
    rw [h24G0 X, h24G0 (comm P X)]
    calc comm P ((24 : ℤ) • kantorG0 P A C X) - (24 : ℤ) • kantorG0 P A C (comm P X)
      _ = (24 : ℤ) • superChargeP (kantorG0 P A C) P X := by
          unfold superChargeP comm; simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
      _ = 0 := by rw [e0, smul_zero]
  have c2 : superChargeP (golay24Gp1 P A C) P X = golay24Gp1 P A C X := by
    change comm P (golay24Gp1 P A C X) - golay24Gp1 P A C (comm P X) = golay24Gp1 P A C X
    rw [h24Gp1 X, h24Gp1 (comm P X)]
    calc comm P ((24 : ℤ) • kantorGp1 P A X) - (24 : ℤ) • kantorGp1 P A (comm P X)
      _ = (24 : ℤ) • superChargeP (kantorGp1 P A) P X := by
          unfold superChargeP comm; simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
      _ = (24 : ℤ) • kantorGp1 P A X := by rw [eP1]
  have c3 : superChargeP (golay24Gm1 P A C) P X = -golay24Gm1 P A C X := by
    change comm P (golay24Gm1 P A C X) - golay24Gm1 P A C (comm P X) = -golay24Gm1 P A C X
    rw [h24Gm1 X, h24Gm1 (comm P X)]
    calc comm P ((24 : ℤ) • kantorGm1 P C X) - (24 : ℤ) • kantorGm1 P C (comm P X)
      _ = (24 : ℤ) • superChargeP (kantorGm1 P C) P X := by
          unfold superChargeP comm; simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
      _ = -((24 : ℤ) • kantorGm1 P C X) := by rw [eM1, smul_neg]
  have c4 : superChargeP (golay24Gp2 P A C) P X = (2 : ℤ) • golay24Gp2 P A C X := by
    change comm P (golay24Gp2 P A C X) - golay24Gp2 P A C (comm P X) = (2 : ℤ) • golay24Gp2 P A C X
    rw [h24Gp2 X, h24Gp2 (comm P X)]
    calc comm P ((24 : ℤ) • kantorGp2 P A X) - (24 : ℤ) • kantorGp2 P A (comm P X)
      _ = (24 : ℤ) • superChargeP (kantorGp2 P A) P X := by
          unfold superChargeP comm; simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
      _ = (2 : ℤ) • ((24 : ℤ) • kantorGp2 P A X) := by rw [eP2, smul_smul, smul_smul]; rfl
  have c5 : superChargeP (golay24Gm2 P A C) P X = (-2 : ℤ) • golay24Gm2 P A C X := by
    change comm P (golay24Gm2 P A C X) - golay24Gm2 P A C (comm P X) = (-2 : ℤ) • golay24Gm2 P A C X
    rw [h24Gm2 X, h24Gm2 (comm P X)]
    calc comm P ((24 : ℤ) • kantorGm2 P C X) - (24 : ℤ) • kantorGm2 P C (comm P X)
      _ = (24 : ℤ) • superChargeP (kantorGm2 P C) P X := by
          unfold superChargeP comm; simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
      _ = (-2 : ℤ) • ((24 : ℤ) • kantorGm2 P C X) := by
          rw [eM2, smul_neg, smul_smul, smul_smul]; abel_nf
  have c6 : golay12Core P A C (golay12Ext P A C X) = 0 := by
    rw [h12Ext X, h12Core, hCrossSmul]
    have h0 : sandwichCross P A C (sandwichSame P A C X) = 0 := by peirce_abel_golay hP
    rw [h0, smul_zero, smul_zero]
  have c7 : golay12Ext P A C (golay12Core P A C X) = 0 := by
    rw [h12Core X, h12Ext, hSameSmul]
    have h0 : sandwichSame P A C (sandwichCross P A C X) = 0 := by peirce_abel_golay hP
    rw [h0, smul_zero, smul_zero]
  have c8 : golay24Gm1 P A C (golay24Gm1 P A C (golay24Gp2 P A C X)) =
      (-48 : ℤ) • golay24Gm2 P A C (golay24Gp2 P A C X) := by
    simp only [h24Gp2, h24Gm1, hGm1Smul, h24Gm2, hGm2Smul]
    have hSq : kantorGm1 P C (kantorGm1 P C (kantorGp2 P A X)) =
        (-2 : ℤ) • kantorGm2 P C (kantorGp2 P A X) := by peirce_abel_golay hP
    rw [hSq]
    simp only [smul_smul]; rfl
  have c9 : golay24Gp1 P A C (golay24Gp1 P A C (golay24Gm2 P A C X)) =
      (-48 : ℤ) • golay24Gp2 P A C (golay24Gm2 P A C X) := by
    simp only [h24Gm2, h24Gp1, hGp1Smul, h24Gp2, hGp2Smul]
    have hSq : kantorGp1 P A (kantorGp1 P A (kantorGm2 P C X)) =
        (-2 : ℤ) • kantorGp2 P A (kantorGm2 P C X) := by peirce_abel_golay hP
    rw [hSq]
    simp only [smul_smul]; rfl
  have c10 : golay12Core P A C (golay12Core P A C X) + golay12Ext P A C (golay12Ext P A C X) =
      (144 : ℤ) • (genV P A C * X * genV P A C) := by
    rw [h12Core X, h12Core, hCrossSmul, h12Ext X, h12Ext, hSameSmul, smul_smul, smul_smul]
    have hId : sandwichCross P A C (sandwichCross P A C X) +
        sandwichSame P A C (sandwichSame P A C X) = genV P A C * X * genV P A C := by
      peirce_abel_golay hP
    calc ((12 * 12 : ℤ) • sandwichCross P A C (sandwichCross P A C X)) +
         ((12 * 12 : ℤ) • sandwichSame P A C (sandwichSame P A C X))
      _ = (144 : ℤ) • (sandwichCross P A C (sandwichCross P A C X) +
                       sandwichSame P A C (sandwichSame P A C X)) := by
          rw [← smul_add]; rfl
      _ = (144 : ℤ) • (genV P A C * X * genV P A C) := by rw [hId]
  have c11 : golay12Core P A C (golay12Core P A C X) - golay12Ext P A C (golay12Ext P A C X) =
      (144 : ℤ) • (genSig P A C * X * genSig P A C) := by
    rw [h12Core X, h12Core, hCrossSmul, h12Ext X, h12Ext, hSameSmul, smul_smul, smul_smul]
    have hId : sandwichCross P A C (sandwichCross P A C X) -
        sandwichSame P A C (sandwichSame P A C X) = genSig P A C * X * genSig P A C := by
      peirce_abel_golay hP
    calc ((12 * 12 : ℤ) • sandwichCross P A C (sandwichCross P A C X)) -
         ((12 * 12 : ℤ) • sandwichSame P A C (sandwichSame P A C X))
      _ = (144 : ℤ) • (sandwichCross P A C (sandwichCross P A C X) -
                       sandwichSame P A C (sandwichSame P A C X)) := by
          rw [← smul_sub]; rfl
      _ = (144 : ℤ) • (genSig P A C * X * genSig P A C) := by rw [hId]
  have c12 : golay24G0 P A C (golay24G0 P A C X) +
      golay24Gp2 P A C (golay24Gm2 P A C X) + golay24Gm2 P A C (golay24Gp2 P A C X) =
      (576 : ℤ) • (genV P A C * X * genV P A C) := by
    rw [h24G0 X, h24G0, hG0Smul, h24Gm2 X, h24Gp2, hGp2Smul, h24Gp2 X, h24Gm2, hGm2Smul,
        smul_smul, smul_smul, smul_smul]
    have hId : kantorG0 P A C (kantorG0 P A C X) +
        kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X) =
        genV P A C * X * genV P A C := by
      peirce_abel_golay hP
    calc ((24 * 24 : ℤ) • kantorG0 P A C (kantorG0 P A C X)) +
         ((24 * 24 : ℤ) • kantorGp2 P A (kantorGm2 P C X)) +
         ((24 * 24 : ℤ) • kantorGm2 P C (kantorGp2 P A X))
      _ = (576 : ℤ) • (kantorG0 P A C (kantorG0 P A C X) +
                       kantorGp2 P A (kantorGm2 P C X) +
                       kantorGm2 P C (kantorGp2 P A X)) := by
          rw [← smul_add, ← smul_add]; rfl
      _ = (576 : ℤ) • (genV P A C * X * genV P A C) := by rw [hId]
  have c13 : golay24G0 P A C (golay24G0 P A C X) -
      golay24Gp2 P A C (golay24Gm2 P A C X) - golay24Gm2 P A C (golay24Gp2 P A C X) =
      (576 : ℤ) • (genSig P A C * X * genSig P A C) := by
    rw [h24G0 X, h24G0, hG0Smul, h24Gm2 X, h24Gp2, hGp2Smul, h24Gp2 X, h24Gm2, hGm2Smul,
        smul_smul, smul_smul, smul_smul]
    have hId : kantorG0 P A C (kantorG0 P A C X) -
        kantorGp2 P A (kantorGm2 P C X) - kantorGm2 P C (kantorGp2 P A X) =
        genSig P A C * X * genSig P A C := by
      peirce_abel_golay hP
    calc ((24 * 24 : ℤ) • kantorG0 P A C (kantorG0 P A C X)) -
         ((24 * 24 : ℤ) • kantorGp2 P A (kantorGm2 P C X)) -
         ((24 * 24 : ℤ) • kantorGm2 P C (kantorGp2 P A X))
      _ = (576 : ℤ) • (kantorG0 P A C (kantorG0 P A C X) -
                       kantorGp2 P A (kantorGm2 P C X) -
                       kantorGm2 P C (kantorGp2 P A X)) := by
          rw [← smul_sub, ← smul_sub]; rfl
      _ = (576 : ℤ) • (genSig P A C * X * genSig P A C) := by rw [hId]
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩

/-! ### Cantor Color Tripotent to Kantor–Golay Operator Bridge -/

/-- Red-to-green and green-to-red hopping are the two Peirce corners based at
the red idempotent when the amplitudes are restricted to the green corner. -/
theorem color_hopping_is_red_peirce_hopping
    {P_R P_G A C : B}
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) :
    conePlus P_R (A * P_G) = P_R * A * P_G ∧
    coneMinus P_R (P_G * C) = P_G * C * P_R := by
  constructor
  · simp only [conePlus]
    calc
      P_R * (A * P_G) * (1 - P_R) = P_R * A * (P_G * (1 - P_R)) := by
        simp only [mul_assoc]
      _ = P_R * A * P_G := by
        rw [mul_sub, mul_one, hGR, sub_zero]
  · simp only [coneMinus]
    calc
      (1 - P_R) * (P_G * C) * P_R = ((1 - P_R) * P_G) * C * P_R := by
        simp only [mul_assoc]
      _ = P_G * C * P_R := by
        simp only [sub_mul, one_mul, hRG, sub_zero]

/-- The color-tripoten charge of red-green hopping is twice its oriented
current, and the two-way return metric is the square of the hopping operator. -/
theorem color_hopping_charge_and_return_metric
    {P_R P_G A C : B}
    (hR : P_R * P_R = P_R) (hG : P_G * P_G = P_G)
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) :
    comm (colorTripotent P_R P_G)
        (genPhi P_R (A * P_G) (P_G * C)) =
      (2 : ℤ) • genJ P_R (A * P_G) (P_G * C) ∧
    genV P_R (A * P_G) (P_G * C) =
      genPhi P_R (A * P_G) (P_G * C) *
        genPhi P_R (A * P_G) (P_G * C) := by
  have hCorners := color_hopping_is_red_peirce_hopping
    (P_R := P_R) (P_G := P_G) (A := A) (C := C) hRG hGR
  have hChargeA := colorTripotent_corner_charge hR hG hRG hGR A
  have hChargeC := colorTripotent_corner_charge hR hG hRG hGR C
  constructor
  · change comm (colorTripotent P_R P_G)
        (conePlus P_R (A * P_G) + coneMinus P_R (P_G * C)) =
      (2 : ℤ) • (conePlus P_R (A * P_G) - coneMinus P_R (P_G * C))
    rw [hCorners.1, hCorners.2]
    calc
      comm (colorTripotent P_R P_G) (P_R * A * P_G + P_G * C * P_R) =
          comm (colorTripotent P_R P_G) (P_R * A * P_G) +
            comm (colorTripotent P_R P_G) (P_G * C * P_R) := by
          unfold comm
          simp only [add_mul, mul_add]
          abel
      _ = (2 : ℤ) • (P_R * A * P_G) -
          (2 : ℤ) • (P_G * C * P_R) := by
        rw [hChargeA.1, hChargeC.2.1]
        abel
      _ = (2 : ℤ) • (P_R * A * P_G - P_G * C * P_R) := by
          rw [zsmul_sub]
  · change conePlus P_R (A * P_G) * coneMinus P_R (P_G * C) +
        coneMinus P_R (P_G * C) * conePlus P_R (A * P_G) =
      (conePlus P_R (A * P_G) + coneMinus P_R (P_G * C)) *
        (conePlus P_R (A * P_G) + coneMinus P_R (P_G * C))
    rw [hCorners.1, hCorners.2]
    have hPlusSq : (P_R * A * P_G) * (P_R * A * P_G) = 0 := by
      calc
        (P_R * A * P_G) * (P_R * A * P_G) =
            P_R * A * (P_G * P_R) * A * P_G := by noncomm_ring
        _ = 0 := by rw [hGR]; simp
    have hMinusSq : (P_G * C * P_R) * (P_G * C * P_R) = 0 := by
      calc
        (P_G * C * P_R) * (P_G * C * P_R) =
            P_G * C * (P_R * P_G) * C * P_R := by noncomm_ring
        _ = 0 := by rw [hRG]; simp
    simp only [add_mul, mul_add, hPlusSq, hMinusSq, zero_add, add_zero]
    abel

/-- The operator cyclotomic polynomials of the red-minus-green tripotent
read out the two retained color corners, with the factor two kept explicit
over an arbitrary ring. Their ordered products recover twice the surviving
two-color support. -/
theorem color_tripotent_cyclotomic_corner_readout
    {P_R P_G : B}
    (hR : P_R * P_R = P_R) (hG : P_G * P_G = P_G)
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) :
    cyclotomicThree (colorTripotent P_R P_G) =
      1 + (2 : ℤ) • P_R ∧
    cyclotomicSix (colorTripotent P_R P_G) =
      1 + (2 : ℤ) • P_G ∧
    cyclotomicThree (colorTripotent P_R P_G) *
        cyclotomicSix (colorTripotent P_R P_G) =
      1 + (2 : ℤ) • (P_R + P_G) ∧
    cyclotomicSix (colorTripotent P_R P_G) *
        cyclotomicThree (colorTripotent P_R P_G) =
      1 + (2 : ℤ) • (P_R + P_G) := by
  simp only [cyclotomicThree, cyclotomicSix, colorTripotent, two_zsmul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    noncomm_ring [hR, hG, hRG, hGR]

/-- Cantor red-green hopping is supported on the surviving two-color corner:
the complementary color idempotent annihilates it on either side. The
tripotent charge ladder has weights two and four on the hopping Hamiltonian. -/
theorem color_hopping_gap_support_and_charge_ladder
    {P_R P_G A C : B}
    (hR : P_R * P_R = P_R) (hG : P_G * P_G = P_G)
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) :
    colorBlue P_R P_G * genPhi P_R (A * P_G) (P_G * C) = 0 ∧
    genPhi P_R (A * P_G) (P_G * C) * colorBlue P_R P_G = 0 ∧
    comm (colorTripotent P_R P_G)
      (comm (colorTripotent P_R P_G)
        (genPhi P_R (A * P_G) (P_G * C))) =
      (4 : ℤ) • genPhi P_R (A * P_G) (P_G * C) := by
  have hCorners := color_hopping_is_red_peirce_hopping
    (P_R := P_R) (P_G := P_G) (A := A) (C := C) hRG hGR
  have hColorPartition := colorBlue_three_corner_decomposition hR hG hRG hGR
  have hBlueR : colorBlue P_R P_G * P_R = 0 := by
    exact hColorPartition.2.1
  have hBlueG : colorBlue P_R P_G * P_G = 0 := by
    exact hColorPartition.2.2.2.1
  have hRBlue : P_R * colorBlue P_R P_G = 0 := by
    exact hColorPartition.1
  have hGBlue : P_G * colorBlue P_R P_G = 0 := by
    exact hColorPartition.2.2.1
  have hChargeA := colorTripotent_corner_charge hR hG hRG hGR A
  have hChargeC := colorTripotent_corner_charge hR hG hRG hGR C
  have hJCharge : comm (colorTripotent P_R P_G)
      (genJ P_R (A * P_G) (P_G * C)) =
      (2 : ℤ) • genPhi P_R (A * P_G) (P_G * C) := by
    change comm (colorTripotent P_R P_G)
        (conePlus P_R (A * P_G) - coneMinus P_R (P_G * C)) =
      (2 : ℤ) • (conePlus P_R (A * P_G) + coneMinus P_R (P_G * C))
    rw [hCorners.1, hCorners.2]
    calc
      comm (colorTripotent P_R P_G) (P_R * A * P_G - P_G * C * P_R) =
          comm (colorTripotent P_R P_G) (P_R * A * P_G) -
            comm (colorTripotent P_R P_G) (P_G * C * P_R) := by
          unfold comm
          simp only [sub_mul, mul_sub]
          abel
      _ = (2 : ℤ) • (P_R * A * P_G) +
          (2 : ℤ) • (P_G * C * P_R) := by
        rw [hChargeA.1, hChargeC.2.1]
        abel
      _ = (2 : ℤ) • (P_R * A * P_G + P_G * C * P_R) := by
        rw [zsmul_add]
  refine ⟨?_, ?_, ?_⟩
  · change colorBlue P_R P_G *
      (conePlus P_R (A * P_G) + coneMinus P_R (P_G * C)) = 0
    rw [hCorners.1, hCorners.2]
    calc
      colorBlue P_R P_G * (P_R * A * P_G + P_G * C * P_R) =
          (colorBlue P_R P_G * P_R) * A * P_G +
            (colorBlue P_R P_G * P_G) * C * P_R := by noncomm_ring
      _ = 0 := by rw [hBlueR, hBlueG]; simp
  · change (conePlus P_R (A * P_G) + coneMinus P_R (P_G * C)) *
      colorBlue P_R P_G = 0
    rw [hCorners.1, hCorners.2]
    calc
      (P_R * A * P_G + P_G * C * P_R) * colorBlue P_R P_G =
          P_R * A * (P_G * colorBlue P_R P_G) +
            P_G * C * (P_R * colorBlue P_R P_G) := by noncomm_ring
      _ = 0 := by rw [hGBlue, hRBlue]; simp
  · have hHCharge := (color_hopping_charge_and_return_metric
      (P_R := P_R) (P_G := P_G) (A := A) (C := C)
      hR hG hRG hGR).1
    calc
      comm (colorTripotent P_R P_G)
          (comm (colorTripotent P_R P_G)
            (genPhi P_R (A * P_G) (P_G * C))) =
          comm (colorTripotent P_R P_G)
            ((2 : ℤ) • genJ P_R (A * P_G) (P_G * C)) := by rw [hHCharge]
      _ = (2 : ℤ) • comm (colorTripotent P_R P_G)
          (genJ P_R (A * P_G) (P_G * C)) := by
          unfold comm
          simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
      _ = (2 : ℤ) • ((2 : ℤ) • genPhi P_R (A * P_G) (P_G * C)) := by
          rw [hJCharge]
      _ = (4 : ℤ) • genPhi P_R (A * P_G) (P_G * C) := by
          rw [smul_smul]
          norm_num

/-- The two-color hopping Hamiltonian is invisible to the grade-zero Kantor
cross-corner channel, while its two grade-one channels recover the oriented
return commutator with opposite signs. This is the finite algebraic
Cantor-to-Kantor connection; it does not identify these channels with a
Golay or Leech code. -/
theorem color_hopping_kantor_grade_profile
    {P_R P_G A C : B}
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) :
    kantorG0 P_R (A * P_G) (P_G * C)
        (genPhi P_R (A * P_G) (P_G * C)) = 0 ∧
    kantorGp1 P_R (A * P_G)
        (genPhi P_R (A * P_G) (P_G * C)) =
      genSig P_R (A * P_G) (P_G * C) ∧
    kantorGm1 P_R (P_G * C)
        (genPhi P_R (A * P_G) (P_G * C)) =
      -genSig P_R (A * P_G) (P_G * C) := by
  have hCorners := color_hopping_is_red_peirce_hopping
    (P_R := P_R) (P_G := P_G) (A := A) (C := C) hRG hGR
  let Np := conePlus P_R (A * P_G)
  let Nm := coneMinus P_R (P_G * C)
  have hNpsq : Np * Np = 0 := by
    dsimp [Np]
    rw [hCorners.1]
    calc
      (P_R * A * P_G) * (P_R * A * P_G) =
          P_R * A * (P_G * P_R) * A * P_G := by noncomm_ring
      _ = 0 := by rw [hGR]; simp
  have hNmsq : Nm * Nm = 0 := by
    dsimp [Nm]
    rw [hCorners.2]
    calc
      (P_G * C * P_R) * (P_G * C * P_R) =
          P_G * C * (P_R * P_G) * C * P_R := by noncomm_ring
      _ = 0 := by rw [hRG]; simp
  have hG0 : kantorG0 P_R (A * P_G) (P_G * C)
      (genPhi P_R (A * P_G) (P_G * C)) = 0 := by
    change kantorTriple Np (Np + Nm) Nm = 0
    unfold kantorTriple
    have h1 : Np * Np * Nm = 0 := by rw [hNpsq]; simp
    have h2 : Np * Nm * Nm = 0 := by
      calc
        Np * Nm * Nm = Np * (Nm * Nm) := by simp only [mul_assoc]
        _ = 0 := by rw [hNmsq]; simp
    have h3 : Nm * Np * Np = 0 := by
      calc
        Nm * Np * Np = Nm * (Np * Np) := by simp only [mul_assoc]
        _ = 0 := by rw [hNpsq]; simp
    have h4 : Nm * Nm * Np = 0 := by rw [hNmsq]; simp
    calc
      Np * (Np + Nm) * Nm + Nm * (Np + Nm) * Np =
          (Np * Np * Nm + Np * Nm * Nm) +
            (Nm * Np * Np + Nm * Nm * Np) := by noncomm_ring
      _ = 0 := by rw [h1, h2, h3, h4]; simp
  have hGp1 : kantorGp1 P_R (A * P_G)
      (genPhi P_R (A * P_G) (P_G * C)) =
      genSig P_R (A * P_G) (P_G * C) := by
    change comm Np (Np + Nm) = comm Np Nm
    unfold comm
    noncomm_ring [hNpsq]
  have hGm1 : kantorGm1 P_R (P_G * C)
      (genPhi P_R (A * P_G) (P_G * C)) =
      -genSig P_R (A * P_G) (P_G * C) := by
    change comm Nm (Np + Nm) = -comm Np Nm
    unfold comm
    noncomm_ring [hNmsq]
  exact ⟨hG0, hGp1, hGm1⟩

/-- The scale-12 Kantor core and scale-144 return specialize to red-green
Cantor hopping. The core preserves the tripotent charge, and the bilateral
return is a two-sided sandwich by the hopping return metric. -/
theorem color_hopping_golay_core_charge_and_scale_144_return
    {P_R P_G A C X : B}
    (hR : P_R * P_R = P_R) (hG : P_G * P_G = P_G)
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) :
    comm (colorTripotent P_R P_G)
      (golay12Core P_R (A * P_G) (P_G * C) X) = 0 ∧
    golay12Core P_R (A * P_G) (P_G * C)
        (golay12Core P_R (A * P_G) (P_G * C) X) +
      golay12Ext P_R (A * P_G) (P_G * C)
        (golay12Ext P_R (A * P_G) (P_G * C) X) =
      (144 : ℤ) •
        (genV P_R (A * P_G) (P_G * C) * X *
          genV P_R (A * P_G) (P_G * C)) := by
  have hCore := (archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes
      hR (A * P_G) (P_G * C) X).2.1
  have hCompression :=
    (archetype_A63_golay_144_leech_576_quadratic_compression_and_eigen_algebra
      hR (A * P_G) (P_G * C) X).2.2.2.2.2.2.2.2.2.1
  constructor
  · rw [hCore]
    have hCross : comm (colorTripotent P_R P_G)
        (sandwichCross P_R (A * P_G) (P_G * C) X) = 0 := by
      have hSandwich : sandwichCross P_R (A * P_G) (P_G * C) X =
          P_R * (A * P_G * X * P_G * C) * P_R +
            P_G * (C * P_R * X * P_R * A) * P_G := by
        have hCorners := color_hopping_is_red_peirce_hopping
          (P_R := P_R) (P_G := P_G) (A := A) (C := C) hRG hGR
        unfold sandwichCross
        rw [hCorners.1, hCorners.2]
        simp only [mul_assoc]
      have hTR : (P_R - P_G) * P_R = P_R := by
        rw [sub_mul, hR, hGR, sub_zero]
      have hRT : P_R * (P_R - P_G) = P_R := by
        rw [mul_sub, hR, hRG, sub_zero]
      have hTG : (P_R - P_G) * P_G = -P_G := by
        rw [sub_mul, hRG, hG, zero_sub]
      have hGT : P_G * (P_R - P_G) = -P_G := by
        rw [mul_sub, hGR, hG, zero_sub]
      rw [hSandwich]
      unfold colorTripotent comm
      have hExpand :
          (P_R - P_G) * (P_R * (A * P_G * X * P_G * C) * P_R +
            P_G * (C * P_R * X * P_R * A) * P_G) -
          (P_R * (A * P_G * X * P_G * C) * P_R +
            P_G * (C * P_R * X * P_R * A) * P_G) * (P_R - P_G) =
          ((P_R - P_G) * P_R) * (A * P_G * X * P_G * C) * P_R +
            ((P_R - P_G) * P_G) * (C * P_R * X * P_R * A) * P_G -
          (P_R * (A * P_G * X * P_G * C) * (P_R * (P_R - P_G)) +
            P_G * (C * P_R * X * P_R * A) * (P_G * (P_R - P_G))) := by
        noncomm_ring
      rw [hExpand, hTR, hTG, hRT, hGT]
      noncomm_ring
    calc
      comm (colorTripotent P_R P_G)
          ((12 : ℤ) • sandwichCross P_R (A * P_G) (P_G * C) X) =
        (12 : ℤ) • comm (colorTripotent P_R P_G)
          (sandwichCross P_R (A * P_G) (P_G * C) X) := by
        unfold comm
        simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
      _ = 0 := by rw [hCross]; simp
  · exact hCompression

/-! ### 5. Stage `G₃` (`A₆₄–A₆₅`): All-Scale `(k, n) ∈ ℕ × ℕ` Defect Tower Channel Isolation -/

/-- Orthogonality-preserving bifurcation of `idempotencyDefect`. -/
theorem idemDefect_orthogonal_split {X Y : B} (hXY : X * Y = 0) (hYX : Y * X = 0) :
    idempotencyDefect (X + Y) = idempotencyDefect X + idempotencyDefect Y ∧
    idempotencyDefect X * idempotencyDefect Y = 0 ∧
    idempotencyDefect Y * idempotencyDefect X = 0 := by
  have hXYY : X * (Y * Y) = 0 := by rw [← mul_assoc, hXY, zero_mul]
  have hYXX : Y * (X * X) = 0 := by rw [← mul_assoc, hYX, zero_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [idempotencyDefect, add_mul, mul_add, hXY, hYX]; abel
  · simp only [idempotencyDefect, sub_mul, mul_sub, mul_assoc, hXY, hXYY, mul_zero]; abel
  · simp only [idempotencyDefect, sub_mul, mul_sub, mul_assoc, hYX, hYXX, mul_zero]; abel

/-- **Theorem `G₃.1` (`archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower`):**
All-scale `(k, n) ∈ ℕ × ℕ` idempotence of `daughterIdemTower k P A` and orthogonal sheet splitting
of `mandelbrotTower n (genV P A C)`. -/
theorem archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    (daughterIdemTower k P A * daughterIdemTower k P A = daughterIdemTower k P A ∧
     conePlus (daughterIdemTower k P A) C * conePlus (daughterIdemTower k P A) C = 0 ∧
     coneMinus (daughterIdemTower k P A) A * coneMinus (daughterIdemTower k P A) A = 0) ∧
    (mandelbrotTower n (genV P A C) =
       mandelbrotTower n (qgtPlus P A C) + mandelbrotTower n (qgtMinus P A C) ∧
     mandelbrotTower n (qgtPlus P A C) * mandelbrotTower n (qgtMinus P A C) = 0 ∧
     mandelbrotTower n (qgtMinus P A C) * mandelbrotTower n (qgtPlus P A C) = 0) := by
  constructor
  · induction k with
    | zero =>
      dsimp [daughterIdemTower]
      refine ⟨hP, ?_, ?_⟩ <;> peirce_abel_golay hP
    | succ k ih =>
      rcases ih with ⟨hPk, _, _⟩
      have hPk1 : daughterIdemTower (k + 1) P A * daughterIdemTower (k + 1) P A =
          daughterIdemTower (k + 1) P A := by
        dsimp [daughterIdemTower]
        peirce_abel_golay hPk
      refine ⟨hPk1, by peirce_nf hPk1, by peirce_nf hPk1⟩
  · induction n with
    | zero =>
      dsimp [mandelbrotTower]
      refine ⟨?_, ?_, ?_⟩ <;> peirce_abel_golay hP
    | succ n ih =>
      rcases ih with ⟨hSplit, hOrth1, hOrth2⟩
      dsimp [mandelbrotTower]
      rw [hSplit]
      exact idemDefect_orthogonal_split hOrth1 hOrth2

/-- Closure of the centralizer `[G, Z] = 0` under `idempotencyDefect`. -/
lemma comm_idemDefect_of_comm {G Z : B} (hGZ : comm G Z = 0) :
    comm G (idempotencyDefect Z) = 0 ∧ -comm G (comm G Z) = 0 := by
  have hEq : G * Z = Z * G := sub_eq_zero.mp hGZ
  refine ⟨?_, by rw [hGZ]; unfold comm; rw [mul_zero, zero_mul, sub_self, neg_zero]⟩
  unfold comm idempotencyDefect
  calc G * (Z * Z - Z) - (Z * Z - Z) * G
    _ = (G * Z) * Z - G * Z - Z * (Z * G) + Z * G := by
        simp only [mul_sub, sub_mul, mul_assoc]; abel
    _ = (Z * G) * Z - Z * G - Z * (G * Z) + Z * G := by rw [hEq]
    _ = 0 := by simp only [mul_assoc]; abel

/-- **Theorem `G₃.2` (`archetype_A65_all_scale_fractal_codeword_error_immunity`):**
For all `(k, n) ∈ ℕ × ℕ`, `V_{k, n} = mandelbrotTower n (genV P_k A C)` commutes with `Φ_k, J_k, Σ_k`,
is annihilated by `hProjPhi`, `hProjJ`, `hProjSig`, and satisfies
`mog24V P_k A C V_{k, n} = (24 : ℤ) • ((V_k * V_k) * V_{k, n})`. -/
theorem archetype_A65_all_scale_fractal_codeword_error_immunity
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let P_k := daughterIdemTower k P A
    let V_k := genV P_k A C
    let V_kn := mandelbrotTower n V_k
    comm (genPhi P_k A C) V_kn = 0 ∧
    comm (genJ P_k A C) V_kn = 0 ∧
    comm (genSig P_k A C) V_kn = 0 ∧
    hProjPhi P_k A C V_kn = 0 ∧
    hProjJ P_k A C V_kn = 0 ∧
    hProjSig P_k A C V_kn = 0 ∧
    mog24V P_k A C V_kn = (24 : ℤ) • ((V_k * V_k) * V_kn) := by
  intro P_k V_k V_kn
  have hPk : P_k * P_k = P_k :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower hP A C k 0).1.1
  have hCommAll :
      comm (genPhi P_k A C) V_kn = 0 ∧
      comm (genJ P_k A C) V_kn = 0 ∧
      comm (genSig P_k A C) V_kn = 0 := by
    dsimp [V_kn]
    induction n with
    | zero =>
      dsimp [mandelbrotTower, V_k]
      refine ⟨?_, ?_, ?_⟩ <;> peirce_abel_golay hPk
    | succ n ih =>
      rcases ih with ⟨hPhi, hJ, hSig⟩
      dsimp [mandelbrotTower]
      exact ⟨(comm_idemDefect_of_comm hPhi).1,
             (comm_idemDefect_of_comm hJ).1,
             (comm_idemDefect_of_comm hSig).1⟩
  rcases hCommAll with ⟨hC_Phi, hC_J, hC_Sig⟩
  have hM_Phi : derivSqPhi P_k A C V_kn = 0 := by
    unfold derivSqPhi; rw [hC_Phi]; unfold comm; rw [mul_zero, zero_mul, sub_self, neg_zero]
  have hM_J : derivSqJ P_k A C V_kn = 0 := by
    unfold derivSqJ; rw [hC_J]; unfold comm; rw [mul_zero, zero_mul, sub_self]
  have hM_Sig : derivSqSig P_k A C V_kn = 0 := by
    unfold derivSqSig; rw [hC_Sig]; unfold comm; rw [mul_zero, zero_mul, sub_self, neg_zero]
  refine ⟨hC_Phi, hC_J, hC_Sig, ?_, ?_, ?_, ?_⟩
  · unfold hProjPhi; rw [hM_Phi, hM_J, hM_Sig, mul_zero, sub_self, sub_zero]
  · unfold hProjJ; rw [hM_J, hM_Phi, hM_Sig, mul_zero, sub_self, sub_zero]
  · unfold hProjSig; rw [hM_Sig, hM_Phi, hM_J, mul_zero, sub_self, sub_zero]
  · unfold mog24V hProjV
    rw [hM_Phi, hM_J, hM_Sig, mul_zero, add_zero, add_zero, add_zero, ← mul_smul]
    rfl

/-! ### 6. Stage `G₄` (`A₆₆–A₆₇`): All-Scale Cone–Sheet Braiding & Chiral Branch Isolation -/

/-- Invariance of the 6-fold cone–sheet braiding relations under `idempotencyDefect`. -/
lemma idemDefect_cone_sheet_braiding {N_p N_m X Y : B}
    (h1 : N_p * X = 0) (h2 : Y * N_p = 0)
    (h3 : N_m * Y = 0) (h4 : X * N_m = 0)
    (h5 : N_p * Y = X * N_p) (h6 : N_m * X = Y * N_m) :
    N_p * idempotencyDefect X = 0 ∧
    idempotencyDefect Y * N_p = 0 ∧
    N_m * idempotencyDefect Y = 0 ∧
    idempotencyDefect X * N_m = 0 ∧
    N_p * idempotencyDefect Y = idempotencyDefect X * N_p ∧
    N_m * idempotencyDefect X = idempotencyDefect Y * N_m := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold idempotencyDefect; rw [mul_sub, ← mul_assoc, h1, zero_mul, sub_self]
  · unfold idempotencyDefect; rw [sub_mul, mul_assoc, h2, mul_zero, sub_self]
  · unfold idempotencyDefect; rw [mul_sub, ← mul_assoc, h3, zero_mul, sub_self]
  · unfold idempotencyDefect; rw [sub_mul, mul_assoc, h4, mul_zero, sub_self]
  · unfold idempotencyDefect
    calc N_p * (Y * Y - Y)
      _ = (N_p * Y) * Y - N_p * Y := by rw [mul_sub, mul_assoc]
      _ = (X * N_p) * Y - X * N_p := by rw [h5]
      _ = X * (N_p * Y) - X * N_p := by rw [mul_assoc]
      _ = X * (X * N_p) - X * N_p := by rw [h5]
      _ = (X * X - X) * N_p := by rw [sub_mul, mul_assoc]
  · unfold idempotencyDefect
    calc N_m * (X * X - X)
      _ = (N_m * X) * X - N_m * X := by rw [mul_sub, mul_assoc]
      _ = (Y * N_m) * X - Y * N_m := by rw [h6]
      _ = Y * (N_m * X) - Y * N_m := by rw [mul_assoc]
      _ = Y * (Y * N_m) - Y * N_m := by rw [h6]
      _ = (Y * Y - Y) * N_m := by rw [sub_mul, mul_assoc]

/-- All-scale `(k, n) ∈ ℕ × ℕ` 6-fold cone–sheet braiding theorem. -/
theorem cone_sheet_braiding_all_scales
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let P_k := daughterIdemTower k P A
    let N_p := conePlus P_k A
    let N_m := coneMinus P_k C
    let X_n := mandelbrotTower n (qgtPlus P_k A C)
    let Y_n := mandelbrotTower n (qgtMinus P_k A C)
    N_p * X_n = 0 ∧
    Y_n * N_p = 0 ∧
    N_m * Y_n = 0 ∧
    X_n * N_m = 0 ∧
    N_p * Y_n = X_n * N_p ∧
    N_m * X_n = Y_n * N_m := by
  intro P_k N_p N_m X_n Y_n
  have hPk : P_k * P_k = P_k :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower hP A C k 0).1.1
  dsimp [X_n, Y_n, N_p, N_m]
  induction n with
  | zero =>
    dsimp [mandelbrotTower]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel_golay hPk
  | succ n ih =>
    rcases ih with ⟨h1, h2, h3, h4, h5, h6⟩
    dsimp [mandelbrotTower]
    exact idemDefect_cone_sheet_braiding h1 h2 h3 h4 h5 h6

/-- **Theorem `G₄.1` (`archetype_A66_all_scale_cone_sheet_braiding_and_leech_24_sector_isolation`):**
All-scale `golay24` sector isolation of `V_{k,n}` and anticommutation of `Σ_{k,n}` with `N₊, N₋, Φ, J`. -/
theorem archetype_A66_all_scale_cone_sheet_braiding_and_leech_24_sector_isolation
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let P_k := daughterIdemTower k P A
    let V_k := genV P_k A C
    let V_kn := mandelbrotTower n V_k
    let Sig_kn := chiralFractalBranch n P_k A C
    comm (conePlus P_k A) V_kn = 0 ∧
    comm (coneMinus P_k C) V_kn = 0 ∧
    golay24Gp1 P_k A C V_kn = 0 ∧
    golay24Gm1 P_k A C V_kn = 0 ∧
    golay24Gp2 P_k A C V_kn = 0 ∧
    golay24Gm2 P_k A C V_kn = 0 ∧
    golay24G0 P_k A C V_kn = (24 : ℤ) • (V_k * V_kn) ∧
    anticomm (conePlus P_k A) Sig_kn = 0 ∧
    anticomm (coneMinus P_k C) Sig_kn = 0 ∧
    anticomm (genPhi P_k A C) Sig_kn = 0 ∧
    anticomm (genJ P_k A C) Sig_kn = 0 := by
  intro P_k V_k V_kn Sig_kn
  have hPk : P_k * P_k = P_k :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower hP A C k 0).1.1
  have hSplit : V_kn = mandelbrotTower n (qgtPlus P_k A C) + mandelbrotTower n (qgtMinus P_k A C) :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower hPk A C 0 n).2.1
  rcases cone_sheet_braiding_all_scales hP A C k n with ⟨h1, h2, h3, h4, h5, h6⟩
  set N_p := conePlus P_k A
  set N_m := coneMinus P_k C
  set X_n := mandelbrotTower n (qgtPlus P_k A C)
  set Y_n := mandelbrotTower n (qgtMinus P_k A C)
  have hNpSq : N_p * N_p = 0 := by dsimp [N_p]; peirce_abel_golay hPk
  have hNmSq : N_m * N_m = 0 := by dsimp [N_m]; peirce_abel_golay hPk
  have hNpV : N_p * V_kn = V_kn * N_p := by
    rw [hSplit]
    calc N_p * (X_n + Y_n)
      _ = N_p * X_n + N_p * Y_n := by rw [mul_add]
      _ = 0 + X_n * N_p := by rw [h1, h5]
      _ = X_n * N_p + 0 := by abel
      _ = X_n * N_p + Y_n * N_p := by rw [h2]
      _ = (X_n + Y_n) * N_p := by rw [add_mul]
  have hNmV : N_m * V_kn = V_kn * N_m := by
    rw [hSplit]
    calc N_m * (X_n + Y_n)
      _ = N_m * X_n + N_m * Y_n := by rw [mul_add]
      _ = Y_n * N_m + 0 := by rw [h6, h3]
      _ = 0 + Y_n * N_m := by abel
      _ = X_n * N_m + Y_n * N_m := by rw [h4]
      _ = (X_n + Y_n) * N_m := by rw [add_mul]
  have hCommNp : comm N_p V_kn = 0 := sub_eq_zero.mpr hNpV
  have hCommNm : comm N_m V_kn = 0 := sub_eq_zero.mpr hNmV
  have hGp1 : kantorGp1 P_k A V_kn = 0 := hCommNp
  have hGm1 : kantorGm1 P_k C V_kn = 0 := hCommNm
  have hGp2 : kantorGp2 P_k A V_kn = 0 := by
    unfold kantorGp2; change (N_p * V_kn) * N_p = 0
    rw [hNpV, mul_assoc, hNpSq, mul_zero]
  have hGm2 : kantorGm2 P_k C V_kn = 0 := by
    unfold kantorGm2; change (N_m * V_kn) * N_m = 0
    rw [hNmV, mul_assoc, hNmSq, mul_zero]
  have hG0 : kantorG0 P_k A C V_kn = V_k * V_kn := by
    unfold kantorG0 kantorTriple
    change (N_p * V_kn) * N_m + (N_m * V_kn) * N_p = (N_p * N_m + N_m * N_p) * V_kn
    calc (N_p * V_kn) * N_m + (N_m * V_kn) * N_p
      _ = N_p * (V_kn * N_m) + N_m * (V_kn * N_p) := by rw [mul_assoc, mul_assoc]
      _ = N_p * (N_m * V_kn) + N_m * (N_p * V_kn) := by rw [← hNmV, ← hNpV]
      _ = (N_p * N_m) * V_kn + (N_m * N_p) * V_kn := by rw [← mul_assoc, ← mul_assoc]
      _ = (N_p * N_m + N_m * N_p) * V_kn := by rw [← add_mul]
  have hA61 := archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hPk A C V_kn
  have hAntiNp : anticomm N_p Sig_kn = 0 := by
    unfold anticomm
    change N_p * (X_n - Y_n) + (X_n - Y_n) * N_p = 0
    calc N_p * (X_n - Y_n) + (X_n - Y_n) * N_p
      _ = (N_p * X_n - N_p * Y_n) + (X_n * N_p - Y_n * N_p) := by rw [mul_sub, sub_mul]
      _ = (0 - X_n * N_p) + (X_n * N_p - 0) := by rw [h1, h5, h2]
      _ = 0 := by abel
  have hAntiNm : anticomm N_m Sig_kn = 0 := by
    unfold anticomm
    change N_m * (X_n - Y_n) + (X_n - Y_n) * N_m = 0
    calc N_m * (X_n - Y_n) + (X_n - Y_n) * N_m
      _ = (N_m * X_n - N_m * Y_n) + (X_n * N_m - Y_n * N_m) := by rw [mul_sub, sub_mul]
      _ = (Y_n * N_m - 0) + (0 - Y_n * N_m) := by rw [h6, h3, h4]
      _ = 0 := by abel
  refine ⟨hCommNp, hCommNm, ?_, ?_, ?_, ?_, ?_, hAntiNp, hAntiNm, ?_, ?_⟩
  · rw [hA61.2.2.2.2.2.2.1, hGp1, smul_zero]
  · rw [hA61.2.2.2.2.2.2.2.1, hGm1, smul_zero]
  · rw [hA61.2.2.2.2.2.2.2.2.1, hGp2, smul_zero]
  · rw [hA61.2.2.2.2.2.2.2.2.2.1, hGm2, smul_zero]
  · rw [hA61.2.2.2.2.2.1, hG0]
  · calc anticomm (genPhi P_k A C) Sig_kn
      _ = anticomm N_p Sig_kn + anticomm N_m Sig_kn := by
        unfold anticomm genPhi; change (N_p + N_m) * Sig_kn + Sig_kn * (N_p + N_m) = _
        simp only [add_mul, mul_add]; abel
      _ = 0 := by rw [hAntiNp, hAntiNm, add_zero]
  · calc anticomm (genJ P_k A C) Sig_kn
      _ = anticomm N_p Sig_kn - anticomm N_m Sig_kn := by
        unfold anticomm genJ; change (N_p - N_m) * Sig_kn + Sig_kn * (N_p - N_m) = _
        simp only [sub_mul, mul_sub]; abel
      _ = 0 := by rw [hAntiNp, hAntiNm, sub_self]

/-- The existing all-depth charge-zero Golay channel applies to the
red-green hopping carrier. Its coefficient is the repository's scale-24
normalization; the unscaled Kantor core has coefficient one. -/
theorem color_hopping_all_depth_golay24_core
    {P_R P_G A C : B}
    (hR : P_R * P_R = P_R) (n : ℕ) :
    let V := genV P_R (A * P_G) (P_G * C)
    golay24G0 P_R (A * P_G) (P_G * C) (mandelbrotTower n V) =
      (24 : ℤ) • (V * mandelbrotTower n V) := by
  dsimp
  have h := archetype_A66_all_scale_cone_sheet_braiding_and_leech_24_sector_isolation
    hR (A * P_G) (P_G * C) 0 n
  dsimp [daughterIdemTower] at h
  exact h.2.2.2.2.2.2.1

/-- The unscaled grade-zero Kantor action on the red-green defect tower has
coefficient one. This is the raw operator identity underlying the scale-24
channel statement above. -/
theorem color_hopping_all_depth_kantor_core
    {P_R P_G A C : B}
    (hR : P_R * P_R = P_R) (n : ℕ) :
    let V := genV P_R (A * P_G) (P_G * C)
    kantorG0 P_R (A * P_G) (P_G * C) (mandelbrotTower n V) =
      V * mandelbrotTower n V := by
  dsimp
  have hVcomm : comm (genV P_R (A * P_G) (P_G * C))
      (mandelbrotTower n (genV P_R (A * P_G) (P_G * C))) = 0 := by
    induction n with
    | zero =>
        change genV P_R (A * P_G) (P_G * C) *
            (genV P_R (A * P_G) (P_G * C) * genV P_R (A * P_G) (P_G * C) -
              genV P_R (A * P_G) (P_G * C)) -
          (genV P_R (A * P_G) (P_G * C) * genV P_R (A * P_G) (P_G * C) -
            genV P_R (A * P_G) (P_G * C)) *
              genV P_R (A * P_G) (P_G * C) = 0
        noncomm_ring
    | succ n ih =>
        simpa [mandelbrotTower] using (comm_idemDefect_of_comm ih).1
  have h := archetype_A66_all_scale_cone_sheet_braiding_and_leech_24_sector_isolation
    hR (A * P_G) (P_G * C) 0 n
  dsimp [daughterIdemTower] at h
  have hNp := (h.1)
  have hNm := h.2.1
  have hNpEq : conePlus P_R (A * P_G) * mandelbrotTower n
      (genV P_R (A * P_G) (P_G * C)) =
      mandelbrotTower n (genV P_R (A * P_G) (P_G * C)) *
        conePlus P_R (A * P_G) := sub_eq_zero.mp hNp
  have hNmEq : coneMinus P_R (P_G * C) * mandelbrotTower n
      (genV P_R (A * P_G) (P_G * C)) =
      mandelbrotTower n (genV P_R (A * P_G) (P_G * C)) *
        coneMinus P_R (P_G * C) := sub_eq_zero.mp hNm
  change (conePlus P_R (A * P_G) *
      mandelbrotTower n (genV P_R (A * P_G) (P_G * C)) *
      coneMinus P_R (P_G * C) +
      coneMinus P_R (P_G * C) *
      mandelbrotTower n (genV P_R (A * P_G) (P_G * C)) *
      conePlus P_R (A * P_G)) =
    genV P_R (A * P_G) (P_G * C) *
      mandelbrotTower n (genV P_R (A * P_G) (P_G * C))
  calc
    _ = mandelbrotTower n (genV P_R (A * P_G) (P_G * C)) *
          (conePlus P_R (A * P_G) * coneMinus P_R (P_G * C) +
           coneMinus P_R (P_G * C) * conePlus P_R (A * P_G)) := by
        noncomm_ring [hNpEq, hNmEq]
    _ = mandelbrotTower n (genV P_R (A * P_G) (P_G * C)) *
          genV P_R (A * P_G) (P_G * C) := rfl
    _ = genV P_R (A * P_G) (P_G * C) *
          mandelbrotTower n (genV P_R (A * P_G) (P_G * C)) :=
        (sub_eq_zero.mp hVcomm).symm



/-- Every finite defect iterate of the Cantor return metric remains in the
zero-charge diagonal color sector. The seed is a sum of red and green return
corners, and the defect operation preserves commutation with the tripotent. -/
theorem color_hopping_tripoten_centralizes_defect_tower
    {P_R P_G A C : B}
    (hR : P_R * P_R = P_R) (hG : P_G * P_G = P_G)
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) (n : ℕ) :
    comm (colorTripotent P_R P_G)
      (mandelbrotTower n (genV P_R (A * P_G) (P_G * C))) = 0 := by
  have hCorners := color_hopping_is_red_peirce_hopping
    (P_R := P_R) (P_G := P_G) (A := A) (C := C) hRG hGR
  have hPlus : conePlus P_R (A * P_G) * coneMinus P_R (P_G * C) =
      P_R * (A * P_G * C) * P_R := by
    rw [hCorners.1, hCorners.2]
    calc
      (P_R * A * P_G) * (P_G * C * P_R) =
          P_R * A * (P_G * P_G) * C * P_R := by noncomm_ring
      _ = P_R * (A * P_G * C) * P_R := by rw [hG]; noncomm_ring
  have hMinus : coneMinus P_R (P_G * C) * conePlus P_R (A * P_G) =
      P_G * (C * P_R * A) * P_G := by
    rw [hCorners.1, hCorners.2]
    calc
      (P_G * C * P_R) * (P_R * A * P_G) =
          P_G * C * (P_R * P_R) * A * P_G := by noncomm_ring
      _ = P_G * (C * P_R * A) * P_G := by rw [hR]; noncomm_ring
  have hDiag := colorTripotent_commutes_with_diagonal_corners
    (P_R := P_R) (P_G := P_G) (X := A * P_G * C) (Y := C * P_R * A)
    hR hG hRG hGR
  have hSeed : comm (colorTripotent P_R P_G)
      (genV P_R (A * P_G) (P_G * C)) = 0 := by
    change comm (colorTripotent P_R P_G)
      (conePlus P_R (A * P_G) * coneMinus P_R (P_G * C) +
       coneMinus P_R (P_G * C) * conePlus P_R (A * P_G)) = 0
    rw [hPlus, hMinus]
    unfold comm
    rw [mul_add, add_mul, sub_eq_zero.mp hDiag.1, sub_eq_zero.mp hDiag.2]
    simp
  induction n with
  | zero =>
      simpa [mandelbrotTower] using (comm_idemDefect_of_comm hSeed).1
  | succ n ih =>
      simpa [mandelbrotTower] using (comm_idemDefect_of_comm ih).1


/-- The deleted blue corner annihilates every finite return-metric defect
iterate on both sides. Thus the finite Cantor–Mandelbrot tower stays supported
on the two retained color corners. -/
theorem color_hopping_gap_annihilates_defect_tower
    {P_R P_G A C : B}
    (hR : P_R * P_R = P_R) (hG : P_G * P_G = P_G)
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) (n : ℕ) :
    colorBlue P_R P_G *
        mandelbrotTower n (genV P_R (A * P_G) (P_G * C)) = 0 ∧
    mandelbrotTower n (genV P_R (A * P_G) (P_G * C)) *
        colorBlue P_R P_G = 0 := by
  have hGap := color_hopping_gap_support_and_charge_ladder
    (P_R := P_R) (P_G := P_G) (A := A) (C := C) hR hG hRG hGR
  have hMetric := color_hopping_charge_and_return_metric
    (P_R := P_R) (P_G := P_G) (A := A) (C := C) hR hG hRG hGR
  have hSeedL : colorBlue P_R P_G * genV P_R (A * P_G) (P_G * C) = 0 := by
    rw [hMetric.2]
    calc
      colorBlue P_R P_G *
          (genPhi P_R (A * P_G) (P_G * C) *
           genPhi P_R (A * P_G) (P_G * C)) =
          (colorBlue P_R P_G * genPhi P_R (A * P_G) (P_G * C)) *
            genPhi P_R (A * P_G) (P_G * C) := by noncomm_ring
      _ = 0 := by rw [hGap.1]; simp
  have hSeedR : genV P_R (A * P_G) (P_G * C) * colorBlue P_R P_G = 0 := by
    rw [hMetric.2]
    calc
      (genPhi P_R (A * P_G) (P_G * C) *
       genPhi P_R (A * P_G) (P_G * C)) * colorBlue P_R P_G =
          genPhi P_R (A * P_G) (P_G * C) *
            (genPhi P_R (A * P_G) (P_G * C) * colorBlue P_R P_G) := by
              noncomm_ring
      _ = 0 := by rw [hGap.2.1]; simp
  have hTower : ∀ m : ℕ,
      colorBlue P_R P_G * mandelbrotTower m
        (genV P_R (A * P_G) (P_G * C)) = 0 ∧
      mandelbrotTower m (genV P_R (A * P_G) (P_G * C)) *
        colorBlue P_R P_G = 0 := by
    intro m
    induction m with
    | zero =>
        simp only [mandelbrotTower, idempotencyDefect, mul_sub, sub_mul]
        constructor
        · rw [← mul_assoc, hSeedL]; simp
        · rw [mul_assoc, hSeedR]; simp
    | succ m ih =>
        simp only [mandelbrotTower, idempotencyDefect, mul_sub, sub_mul]
        constructor
        · rw [← mul_assoc, ih.1]; simp
        · rw [mul_assoc, ih.2]; simp
  exact hTower n

/-- The two transfer cyclotomic factors `1 + V` and `1 - V` centralize
every finite iterate of the color-hopping return metric's idempotency defect.
This connects the operator cyclotomic evaluations to the existing
Cantor–Mandelbrot tower without asserting spectral or limiting behavior. -/
theorem color_hopping_transfer_cyclotomic_centralizes_defect_tower
    {P_R P_G A C : B}
    (hR : P_R * P_R = P_R) (n : ℕ) :
    let V := genV P_R (A * P_G) (P_G * C)
    comm (cyclotomicSix (peirceTransfer P_R (A * P_G) (P_G * C)))
        (mandelbrotTower n V) = 0 ∧
    comm (cyclotomicSix (peirceTransferJ P_R (A * P_G) (P_G * C)))
        (mandelbrotTower n V) = 0 := by
  dsimp
  let V := genV P_R (A * P_G) (P_G * C)
  have hVComm : comm V (mandelbrotTower n V) = 0 := by
    induction n with
    | zero =>
      simp only [mandelbrotTower, idempotencyDefect, comm]
      noncomm_ring
    | succ n ih =>
      simpa [mandelbrotTower] using (comm_idemDefect_of_comm ih).1
  have hVEq : V * mandelbrotTower n V = mandelbrotTower n V * V :=
    sub_eq_zero.mp hVComm
  rcases transfer_cyclotomic_evaluations (P := P_R) hR
      (A * P_G) (P_G * C) with ⟨hPlus, hMinus⟩
  have hPlusComm : comm (1 + V) (mandelbrotTower n V) = 0 := by
    unfold comm
    simp only [add_mul, mul_add, one_mul, mul_one]
    rw [hVEq]
    abel
  have hMinusComm : comm (1 - V) (mandelbrotTower n V) = 0 := by
    unfold comm
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    rw [hVEq]
    abel
  exact ⟨by rw [hPlus]; exact hPlusComm,
    by rw [hMinus]; exact hMinusComm⟩

/-- The same transfer cyclotomic factors centralize each of the two
orthogonal Peirce-sheet defect iterates separately, not only their sum. The
proof propagates the two diagonal-corner centralizers through the defect
recursion. -/
theorem color_hopping_transfer_cyclotomic_centralizes_sheet_towers
    {P_R P_G A C : B}
    (hR : P_R * P_R = P_R) (n : ℕ) :
    let Xn := mandelbrotTower n (qgtPlus P_R (A * P_G) (P_G * C))
    let Yn := mandelbrotTower n (qgtMinus P_R (A * P_G) (P_G * C))
    comm (cyclotomicSix (peirceTransfer P_R (A * P_G) (P_G * C))) Xn = 0 ∧
    comm (cyclotomicSix (peirceTransfer P_R (A * P_G) (P_G * C))) Yn = 0 ∧
    comm (cyclotomicSix (peirceTransferJ P_R (A * P_G) (P_G * C))) Xn = 0 ∧
    comm (cyclotomicSix (peirceTransferJ P_R (A * P_G) (P_G * C))) Yn = 0 := by
  dsimp
  let V := genV P_R (A * P_G) (P_G * C)
  let Qp := qgtPlus P_R (A * P_G) (P_G * C)
  let Qm := qgtMinus P_R (A * P_G) (P_G * C)
  have hVQp : comm V Qp = 0 := by
    dsimp [V, Qp]
    peirce_abel_golay hR
  have hVQm : comm V Qm = 0 := by
    dsimp [V, Qm]
    peirce_abel_golay hR
  have hVQpTower : ∀ m : ℕ, comm V (mandelbrotTower m Qp) = 0 := by
    intro m
    induction m with
    | zero => simpa [mandelbrotTower] using (comm_idemDefect_of_comm hVQp).1
    | succ m ih =>
      simpa [mandelbrotTower] using (comm_idemDefect_of_comm ih).1
  have hVQmTower : ∀ m : ℕ, comm V (mandelbrotTower m Qm) = 0 := by
    intro m
    induction m with
    | zero => simpa [mandelbrotTower] using (comm_idemDefect_of_comm hVQm).1
    | succ m ih =>
      simpa [mandelbrotTower] using (comm_idemDefect_of_comm ih).1
  have hVXp := hVQpTower n
  have hVYm := hVQmTower n
  have hPlusEval := (transfer_cyclotomic_evaluations (P := P_R) hR
    (A * P_G) (P_G * C)).1
  have hMinusEval := (transfer_cyclotomic_evaluations (P := P_R) hR
    (A * P_G) (P_G * C)).2
  have hCommPlus (Y : B) (h : comm V Y = 0) : comm (1 + V) Y = 0 := by
    have hEq : V * Y = Y * V := sub_eq_zero.mp h
    unfold comm
    simp only [add_mul, mul_add, one_mul, mul_one]
    rw [hEq]
    abel
  have hCommMinus (Y : B) (h : comm V Y = 0) : comm (1 - V) Y = 0 := by
    have hEq : V * Y = Y * V := sub_eq_zero.mp h
    unfold comm
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    rw [hEq]
    abel
  exact ⟨by rw [hPlusEval]; exact hCommPlus _ hVXp,
    by rw [hPlusEval]; exact hCommPlus _ hVYm,
    by rw [hMinusEval]; exact hCommMinus _ hVXp,
    by rw [hMinusEval]; exact hCommMinus _ hVYm⟩

/-- The transfer cyclotomic pair identifies the two defect polynomials of
the hopping return metric: the `1 + V` factor has bar-defect, and the `1 - V`
factor has ordinary idempotency defect. Their ordered products both equal
`1 - V²` in the ambient noncommutative ring. -/
theorem color_hopping_cyclotomic_defect_and_ordered_product
    {P_R P_G A C : B}
    (hR : P_R * P_R = P_R) :
    let V := genV P_R (A * P_G) (P_G * C)
    idempotencyDefect (cyclotomicSix (peirceTransfer P_R (A * P_G) (P_G * C))) =
      idempotencyDefectBar V ∧
    idempotencyDefect (cyclotomicSix (peirceTransferJ P_R (A * P_G) (P_G * C))) =
      idempotencyDefect V ∧
    cyclotomicSix (peirceTransfer P_R (A * P_G) (P_G * C)) *
        cyclotomicSix (peirceTransferJ P_R (A * P_G) (P_G * C)) =
      1 - V * V ∧
    cyclotomicSix (peirceTransferJ P_R (A * P_G) (P_G * C)) *
        cyclotomicSix (peirceTransfer P_R (A * P_G) (P_G * C)) =
      1 - V * V := by
  dsimp
  let V := genV P_R (A * P_G) (P_G * C)
  rcases transfer_cyclotomic_evaluations (P := P_R) hR
      (A * P_G) (P_G * C) with ⟨hPlus, hMinus⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hPlus]
    unfold idempotencyDefect idempotencyDefectBar
    noncomm_ring
  · rw [hMinus]
    unfold idempotencyDefect
    noncomm_ring
  · rw [hPlus, hMinus]
    noncomm_ring
  · rw [hMinus, hPlus]
    noncomm_ring


/-- **Theorem `G₄.2` (`archetype_A67_all_scale_chiral_defect_leech_and_mog24_isolation`):**
All-scale `(k, n) ∈ ℕ × ℕ` chiral branch isolation: `golay24G0 P_k A C Σ_{k,n} = -(24 : ℤ) • (V_k * Σ_{k,n})`,
`hProjV = hProjPhi = hProjJ = 0` on `Σ_{k,n}`, and `mog24Sig P_k A C Σ_{k,n} = (24 : ℤ) • ((V_k * V_k) * Σ_{k,n})`. -/
theorem archetype_A67_all_scale_chiral_defect_leech_and_mog24_isolation
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let P_k := daughterIdemTower k P A
    let V_k := genV P_k A C
    let Sig_kn := chiralFractalBranch n P_k A C
    golay24Gp2 P_k A C Sig_kn = 0 ∧
    golay24Gm2 P_k A C Sig_kn = 0 ∧
    golay24G0 P_k A C Sig_kn = -((24 : ℤ) • (V_k * Sig_kn)) ∧
    derivSqPhi P_k A C Sig_kn = -((4 : ℤ) • (V_k * Sig_kn)) ∧
    derivSqJ P_k A C Sig_kn = -((4 : ℤ) • (V_k * Sig_kn)) ∧
    derivSqSig P_k A C Sig_kn = 0 ∧
    hProjV P_k A C Sig_kn = 0 ∧
    hProjPhi P_k A C Sig_kn = 0 ∧
    hProjJ P_k A C Sig_kn = 0 ∧
    mog24Sig P_k A C Sig_kn = (24 : ℤ) • ((V_k * V_k) * Sig_kn) := by
  intro P_k V_k Sig_kn
  have hPk : P_k * P_k = P_k :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower hP A C k 0).1.1
  rcases archetype_A66_all_scale_cone_sheet_braiding_and_leech_24_sector_isolation hP A C k n with
    ⟨_, _, _, _, _, _, _, hAntiNp, hAntiNm, hAntiPhi, hAntiJ⟩
  set N_p := conePlus P_k A
  set N_m := coneMinus P_k C
  have hNpSq : N_p * N_p = 0 := by dsimp [N_p]; peirce_abel_golay hPk
  have hNmSq : N_m * N_m = 0 := by dsimp [N_m]; peirce_abel_golay hPk
  have hNpS : N_p * Sig_kn = -(Sig_kn * N_p) := eq_neg_of_add_eq_zero_left hAntiNp
  have hNmS : N_m * Sig_kn = -(Sig_kn * N_m) := eq_neg_of_add_eq_zero_left hAntiNm
  have hGp2 : kantorGp2 P_k A Sig_kn = 0 := by
    unfold kantorGp2; change (N_p * Sig_kn) * N_p = 0
    rw [hNpS, neg_mul, mul_assoc, hNpSq, mul_zero, neg_zero]
  have hGm2 : kantorGm2 P_k C Sig_kn = 0 := by
    unfold kantorGm2; change (N_m * Sig_kn) * N_m = 0
    rw [hNmS, neg_mul, mul_assoc, hNmSq, mul_zero, neg_zero]
  have hVSig_comm : V_k * Sig_kn = Sig_kn * V_k := by
    change (N_p * N_m + N_m * N_p) * Sig_kn = Sig_kn * (N_p * N_m + N_m * N_p)
    calc (N_p * N_m + N_m * N_p) * Sig_kn
      _ = N_p * (N_m * Sig_kn) + N_m * (N_p * Sig_kn) := by rw [add_mul, mul_assoc, mul_assoc]
      _ = N_p * -(Sig_kn * N_m) + N_m * -(Sig_kn * N_p) := by rw [hNmS, hNpS]
      _ = -((N_p * Sig_kn) * N_m) - (N_m * Sig_kn) * N_p := by
          simp only [mul_neg, mul_assoc]; abel
      _ = -(-(Sig_kn * N_p) * N_m) - -(Sig_kn * N_m) * N_p := by rw [hNpS, hNmS]
      _ = Sig_kn * (N_p * N_m + N_m * N_p) := by
          simp only [neg_mul, neg_neg, mul_add, mul_assoc]; abel
  have hSigSig_comm : comm (genSig P_k A C) Sig_kn = 0 := by
    unfold comm genSig
    change (N_p * N_m - N_m * N_p) * Sig_kn - Sig_kn * (N_p * N_m - N_m * N_p) = 0
    calc (N_p * N_m - N_m * N_p) * Sig_kn - Sig_kn * (N_p * N_m - N_m * N_p)
      _ = N_p * (N_m * Sig_kn) - N_m * (N_p * Sig_kn) - Sig_kn * (N_p * N_m - N_m * N_p) := by
          rw [sub_mul, mul_assoc, mul_assoc]
      _ = N_p * -(Sig_kn * N_m) - N_m * -(Sig_kn * N_p) - Sig_kn * (N_p * N_m - N_m * N_p) := by
          rw [hNmS, hNpS]
      _ = -((N_p * Sig_kn) * N_m) + (N_m * Sig_kn) * N_p - Sig_kn * (N_p * N_m - N_m * N_p) := by
          simp only [mul_neg, mul_assoc]; abel
      _ = -(-(Sig_kn * N_p) * N_m) + -(Sig_kn * N_m) * N_p - Sig_kn * (N_p * N_m - N_m * N_p) := by
          rw [hNpS, hNmS]
      _ = 0 := by simp only [neg_mul, neg_neg, mul_sub, mul_assoc]; abel
  have hG0 : kantorG0 P_k A C Sig_kn = -(V_k * Sig_kn) := by
    unfold kantorG0 kantorTriple
    change (N_p * Sig_kn) * N_m + (N_m * Sig_kn) * N_p = -(V_k * Sig_kn)
    calc (N_p * Sig_kn) * N_m + (N_m * Sig_kn) * N_p
      _ = -(Sig_kn * N_p) * N_m + -(Sig_kn * N_m) * N_p := by rw [hNpS, hNmS]
      _ = -(Sig_kn * (N_p * N_m + N_m * N_p)) := by
          simp only [neg_mul, mul_add, mul_assoc]; abel
      _ = -(Sig_kn * V_k) := rfl
      _ = -(V_k * Sig_kn) := by rw [hVSig_comm]
  have hA61 := archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hPk A C Sig_kn
  have hPhiSq : genPhi P_k A C * genPhi P_k A C = V_k := by
    change genPhi P_k A C * genPhi P_k A C = genV P_k A C; peirce_nf hPk
  have hJSq : genJ P_k A C * genJ P_k A C = -V_k := by
    change genJ P_k A C * genJ P_k A C = -genV P_k A C; peirce_nf hPk
  have hPhiS : Sig_kn * genPhi P_k A C = -(genPhi P_k A C * Sig_kn) :=
    eq_neg_of_add_eq_zero_right hAntiPhi
  have hJS : Sig_kn * genJ P_k A C = -(genJ P_k A C * Sig_kn) :=
    eq_neg_of_add_eq_zero_right hAntiJ
  have hM_Phi : derivSqPhi P_k A C Sig_kn = -((4 : ℤ) • (V_k * Sig_kn)) := by
    unfold derivSqPhi comm
    have hSand : genPhi P_k A C * Sig_kn * genPhi P_k A C = -(V_k * Sig_kn) := by
      calc genPhi P_k A C * Sig_kn * genPhi P_k A C
        _ = genPhi P_k A C * (Sig_kn * genPhi P_k A C) := by rw [mul_assoc]
        _ = genPhi P_k A C * -(genPhi P_k A C * Sig_kn) := by rw [hPhiS]
        _ = -((genPhi P_k A C * genPhi P_k A C) * Sig_kn) := by simp only [mul_neg, mul_assoc]
        _ = -(V_k * Sig_kn) := by rw [hPhiSq]
    calc -(genPhi P_k A C * (genPhi P_k A C * Sig_kn - Sig_kn * genPhi P_k A C) -
           (genPhi P_k A C * Sig_kn - Sig_kn * genPhi P_k A C) * genPhi P_k A C)
      _ = -((genPhi P_k A C * genPhi P_k A C) * Sig_kn -
            genPhi P_k A C * Sig_kn * genPhi P_k A C -
            genPhi P_k A C * Sig_kn * genPhi P_k A C +
            Sig_kn * (genPhi P_k A C * genPhi P_k A C)) := by
          simp only [mul_sub, sub_mul, mul_assoc]; abel
      _ = -(V_k * Sig_kn - -(V_k * Sig_kn) - -(V_k * Sig_kn) + V_k * Sig_kn) := by
          rw [hPhiSq, hSand, ← hVSig_comm]
      _ = -((4 : ℤ) • (V_k * Sig_kn)) := by abel
  have hM_J : derivSqJ P_k A C Sig_kn = -((4 : ℤ) • (V_k * Sig_kn)) := by
    unfold derivSqJ comm
    have hSand : genJ P_k A C * Sig_kn * genJ P_k A C = V_k * Sig_kn := by
      calc genJ P_k A C * Sig_kn * genJ P_k A C
        _ = genJ P_k A C * (Sig_kn * genJ P_k A C) := by rw [mul_assoc]
        _ = genJ P_k A C * -(genJ P_k A C * Sig_kn) := by rw [hJS]
        _ = -((genJ P_k A C * genJ P_k A C) * Sig_kn) := by simp only [mul_neg, mul_assoc]
        _ = -((-V_k) * Sig_kn) := by rw [hJSq]
        _ = V_k * Sig_kn := by simp only [neg_mul, neg_neg]
    calc genJ P_k A C * (genJ P_k A C * Sig_kn - Sig_kn * genJ P_k A C) -
         (genJ P_k A C * Sig_kn - Sig_kn * genJ P_k A C) * genJ P_k A C
      _ = (genJ P_k A C * genJ P_k A C) * Sig_kn -
          genJ P_k A C * Sig_kn * genJ P_k A C -
          genJ P_k A C * Sig_kn * genJ P_k A C +
          Sig_kn * (genJ P_k A C * genJ P_k A C) := by
          simp only [mul_sub, sub_mul, mul_assoc]; abel
      _ = (-V_k) * Sig_kn - V_k * Sig_kn - V_k * Sig_kn + Sig_kn * (-V_k) := by
          rw [hJSq, hSand]
      _ = -(V_k * Sig_kn) - V_k * Sig_kn - V_k * Sig_kn - V_k * Sig_kn := by
          simp only [neg_mul, mul_neg, ← hVSig_comm]; abel
      _ = -((4 : ℤ) • (V_k * Sig_kn)) := by abel
  have hM_Sig : derivSqSig P_k A C Sig_kn = 0 := by
    unfold derivSqSig; rw [hSigSig_comm]; unfold comm; rw [mul_zero, zero_mul, sub_self, neg_zero]
  refine ⟨?_, ?_, ?_, hM_Phi, hM_J, hM_Sig, ?_, ?_, ?_, ?_⟩
  · rw [hA61.2.2.2.2.2.2.2.2.1, hGp2, smul_zero]
  · rw [hA61.2.2.2.2.2.2.2.2.2.1, hGm2, smul_zero]
  · rw [hA61.2.2.2.2.2.1, hG0, smul_neg]
  · unfold hProjV
    rw [hM_Phi, hM_J, hM_Sig, mul_neg, mul_smul_comm, ← mul_assoc]
    change (8 : ℤ) • ((V_k * V_k) * Sig_kn) +
           (-((4 : ℤ) • ((V_k * V_k) * Sig_kn)) + -((4 : ℤ) • ((V_k * V_k) * Sig_kn)) + 0) = 0
    abel
  · unfold hProjPhi
    rw [hM_Phi, hM_J, hM_Sig, sub_self, sub_zero]
  · unfold hProjJ
    rw [hM_J, hM_Phi, hM_Sig, sub_self, sub_zero]
  · unfold mog24Sig hProjSig
    rw [hM_Sig, hM_Phi, hM_J, mul_neg, mul_smul_comm, ← mul_assoc]
    change (3 : ℤ) • (0 - -((4 : ℤ) • ((V_k * V_k) * Sig_kn)) -
                         -((4 : ℤ) • ((V_k * V_k) * Sig_kn))) =
           (24 : ℤ) • ((V_k * V_k) * Sig_kn)
    have h8 : (0 : B) - -((4 : ℤ) • ((V_k * V_k) * Sig_kn)) -
                        -((4 : ℤ) • ((V_k * V_k) * Sig_kn)) =
              (8 : ℤ) • ((V_k * V_k) * Sig_kn) := by abel
    rw [h8, smul_smul]
    rfl

/-! ### 7. Stage `G₅` (`A₆₈`): All-Scale Single-Sheet Swap & Scale-12/24 Projections -/

/-- **Theorem `G₅.1` (`archetype_A68_single_sheet_leech_swap_and_golay_12_24_projections`):**
All-scale single-sheet swap `golay24G0 P_k A C X_n = (24 : ℤ) • (V_k * Y_n)` and
`golay24G0 P_k A C Y_n = (24 : ℤ) • (V_k * X_n)`, together with the Scale-12 half-projections
`mog24V P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * V_{k,n})` and
`mog24Sig P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * Σ_{k,n})`. -/
theorem archetype_A68_single_sheet_leech_swap_and_golay_12_24_projections
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let P_k := daughterIdemTower k P A
    let V_k := genV P_k A C
    let Sig_k := genSig P_k A C
    let X_n := mandelbrotTower n (qgtPlus P_k A C)
    let Y_n := mandelbrotTower n (qgtMinus P_k A C)
    let V_kn := mandelbrotTower n V_k
    let Sig_kn := chiralFractalBranch n P_k A C
    Sig_k * X_n = V_k * X_n ∧
    Sig_k * Y_n = -(V_k * Y_n) ∧
    (V_k - Sig_k) * X_n = 0 ∧
    (V_k + Sig_k) * Y_n = 0 ∧
    golay24G0 P_k A C X_n = (24 : ℤ) • (V_k * Y_n) ∧
    golay24G0 P_k A C Y_n = (24 : ℤ) • (V_k * X_n) ∧
    mog24V P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * V_kn) ∧
    mog24Sig P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * Sig_kn) ∧
    mog24V P_k A C X_n + mog24Sig P_k A C X_n = (24 : ℤ) • ((V_k * V_k) * X_n) ∧
    mog24V P_k A C X_n - mog24Sig P_k A C X_n = (24 : ℤ) • ((V_k * V_k) * Y_n) := by
  intro P_k V_k Sig_k X_n Y_n V_kn Sig_kn
  have hPk : P_k * P_k = P_k :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower hP A C k 0).1.1
  have hSplit : V_kn = X_n + Y_n :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower hPk A C 0 n).2.1
  rcases cone_sheet_braiding_all_scales hP A C k n with ⟨h1, h2, h3, h4, h5, h6⟩
  set N_p := conePlus P_k A
  set N_m := coneMinus P_k C
  have hSig_X : Sig_k * X_n = V_k * X_n := by
    change (N_p * N_m - N_m * N_p) * X_n = (N_p * N_m + N_m * N_p) * X_n
    calc (N_p * N_m - N_m * N_p) * X_n
      _ = N_p * (N_m * X_n) - N_m * (N_p * X_n) := by simp only [sub_mul, mul_assoc]
      _ = N_p * (N_m * X_n) + N_m * (N_p * X_n) := by rw [h1, mul_zero, sub_zero, add_zero]
      _ = (N_p * N_m + N_m * N_p) * X_n := by simp only [add_mul, mul_assoc]
  have hSig_Y : Sig_k * Y_n = -(V_k * Y_n) := by
    change (N_p * N_m - N_m * N_p) * Y_n = -((N_p * N_m + N_m * N_p) * Y_n)
    calc (N_p * N_m - N_m * N_p) * Y_n
      _ = N_p * (N_m * Y_n) - N_m * (N_p * Y_n) := by simp only [sub_mul, mul_assoc]
      _ = -(N_p * (N_m * Y_n) + N_m * (N_p * Y_n)) := by rw [h3, mul_zero, zero_sub, zero_add]
      _ = -((N_p * N_m + N_m * N_p) * Y_n) := by simp only [add_mul, mul_assoc]
  have hAnn_X : (V_k - Sig_k) * X_n = 0 := by rw [sub_mul, hSig_X, sub_self]
  have hAnn_Y : (V_k + Sig_k) * Y_n = 0 := by rw [add_mul, hSig_Y, add_neg_cancel]
  have hG0_X : kantorG0 P_k A C X_n = V_k * Y_n := by
    unfold kantorG0 kantorTriple
    change (N_p * X_n) * N_m + (N_m * X_n) * N_p = (N_p * N_m + N_m * N_p) * Y_n
    calc (N_p * X_n) * N_m + (N_m * X_n) * N_p
      _ = 0 * N_m + N_m * (X_n * N_p) := by rw [h1, mul_assoc]
      _ = N_p * (N_m * Y_n) + N_m * (N_p * Y_n) := by rw [zero_mul, h3, mul_zero, ← h5]
      _ = (N_p * N_m + N_m * N_p) * Y_n := by simp only [add_mul, mul_assoc]
  have hG0_Y : kantorG0 P_k A C Y_n = V_k * X_n := by
    unfold kantorG0 kantorTriple
    change (N_p * Y_n) * N_m + (N_m * Y_n) * N_p = (N_p * N_m + N_m * N_p) * X_n
    calc (N_p * Y_n) * N_m + (N_m * Y_n) * N_p
      _ = N_p * (Y_n * N_m) + 0 * N_p := by rw [mul_assoc, h3]
      _ = N_p * (N_m * X_n) + N_m * (N_p * X_n) := by rw [zero_mul, h1, mul_zero, ← h6]
      _ = (N_p * N_m + N_m * N_p) * X_n := by simp only [add_mul, mul_assoc]
  have hA61_X := archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hPk A C X_n
  have hA61_Y := archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hPk A C Y_n
  have hVX_comm : V_k * X_n = X_n * V_k := by
    change (N_p * N_m + N_m * N_p) * X_n = X_n * (N_p * N_m + N_m * N_p)
    calc (N_p * N_m + N_m * N_p) * X_n
      _ = N_p * (N_m * X_n) + N_m * (N_p * X_n) := by simp only [add_mul, mul_assoc]
      _ = N_p * (Y_n * N_m) + 0 := by rw [h6, h1, mul_zero]
      _ = (N_p * Y_n) * N_m := by rw [add_zero, mul_assoc]
      _ = (X_n * N_p) * N_m + (X_n * N_m) * N_p := by rw [h5, h4, zero_mul, add_zero]
      _ = X_n * (N_p * N_m + N_m * N_p) := by simp only [mul_add, mul_assoc]
  have hSigX_comm : comm Sig_k X_n = 0 := by
    unfold comm
    have hXSig : X_n * Sig_k = X_n * V_k := by
      change X_n * (N_p * N_m - N_m * N_p) = X_n * (N_p * N_m + N_m * N_p)
      calc X_n * (N_p * N_m - N_m * N_p)
        _ = (X_n * N_p) * N_m - (X_n * N_m) * N_p := by simp only [mul_sub, mul_assoc]
        _ = (X_n * N_p) * N_m + (X_n * N_m) * N_p := by rw [h4, zero_mul, sub_zero, add_zero]
        _ = X_n * (N_p * N_m + N_m * N_p) := by simp only [mul_add, mul_assoc]
    rw [hSig_X, hXSig, hVX_comm, sub_self]
  have hPhiSq : genPhi P_k A C * genPhi P_k A C = V_k := by
    change genPhi P_k A C * genPhi P_k A C = genV P_k A C; peirce_nf hPk
  have hJSq : genJ P_k A C * genJ P_k A C = -V_k := by
    change genJ P_k A C * genJ P_k A C = -genV P_k A C; peirce_nf hPk
  have h1' : N_p * X_n = 0 := h1
  have h4' : X_n * N_m = 0 := h4
  have hPhiXPhi : genPhi P_k A C * X_n * genPhi P_k A C = V_k * Y_n := by
    unfold genPhi
    change (N_p + N_m) * X_n * (N_p + N_m) = V_k * Y_n
    calc (N_p + N_m) * X_n * (N_p + N_m)
      _ = (N_p * X_n) * N_p + (N_p * X_n) * N_m + (N_m * X_n) * N_p + (N_m * X_n) * N_m := by
          simp only [add_mul, mul_add]; abel
      _ = (N_p * X_n) * N_m + (N_m * X_n) * N_p := by
          rw [mul_assoc N_m X_n N_m, h1', h4', zero_mul, mul_zero]; abel
      _ = V_k * Y_n := hG0_X
  have hJXJ : genJ P_k A C * X_n * genJ P_k A C = -(V_k * Y_n) := by
    unfold genJ
    change (N_p - N_m) * X_n * (N_p - N_m) = -(V_k * Y_n)
    calc (N_p - N_m) * X_n * (N_p - N_m)
      _ = (N_p * X_n) * N_p - (N_p * X_n) * N_m - (N_m * X_n) * N_p + (N_m * X_n) * N_m := by
          simp only [sub_mul, mul_sub]; abel
      _ = -((N_p * X_n) * N_m + (N_m * X_n) * N_p) := by
          rw [mul_assoc N_m X_n N_m, h1', h4', zero_mul, mul_zero]; abel
      _ = -(V_k * Y_n) := congrArg Neg.neg hG0_X
  have hM_Phi : derivSqPhi P_k A C X_n = -((2 : ℤ) • (V_k * X_n - V_k * Y_n)) := by
    unfold derivSqPhi comm
    calc -(genPhi P_k A C * (genPhi P_k A C * X_n - X_n * genPhi P_k A C) -
           (genPhi P_k A C * X_n - X_n * genPhi P_k A C) * genPhi P_k A C)
      _ = -((genPhi P_k A C * genPhi P_k A C) * X_n -
            genPhi P_k A C * X_n * genPhi P_k A C -
            genPhi P_k A C * X_n * genPhi P_k A C +
            X_n * (genPhi P_k A C * genPhi P_k A C)) := by
          simp only [mul_sub, sub_mul, mul_assoc]; abel
      _ = -(V_k * X_n - V_k * Y_n - V_k * Y_n + V_k * X_n) := by
          rw [hPhiSq, hPhiXPhi, ← hVX_comm]
      _ = -((2 : ℤ) • (V_k * X_n - V_k * Y_n)) := by abel
  have hM_J : derivSqJ P_k A C X_n = -((2 : ℤ) • (V_k * X_n - V_k * Y_n)) := by
    unfold derivSqJ comm
    calc genJ P_k A C * (genJ P_k A C * X_n - X_n * genJ P_k A C) -
         (genJ P_k A C * X_n - X_n * genJ P_k A C) * genJ P_k A C
      _ = (genJ P_k A C * genJ P_k A C) * X_n -
          genJ P_k A C * X_n * genJ P_k A C -
          genJ P_k A C * X_n * genJ P_k A C +
          X_n * (genJ P_k A C * genJ P_k A C) := by
          simp only [mul_sub, sub_mul, mul_assoc]; abel
      _ = (-V_k) * X_n - -(V_k * Y_n) - -(V_k * Y_n) + X_n * (-V_k) := by
          rw [hJSq, hJXJ]
      _ = -(V_k * X_n) + V_k * Y_n + V_k * Y_n - V_k * X_n := by
          simp only [neg_mul, mul_neg, ← hVX_comm]; abel
      _ = -((2 : ℤ) • (V_k * X_n - V_k * Y_n)) := by abel
  have hM_Sig : derivSqSig P_k A C X_n = 0 := by
    unfold derivSqSig; rw [hSigX_comm]; unfold comm; rw [mul_zero, zero_mul, sub_self, neg_zero]
  have hMogV_X : mog24V P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * V_kn) := by
    unfold mog24V hProjV
    rw [hM_Phi, hM_J, hM_Sig, hSplit, add_zero]
    change (3 : ℤ) • ((8 : ℤ) • ((V_k * V_k) * X_n) +
           (V_k * -((2 : ℤ) • (V_k * X_n - V_k * Y_n)) +
            V_k * -((2 : ℤ) • (V_k * X_n - V_k * Y_n)))) =
           (12 : ℤ) • ((V_k * V_k) * (X_n + Y_n))
    simp only [mul_neg, mul_smul_comm, mul_sub, mul_add, ← mul_assoc, smul_add, smul_sub,
               smul_neg, smul_smul]
    abel_nf
  have hMogSig_X : mog24Sig P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * Sig_kn) := by
    unfold mog24Sig hProjSig
    rw [hM_Sig, hM_Phi, hM_J]
    change (3 : ℤ) • (0 - V_k * -((2 : ℤ) • (V_k * X_n - V_k * Y_n)) -
                          V_k * -((2 : ℤ) • (V_k * X_n - V_k * Y_n))) =
           (12 : ℤ) • ((V_k * V_k) * (X_n - Y_n))
    simp only [mul_neg, mul_smul_comm, mul_sub, ← mul_assoc,
               smul_sub, smul_neg, smul_smul, smul_zero]
    abel_nf
  refine ⟨hSig_X, hSig_Y, hAnn_X, hAnn_Y, ?_, ?_, hMogV_X, hMogSig_X, ?_, ?_⟩
  · rw [hA61_X.2.2.2.2.2.1, hG0_X]
  · rw [hA61_Y.2.2.2.2.2.1, hG0_Y]
  · rw [hMogV_X, hMogSig_X, hSplit]
    change (12 : ℤ) • ((V_k * V_k) * (X_n + Y_n)) +
           (12 : ℤ) • ((V_k * V_k) * (X_n - Y_n)) =
           (24 : ℤ) • ((V_k * V_k) * X_n)
    simp only [mul_add, mul_sub, smul_add, smul_sub]
    abel
  · rw [hMogV_X, hMogSig_X, hSplit]
    change (12 : ℤ) • ((V_k * V_k) * (X_n + Y_n)) -
           (12 : ℤ) • ((V_k * V_k) * (X_n - Y_n)) =
           (24 : ℤ) • ((V_k * V_k) * Y_n)
    simp only [mul_add, mul_sub, smul_add, smul_sub]
    abel

/-! ### 8. Stage `G₆` (`A₆₉`): All-Scale Single-Sheet Decoders (`mog24SheetPlus` & `mog24SheetMinus`) -/

/-- **Theorem `G₆.1` (`archetype_A69_all_scale_quantum_erasure_decoder_and_sheet_separation`):**
For any idempotent `P` (`P * P = P`), any `A, C : B`, and all `(k, n) ∈ ℕ × ℕ`:
1. `Sig_k * Sig_kn = V_k * V_kn` and `Sig_k * V_kn = V_k * Sig_kn`,
2. `mog24V P_k A C Y_n = (12 : ℤ) • ((V_k * V_k) * V_kn)` and
   `mog24Sig P_k A C Y_n = -((12 : ℤ) • ((V_k * V_k) * Sig_kn))`,
3. `mog24SheetPlus P_k A C X_n = (24 : ℤ) • ((V_k * V_k * V_k) * V_kn)` and `mog24SheetPlus P_k A C Y_n = 0`,
4. `mog24SheetMinus P_k A C X_n = 0` and `mog24SheetMinus P_k A C Y_n = (24 : ℤ) • ((V_k * V_k * V_k) * V_kn)`. -/
theorem archetype_A69_all_scale_quantum_erasure_decoder_and_sheet_separation
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let P_k := daughterIdemTower k P A
    let V_k := genV P_k A C
    let Sig_k := genSig P_k A C
    let X_n := mandelbrotTower n (qgtPlus P_k A C)
    let Y_n := mandelbrotTower n (qgtMinus P_k A C)
    let V_kn := mandelbrotTower n V_k
    let Sig_kn := chiralFractalBranch n P_k A C
    Sig_k * Sig_kn = V_k * V_kn ∧
    Sig_k * V_kn = V_k * Sig_kn ∧
    mog24V P_k A C Y_n = (12 : ℤ) • ((V_k * V_k) * V_kn) ∧
    mog24Sig P_k A C Y_n = -((12 : ℤ) • ((V_k * V_k) * Sig_kn)) ∧
    mog24SheetPlus P_k A C X_n = (24 : ℤ) • ((V_k * V_k * V_k) * V_kn) ∧
    mog24SheetPlus P_k A C Y_n = 0 ∧
    mog24SheetMinus P_k A C X_n = 0 ∧
    mog24SheetMinus P_k A C Y_n = (24 : ℤ) • ((V_k * V_k * V_k) * V_kn) := by
  intro P_k V_k Sig_k X_n Y_n V_kn Sig_kn
  have hPk : P_k * P_k = P_k :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower hP A C k 0).1.1
  have hSplit : V_kn = X_n + Y_n :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower hPk A C 0 n).2.1
  rcases archetype_A68_single_sheet_leech_swap_and_golay_12_24_projections hP A C k n with
    ⟨hSig_X, hSig_Y, _, _, _, _, hMogV_X, hMogSig_X, _, _⟩
  rcases archetype_A65_all_scale_fractal_codeword_error_immunity hP A C k n with
    ⟨_, _, _, _, _, _, hMogV_V⟩
  rcases archetype_A67_all_scale_chiral_defect_leech_and_mog24_isolation hP A C k n with
    ⟨_, _, _, _, _, _, hPV_S, _, _, hMogSig_S⟩
  have hMogSig_V : mog24Sig P_k A C V_kn = 0 := by
    unfold mog24Sig
    rw [(archetype_A65_all_scale_fractal_codeword_error_immunity hP A C k n).2.2.2.2.2.1,
        smul_zero]
  have hSwap1 : Sig_k * Sig_kn = V_k * V_kn := by
    change Sig_k * (X_n - Y_n) = V_k * V_kn
    rw [mul_sub, hSig_X, hSig_Y, sub_neg_eq_add, ← mul_add, ← hSplit]
  have hSwap2 : Sig_k * V_kn = V_k * Sig_kn := by
    rw [hSplit, mul_add, hSig_X, hSig_Y]
    change V_k * X_n + -(V_k * Y_n) = V_k * (X_n - Y_n)
    rw [mul_sub, sub_eq_add_neg]
  have hDPhi : derivSqPhi P_k A C (X_n + Y_n) = derivSqPhi P_k A C X_n + derivSqPhi P_k A C Y_n := by
    unfold derivSqPhi comm; simp only [mul_add, add_mul, sub_mul, mul_sub]; abel
  have hDJ : derivSqJ P_k A C (X_n + Y_n) = derivSqJ P_k A C X_n + derivSqJ P_k A C Y_n := by
    unfold derivSqJ comm; simp only [mul_add, add_mul, sub_mul, mul_sub]; abel
  have hDSig : derivSqSig P_k A C (X_n + Y_n) = derivSqSig P_k A C X_n + derivSqSig P_k A C Y_n := by
    unfold derivSqSig comm; simp only [mul_add, add_mul, sub_mul, mul_sub]; abel
  have hLinV : mog24V P_k A C (X_n + Y_n) = mog24V P_k A C X_n + mog24V P_k A C Y_n := by
    unfold mog24V hProjV
    rw [hDPhi, hDJ, hDSig]
    simp only [mul_add, smul_add]; abel
  have hLinSig : mog24Sig P_k A C (X_n + Y_n) = mog24Sig P_k A C X_n + mog24Sig P_k A C Y_n := by
    unfold mog24Sig hProjSig
    rw [hDPhi, hDJ, hDSig]
    simp only [mul_add, sub_eq_add_neg, neg_add_rev, smul_add]; abel
  have hMogV_X' : mog24V P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * V_kn) := hMogV_X
  have hMogSig_X' : mog24Sig P_k A C X_n = (12 : ℤ) • ((V_k * V_k) * Sig_kn) := hMogSig_X
  have hMogV_Y : mog24V P_k A C Y_n = (12 : ℤ) • ((V_k * V_k) * V_kn) := by
    have hSum : mog24V P_k A C X_n + mog24V P_k A C Y_n = (24 : ℤ) • ((V_k * V_k) * V_kn) := by
      rw [← hLinV, ← hSplit]
      exact hMogV_V
    rw [hMogV_X'] at hSum
    calc mog24V P_k A C Y_n
      _ = ((12 : ℤ) • ((V_k * V_k) * V_kn) + mog24V P_k A C Y_n) -
          (12 : ℤ) • ((V_k * V_k) * V_kn) := by abel
      _ = (24 : ℤ) • ((V_k * V_k) * V_kn) - (12 : ℤ) • ((V_k * V_k) * V_kn) := by rw [hSum]
      _ = (12 : ℤ) • ((V_k * V_k) * V_kn) := by rw [← sub_smul]; rfl
  have hMogSig_Y : mog24Sig P_k A C Y_n = -((12 : ℤ) • ((V_k * V_k) * Sig_kn)) := by
    have hSum : mog24Sig P_k A C X_n + mog24Sig P_k A C Y_n = 0 := by
      rw [← hLinSig, ← hSplit]
      exact hMogSig_V
    rw [hMogSig_X'] at hSum
    exact eq_neg_of_add_eq_zero_right hSum
  have hSigV_comm : Sig_k * V_k = V_k * Sig_k := by
    change genSig P_k A C * genV P_k A C = genV P_k A C * genSig P_k A C; peirce_nf hPk
  have hSigTriple : Sig_k * ((V_k * V_k) * Sig_kn) = (V_k * V_k) * (V_k * V_kn) := by
    calc Sig_k * ((V_k * V_k) * Sig_kn)
      _ = (Sig_k * V_k) * (V_k * Sig_kn) := by simp only [mul_assoc]
      _ = (V_k * Sig_k) * (V_k * Sig_kn) := by rw [hSigV_comm]
      _ = V_k * (Sig_k * V_k) * Sig_kn := by simp only [mul_assoc]
      _ = V_k * (V_k * Sig_k) * Sig_kn := by rw [hSigV_comm]
      _ = (V_k * V_k) * (Sig_k * Sig_kn) := by simp only [mul_assoc]
      _ = (V_k * V_k) * (V_k * V_kn) := by rw [hSwap1]
  have hAssocV : V_k * ((V_k * V_k) * V_kn) = (V_k * V_k * V_k) * V_kn := by
    simp only [mul_assoc]
  have hSigTriple' : Sig_k * ((V_k * V_k) * Sig_kn) = (V_k * V_k * V_k) * V_kn := by
    rw [hSigTriple]; simp only [mul_assoc]
  refine ⟨hSwap1, hSwap2, hMogV_Y, hMogSig_Y, ?_, ?_, ?_, ?_⟩
  · unfold mog24SheetPlus
    change V_k * mog24V P_k A C X_n + Sig_k * mog24Sig P_k A C X_n = _
    rw [hMogV_X', hMogSig_X', mul_smul_comm, mul_smul_comm, hAssocV, hSigTriple', ← add_smul]
    rfl
  · unfold mog24SheetPlus
    change V_k * mog24V P_k A C Y_n + Sig_k * mog24Sig P_k A C Y_n = 0
    rw [hMogV_Y, hMogSig_Y, mul_neg, mul_smul_comm, mul_smul_comm, hAssocV, hSigTriple',
        add_neg_cancel]
  · unfold mog24SheetMinus
    change V_k * mog24V P_k A C X_n - Sig_k * mog24Sig P_k A C X_n = 0
    rw [hMogV_X', hMogSig_X', mul_smul_comm, mul_smul_comm, hAssocV, hSigTriple', sub_self]
  · unfold mog24SheetMinus
    change V_k * mog24V P_k A C Y_n - Sig_k * mog24Sig P_k A C Y_n = _
    rw [hMogV_Y, hMogSig_Y, mul_neg, mul_smul_comm, mul_smul_comm, hAssocV, hSigTriple',
        sub_neg_eq_add, ← add_smul]
    rfl

/-! ### 8. Stage `D₄₀` (Priority 2): All-Mode Scale-12 / Scale-24 Golay–Leech–MOG Ladder on Even Virasoro Modes -/

/-- **Theorem `D₄₀` (`stage_D40_all_mode_virasoro_golay_leech_mog_ladder`):**
For any idempotent `P` (`P * P = P`), any `A, C : B`, and every mode index `m : ℕ`,
applying the Scale-12 (`golay12Core`, `golay12Root`, `golay12Ext`), Scale-24
(`golay24G0`, `golay24Gp1`, `golay24Gm1`, `golay24Gp2`, `golay24Gm2`), and Scale-24 MOG
(`mog24V`, `mog24Phi`, `mog24J`, `mog24Sig`) operators to the even Virasoro mode
`virasoroModeEven m P A C = opPow (m + 1) (genV P A C)` yields an exact mode-raising ladder
in the charge-`0` / `V`-channel while annihilating all non-zero charge and shear channels:
1. **Scale-12 Mode Shift & Syndrome Vanishing:**
   - `golay12Core P A C (virasoroModeEven m P A C) = (12 : ℤ) • virasoroModeEven (m + 1) P A C`,
   - `golay12Root P A C (virasoroModeEven m P A C) = 0`,
   - `golay12Ext P A C (virasoroModeEven m P A C) = 0`;
2. **Scale-24 Leech Mode Shift & Four-Sector Annihilation (`m_charge ∈ {±1, ±2}`):**
   - `golay24G0 P A C (virasoroModeEven m P A C) = (24 : ℤ) • virasoroModeEven (m + 1) P A C`,
   - `golay24Gp1 P A C (virasoroModeEven m P A C) = 0`,
   - `golay24Gm1 P A C (virasoroModeEven m P A C) = 0`,
   - `golay24Gp2 P A C (virasoroModeEven m P A C) = 0`,
   - `golay24Gm2 P A C (virasoroModeEven m P A C) = 0`;
3. **Scale-24 MOG Double-Mode Shift & Shear Channel Annihilation:**
   - `mog24V P A C (virasoroModeEven m P A C) = (24 : ℤ) • virasoroModeEven (m + 2) P A C`,
   - `mog24Phi P A C (virasoroModeEven m P A C) = 0`,
   - `mog24J P A C (virasoroModeEven m P A C) = 0`,
   - `mog24Sig P A C (virasoroModeEven m P A C) = 0`. -/
theorem stage_D40_all_mode_virasoro_golay_leech_mog_ladder
    {P : B} (hP : P * P = P) (A C : B) (m : ℕ) :
    golay12Core P A C (virasoroModeEven m P A C) =
      (12 : ℤ) • virasoroModeEven (m + 1) P A C ∧
    golay12Root P A C (virasoroModeEven m P A C) = 0 ∧
    golay12Ext P A C (virasoroModeEven m P A C) = 0 ∧
    golay24G0 P A C (virasoroModeEven m P A C) =
      (24 : ℤ) • virasoroModeEven (m + 1) P A C ∧
    golay24Gp1 P A C (virasoroModeEven m P A C) = 0 ∧
    golay24Gm1 P A C (virasoroModeEven m P A C) = 0 ∧
    golay24Gp2 P A C (virasoroModeEven m P A C) = 0 ∧
    golay24Gm2 P A C (virasoroModeEven m P A C) = 0 ∧
    mog24V P A C (virasoroModeEven m P A C) =
      (24 : ℤ) • virasoroModeEven (m + 2) P A C ∧
    mog24Phi P A C (virasoroModeEven m P A C) = 0 ∧
    mog24J P A C (virasoroModeEven m P A C) = 0 ∧
    mog24Sig P A C (virasoroModeEven m P A C) = 0 := by
  let W := virasoroModeEven m P A C
  rcases opPow_genV_comm_invS_and_cones hP A C (m + 1) with ⟨_, hCp, hCm⟩
  have hCp' : conePlus P A * W = W * conePlus P A := hCp
  have hCm' : coneMinus P C * W = W * coneMinus P C := hCm
  have hNpSq : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have hNmSq : coneMinus P C * coneMinus P C = 0 := by peirce_nf hP
  have hGp1 : kantorGp1 P A W = 0 := by
    unfold kantorGp1 comm; rw [hCp', sub_self]
  have hGm1 : kantorGm1 P C W = 0 := by
    unfold kantorGm1 comm; rw [hCm', sub_self]
  have hGp2 : kantorGp2 P A W = 0 := by
    calc kantorGp2 P A W
      _ = (conePlus P A * W) * conePlus P A := rfl
      _ = (W * conePlus P A) * conePlus P A := by rw [hCp']
      _ = W * (conePlus P A * conePlus P A) := by rw [mul_assoc]
      _ = 0 := by rw [hNpSq, mul_zero]
  have hGm2 : kantorGm2 P C W = 0 := by
    calc kantorGm2 P C W
      _ = (coneMinus P C * W) * coneMinus P C := rfl
      _ = (W * coneMinus P C) * coneMinus P C := by rw [hCm']
      _ = W * (coneMinus P C * coneMinus P C) := by rw [mul_assoc]
      _ = 0 := by rw [hNmSq, mul_zero]
  have hSame : sandwichSame P A C W = 0 := by
    change kantorGp2 P A W + kantorGm2 P C W = 0
    rw [hGp2, hGm2, add_zero]
  have hCommPhi : comm (genPhi P A C) W = 0 := by
    unfold comm genPhi; rw [add_mul, mul_add, hCp', hCm', sub_self]
  have hCommJ : comm (genJ P A C) W = 0 := by
    unfold comm genJ; rw [sub_mul, mul_sub, hCp', hCm', sub_self]
  have hCommSig : comm (genSig P A C) W = 0 := by
    unfold comm genSig
    calc (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) * W -
         W * (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A)
      _ = conePlus P A * (coneMinus P C * W) - coneMinus P C * (conePlus P A * W) -
          W * (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) := by
          simp only [sub_mul, mul_assoc]
      _ = conePlus P A * (W * coneMinus P C) - coneMinus P C * (W * conePlus P A) -
          W * (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) := by
          rw [hCm', hCp']
      _ = (conePlus P A * W) * coneMinus P C - (coneMinus P C * W) * conePlus P A -
          W * (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) := by
          simp only [mul_assoc]
      _ = (W * conePlus P A) * coneMinus P C - (W * coneMinus P C) * conePlus P A -
          W * (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) := by
          rw [hCp', hCm']
      _ = 0 := by simp only [mul_sub, mul_assoc, sub_self]
  have hG0 : kantorG0 P A C W = virasoroModeEven (m + 1) P A C := by
    unfold kantorG0 kantorTriple
    calc (conePlus P A * W) * coneMinus P C + (coneMinus P C * W) * conePlus P A
      _ = (W * conePlus P A) * coneMinus P C + (W * coneMinus P C) * conePlus P A := by
          rw [hCp', hCm']
      _ = W * (conePlus P A * coneMinus P C + coneMinus P C * conePlus P A) := by
          simp only [mul_add, mul_assoc]
      _ = virasoroModeEven (m + 1) P A C := rfl
  have hCross : sandwichCross P A C W = virasoroModeEven (m + 1) P A C := hG0
  have hVW : genV P A C * W = virasoroModeEven (m + 1) P A C :=
    mul_opPow_comm (m + 1) (genV P A C)
  have hVVW : (genV P A C * genV P A C) * W = virasoroModeEven (m + 2) P A C := by
    calc (genV P A C * genV P A C) * W
      _ = genV P A C * (genV P A C * W) := by rw [mul_assoc]
      _ = genV P A C * virasoroModeEven (m + 1) P A C := by rw [hVW]
      _ = virasoroModeEven (m + 2) P A C := mul_opPow_comm (m + 2) (genV P A C)
  have hA61 := archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes hP A C W
  have hDPhi : derivSqPhi P A C W = 0 := by
    unfold derivSqPhi; rw [hCommPhi]; unfold comm; rw [mul_zero, zero_mul, sub_self, neg_zero]
  have hDJ : derivSqJ P A C W = 0 := by
    unfold derivSqJ; rw [hCommJ]; unfold comm; rw [mul_zero, zero_mul, sub_self]
  have hDSig : derivSqSig P A C W = 0 := by
    unfold derivSqSig; rw [hCommSig]; unfold comm; rw [mul_zero, zero_mul, sub_self, neg_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hA61.2.1, hCross]
  · rw [hA61.2.2.1, hCommPhi, smul_zero]
  · rw [hA61.2.2.2.1, hSame, smul_zero]
  · rw [hA61.2.2.2.2.2.1, hG0]
  · rw [hA61.2.2.2.2.2.2.1, hGp1, smul_zero]
  · rw [hA61.2.2.2.2.2.2.2.1, hGm1, smul_zero]
  · rw [hA61.2.2.2.2.2.2.2.2.1, hGp2, smul_zero]
  · rw [hA61.2.2.2.2.2.2.2.2.2.1, hGm2, smul_zero]
  · unfold mog24V hProjV
    rw [hDPhi, hDJ, hDSig, mul_zero, add_zero, add_zero, add_zero, smul_smul, hVVW]
    rfl
  · unfold mog24Phi hProjPhi
    rw [hDPhi, hDJ, hDSig, mul_zero, sub_zero, sub_zero, smul_zero]
  · unfold mog24J hProjJ
    rw [hDJ, hDPhi, hDSig, mul_zero, sub_zero, sub_zero, smul_zero]
  · unfold mog24Sig hProjSig
    rw [hDSig, hDPhi, hDJ, mul_zero, sub_zero, sub_zero, smul_zero]

/-! ### Ideal projections of the two-scale defect sheets -/

/-- At every horizontal idempotent scale and every vertical defect depth, the
left and right Peirce ideal actions select the same two QGT sheets. Acting on
the pilot element `Φ * Vₙ` then separates its upper and lower corner terms.
The last identity records the anticommutator of those two selected terms as
the metric acting on the square of the defect iterate. -/
theorem fractal_sheet_ideal_projections_and_wave_split
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let Pk := daughterIdemTower k P A
    let V := genV Pk A C
    let Φ := genPhi Pk A C
    let J := genJ Pk A C
    let Xn := mandelbrotTower n (qgtPlus Pk A C)
    let Yn := mandelbrotTower n (qgtMinus Pk A C)
    let Vn := mandelbrotTower n V
    let Np := conePlus Pk A
    let Nm := coneMinus Pk C
    Pk * Vn = Xn ∧
    Vn * Pk = Xn ∧
    (1 - Pk) * Vn = Yn ∧
    Vn * (1 - Pk) = Yn ∧
    Pk * (Φ * Vn) = Np * Vn ∧
    (Φ * Vn) * Pk = Nm * Vn ∧
    Np * Vn + Nm * Vn = Φ * Vn ∧
    Np * Vn - Nm * Vn = J * Vn ∧
    (Np * Vn) * (Nm * Vn) + (Nm * Vn) * (Np * Vn) = V * (Vn * Vn) := by
  intro Pk V Φ J Xn Yn Vn Np Nm
  have hPk : Pk * Pk = Pk :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower
      hP A C k 0).1.1
  have hSplit : Vn = Xn + Yn :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower
      hPk A C 0 n).2.1
  have hXL : Pk * Xn = Xn := by
    simpa [Xn, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (qgtPlus_defect_iterates_left hPk A C (n + 1))
  have hXR : Xn * Pk = Xn := by
    simpa [Xn, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (qgtPlus_defect_iterates_right hPk A C (n + 1))
  have hYL : (1 - Pk) * Yn = Yn := by
    simpa [Yn, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (qgtMinus_defect_iterates_left hPk A C (n + 1))
  have hYR : Yn * (1 - Pk) = Yn := by
    simpa [Yn, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (qgtMinus_defect_iterates_right hPk A C (n + 1))
  have hXcL : (1 - Pk) * Xn = 0 := by
    rw [sub_mul, one_mul, hXL, sub_self]
  have hXcR : Xn * (1 - Pk) = 0 := by
    rw [mul_sub, mul_one, hXR, sub_self]
  have hYcL : Pk * Yn = 0 := by
    have hcomp : Pk = 1 - (1 - Pk) := by abel
    rw [hcomp, sub_mul, one_mul, hYL]
    abel
  have hYcR : Yn * Pk = 0 := by
    have hcomp : Pk = 1 - (1 - Pk) := by abel
    rw [hcomp, mul_sub, mul_one, hYR]
    abel
  have hCommData :=
    archetype_A66_all_scale_cone_sheet_braiding_and_leech_24_sector_isolation
      hP A C k n
  have hNpV : Np * Vn = Vn * Np := sub_eq_zero.mp hCommData.1
  have hNmV : Nm * Vn = Vn * Nm := sub_eq_zero.mp hCommData.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSplit, mul_add, hXL, hYcL, add_zero]
  · rw [hSplit, add_mul, hXR, hYcR, add_zero]
  · rw [hSplit, mul_add, hXcL, hYL, zero_add]
  · rw [hSplit, add_mul, hXcR, hYR, zero_add]
  · simpa [Vn, Φ, V, Np, Nm, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (genPhi_defect_iterates_left hPk A C (n + 1))
  · simpa [Vn, Φ, V, Np, Nm, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (genPhi_defect_iterates_right hPk A C (n + 1))
  · change Np * Vn + Nm * Vn = (Np + Nm) * Vn
    rw [add_mul]
  · change Np * Vn - Nm * Vn = (Np - Nm) * Vn
    rw [sub_mul]
  · calc
      (Np * Vn) * (Nm * Vn) + (Nm * Vn) * (Np * Vn)
          = Np * (Vn * Nm) * Vn + Nm * (Vn * Np) * Vn := by
              simp only [mul_assoc]
      _ = Np * (Nm * Vn) * Vn + Nm * (Np * Vn) * Vn := by
            rw [← hNmV, ← hNpV]
      _ = (Np * Nm + Nm * Np) * (Vn * Vn) := by
            simp only [add_mul, mul_assoc]
      _ = V * (Vn * Vn) := by
            simp only [V, genV, Np, Nm, anticomm]

/-- The local two-state chart identities lift to every horizontal daughter scale
and every vertical defect depth.  The chiral branch readout is `(1 + V) * Xn`;
the frequently proposed `(1 - V) * Xn` formula is contradicted by the exact
depth-zero residual `2 * Q₊²` recorded in `chart_sigma_euler_compression_residual`.
-/
theorem all_scale_fractal_two_state_chart_transition
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let Pk := daughterIdemTower k P A
    let Pk1 := daughterIdemTower (k + 1) P A
    let V := genV Pk A C
    let Xn := mandelbrotTower n (qgtPlus Pk A C)
    let Vn := mandelbrotTower n V
    let Sig := chiralFractalBranch n Pk A C
    chartBruhatConj Pk A C (Pk + coneMinus Pk C) = Pk1 ∧
    chartBruhatConjInv Pk A C Pk1 = Pk + coneMinus Pk C ∧
    Pk1 * (genPhi Pk A C * Vn) * (Pk + coneMinus Pk C) = 0 ∧
    Pk1 * (genJ Pk A C * Vn) * (Pk + coneMinus Pk C) =
      (2 : ℤ) • (qgtPlus Pk A C * Xn) ∧
    Pk1 * Vn * (Pk + coneMinus Pk C) =
      (1 - V) * Xn ∧
    Pk1 * Sig * (Pk + coneMinus Pk C) = (1 + V) * Xn := by
  intro Pk Pk1 V Xn Vn Sig
  have hPk : Pk * Pk = Pk :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower
      hP A C k 0).1.1
  have hNext : Pk1 = Pk - conePlus Pk A := by
    change daughterIdemTower (k + 1) P A =
      daughterIdemTower k P A - conePlus (daughterIdemTower k P A) A
    rfl
  have hOdd := chart_two_state_odd_defect_iterates hPk A C (n + 1)
  have hPlus :
      (Pk - conePlus Pk A) * Xn * (Pk + coneMinus Pk C) = Xn := by
    simpa [Xn, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (chart_two_state_qgtPlus_defect_iterate hPk A C (n + 1))
  have hMinus :
      (Pk - conePlus Pk A) *
        mandelbrotTower n (qgtMinus Pk A C) * (Pk + coneMinus Pk C) =
      -(V * Xn) := by
    simpa [Xn, V, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (chart_two_state_qgtMinus_defect_iterate hPk A C (n + 1))
  have hV :
      (Pk - conePlus Pk A) * Vn * (Pk + coneMinus Pk C) = (1 - V) * Xn := by
    simpa [Xn, Vn, V, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (chart_two_state_genV_and_qgtDefectDiff_iterates hPk A C (n + 1)).1
  have hJValue :
      V * Xn = qgtPlus Pk A C * Xn := by
    simpa [Xn, V, mandelbrotTower_eq_idempotencyDefect_iterate] using
      (genV_mul_qgtPlus_defect_iterate hPk A C (n + 1)).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hNext]
    exact (chart_bruhat_conjugation_transition hPk A C).1
  · rw [hNext]
    exact (chart_bruhat_conjugation_transition hPk A C).2
  · rw [hNext]
    simpa [Vn, mandelbrotTower_eq_idempotencyDefect_iterate] using hOdd.1
  · rw [hNext]
    calc
      (Pk - conePlus Pk A) * (genJ Pk A C * Vn) *
          (Pk + coneMinus Pk C) = (2 : ℤ) • (V * Xn) := by
            simpa [Vn, V, Xn, mandelbrotTower_eq_idempotencyDefect_iterate] using hOdd.2
      _ = (2 : ℤ) • (qgtPlus Pk A C * Xn) := by rw [hJValue]
  · rw [hNext]
    exact hV
  · rw [hNext]
    change (Pk - conePlus Pk A) *
      (mandelbrotTower n (qgtPlus Pk A C) -
        mandelbrotTower n (qgtMinus Pk A C)) *
      (Pk + coneMinus Pk C) = (1 + V) * Xn
    calc
      _ = ((Pk - conePlus Pk A) * Xn * (Pk + coneMinus Pk C)) -
          ((Pk - conePlus Pk A) *
            mandelbrotTower n (qgtMinus Pk A C) * (Pk + coneMinus Pk C)) := by
              noncomm_ring
      _ = Xn - (-(V * Xn)) := by rw [hPlus, hMinus]
      _ = (1 + V) * Xn := by noncomm_ring

/-! ### Transcript archetype A₆₈ (alternate label): diffusion and focusing decomposition

The transcript reuses `A₆₈` for two distinct claims. The repository's established
`A₆₈` remains the single-sheet theorem above; this separately named result records
the diffusion/focusing identity without overwriting that owner.
-/

/-- The second-order Peirce derivations split into the cross-channel diffusion
operator and the same-channel focusing operator. -/
def diffusionOp (P A C X : B) : B :=
  (2 : ℤ) • sandwichCross P A C X - anticomm (genV P A C) X

/-- Same-corner contribution to the second-order derivations. -/
def focusingOp (P A C X : B) : B := sandwichSame P A C X

/-- Diffusion/focusing decomposition and its action on the two canonical
off-diagonal combinations. This is the algebraic identity only; physical
interpretations of the operators are not part of the theorem. -/
theorem archetype_A68_diffusion_focusing_decomposition
    {P : B} (hP : P * P = P) (A C X : B) :
    derivSqPhi P A C X = diffusionOp P A C X + (2 : ℤ) • focusingOp P A C X ∧
    derivSqJ P A C X = diffusionOp P A C X - (2 : ℤ) • focusingOp P A C X ∧
    diffusionOp P A C (genPhi P A C) =
      -((2 : ℤ) • (genV P A C * genPhi P A C)) ∧
    diffusionOp P A C (genJ P A C) =
      -((2 : ℤ) • (genV P A C * genJ P A C)) ∧
    focusingOp P A C (genPhi P A C) = genV P A C * genPhi P A C ∧
    focusingOp P A C (genJ P A C) = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold diffusionOp focusingOp
    peirce_abel_golay hP
  · unfold diffusionOp focusingOp
    peirce_abel_golay hP
  · unfold diffusionOp
    peirce_abel_golay hP
  · unfold diffusionOp
    peirce_abel_golay hP
  · unfold focusingOp
    peirce_abel_golay hP
  · unfold focusingOp
    peirce_abel_golay hP

/-- All-scale extension of the diffusion/focusing split on the two iterated
defect sheets. It relies on the previously proved A64 tower decomposition and
A66 commutation of the iterated defect with both Peirce cones. -/
theorem archetype_A68_all_scale_diffusion_focusing_balance
    {P : B} (hP : P * P = P) (A C : B) (k n : ℕ) :
    let Pk := daughterIdemTower k P A
    let Vk := genV Pk A C
    let Vkn := mandelbrotTower n Vk
    let Phik := genPhi Pk A C
    let Jk := genJ Pk A C
    focusingOp Pk A C (Phik * Vkn) = Vk * Phik * Vkn ∧
    focusingOp Pk A C (Jk * Vkn) = -(Vk * Jk * Vkn) ∧
    diffusionOp Pk A C (Phik * Vkn) = -((2 : ℤ) • (Vk * Phik * Vkn)) ∧
    diffusionOp Pk A C (Jk * Vkn) = -((2 : ℤ) • (Vk * Jk * Vkn)) ∧
    derivSqPhi Pk A C (Phik * Vkn) = 0 ∧
    derivSqPhi Pk A C (Jk * Vkn) = -((4 : ℤ) • (Vk * Jk * Vkn)) := by
  intro Pk Vk Vkn Phik Jk
  have hPk : Pk * Pk = Pk :=
    (archetype_A64_universal_all_scale_fractal_rg_and_mandelbrot_tower
      hP A C k 0).1.1
  rcases archetype_A66_all_scale_cone_sheet_braiding_and_leech_24_sector_isolation
      hP A C k n with ⟨hCommNp, hCommNm, _, _, _, _, _, _, _, _, _⟩
  set Np := conePlus Pk A
  set Nm := coneMinus Pk C
  have hNpV : Np * Vkn = Vkn * Np := sub_eq_zero.mp hCommNp
  have hNmV : Nm * Vkn = Vkn * Nm := sub_eq_zero.mp hCommNm
  have hPullCross : ∀ Z : B,
      sandwichCross Pk A C (Z * Vkn) = sandwichCross Pk A C Z * Vkn := by
    intro Z
    change Np * (Z * Vkn) * Nm + Nm * (Z * Vkn) * Np =
      (Np * Z * Nm + Nm * Z * Np) * Vkn
    calc
      _ = (Np * Z) * (Vkn * Nm) + (Nm * Z) * (Vkn * Np) := by
        simp only [mul_assoc]
      _ = (Np * Z) * (Nm * Vkn) + (Nm * Z) * (Np * Vkn) := by
        rw [← hNmV, ← hNpV]
      _ = _ := by simp only [add_mul, mul_assoc]
  have hPullSame : ∀ Z : B,
      focusingOp Pk A C (Z * Vkn) = focusingOp Pk A C Z * Vkn := by
    intro Z
    change Np * (Z * Vkn) * Np + Nm * (Z * Vkn) * Nm =
      (Np * Z * Np + Nm * Z * Nm) * Vkn
    calc
      _ = (Np * Z) * (Vkn * Np) + (Nm * Z) * (Vkn * Nm) := by
        simp only [mul_assoc]
      _ = (Np * Z) * (Np * Vkn) + (Nm * Z) * (Nm * Vkn) := by
        rw [← hNpV, ← hNmV]
      _ = _ := by simp only [add_mul, mul_assoc]
  have hVkVkn : Vk * Vkn = Vkn * Vk := by
    change (Np * Nm + Nm * Np) * Vkn = Vkn * (Np * Nm + Nm * Np)
    calc
      _ = (Np * Vkn) * Nm + (Nm * Vkn) * Np := by
        simp only [add_mul, mul_assoc]
        rw [hNmV, hNpV]
      _ = (Vkn * Np) * Nm + (Vkn * Nm) * Np := by
        rw [hNpV, hNmV]
      _ = _ := by simp only [mul_add, mul_assoc]
  have hPullDiff : ∀ Z : B,
      diffusionOp Pk A C (Z * Vkn) = diffusionOp Pk A C Z * Vkn := by
    intro Z
    unfold diffusionOp anticomm
    rw [hPullCross Z]
    change (2 : ℤ) • (sandwichCross Pk A C Z * Vkn) -
        (Vk * (Z * Vkn) + (Z * Vkn) * Vk) =
      ((2 : ℤ) • sandwichCross Pk A C Z - (Vk * Z + Z * Vk)) * Vkn
    rw [mul_assoc Z Vkn Vk, ← hVkVkn]
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc]
  have hDecomp : ∀ Z : B,
      derivSqPhi Pk A C Z = diffusionOp Pk A C Z +
        (2 : ℤ) • focusingOp Pk A C Z := by
    intro Z
    unfold diffusionOp focusingOp
    peirce_abel_golay hPk
  have hFocPhi : focusingOp Pk A C (genPhi Pk A C) = Vk * genPhi Pk A C := by
    unfold focusingOp
    change sandwichSame Pk A C (genPhi Pk A C) = genV Pk A C * genPhi Pk A C
    peirce_abel_golay hPk
  have hFocJ : focusingOp Pk A C (genJ Pk A C) = -(Vk * genJ Pk A C) := by
    unfold focusingOp
    change sandwichSame Pk A C (genJ Pk A C) = -(genV Pk A C * genJ Pk A C)
    peirce_abel_golay hPk
  have hDiffPhi : diffusionOp Pk A C (genPhi Pk A C) =
      -((2 : ℤ) • (Vk * genPhi Pk A C)) := by
    unfold diffusionOp
    change (2 : ℤ) • sandwichCross Pk A C (genPhi Pk A C) -
      anticomm (genV Pk A C) (genPhi Pk A C) =
      -((2 : ℤ) • (genV Pk A C * genPhi Pk A C))
    peirce_abel_golay hPk
  have hDiffJ : diffusionOp Pk A C (genJ Pk A C) =
      -((2 : ℤ) • (Vk * genJ Pk A C)) := by
    unfold diffusionOp
    change (2 : ℤ) • sandwichCross Pk A C (genJ Pk A C) -
      anticomm (genV Pk A C) (genJ Pk A C) =
      -((2 : ℤ) • (genV Pk A C * genJ Pk A C))
    peirce_abel_golay hPk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPullSame (genPhi Pk A C), hFocPhi]
  · rw [hPullSame (genJ Pk A C), hFocJ, neg_mul]
  · rw [hPullDiff (genPhi Pk A C), hDiffPhi, neg_mul, smul_mul_assoc]
  · rw [hPullDiff (genJ Pk A C), hDiffJ, neg_mul, smul_mul_assoc]
  · rw [hDecomp (genPhi Pk A C * Vkn), hPullDiff (genPhi Pk A C),
        hPullSame (genPhi Pk A C), hDiffPhi, hFocPhi,
        neg_mul, smul_mul_assoc, neg_add_cancel]
  · rw [hDecomp (genJ Pk A C * Vkn), hPullDiff (genJ Pk A C),
        hPullSame (genJ Pk A C), hDiffJ, hFocJ,
        neg_mul, neg_mul, smul_mul_assoc, smul_neg]
    abel

end InfoGeometry.OperatorAlgebra.PeirceSpine
