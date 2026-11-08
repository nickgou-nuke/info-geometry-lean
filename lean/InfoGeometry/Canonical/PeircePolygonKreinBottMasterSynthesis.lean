/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.MasterCausalPosetD1ToD15
import InfoGeometry.OperatorAlgebra.PeirceSpine.QuantumAffineFlagClusterPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.UHFHeisenbergSugawaraVirasoroPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceTetradPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.CayleyDicksonHopfPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.GolayLeechMOGSheetPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.KleinAction
import InfoGeometry.OperatorAlgebra.PeirceSpine.PrimalDual
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.Categorical.TwoSheetKreinStageSystem
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.SignedNetwork.RankedDAGResolvent
import InfoGeometry.Clifford.ClNNFockChiralProjectorClosure
import InfoGeometry.Clifford.SplitCl44CausalEnvelope
import InfoGeometry.Twistor.PenroseTwistorOperatorBridge
import InfoGeometry.Canonical.SMNormalizedGaugeEmbedding
import InfoGeometry.Algebra.Clifford55GaugeSubalgebraBridge
import InfoGeometry.Algebra.StructureConstants
import InfoGeometry.Algebra.CuntzO3LieAlgebraCasimir
import InfoGeometry.Clifford.CliffordTower
import InfoGeometry.Physics.FineStructureDerivation
import InfoGeometry.Physics.PellisFineStructure

/-!
# All-`m` Polygon Lucas–Fibonacci Braiding, Covariant Bianchi Tower, Colimit Coercivity, and Multi-Period `Cl(5, 5)` Bott Spinor Synthesis

Advances all four certified pillars (`1 → 2 → 3 → 4`) across arbitrary non-commutative
operator rings `[Ring B]`, the two-sheet Hestenes–Krein colimit, the matrix exterior-algebra
Yang–Mills carrier, the `Cl(5, 5)` Bott-periodicity spinor tower `Stage (5 + 8 * k)`, and
the `Cl(1, 1)^{\otimes n}` inductive colimit `Limit`:

1. **Pillar 1 (Stage `D₂₆` — All-`m` Polygon Lucas–Fibonacci & Klein-Bottle Penrose Tower):**
   Defines `polygonFibSeq P A C m` and `polygonLucasGen P A C m` for all `m : ℕ` (extending
   Pentagon `m = 5`, Hexagon `m = 6`, Heptagon `m = 7` to Octagon `m = 8`, Nonagon `m = 9`,
   Decagon `m = 10`, and arbitrary `m`), and proves by induction on `m` the universal
   non-commutative Penrose Kite/Dart power inflation law
   `(penroseKiteOp P A C) ^ (m + 1) = polygonFibSeq P A C (m + 1) * penroseKiteOp P A C + penroseDartOp P A C * polygonFibSeq P A C m`,
   the radical-letter difference factorization, the cross-polygon Lucas–Fibonacci relation,
   and the all-`m` Klein-bottle meridian invariance and intertwining identities.
2. **Pillar 2 (Move #1 Upgrade — All-`m` Covariant Bianchi Tower & Cross-Carrier Yang–Mills / Two-Sheet Krein Synthesis):**
   Proves ring-homomorphism functoriality of `peirceGradingDeriv`, `peirceCovariantDeriv`,
   and `peirceMaurerCartanCurvature`, and proves that for every `m : ℕ`, both
   `polygonFibSeq P A C m` and `polygonLucasGen P A C m` are covariantly constant
   (`peirceCovariantDeriv P A C (...) = 0`) across `[Ring B]`, the two-sheet Krein filtered
   colimit `Module.End ℝ (Carrier StageFunctor)`, and `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)`.
3. **Pillar 3 (Move #2 Upgrade — All-`m` Inductive Polygon Fibonacci & Lucas Trace Coercivity Tower in `Limit`):**
   Proves the shifted Hermitian-square reductions
   `star X * (V * F_m) * X = star (Φ * X) * F_m * (Φ * X)` and
   `star X * (V * L_m) * X = star (Φ * X) * L_m * (Φ * X)` over any `[Ring B] [StarRing B]`,
   and establishes by induction on `m : ℕ` in `Limit` that `0 ≤ tau (star X * F_m * X)`,
   `0 ≤ tau (star X * L_m * X)`,
   `tau (star X * F_{m+1} * X) ≤ tau (star X * F_{m+2} * X) ≤ tau (star X * L_{m+2} * X)`,
   and `tau (star X * L_{m+1} * X) ≤ tau (star X * L_{m+2} * X)`.
4. **Pillar 4 (Move #3 Upgrade — Multi-Period `Cl(5, 5)` Bott-Boundary Spinor Tower `Stage (5 + 8 * k)` & Colimit Intertwiner):**
   Constructs `cl55ToBottStage (k : ℕ) : Cl55 →+* Stage (5 + 8 * k)` across all `8k` Bott
   periods and proves exact colimit invariance and intertwining of `cl55VacuumIdempotent`,
   `peirceBdGHamiltonian`, `peirceMaurerCartanCurvature`, `polygonFibSeq`, `polygonLucasGen`,
   and `(penroseKiteOp ω A_cl C_cl) ^ (m + 1)` into `Limit`.
-/

namespace InfoGeometry.Canonical.PeircePolygonKreinBottMasterSynthesis

open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
open InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge
open InfoGeometry.Canonical.LieJordanHodgeColimit
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge

/-! ## 1. Pillar 1: Stage `D₂₆` All-`m` Polygon Lucas–Fibonacci & Klein-Bottle Penrose Tower -/

section AllMPolygonAndKleinPenroseTower

variable {B : Type*} [Ring B]

/-- **All-`m` Operator Fibonacci Polynomial Sequence (`polygonFibSeq`)**:
Defined recursively over any non-commutative ring `B` in terms of the Peirce horizon
metric `V = genV P A C`:
- `polygonFibSeq P A C 0 = 0`,
- `polygonFibSeq P A C 1 = 1`,
- `polygonFibSeq P A C (m + 2) = polygonFibSeq P A C (m + 1) + genV P A C * polygonFibSeq P A C m`. -/
def polygonFibSeq (P A C : B) : ℕ → B
  | 0 => 0
  | 1 => 1
  | m + 2 => polygonFibSeq P A C (m + 1) + genV P A C * polygonFibSeq P A C m

/-- **All-`m` Operator Lucas Sequence (`polygonLucasGen`)**:
The symmetric `m`-gon transfer trace operator `(peirceTransfer P A C) ^ m + (peirceTransferComplement P A C) ^ m`
in any non-commutative ring `B`. -/
def polygonLucasGen (P A C : B) (m : ℕ) : B :=
  (peirceTransfer P A C) ^ m + (peirceTransferComplement P A C) ^ m

/-- **Octagon (`m = 8`), Nonagon (`m = 9`), and Decagon (`m = 10`) Lucas Operators**: -/
def polygonLucas8 (P A C : B) : B := polygonLucasGen P A C 8
def polygonLucas9 (P A C : B) : B := polygonLucasGen P A C 9
def polygonLucas10 (P A C : B) : B := polygonLucasGen P A C 10

@[simp]
theorem polygonFibSeq_zero (P A C : B) : polygonFibSeq P A C 0 = 0 := rfl

@[simp]
theorem polygonFibSeq_one (P A C : B) : polygonFibSeq P A C 1 = 1 := rfl

@[simp]
theorem polygonFibSeq_succ_succ (P A C : B) (m : ℕ) :
    polygonFibSeq P A C (m + 2) =
      polygonFibSeq P A C (m + 1) + genV P A C * polygonFibSeq P A C m := rfl

/-- Any element `X : B` that commutes with `genV P A C` commutes with `polygonFibSeq P A C m`
for every `m : ℕ`. -/
theorem polygonFibSeq_comm_of_genV_comm (P A C X : B)
    (hVX : genV P A C * X = X * genV P A C) :
    ∀ m : ℕ, polygonFibSeq P A C m * X = X * polygonFibSeq P A C m
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
      have ih1 := polygonFibSeq_comm_of_genV_comm P A C X hVX (m + 1)
      have ih0 := polygonFibSeq_comm_of_genV_comm P A C X hVX m
      simp only [polygonFibSeq_succ_succ, add_mul, mul_add]
      rw [ih1, mul_assoc (genV P A C) (polygonFibSeq P A C m) X, ih0,
          ← mul_assoc (genV P A C) X (polygonFibSeq P A C m), hVX,
          mul_assoc X (genV P A C) (polygonFibSeq P A C m)]

/-- Universal ring-homomorphism functoriality of `polygonFibSeq`. -/
theorem map_polygonFibSeq
    {D : Type*} [Ring D] (f : B →+* D) (P A C : B) :
    ∀ m : ℕ, f (polygonFibSeq P A C m) = polygonFibSeq (f P) (f A) (f C) m
  | 0 => by simp
  | 1 => by simp
  | k + 2 => by
      simp only [polygonFibSeq_succ_succ, map_add, map_mul, map_genV,
        map_polygonFibSeq f P A C (k + 1), map_polygonFibSeq f P A C k]

/-- Universal ring-homomorphism functoriality of `polygonFibSeq` and `polygonLucasGen`. -/
theorem map_polygonFibSeq_and_polygonLucasGen
    {D : Type*} [Ring D] (f : B →+* D) (P A C : B) (m : ℕ) :
    f (polygonFibSeq P A C m) = polygonFibSeq (f P) (f A) (f C) m ∧
    f (polygonLucasGen P A C m) = polygonLucasGen (f P) (f A) (f C) m := by
  refine ⟨map_polygonFibSeq f P A C m, ?_⟩
  unfold polygonLucasGen peirceTransfer peirceTransferComplement
  rw [map_add, map_pow, map_pow, map_add, map_sub, map_sub, map_one, map_genPhi]

/-- Klein-bottle meridian parity invariance of `polygonFibSeq P A C m` for all `m : ℕ`. -/
theorem parityConj_polygonFibSeq
    {P : B} (hP : P * P = P) (A C : B) :
    ∀ m : ℕ, parityConj P (polygonFibSeq P A C m) = polygonFibSeq P A C m
  | 0 => by unfold parityConj; simp
  | 1 => by simp only [polygonFibSeq_one]; unfold parityConj; peirce_nf hP
  | k + 2 => by
      have hS2 : invS P * invS P = 1 := by peirce_nf hP
      have hParAdd : ∀ X Y : B, parityConj P (X + Y) = parityConj P X + parityConj P Y := by
        intro X Y; unfold parityConj; noncomm_ring
      have hParMul : ∀ X Y : B, parityConj P (X * Y) = parityConj P X * parityConj P Y := by
        intro X Y
        unfold parityConj
        calc
          invS P * (X * Y) * invS P =
              invS P * X * (invS P * invS P) * Y * invS P := by
            rw [hS2]; noncomm_ring
          _ = (invS P * X * invS P) * (invS P * Y * invS P) := by noncomm_ring
      have hParV : parityConj P (genV P A C) = genV P A C := by
        unfold parityConj; peirce_nf hP
      simp only [polygonFibSeq_succ_succ, hParAdd, hParMul, hParV,
        parityConj_polygonFibSeq hP A C (k + 1), parityConj_polygonFibSeq hP A C k]

/-- Exact consistency of `polygonFibSeq` and `polygonLucasGen` with Stage `D₂₅`
Pentagon (`m = 5`), Hexagon (`m = 6`), and Heptagon (`m = 7`) operators. -/
theorem polygonFibSeq_and_polygonLucasGen_five_six_seven (P A C : B) :
    polygonFibSeq P A C 2 = 1 ∧
    polygonFibSeq P A C 3 = 1 + genV P A C ∧
    polygonFibSeq P A C 4 = 1 + (2 : ℤ) • genV P A C ∧
    polygonFibSeq P A C 5 = polygonFib5 P A C ∧
    polygonFibSeq P A C 6 = polygonFib6 P A C ∧
    polygonFibSeq P A C 7 = polygonFib7 P A C ∧
    polygonLucasGen P A C 5 = polygonLucas5 P A C ∧
    polygonLucasGen P A C 6 = polygonLucas6 P A C ∧
    polygonLucasGen P A C 7 = polygonLucas7 P A C := by
  have h2 : polygonFibSeq P A C 2 = 1 := by
    change polygonFibSeq P A C 1 + genV P A C * polygonFibSeq P A C 0 = 1
    simp
  have h3 : polygonFibSeq P A C 3 = 1 + genV P A C := by
    change polygonFibSeq P A C 2 + genV P A C * polygonFibSeq P A C 1 = 1 + genV P A C
    rw [h2, polygonFibSeq_one, mul_one]
  have h4 : polygonFibSeq P A C 4 = 1 + (2 : ℤ) • genV P A C := by
    change polygonFibSeq P A C 3 + genV P A C * polygonFibSeq P A C 2 = _
    rw [h3, h2, mul_one, two_zsmul, add_assoc]
  have h5 : polygonFibSeq P A C 5 = polygonFib5 P A C := by
    change polygonFibSeq P A C 4 + genV P A C * polygonFibSeq P A C 3 = _
    rw [h4, h3]
    unfold polygonFib5
    noncomm_ring
  have h6 : polygonFibSeq P A C 6 = polygonFib6 P A C := by
    change polygonFibSeq P A C 5 + genV P A C * polygonFibSeq P A C 4 = _
    rw [h5, h4]
    unfold polygonFib5 polygonFib6
    noncomm_ring
  have h7 : polygonFibSeq P A C 7 = polygonFib7 P A C := by
    change polygonFibSeq P A C 6 + genV P A C * polygonFibSeq P A C 5 = _
    rw [h6, h5]
    unfold polygonFib5 polygonFib6 polygonFib7
    noncomm_ring
  exact ⟨h2, h3, h4, h5, h6, h7, rfl, rfl, rfl⟩

/-- **Theorem 1.1 (`all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence`)**:
In any non-commutative ring `B` with idempotent `P` (`P * P = P`), for every `m : ℕ`:
1. **All-`m` Transfer & Penrose Kite/Dart Power Inflation Law:**
   - `(peirceTransfer P A C) ^ (m + 1) = polygonFibSeq P A C (m + 1) * peirceTransfer P A C + genV P A C * polygonFibSeq P A C m`,
   - `(peirceTransferComplement P A C) ^ (m + 1) = polygonFibSeq P A C (m + 1) * peirceTransferComplement P A C + genV P A C * polygonFibSeq P A C m`,
   - `(penroseKiteOp P A C) ^ (m + 1) = polygonFibSeq P A C (m + 1) * penroseKiteOp P A C + penroseDartOp P A C * polygonFibSeq P A C m`;
2. **All-`m` Radical-Letter Difference & Cross-Polygon Lucas–Fibonacci Identity:**
   - `(peirceTransfer P A C) ^ m - (peirceTransferComplement P A C) ^ m = polygonFibSeq P A C m * radicalLetterPlus P A C`,
   - `polygonLucasGen P A C (m + 1) = polygonFibSeq P A C (m + 1) + (2 : ℤ) • (genV P A C * polygonFibSeq P A C m)`,
   - `polygonLucasGen P A C (m + 2) = polygonLucasGen P A C (m + 1) + genV P A C * polygonLucasGen P A C m`;
3. **All-`m` Klein-Bottle Meridian Invariance & Intertwining:**
   - `parityConj P (polygonFibSeq P A C m) = polygonFibSeq P A C m`,
   - `parityConj P (polygonLucasGen P A C (m + 1)) = polygonLucasGen P A C (m + 1)`,
   - `genPhi P A C * parityConj P ((penroseKiteOp P A C) ^ m) = (peirceTransferComplement P A C) ^ m * genPhi P A C`. -/
theorem all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence
    {P : B} (hP : P * P = P) (A C : B) (m : ℕ) :
    (peirceTransfer P A C) ^ (m + 1) =
      polygonFibSeq P A C (m + 1) * peirceTransfer P A C +
        genV P A C * polygonFibSeq P A C m ∧
    (peirceTransferComplement P A C) ^ (m + 1) =
      polygonFibSeq P A C (m + 1) * peirceTransferComplement P A C +
        genV P A C * polygonFibSeq P A C m ∧
    (penroseKiteOp P A C) ^ (m + 1) =
      polygonFibSeq P A C (m + 1) * penroseKiteOp P A C +
        penroseDartOp P A C * polygonFibSeq P A C m ∧
    (peirceTransfer P A C) ^ m - (peirceTransferComplement P A C) ^ m =
      polygonFibSeq P A C m * radicalLetterPlus P A C ∧
    polygonLucasGen P A C (m + 1) =
      polygonFibSeq P A C (m + 1) + (2 : ℤ) • (genV P A C * polygonFibSeq P A C m) ∧
    polygonLucasGen P A C (m + 2) =
      polygonLucasGen P A C (m + 1) + genV P A C * polygonLucasGen P A C m ∧
    parityConj P (polygonFibSeq P A C m) = polygonFibSeq P A C m ∧
    parityConj P (polygonLucasGen P A C (m + 1)) = polygonLucasGen P A C (m + 1) ∧
    genPhi P A C * parityConj P ((penroseKiteOp P A C) ^ m) =
      (peirceTransferComplement P A C) ^ m * genPhi P A C := by
  have hT2 : peirceTransfer P A C * peirceTransfer P A C =
      peirceTransfer P A C + genV P A C :=
    peirceTransfer_quadratic_relation hP A C
  have hTbar2 : peirceTransferComplement P A C * peirceTransferComplement P A C =
      peirceTransferComplement P A C + genV P A C := by
    unfold peirceTransferComplement; peirce_nf hP
  have hFibCommV : ∀ k : ℕ,
      polygonFibSeq P A C k * genV P A C = genV P A C * polygonFibSeq P A C k :=
    polygonFibSeq_comm_of_genV_comm P A C (genV P A C) rfl
  have hPowBoth : ∀ k : ℕ,
      (peirceTransfer P A C) ^ (k + 1) =
        polygonFibSeq P A C (k + 1) * peirceTransfer P A C +
          genV P A C * polygonFibSeq P A C k ∧
      (peirceTransferComplement P A C) ^ (k + 1) =
        polygonFibSeq P A C (k + 1) * peirceTransferComplement P A C +
          genV P A C * polygonFibSeq P A C k := by
    intro k
    induction k with
    | zero =>
        simp
    | succ j ih =>
        rcases ih with ⟨ihT, ihTbar⟩
        refine ⟨?_, ?_⟩
        · rw [pow_succ (peirceTransfer P A C) (j + 1), ihT]
          calc
            (polygonFibSeq P A C (j + 1) * peirceTransfer P A C +
                genV P A C * polygonFibSeq P A C j) * peirceTransfer P A C =
              polygonFibSeq P A C (j + 1) *
                  (peirceTransfer P A C * peirceTransfer P A C) +
                genV P A C * polygonFibSeq P A C j * peirceTransfer P A C := by noncomm_ring
            _ = polygonFibSeq P A C (j + 1) * (peirceTransfer P A C + genV P A C) +
                genV P A C * polygonFibSeq P A C j * peirceTransfer P A C := by rw [hT2]
            _ = (polygonFibSeq P A C (j + 1) + genV P A C * polygonFibSeq P A C j) *
                  peirceTransfer P A C +
                polygonFibSeq P A C (j + 1) * genV P A C := by noncomm_ring
            _ = polygonFibSeq P A C (j + 2) * peirceTransfer P A C +
                genV P A C * polygonFibSeq P A C (j + 1) := by
              rw [hFibCommV (j + 1)]
              rfl
        · rw [pow_succ (peirceTransferComplement P A C) (j + 1), ihTbar]
          calc
            (polygonFibSeq P A C (j + 1) * peirceTransferComplement P A C +
                genV P A C * polygonFibSeq P A C j) * peirceTransferComplement P A C =
              polygonFibSeq P A C (j + 1) *
                  (peirceTransferComplement P A C * peirceTransferComplement P A C) +
                genV P A C * polygonFibSeq P A C j *
                  peirceTransferComplement P A C := by noncomm_ring
            _ = polygonFibSeq P A C (j + 1) *
                  (peirceTransferComplement P A C + genV P A C) +
                genV P A C * polygonFibSeq P A C j *
                  peirceTransferComplement P A C := by rw [hTbar2]
            _ = (polygonFibSeq P A C (j + 1) + genV P A C * polygonFibSeq P A C j) *
                  peirceTransferComplement P A C +
                polygonFibSeq P A C (j + 1) * genV P A C := by noncomm_ring
            _ = polygonFibSeq P A C (j + 2) * peirceTransferComplement P A C +
                genV P A C * polygonFibSeq P A C (j + 1) := by
              rw [hFibCommV (j + 1)]
              rfl
  rcases hPowBoth m with ⟨hTm, hTbarm⟩
  have hDiff : (peirceTransfer P A C) ^ m - (peirceTransferComplement P A C) ^ m =
      polygonFibSeq P A C m * radicalLetterPlus P A C := by
    cases m with
    | zero => simp
    | succ j =>
        rcases hPowBoth j with ⟨hTj, hTbarj⟩
        rw [hTj, hTbarj]
        have hSub : peirceTransfer P A C - peirceTransferComplement P A C =
            radicalLetterPlus P A C := by
          unfold radicalLetterPlus peirceTransfer peirceTransferComplement
          noncomm_ring
        calc
          (polygonFibSeq P A C (j + 1) * peirceTransfer P A C +
              genV P A C * polygonFibSeq P A C j) -
            (polygonFibSeq P A C (j + 1) * peirceTransferComplement P A C +
              genV P A C * polygonFibSeq P A C j) =
            polygonFibSeq P A C (j + 1) *
              (peirceTransfer P A C - peirceTransferComplement P A C) := by noncomm_ring
          _ = polygonFibSeq P A C (j + 1) * radicalLetterPlus P A C := by rw [hSub]
  have hLucasCross : ∀ k : ℕ,
      polygonLucasGen P A C (k + 1) =
        polygonFibSeq P A C (k + 1) +
          (2 : ℤ) • (genV P A C * polygonFibSeq P A C k) := by
    intro k
    rcases hPowBoth k with ⟨hTk, hTbark⟩
    unfold polygonLucasGen
    rw [hTk, hTbark]
    have hSum : peirceTransfer P A C + peirceTransferComplement P A C = 1 :=
      (peirceTransfer_defect_and_vieta hP A C).2.2.2.1
    calc
      (polygonFibSeq P A C (k + 1) * peirceTransfer P A C +
          genV P A C * polygonFibSeq P A C k) +
        (polygonFibSeq P A C (k + 1) * peirceTransferComplement P A C +
          genV P A C * polygonFibSeq P A C k) =
        polygonFibSeq P A C (k + 1) *
            (peirceTransfer P A C + peirceTransferComplement P A C) +
          (2 : ℤ) • (genV P A C * polygonFibSeq P A C k) := by noncomm_ring
      _ = polygonFibSeq P A C (k + 1) +
          (2 : ℤ) • (genV P A C * polygonFibSeq P A C k) := by rw [hSum, mul_one]
  have hLucasRec :
      polygonLucasGen P A C (m + 2) =
        polygonLucasGen P A C (m + 1) + genV P A C * polygonLucasGen P A C m := by
    unfold polygonLucasGen
    rw [peirceTransfer_power_recurrence hP A C m,
        quadratic_power_recurrence (peirceTransferComplement P A C) (genV P A C) hTbar2 m]
    noncomm_ring
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  have hParAdd : ∀ X Y : B, parityConj P (X + Y) = parityConj P X + parityConj P Y := by
    intro X Y; unfold parityConj; noncomm_ring
  have hParZsmul : ∀ (n : ℤ) (X : B), parityConj P (n • X) = n • parityConj P X := by
    intro n X; unfold parityConj; noncomm_ring
  have hParMul : ∀ X Y : B, parityConj P (X * Y) = parityConj P X * parityConj P Y := by
    intro X Y
    unfold parityConj
    calc
      invS P * (X * Y) * invS P =
          invS P * X * (invS P * invS P) * Y * invS P := by
        rw [hS2]; noncomm_ring
      _ = (invS P * X * invS P) * (invS P * Y * invS P) := by noncomm_ring
  have hParOne : parityConj P 1 = 1 := by
    unfold parityConj; peirce_nf hP
  have hParV : parityConj P (genV P A C) = genV P A C := by
    unfold parityConj; peirce_nf hP
  have hParLuc : parityConj P (polygonLucasGen P A C (m + 1)) =
      polygonLucasGen P A C (m + 1) := by
    rw [hLucasCross m, hParAdd, hParZsmul, hParMul, hParV,
        parityConj_polygonFibSeq hP A C (m + 1), parityConj_polygonFibSeq hP A C m]
  have hMeridian :
      genPhi P A C * parityConj P ((penroseKiteOp P A C) ^ m) =
        (peirceTransferComplement P A C) ^ m * genPhi P A C := by
    cases m with
    | zero =>
        simp [hParOne]
    | succ j =>
        rcases hPowBoth j with ⟨hTj, hTbarj⟩
        have hKitePow :
            (penroseKiteOp P A C) ^ (j + 1) =
              polygonFibSeq P A C (j + 1) * penroseKiteOp P A C +
                genV P A C * polygonFibSeq P A C j := hTj
        have hParKite1 :
            genPhi P A C * parityConj P (penroseKiteOp P A C) =
              peirceTransferComplement P A C * genPhi P A C :=
          (klein_bottle_penrose_tiling_inflation_and_meridian_intertwining hP A C).2.2.2.2.2.2.2.1
        have hVPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by
          peirce_nf hP
        have hFibPhi1 :
            polygonFibSeq P A C (j + 1) * genPhi P A C =
              genPhi P A C * polygonFibSeq P A C (j + 1) :=
          polygonFibSeq_comm_of_genV_comm P A C (genPhi P A C) hVPhi (j + 1)
        have hFibPhij :
            polygonFibSeq P A C j * genPhi P A C =
              genPhi P A C * polygonFibSeq P A C j :=
          polygonFibSeq_comm_of_genV_comm P A C (genPhi P A C) hVPhi j
        rw [hKitePow, hTbarj, hParAdd, hParMul, hParMul, hParV,
            parityConj_polygonFibSeq hP A C (j + 1), parityConj_polygonFibSeq hP A C j]
        calc
          genPhi P A C *
              (polygonFibSeq P A C (j + 1) * parityConj P (penroseKiteOp P A C) +
                genV P A C * polygonFibSeq P A C j) =
            (genPhi P A C * polygonFibSeq P A C (j + 1)) *
                parityConj P (penroseKiteOp P A C) +
              (genPhi P A C * genV P A C) * polygonFibSeq P A C j := by noncomm_ring
          _ = polygonFibSeq P A C (j + 1) *
                (genPhi P A C * parityConj P (penroseKiteOp P A C)) +
              genV P A C * (genPhi P A C * polygonFibSeq P A C j) := by
            rw [← hFibPhi1, ← hVPhi]
            noncomm_ring
          _ = polygonFibSeq P A C (j + 1) *
                (peirceTransferComplement P A C * genPhi P A C) +
              genV P A C * (polygonFibSeq P A C j * genPhi P A C) := by
            rw [hParKite1, hFibPhij]
          _ = (polygonFibSeq P A C (j + 1) * peirceTransferComplement P A C +
                genV P A C * polygonFibSeq P A C j) * genPhi P A C := by noncomm_ring
  exact ⟨hTm, hTbarm, hTm, hDiff, hLucasCross m, hLucasRec,
    parityConj_polygonFibSeq hP A C m, hParLuc, hMeridian⟩

end AllMPolygonAndKleinPenroseTower

/-! ## 2. Pillar 2: Move #1 Upgrade — All-`m` Covariant Bianchi Tower & Cross-Carrier Yang–Mills / Two-Sheet Krein Synthesis -/

section AllMCovariantBianchiAndCrossCarrierYangMills

/-- Universal ring-homomorphism functoriality of the Peirce Maurer–Cartan gauge package
(`peirceGradingDeriv`, `peirceCovariantDeriv`, `peirceMaurerCartanCurvature`). -/
theorem map_peirce_maurer_cartan_gauge_package
    {B D : Type*} [Ring B] [Ring D] (f : B →+* D) (P A C X : B) :
    f (peirceGradingDeriv P X) = peirceGradingDeriv (f P) (f X) ∧
    f (peirceCovariantDeriv P A C X) = peirceCovariantDeriv (f P) (f A) (f C) (f X) ∧
    f (peirceMaurerCartanCurvature P A C) =
      peirceMaurerCartanCurvature (f P) (f A) (f C) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold peirceGradingDeriv
    exact map_comm f P X
  · unfold peirceCovariantDeriv peirceGradingDeriv
    rw [map_add, map_comm, map_comm, map_genPhi]
  · unfold peirceMaurerCartanCurvature peirceGradingDeriv
    rw [map_add, map_comm, map_mul, map_genPhi]

/-- For any associative ring `B` with idempotent `P` (`P * P = P`), any `A, C : B`,
and every `m : ℕ`, both `polygonFibSeq P A C m` and `polygonLucasGen P A C m`
commute with `P` and `genPhi P A C`, and lie in the exact kernel of both
`peirceGradingDeriv P` and `peirceCovariantDeriv P A C`. -/
theorem peirceCovariantDeriv_polygonFibSeq_and_polygonLucasGen_eq_zero
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (m : ℕ) :
    peirceGradingDeriv P (polygonFibSeq P A C m) = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (genPhi P A C) (polygonFibSeq P A C m) = 0 ∧
    peirceCovariantDeriv P A C (polygonFibSeq P A C m) = 0 ∧
    peirceGradingDeriv P (polygonLucasGen P A C m) = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (genPhi P A C) (polygonLucasGen P A C m) = 0 ∧
    peirceCovariantDeriv P A C (polygonLucasGen P A C m) = 0 := by
  have hVQ : genV P A C * P = P * genV P A C := by peirce_nf hP
  have hVPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by
    peirce_nf hP
  have hFibQ : polygonFibSeq P A C m * P = P * polygonFibSeq P A C m :=
    polygonFibSeq_comm_of_genV_comm P A C P hVQ m
  have hFibPhi :
      polygonFibSeq P A C m * genPhi P A C =
        genPhi P A C * polygonFibSeq P A C m :=
    polygonFibSeq_comm_of_genV_comm P A C (genPhi P A C) hVPhi m
  have hGradFib : peirceGradingDeriv P (polygonFibSeq P A C m) = 0 := by
    unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [hFibQ, sub_self]
  have hCommFib :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (genPhi P A C) (polygonFibSeq P A C m) = 0 := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [hFibPhi, sub_self]
  have hCovFib : peirceCovariantDeriv P A C (polygonFibSeq P A C m) = 0 := by
    unfold peirceCovariantDeriv
    rw [hGradFib, hCommFib, add_zero]
  have hLuc :
      peirceGradingDeriv P (polygonLucasGen P A C m) = 0 ∧
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (genPhi P A C) (polygonLucasGen P A C m) = 0 := by
    cases m with
    | zero =>
        unfold polygonLucasGen peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        simp only [pow_zero]
        refine ⟨by noncomm_ring, by noncomm_ring⟩
    | succ j =>
        have hCross :=
          (all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence hP A C j).2.2.2.2.1
        have hFibQ1 : polygonFibSeq P A C (j + 1) * P = P * polygonFibSeq P A C (j + 1) :=
          polygonFibSeq_comm_of_genV_comm P A C P hVQ (j + 1)
        have hFibQj : polygonFibSeq P A C j * P = P * polygonFibSeq P A C j :=
          polygonFibSeq_comm_of_genV_comm P A C P hVQ j
        have hFibPhi1 :
            polygonFibSeq P A C (j + 1) * genPhi P A C =
              genPhi P A C * polygonFibSeq P A C (j + 1) :=
          polygonFibSeq_comm_of_genV_comm P A C (genPhi P A C) hVPhi (j + 1)
        have hFibPhij :
            polygonFibSeq P A C j * genPhi P A C =
              genPhi P A C * polygonFibSeq P A C j :=
          polygonFibSeq_comm_of_genV_comm P A C (genPhi P A C) hVPhi j
        rw [hCross]
        unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        refine ⟨?_, ?_⟩
        · calc
            P * (polygonFibSeq P A C (j + 1) +
                (2 : ℤ) • (genV P A C * polygonFibSeq P A C j)) -
              (polygonFibSeq P A C (j + 1) +
                (2 : ℤ) • (genV P A C * polygonFibSeq P A C j)) * P =
            (P * polygonFibSeq P A C (j + 1) - polygonFibSeq P A C (j + 1) * P) +
              (2 : ℤ) • (P * genV P A C * polygonFibSeq P A C j -
                genV P A C * (polygonFibSeq P A C j * P)) := by noncomm_ring
            _ = 0 := by
              rw [← hFibQ1, sub_self, zero_add, ← hVQ, hFibQj,
                  ← mul_assoc (genV P A C) P, hVQ, sub_self, smul_zero]
        · calc
            genPhi P A C * (polygonFibSeq P A C (j + 1) +
                (2 : ℤ) • (genV P A C * polygonFibSeq P A C j)) -
              (polygonFibSeq P A C (j + 1) +
                (2 : ℤ) • (genV P A C * polygonFibSeq P A C j)) * genPhi P A C =
            (genPhi P A C * polygonFibSeq P A C (j + 1) -
                polygonFibSeq P A C (j + 1) * genPhi P A C) +
              (2 : ℤ) • (genPhi P A C * genV P A C * polygonFibSeq P A C j -
                genV P A C * (polygonFibSeq P A C j * genPhi P A C)) := by noncomm_ring
            _ = 0 := by
              rw [← hFibPhi1, sub_self, zero_add, ← hVPhi, hFibPhij,
                  ← mul_assoc (genV P A C) (genPhi P A C), hVPhi, sub_self, smul_zero]
  exact ⟨hGradFib, hCommFib, hCovFib, hLuc.1, hLuc.2,
    by unfold peirceCovariantDeriv; rw [hLuc.1, hLuc.2, add_zero]⟩

/-- **Theorem 2.1 (`peirceCovariantDeriv_polygon_tower_and_cross_carrier_yang_mills`)**:
Unifies the all-`m` covariant Bianchi constancy of `polygonFibSeq` and `polygonLucasGen`
across:
1. Any associative ring `[Ring B]` with idempotent `P` (`P * P = P`);
2. The two-sheet Hestenes–Krein filtered colimit `Module.End ℝ (Carrier StageFunctor)`
   (`P_colim = twoSheetColimitEnd plusStage`);
3. `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)` (`A_conn = genPhi P_mat A_mat C_mat`). -/
theorem peirceCovariantDeriv_polygon_tower_and_cross_carrier_yang_mills
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (m : ℕ)
    (A_colim C_colim :
      Module.End ℝ
        (InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.Carrier
          InfoGeometry.Categorical.TwoSheetKreinStageSystem.StageFunctor))
    {R : Type*} [CommRing R] {V_ext : Type*} [AddCommGroup V_ext] [Module R V_ext]
    {n : ℕ}
    {P_mat : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)}
    (hP_mat : P_mat * P_mat = P_mat)
    (A_mat C_mat : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)) :
    let P_colim :=
      InfoGeometry.Categorical.TwoSheetKreinStageSystem.twoSheetColimitEnd
        InfoGeometry.Categorical.TwoSheetKreinStageSystem.plusStage
    let A_conn := genPhi P_mat A_mat C_mat
    peirceGradingDeriv P (polygonFibSeq P A C m) = 0 ∧
    peirceCovariantDeriv P A C (polygonFibSeq P A C m) = 0 ∧
    peirceGradingDeriv P (polygonLucasGen P A C m) = 0 ∧
    peirceCovariantDeriv P A C (polygonLucasGen P A C m) = 0 ∧
    peirceCovariantDeriv P_colim A_colim C_colim
      (polygonFibSeq P_colim A_colim C_colim m) = 0 ∧
    peirceCovariantDeriv P_colim A_colim C_colim
      (polygonLucasGen P_colim A_colim C_colim m) = 0 ∧
    covariantDerivative A_conn 0 (polygonFibSeq P_mat A_mat C_mat m) = 0 ∧
    covariantDerivative A_conn 0 (polygonLucasGen P_mat A_mat C_mat m) = 0 := by
  dsimp only
  rcases peirceCovariantDeriv_polygonFibSeq_and_polygonLucasGen_eq_zero hP A C m with
    ⟨hGF, _, hCF, hGL, _, hCL⟩
  rcases peirceCovariantDeriv_polygonFibSeq_and_polygonLucasGen_eq_zero
      InfoGeometry.Categorical.TwoSheetKreinStageSystem.twoSheetColimit_plus_idempotent
      A_colim C_colim m with
    ⟨_, _, hCF_colim, _, _, hCL_colim⟩
  rcases peirceCovariantDeriv_polygonFibSeq_and_polygonLucasGen_eq_zero
      hP_mat A_mat C_mat m with
    ⟨_, hCommF_mat, _, _, hCommL_mat, _⟩
  have hExtZero : ∀ M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext),
      matrixExteriorDerivative
        (0 : ExteriorAlgebra R V_ext →ₗ[R] ExteriorAlgebra R V_ext) M = 0 := by
    intro M
    ext i j
    simp [matrixExteriorDerivative]
  refine ⟨hGF, hCF, hGL, hCL, hCF_colim, hCL_colim, ?_, ?_⟩
  · unfold covariantDerivative matrixCommutator
    rw [hExtZero, zero_add]
    exact hCommF_mat
  · unfold covariantDerivative matrixCommutator
    rw [hExtZero, zero_add]
    exact hCommL_mat

end AllMCovariantBianchiAndCrossCarrierYangMills

/-! ## 3. Pillar 3: Move #2 Upgrade — All-`m` Inductive Polygon Fibonacci & Lucas Trace Coercivity Tower in `Limit` -/

section LimitAllMPolygonTraceCoercivityTower

/-- **Shifted Hermitian-Square Reduction for `polygonFibSeq` and `polygonLucasGen`**:
In any `*`-ring `B`, for any self-adjoint idempotent `P : B` (`P * P = P`, `star P = P`),
any `A X : B`, and every `m : ℕ`:
1. `star X * (genV P A (star A) * polygonFibSeq P A (star A) m) * X =
     star (genPhi P A (star A) * X) * polygonFibSeq P A (star A) m * (genPhi P A (star A) * X)`;
2. `star X * (genV P A (star A) * polygonLucasGen P A (star A) m) * X =
     star (genPhi P A (star A) * X) * polygonLucasGen P A (star A) m * (genPhi P A (star A) * X)`. -/
theorem star_mul_genV_polygon_eq_shifted_conjugation
    {B : Type*} [Ring B] [StarRing B]
    {P : B} (hP : P * P = P) (hPs : star P = P) (A X : B) (m : ℕ) :
    star X * (genV P A (star A) * polygonFibSeq P A (star A) m) * X =
      star (genPhi P A (star A) * X) * polygonFibSeq P A (star A) m *
        (genPhi P A (star A) * X) ∧
    star X * (genV P A (star A) * polygonLucasGen P A (star A) m) * X =
      star (genPhi P A (star A) * X) * polygonLucasGen P A (star A) m *
        (genPhi P A (star A) * X) := by
  have hPhiS : star (genPhi P A (star A)) = genPhi P A (star A) := by
    change star (P * A * (1 - P) + (1 - P) * star A * P) =
      P * A * (1 - P) + (1 - P) * star A * P
    simp only [star_add, star_mul, star_sub, star_one, star_star, hPs, mul_assoc]
    exact add_comm _ _
  have hPhi2 : genPhi P A (star A) * genPhi P A (star A) = genV P A (star A) := by
    peirce_nf hP
  have hFibPhi :
      polygonFibSeq P A (star A) m * genPhi P A (star A) =
        genPhi P A (star A) * polygonFibSeq P A (star A) m := by
    have hComm :=
      (peirceCovariantDeriv_polygonFibSeq_and_polygonLucasGen_eq_zero hP A (star A) m).2.1
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm at hComm
    exact (sub_eq_zero.mp hComm).symm
  have hLucPhi :
      polygonLucasGen P A (star A) m * genPhi P A (star A) =
        genPhi P A (star A) * polygonLucasGen P A (star A) m := by
    have hComm :=
      (peirceCovariantDeriv_polygonFibSeq_and_polygonLucasGen_eq_zero hP A (star A) m).2.2.2.2.1
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm at hComm
    exact (sub_eq_zero.mp hComm).symm
  refine ⟨?_, ?_⟩
  · rw [star_mul, hPhiS, ← hPhi2]
    calc
      star X * ((genPhi P A (star A) * genPhi P A (star A)) *
          polygonFibSeq P A (star A) m) * X =
        star X * genPhi P A (star A) *
          (genPhi P A (star A) * polygonFibSeq P A (star A) m) * X := by noncomm_ring
      _ = star X * genPhi P A (star A) *
          (polygonFibSeq P A (star A) m * genPhi P A (star A)) * X := by rw [hFibPhi]
      _ = star X * genPhi P A (star A) * polygonFibSeq P A (star A) m *
          (genPhi P A (star A) * X) := by noncomm_ring
  · rw [star_mul, hPhiS, ← hPhi2]
    calc
      star X * ((genPhi P A (star A) * genPhi P A (star A)) *
          polygonLucasGen P A (star A) m) * X =
        star X * genPhi P A (star A) *
          (genPhi P A (star A) * polygonLucasGen P A (star A) m) * X := by noncomm_ring
      _ = star X * genPhi P A (star A) *
          (polygonLucasGen P A (star A) m * genPhi P A (star A)) * X := by rw [hLucPhi]
      _ = star X * genPhi P A (star A) * polygonLucasGen P A (star A) m *
          (genPhi P A (star A) * X) := by noncomm_ring

/-- **Theorem 3.1 (`limit_all_m_polygon_fibonacci_and_lucas_trace_coercivity_tower`)**:
In the `Cl(1, 1)^{\otimes n}` inductive colimit `Limit`, for any linear trace extension
`tau : Limit →ₗ[ℝ] ℝ` of `normalizedTrace`, any self-adjoint idempotent `P : Limit`
(`P * P = P`, `star P = P`), any `A X : Limit`, and every `m : ℕ`:
1. `0 ≤ tau (star X * polygonFibSeq P A (star A) m * X)` and
   `0 ≤ tau (star X * polygonLucasGen P A (star A) m * X)`;
2. **Monotone Fibonacci Coercivity Step:**
   `tau (star X * polygonFibSeq P A (star A) (m + 1) * X) ≤
     tau (star X * polygonFibSeq P A (star A) (m + 2) * X)`;
3. **Fibonacci-to-Lucas Domination:**
   `tau (star X * polygonFibSeq P A (star A) (m + 1) * X) ≤
     tau (star X * polygonLucasGen P A (star A) (m + 1) * X)`;
4. **Monotone Lucas Coercivity Step:**
   `tau (star X * polygonLucasGen P A (star A) (m + 1) * X) ≤
     tau (star X * polygonLucasGen P A (star A) (m + 2) * X)`. -/
theorem limit_all_m_polygon_fibonacci_and_lucas_trace_coercivity_tower
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ k (a : Stage k), tau (ofStage k a) = normalizedTrace k a)
    {P : Limit} (hP : P * P = P) (hPs : star P = P)
    (A X : Limit) (m : ℕ) :
    0 ≤ tau (star X * polygonFibSeq P A (star A) m * X) ∧
    0 ≤ tau (star X * polygonLucasGen P A (star A) m * X) ∧
    tau (star X * polygonFibSeq P A (star A) (m + 1) * X) ≤
      tau (star X * polygonFibSeq P A (star A) (m + 2) * X) ∧
    tau (star X * polygonFibSeq P A (star A) (m + 1) * X) ≤
      tau (star X * polygonLucasGen P A (star A) (m + 1) * X) ∧
    tau (star X * polygonLucasGen P A (star A) (m + 1) * X) ≤
      tau (star X * polygonLucasGen P A (star A) (m + 2) * X) := by
  have hPos : ∀ Y : Limit, 0 ≤ tau (star Y * Y) :=
    trace_extension_positive tau htau
  let Φ := genPhi P A (star A)
  have hFibRecExpand : ∀ (k : ℕ) (Y : Limit),
      tau (star Y * polygonFibSeq P A (star A) (k + 2) * Y) =
        tau (star Y * polygonFibSeq P A (star A) (k + 1) * Y) +
          tau (star (Φ * Y) * polygonFibSeq P A (star A) k * (Φ * Y)) := by
    intro k Y
    have hSplit :
        star Y * polygonFibSeq P A (star A) (k + 2) * Y =
          star Y * polygonFibSeq P A (star A) (k + 1) * Y +
            star Y * (genV P A (star A) * polygonFibSeq P A (star A) k) * Y := by
      simp only [polygonFibSeq_succ_succ, mul_add, add_mul]
    rw [hSplit, map_add,
        (star_mul_genV_polygon_eq_shifted_conjugation hP hPs A Y k).1]
  have hFibNonneg : ∀ (k : ℕ) (Y : Limit),
      0 ≤ tau (star Y * polygonFibSeq P A (star A) k * Y) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro Y
        rcases k with _ | _ | j
        · simp
        · simp [hPos Y]
        · rw [hFibRecExpand j Y]
          exact add_nonneg (ih (j + 1) (Nat.lt_succ_self (j + 1)) Y)
            (ih j (Nat.lt_trans (Nat.lt_succ_self j) (Nat.lt_succ_self (j + 1))) (Φ * Y))
  have hLucExpand : ∀ (k : ℕ) (Y : Limit),
      tau (star Y * polygonLucasGen P A (star A) (k + 1) * Y) =
        tau (star Y * polygonFibSeq P A (star A) (k + 1) * Y) +
          2 * tau (star (Φ * Y) * polygonFibSeq P A (star A) k * (Φ * Y)) := by
    intro k Y
    have hCross :=
      (all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence hP A (star A) k).2.2.2.2.1
    have hTwo :
        star Y * polygonLucasGen P A (star A) (k + 1) * Y =
          star Y * polygonFibSeq P A (star A) (k + 1) * Y +
            (2 : ℤ) • (star Y * (genV P A (star A) * polygonFibSeq P A (star A) k) * Y) := by
      rw [hCross]
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    rw [hTwo, map_add, map_zsmul, zsmul_eq_mul, Int.cast_ofNat,
        (star_mul_genV_polygon_eq_shifted_conjugation hP hPs A Y k).1]
  have hLucRecExpand : ∀ (k : ℕ) (Y : Limit),
      tau (star Y * polygonLucasGen P A (star A) (k + 2) * Y) =
        tau (star Y * polygonLucasGen P A (star A) (k + 1) * Y) +
          tau (star (Φ * Y) * polygonLucasGen P A (star A) k * (Φ * Y)) := by
    intro k Y
    have hRec :=
      (all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence hP A (star A) k).2.2.2.2.2.1
    have hSplit :
        star Y * polygonLucasGen P A (star A) (k + 2) * Y =
          star Y * polygonLucasGen P A (star A) (k + 1) * Y +
            star Y * (genV P A (star A) * polygonLucasGen P A (star A) k) * Y := by
      rw [hRec]
      simp only [mul_add, add_mul]
    rw [hSplit, map_add,
        (star_mul_genV_polygon_eq_shifted_conjugation hP hPs A Y k).2]
  have hLucNonneg : ∀ (k : ℕ) (Y : Limit),
      0 ≤ tau (star Y * polygonLucasGen P A (star A) k * Y) := by
    intro k Y
    cases k with
    | zero =>
        have hZero :
            star Y * polygonLucasGen P A (star A) 0 * Y =
              star Y * Y + star Y * Y := by
          unfold polygonLucasGen
          simp only [pow_zero, add_mul, mul_add, mul_one]
        rw [hZero, map_add]
        exact add_nonneg (hPos Y) (hPos Y)
    | succ j =>
        rw [hLucExpand j Y]
        linarith [hFibNonneg (j + 1) Y, hFibNonneg j (Φ * Y)]
  refine ⟨hFibNonneg m X, hLucNonneg m X, ?_, ?_, ?_⟩
  · rw [hFibRecExpand m X]
    linarith [hFibNonneg m (Φ * X)]
  · rw [hLucExpand m X]
    linarith [hFibNonneg m (Φ * X)]
  · rw [hLucRecExpand m X]
    linarith [hLucNonneg m (Φ * X)]

end LimitAllMPolygonTraceCoercivityTower

/-! ## 4. Pillar 4: Move #3 Upgrade — Multi-Period `Cl(5, 5)` Bott-Boundary Spinor Tower `Stage (5 + 8 * k)` & Colimit Intertwiner -/

section MultiPeriodCl55BottSpinorTower

/-- **Multi-Period `Cl(5, 5)` Bott-Boundary Spinor Embedding (`cl55ToBottStage`)**:
Embeds `Cl(5, 5)` into `Stage (5 + 8 * k)` (`32 · 256ᵏ × 32 · 256ᵏ` real matrices) for every
Bott period `k : ℕ` by composing `cl55ToStage5` with the tensor-tower bonding map
`bondMap stageBond 5 (5 + 8 * k) (Nat.le_add_right 5 (8 * k))`. -/
noncomputable def cl55ToBottStage (k : ℕ) :
    InfoGeometry.Clifford.Clifford55.Cl55 →+* Stage (5 + 8 * k) :=
  (bondMap stageBond 5 (5 + 8 * k) (Nat.le_add_right 5 (8 * k))).comp cl55ToStage5

/-- General `Cl(5, 5)` multi-period Bott-stage and colimit intertwining theorem for any
idempotent `ω : Cl55` (`ω * ω = ω`), keeping `ω` opaque during elaboration. -/
theorem cl55_multi_period_bott_intertwiner_of_idempotent
    {ω : InfoGeometry.Clifford.Clifford55.Cl55} (hω : ω * ω = ω)
    (k m : ℕ) (D_cl A_cl C_cl x : InfoGeometry.Clifford.Clifford55.Cl55) :
    let P₅ := cl55ToStage5 ω
    let D₅ := cl55ToStage5 D_cl
    let A₅ := cl55ToStage5 A_cl
    let C₅ := cl55ToStage5 C_cl
    let P_k := cl55ToBottStage k ω
    let P_lim := ofStage 5 P₅
    let D_lim := ofStage 5 D₅
    let A_lim := ofStage 5 A₅
    let C_lim := ofStage 5 C₅
    ofStage (5 + 8 * k) (cl55ToBottStage k x) = ofStage 5 (cl55ToStage5 x) ∧
    P_k * P_k = P_k ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (peirceBdGHamiltonian ω D_cl A_cl C_cl)) =
      peirceBdGHamiltonian P_lim D_lim A_lim C_lim ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (peirceMaurerCartanCurvature ω A_cl C_cl)) =
      genJ P_lim A_lim C_lim + genV P_lim A_lim C_lim ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (polygonFibSeq ω A_cl C_cl m)) =
      polygonFibSeq P_lim A_lim C_lim m ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (polygonLucasGen ω A_cl C_cl m)) =
      polygonLucasGen P_lim A_lim C_lim m ∧
    (penroseKiteOp P_lim A_lim C_lim) ^ (m + 1) =
      polygonFibSeq P_lim A_lim C_lim (m + 1) * penroseKiteOp P_lim A_lim C_lim +
        penroseDartOp P_lim A_lim C_lim * polygonFibSeq P_lim A_lim C_lim m := by
  dsimp only
  have hCoherent : ∀ y : InfoGeometry.Clifford.Clifford55.Cl55,
      ofStage (5 + 8 * k) (cl55ToBottStage k y) = ofStage 5 (cl55ToStage5 y) := by
    intro y
    unfold cl55ToBottStage
    exact directLimitOf_bondMap stageBond 5 (5 + 8 * k) (Nat.le_add_right 5 (8 * k))
      (cl55ToStage5 y)
  have hPk : cl55ToBottStage k ω * cl55ToBottStage k ω = cl55ToBottStage k ω :=
    map_idempotent (cl55ToBottStage k) hω
  have hP5 : cl55ToStage5 ω * cl55ToStage5 ω = cl55ToStage5 ω :=
    map_idempotent cl55ToStage5 hω
  have hPlim :
      ofStage 5 (cl55ToStage5 ω) * ofStage 5 (cl55ToStage5 ω) =
        ofStage 5 (cl55ToStage5 ω) :=
    map_idempotent (ofStage 5) hP5
  have hBdG :
      ofStage (5 + 8 * k) (cl55ToBottStage k (peirceBdGHamiltonian ω D_cl A_cl C_cl)) =
        peirceBdGHamiltonian
          (ofStage 5 (cl55ToStage5 ω)) (ofStage 5 (cl55ToStage5 D_cl))
          (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) := by
    rw [hCoherent,
        (map_peirceBdGHamiltonian cl55ToStage5 ω D_cl A_cl C_cl).2.2,
        (map_peirceBdGHamiltonian (ofStage 5)
          (cl55ToStage5 ω) (cl55ToStage5 D_cl)
          (cl55ToStage5 A_cl) (cl55ToStage5 C_cl)).2.2]
  have hMC_cl :
      peirceMaurerCartanCurvature ω A_cl C_cl =
        genJ ω A_cl C_cl + genV ω A_cl C_cl := by
    unfold peirceMaurerCartanCurvature peirceGradingDeriv
    peirce_nf hω
  have hMC :
      ofStage (5 + 8 * k) (cl55ToBottStage k (peirceMaurerCartanCurvature ω A_cl C_cl)) =
        genJ (ofStage 5 (cl55ToStage5 ω))
            (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) +
          genV (ofStage 5 (cl55ToStage5 ω))
            (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) := by
    rw [hCoherent, hMC_cl, map_add, map_genJ, map_genV, map_add, map_genJ, map_genV]
  have hMapF :
      ofStage (5 + 8 * k) (cl55ToBottStage k (polygonFibSeq ω A_cl C_cl m)) =
        polygonFibSeq (ofStage 5 (cl55ToStage5 ω))
          (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) m := by
    rw [hCoherent, map_polygonFibSeq cl55ToStage5 ω A_cl C_cl m,
        map_polygonFibSeq (ofStage 5)
          (cl55ToStage5 ω) (cl55ToStage5 A_cl) (cl55ToStage5 C_cl) m]
  have hMapL :
      ofStage (5 + 8 * k) (cl55ToBottStage k (polygonLucasGen ω A_cl C_cl m)) =
        polygonLucasGen (ofStage 5 (cl55ToStage5 ω))
          (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) m := by
    rw [hCoherent,
        (map_polygonFibSeq_and_polygonLucasGen cl55ToStage5 ω A_cl C_cl m).2,
        (map_polygonFibSeq_and_polygonLucasGen (ofStage 5)
          (cl55ToStage5 ω) (cl55ToStage5 A_cl) (cl55ToStage5 C_cl) m).2]
  have hInfl :=
    (all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence
      hPlim (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) m).2.2.1
  exact ⟨hCoherent x, hPk, hBdG, hMC, hMapF, hMapL, hInfl⟩

/-- **Theorem 4.1 (`cl55_multi_period_bott_spinor_tower_and_all_m_colimit_bridge`)**:
For every Bott period `k : ℕ`, every polygon stage `m : ℕ`, and all `D_cl A_cl C_cl : Cl55`:
1. **Exact Multi-Period Colimit Invariance:**
   `ofStage (5 + 8 * k) (cl55ToBottStage k x) = ofStage 5 (cl55ToStage5 x)` for all `x : Cl55`;
2. **Bott-Stage Spinor Idempotent:**
   `P_k = cl55ToBottStage k cl55VacuumIdempotent` is an idempotent in `Stage (5 + 8 * k)`;
3. **All-Period Colimit Intertwining of `peirceBdGHamiltonian`, `peirceMaurerCartanCurvature`, `polygonFibSeq`, `polygonLucasGen`, and Inflated Penrose Kite/Dart Powers:**
   `ofStage (5 + 8 * k) ∘ cl55ToBottStage k` transports `peirceBdGHamiltonian`,
   `peirceMaurerCartanCurvature`, `polygonFibSeq`, `polygonLucasGen`, and the `(m + 1)`-step
   Penrose Kite/Dart power inflation law from `Cl(5, 5)` into `Limit`. -/
theorem cl55_multi_period_bott_spinor_tower_and_all_m_colimit_bridge
    (k m : ℕ) (D_cl A_cl C_cl x : InfoGeometry.Clifford.Clifford55.Cl55) :
    let ω := InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent
    let P₅ := cl55ToStage5 ω
    let D₅ := cl55ToStage5 D_cl
    let A₅ := cl55ToStage5 A_cl
    let C₅ := cl55ToStage5 C_cl
    let P_k := cl55ToBottStage k ω
    let P_lim := ofStage 5 P₅
    let D_lim := ofStage 5 D₅
    let A_lim := ofStage 5 A₅
    let C_lim := ofStage 5 C₅
    ofStage (5 + 8 * k) (cl55ToBottStage k x) = ofStage 5 (cl55ToStage5 x) ∧
    P_k * P_k = P_k ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (peirceBdGHamiltonian ω D_cl A_cl C_cl)) =
      peirceBdGHamiltonian P_lim D_lim A_lim C_lim ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (peirceMaurerCartanCurvature ω A_cl C_cl)) =
      genJ P_lim A_lim C_lim + genV P_lim A_lim C_lim ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (polygonFibSeq ω A_cl C_cl m)) =
      polygonFibSeq P_lim A_lim C_lim m ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (polygonLucasGen ω A_cl C_cl m)) =
      polygonLucasGen P_lim A_lim C_lim m ∧
    (penroseKiteOp P_lim A_lim C_lim) ^ (m + 1) =
      polygonFibSeq P_lim A_lim C_lim (m + 1) * penroseKiteOp P_lim A_lim C_lim +
        penroseDartOp P_lim A_lim C_lim * polygonFibSeq P_lim A_lim C_lim m :=
  cl55_multi_period_bott_intertwiner_of_idempotent
    InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent_idempotent
    k m D_cl A_cl C_cl x

end MultiPeriodCl55BottSpinorTower

/-! ## 5. The 4-Fold Peirce Tetraktys Ladder (`1 + 2 + 1 = 4`) & Polygon Bivector Action -/

section FourFoldTetraktysLadderAndPolygonBivector

/-- **Theorem 5.1 (`tetraktys_witt_clifford_fourfold_ladder_and_polygon_bivector_bridge`)**:
Unifies the two dual viewpoints of the 4-Fold Peirce Tetraktys (`Φ, J, V, Σ`, `1 + 2 + 1 = 4`)
and its action on the all-`m` polygon Fibonacci sequence in any associative ring `[Ring B]`
with idempotent `P` (`P * P = P`):
1. **Viewpoint 1 (Null Witt Lightcone Corners `N₊, N₋` → Interior `V` + Exterior `Σ`):**
   - `conePlus P A * conePlus P A = 0` and `coneMinus P C * coneMinus P C = 0`,
   - `anticomm (conePlus P A) (coneMinus P C) = genV P A C` (interior / Jordan product),
   - `comm (conePlus P A) (coneMinus P C) = genSig P A C` (exterior / Lie wedge product),
   - `genV P A C + genSig P A C = (2 : ℤ) • qgtPlus P A C` and
     `genV P A C - genSig P A C = (2 : ℤ) • qgtMinus P A C`;
2. **Viewpoint 2 (Orthogonal `Cl(1, 1)` 1-Vectors `Φ, J` → Interior `V` + Exterior `Σ`):**
   - `genPhi P A C * genPhi P A C = genV P A C` and `genJ P A C * genJ P A C = -genV P A C`,
   - `anticomm (genPhi P A C) (genJ P A C) = 0` (mutual Clifford orthogonality),
   - `genJ P A C * genPhi P A C = genSig P A C` and `genPhi P A C * genJ P A C = -genSig P A C`,
   - `genSig P A C = invS P * genV P A C`;
3. **Bivector `Σ` Action on the All-`m` Polygon Fibonacci Sequence:**
   - `genSig P A C * polygonFibSeq P A C m =
       invS P * (polygonFibSeq P A C (m + 2) - polygonFibSeq P A C (m + 1))`. -/
theorem tetraktys_witt_clifford_fourfold_ladder_and_polygon_bivector_bridge
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (m : ℕ) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    anticomm (conePlus P A) (coneMinus P C) = genV P A C ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (coneMinus P C) = genSig P A C ∧
    genV P A C + genSig P A C = (2 : ℤ) • qgtPlus P A C ∧
    genV P A C - genSig P A C = (2 : ℤ) • qgtMinus P A C ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C = -genSig P A C ∧
    genSig P A C = invS P * genV P A C ∧
    genSig P A C * polygonFibSeq P A C m =
      invS P * (polygonFibSeq P A C (m + 2) - polygonFibSeq P A C (m + 1)) := by
  have hSigSV : genSig P A C = invS P * genV P A C := by peirce_nf hP
  refine ⟨by peirce_nf hP, by peirce_nf hP, rfl, rfl,
    by unfold qgtPlus; peirce_nf hP,
    by unfold qgtMinus; peirce_nf hP,
    by peirce_nf hP, by peirce_nf hP,
    by unfold anticomm; peirce_nf hP,
    by peirce_nf hP, by peirce_nf hP, hSigSV, ?_⟩
  rw [hSigSV, mul_assoc (invS P) (genV P A C) (polygonFibSeq P A C m)]
  congr 1
  simp only [polygonFibSeq_succ_succ, add_sub_cancel_left]

end FourFoldTetraktysLadderAndPolygonBivector

/-! ## 6. Tetraktys Sandwich Character Channels → Unit-Square Klein Four-Group Action (`peirceKleinHom`) -/

section SandwichChannelsToUnitSquareKleinAction

/-- **Theorem 6.1 (`sandwich_channel_universal_parity_and_mass_factorization`)**:
In any associative ring `[Ring B]` with idempotent `P` (`P * P = P`), before imposing any
unit-square condition on `V = genV P A C`:
1. **Universal Parity-Grading Factorization of `Σ` and `J`:**
   - `genSig P A C = invS P * genV P A C` and `genSig P A C = genV P A C * invS P`,
   - `genJ P A C = invS P * genPhi P A C` and `genJ P A C = -(genPhi P A C * invS P)`;
2. **Universal Sandwich Intertwining of `J`, `Φ`, and `parityConj`:**
   - `-(genJ P A C * X * genJ P A C) = genPhi P A C * parityConj P X * genPhi P A C`,
   - `-(genJ P A C * X * genJ P A C) = parityConj P (genPhi P A C * X * genPhi P A C)`;
3. **Exact Factorization of the Sandwich Character Channels `grpJ` and `grpSig` through `parityConj`:**
   - `grpJ P A C X = grpPhi P A C (parityConj P X)`,
   - `grpSig P A C X = genV P A C * parityConj P X * genV P A C`. -/
theorem sandwich_channel_universal_parity_and_mass_factorization
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B) :
    genSig P A C = invS P * genV P A C ∧
    genSig P A C = genV P A C * invS P ∧
    genJ P A C = invS P * genPhi P A C ∧
    genJ P A C = -(genPhi P A C * invS P) ∧
    -(genJ P A C * X * genJ P A C) = genPhi P A C * parityConj P X * genPhi P A C ∧
    -(genJ P A C * X * genJ P A C) = parityConj P (genPhi P A C * X * genPhi P A C) ∧
    grpJ P A C X = grpPhi P A C (parityConj P X) ∧
    grpSig P A C X = genV P A C * parityConj P X * genV P A C := by
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
    by unfold parityConj; peirce_nf hP,
    by unfold parityConj; peirce_nf hP,
    by unfold grpJ grpPhi parityConj; peirce_nf hP,
    by unfold grpSig parityConj; peirce_nf hP⟩

/-- **Theorem 6.2 (`peirceKleinHom_eq_group_sandwich_character_channels_and_fourier_projectors`)**:
Bridges the polynomial sandwich character channels (`grpId`, `grpPhi`, `grpSig`, `grpJ`,
`fourierV`, `fourierPhi`, `fourierJ`, `fourierSig`) in `Homogenized.lean` directly to the
conditional Klein four-group ring-automorphism action `peirceKleinHom hP A C hV` in
`UnitSquareAction.lean` and `KleinAction.lean` under the unit-square hypothesis
`hV : genV P A C = 1`:
1. **Bivector Collapse to the Peirce Grading Involution:**
   `genSig P A C = invS P`;
2. **Exact Identification of All Four Klein Four-Group Automorphisms with the Four Sandwich Character Channels:**
   For every ambient ring element `X : B`:
   - `(peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 0))) X = grpId P A C X` and `grpId P A C X = X`,
   - `(peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 0))) X = grpPhi P A C X` and
     `grpPhi P A C X = phiUnitSquareEquiv hP A C hV X`,
   - `(peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 1))) X = grpSig P A C X` and
     `grpSig P A C X = parityConjRingEquiv hP X`,
   - `(peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 1))) X = grpJ P A C X` and
     `grpJ P A C X = phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X)`;
3. **Fourier Character Combinations as Explicit Klein Group-Ring Averages:**
   - `fourierV P A C X = (2 : ℤ) • ((peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 0))) X +
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 0))) X +
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 1))) X +
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 1))) X)`,
   - `fourierPhi P A C X = (2 : ℤ) • ((peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 0))) X +
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 0))) X -
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 1))) X -
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 1))) X)`,
   - `fourierJ P A C X = (2 : ℤ) • ((peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 0))) X -
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 0))) X +
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 1))) X -
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 1))) X)`,
   - `fourierSig P A C X = (2 : ℤ) • ((peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 0))) X -
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 0))) X -
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 1))) X +
       (peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 1))) X)`. -/
theorem peirceKleinHom_eq_group_sandwich_character_channels_and_fourier_projectors
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
    (hV : genV P A C = 1) (X : B) :
    let K := peirceKleinHom hP A C hV
    let g00 : Multiplicative (ZMod 2 × ZMod 2) := Multiplicative.ofAdd (0, 0)
    let g10 : Multiplicative (ZMod 2 × ZMod 2) := Multiplicative.ofAdd (1, 0)
    let g01 : Multiplicative (ZMod 2 × ZMod 2) := Multiplicative.ofAdd (0, 1)
    let g11 : Multiplicative (ZMod 2 × ZMod 2) := Multiplicative.ofAdd (1, 1)
    genSig P A C = invS P ∧
    (K g00) X = grpId P A C X ∧
    grpId P A C X = X ∧
    (K g10) X = grpPhi P A C X ∧
    grpPhi P A C X = phiUnitSquareEquiv hP A C hV X ∧
    (K g01) X = grpSig P A C X ∧
    grpSig P A C X = parityConjRingEquiv hP X ∧
    (K g11) X = grpJ P A C X ∧
    grpJ P A C X = phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X) ∧
    fourierV P A C X = (2 : ℤ) • ((K g00) X + (K g10) X + (K g11) X + (K g01) X) ∧
    fourierPhi P A C X = (2 : ℤ) • ((K g00) X + (K g10) X - (K g11) X - (K g01) X) ∧
    fourierJ P A C X = (2 : ℤ) • ((K g00) X - (K g10) X + (K g11) X - (K g01) X) ∧
    fourierSig P A C X = (2 : ℤ) • ((K g00) X - (K g10) X - (K g11) X + (K g01) X) := by
  dsimp only
  have hSigS : genSig P A C = invS P := by
    calc
      genSig P A C = invS P * genV P A C := by peirce_nf hP
      _ = invS P * 1 := by rw [hV]
      _ = invS P := mul_one (invS P)
  have hGrpId : grpId P A C X = X := by
    unfold grpId
    rw [hV, mul_one, one_mul]
  have hK00 : (peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 0))) X = X := rfl
  have hGrpPhi : grpPhi P A C X = phiUnitSquareEquiv hP A C hV X := by
    change genV P A C * (genPhi P A C * X * genPhi P A C) = genPhi P A C * X * genPhi P A C
    rw [hV, one_mul]
  have hK10 :
      (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 0))) X =
        phiUnitSquareEquiv hP A C hV X := rfl
  have hGrpSig : grpSig P A C X = parityConjRingEquiv hP X := by
    change genSig P A C * X * genSig P A C = invS P * X * invS P
    rw [hSigS]
  have hK01 :
      (peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 1))) X =
        parityConjRingEquiv hP X := rfl
  have hGrpJ :
      grpJ P A C X = phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X) := by
    rw [(sandwich_channel_universal_parity_and_mass_factorization hP A C X).2.2.2.2.2.2.1]
    change genV P A C * (genPhi P A C * parityConj P X * genPhi P A C) =
      genPhi P A C * parityConj P X * genPhi P A C
    rw [hV, one_mul]
  have hK11 :
      (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 1))) X =
        phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X) := rfl
  have hEq00 : (peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 0))) X = grpId P A C X :=
    hK00.trans hGrpId.symm
  have hEq10 : (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 0))) X = grpPhi P A C X :=
    hK10.trans hGrpPhi.symm
  have hEq01 : (peirceKleinHom hP A C hV (Multiplicative.ofAdd (0, 1))) X = grpSig P A C X :=
    hK01.trans hGrpSig.symm
  have hEq11 : (peirceKleinHom hP A C hV (Multiplicative.ofAdd (1, 1))) X = grpJ P A C X :=
    hK11.trans hGrpJ.symm
  refine ⟨hSigS, hEq00, hGrpId, hEq10, hGrpPhi, hEq01, hGrpSig, hEq11, hGrpJ, ?_, ?_, ?_, ?_⟩
  · unfold fourierV
    rw [hEq00, hEq10, hEq11, hEq01]
  · unfold fourierPhi
    rw [hEq00, hEq10, hEq11, hEq01]
  · unfold fourierJ
    rw [hEq00, hEq10, hEq11, hEq01]
  · unfold fourierSig
    rw [hEq00, hEq10, hEq11, hEq01]

end SandwichChannelsToUnitSquareKleinAction

/-! ## 7. All-`m` Eisenstein–Chebyshev Cyclotomic Tower (`eisensteinSeq`, `eisensteinLucasGen`) & Golden–Eisenstein Duality -/

section AllMEisensteinCyclotomicTower

variable {B : Type*} [Ring B]

/-- **All-`m` Operator Eisenstein–Chebyshev Polynomial Sequence (`eisensteinSeq`)**:
The elliptic hypercomplex (`γ = -1`) partner to `polygonFibSeq` (`γ = +1`), defined
recursively over any non-commutative ring `B` in terms of `V = genV P A C`:
- `eisensteinSeq P A C 0 = 0`,
- `eisensteinSeq P A C 1 = 1`,
- `eisensteinSeq P A C (m + 2) = eisensteinSeq P A C (m + 1) - genV P A C * eisensteinSeq P A C m`. -/
def eisensteinSeq (P A C : B) : ℕ → B
  | 0 => 0
  | 1 => 1
  | m + 2 => eisensteinSeq P A C (m + 1) - genV P A C * eisensteinSeq P A C m

/-- **All-`m` Operator Eisenstein Lucas–Chebyshev Trace Sequence (`eisensteinLucasGen`)**:
The symmetric `m`-th power sum of the operator `Φ₆` roots `peirceTransferJ P A C = P + J`
and `peirceTransferJComplement P A C = (1 - P) - J`:
`eisensteinLucasGen P A C m = (peirceTransferJ P A C) ^ m + (peirceTransferJComplement P A C) ^ m`. -/
def eisensteinLucasGen (P A C : B) (m : ℕ) : B :=
  (peirceTransferJ P A C) ^ m + (peirceTransferJComplement P A C) ^ m

@[simp]
theorem eisensteinSeq_zero (P A C : B) : eisensteinSeq P A C 0 = 0 := rfl

@[simp]
theorem eisensteinSeq_one (P A C : B) : eisensteinSeq P A C 1 = 1 := rfl

@[simp]
theorem eisensteinSeq_succ_succ (P A C : B) (m : ℕ) :
    eisensteinSeq P A C (m + 2) =
      eisensteinSeq P A C (m + 1) - genV P A C * eisensteinSeq P A C m := rfl

/-- Any element `X : B` that commutes with `genV P A C` commutes with `eisensteinSeq P A C m`
for every `m : ℕ`. -/
theorem eisensteinSeq_comm_of_genV_comm (P A C X : B)
    (hVX : genV P A C * X = X * genV P A C) :
    ∀ m : ℕ, eisensteinSeq P A C m * X = X * eisensteinSeq P A C m
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
      have ih1 := eisensteinSeq_comm_of_genV_comm P A C X hVX (m + 1)
      have ih0 := eisensteinSeq_comm_of_genV_comm P A C X hVX m
      simp only [eisensteinSeq_succ_succ, sub_mul, mul_sub]
      rw [ih1, mul_assoc (genV P A C) (eisensteinSeq P A C m) X, ih0,
          ← mul_assoc (genV P A C) X (eisensteinSeq P A C m), hVX,
          mul_assoc X (genV P A C) (eisensteinSeq P A C m)]

/-- Universal ring-homomorphism functoriality of `eisensteinSeq`. -/
theorem map_eisensteinSeq
    {D : Type*} [Ring D] (f : B →+* D) (P A C : B) :
    ∀ m : ℕ, f (eisensteinSeq P A C m) = eisensteinSeq (f P) (f A) (f C) m
  | 0 => by simp
  | 1 => by simp
  | k + 2 => by
      simp only [eisensteinSeq_succ_succ, map_sub, map_mul, map_genV,
        map_eisensteinSeq f P A C (k + 1), map_eisensteinSeq f P A C k]

/-- Universal ring-homomorphism functoriality of `eisensteinSeq` and `eisensteinLucasGen`. -/
theorem map_eisensteinSeq_and_eisensteinLucasGen
    {D : Type*} [Ring D] (f : B →+* D) (P A C : B) (m : ℕ) :
    f (eisensteinSeq P A C m) = eisensteinSeq (f P) (f A) (f C) m ∧
    f (eisensteinLucasGen P A C m) = eisensteinLucasGen (f P) (f A) (f C) m := by
  refine ⟨map_eisensteinSeq f P A C m, ?_⟩
  unfold eisensteinLucasGen peirceTransferJ peirceTransferJComplement
  rw [map_add, map_pow, map_pow, map_add, map_sub, map_sub, map_one, map_genJ]

/-- Klein-bottle meridian parity invariance of `eisensteinSeq P A C m` for all `m : ℕ`. -/
theorem parityConj_eisensteinSeq
    {P : B} (hP : P * P = P) (A C : B) :
    ∀ m : ℕ, parityConj P (eisensteinSeq P A C m) = eisensteinSeq P A C m
  | 0 => by unfold parityConj; simp
  | 1 => by simp only [eisensteinSeq_one]; unfold parityConj; peirce_nf hP
  | k + 2 => by
      have hS2 : invS P * invS P = 1 := by peirce_nf hP
      have hParSub : ∀ X Y : B, parityConj P (X - Y) = parityConj P X - parityConj P Y := by
        intro X Y; unfold parityConj; noncomm_ring
      have hParMul : ∀ X Y : B, parityConj P (X * Y) = parityConj P X * parityConj P Y := by
        intro X Y
        unfold parityConj
        calc
          invS P * (X * Y) * invS P =
              invS P * X * (invS P * invS P) * Y * invS P := by
            rw [hS2]; noncomm_ring
          _ = (invS P * X * invS P) * (invS P * Y * invS P) := by noncomm_ring
      have hParV : parityConj P (genV P A C) = genV P A C := by
        unfold parityConj; peirce_nf hP
      simp only [eisensteinSeq_succ_succ, hParSub, hParMul, hParV,
        parityConj_eisensteinSeq hP A C (k + 1), parityConj_eisensteinSeq hP A C k]

/-- **Theorem 7.1 (`eisensteinSeq_and_eisensteinLucasGen_one_through_six`)**:
Explicit operator polynomial expansions of `eisensteinSeq P A C m` for `2 ≤ m ≤ 6`
and the alternating-sign Hexagon Eisenstein trace `eisensteinLucasGen P A C 6` vs.
the paracomplex Golden Hexagon trace `polygonLucas6 P A C`:
- `eisensteinSeq P A C 2 = 1`,
- `eisensteinSeq P A C 3 = 1 - genV P A C` (vanishes on the unit cyclotomic shell `V = 1`),
- `eisensteinSeq P A C 4 = 1 - (2 : ℤ) • genV P A C`,
- `eisensteinSeq P A C 5 = 1 - (3 : ℤ) • genV P A C + genV P A C * genV P A C`,
- `eisensteinSeq P A C 6 = (1 - genV P A C) * (1 - (3 : ℤ) • genV P A C)`,
- `eisensteinLucasGen P A C 3 = 1 - (3 : ℤ) • genV P A C`,
- `eisensteinLucasGen P A C 6 =
    1 - (6 : ℤ) • genV P A C + (9 : ℤ) • (genV P A C * genV P A C) -
      (2 : ℤ) • (genV P A C * genV P A C * genV P A C)`. -/
theorem eisensteinSeq_and_eisensteinLucasGen_one_through_six
    {P : B} (hP : P * P = P) (A C : B) :
    eisensteinSeq P A C 2 = 1 ∧
    eisensteinSeq P A C 3 = 1 - genV P A C ∧
    eisensteinSeq P A C 4 = 1 - (2 : ℤ) • genV P A C ∧
    eisensteinSeq P A C 5 =
      1 - (3 : ℤ) • genV P A C + genV P A C * genV P A C ∧
    eisensteinSeq P A C 6 =
      (1 - genV P A C) * (1 - (3 : ℤ) • genV P A C) ∧
    eisensteinLucasGen P A C 3 = 1 - (3 : ℤ) • genV P A C ∧
    eisensteinLucasGen P A C 6 =
      1 - (6 : ℤ) • genV P A C + (9 : ℤ) • (genV P A C * genV P A C) -
        (2 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
  have h2 : eisensteinSeq P A C 2 = 1 := by
    change eisensteinSeq P A C 1 - genV P A C * eisensteinSeq P A C 0 = 1
    simp
  have h3 : eisensteinSeq P A C 3 = 1 - genV P A C := by
    change eisensteinSeq P A C 2 - genV P A C * eisensteinSeq P A C 1 = 1 - genV P A C
    rw [h2, eisensteinSeq_one, mul_one]
  have h4 : eisensteinSeq P A C 4 = 1 - (2 : ℤ) • genV P A C := by
    change eisensteinSeq P A C 3 - genV P A C * eisensteinSeq P A C 2 = _
    rw [h3, h2, mul_one]
    noncomm_ring
  have h5 : eisensteinSeq P A C 5 =
      1 - (3 : ℤ) • genV P A C + genV P A C * genV P A C := by
    change eisensteinSeq P A C 4 - genV P A C * eisensteinSeq P A C 3 = _
    rw [h4, h3]
    noncomm_ring
  have h6 : eisensteinSeq P A C 6 =
      (1 - genV P A C) * (1 - (3 : ℤ) • genV P A C) := by
    change eisensteinSeq P A C 5 - genV P A C * eisensteinSeq P A C 4 = _
    rw [h5, h4]
    noncomm_ring
  refine ⟨h2, h3, h4, h5, h6, ?_, ?_⟩
  · simp only [eisensteinLucasGen, peirceTransferJ, peirceTransferJComplement,
      pow_succ, pow_zero, one_mul]
    peirce_nf hP
  · simp only [eisensteinLucasGen, peirceTransferJ, peirceTransferJComplement,
      pow_succ, pow_zero, one_mul]
    peirce_nf hP

/-- **Theorem 7.2 (`all_m_eisenstein_power_linearization_radical_factorization_and_bianchi`)**:
In any non-commutative ring `B` with idempotent `P` (`P * P = P`), for every `m : ℕ`:
1. **Zero-Shell `Φ₆` Characteristic Polynomial & All-`m` Eisenstein Power Linearization:**
   - `opCharPolyPhi6 P A C (peirceTransferJ P A C) = 0` and
     `opCharPolyPhi6 P A C (peirceTransferJComplement P A C) = 0`,
   - `(peirceTransferJ P A C) ^ (m + 1) =
       eisensteinSeq P A C (m + 1) * peirceTransferJ P A C -
         genV P A C * eisensteinSeq P A C m`,
   - `(peirceTransferJComplement P A C) ^ (m + 1) =
       eisensteinSeq P A C (m + 1) * peirceTransferJComplement P A C -
         genV P A C * eisensteinSeq P A C m`;
2. **All-`m` Eisenstein Radical Difference & Lucas–Chebyshev Trace Recurrence:**
   - `(peirceTransferJ P A C) ^ m - (peirceTransferJComplement P A C) ^ m =
       eisensteinSeq P A C m * radicalLetterMinus P A C`,
   - `eisensteinLucasGen P A C (m + 1) =
       eisensteinSeq P A C (m + 1) - (2 : ℤ) • (genV P A C * eisensteinSeq P A C m)`,
   - `eisensteinLucasGen P A C (m + 2) =
       eisensteinLucasGen P A C (m + 1) - genV P A C * eisensteinLucasGen P A C m`;
3. **All-`m` Klein-Bottle Meridian Invariance & Covariant Bianchi Constancy:**
   - `parityConj P (eisensteinSeq P A C m) = eisensteinSeq P A C m`,
   - `parityConj P (eisensteinLucasGen P A C (m + 1)) = eisensteinLucasGen P A C (m + 1)`,
   - `peirceCovariantDeriv P A C (eisensteinSeq P A C m) = 0`,
   - `peirceCovariantDeriv P A C (eisensteinLucasGen P A C (m + 1)) = 0`. -/
theorem all_m_eisenstein_power_linearization_radical_factorization_and_bianchi
    {P : B} (hP : P * P = P) (A C : B) (m : ℕ) :
    opCharPolyPhi6 P A C (peirceTransferJ P A C) = 0 ∧
    opCharPolyPhi6 P A C (peirceTransferJComplement P A C) = 0 ∧
    (peirceTransferJ P A C) ^ (m + 1) =
      eisensteinSeq P A C (m + 1) * peirceTransferJ P A C -
        genV P A C * eisensteinSeq P A C m ∧
    (peirceTransferJComplement P A C) ^ (m + 1) =
      eisensteinSeq P A C (m + 1) * peirceTransferJComplement P A C -
        genV P A C * eisensteinSeq P A C m ∧
    (peirceTransferJ P A C) ^ m - (peirceTransferJComplement P A C) ^ m =
      eisensteinSeq P A C m * radicalLetterMinus P A C ∧
    eisensteinLucasGen P A C (m + 1) =
      eisensteinSeq P A C (m + 1) - (2 : ℤ) • (genV P A C * eisensteinSeq P A C m) ∧
    eisensteinLucasGen P A C (m + 2) =
      eisensteinLucasGen P A C (m + 1) - genV P A C * eisensteinLucasGen P A C m ∧
    parityConj P (eisensteinSeq P A C m) = eisensteinSeq P A C m ∧
    parityConj P (eisensteinLucasGen P A C (m + 1)) = eisensteinLucasGen P A C (m + 1) ∧
    peirceCovariantDeriv P A C (eisensteinSeq P A C m) = 0 ∧
    peirceCovariantDeriv P A C (eisensteinLucasGen P A C (m + 1)) = 0 := by
  have hPhi6W : opCharPolyPhi6 P A C (peirceTransferJ P A C) = 0 := by
    unfold opCharPolyPhi6 peirceTransferJ; peirce_nf hP
  have hPhi6Wbar : opCharPolyPhi6 P A C (peirceTransferJComplement P A C) = 0 := by
    unfold opCharPolyPhi6 peirceTransferJComplement; peirce_nf hP
  have hW2 : peirceTransferJ P A C * peirceTransferJ P A C =
      peirceTransferJ P A C - genV P A C := by
    unfold peirceTransferJ; peirce_nf hP
  have hWbar2 : peirceTransferJComplement P A C * peirceTransferJComplement P A C =
      peirceTransferJComplement P A C - genV P A C := by
    unfold peirceTransferJComplement; peirce_nf hP
  have hEisCommV : ∀ k : ℕ,
      eisensteinSeq P A C k * genV P A C = genV P A C * eisensteinSeq P A C k :=
    eisensteinSeq_comm_of_genV_comm P A C (genV P A C) rfl
  have hPowBoth : ∀ k : ℕ,
      (peirceTransferJ P A C) ^ (k + 1) =
        eisensteinSeq P A C (k + 1) * peirceTransferJ P A C -
          genV P A C * eisensteinSeq P A C k ∧
      (peirceTransferJComplement P A C) ^ (k + 1) =
        eisensteinSeq P A C (k + 1) * peirceTransferJComplement P A C -
          genV P A C * eisensteinSeq P A C k := by
    intro k
    induction k with
    | zero =>
        simp
    | succ j ih =>
        rcases ih with ⟨ihW, ihWbar⟩
        refine ⟨?_, ?_⟩
        · rw [pow_succ (peirceTransferJ P A C) (j + 1), ihW]
          calc
            (eisensteinSeq P A C (j + 1) * peirceTransferJ P A C -
                genV P A C * eisensteinSeq P A C j) * peirceTransferJ P A C =
              eisensteinSeq P A C (j + 1) *
                  (peirceTransferJ P A C * peirceTransferJ P A C) -
                genV P A C * eisensteinSeq P A C j * peirceTransferJ P A C := by noncomm_ring
            _ = eisensteinSeq P A C (j + 1) * (peirceTransferJ P A C - genV P A C) -
                genV P A C * eisensteinSeq P A C j * peirceTransferJ P A C := by rw [hW2]
            _ = (eisensteinSeq P A C (j + 1) - genV P A C * eisensteinSeq P A C j) *
                  peirceTransferJ P A C -
                eisensteinSeq P A C (j + 1) * genV P A C := by noncomm_ring
            _ = eisensteinSeq P A C (j + 2) * peirceTransferJ P A C -
                genV P A C * eisensteinSeq P A C (j + 1) := by
              rw [hEisCommV (j + 1)]
              rfl
        · rw [pow_succ (peirceTransferJComplement P A C) (j + 1), ihWbar]
          calc
            (eisensteinSeq P A C (j + 1) * peirceTransferJComplement P A C -
                genV P A C * eisensteinSeq P A C j) * peirceTransferJComplement P A C =
              eisensteinSeq P A C (j + 1) *
                  (peirceTransferJComplement P A C * peirceTransferJComplement P A C) -
                genV P A C * eisensteinSeq P A C j *
                  peirceTransferJComplement P A C := by noncomm_ring
            _ = eisensteinSeq P A C (j + 1) *
                  (peirceTransferJComplement P A C - genV P A C) -
                genV P A C * eisensteinSeq P A C j *
                  peirceTransferJComplement P A C := by rw [hWbar2]
            _ = (eisensteinSeq P A C (j + 1) - genV P A C * eisensteinSeq P A C j) *
                  peirceTransferJComplement P A C -
                eisensteinSeq P A C (j + 1) * genV P A C := by noncomm_ring
            _ = eisensteinSeq P A C (j + 2) * peirceTransferJComplement P A C -
                genV P A C * eisensteinSeq P A C (j + 1) := by
              rw [hEisCommV (j + 1)]
              rfl
  rcases hPowBoth m with ⟨hWm, hWbarm⟩
  have hDiff : (peirceTransferJ P A C) ^ m - (peirceTransferJComplement P A C) ^ m =
      eisensteinSeq P A C m * radicalLetterMinus P A C := by
    cases m with
    | zero => simp
    | succ j =>
        rcases hPowBoth j with ⟨hWj, hWbarj⟩
        rw [hWj, hWbarj]
        have hSub : peirceTransferJ P A C - peirceTransferJComplement P A C =
            radicalLetterMinus P A C := by
          unfold radicalLetterMinus peirceTransferJ peirceTransferJComplement
          noncomm_ring
        calc
          (eisensteinSeq P A C (j + 1) * peirceTransferJ P A C -
              genV P A C * eisensteinSeq P A C j) -
            (eisensteinSeq P A C (j + 1) * peirceTransferJComplement P A C -
              genV P A C * eisensteinSeq P A C j) =
            eisensteinSeq P A C (j + 1) *
              (peirceTransferJ P A C - peirceTransferJComplement P A C) := by noncomm_ring
          _ = eisensteinSeq P A C (j + 1) * radicalLetterMinus P A C := by rw [hSub]
  have hEisCross : ∀ k : ℕ,
      eisensteinLucasGen P A C (k + 1) =
        eisensteinSeq P A C (k + 1) -
          (2 : ℤ) • (genV P A C * eisensteinSeq P A C k) := by
    intro k
    rcases hPowBoth k with ⟨hWk, hWbark⟩
    unfold eisensteinLucasGen
    rw [hWk, hWbark]
    have hSum : peirceTransferJ P A C + peirceTransferJComplement P A C = 1 := by
      unfold peirceTransferJ peirceTransferJComplement; noncomm_ring
    calc
      (eisensteinSeq P A C (k + 1) * peirceTransferJ P A C -
          genV P A C * eisensteinSeq P A C k) +
        (eisensteinSeq P A C (k + 1) * peirceTransferJComplement P A C -
          genV P A C * eisensteinSeq P A C k) =
        eisensteinSeq P A C (k + 1) *
            (peirceTransferJ P A C + peirceTransferJComplement P A C) -
          (2 : ℤ) • (genV P A C * eisensteinSeq P A C k) := by noncomm_ring
      _ = eisensteinSeq P A C (k + 1) -
          (2 : ℤ) • (genV P A C * eisensteinSeq P A C k) := by rw [hSum, mul_one]
  have hEisRec :
      eisensteinLucasGen P A C (m + 2) =
        eisensteinLucasGen P A C (m + 1) - genV P A C * eisensteinLucasGen P A C m := by
    unfold eisensteinLucasGen
    have hWRec : ∀ X V₀ : B, X * X = X - V₀ → ∀ k : ℕ,
        X ^ (k + 2) = X ^ (k + 1) - V₀ * X ^ k := by
      intro X V₀ hX2 k
      induction k with
      | zero =>
          rw [zero_add, pow_two, pow_one, pow_zero, mul_one]
          exact hX2
      | succ j ih =>
          calc
            X ^ (j + 1 + 2) = X ^ (j + 2) * X := pow_succ X (j + 2)
            _ = (X ^ (j + 1) - V₀ * X ^ j) * X := by rw [ih]
            _ = X ^ (j + 1 + 1) - V₀ * X ^ (j + 1) := by
              rw [sub_mul, ← pow_succ X (j + 1), mul_assoc V₀ (X ^ j) X, ← pow_succ X j]
    have hVcommW : genV P A C * peirceTransferJ P A C =
        peirceTransferJ P A C * genV P A C := by
      unfold peirceTransferJ; peirce_nf hP
    rw [hWRec (peirceTransferJ P A C) (genV P A C) hW2 m,
        hWRec (peirceTransferJComplement P A C) (genV P A C) hWbar2 m]
    noncomm_ring
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  have hParSub : ∀ X Y : B, parityConj P (X - Y) = parityConj P X - parityConj P Y := by
    intro X Y; unfold parityConj; noncomm_ring
  have hParZsmul : ∀ (n : ℤ) (X : B), parityConj P (n • X) = n • parityConj P X := by
    intro n X; unfold parityConj; noncomm_ring
  have hParMul : ∀ X Y : B, parityConj P (X * Y) = parityConj P X * parityConj P Y := by
    intro X Y
    unfold parityConj
    calc
      invS P * (X * Y) * invS P =
          invS P * X * (invS P * invS P) * Y * invS P := by
        rw [hS2]; noncomm_ring
      _ = (invS P * X * invS P) * (invS P * Y * invS P) := by noncomm_ring
  have hParV : parityConj P (genV P A C) = genV P A C := by
    unfold parityConj; peirce_nf hP
  have hParLucas : parityConj P (eisensteinLucasGen P A C (m + 1)) =
      eisensteinLucasGen P A C (m + 1) := by
    rw [hEisCross m, hParSub, hParZsmul, hParMul, hParV,
        parityConj_eisensteinSeq hP A C (m + 1), parityConj_eisensteinSeq hP A C m]
  have hVQ : genV P A C * P = P * genV P A C := by peirce_nf hP
  have hVPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by
    peirce_nf hP
  have hEisQ : ∀ k : ℕ, eisensteinSeq P A C k * P = P * eisensteinSeq P A C k :=
    eisensteinSeq_comm_of_genV_comm P A C P hVQ
  have hEisPhi : ∀ k : ℕ, eisensteinSeq P A C k * genPhi P A C =
      genPhi P A C * eisensteinSeq P A C k :=
    eisensteinSeq_comm_of_genV_comm P A C (genPhi P A C) hVPhi
  have hCovEis : ∀ k : ℕ, peirceCovariantDeriv P A C (eisensteinSeq P A C k) = 0 := by
    intro k
    unfold peirceCovariantDeriv peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [← hEisQ k, ← hEisPhi k, sub_self, sub_self, add_zero]
  have hLucQ :
      eisensteinLucasGen P A C (m + 1) * P =
        P * eisensteinLucasGen P A C (m + 1) := by
    have hVP_eis : (genV P A C * eisensteinSeq P A C m) * P =
        P * (genV P A C * eisensteinSeq P A C m) := by
      rw [mul_assoc, hEisQ m, ← mul_assoc, hVQ, mul_assoc]
    rw [hEisCross m]
    calc
      (eisensteinSeq P A C (m + 1) - (2 : ℤ) • (genV P A C * eisensteinSeq P A C m)) * P =
          eisensteinSeq P A C (m + 1) * P -
            (2 : ℤ) • ((genV P A C * eisensteinSeq P A C m) * P) := by noncomm_ring
      _ = P * eisensteinSeq P A C (m + 1) -
            (2 : ℤ) • (P * (genV P A C * eisensteinSeq P A C m)) := by
          rw [hEisQ (m + 1), hVP_eis]
      _ = P * (eisensteinSeq P A C (m + 1) -
            (2 : ℤ) • (genV P A C * eisensteinSeq P A C m)) := by noncomm_ring
  have hLucPhi :
      eisensteinLucasGen P A C (m + 1) * genPhi P A C =
        genPhi P A C * eisensteinLucasGen P A C (m + 1) := by
    have hVPhi_eis : (genV P A C * eisensteinSeq P A C m) * genPhi P A C =
        genPhi P A C * (genV P A C * eisensteinSeq P A C m) := by
      rw [mul_assoc, hEisPhi m, ← mul_assoc, hVPhi, mul_assoc]
    rw [hEisCross m]
    calc
      (eisensteinSeq P A C (m + 1) - (2 : ℤ) • (genV P A C * eisensteinSeq P A C m)) *
            genPhi P A C =
          eisensteinSeq P A C (m + 1) * genPhi P A C -
            (2 : ℤ) • ((genV P A C * eisensteinSeq P A C m) * genPhi P A C) := by noncomm_ring
      _ = genPhi P A C * eisensteinSeq P A C (m + 1) -
            (2 : ℤ) • (genPhi P A C * (genV P A C * eisensteinSeq P A C m)) := by
          rw [hEisPhi (m + 1), hVPhi_eis]
      _ = genPhi P A C * (eisensteinSeq P A C (m + 1) -
            (2 : ℤ) • (genV P A C * eisensteinSeq P A C m)) := by noncomm_ring
  have hCovLucas :
      peirceCovariantDeriv P A C (eisensteinLucasGen P A C (m + 1)) = 0 := by
    unfold peirceCovariantDeriv peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [← hLucQ, ← hLucPhi, sub_self, sub_self, add_zero]
  exact ⟨hPhi6W, hPhi6Wbar, hWm, hWbarm, hDiff, hEisCross m, hEisRec,
    parityConj_eisensteinSeq hP A C m, hParLucas, hCovEis m, hCovLucas⟩

end AllMEisensteinCyclotomicTower

/-! ## 8. Multi-Period `Cl(5, 5)` Bott-Spinor & Inductive-Colimit Synthesis of Archetypes `X₈ → X₁₁` and the All-`m` Eisenstein–Golden Duality -/

section Cl55MultiPeriodTetraktysKantorCyclotomicEisensteinSynthesis

/-- **Theorem 8.1 (`cl55_multi_period_bott_tetraktys_kantor_cyclotomic_and_eisenstein_colimit_bridge`)**:
For any idempotent `ω : Cl55` (`ω * ω = ω`, such as `cl55VacuumIdempotent`), every Bott
period `k : ℕ`, every stage `m : ℕ`, any paracomplex scalar `z = a + b j ∈ SplitComplex.Carrier ℤ`,
and all `D_cl A_cl C_cl : Cl55`, the multi-period Bott embedding
`ofStage (5 + 8 * k) ∘ cl55ToBottStage k : Cl55 →+* Limit` intertwines:
1. **All-`m` Eisenstein–Chebyshev Sequences (`eisensteinSeq`, `eisensteinLucasGen`) & Power Linearization:**
   - `ofStage (5 + 8 * k) (cl55ToBottStage k (eisensteinSeq ω A_cl C_cl m)) = eisensteinSeq P_lim A_lim C_lim m`,
   - `ofStage (5 + 8 * k) (cl55ToBottStage k (eisensteinLucasGen ω A_cl C_cl m)) = eisensteinLucasGen P_lim A_lim C_lim m`,
   - `(peirceTransferJ P_lim A_lim C_lim) ^ (m + 1) =
       eisensteinSeq P_lim A_lim C_lim (m + 1) * peirceTransferJ P_lim A_lim C_lim -
         genV P_lim A_lim C_lim * eisensteinSeq P_lim A_lim C_lim m`;
2. **Cayley–Dickson Paracomplex Boost (`γ = +1`) vs. Elliptic Hypercomplex (`γ = -1`) Norm Law (`X₁₀`):**
   - `splitComplexToBoostOp P_lim A_lim C_lim ⟨z.re, z.im⟩ *
       splitComplexToBoostOp P_lim A_lim C_lim ⟨z.re, -z.im⟩ =
       (z.re * z.re) • (1 : Limit) - (z.im * z.im) • genV P_lim A_lim C_lim`;
3. **5-Graded Anomaly Generators, Kantor Triple Product, and Zero-Shell Operator Cyclotomic Characteristic Polynomials (`X₁₁`):**
   - `[invS P_lim, bdgUpperAnomaly P_lim D_lim A_lim] = (2 : ℤ) • bdgUpperAnomaly P_lim D_lim A_lim`,
   - `[invS P_lim, bdgLowerAnomaly P_lim D_lim C_lim] = -(2 : ℤ) • bdgLowerAnomaly P_lim D_lim C_lim`,
   - `opKantorTriple (conePlus P_lim A_lim) (coneMinus P_lim C_lim) (conePlus P_lim A_lim) =
       (2 : ℤ) • (genV P_lim A_lim C_lim * conePlus P_lim A_lim)`,
   - `opCharPolyPhi6 P_lim A_lim C_lim (peirceTransferJ P_lim A_lim C_lim) = 0`,
   - `opCharPolyPhi3 P_lim A_lim C_lim (cubeRootOp P_lim A_lim C_lim) = 0`,
   - `opCharPolyTransfer P_lim A_lim C_lim (peirceTransfer P_lim A_lim C_lim) = 0`. -/
theorem cl55_multi_period_bott_tetraktys_kantor_cyclotomic_and_eisenstein_colimit_bridge
    {ω : InfoGeometry.Clifford.Clifford55.Cl55} (hω : ω * ω = ω)
    (k m : ℕ)
    (z : InfoGeometry.Canonical.SplitComplex.Carrier ℤ)
    (D_cl A_cl C_cl : InfoGeometry.Clifford.Clifford55.Cl55) :
    let P₅ := cl55ToStage5 ω
    let D₅ := cl55ToStage5 D_cl
    let A₅ := cl55ToStage5 A_cl
    let C₅ := cl55ToStage5 C_cl
    let P_lim := ofStage 5 P₅
    let D_lim := ofStage 5 D₅
    let A_lim := ofStage 5 A₅
    let C_lim := ofStage 5 C₅
    ofStage (5 + 8 * k) (cl55ToBottStage k (eisensteinSeq ω A_cl C_cl m)) =
      eisensteinSeq P_lim A_lim C_lim m ∧
    ofStage (5 + 8 * k) (cl55ToBottStage k (eisensteinLucasGen ω A_cl C_cl m)) =
      eisensteinLucasGen P_lim A_lim C_lim m ∧
    (peirceTransferJ P_lim A_lim C_lim) ^ (m + 1) =
      eisensteinSeq P_lim A_lim C_lim (m + 1) * peirceTransferJ P_lim A_lim C_lim -
        genV P_lim A_lim C_lim * eisensteinSeq P_lim A_lim C_lim m ∧
    splitComplexToBoostOp P_lim A_lim C_lim ⟨z.re, z.im⟩ *
        splitComplexToBoostOp P_lim A_lim C_lim ⟨z.re, -z.im⟩ =
      (z.re * z.re) • (1 : Limit) - (z.im * z.im) • genV P_lim A_lim C_lim ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (invS P_lim) (bdgUpperAnomaly P_lim D_lim A_lim) =
      (2 : ℤ) • bdgUpperAnomaly P_lim D_lim A_lim ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (invS P_lim) (bdgLowerAnomaly P_lim D_lim C_lim) =
      -(2 : ℤ) • bdgLowerAnomaly P_lim D_lim C_lim ∧
    opKantorTriple (conePlus P_lim A_lim) (coneMinus P_lim C_lim) (conePlus P_lim A_lim) =
      (2 : ℤ) • (genV P_lim A_lim C_lim * conePlus P_lim A_lim) ∧
    opCharPolyPhi6 P_lim A_lim C_lim (peirceTransferJ P_lim A_lim C_lim) = 0 ∧
    opCharPolyPhi3 P_lim A_lim C_lim (cubeRootOp P_lim A_lim C_lim) = 0 ∧
    opCharPolyTransfer P_lim A_lim C_lim (peirceTransfer P_lim A_lim C_lim) = 0 := by
  dsimp only
  have hCoherent : ∀ y : InfoGeometry.Clifford.Clifford55.Cl55,
      ofStage (5 + 8 * k) (cl55ToBottStage k y) = ofStage 5 (cl55ToStage5 y) := by
    intro y
    unfold cl55ToBottStage
    exact directLimitOf_bondMap stageBond 5 (5 + 8 * k) (Nat.le_add_right 5 (8 * k))
      (cl55ToStage5 y)
  have hP5 : cl55ToStage5 ω * cl55ToStage5 ω = cl55ToStage5 ω :=
    map_idempotent cl55ToStage5 hω
  have hPlim :
      ofStage 5 (cl55ToStage5 ω) * ofStage 5 (cl55ToStage5 ω) =
        ofStage 5 (cl55ToStage5 ω) :=
    map_idempotent (ofStage 5) hP5
  have hMapEis :
      ofStage (5 + 8 * k) (cl55ToBottStage k (eisensteinSeq ω A_cl C_cl m)) =
        eisensteinSeq (ofStage 5 (cl55ToStage5 ω))
          (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) m := by
    rw [hCoherent, map_eisensteinSeq cl55ToStage5 ω A_cl C_cl m,
        map_eisensteinSeq (ofStage 5)
          (cl55ToStage5 ω) (cl55ToStage5 A_cl) (cl55ToStage5 C_cl) m]
  have hMapEisL :
      ofStage (5 + 8 * k) (cl55ToBottStage k (eisensteinLucasGen ω A_cl C_cl m)) =
        eisensteinLucasGen (ofStage 5 (cl55ToStage5 ω))
          (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) m := by
    rw [hCoherent,
        (map_eisensteinSeq_and_eisensteinLucasGen cl55ToStage5 ω A_cl C_cl m).2,
        (map_eisensteinSeq_and_eisensteinLucasGen (ofStage 5)
          (cl55ToStage5 ω) (cl55ToStage5 A_cl) (cl55ToStage5 C_cl) m).2]
  have hEisPow :=
    (all_m_eisenstein_power_linearization_radical_factorization_and_bianchi
      hPlim (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) m).2.2.1
  rcases limit_tetraktys_clifford_exterior_and_cayley_dickson_boost_bridge
      (le_refl 5) hP5 (cl55ToStage5 A_cl) (cl55ToStage5 C_cl) z z z.re z.im with
    ⟨_, _, _, _, _, _, _, _, hBoostNorm, _⟩
  rcases limit_kantor_triple_five_grade_anomalies_and_operator_cyclotomic_charpoly_bridge
      (le_refl 5) hP5 (cl55ToStage5 A_cl) (cl55ToStage5 C_cl)
      (cl55ToStage5 D_cl) (cl55ToStage5 D_cl) with
    ⟨_, _, _, _, hEigUp, hEigLow, hTriple, _, _, hPhi6, hPhi3, hTrans⟩
  exact ⟨hMapEis, hMapEisL, hEisPow, hBoostNorm,
    hEigUp, hEigLow, hTriple, hPhi6, hPhi3, hTrans⟩

end Cl55MultiPeriodTetraktysKantorCyclotomicEisensteinSynthesis

/-! ## 9. Carrier Soldering & Ring-Intertwining Bridge: Finite DAG Resolvent, Fock Chiral-Projector Transport, and Penrose Twistor / Split `Cl(4, 4)` Operators ↔ Peirce–Plabic Operator Ring -/

section FockPenroseSplitCl44AndDAGResolventSolderingBridge

open InfoGeometry.SignedNetwork.RankedDAGResolvent
open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.SplitCl44CausalEnvelope
open InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.ChiralTwistorSheets
open InfoGeometry.Twistor.PenroseTwistorOperatorBridge

/-- Sheet projector `P₀ = diag(1, 0) : Matrix (Fin 2) (Fin 2) ℝ` on the two-node DAG carrier. -/
def twoNodeSheetProj : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 0]

/-- Canonical two-node nilpotent DAG adjacency matrix `!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ`. -/
def twoNodeNilpotent : Matrix (Fin 2) (Fin 2) ℝ :=
  twoNodeDAG

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` between the sheet
projector `twoNodeSheetProj` and the nilpotent DAG generator `twoNodeNilpotent`. -/
theorem twoNodeSheetProj_mul_twoNodeNilpotent_ne :
    twoNodeSheetProj * twoNodeNilpotent ≠ twoNodeNilpotent * twoNodeSheetProj := by
  intro hEq
  have h10 : (0 : ℝ) = 1 := by
    simpa [twoNodeSheetProj, twoNodeNilpotent, twoNodeDAG] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hEq
  exact zero_ne_one h10

/-- Two-step finite DAG resolvent evaluation in any associative unital ring:
`finiteGreen T 2 = 1 + T`. -/
theorem finiteGreen_two {B : Type*} [Ring B] (T : B) :
    finiteGreen T 2 = 1 + T := by
  unfold finiteGreen
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, pow_zero, pow_one]

/-- **Theorem 9.1 (`dag_resolvent_peirce_plabic_and_twoNodeDAG_soldering_bridge`)**:
Direct operator-ring soldering between the finite DAG resolvent `finiteGreen`
(`RankedDAGResolvent.lean`) and the Peirce–Plabic operator ring
(`MasterCausalPosetD1ToD15.lean`), specialized also to the canonical two-node DAG
`twoNodeDAG : Matrix (Fin 2) (Fin 2) ℝ`:
1. **Universal Peirce–Plabic Unipotent Shear = 2-Step Nilpotent DAG Resolvent:**
   For any idempotent `P : B` (`P * P = P`) and `A C : B`:
   - `finiteGreen (conePlus P A) 2 = plabicWhiteShear P A` with two-sided inverse
     `finiteGreen (-conePlus P A) 2 = 1 - conePlus P A`,
   - `finiteGreen (-coneMinus P C) 2 = plabicBlackShear P C` with two-sided inverse
     `finiteGreen (coneMinus P C) 2 = 1 + coneMinus P C`;
2. **Plabic Trip Operators, Unipotent Sandwich Automorphisms, Steinberg Braid, and Plabic Boundary Operator as Products of DAG Resolvents:**
   - `plabicTripWB P A C = finiteGreen (conePlus P A) 2 * finiteGreen (-coneMinus P C) 2`,
   - `plabicTripBW P A C = finiteGreen (-coneMinus P C) 2 * finiteGreen (conePlus P A) 2`,
   - `conjPlus P A X = finiteGreen (conePlus P A) 2 * X * finiteGreen (-conePlus P A) 2`,
   - `conjMinus P C X = finiteGreen (-coneMinus P C) 2 * X * finiteGreen (coneMinus P C) 2`,
   - `steinbergBraid P A C = finiteGreen (conePlus P A) 2 * finiteGreen (-coneMinus P C) 2 * finiteGreen (conePlus P A) 2`,
   - `plabicBoundaryOp P A C = finiteGreen (-coneMinus P C) 2 * finiteGreen (conePlus P A) 2 - finiteGreen (conePlus P A) 2 * finiteGreen (-coneMinus P C) 2 = genSig P A C`;
3. **Explicit `2 × 2` Soldering of `twoNodeDAG` to `coneMinus twoNodeSheetProj`:**
   On `Matrix (Fin 2) (Fin 2) ℝ` with sheet projector `P₀ = twoNodeSheetProj`:
   - `twoNodeSheetProj * twoNodeSheetProj = twoNodeSheetProj`,
   - `twoNodeDAG = coneMinus twoNodeSheetProj twoNodeDAG`,
   - `finiteGreen twoNodeDAG 2 = plabicBlackShear twoNodeSheetProj (-twoNodeDAG) = !![1, 0; 1, 1]`,
   - `finiteGreen twoNodeDAG 2 * plabicBlackShear twoNodeSheetProj twoNodeDAG = 1` and
     `plabicBlackShear twoNodeSheetProj twoNodeDAG * finiteGreen twoNodeDAG 2 = 1`. -/
theorem dag_resolvent_peirce_plabic_and_twoNodeDAG_soldering_bridge
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B) :
    let P₀ : Matrix (Fin 2) (Fin 2) ℝ := twoNodeSheetProj
    finiteGreen (conePlus P A) 2 = plabicWhiteShear P A ∧
    finiteGreen (-conePlus P A) 2 = 1 - conePlus P A ∧
    finiteGreen (conePlus P A) 2 * finiteGreen (-conePlus P A) 2 = 1 ∧
    finiteGreen (-conePlus P A) 2 * finiteGreen (conePlus P A) 2 = 1 ∧
    finiteGreen (-coneMinus P C) 2 = plabicBlackShear P C ∧
    finiteGreen (coneMinus P C) 2 = 1 + coneMinus P C ∧
    finiteGreen (-coneMinus P C) 2 * finiteGreen (coneMinus P C) 2 = 1 ∧
    finiteGreen (coneMinus P C) 2 * finiteGreen (-coneMinus P C) 2 = 1 ∧
    plabicTripWB P A C =
      finiteGreen (conePlus P A) 2 * finiteGreen (-coneMinus P C) 2 ∧
    plabicTripBW P A C =
      finiteGreen (-coneMinus P C) 2 * finiteGreen (conePlus P A) 2 ∧
    conjPlus P A X =
      finiteGreen (conePlus P A) 2 * X * finiteGreen (-conePlus P A) 2 ∧
    conjMinus P C X =
      finiteGreen (coneMinus P C) 2 * X * finiteGreen (-coneMinus P C) 2 ∧
    steinbergBraid P A C =
      finiteGreen (conePlus P A) 2 * finiteGreen (-coneMinus P C) 2 *
        finiteGreen (conePlus P A) 2 ∧
    plabicBoundaryOp P A C =
      finiteGreen (conePlus P A) 2 * finiteGreen (-coneMinus P C) 2 * P *
        finiteGreen (coneMinus P C) 2 * finiteGreen (-conePlus P A) 2 ∧
    plabicBoundaryOp P A C * plabicBoundaryOp P A C = plabicBoundaryOp P A C ∧
    P₀ * P₀ = P₀ ∧
    twoNodeDAG = coneMinus P₀ twoNodeDAG ∧
    finiteGreen twoNodeDAG 2 = plabicBlackShear P₀ (-twoNodeDAG) ∧
    finiteGreen twoNodeDAG 2 * plabicBlackShear P₀ twoNodeDAG = 1 ∧
    plabicBlackShear P₀ twoNodeDAG * finiteGreen twoNodeDAG 2 = 1 := by
  dsimp only
  have hWhite : finiteGreen (conePlus P A) 2 = plabicWhiteShear P A := by
    rw [finiteGreen_two]; rfl
  have hWhiteInv : finiteGreen (-conePlus P A) 2 = 1 - conePlus P A := by
    rw [finiteGreen_two, sub_eq_add_neg]
  have hBlack : finiteGreen (-coneMinus P C) 2 = plabicBlackShear P C := by
    rw [finiteGreen_two]; unfold plabicBlackShear; rw [sub_eq_add_neg]
  have hBlackInv : finiteGreen (coneMinus P C) 2 = 1 + coneMinus P C :=
    finiteGreen_two (coneMinus P C)
  have hW_mul_inv :
      finiteGreen (conePlus P A) 2 * finiteGreen (-conePlus P A) 2 = 1 := by
    rw [hWhite, hWhiteInv]; unfold plabicWhiteShear; peirce_nf hP
  have hInv_mul_W :
      finiteGreen (-conePlus P A) 2 * finiteGreen (conePlus P A) 2 = 1 := by
    rw [hWhite, hWhiteInv]; unfold plabicWhiteShear; peirce_nf hP
  have hB_mul_inv :
      finiteGreen (-coneMinus P C) 2 * finiteGreen (coneMinus P C) 2 = 1 := by
    rw [hBlack, hBlackInv]; unfold plabicBlackShear; peirce_nf hP
  have hInv_mul_B :
      finiteGreen (coneMinus P C) 2 * finiteGreen (-coneMinus P C) 2 = 1 := by
    rw [hBlack, hBlackInv]; unfold plabicBlackShear; peirce_nf hP
  have hTripWB :
      plabicTripWB P A C =
        finiteGreen (conePlus P A) 2 * finiteGreen (-coneMinus P C) 2 := by
    rw [hWhite, hBlack]; rfl
  have hTripBW :
      plabicTripBW P A C =
        finiteGreen (-coneMinus P C) 2 * finiteGreen (conePlus P A) 2 := by
    rw [hWhite, hBlack]; rfl
  have hConjP :
      conjPlus P A X =
        finiteGreen (conePlus P A) 2 * X * finiteGreen (-conePlus P A) 2 := by
    rw [hWhite, hWhiteInv]; rfl
  have hConjM :
      conjMinus P C X =
        finiteGreen (coneMinus P C) 2 * X * finiteGreen (-coneMinus P C) 2 := by
    rw [hBlackInv, hBlack]; rfl
  have hBraid :
      steinbergBraid P A C =
        finiteGreen (conePlus P A) 2 * finiteGreen (-coneMinus P C) 2 *
          finiteGreen (conePlus P A) 2 := by
    rw [hWhite, hBlack]; rfl
  have hBoundaryDAG :
      plabicBoundaryOp P A C =
        finiteGreen (conePlus P A) 2 * finiteGreen (-coneMinus P C) 2 * P *
          finiteGreen (coneMinus P C) 2 * finiteGreen (-conePlus P A) 2 := by
    rw [hWhite, hBlack, hBlackInv, hWhiteInv]
    rfl
  have hBoundaryIdem :
      plabicBoundaryOp P A C * plabicBoundaryOp P A C = plabicBoundaryOp P A C := by
    unfold plabicBoundaryOp
    peirce_nf hP
  have hP0 : twoNodeSheetProj * twoNodeSheetProj = twoNodeSheetProj := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twoNodeSheetProj]
  have hTwoNode : twoNodeDAG = coneMinus twoNodeSheetProj twoNodeDAG := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twoNodeDAG, coneMinus, twoNodeSheetProj,
        Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two]
  have hTwoNodeShear :
      finiteGreen twoNodeDAG 2 =
        plabicBlackShear twoNodeSheetProj (-twoNodeDAG) := by
    rw [finiteGreen_two]
    unfold plabicBlackShear
    have hNeg :
        coneMinus twoNodeSheetProj (-twoNodeDAG) = -twoNodeDAG := by
      calc
        coneMinus twoNodeSheetProj (-twoNodeDAG) =
          -coneMinus twoNodeSheetProj twoNodeDAG := by
          unfold coneMinus; noncomm_ring
        _ = -twoNodeDAG := by rw [← hTwoNode]
    rw [hNeg, sub_neg_eq_add]
  have hTwoNodeInvR :
      finiteGreen twoNodeDAG 2 *
        plabicBlackShear twoNodeSheetProj twoNodeDAG = 1 := by
    have hShearEq : plabicBlackShear twoNodeSheetProj twoNodeDAG = 1 - twoNodeDAG := by
      unfold plabicBlackShear
      rw [← hTwoNode]
    rw [hShearEq]
    exact twoNodeDAG_green_right
  have hTwoNodeInvL :
      plabicBlackShear twoNodeSheetProj twoNodeDAG *
        finiteGreen twoNodeDAG 2 = 1 := by
    have hShearEq : plabicBlackShear twoNodeSheetProj twoNodeDAG = 1 - twoNodeDAG := by
      unfold plabicBlackShear
      rw [← hTwoNode]
    rw [hShearEq]
    exact twoNodeDAG_green_left
  exact ⟨hWhite, hWhiteInv, hW_mul_inv, hInv_mul_W, hBlack, hBlackInv,
    hB_mul_inv, hInv_mul_B, hTripWB, hTripBW, hConjP, hConjM, hBraid,
    hBoundaryDAG, hBoundaryIdem, hP0, hTwoNode, hTwoNodeShear, hTwoNodeInvR, hTwoNodeInvL⟩

/-- Finite-stage Fock grade involution promoted to a linear endomorphism in
`Module.End ℝ (FockStage n)`. -/
noncomputable def fockStageInvoluteEnd (n : ℕ) : Module.End ℝ (FockStage n) :=
  CliffordAlgebra.involute.toLinearMap

/-- Finite-stage Fock chiral projector promoted to an element of the associative operator
ring `Module.End ℝ (FockStage n)` (`P_n = (1 / 2) • (1 + fockStageInvoluteEnd n)`). -/
noncomputable def fockStageChiralIdempotent (n : ℕ) : Module.End ℝ (FockStage n) :=
  (1 / 2 : ℝ) • (LinearMap.id + fockStageInvoluteEnd n)

/-- Infinite-stage Fock chiral projector promoted to an element of the associative operator
ring `Module.End ℝ FockInfinity` (`P_∞ = (1 / 2) • (1 + fockInfinityInvolute)`). -/
noncomputable def fockChiralIdempotent : Module.End ℝ FockInfinity :=
  (1 / 2 : ℝ) • (LinearMap.id + fockInfinityInvolute)

/-- **Theorem 9.2 (`fock_chiral_projector_peirce_operator_ring_intertwining_bridge`)**:
Soldering and intertwining bridge between the finite/infinite Fock chiral projectors
(`ClNNFockChiralProjectorClosure.lean`) and the Peirce operator ring in
`Module.End ℝ (FockStage n)` and `Module.End ℝ FockInfinity`:
1. **Operator-Ring Idempotence & Complementary Sheet Identification:**
   - `fockStageChiralIdempotent n * fockStageChiralIdempotent n = fockStageChiralIdempotent n`,
   - `fockChiralIdempotent * fockChiralIdempotent = fockChiralIdempotent`,
   - `(fockStageChiralIdempotent n) ψ = (1 / 2 : ℝ) • (ψ + CliffordAlgebra.involute ψ)`,
   - `(1 - fockStageChiralIdempotent n) ψ = (1 / 2 : ℝ) • (ψ - CliffordAlgebra.involute ψ)`,
   - `fockChiralIdempotent Ψ = fockInfinityProjectorPlus Ψ`,
   - `(1 - fockChiralIdempotent) Ψ = fockInfinityProjectorMinus Ψ`;
2. **Peirce Reflection `invS` Recovers the Canonical Fock Grading Involution:**
   - `invS (fockStageChiralIdempotent n) = fockStageInvoluteEnd n` and
     `invS (fockStageChiralIdempotent n) * invS (fockStageChiralIdempotent n) = 1`,
   - `invS fockChiralIdempotent = fockInfinityInvolute` and
     `invS fockChiralIdempotent * invS fockChiralIdempotent = 1`;
3. **Stage-to-Stage & Stage-to-`FockInfinity` Intertwining of the Peirce–Plabic Sheet Decomposition:**
   For every `h : n ≤ m` and `ψ : FockStage n`:
   - `fockStageMap n m h ((fockStageChiralIdempotent n) ψ) = (fockStageChiralIdempotent m) (fockStageMap n m h ψ)`,
   - `fockStageMap n m h ((1 - fockStageChiralIdempotent n) ψ) = (1 - fockStageChiralIdempotent m) (fockStageMap n m h ψ)`,
   - `fockStageMap n m h ((invS (fockStageChiralIdempotent n)) ψ) = (invS (fockStageChiralIdempotent m)) (fockStageMap n m h ψ)`,
   - `fockToInfinity n ((fockStageChiralIdempotent n) ψ) = fockChiralIdempotent (fockToInfinity n ψ)`,
   - `fockToInfinity n ((1 - fockStageChiralIdempotent n) ψ) = (1 - fockChiralIdempotent) (fockToInfinity n ψ)`,
   - `fockToInfinity n ((invS (fockStageChiralIdempotent n)) ψ) = (invS fockChiralIdempotent) (fockToInfinity n ψ)`. -/
theorem fock_chiral_projector_peirce_operator_ring_intertwining_bridge
    {n m : ℕ} (h : n ≤ m) (ψ : FockStage n) (Ψ : FockInfinity) :
    let P_n := fockStageChiralIdempotent n
    let P_m := fockStageChiralIdempotent m
    let P_inf := fockChiralIdempotent
    P_n * P_n = P_n ∧
    P_inf * P_inf = P_inf ∧
    P_n ψ = (1 / 2 : ℝ) • (ψ + CliffordAlgebra.involute ψ) ∧
    (1 - P_n) ψ = (1 / 2 : ℝ) • (ψ - CliffordAlgebra.involute ψ) ∧
    P_inf Ψ = fockInfinityProjectorPlus Ψ ∧
    (1 - P_inf) Ψ = fockInfinityProjectorMinus Ψ ∧
    invS P_n = fockStageInvoluteEnd n ∧
    invS P_n * invS P_n = 1 ∧
    invS P_inf = fockInfinityInvolute ∧
    invS P_inf * invS P_inf = 1 ∧
    fockStageMap n m h (P_n ψ) = P_m (fockStageMap n m h ψ) ∧
    fockStageMap n m h ((1 - P_n) ψ) = (1 - P_m) (fockStageMap n m h ψ) ∧
    fockStageMap n m h ((invS P_n) ψ) = (invS P_m) (fockStageMap n m h ψ) ∧
    fockToInfinity n (P_n ψ) = P_inf (fockToInfinity n ψ) ∧
    fockToInfinity n ((1 - P_n) ψ) = (1 - P_inf) (fockToInfinity n ψ) ∧
    fockToInfinity n ((invS P_n) ψ) = (invS P_inf) (fockToInfinity n ψ) := by
  dsimp only
  have hApplyPlusStage : ∀ (k : ℕ) (φ : FockStage k),
      fockStageChiralIdempotent k φ = (1 / 2 : ℝ) • (φ + CliffordAlgebra.involute φ) := by
    intro k φ
    rfl
  have hApplyMinusStage : ∀ (k : ℕ) (φ : FockStage k),
      (1 - fockStageChiralIdempotent k) φ =
        (1 / 2 : ℝ) • (φ - CliffordAlgebra.involute φ) := by
    intro k φ
    have h1 : (1 - fockStageChiralIdempotent k) φ = φ - fockStageChiralIdempotent k φ := rfl
    rw [h1, hApplyPlusStage]
    module
  have hApplyPlusInf : ∀ Φ : FockInfinity,
      fockChiralIdempotent Φ = fockInfinityProjectorPlus Φ := fun _ => rfl
  have hApplyMinusInf : ∀ Φ : FockInfinity,
      (1 - fockChiralIdempotent) Φ = fockInfinityProjectorMinus Φ := by
    intro Φ
    have h1 : (1 - fockChiralIdempotent) Φ = Φ - fockChiralIdempotent Φ := rfl
    rw [h1, hApplyPlusInf]
    unfold fockInfinityProjectorPlus fockInfinityProjectorMinus
    module
  have hPnIdem : fockStageChiralIdempotent n * fockStageChiralIdempotent n =
      fockStageChiralIdempotent n := by
    apply LinearMap.ext
    intro φ
    change fockStageChiralIdempotent n (fockStageChiralIdempotent n φ) =
      fockStageChiralIdempotent n φ
    rw [hApplyPlusStage, hApplyPlusStage]
    simp only [map_smul, map_add]
    rw [CliffordAlgebra.involute_involutive φ]
    module
  have hPinfIdem : fockChiralIdempotent * fockChiralIdempotent = fockChiralIdempotent := by
    apply LinearMap.ext
    intro Φ
    change fockChiralIdempotent (fockChiralIdempotent Φ) = fockChiralIdempotent Φ
    rw [hApplyPlusInf, hApplyPlusInf, fockInfinityProjectorPlus_idempotent]
  have hInvStage : ∀ k : ℕ,
      invS (fockStageChiralIdempotent k) = fockStageInvoluteEnd k := by
    intro k
    apply LinearMap.ext
    intro φ
    have hInvApply :
        (invS (fockStageChiralIdempotent k)) φ =
          fockStageChiralIdempotent k φ - (1 - fockStageChiralIdempotent k) φ := rfl
    rw [hInvApply, hApplyPlusStage, hApplyMinusStage]
    change (1 / 2 : ℝ) • (φ + fockStageInvoluteEnd k φ) -
        (1 / 2 : ℝ) • (φ - fockStageInvoluteEnd k φ) =
      fockStageInvoluteEnd k φ
    module
  have hInvSn : invS (fockStageChiralIdempotent n) = fockStageInvoluteEnd n :=
    hInvStage n
  have hInvSnSq :
      invS (fockStageChiralIdempotent n) * invS (fockStageChiralIdempotent n) = 1 := by
    peirce_nf hPnIdem
  have hInvSinf : invS fockChiralIdempotent = fockInfinityInvolute := by
    apply LinearMap.ext
    intro Φ
    have hInvApply :
        (invS fockChiralIdempotent) Φ =
          fockChiralIdempotent Φ - (1 - fockChiralIdempotent) Φ := rfl
    rw [hInvApply, hApplyPlusInf, hApplyMinusInf, fockInfinityProjectorPlus_sub_minus]
  have hInvSinfSq :
      invS fockChiralIdempotent * invS fockChiralIdempotent = 1 := by
    peirce_nf hPinfIdem
  have hStagePlus :
      fockStageMap n m h (fockStageChiralIdempotent n ψ) =
        fockStageChiralIdempotent m (fockStageMap n m h ψ) := by
    rw [hApplyPlusStage, hApplyPlusStage, fockStageMap_projectorPlus]
  have hStageMinus :
      fockStageMap n m h ((1 - fockStageChiralIdempotent n) ψ) =
        (1 - fockStageChiralIdempotent m) (fockStageMap n m h ψ) := by
    rw [hApplyMinusStage, hApplyMinusStage, fockStageMap_projectorMinus]
  have hStageInvS :
      fockStageMap n m h ((invS (fockStageChiralIdempotent n)) ψ) =
        (invS (fockStageChiralIdempotent m)) (fockStageMap n m h ψ) := by
    rw [hInvStage n, hInvStage m]
    exact (fockStageMap_involute n m h ψ).symm
  have hToInfLin : ∀ (c : ℝ) (x : FockStage n),
      fockToInfinity n (c • x) = c • fockToInfinity n x :=
    fun c x => (DirectLimit.Module.of ℝ ℕ FockStage (fun i j hij => fockStageMap i j hij) n).map_smul c x
  have hToInfAdd : ∀ (x y : FockStage n),
      fockToInfinity n (x + y) = fockToInfinity n x + fockToInfinity n y :=
    fun x y => (DirectLimit.Module.of ℝ ℕ FockStage (fun i j hij => fockStageMap i j hij) n).map_add x y
  have hToInfSub : ∀ (x y : FockStage n),
      fockToInfinity n (x - y) = fockToInfinity n x - fockToInfinity n y :=
    fun x y => (DirectLimit.Module.of ℝ ℕ FockStage (fun i j hij => fockStageMap i j hij) n).map_sub x y
  have hInfPlus :
      fockToInfinity n (fockStageChiralIdempotent n ψ) =
        fockChiralIdempotent (fockToInfinity n ψ) := by
    rw [hApplyPlusStage, hApplyPlusInf]
    unfold fockInfinityProjectorPlus
    rw [hToInfLin, hToInfAdd, fockInfinityInvolute_ofStage]
  have hInfMinus :
      fockToInfinity n ((1 - fockStageChiralIdempotent n) ψ) =
        (1 - fockChiralIdempotent) (fockToInfinity n ψ) := by
    rw [hApplyMinusStage, hApplyMinusInf]
    unfold fockInfinityProjectorMinus
    rw [hToInfLin, hToInfSub, fockInfinityInvolute_ofStage]
  have hInfInvS :
      fockToInfinity n ((invS (fockStageChiralIdempotent n)) ψ) =
        (invS fockChiralIdempotent) (fockToInfinity n ψ) := by
    rw [hInvStage n, hInvSinf]
    exact (fockInfinityInvolute_ofStage n ψ).symm
  exact ⟨hPnIdem, hPinfIdem, hApplyPlusStage n ψ, hApplyMinusStage n ψ,
    hApplyPlusInf Ψ, hApplyMinusInf Ψ, hInvSn, hInvSnSq, hInvSinf, hInvSinfSq,
    hStagePlus, hStageMinus, hStageInvS, hInfPlus, hInfMinus, hInfInvS⟩

/-- Explicit ring equivalence `Matrix (Fin 4) (Fin 4) ℂ ≃+* Module.End ℂ Twistor4`
whose underlying map is definitionally `transportTwistorMatrix`
(`PenroseTwistorOperatorBridge.lean`). -/
noncomputable def transportTwistorRingEquiv :
    Matrix (Fin 4) (Fin 4) ℂ ≃+* Module.End ℂ Twistor4 where
  toFun := transportTwistorMatrix
  invFun f :=
    Matrix.toLin'.symm
      ((penroseTwistor4CarrierEquiv.toLinearMap.comp f).comp
        penroseTwistor4CarrierEquiv.symm.toLinearMap)
  left_inv M := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro z
    unfold transportTwistorMatrix
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  right_inv f := by
    apply LinearMap.ext
    intro p
    unfold transportTwistorMatrix
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  map_mul' A B := by
    apply LinearMap.ext
    intro p
    change transportTwistorMatrix (A * B) p =
      transportTwistorMatrix A (transportTwistorMatrix B p)
    unfold transportTwistorMatrix
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      Matrix.toLin'_mul, LinearEquiv.apply_symm_apply]
  map_add' A B := by
    apply LinearMap.ext
    intro p
    change transportTwistorMatrix (A + B) p =
      transportTwistorMatrix A p + transportTwistorMatrix B p
    unfold transportTwistorMatrix
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      map_add, LinearMap.add_apply]

/-- Positive-helicity twistor sheet projector `P_tw : Matrix (Fin 4) (Fin 4) ℂ`
projecting onto coordinates `(0, 1)`. -/
def twistorSheetProj : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Pseudo-Hermitian `SU(2, 2)` twistor metric matrix `diag(1, 1, -1, -1)`. -/
def twistorMetricDiag : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Endpoint Peirce projector `P_end = E₀₀ : Matrix (Fin 4) (Fin 4) ℂ` selecting the
initial coordinate `0` of the 4-step Penrose shift ladder. -/
def twistorEndpointProj : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Upper endpoint corner `E₀₃ : Matrix (Fin 4) (Fin 4) ℂ`. -/
def twistorEndpointPlus : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Lower endpoint corner `E₃₀ : Matrix (Fin 4) (Fin 4) ℂ`. -/
def twistorEndpointMinus : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     1, 0, 0, 0]

/-- Explicit non-commutativity witness on `Matrix (Fin 4) (Fin 4) ℂ` between the endpoint
Peirce projector `twistorEndpointProj` and the upper corner `twistorEndpointPlus`. -/
theorem twistorEndpointProj_mul_twistorEndpointPlus_ne :
    twistorEndpointProj * twistorEndpointPlus ≠ twistorEndpointPlus * twistorEndpointProj := by
  intro hEq
  have h03 : (1 : ℂ) = 0 := by
    simpa [twistorEndpointProj, twistorEndpointPlus] using
      congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 3) hEq
  exact one_ne_zero h03

/-- Explicit non-commutativity witness for the finite twistor coordinate and derivative
matrices (`twistorCoordinate * twistorDerivative ≠ twistorDerivative * twistorCoordinate`). -/
theorem twistorCoordinate_mul_twistorDerivative_ne :
    twistorCoordinate * twistorDerivative ≠ twistorDerivative * twistorCoordinate := by
  intro hEq
  have hCommZero : commutator twistorCoordinate twistorDerivative = 0 :=
    sub_eq_zero.mpr hEq
  rw [finite_twistor_commutator] at hCommZero
  have h00 : (1 : ℂ) = 0 := by
    simpa using congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) hCommZero
  exact one_ne_zero h00

/-- **Theorem 9.3 (`penrose_twistor_splitCl44_and_firstQuantized_peirce_soldering_bridge`)**:
Complete carrier soldering and operator-ring isomorphism connecting:
- the Penrose twistor space `TwistorCarrier = Fin 4 → ℂ` and the split `Cl(4, 4)`
  quadratic space `SplitCl44Carrier` (`SplitCl44CausalEnvelope.lean`), and
- the Penrose first-quantized operators `firstQuantizedCoordinate`,
  `firstQuantizedDerivative`, `firstQuantizedBoundary` (`PenroseTwistorOperatorBridge.lean`),
  the Peirce–Plabic operator ring, and the finite DAG resolvent `finiteGreen`:
1. **Soldering `TwistorCarrier ≃ₗ[ℝ] SplitCl44Carrier` & Exact Helicity–Quadratic Isometry:**
   - `SplitCl44Quad (penroseTwistorToSplitCl44Equiv z) = helicity z`,
   - `PenroseTwistorHasSplitCl44NullModel` holds unconditionally (`penroseTwistorHasSplitCl44NullModel`);
2. **Ring Isomorphism `transportTwistorRingEquiv : Matrix (Fin 4) (Fin 4) ℂ ≃+* Module.End ℂ Twistor4` & Sheet Grading:**
   - `twistorSheetProj * twistorSheetProj = twistorSheetProj`,
   - `invS twistorSheetProj = twistorMetricDiag`, so the `SU(2, 2)` pseudo-Hermitian
     twistor metric matrix is literally the Peirce sheet reflection `invS twistorSheetProj`;
3. **Peirce Chiral Bivector `genSig` = Penrose Boundary Anomaly `[X, D]`:**
   - `twistorEndpointProj * twistorEndpointProj = twistorEndpointProj`,
   - `genSig twistorEndpointProj twistorEndpointPlus twistorEndpointMinus =
        commutator twistorCoordinate twistorDerivative`,
   - `twistorCoordinate * twistorDerivative ≠ twistorDerivative * twistorCoordinate`,
   - Under `transportTwistorRingEquiv`, the Peirce chiral bivector maps to the Penrose
     first-quantized boundary anomaly:
     `transportTwistorRingEquiv (genSig twistorEndpointProj twistorEndpointPlus twistorEndpointMinus) =
        firstQuantizedBoundary =
        firstQuantizedCoordinate * firstQuantizedDerivative -
          firstQuantizedDerivative * firstQuantizedCoordinate`;
4. **4-Step Nilpotent DAG Resolvents of First-Quantized Twistor Operators:**
   - `firstQuantizedCoordinate ^ 4 = 0` and `firstQuantizedDerivative ^ 4 = 0`,
   - `(1 - firstQuantizedCoordinate) * finiteGreen firstQuantizedCoordinate 4 = 1` and
     `finiteGreen firstQuantizedCoordinate 4 * (1 - firstQuantizedCoordinate) = 1`,
   - `(1 - firstQuantizedDerivative) * finiteGreen firstQuantizedDerivative 4 = 1` and
     `finiteGreen firstQuantizedDerivative 4 * (1 - firstQuantizedDerivative) = 1`. -/
theorem penrose_twistor_splitCl44_and_firstQuantized_peirce_soldering_bridge
    (z : TwistorCarrier) :
    SplitCl44Quad (penroseTwistorToSplitCl44Equiv z) = helicity z ∧
    PenroseTwistorHasSplitCl44NullModel ∧
    twistorSheetProj * twistorSheetProj = twistorSheetProj ∧
    invS twistorSheetProj = twistorMetricDiag ∧
    twistorEndpointProj * twistorEndpointProj = twistorEndpointProj ∧
    genSig twistorEndpointProj twistorEndpointPlus twistorEndpointMinus =
      commutator twistorCoordinate twistorDerivative ∧
    twistorCoordinate * twistorDerivative ≠ twistorDerivative * twistorCoordinate ∧
    transportTwistorRingEquiv
        (genSig twistorEndpointProj twistorEndpointPlus twistorEndpointMinus) =
      firstQuantizedBoundary ∧
    firstQuantizedBoundary =
      firstQuantizedCoordinate * firstQuantizedDerivative -
        firstQuantizedDerivative * firstQuantizedCoordinate ∧
    firstQuantizedCoordinate ^ 4 = 0 ∧
    firstQuantizedDerivative ^ 4 = 0 ∧
    (1 - firstQuantizedCoordinate) * finiteGreen firstQuantizedCoordinate 4 = 1 ∧
    finiteGreen firstQuantizedCoordinate 4 * (1 - firstQuantizedCoordinate) = 1 ∧
    (1 - firstQuantizedDerivative) * finiteGreen firstQuantizedDerivative 4 = 1 ∧
    finiteGreen firstQuantizedDerivative 4 * (1 - firstQuantizedDerivative) = 1 := by
  have hQuad : SplitCl44Quad (penroseTwistorToSplitCl44Equiv z) = helicity z :=
    penroseTwistorToSplitCl44Equiv_quad z
  have hNullModel : PenroseTwistorHasSplitCl44NullModel :=
    penroseTwistorHasSplitCl44NullModel
  have hSheetIdem : twistorSheetProj * twistorSheetProj = twistorSheetProj := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twistorSheetProj]
  have hSheetInvS : invS twistorSheetProj = twistorMetricDiag := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [invS, twistorSheetProj, twistorMetricDiag]
  have hEndIdem : twistorEndpointProj * twistorEndpointProj = twistorEndpointProj := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twistorEndpointProj]
  have hPlusCorner :
      conePlus twistorEndpointProj twistorEndpointPlus = twistorEndpointPlus := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conePlus, twistorEndpointProj, twistorEndpointPlus,
        Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_four]
  have hMinusCorner :
      coneMinus twistorEndpointProj twistorEndpointMinus = twistorEndpointMinus := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coneMinus, twistorEndpointProj, twistorEndpointMinus,
        Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_four]
  have hGenSigComm :
      genSig twistorEndpointProj twistorEndpointPlus twistorEndpointMinus =
        commutator twistorCoordinate twistorDerivative := by
    unfold genSig
    rw [hPlusCorner, hMinusCorner, finite_twistor_commutator]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
        twistorEndpointPlus, twistorEndpointMinus]
  have hTransportGenSig :
      transportTwistorRingEquiv
          (genSig twistorEndpointProj twistorEndpointPlus twistorEndpointMinus) =
        firstQuantizedBoundary := by
    rw [hGenSigComm, finite_twistor_commutator]
    rfl
  have hBoundaryComm :
      firstQuantizedBoundary =
        firstQuantizedCoordinate * firstQuantizedDerivative -
          firstQuantizedDerivative * firstQuantizedCoordinate :=
    firstQuantized_commutator_eq_boundary.symm
  have hMatCoord4 : twistorCoordinate ^ 4 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twistorCoordinate, pow_succ, pow_zero]
  have hMatDeriv4 : twistorDerivative ^ 4 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twistorDerivative, pow_succ, pow_zero]
  have hCoord4 : firstQuantizedCoordinate ^ 4 = 0 := by
    change (transportTwistorRingEquiv twistorCoordinate) ^ 4 = 0
    rw [← map_pow, hMatCoord4, map_zero]
  have hDeriv4 : firstQuantizedDerivative ^ 4 = 0 := by
    change (transportTwistorRingEquiv twistorDerivative) ^ 4 = 0
    rw [← map_pow, hMatDeriv4, map_zero]
  exact ⟨hQuad, hNullModel, hSheetIdem, hSheetInvS, hEndIdem,
    hGenSigComm, twistorCoordinate_mul_twistorDerivative_ne,
    hTransportGenSig, hBoundaryComm, hCoord4, hDeriv4,
    finiteGreen_left_inverse firstQuantizedCoordinate 4 hCoord4,
    finiteGreen_right_inverse firstQuantizedCoordinate 4 hCoord4,
    finiteGreen_left_inverse firstQuantizedDerivative 4 hDeriv4,
    finiteGreen_right_inverse firstQuantizedDerivative 4 hDeriv4⟩

/-!
## 10. Master Causal Poset Synthesis of the Deconfabulated Operator Stream (`P₁ ≼ P₂ ≼ ⋯ ≼ P₁₂`)

Unifies the entire causal poset of extracted non-commutative operator archetypes across an
arbitrary associative unital ring `[Ring B]` with idempotent `P` (`P * P = P`) and the
concrete non-commutative matrix/operator carriers:
1. **`P₁ → P₂` (Witt Null Cones & 4-Fold Clifford–Peirce Tetraktys `Λ^• ≅ Cl_{1,1}`):**
   - `conePlus P A * conePlus P A = 0`, `coneMinus P C * coneMinus P C = 0`,
   - `genPhi P A C * genPhi P A C = genV P A C`, `genJ P A C * genJ P A C = -genV P A C`,
   - `anticomm (genPhi P A C) (genJ P A C) = 0`, `genJ P A C * genPhi P A C = genSig P A C`;
2. **`P₃` (Chiral Euler/Dirichlet–Möbius Factorizations, Corrected Mangoldt Product, & Primal-Dual Chord Potentials):**
   - `(1 - qgtPlus P A C) * (1 - qgtMinus P A C) = zetaFactor P A C`,
   - `(1 + qgtPlus P A C) * (1 + qgtMinus P A C) = zetaPlusFactor P A C`,
   - `(1 - qgtPlus P A C) * (1 + qgtMinus P A C) = chiralFactor P A C`,
   - `(1 + qgtPlus P A C) * (1 - qgtMinus P A C) = chiralConjugateFactor P A C`,
   - `chiralFactor P A C * chiralConjugateFactor P A C = 1 - genV P A C * genV P A C`,
   - `(1 - genPhi P A C) * (1 - genJ P A C) * (1 + genJ P A C) * (1 + genPhi P A C) = 1 - genV P A C * genV P A C`,
   - `(1 - genSig P A C) * (genSig P A C + genV P A C * genSig P A C) = (1 + genV P A C) * (genSig P A C - genV P A C * genV P A C)`,
   - `(P - conjPlus P A P) * (conjMinus P C P - P) = qgtPlus P A C` and
     `(conjMinus P C P - P) * (P - conjPlus P A P) = qgtMinus P A C`;
3. **`P₄ → P₅` (Mandelbrot Defect Tower `δ^[n]`, Fourier Sandwich Projectors, & Conditional `V = 1` Klein Action):**
   - `idempotencyDefect (-genPhi P A C) * idempotencyDefect (genPhi P A C) = idempotencyDefect (genV P A C)`,
   - `idempotencyDefect^[n] (genV P A C) = idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C)`,
   - `fourierV P A C X + fourierPhi P A C X + fourierJ P A C X + fourierSig P A C X = (8 : ℤ) • ((genV P A C * genV P A C) * X)`;
4. **`P₆ → P₈` (Operator Cyclotomic Characteristic Polynomials, All-`m` Polygon & Eisenstein Linearization, & Covariant Bianchi Flatness):**
   - `opCharPolyPhi6 P A C (peirceTransferJ P A C) = 0`,
   - `opCharPolyPhi3 P A C (cubeRootOp P A C) = 0`,
   - `opCharPolyTransfer P A C (peirceTransfer P A C) = 0`,
   - `(peirceTransfer P A C) ^ (m + 1) = polygonFibSeq P A C (m + 1) * peirceTransfer P A C + genV P A C * polygonFibSeq P A C m`,
   - `(peirceTransferJ P A C) ^ (m + 1) = eisensteinSeq P A C (m + 1) * peirceTransferJ P A C - genV P A C * eisensteinSeq P A C m`,
   - `peirceCovariantDeriv P A C (polygonFibSeq P A C m) = 0` and
     `peirceCovariantDeriv P A C (eisensteinSeq P A C m) = 0`;
5. **`P₉ → P₁₂` (Cross-Carrier Soldering: DAG Neumann Resolvent, Fock Chiral Projector, Penrose Twistor First-Quantized Anomaly, & Split `Cl(4, 4)` Isometry):**
   - `(1 - twoNodeDAG) * finiteGreen twoNodeDAG 2 = 1`,
   - `fockChiralIdempotent * fockChiralIdempotent = fockChiralIdempotent`,
   - `SplitCl44Quad (penroseTwistorToSplitCl44Equiv z) = helicity z`,
   - `transportTwistorRingEquiv (genSig twistorEndpointProj twistorEndpointPlus twistorEndpointMinus) = firstQuantizedBoundary`.
-/

/-- **Theorem 10.1 (`deconfabulated_causal_poset_master_synthesis`)**:
Complete kernel-checked synthesis of the 12-stage causal poset (`P₁ ≼ P₂ ≼ ⋯ ≼ P₁₂`)
extracted from the raw stream of consciousness over an arbitrary non-commutative ring
`[Ring B]` (`P * P = P`), including non-commutative 3-colour Levi-Civita cross-commutator
and Zorn split-octonion structure constants (`ThreeColorOperatorCrossCommutator`), and
soldered across the DAG, Fock, Penrose twistor, and split `Cl(4, 4)` operator carriers. -/
theorem deconfabulated_causal_poset_master_synthesis
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B)
    (U V_vec : InfoGeometry.Canonical.OperatorVector B)
    (n m : ℕ) (z : TwistorCarrier) :
    -- P₁ → P₂: Nilpotent Witt cones & 4-fold Clifford–Peirce Tetraktys
    (conePlus P A * conePlus P A = 0 ∧
     coneMinus P C * coneMinus P C = 0 ∧
     genPhi P A C * genPhi P A C = genV P A C ∧
     genJ P A C * genJ P A C = -genV P A C ∧
     anticomm (genPhi P A C) (genJ P A C) = 0 ∧
     genJ P A C * genPhi P A C = genSig P A C) ∧
    -- P₃: Chiral Euler/Dirichlet–Möbius factorizations, corrected Mangoldt product, & primal-dual chord potentials
    ((1 - qgtPlus P A C) * (1 - qgtMinus P A C) = zetaFactor P A C ∧
     (1 + qgtPlus P A C) * (1 + qgtMinus P A C) = zetaPlusFactor P A C ∧
     (1 - qgtPlus P A C) * (1 + qgtMinus P A C) = chiralFactor P A C ∧
     (1 + qgtPlus P A C) * (1 - qgtMinus P A C) = chiralConjugateFactor P A C ∧
     chiralFactor P A C * chiralConjugateFactor P A C = 1 - genV P A C * genV P A C ∧
     (1 - genPhi P A C) * (1 - genJ P A C) * (1 + genJ P A C) * (1 + genPhi P A C) =
       1 - genV P A C * genV P A C ∧
     (1 - genSig P A C) * (genSig P A C + genV P A C * genSig P A C) =
       (1 + genV P A C) * (genSig P A C - genV P A C * genV P A C) ∧
     (P - conjPlus P A P) * (conjMinus P C P - P) = qgtPlus P A C ∧
     (conjMinus P C P - P) * (P - conjPlus P A P) = qgtMinus P A C) ∧
    -- P₄ → P₅: Mandelbrot defect iteration & Fourier sandwich projector partition
    (idempotencyDefect (-genPhi P A C) * idempotencyDefect (genPhi P A C) =
       idempotencyDefect (genV P A C) ∧
     idempotencyDefect^[n] (genV P A C) =
       idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C) ∧
     fourierV P A C X + fourierPhi P A C X + fourierJ P A C X + fourierSig P A C X =
       (8 : ℤ) • ((genV P A C * genV P A C) * X)) ∧
    -- P₆ → P₈: Non-commutative 3-colour ε_{ijk} / Zorn structure constants, cyclotomic charpolys, Polygon & Eisenstein linearization, & Bianchi flatness
    (InfoGeometry.Canonical.leviCivitaOperatorCross U V_vec =
       InfoGeometry.Canonical.operatorCross U V_vec ∧
     InfoGeometry.Canonical.operatorCross U U 0 = comm (U 1) (U 2) ∧
     InfoGeometry.Canonical.operatorCross U U 1 = comm (U 2) (U 0) ∧
     InfoGeometry.Canonical.operatorCross U U 2 = comm (U 0) (U 1) ∧
     InfoGeometry.Canonical.operatorZornMul
       (InfoGeometry.Canonical.sigmaPlus U) (InfoGeometry.Canonical.sigmaPlus V_vec) =
       InfoGeometry.Canonical.sigmaMinus (InfoGeometry.Canonical.operatorCross U V_vec) ∧
     InfoGeometry.Canonical.operatorZornMul
       (InfoGeometry.Canonical.sigmaMinus U) (InfoGeometry.Canonical.sigmaMinus V_vec) =
       InfoGeometry.Canonical.sigmaPlus (-InfoGeometry.Canonical.operatorCross U V_vec) ∧
     InfoGeometry.Canonical.operatorZornMul
       (InfoGeometry.Canonical.sigmaPlus U) (InfoGeometry.Canonical.sigmaMinus V_vec) =
       InfoGeometry.Canonical.nPlus (InfoGeometry.Canonical.operatorDot U V_vec) ∧
     InfoGeometry.Canonical.operatorZornMul
       (InfoGeometry.Canonical.sigmaMinus U) (InfoGeometry.Canonical.sigmaPlus V_vec) =
       InfoGeometry.Canonical.nMinus (InfoGeometry.Canonical.operatorDot U V_vec) ∧
     opCharPolyPhi6 P A C (peirceTransferJ P A C) = 0 ∧
     opCharPolyPhi3 P A C (cubeRootOp P A C) = 0 ∧
     opCharPolyTransfer P A C (peirceTransfer P A C) = 0 ∧
     (peirceTransfer P A C) ^ (m + 1) =
       polygonFibSeq P A C (m + 1) * peirceTransfer P A C +
         genV P A C * polygonFibSeq P A C m ∧
     (peirceTransferJ P A C) ^ (m + 1) =
       eisensteinSeq P A C (m + 1) * peirceTransferJ P A C -
         genV P A C * eisensteinSeq P A C m ∧
     peirceCovariantDeriv P A C (polygonFibSeq P A C m) = 0 ∧
     peirceCovariantDeriv P A C (eisensteinSeq P A C m) = 0) ∧
    -- P₉ → P₁₂: Cross-carrier soldering (DAG resolvent, Fock chiral projector, Penrose twistor, Split Cl(4,4))
    ((1 - twoNodeDAG) * finiteGreen twoNodeDAG 2 = 1 ∧
     fockChiralIdempotent * fockChiralIdempotent = fockChiralIdempotent ∧
     SplitCl44Quad (penroseTwistorToSplitCl44Equiv z) = helicity z ∧
     transportTwistorRingEquiv
         (genSig twistorEndpointProj twistorEndpointPlus twistorEndpointMinus) =
       firstQuantizedBoundary) := by
  have hTet1 : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have hTet2 : coneMinus P C * coneMinus P C = 0 := by peirce_nf hP
  have hTet3 : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
  have hTet4 : genJ P A C * genJ P A C = -genV P A C := by peirce_nf hP
  have hTet5 : anticomm (genPhi P A C) (genJ P A C) = 0 := by peirce_nf hP
  have hTet6 : genJ P A C * genPhi P A C = genSig P A C := by peirce_nf hP
  have hEuler := chiralEuler_factorizations hP A C
  have hChiralProd := (chiral_factor_product hP A C).2
  have hSuper4 := supercharge_four_factor_product hP A C
  have hMangoldt := chiral_mangoldt_product hP A C
  have hChord := archetype_A42_primal_dual_chord_potentials hP A C
  have hDefProd := (genPhi_defect_product hP A C).1
  have hDefSplit := genV_defect_iterates_cycle_split hP A C n
  have hFourSum :
      fourierV P A C X + fourierPhi P A C X + fourierJ P A C X + fourierSig P A C X =
        (8 : ℤ) • ((genV P A C * genV P A C) * X) := by
    unfold fourierV fourierPhi fourierJ fourierSig grpId
    module
  have hChar6 : opCharPolyPhi6 P A C (peirceTransferJ P A C) = 0 := by
    unfold opCharPolyPhi6 peirceTransferJ; peirce_nf hP
  have hChar3 : opCharPolyPhi3 P A C (cubeRootOp P A C) = 0 := by
    unfold opCharPolyPhi3 cubeRootOp; peirce_nf hP
  have hCharT : opCharPolyTransfer P A C (peirceTransfer P A C) = 0 := by
    unfold opCharPolyTransfer peirceTransfer; peirce_nf hP
  have hPolyPow :=
    (all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence hP A C m).1
  have hEis :=
    all_m_eisenstein_power_linearization_radical_factorization_and_bianchi hP A C m
  have hPolyBianchi :=
    (peirceCovariantDeriv_polygonFibSeq_and_polygonLucasGen_eq_zero hP A C m).2.2.1
  have hFockIdem : fockChiralIdempotent * fockChiralIdempotent = fockChiralIdempotent := by
    apply LinearMap.ext
    intro Φ
    change fockChiralIdempotent (fockChiralIdempotent Φ) = fockChiralIdempotent Φ
    exact fockInfinityProjectorPlus_idempotent Φ
  have hTwistor :=
    penrose_twistor_splitCl44_and_firstQuantized_peirce_soldering_bridge z
  exact ⟨⟨hTet1, hTet2, hTet3, hTet4, hTet5, hTet6⟩,
    ⟨hEuler.1, hEuler.2.1, hEuler.2.2.1, hEuler.2.2.2,
      hChiralProd, hSuper4, hMangoldt, hChord.1, hChord.2.1⟩,
    ⟨hDefProd, hDefSplit, hFourSum⟩,
    ⟨InfoGeometry.Canonical.leviCivitaOperatorCross_eq_operatorCross U V_vec,
      rfl, rfl, rfl,
      InfoGeometry.Canonical.sigmaPlus_mul_sigmaPlus U V_vec,
      InfoGeometry.Canonical.sigmaMinus_mul_sigmaMinus U V_vec,
      InfoGeometry.Canonical.sigmaPlus_mul_sigmaMinus U V_vec,
      InfoGeometry.Canonical.sigmaMinus_mul_sigmaPlus U V_vec,
      hChar6, hChar3, hCharT, hPolyPow, hEis.2.2.1, hPolyBianchi,
      hEis.2.2.2.2.2.2.2.2.2.1⟩,
    ⟨twoNodeDAG_green_left, hFockIdem,
      hTwistor.1, hTwistor.2.2.2.2.2.2.2.1⟩⟩

end FockPenroseSplitCl44AndDAGResolventSolderingBridge

/-!
## 11. Group Structure Constants, 3-Idempotent Gauge Partition, Cuntz $\mathcal{O}_3$ Casimir, and Interaction Scales Synthesis

Unifies the three highest-return moves connecting the repository's **Group Structure
Constants and Interaction Scales** to the **Peirce–Tetraktys–Kantor–Twistor–Colimit Spine**:
1. **Move A (Non-Commutative Zorn Boost Weights $(0, +2, -2, 0)$ & Levi-Civita $\varepsilon_{ijk}$ Self-Cross-Product Lie Commutator Emergence):**
   - Defines `opZornBoostFlow u u_inv X` on `NCZornElement B` over any associative ring `[Ring B]`,
     scaling the scalar Peirce corners by opposite boost conjugations
     (`u * X.n_plus * u_inv`, `u_inv * X.n_minus * u`) and the 3-color off-diagonal vector grades
     by double boost weights (`u * X.sigma_plus i * u`, `u_inv * X.sigma_minus i * u_inv`),
     with exact two-sided inversion when `u * u_inv = 1` and `u_inv * u = 1`;
   - Defines `opZornPureVec u_vec v_vec : NCZornElement B` and proves that in the non-commutative
     Zorn product `Z * Z`, the scalar diagonal grades capture the 3-color inner products
     `zornDot u_vec v_vec` and `zornDot v_vec u_vec` (matching the sum of the three spatial
     Peirce chiral-plane horizon metrics `∑ i : Fin 3, genV peirceSheetProj (zornChiralPlaneMatrix i Z) (zornChiralPlaneMatrix i Z)`),
     while the off-diagonal vector grades do **not** vanish when `B` is non-commutative:
     instead, they equal the exact Levi-Civita $\varepsilon_{ijk}$ operator self-cross-products
     `leviCivitaOperatorCross u_vec u_vec` and `-leviCivitaOperatorCross v_vec v_vec`,
     whose components are the non-abelian Lie commutators `[u_j, u_k]` and `-[v_j, v_k]`.
2. **Move B (3-Idempotent `Cl(5, 5)` Gauge Partition $\mathbb{H}^{3,3} \oplus \mathbb{H}^{1,1} \oplus \mathbb{H}^{1,1}$ ↔ 2-Sheet Peirce Decomposition & $\mathfrak{su}(3) \oplus \mathfrak{su}(2) \oplus \mathfrak{u}(1)$ Structure Constants):**
   - Bridges `Clifford55GaugeSubalgebra.OrthogonalIdempotentSystem B` ($e_1 + e_2 + e_3 = 1$)
     with the 2-sheet Peirce decomposition ($P = e_1$, $1 - P = e_2 + e_3$, `invS e_1 = e_1 - e_2 - e_3`),
     proving that the Peirce involution `invS e_1` acts as $+1$ on the color block $e_1 B e_1$
     and $-1$ on the electroweak blocks $e_2 B e_2 \oplus e_3 B e_3$, while the Peirce off-diagonal
     Witt cones `conePlus e_1 X` and `coneMinus e_1 X` decompose into the color-weak and
     color-hypercharge cross-sheet transition blocks $e_1 X e_2 + e_1 X e_3$ and $e_2 X e_1 + e_3 X e_1$
     and vanish identically whenever `StabilizesIdempotents S X` holds;
   - Combines this partition with the concrete $(6, 2, 2)$ hyperbolic trace signature on
     `Matrix (Fin 10) (Fin 10) ℝ`, the $\mathfrak{su}(3)$ Gell-Mann antisymmetric and symmetric
     structure constants $f_{abc}, d_{abc}$ (`commutator_formula` and `d_normalization`:
     $\sum_{c,e} d_{ace} d_{bce} = \frac{20}{3}\delta_{ab}$), and the electroweak/GUT trace
     normalizations (`SMNormalizedGaugeEmbedding`: $\operatorname{Tr}(T_3^2) = 2$,
     $\operatorname{Tr}(Y^2) = 10/3$, $k_Y = 5/3$, $g_1^2/g_2^2 = 3/5$, $\sin^2\theta_W = 3/8$).
3. **Move C (Cuntz $\mathcal{O}_3$ Quadratic Casimir Identity $C_2 = \frac{8}{3}\cdot 1$ & Mersenne–Tensor-Tower Stage Dimension / Fine-Structure Colimit Bridge):**
   - Proves that in any `[CommRing R] [Invertible (2 : R)] [Invertible (6 : R)]`, for any
     `g : CuntzO3Generators R`, the Cuntz $\mathcal{O}_3$ completeness relation
     $P_1 + P_2 + P_3 = 1$ collapses the $\mathfrak{su}(3)$ quadratic Casimir operator
     `casimir2 g` identically to the central scalar $2 + 4 * ⅟(6 : R) = 16 * ⅟(6 : R)$ ($= 8/3$),
     so `lieBracket (casimir2 g) X = 0` for all $X \in R$;
   - Bridges the Combinatorial Hierarchy / Mersenne numbers `mersenne n = 2^n - 1`
     (`3 + 7 + 127 = 137`) and the Pellis golden-ratio decomposition with the $2^n \times 2^n$
     tensor-tower stage dimensions `Fintype.card (Fin (2^n)) = mersenne n + 1` and
     `Fintype.card (Fin (2^n) × Fin (2^n)) = mersenne (2 * n) + 1`, and the operator Penrose
     Kite/Dart golden-ratio quadratic equation in the inductive colimit `Limit`.
-/

section StructureConstantsAndInteractionScalesSynthesis

open InfoGeometry.Physics.NCG
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge
open InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
open InfoGeometry.Canonical.SMNormalizedGaugeEmbedding
open InfoGeometry.Algebra.Clifford55GaugeSubalgebra
open InfoGeometry.Algebra.StructureConstants
open InfoGeometry.Algebra.CuntzO3TriSupersymmetry
open InfoGeometry.Algebra.CuntzO3LieAlgebraCasimir
open InfoGeometry.Clifford.CliffordTower
open InfoGeometry.Physics.FineStructureDerivation
open PellisFineStructure

/-- Non-commutative Zorn boost conjugation flow on `OperatorZornMatrix B` over an arbitrary
ring `[Ring B]`: generalizes `ZornScalingFlow.diagConj` to non-commutative operator entries
with boost weights `(0, +2, -2, 0)` (conjugation on the scalar Peirce sheets and double
scaling on the 3-color off-diagonal vector grades). -/
def opZornBoostFlow {B : Type*} [Ring B] (u u_inv : B) (X : OperatorZornMatrix B) :
    OperatorZornMatrix B where
  n_plus := u * X.n_plus * u_inv
  n_minus := u_inv * X.n_minus * u
  sigma_plus := fun i => u * X.sigma_plus i * u
  sigma_minus := fun i => u_inv * X.sigma_minus i * u_inv

/-- **Theorem 11.1 (`opZorn_boost_scaling_and_leviCivita_self_cross_commutator_bridge`, Move A)**:
Over any associative unital ring `[Ring B]`:
1. **Non-Commutative Zorn Boost Weights & Exact Inversion:**
   For any `u, u_inv : B` with `u * u_inv = 1` and `u_inv * u = 1`, `opZornBoostFlow u u_inv`
   scales the four Zorn grades by `(u · n_+ · u⁻¹, u · σ_+ · u, u⁻¹ · σ_- · u⁻¹, u⁻¹ · n_- · u)`
   and is inverted on both sides by `opZornBoostFlow u_inv u`;
2. **Pure-Vector Zorn Square = Horizon Metric Sum + Levi-Civita $\varepsilon_{ijk}$ Self-Cross Lie Commutators:**
   For `Z = chiralOperatorZorn u_vec v_vec`, the square `Z * Z` has:
   - scalar Peirce corners `(Z * Z).n_plus = operatorDot u_vec v_vec` and
     `(Z * Z).n_minus = operatorDot v_vec u_vec`, matching the sum of the three spatial
     Peirce chiral-plane horizon metrics
     `∑ i : Fin 3, genV peirceSheetProj (zornChiralPlaneMatrix i Z) (zornChiralPlaneMatrix i Z) = !![(Z * Z).n_plus, 0; 0, (Z * Z).n_minus]`,
   - upper and lower 3-color vector grades equal to the Levi-Civita $\varepsilon_{ijk}$
     operator self-cross-products:
     `(Z * Z).sigma_plus = -leviCivitaOperatorCross v_vec v_vec` and
     `(Z * Z).sigma_minus = leviCivitaOperatorCross u_vec u_vec`,
   - componentwise evaluation of `(Z * Z).sigma_plus` and `(Z * Z).sigma_minus` to the exact
     non-abelian Lie commutators `-comm (v_vec 1) (v_vec 2)`, `-comm (v_vec 2) (v_vec 0)`,
     `-comm (v_vec 0) (v_vec 1)` and `comm (u_vec 1) (u_vec 2)`, `comm (u_vec 2) (u_vec 0)`,
     `comm (u_vec 0) (u_vec 1)`. -/
theorem opZorn_boost_scaling_and_leviCivita_self_cross_commutator_bridge
    {B : Type*} [Ring B]
    {u u_inv : B} (hu : u * u_inv = 1) (hu_inv : u_inv * u = 1)
    (X : OperatorZornMatrix B) (u_vec v_vec : OperatorVector B) :
    let Z := chiralOperatorZorn u_vec v_vec
    (opZornBoostFlow u u_inv X).n_plus = u * X.n_plus * u_inv ∧
    (opZornBoostFlow u u_inv X).n_minus = u_inv * X.n_minus * u ∧
    (∀ i : Fin 3, (opZornBoostFlow u u_inv X).sigma_plus i = u * X.sigma_plus i * u) ∧
    (∀ i : Fin 3, (opZornBoostFlow u u_inv X).sigma_minus i = u_inv * X.sigma_minus i * u_inv) ∧
    opZornBoostFlow u_inv u (opZornBoostFlow u u_inv X) = X ∧
    opZornBoostFlow u u_inv (opZornBoostFlow u_inv u X) = X ∧
    (Z * Z).n_plus = operatorDot u_vec v_vec ∧
    (Z * Z).n_minus = operatorDot v_vec u_vec ∧
    (∑ i : Fin 3,
      genV (peirceSheetProj (A := B))
        (zornChiralPlaneMatrix i Z) (zornChiralPlaneMatrix i Z)) =
      Matrix.of ![![(Z * Z).n_plus, 0], ![0, (Z * Z).n_minus]] ∧
    (Z * Z).sigma_plus = -leviCivitaOperatorCross v_vec v_vec ∧
    (Z * Z).sigma_minus = leviCivitaOperatorCross u_vec u_vec ∧
    (Z * Z).sigma_plus 0 = -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (v_vec 1) (v_vec 2) ∧
    (Z * Z).sigma_plus 1 = -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (v_vec 2) (v_vec 0) ∧
    (Z * Z).sigma_plus 2 = -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (v_vec 0) (v_vec 1) ∧
    (Z * Z).sigma_minus 0 = InfoGeometry.OperatorAlgebra.PeirceSpine.comm (u_vec 1) (u_vec 2) ∧
    (Z * Z).sigma_minus 1 = InfoGeometry.OperatorAlgebra.PeirceSpine.comm (u_vec 2) (u_vec 0) ∧
    (Z * Z).sigma_minus 2 = InfoGeometry.OperatorAlgebra.PeirceSpine.comm (u_vec 0) (u_vec 1) := by
  intro Z
  have hInvL : opZornBoostFlow u_inv u (opZornBoostFlow u u_inv X) = X := by
    apply operatorZornMatrix_ext <;> simp only [opZornBoostFlow]
    · calc
        u_inv * (u * X.n_plus * u_inv) * u
            = (u_inv * u) * X.n_plus * (u_inv * u) := by noncomm_ring
        _ = 1 * X.n_plus * 1 := by rw [hu_inv]
        _ = X.n_plus := by noncomm_ring
    · calc
        u * (u_inv * X.n_minus * u) * u_inv
            = (u * u_inv) * X.n_minus * (u * u_inv) := by noncomm_ring
        _ = 1 * X.n_minus * 1 := by rw [hu]
        _ = X.n_minus := by noncomm_ring
    · funext i
      calc
        u_inv * (u * X.sigma_plus i * u) * u_inv
            = (u_inv * u) * X.sigma_plus i * (u * u_inv) := by noncomm_ring
        _ = 1 * X.sigma_plus i * 1 := by rw [hu_inv, hu]
        _ = X.sigma_plus i := by noncomm_ring
    · funext i
      calc
        u * (u_inv * X.sigma_minus i * u_inv) * u
            = (u * u_inv) * X.sigma_minus i * (u_inv * u) := by noncomm_ring
        _ = 1 * X.sigma_minus i * 1 := by rw [hu, hu_inv]
        _ = X.sigma_minus i := by noncomm_ring
  have hInvR : opZornBoostFlow u u_inv (opZornBoostFlow u_inv u X) = X := by
    apply operatorZornMatrix_ext <;> simp only [opZornBoostFlow]
    · calc
        u * (u_inv * X.n_plus * u) * u_inv
            = (u * u_inv) * X.n_plus * (u * u_inv) := by noncomm_ring
        _ = 1 * X.n_plus * 1 := by rw [hu]
        _ = X.n_plus := by noncomm_ring
    · calc
        u_inv * (u * X.n_minus * u_inv) * u
            = (u_inv * u) * X.n_minus * (u_inv * u) := by noncomm_ring
        _ = 1 * X.n_minus * 1 := by rw [hu_inv]
        _ = X.n_minus := by noncomm_ring
    · funext i
      calc
        u * (u_inv * X.sigma_plus i * u_inv) * u
            = (u * u_inv) * X.sigma_plus i * (u_inv * u) := by noncomm_ring
        _ = 1 * X.sigma_plus i * 1 := by rw [hu, hu_inv]
        _ = X.sigma_plus i := by noncomm_ring
    · funext i
      calc
        u_inv * (u * X.sigma_minus i * u) * u_inv
            = (u_inv * u) * X.sigma_minus i * (u * u_inv) := by noncomm_ring
        _ = 1 * X.sigma_minus i * 1 := by rw [hu_inv, hu]
        _ = X.sigma_minus i := by noncomm_ring
  have hSq : Z * Z =
      operatorZornCoordinates
        (operatorDot u_vec v_vec)
        (operatorDot v_vec u_vec)
        (-operatorCross v_vec v_vec)
        (operatorCross u_vec u_vec) :=
    operatorZornMul_chiralOperatorZorn u_vec v_vec
  have hNp : (Z * Z).n_plus = operatorDot u_vec v_vec := by
    rw [hSq, operatorZornCoordinates_nPlus]
  have hNm : (Z * Z).n_minus = operatorDot v_vec u_vec := by
    rw [hSq, operatorZornCoordinates_nMinus]
  have hSumV :
      (∑ i : Fin 3,
        genV (peirceSheetProj (A := B))
          (zornChiralPlaneMatrix i Z) (zornChiralPlaneMatrix i Z)) =
        Matrix.of ![![(Z * Z).n_plus, 0], ![0, (Z * Z).n_minus]] := by
    rw [sum_zornChiralPlane_genV Z Z, hNp, hNm]
    rfl
  have hSp : (Z * Z).sigma_plus = -leviCivitaOperatorCross v_vec v_vec := by
    rw [hSq, operatorZornCoordinates_sigmaPlus, leviCivitaOperatorCross_eq_operatorCross]
  have hSm : (Z * Z).sigma_minus = leviCivitaOperatorCross u_vec u_vec := by
    rw [hSq, operatorZornCoordinates_sigmaMinus, leviCivitaOperatorCross_eq_operatorCross]
  have hSp0 : (Z * Z).sigma_plus 0 =
      -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (v_vec 1) (v_vec 2) := by
    rw [hSq, operatorZornCoordinates_sigmaPlus]
    rfl
  have hSp1 : (Z * Z).sigma_plus 1 =
      -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (v_vec 2) (v_vec 0) := by
    rw [hSq, operatorZornCoordinates_sigmaPlus]
    rfl
  have hSp2 : (Z * Z).sigma_plus 2 =
      -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (v_vec 0) (v_vec 1) := by
    rw [hSq, operatorZornCoordinates_sigmaPlus]
    rfl
  have hSm0 : (Z * Z).sigma_minus 0 =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (u_vec 1) (u_vec 2) := by
    rw [hSq, operatorZornCoordinates_sigmaMinus]
    rfl
  have hSm1 : (Z * Z).sigma_minus 1 =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (u_vec 2) (u_vec 0) := by
    rw [hSq, operatorZornCoordinates_sigmaMinus]
    rfl
  have hSm2 : (Z * Z).sigma_minus 2 =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (u_vec 0) (u_vec 1) := by
    rw [hSq, operatorZornCoordinates_sigmaMinus]
    rfl
  exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, hInvL, hInvR,
    hNp, hNm, hSumV, hSp, hSm, hSp0, hSp1, hSp2, hSm0, hSm1, hSm2⟩

/-- **Theorem 11.2 (`three_idempotent_peirce_gauge_partition_and_sm_structure_constants_bridge`, Move B)**:
Connects the 3-idempotent gauge partition $e_1 + e_2 + e_3 = 1$ of
`OrthogonalIdempotentSystem B` (`Clifford55GaugeSubalgebraBridge.lean`) to the 2-sheet
Peirce decomposition (`invS`, `conePlus`, `coneMinus`) and unifies it with the $(6, 2, 2)$
hyperbolic trace signature, the $\mathfrak{su}(3)$ Gell-Mann structure constants $f_{abc}, d_{abc}$,
and the electroweak/GUT trace normalizations (`SMNormalizedGaugeEmbedding.lean`):
1. **3-Idempotent ↔ 2-Sheet Peirce Decomposition:**
   For any `S : OrthogonalIdempotentSystem B` and `X, Y, Z : B`:
   - `1 - S.e1 = S.e2 + S.e3` and `invS S.e1 = S.e1 - S.e2 - S.e3`,
   - `invS S.e1 * (S.e1 * X * S.e1) = S.e1 * X * S.e1` (`+1` eigenvalue on the color block),
   - `invS S.e1 * (S.e2 * Y * S.e2) = -(S.e2 * Y * S.e2)` and
     `invS S.e1 * (S.e3 * Z * S.e3) = -(S.e3 * Z * S.e3)` (`-1` eigenvalue on the weak/hypercharge blocks),
   - `conePlus S.e1 X = S.e1 * X * S.e2 + S.e1 * X * S.e3` and
     `coneMinus S.e1 X = S.e2 * X * S.e1 + S.e3 * X * S.e1`,
   - if `StabilizesIdempotents S X`, then both cross-sheet Witt cones vanish:
     `conePlus S.e1 X = 0` and `coneMinus S.e1 X = 0`;
2. **Concrete $(6, 2, 2)$ Ranks, $\mathfrak{su}(3)$ Structure Constants, & Electroweak Trace Ratios:**
   - `Matrix.trace e1 = 6`, `Matrix.trace e2 = 2`, `Matrix.trace e3 = 2`,
   - `(∑ c : Fin 8, ∑ e : Fin 8, d a c e * d b c e) = (20 / 3 : ℝ) * (if a = b then 1 else 0 : ℝ)`,
   - `traceNormSq weakT3Generator = 2`, `traceNormSq hyperchargeGenerator = 10 / 3`,
     `hyperchargeNormalizationIndex = 5 / 3`,
     `normalizedHyperchargeCouplingSq / normalizedWeakCouplingSq = 3 / 5`,
     `derivedWeakAngleSinSq = 3 / 8`, and `(20 / 3 : ℚ) = 4 * hyperchargeNormalizationIndex`. -/
theorem three_idempotent_peirce_gauge_partition_and_sm_structure_constants_bridge
    {B : Type*} [Ring B] (S : OrthogonalIdempotentSystem B) (X Y Z : B)
    (a b : Fin 8) :
    (1 - S.e1 = S.e2 + S.e3 ∧
     invS S.e1 = S.e1 - S.e2 - S.e3 ∧
     invS S.e1 * (S.e1 * X * S.e1) = S.e1 * X * S.e1 ∧
     invS S.e1 * (S.e2 * Y * S.e2) = -(S.e2 * Y * S.e2) ∧
     invS S.e1 * (S.e3 * Z * S.e3) = -(S.e3 * Z * S.e3) ∧
     conePlus S.e1 X = S.e1 * X * S.e2 + S.e1 * X * S.e3 ∧
     coneMinus S.e1 X = S.e2 * X * S.e1 + S.e3 * X * S.e1 ∧
     (StabilizesIdempotents S X → conePlus S.e1 X = 0 ∧ coneMinus S.e1 X = 0)) ∧
    (Matrix.trace e1 = 6 ∧
     Matrix.trace e2 = 2 ∧
     Matrix.trace e3 = 2 ∧
     (∑ c : Fin 8, ∑ e : Fin 8, d a c e * d b c e) =
       (20 / 3 : ℝ) * (if a = b then 1 else 0 : ℝ) ∧
     traceNormSq weakT3Generator = 2 ∧
     traceNormSq hyperchargeGenerator = 10 / 3 ∧
     hyperchargeNormalizationIndex = 5 / 3 ∧
     normalizedHyperchargeCouplingSq / normalizedWeakCouplingSq = 3 / 5 ∧
     derivedWeakAngleSinSq = 3 / 8 ∧
     (20 / 3 : ℚ) = 4 * hyperchargeNormalizationIndex) := by
  have hComp : 1 - S.e1 = S.e2 + S.e3 := by
    calc
      1 - S.e1 = (S.e1 + S.e2 + S.e3) - S.e1 := by rw [S.partition_unity]
      _ = S.e2 + S.e3 := by abel
  have hInvS : invS S.e1 = S.e1 - S.e2 - S.e3 := by
    calc
      invS S.e1 = S.e1 - (1 - S.e1) := by
        unfold invS
        noncomm_ring
      _ = S.e1 - (S.e2 + S.e3) := by rw [hComp]
      _ = S.e1 - S.e2 - S.e3 := by abel
  have hEig1 : invS S.e1 * (S.e1 * X * S.e1) = S.e1 * X * S.e1 := by
    rw [hInvS]
    calc
      (S.e1 - S.e2 - S.e3) * (S.e1 * X * S.e1)
          = (S.e1 * S.e1) * X * S.e1 - (S.e2 * S.e1) * X * S.e1 -
              (S.e3 * S.e1) * X * S.e1 := by noncomm_ring
      _ = S.e1 * X * S.e1 - 0 * X * S.e1 - 0 * X * S.e1 := by
        rw [S.e1_idem, S.e2_e1_ortho, S.e3_e1_ortho]
      _ = S.e1 * X * S.e1 := by noncomm_ring
  have hEig2 : invS S.e1 * (S.e2 * Y * S.e2) = -(S.e2 * Y * S.e2) := by
    rw [hInvS]
    calc
      (S.e1 - S.e2 - S.e3) * (S.e2 * Y * S.e2)
          = (S.e1 * S.e2) * Y * S.e2 - (S.e2 * S.e2) * Y * S.e2 -
              (S.e3 * S.e2) * Y * S.e2 := by noncomm_ring
      _ = 0 * Y * S.e2 - S.e2 * Y * S.e2 - 0 * Y * S.e2 := by
        rw [S.e1_e2_ortho, S.e2_idem, S.e3_e2_ortho]
      _ = -(S.e2 * Y * S.e2) := by noncomm_ring
  have hEig3 : invS S.e1 * (S.e3 * Z * S.e3) = -(S.e3 * Z * S.e3) := by
    rw [hInvS]
    calc
      (S.e1 - S.e2 - S.e3) * (S.e3 * Z * S.e3)
          = (S.e1 * S.e3) * Z * S.e3 - (S.e2 * S.e3) * Z * S.e3 -
              (S.e3 * S.e3) * Z * S.e3 := by noncomm_ring
      _ = 0 * Z * S.e3 - 0 * Z * S.e3 - S.e3 * Z * S.e3 := by
        rw [S.e1_e3_ortho, S.e2_e3_ortho, S.e3_idem]
      _ = -(S.e3 * Z * S.e3) := by noncomm_ring
  have hConeP : conePlus S.e1 X = S.e1 * X * S.e2 + S.e1 * X * S.e3 := by
    unfold conePlus
    rw [hComp]
    noncomm_ring
  have hConeM : coneMinus S.e1 X = S.e2 * X * S.e1 + S.e3 * X * S.e1 := by
    unfold coneMinus
    rw [hComp]
    noncomm_ring
  have hStab : StabilizesIdempotents S X → conePlus S.e1 X = 0 ∧ coneMinus S.e1 X = 0 := by
    intro hS
    have hCross := (stabilizes_iff_cross_blocks_vanish S X).mp hS
    rcases hCross with ⟨h12, h13, h21, _, h31, _⟩
    refine ⟨?_, ?_⟩
    · rw [hConeP, h12, h13, add_zero]
    · rw [hConeM, h21, h31, add_zero]
  have hRatio20 : (20 / 3 : ℚ) = 4 * hyperchargeNormalizationIndex := by
    rw [hyperchargeNormalizationIndex_eq_five_thirds]
    norm_num
  exact ⟨⟨hComp, hInvS, hEig1, hEig2, hEig3, hConeP, hConeM, hStab⟩,
    ⟨e1_trace, e2_trace, e3_trace, d_normalization a b,
     weakT3_traceNormSq, hypercharge_traceNormSq,
     hyperchargeNormalizationIndex_eq_five_thirds,
     normalized_coupling_ratio, derivedWeakAngleSinSq_eq_three_eighths,
     hRatio20⟩⟩

/-- **Theorem 11.3 (`cuntz_casimir2_eq_sixteen_invOf_six_and_central`, Move C.1)**:
In any commutative ring `[CommRing R]` with `[Invertible (2 : R)] [Invertible (6 : R)]`,
for any Cuntz $\mathcal{O}_3$ generator family `g : CuntzO3Generators R`, the Cuntz
completeness relation $P_1 + P_2 + P_3 = 1$ collapses the $\mathfrak{su}(3)$ quadratic
Casimir operator `casimir2 g` identically to the central scalar
`2 + 4 * ⅟(6 : R) = 16 * ⅟(6 : R)` ($= 8 / 3$), and `lieBracket (casimir2 g) x = 0`
for every $x \in R$. -/
theorem cuntz_casimir2_eq_sixteen_invOf_six_and_central
    {R : Type*} [CommRing R] [Invertible (2 : R)] [Invertible (6 : R)]
    (g : CuntzO3Generators R) (x : R) :
    casimir2 g = 2 + 4 * ⅟(6 : R) ∧
    casimir2 g = 16 * ⅟(6 : R) ∧
    InfoGeometry.Algebra.CuntzO3TriSupersymmetry.lieBracket (casimir2 g) x = 0 := by
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self (2 : R)
  have h6 : (6 : R) * ⅟(6 : R) = 1 := mul_invOf_self (6 : R)
  have hhalf : ⅟(2 : R) = 3 * ⅟(6 : R) := by
    calc
      ⅟(2 : R) = ⅟(2 : R) * ((6 : R) * ⅟(6 : R)) := by rw [h6, mul_one]
      _ = (⅟(2 : R) * 2) * (3 * ⅟(6 : R)) := by ring
      _ = 3 * ⅟(6 : R) := by rw [h2, one_mul]
  have hCas1 : casimir2 g = 2 + 4 * ⅟(6 : R) := by
    rw [casimir2_eq_scalar g, hhalf]
    ring
  have hCas2 : casimir2 g = 16 * ⅟(6 : R) := by
    rw [hCas1]
    calc
      2 + 4 * ⅟(6 : R) = 2 * ((6 : R) * ⅟(6 : R)) + 4 * ⅟(6 : R) := by
        rw [h6, mul_one]
      _ = 16 * ⅟(6 : R) := by ring
  exact ⟨hCas1, hCas2, casimir2_commutes g x⟩

/-- **Theorem 11.4 (`mersenne_tensor_tower_stage_dimension_and_fine_structure_colimit_bridge`, Move C.2)**:
Unifies the Combinatorial Hierarchy / Mersenne numbers `mersenne n = 2^n - 1`
(`CliffordTower.lean`), the parafermion centralizer hierarchy `3 + 7 + 127 = 137`
(`FineStructureDerivation.lean`), and the Pellis golden-ratio decomposition
(`PellisFineStructure.lean`) with:
1. the $2^n \times 2^n$ tensor-tower spinor and matrix dimensions at finite stage `n`:
   `Fintype.card (Fin (2 ^ n)) = mersenne n + 1` and
   `Fintype.card (Fin (2 ^ n) × Fin (2 ^ n)) = mersenne (2 * n) + 1`,
2. the concrete Combinatorial Hierarchy values `mersenne 2 = 3`, `mersenne 3 = 7`,
   `mersenne 7 = 127`, `parafermionCentralizerDim = 137`, `alpha_combinatorial = 1 / 137`,
   and the golden-ratio quadratic equation `phi ^ 2 = phi + 1`,
3. the non-commutative operator Penrose Kite/Dart golden-ratio quadratic equation
   `(penroseKiteOp Pinf Ainf Cinf) ^ 2 = penroseKiteOp Pinf Ainf Cinf + penroseDartOp Pinf Ainf Cinf`
   and all-`m` power inflation law in the $2^n \times 2^n$ inductive colimit `Limit`. -/
theorem mersenne_tensor_tower_stage_dimension_and_fine_structure_colimit_bridge
    (n m : ℕ) {Pinf : Limit} (hPinf : Pinf * Pinf = Pinf) (Ainf Cinf : Limit) :
    Fintype.card (Fin (2 ^ n)) = InfoGeometry.Clifford.CliffordTower.mersenne n + 1 ∧
    Fintype.card (Fin (2 ^ n) × Fin (2 ^ n)) =
      InfoGeometry.Clifford.CliffordTower.mersenne (2 * n) + 1 ∧
    InfoGeometry.Clifford.CliffordTower.mersenne 2 = 3 ∧
    InfoGeometry.Clifford.CliffordTower.mersenne 3 = 7 ∧
    InfoGeometry.Clifford.CliffordTower.mersenne 7 = 127 ∧
    parafermionCentralizerDim =
      InfoGeometry.Clifford.CliffordTower.mersenne 2 +
        InfoGeometry.Clifford.CliffordTower.mersenne 3 +
        InfoGeometry.Clifford.CliffordTower.mersenne 7 ∧
    parafermionCentralizerDim = 137 ∧
    InfoGeometry.Physics.FineStructureDerivation.alpha_combinatorial = 1 / (137 : ℝ) ∧
    phi ^ 2 = phi + 1 ∧
    0 < pellis_correction ∧ pellis_correction < 1 ∧
    (penroseKiteOp Pinf Ainf Cinf) ^ 2 =
      penroseKiteOp Pinf Ainf Cinf + penroseDartOp Pinf Ainf Cinf ∧
    (penroseKiteOp Pinf Ainf Cinf) ^ (m + 1) =
      polygonFibSeq Pinf Ainf Cinf (m + 1) * penroseKiteOp Pinf Ainf Cinf +
        penroseDartOp Pinf Ainf Cinf * polygonFibSeq Pinf Ainf Cinf m := by
  have hPowPos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hPowPos2 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
  have hCardSpinor :
      Fintype.card (Fin (2 ^ n)) = InfoGeometry.Clifford.CliffordTower.mersenne n + 1 := by
    rw [Fintype.card_fin, InfoGeometry.Clifford.CliffordTower.mersenne,
      Nat.sub_add_cancel hPowPos]
  have hCardMat :
      Fintype.card (Fin (2 ^ n) × Fin (2 ^ n)) =
        InfoGeometry.Clifford.CliffordTower.mersenne (2 * n) + 1 := by
    rw [Fintype.card_prod, Fintype.card_fin,
      InfoGeometry.Clifford.CliffordTower.mersenne, Nat.sub_add_cancel hPowPos2]
    rw [two_mul, pow_add]
  have hKiteSq :
      (penroseKiteOp Pinf Ainf Cinf) ^ 2 =
        penroseKiteOp Pinf Ainf Cinf + penroseDartOp Pinf Ainf Cinf := by
    rw [sq]
    unfold penroseKiteOp penroseDartOp peirceTransfer
    peirce_nf hPinf
  have hKitePow :
      (penroseKiteOp Pinf Ainf Cinf) ^ (m + 1) =
        polygonFibSeq Pinf Ainf Cinf (m + 1) * penroseKiteOp Pinf Ainf Cinf +
          penroseDartOp Pinf Ainf Cinf * polygonFibSeq Pinf Ainf Cinf m :=
    (all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence hPinf Ainf Cinf m).1
  exact ⟨hCardSpinor, hCardMat, mersenne_two, mersenne_three, mersenne_seven,
    centralizer_equals_hierarchy, centralizer_is_137,
    combinatorial_alpha_is_1_137, phi_quadratic,
    correction_bounds.1, correction_bounds.2,
    hKiteSq, hKitePow⟩

end StructureConstantsAndInteractionScalesSynthesis

/-!
## 12. Stage `D₂₅` (`F₁ → F₅`): Non-Commutative Dressing Field Method (`DFM`), Cocyclic Maurer–Cartan Chain Rule, Flat Ehresmann Connection, Dressed BRST Ghost Vanishing (`C_ghost^U = 0`), Relational Frame Transformations of the Second Kind (`U ↦ U Ξ`), and Unipotent / Bruhat–Postnikov Peirce Horizon Dressing

Formalizes the 5-stage causal poset (`F₁ → F₅`) of non-commutative dressing-field and
cocyclic operator archetypes over an arbitrary associative ring `[Ring B]` (with zero
commutativity or scalar assumptions), bridges them to the Peirce–Bruhat–Postnikov spine
(`conePlus`, `coneMinus`, `genV`, `plabicWhiteShear`, `plabicTripWB`, `leftCornerPullback`),
and transports them to the $2^n \times 2^n$ tensor-tower inductive colimit `Limit`:
1. **`F₁` (`maurerCartanCocycle`, `maurer_cartan_cocycle_and_composition`, `flat_ehresmann_maurer_cartan_curvature_zero`):**
   - For any map `d : B → B` satisfying the Leibniz rule `d (U * Γ) = d U * Γ + U * d Γ`
     and `U_inv * U = 1`, the non-Abelian Maurer–Cartan 1-cocycle
     `maurerCartanCocycle d U U_inv = U_inv * d U` satisfies the exact cocycle chain rule
     `maurerCartanCocycle d (U * Γ) (Γ_inv * U_inv) = Γ_inv * maurerCartanCocycle d U U_inv * Γ + maurerCartanCocycle d Γ Γ_inv`,
     and `dressedConn` composes transitively:
     `dressedConn d Γ Γ_inv (dressedConn d U U_inv A) = dressedConn d (U * Γ) (Γ_inv * U_inv) A`;
   - Whenever `U * U_inv = 1`, `U_inv * U = 1`, `d 1 = 0`, `d (U_inv * U) = d U_inv * U + U_inv * d U`,
     and `d (U_inv * d U) = d U_inv * d U + U_inv * d (d U)`, the inverse derivation rule
     `d U_inv = -(U_inv * d U * U_inv)` holds and the pure-dressing Ehresmann connection
     `ω₀ = maurerCartanCocycle d U U_inv = -(d U_inv * U)` satisfies
     `d ω₀ + ω₀ * ω₀ = U_inv * d (d U)` (and vanishes identically whenever `d (d U) = 0`).
2. **`F₂` (`dressed_fields_exact_gauge_invariance`):**
   Under gauge transformations `A^Γ = dressedConn d Γ Γ_inv A`, `F^Γ = dressedCurv Γ Γ_inv F`,
   `φ^Γ = dressedState Γ_inv φ` and dressing field equivariance `U^Γ = Γ_inv * U`
   (`(U^Γ)_inv = U_inv * Γ`), all three dressed observables are strictly gauge-invariant:
   `dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) = dressedConn d U U_inv A`,
   `dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F) = dressedCurv U U_inv F`,
   and `dressedState (U_inv * Γ) (dressedState Γ_inv φ) = dressedState U_inv φ`.
3. **`F₃` (`brstGhostFromDressing`, `dressedGhost`, `dressed_brst_ghost_vanishes`):**
   When the dressing field transforms under a BRST variation `δ_brst : B → B` as
   `δ_brst U = -C_ghost * U` so that `C_ghost = brstGhostFromDressing δ_brst U U_inv = -(δ_brst U * U_inv)`,
   the dressed BRST ghost vanishes identically:
   `dressedGhost δ_brst U U_inv (brstGhostFromDressing δ_brst U U_inv) = 0`.
4. **`F₄` (`frame_transformation_of_second_kind`):**
   Right-multiplying the dressing field by a frame transition `U ↦ U * Ξ` (`U_inv ↦ Ξ_inv * U_inv`)
   induces a relational transformation of the second kind on all dressed observables:
   `dressedConn d (U * Ξ) (Ξ_inv * U_inv) A = dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A)`,
   `dressedCurv (U * Ξ) (Ξ_inv * U_inv) F = dressedCurv Ξ Ξ_inv (dressedCurv U U_inv F)`,
   and `dressedState (Ξ_inv * U_inv) φ = dressedState Ξ_inv (dressedState U_inv φ)`.
5. **`F₅` (`peirce_horizon_unipotent_and_bruhat_dressing`, `stage_D25_dressing_field_method_cocycle_and_brst_master_synthesis`, `limit_stage_D25_dressing_field_and_bruhat_cocycle_bridge`):**
   In any associative ring `[Ring B]` with idempotent `P * P = P` and inner derivation `d = comm P`:
   - For the unipotent horizon dressing `U = 1 + conePlus P A = plabicWhiteShear P A` with
     `U_inv = 1 - conePlus P A`, `maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A`,
     `dressedConn (comm P) (1 + conePlus P A) (1 - conePlus P A) P = P + (2 : ℤ) • conePlus P A`,
     and `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C`;
   - For the Bruhat–Postnikov two-cone dressing `U = plabicTripWB P A C = (1 + conePlus P A) * (1 - coneMinus P C)`
     with `U_inv = plabicTripWBInv P A C = (1 + coneMinus P C) * (1 - conePlus P A)`,
     `maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C) = leftCornerPullback P A C = genPhi P A C - genSig P A C - genV P A C * coneMinus P C`
     and `idempotencyDefect (P + maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C)) = 0`;
   - All unipotent and Bruhat–Postnikov dressing identities transport across `bondMap stageBond n m hnm`
     and `ofStage n` to the $2^n \times 2^n$ inductive colimit `Limit`.
-/

section NonCommutativeDressingFieldCocycleAndBRSTPoset

variable {B : Type*} [Ring B]

/-- **Archetype `F₁` (`maurerCartanCocycle`):**
Given any derivation map `d : B → B` and an operator `U` with left/two-sided inverse `U_inv`,
`maurerCartanCocycle d U U_inv = U_inv * d U`. -/
def maurerCartanCocycle (d : B → B) (U U_inv : B) : B :=
  U_inv * d U

/-- **Archetype `F₂` (`dressedConn`):**
Non-commutative dressed connection / gauge transformation `U_inv * A * U + U_inv * d U`. -/
def dressedConn (d : B → B) (U U_inv A : B) : B :=
  U_inv * A * U + U_inv * d U

/-- **Archetype `F₂` (`dressedCurv`):**
Non-commutative dressed curvature / adjoint-covariant tensor `U_inv * F * U`. -/
def dressedCurv (U U_inv F : B) : B :=
  U_inv * F * U

/-- **Archetype `F₂` (`dressedState`):**
Non-commutative dressed matter / spinor state `U_inv * φ`. -/
def dressedState (U_inv φ : B) : B :=
  U_inv * φ

/-- **Archetype `F₃` (`brstGhostFromDressing`):**
Pure BRST ghost extracted from the dressing variation `-(δ_brst U * U_inv)`. -/
def brstGhostFromDressing (δ_brst : B → B) (U U_inv : B) : B :=
  -(δ_brst U * U_inv)

/-- **Archetype `F₃` (`dressedGhost`):**
Dressed BRST ghost `U_inv * C_ghost * U + U_inv * δ_brst U`. -/
def dressedGhost (δ_brst : B → B) (U U_inv C_ghost : B) : B :=
  U_inv * C_ghost * U + U_inv * δ_brst U

/-- **Theorem 12.1 (`maurer_cartan_cocycle_and_composition`, Archetype `F₁.1`):**
Let `d : B → B` satisfy the Leibniz rule `d (U * Γ) = d U * Γ + U * d Γ` and let `U_inv * U = 1`.
Then:
1. `maurerCartanCocycle d (U * Γ) (Γ_inv * U_inv) =`
   `Γ_inv * maurerCartanCocycle d U U_inv * Γ + maurerCartanCocycle d Γ Γ_inv`.
2. `dressedConn d Γ Γ_inv (dressedConn d U U_inv A) = dressedConn d (U * Γ) (Γ_inv * U_inv) A`. -/
theorem maurer_cartan_cocycle_and_composition
    (d : B → B) {U U_inv Γ Γ_inv : B}
    (hLeib : d (U * Γ) = d U * Γ + U * d Γ)
    (hU : U_inv * U = 1) (A : B) :
    maurerCartanCocycle d (U * Γ) (Γ_inv * U_inv) =
      Γ_inv * maurerCartanCocycle d U U_inv * Γ + maurerCartanCocycle d Γ Γ_inv ∧
    dressedConn d Γ Γ_inv (dressedConn d U U_inv A) =
      dressedConn d (U * Γ) (Γ_inv * U_inv) A := by
  have hCocycle : maurerCartanCocycle d (U * Γ) (Γ_inv * U_inv) =
      Γ_inv * maurerCartanCocycle d U U_inv * Γ + maurerCartanCocycle d Γ Γ_inv := by
    unfold maurerCartanCocycle
    rw [hLeib, mul_add]
    congr 1
    · simp only [mul_assoc]
    · calc
        (Γ_inv * U_inv) * (U * d Γ)
            = Γ_inv * (U_inv * U) * d Γ := by simp only [mul_assoc]
        _ = Γ_inv * d Γ := by rw [hU, mul_one]
  refine ⟨hCocycle, ?_⟩
  unfold dressedConn
  change Γ_inv * (U_inv * A * U + maurerCartanCocycle d U U_inv) * Γ +
      maurerCartanCocycle d Γ Γ_inv =
    (Γ_inv * U_inv) * A * (U * Γ) + maurerCartanCocycle d (U * Γ) (Γ_inv * U_inv)
  rw [hCocycle, mul_add, add_mul, add_assoc]
  congr 1
  simp only [mul_assoc]

/-- **Theorem 12.2 (`flat_ehresmann_maurer_cartan_curvature_zero`, Archetype `F₁.2`):**
For any `d : B → B` and two-sided inverse pair `(U, U_inv)` (`U * U_inv = 1`, `U_inv * U = 1`)
satisfying `d 1 = 0`, `d (U_inv * U) = d U_inv * U + U_inv * d U`, and
`d (U_inv * d U) = d U_inv * d U + U_inv * d (d U)`:
1. **Non-Commutative Inverse Derivation Rule:**
   `d U_inv = -(U_inv * d U * U_inv)` and `maurerCartanCocycle d U U_inv = -(d U_inv * U)`;
2. **Maurer–Cartan Curvature Identity:**
   `d (maurerCartanCocycle d U U_inv) + maurerCartanCocycle d U U_inv * maurerCartanCocycle d U U_inv = U_inv * d (d U)`;
3. **Flat Ehresmann Connection (`d²(U) = 0 ⟹ d ω₀ + ω₀² = 0`):**
   If `d (d U) = 0`, then
   `d (maurerCartanCocycle d U U_inv) + maurerCartanCocycle d U U_inv * maurerCartanCocycle d U U_inv = 0`. -/
theorem flat_ehresmann_maurer_cartan_curvature_zero
    (d : B → B) {U U_inv : B}
    (hUUinv : U * U_inv = 1) (hUinvU : U_inv * U = 1)
    (hd1 : d 1 = 0)
    (hLeibInv : d (U_inv * U) = d U_inv * U + U_inv * d U)
    (hLeibMC : d (U_inv * d U) = d U_inv * d U + U_inv * d (d U)) :
    d U_inv = -(U_inv * d U * U_inv) ∧
    maurerCartanCocycle d U U_inv = -(d U_inv * U) ∧
    d (maurerCartanCocycle d U U_inv) +
        maurerCartanCocycle d U U_inv * maurerCartanCocycle d U U_inv =
      U_inv * d (d U) ∧
    (d (d U) = 0 →
      d (maurerCartanCocycle d U U_inv) +
        maurerCartanCocycle d U U_inv * maurerCartanCocycle d U U_inv = 0) := by
  have hZero : d U_inv * U + U_inv * d U = 0 := by
    rw [← hLeibInv, hUinvU, hd1]
  have hdUinvU : d U_inv * U = -(U_inv * d U) :=
    eq_neg_of_add_eq_zero_left hZero
  have hdUinv : d U_inv = -(U_inv * d U * U_inv) := by
    calc
      d U_inv = d U_inv * (U * U_inv) := by rw [hUUinv, mul_one]
      _ = (d U_inv * U) * U_inv := by noncomm_ring
      _ = -(U_inv * d U) * U_inv := by rw [hdUinvU]
      _ = -(U_inv * d U * U_inv) := by noncomm_ring
  have hMCneg : maurerCartanCocycle d U U_inv = -(d U_inv * U) := by
    unfold maurerCartanCocycle
    rw [hdUinvU, neg_neg]
  have hCurv :
      d (maurerCartanCocycle d U U_inv) +
          maurerCartanCocycle d U U_inv * maurerCartanCocycle d U U_inv =
        U_inv * d (d U) := by
    unfold maurerCartanCocycle
    rw [hLeibMC, hdUinv]
    noncomm_ring
  refine ⟨hdUinv, hMCneg, hCurv, ?_⟩
  intro hddU
  rw [hCurv, hddU, mul_zero]

/-- **Theorem 12.3 (`dressed_fields_exact_gauge_invariance`, Archetype `F₂`):**
Under a gauge transformation `Γ` (`Γ_inv * Γ = 1`, `Γ * Γ_inv = 1`), where bare fields
transform as `A^Γ = dressedConn d Γ Γ_inv A`, `F^Γ = dressedCurv Γ Γ_inv F`,
`φ^Γ = dressedState Γ_inv φ` and the dressing field transforms as `U^Γ = Γ_inv * U`
with inverse `(U^Γ)_inv = U_inv * Γ`, all dressed observables are strictly gauge-invariant:
1. `dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) = dressedConn d U U_inv A`,
2. `dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F) = dressedCurv U U_inv F`,
3. `dressedState (U_inv * Γ) (dressedState Γ_inv φ) = dressedState U_inv φ`. -/
theorem dressed_fields_exact_gauge_invariance
    (d : B → B) {U U_inv Γ Γ_inv : B}
    (hLeib : d (Γ * (Γ_inv * U)) = d Γ * (Γ_inv * U) + Γ * d (Γ_inv * U))
    (hΓ1 : Γ_inv * Γ = 1) (hΓ2 : Γ * Γ_inv = 1) (A F φ : B) :
    dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) =
      dressedConn d U U_inv A ∧
    dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F) =
      dressedCurv U U_inv F ∧
    dressedState (U_inv * Γ) (dressedState Γ_inv φ) =
      dressedState U_inv φ := by
  have hComp :=
    (maurer_cartan_cocycle_and_composition d (U_inv := Γ_inv) (Γ_inv := U_inv * Γ)
      hLeib hΓ1 A).2
  have hProd1 : Γ * (Γ_inv * U) = U := by rw [← mul_assoc, hΓ2, one_mul]
  have hProd2 : (U_inv * Γ) * Γ_inv = U_inv := by rw [mul_assoc, hΓ2, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hComp, hProd1, hProd2]
  · unfold dressedCurv
    calc
      (U_inv * Γ) * (Γ_inv * F * Γ) * (Γ_inv * U)
          = U_inv * (Γ * Γ_inv) * F * (Γ * Γ_inv) * U := by simp only [mul_assoc]
      _ = U_inv * F * U := by rw [hΓ2, mul_one, mul_one]
  · unfold dressedState
    rw [← mul_assoc, hProd2]

/-- **Theorem 12.4 (`dressed_brst_ghost_vanishes`, Archetype `F₃`):**
When the dressing field `U` (`U_inv * U = 1`) reduces the gauge symmetry so that the BRST
ghost is `C_ghost = brstGhostFromDressing δ_brst U U_inv = -(δ_brst U * U_inv)`, the
dressed ghost vanishes identically:
`dressedGhost δ_brst U U_inv (brstGhostFromDressing δ_brst U U_inv) = 0`. -/
theorem dressed_brst_ghost_vanishes
    (δ_brst : B → B) {U U_inv : B} (hU : U_inv * U = 1) :
    dressedGhost δ_brst U U_inv (brstGhostFromDressing δ_brst U U_inv) = 0 := by
  unfold dressedGhost brstGhostFromDressing
  have hSimp : U_inv * -(δ_brst U * U_inv) * U = -(U_inv * δ_brst U) := by
    calc
      U_inv * -(δ_brst U * U_inv) * U
          = -(U_inv * δ_brst U * (U_inv * U)) := by
            simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(U_inv * δ_brst U) := by rw [hU, mul_one]
  rw [hSimp, neg_add_cancel]

/-- **Theorem 12.5 (`frame_transformation_of_second_kind`, Archetype `F₄`):**
Under a relational reference-frame transition `U ↦ U * Ξ` (with inverse `Ξ_inv * U_inv`
where `U_inv * U = 1`), the dressed observables transform covariantly by `Ξ`:
1. `dressedConn d (U * Ξ) (Ξ_inv * U_inv) A = dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A)`,
2. `dressedCurv (U * Ξ) (Ξ_inv * U_inv) F = dressedCurv Ξ Ξ_inv (dressedCurv U U_inv F)`,
3. `dressedState (Ξ_inv * U_inv) φ = dressedState Ξ_inv (dressedState U_inv φ)`. -/
theorem frame_transformation_of_second_kind
    (d : B → B) {U U_inv Ξ Ξ_inv : B}
    (hLeib : d (U * Ξ) = d U * Ξ + U * d Ξ)
    (hU : U_inv * U = 1) (A F φ : B) :
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A =
      dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A) ∧
    dressedCurv (U * Ξ) (Ξ_inv * U_inv) F =
      dressedCurv Ξ Ξ_inv (dressedCurv U U_inv F) ∧
    dressedState (Ξ_inv * U_inv) φ =
      dressedState Ξ_inv (dressedState U_inv φ) := by
  refine ⟨(maurer_cartan_cocycle_and_composition d hLeib hU A).2.symm, ?_, ?_⟩
  · unfold dressedCurv
    simp only [mul_assoc]
  · unfold dressedState
    rw [mul_assoc]

/-- Explicit two-sided inverse `(1 + coneMinus P C) * (1 - conePlus P A)` of the
Bruhat–Postnikov two-cone dressing operator `plabicTripWB P A C`. -/
def plabicTripWBInv (P A C : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A)

/-- **Theorem 12.6 (`peirce_horizon_unipotent_and_bruhat_dressing`, Archetype `F₅`):**
Bridges the non-commutative Dressing Field Method to the Peirce–Bruhat–Postnikov spine
over any `[Ring B]` with idempotent `P` (`P * P = P`) and inner grading derivation `d = comm P`:
1. **Unipotent Horizon Dressing (`U = 1 + conePlus P A = plabicWhiteShear P A`):**
   - `(1 - conePlus P A) * (1 + conePlus P A) = 1`,
   - `maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A`,
   - `dressedConn (comm P) (1 + conePlus P A) (1 - conePlus P A) P = P + (2 : ℤ) • conePlus P A`,
   - `dressedConn (fun X => -comm P X) (1 + conePlus P A) (1 - conePlus P A) P = P`,
   - `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C`;
2. **Bruhat–Postnikov Two-Cone Dressing (`U = plabicTripWB P A C`, `U_inv = plabicTripWBInv P A C`):**
   - `maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C) = leftCornerPullback P A C`,
   - `maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C) = genPhi P A C - genSig P A C - genV P A C * coneMinus P C`,
   - `idempotencyDefect (P + maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C)) = 0`,
   - `dressedCurv (plabicTripWB P A C) (plabicTripWBInv P A C) P = P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C`. -/
theorem peirce_horizon_unipotent_and_bruhat_dressing
    {P : B} (hP : P * P = P) (A C : B) :
    (1 - conePlus P A) * (1 + conePlus P A) = 1 ∧
    maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A ∧
    dressedConn (comm P) (1 + conePlus P A) (1 - conePlus P A) P =
      P + (2 : ℤ) • conePlus P A ∧
    dressedConn (fun X => -comm P X) (1 + conePlus P A) (1 - conePlus P A) P = P ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C ∧
    maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C) =
      leftCornerPullback P A C ∧
    maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C) =
      genPhi P A C - genSig P A C - genV P A C * coneMinus P C ∧
    idempotencyDefect
        (P + maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C)) = 0 ∧
    dressedCurv (plabicTripWB P A C) (plabicTripWBInv P A C) P =
      P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C := by
  have hInv : (1 - conePlus P A) * (1 + conePlus P A) = 1 := by peirce_nf hP
  have hMC :
      maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A := by
    unfold maurerCartanCocycle
    peirce_nf hP
  have hConnPlus :
      dressedConn (comm P) (1 + conePlus P A) (1 - conePlus P A) P =
        P + (2 : ℤ) • conePlus P A := by
    unfold dressedConn
    peirce_nf hP
  have hConnMinus :
      dressedConn (fun X => -comm P X) (1 + conePlus P A) (1 - conePlus P A) P = P := by
    unfold dressedConn
    peirce_nf hP
  have hCurvV :
      dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C := by
    unfold dressedCurv
    peirce_nf hP
  have hBruhatDef :
      maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C) =
        leftCornerPullback P A C := by
    rfl
  have hBruhatEq :
      maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C) =
        genPhi P A C - genSig P A C - genV P A C * coneMinus P C := by
    rw [hBruhatDef]
    exact leftCornerPullback_eq hP A C
  have hBruhatIdem :
      idempotencyDefect
          (P + maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C)) = 0 := by
    rw [hBruhatDef]
    exact leftCornerPullback_idempotency hP A C
  have hBruhatChart :
      dressedCurv (plabicTripWB P A C) (plabicTripWBInv P A C) P =
        P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C := by
    unfold dressedCurv plabicTripWB plabicTripWBInv plabicWhiteShear plabicBlackShear
    peirce_nf hP
  exact ⟨hInv, hMC, hConnPlus, hConnMinus, hCurvV,
    hBruhatDef, hBruhatEq, hBruhatIdem, hBruhatChart⟩

/-- **Theorem 12.7 (`stage_D25_dressing_field_method_cocycle_and_brst_master_synthesis`):**
Master synthesis of the 5-stage causal poset (`F₁ → F₅`) of the non-commutative Dressing
Field Method over any `[Ring B]`:
1. **`F₁` (Non-Abelian 1-Cocycle Chain Rule):**
   `maurerCartanCocycle d (U * Ξ) (Ξ_inv * U_inv) = Ξ_inv * maurerCartanCocycle d U U_inv * Ξ + maurerCartanCocycle d Ξ Ξ_inv`;
2. **`F₂` (Exact Gauge Invariance of Dressed Connection, Curvature & Matter States):**
   `dressedConn`, `dressedCurv`, and `dressedState` are strictly invariant under
   `(U, U_inv) ↦ (Γ_inv * U, U_inv * Γ)` and `(A, F, φ) ↦ (A^Γ, F^Γ, φ^Γ)`;
3. **`F₃` (Dressed BRST Ghost Vanishing `C_ghost^U = 0`):**
   `dressedGhost δ_brst U U_inv (brstGhostFromDressing δ_brst U U_inv) = 0`;
4. **`F₄` (Relational Frame Transformations of the Second Kind `U ↦ U * Ξ`):**
   `dressedConn d (U * Ξ) (Ξ_inv * U_inv) A = dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A)`;
5. **`F₅` (Unipotent & Bruhat–Postnikov Peirce Horizon Dressing):**
   `maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A`,
   `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C`,
   `maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C) = genPhi P A C - genSig P A C - genV P A C * coneMinus P C`,
   and `dressedCurv (plabicTripWB P A C) (plabicTripWBInv P A C) P = P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C`. -/
theorem stage_D25_dressing_field_method_cocycle_and_brst_master_synthesis
    (d δ_brst : B → B) {P U U_inv Γ Γ_inv Ξ Ξ_inv : B}
    (hP : P * P = P)
    (hLeibΓ : d (Γ * (Γ_inv * U)) = d Γ * (Γ_inv * U) + Γ * d (Γ_inv * U))
    (hLeibΞ : d (U * Ξ) = d U * Ξ + U * d Ξ)
    (hU : U_inv * U = 1) (hΓ1 : Γ_inv * Γ = 1) (hΓ2 : Γ * Γ_inv = 1)
    (A C F φ : B) :
    maurerCartanCocycle d (U * Ξ) (Ξ_inv * U_inv) =
      Ξ_inv * maurerCartanCocycle d U U_inv * Ξ + maurerCartanCocycle d Ξ Ξ_inv ∧
    dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) =
      dressedConn d U U_inv A ∧
    dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F) =
      dressedCurv U U_inv F ∧
    dressedState (U_inv * Γ) (dressedState Γ_inv φ) =
      dressedState U_inv φ ∧
    dressedGhost δ_brst U U_inv (brstGhostFromDressing δ_brst U U_inv) = 0 ∧
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A =
      dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A) ∧
    maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C ∧
    maurerCartanCocycle (comm P) (plabicTripWB P A C) (plabicTripWBInv P A C) =
      genPhi P A C - genSig P A C - genV P A C * coneMinus P C ∧
    dressedCurv (plabicTripWB P A C) (plabicTripWBInv P A C) P =
      P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C := by
  rcases maurer_cartan_cocycle_and_composition d hLeibΞ hU A with ⟨hC1, hC2⟩
  rcases dressed_fields_exact_gauge_invariance d hLeibΓ hΓ1 hΓ2 A F φ with ⟨hG1, hG2, hG3⟩
  have hGhost := dressed_brst_ghost_vanishes δ_brst hU
  rcases peirce_horizon_unipotent_and_bruhat_dressing hP A C with
    ⟨_, hP2, _, _, hP5, _, hP7, _, hP9⟩
  exact ⟨hC1, hG1, hG2, hG3, hGhost, hC2.symm, hP2, hP5, hP7, hP9⟩

/-- **Theorem 12.8 (`limit_stage_D25_dressing_field_and_bruhat_cocycle_bridge`):**
Transports the Stage `D₂₅` unipotent and Bruhat–Postnikov dressing field package across
the $2^n \times 2^n$ tensor-tower bonding maps `bondMap stageBond n m hnm : Stage n →+* Stage m`
and canonical colimit embeddings `ofStage n : Stage n →+* Limit` into the inductive
colimit `Limit`. -/
theorem limit_stage_D25_dressing_field_and_bruhat_cocycle_bridge
    {P : ℕ → ∀ n, Stage n} {A C : ∀ n, Stage n}
    {Pinf Ainf Cinf : Limit}
    (start : ℕ)
    (hP_stage : ∀ n, start ≤ n → P n n * P n n = P n n)
    (hP_lim : ∀ n, start ≤ n → ofStage n (P n n) = Pinf)
    (hA_lim : ∀ n, start ≤ n → ofStage n (A n) = Ainf)
    (hC_lim : ∀ n, start ≤ n → ofStage n (C n) = Cinf) :
    Pinf * Pinf = Pinf ∧
    (∀ n, start ≤ n →
      ofStage n
          (maurerCartanCocycle (comm (P n n))
            (1 + conePlus (P n n) (A n)) (1 - conePlus (P n n) (A n))) =
        conePlus Pinf Ainf ∧
      ofStage n
          (dressedConn (comm (P n n))
            (1 + conePlus (P n n) (A n)) (1 - conePlus (P n n) (A n)) (P n n)) =
        Pinf + (2 : ℤ) • conePlus Pinf Ainf ∧
      ofStage n
          (dressedCurv
            (1 + conePlus (P n n) (A n)) (1 - conePlus (P n n) (A n))
            (genV (P n n) (A n) (C n))) =
        genV Pinf Ainf Cinf ∧
      ofStage n
          (maurerCartanCocycle (comm (P n n))
            (plabicTripWB (P n n) (A n) (C n)) (plabicTripWBInv (P n n) (A n) (C n))) =
        genPhi Pinf Ainf Cinf - genSig Pinf Ainf Cinf -
          genV Pinf Ainf Cinf * coneMinus Pinf Cinf ∧
      ofStage n
          (dressedCurv
            (plabicTripWB (P n n) (A n) (C n)) (plabicTripWBInv (P n n) (A n) (C n))
            (P n n)) =
        Pinf + genPhi Pinf Ainf Cinf - genSig Pinf Ainf Cinf -
          genV Pinf Ainf Cinf * coneMinus Pinf Cinf) ∧
    maurerCartanCocycle (comm Pinf) (1 + conePlus Pinf Ainf) (1 - conePlus Pinf Ainf) =
      conePlus Pinf Ainf ∧
    dressedConn (comm Pinf) (1 + conePlus Pinf Ainf) (1 - conePlus Pinf Ainf) Pinf =
      Pinf + (2 : ℤ) • conePlus Pinf Ainf ∧
    dressedCurv (1 + conePlus Pinf Ainf) (1 - conePlus Pinf Ainf) (genV Pinf Ainf Cinf) =
      genV Pinf Ainf Cinf ∧
    maurerCartanCocycle (comm Pinf) (plabicTripWB Pinf Ainf Cinf) (plabicTripWBInv Pinf Ainf Cinf) =
      genPhi Pinf Ainf Cinf - genSig Pinf Ainf Cinf -
        genV Pinf Ainf Cinf * coneMinus Pinf Cinf ∧
    idempotencyDefect
        (Pinf + maurerCartanCocycle (comm Pinf)
          (plabicTripWB Pinf Ainf Cinf) (plabicTripWBInv Pinf Ainf Cinf)) = 0 ∧
    dressedCurv (plabicTripWB Pinf Ainf Cinf) (plabicTripWBInv Pinf Ainf Cinf) Pinf =
      Pinf + genPhi Pinf Ainf Cinf - genSig Pinf Ainf Cinf -
        genV Pinf Ainf Cinf * coneMinus Pinf Cinf := by
  have hPinf : Pinf * Pinf = Pinf := by
    have h0 : start ≤ start := le_rfl
    rw [← hP_lim start h0, ← map_mul, hP_stage start h0]
  have hStage :
      ∀ n, start ≤ n →
        ofStage n
            (maurerCartanCocycle (comm (P n n))
              (1 + conePlus (P n n) (A n)) (1 - conePlus (P n n) (A n))) =
          conePlus Pinf Ainf ∧
        ofStage n
            (dressedConn (comm (P n n))
              (1 + conePlus (P n n) (A n)) (1 - conePlus (P n n) (A n)) (P n n)) =
          Pinf + (2 : ℤ) • conePlus Pinf Ainf ∧
        ofStage n
            (dressedCurv
              (1 + conePlus (P n n) (A n)) (1 - conePlus (P n n) (A n))
              (genV (P n n) (A n) (C n))) =
          genV Pinf Ainf Cinf ∧
        ofStage n
            (maurerCartanCocycle (comm (P n n))
              (plabicTripWB (P n n) (A n) (C n)) (plabicTripWBInv (P n n) (A n) (C n))) =
          genPhi Pinf Ainf Cinf - genSig Pinf Ainf Cinf -
            genV Pinf Ainf Cinf * coneMinus Pinf Cinf ∧
        ofStage n
            (dressedCurv
              (plabicTripWB (P n n) (A n) (C n)) (plabicTripWBInv (P n n) (A n) (C n))
              (P n n)) =
          Pinf + genPhi Pinf Ainf Cinf - genSig Pinf Ainf Cinf -
            genV Pinf Ainf Cinf * coneMinus Pinf Cinf := by
    intro n hn
    have hPn := hP_stage n hn
    rcases peirce_horizon_unipotent_and_bruhat_dressing hPn (A n) (C n) with
      ⟨_, hMCn, hConnn, _, hCurvVn, _, hBruhatEqn, _, hBruhatChartn⟩
    have hMapConeP : ofStage n (conePlus (P n n) (A n)) = conePlus Pinf Ainf := by
      rw [map_conePlus, hP_lim n hn, hA_lim n hn]
    have hMapConeM : ofStage n (coneMinus (P n n) (C n)) = coneMinus Pinf Cinf := by
      rw [map_coneMinus, hP_lim n hn, hC_lim n hn]
    have hMapPhi : ofStage n (genPhi (P n n) (A n) (C n)) = genPhi Pinf Ainf Cinf := by
      rw [map_genPhi, hP_lim n hn, hA_lim n hn, hC_lim n hn]
    have hMapSig : ofStage n (genSig (P n n) (A n) (C n)) = genSig Pinf Ainf Cinf := by
      rw [map_genSig, hP_lim n hn, hA_lim n hn, hC_lim n hn]
    have hMapV : ofStage n (genV (P n n) (A n) (C n)) = genV Pinf Ainf Cinf := by
      rw [map_genV, hP_lim n hn, hC_lim n hn, hA_lim n hn]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hMCn, hMapConeP]
    · rw [hConnn, map_add, map_zsmul, hP_lim n hn, hMapConeP]
    · rw [hCurvVn, hMapV]
    · rw [hBruhatEqn, map_sub, map_sub, map_mul, hMapPhi, hMapSig, hMapV, hMapConeM]
    · rw [hBruhatChartn, map_sub, map_sub, map_add, map_mul,
        hP_lim n hn, hMapPhi, hMapSig, hMapV, hMapConeM]
  rcases peirce_horizon_unipotent_and_bruhat_dressing hPinf Ainf Cinf with
    ⟨_, hMCinf, hConninf, _, hCurvVinf, _, hBruhatEqinf, hBruhatIdeminf, hBruhatChartinf⟩
  exact ⟨hPinf, hStage, hMCinf, hConninf, hCurvVinf,
    hBruhatEqinf, hBruhatIdeminf, hBruhatChartinf⟩

/-- **Archetype `F₂`/`F₃` (`relationalPairing`):**
Relational point-coincidence pairing `star Ψ₁ * F * Ψ₂` over `[Ring B] [StarRing B]`. -/
def relationalPairing [StarRing B] (Ψ₁ F Ψ₂ : B) : B :=
  star Ψ₁ * F * Ψ₂

/-- **Archetype `F₄` (`brstGhostFull`, `brstGhostPartial`):**
- `brstGhostFull δ_brst U U_inv = -(δ_brst U * U_inv)` (full gauge group reduction),
- `brstGhostPartial δ_brst U₁ U₁_inv C_res = -(δ_brst U₁ * U₁_inv) + U₁ * C_res * U₁_inv`
  (partial normal-subgroup reduction leaving residual ghost `C_res`). -/
def brstGhostFull (δ_brst : B → B) (U U_inv : B) : B :=
  -(δ_brst U * U_inv)

def brstGhostPartial (δ_brst : B → B) (U₁ U₁_inv C_res : B) : B :=
  -(δ_brst U₁ * U₁_inv) + U₁ * C_res * U₁_inv

/-- **Archetype `F₅` (`connectionShiftCocycle`):**
Finite gauge/frame shift 1-cocycle `dressedConn d Γ Γ_inv A - A`. -/
def connectionShiftCocycle (d : B → B) (Γ Γ_inv A : B) : B :=
  dressedConn d Γ Γ_inv A - A

/-- **Theorem 12.9 (`point_coincidence_gauge_invariance`, Archetype `F₂`):**
Under a gauge transformation `Γ` (`Γ_inv * Γ = 1`, `Γ * Γ_inv = 1`) where `U^Γ = Γ_inv * U`
and `(U^Γ)_inv = U_inv * Γ`:
1. `(A^Γ)^{U^Γ} = A^U`, `(F^Γ)^{U^Γ} = F^U`, and `(Ψ^Γ)^{U^Γ} = Ψ^U`.
2. Consequently, the dressed point-coincidence pairing
   `relationalPairing (Ψ₁^U) (F^U) (Ψ₂^U)` is strictly gauge-invariant. -/
theorem point_coincidence_gauge_invariance [StarRing B]
    (d : B → B) {U U_inv Γ Γ_inv : B}
    (hLeib : d (Γ * (Γ_inv * U)) = d Γ * (Γ_inv * U) + Γ * d (Γ_inv * U))
    (hΓ1 : Γ_inv * Γ = 1) (hΓ2 : Γ * Γ_inv = 1) (A F Ψ₁ Ψ₂ : B) :
    dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) =
      dressedConn d U U_inv A ∧
    dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F) =
      dressedCurv U U_inv F ∧
    dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₁) =
      dressedState U_inv Ψ₁ ∧
    relationalPairing
      (dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₁))
      (dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F))
      (dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₂)) =
      relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂) := by
  rcases dressed_fields_exact_gauge_invariance d (U_inv := U_inv) hLeib hΓ1 hΓ2 A F Ψ₁ with
    ⟨hConn, hCurv, hState1⟩
  have hState2 := (dressed_fields_exact_gauge_invariance d (U_inv := U_inv) hLeib hΓ1 hΓ2 A F Ψ₂).2.2
  refine ⟨hConn, hCurv, hState1, ?_⟩
  rw [hState1, hState2, hCurv]

/-- **Theorem 12.10 (`quantum_reference_frame_switching_of_second_kind`, Archetype `F₃`):**
Under a change of physical reference frame `U ↦ U * Ξ` (with inverse `Ξ_inv * U_inv` where `U_inv * U = 1`):
1. `dressedConn d (U * Ξ) (Ξ_inv * U_inv) A = dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A)`.
2. `dressedCurv (U * Ξ) (Ξ_inv * U_inv) F = dressedCurv Ξ Ξ_inv (dressedCurv U U_inv F)`.
3. `dressedState (Ξ_inv * U_inv) Ψ₁ = dressedState Ξ_inv (dressedState U_inv Ψ₁)`.
4. **Unitary Quantum Reference Frame Equivalence (`star Ξ_inv = Ξ` and `Ξ * Ξ_inv = 1`):**
   Switching between two unitary quantum reference frames preserves the relational measurement
   pairing identically:
   `relationalPairing (dressedState (Ξ_inv * U_inv) Ψ₁) (dressedCurv (U * Ξ) (Ξ_inv * U_inv) F) (dressedState (Ξ_inv * U_inv) Ψ₂) =`
   `relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂)`. -/
theorem quantum_reference_frame_switching_of_second_kind [StarRing B]
    (d : B → B) {U U_inv Ξ Ξ_inv : B}
    (hLeib : d (U * Ξ) = d U * Ξ + U * d Ξ)
    (hU : U_inv * U = 1) (hΞ : Ξ * Ξ_inv = 1) (hΞunitary : star Ξ_inv = Ξ)
    (A F Ψ₁ Ψ₂ : B) :
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A =
      dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A) ∧
    dressedCurv (U * Ξ) (Ξ_inv * U_inv) F =
      dressedCurv Ξ Ξ_inv (dressedCurv U U_inv F) ∧
    dressedState (Ξ_inv * U_inv) Ψ₁ =
      dressedState Ξ_inv (dressedState U_inv Ψ₁) ∧
    relationalPairing
      (dressedState (Ξ_inv * U_inv) Ψ₁)
      (dressedCurv (U * Ξ) (Ξ_inv * U_inv) F)
      (dressedState (Ξ_inv * U_inv) Ψ₂) =
      relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂) := by
  rcases frame_transformation_of_second_kind d (Ξ_inv := Ξ_inv) hLeib hU A F Ψ₁ with
    ⟨hConn, hCurv, hState1⟩
  have hState2 := (frame_transformation_of_second_kind d (Ξ_inv := Ξ_inv) hLeib hU A F Ψ₂).2.2
  refine ⟨hConn, hCurv, hState1, ?_⟩
  rw [hState1, hState2, hCurv]
  unfold relationalPairing dressedState dressedCurv
  rw [star_mul, hΞunitary]
  calc (star (U_inv * Ψ₁) * Ξ) * (Ξ_inv * (U_inv * F * U) * Ξ) * (Ξ_inv * (U_inv * Ψ₂))
    _ = star (U_inv * Ψ₁) * (Ξ * Ξ_inv) * (U_inv * F * U) * (Ξ * Ξ_inv) * (U_inv * Ψ₂) := by
        simp only [mul_assoc]
    _ = star (U_inv * Ψ₁) * (U_inv * F * U) * (U_inv * Ψ₂) := by
        rw [hΞ, mul_one, mul_one]

/-- **Theorem 12.11 (`full_and_partial_brst_ghost_reduction`, Archetype `F₄`):**
Let `δ_brst : B → B` be a BRST variation.
1. **Full Symmetry Reduction:**
   `dressedGhost δ_brst U U_inv (brstGhostFull δ_brst U U_inv) = 0`.
2. **Partial Subgroup Reduction:**
   `dressedGhost δ_brst U₁ U₁_inv (brstGhostPartial δ_brst U₁ U₁_inv C_res) = C_res`. -/
theorem full_and_partial_brst_ghost_reduction
    (δ_brst : B → B) {U U_inv U₁ U₁_inv : B}
    (hU : U_inv * U = 1) (hU₁ : U₁_inv * U₁ = 1) (C_res : B) :
    dressedGhost δ_brst U U_inv (brstGhostFull δ_brst U U_inv) = 0 ∧
    dressedGhost δ_brst U₁ U₁_inv (brstGhostPartial δ_brst U₁ U₁_inv C_res) = C_res := by
  have hFull : dressedGhost δ_brst U U_inv (brstGhostFull δ_brst U U_inv) = 0 :=
    dressed_brst_ghost_vanishes δ_brst hU
  refine ⟨hFull, ?_⟩
  unfold dressedGhost brstGhostPartial
  rw [mul_add, add_mul]
  have hSimp1 : U₁_inv * -(δ_brst U₁ * U₁_inv) * U₁ = -(U₁_inv * δ_brst U₁) := by
    calc U₁_inv * -(δ_brst U₁ * U₁_inv) * U₁
      _ = -(U₁_inv * δ_brst U₁ * (U₁_inv * U₁)) := by simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(U₁_inv * δ_brst U₁) := by rw [hU₁, mul_one]
  have hSimp2 : U₁_inv * (U₁ * C_res * U₁_inv) * U₁ = C_res := by
    calc U₁_inv * (U₁ * C_res * U₁_inv) * U₁
      _ = (U₁_inv * U₁) * C_res * (U₁_inv * U₁) := by simp only [mul_assoc]
      _ = C_res := by rw [hU₁, one_mul, mul_one]
  rw [hSimp1, hSimp2]
  abel

/-- **Theorem 12.12 (`anomaly_cancellation_and_second_kind_resurgence`, Archetype `F₅`):**
1. **Gauge Anomaly Cancellation:**
   `dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) - dressedConn d U U_inv A = 0`.
2. **Resurgence Under Frame Transformations of the 2nd Kind:**
   `dressedConn d (U * Ξ) (Ξ_inv * U_inv) A - dressedConn d U U_inv A =`
   `connectionShiftCocycle d Ξ Ξ_inv (dressedConn d U U_inv A)`. -/
theorem anomaly_cancellation_and_second_kind_resurgence
    (d : B → B) {U U_inv Γ Γ_inv Ξ Ξ_inv : B}
    (hLeibΓ : d (Γ * (Γ_inv * U)) = d Γ * (Γ_inv * U) + Γ * d (Γ_inv * U))
    (hLeibΞ : d (U * Ξ) = d U * Ξ + U * d Ξ)
    (hU : U_inv * U = 1) (hΓ1 : Γ_inv * Γ = 1) (hΓ2 : Γ * Γ_inv = 1) (A : B) :
    dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) -
      dressedConn d U U_inv A = 0 ∧
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A - dressedConn d U U_inv A =
      connectionShiftCocycle d Ξ Ξ_inv (dressedConn d U U_inv A) := by
  have hInv := (dressed_fields_exact_gauge_invariance d (U_inv := U_inv) hLeibΓ hΓ1 hΓ2 A 0 0).1
  have hComp := (maurer_cartan_cocycle_and_composition d (Γ_inv := Ξ_inv) hLeibΞ hU A).2.symm
  refine ⟨by rw [hInv, sub_self], ?_⟩
  unfold connectionShiftCocycle
  rw [hComp]

/-- **Theorem 12.13 (`gribov_free_peirce_horizon_dressing`, Archetype `F₆`):**
For any idempotent `P` (`P * P = P`) and any `A, C : B`, the internal horizon dressing field
`U = 1 + conePlus P A = finiteGreen (conePlus P A) 2` is globally invertible by polynomial
nilpotency (`U_inv = 1 - conePlus P A = finiteGreen (-conePlus P A) 2`), satisfies
`maurerCartanCocycle (comm P) U U_inv = conePlus P A`, and leaves the horizon metric
`genV P A C` strictly invariant (`dressedCurv U U_inv (genV P A C) = genV P A C`). -/
theorem gribov_free_peirce_horizon_dressing {P : B} (hP : P * P = P) (A C : B) :
    (1 - conePlus P A) * (1 + conePlus P A) = 1 ∧
    maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A ∧
    dressedConn (comm P) (1 + conePlus P A) (1 - conePlus P A) P =
      P + (2 : ℤ) • conePlus P A ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C := by
  rcases peirce_horizon_unipotent_and_bruhat_dressing hP A C with
    ⟨hInv, hMC, hConn, _, hCurvV, _, _, _, _⟩
  exact ⟨hInv, hMC, hConn, hCurvV⟩

/-- **Theorem 12.14 (`stage_D26_relational_dressing_frame_switching_and_brst_master_synthesis`):**
Master synthesis of Stage `D₂₆` (`F₁ → F₆`): Non-Commutative Relational Dressing Field,
Point-Coincidence Invariance, Quantum Reference Frame Switching of the 2nd Kind,
Full/Partial BRST Ghost Reduction, Anomaly Resurgence & Gribov-Free Unipotent Peirce Horizon Dressing. -/
theorem stage_D26_relational_dressing_frame_switching_and_brst_master_synthesis [StarRing B]
    (d δ_brst : B → B) {P U U_inv U₁ U₁_inv Γ Γ_inv Ξ Ξ_inv : B}
    (hP : P * P = P)
    (hLeibΓ : d (Γ * (Γ_inv * U)) = d Γ * (Γ_inv * U) + Γ * d (Γ_inv * U))
    (hLeibΞ : d (U * Ξ) = d U * Ξ + U * d Ξ)
    (hU : U_inv * U = 1) (hU₁ : U₁_inv * U₁ = 1)
    (hΓ1 : Γ_inv * Γ = 1) (hΓ2 : Γ * Γ_inv = 1)
    (hΞ : Ξ * Ξ_inv = 1) (hΞunitary : star Ξ_inv = Ξ)
    (A C F Ψ₁ Ψ₂ C_res : B) :
    -- 1. Non-Abelian 1-Cocycle Chain Rule (F₁):
    maurerCartanCocycle d (U * Ξ) (Ξ_inv * U_inv) =
      Ξ_inv * maurerCartanCocycle d U U_inv * Ξ + maurerCartanCocycle d Ξ Ξ_inv ∧
    -- 2. Point-Coincidence Gauge Invariance of Dressed Fields & Relational Pairings (F₂):
    dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) =
      dressedConn d U U_inv A ∧
    relationalPairing
      (dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₁))
      (dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F))
      (dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₂)) =
      relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂) ∧
    -- 3. Quantum Reference Frame Switching (2nd Kind `U ↦ U Ξ`) & Unitary Pairing Invariance (F₃):
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A =
      dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A) ∧
    relationalPairing
      (dressedState (Ξ_inv * U_inv) Ψ₁)
      (dressedCurv (U * Ξ) (Ξ_inv * U_inv) F)
      (dressedState (Ξ_inv * U_inv) Ψ₂) =
      relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂) ∧
    -- 4. Full BRST Ghost Vanishing vs. Partial Subgroup Ghost Reduction (F₄):
    dressedGhost δ_brst U U_inv (brstGhostFull δ_brst U U_inv) = 0 ∧
    dressedGhost δ_brst U₁ U₁_inv (brstGhostPartial δ_brst U₁ U₁_inv C_res) = C_res ∧
    -- 5. Anomaly Cancellation on Dressed Connections & 2nd-Kind Resurgence (F₅):
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A - dressedConn d U U_inv A =
      connectionShiftCocycle d Ξ Ξ_inv (dressedConn d U U_inv A) ∧
    -- 6. Gribov-Free Unipotent Peirce Horizon Dressing (F₆):
    maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C := by
  rcases maurer_cartan_cocycle_and_composition d (Γ_inv := Ξ_inv) hLeibΞ hU A with ⟨hC1, _⟩
  rcases point_coincidence_gauge_invariance d (U_inv := U_inv) hLeibΓ hΓ1 hΓ2 A F Ψ₁ Ψ₂ with
    ⟨hPC1, _, _, hPC4⟩
  rcases quantum_reference_frame_switching_of_second_kind d hLeibΞ hU hΞ hΞunitary A F Ψ₁ Ψ₂ with
    ⟨hQF1, _, _, hQF4⟩
  rcases full_and_partial_brst_ghost_reduction δ_brst hU hU₁ C_res with ⟨hB1, hB2⟩
  rcases anomaly_cancellation_and_second_kind_resurgence d (Ξ_inv := Ξ_inv) hLeibΓ hLeibΞ hU hΓ1 hΓ2 A with
    ⟨_, hAnom2⟩
  rcases gribov_free_peirce_horizon_dressing hP A C with ⟨_, hP2, _, hP4⟩
  exact ⟨hC1, hPC1, hPC4, hQF1, hQF4, hB1, hB2, hAnom2, hP2, hP4⟩

/-!
## 13. Stage `D₂₆` × Quantum Affine `T`-System, Cluster Adjacency & Dressed Symbol Alphabet Bridge

Bridges Stage `D₂₆` (Non-Commutative Relational Dressing Field Method, Point-Coincidence Invariance,
and Unipotent/Bruhat–Postnikov Horizon Dressing) directly to the quantum affine Kirillov–Reshetikhin
`T`-system (Cassini–Hirota bilinear cluster exchange relations), Grassmannian plabic incidence, and
scattering-amplitude algebraic square-root symbol letters (`radicalLetterPlus`, `radicalLetterMinus`):
1. **All-`m` Non-Commutative Kirillov–Reshetikhin `T`-System (`all_m_kirillov_reshetikhin_t_system_polygon_and_eisenstein`):**
   For every `m : ℕ` in any associative ring `[Ring B]` with idempotent `P * P = P`:
   - **Golden / Polygon `T`-System Exchange:**
     `polygonFibSeq P A C (m + 1) * polygonFibSeq P A C (m + 1) - polygonFibSeq P A C (m + 2) * polygonFibSeq P A C m = (-genV P A C) ^ m`,
   - **Eisenstein / Root-of-Unity `T`-System Exchange:**
     `eisensteinSeq P A C (m + 1) * eisensteinSeq P A C (m + 1) - eisensteinSeq P A C (m + 2) * eisensteinSeq P A C m = (genV P A C) ^ m`;
2. **All-`m` Horizon-Dressing Invariance of Kirillov–Reshetikhin Cluster Variables (`dressedCurv_polygonFibSeq_and_eisensteinSeq_of_genV_fixed`):**
   Whenever a dressing field `(U, U_inv)` (`U * U_inv = 1`, `U_inv * U = 1`) preserves the horizon
   scale `genV P A C` (`dressedCurv U U_inv (genV P A C) = genV P A C`, which holds unconditionally
   for both the Gribov-free unipotent horizon dressing `U = 1 + conePlus P A` and the Bruhat–Postnikov
   two-cone dressing `U = plabicTripWB P A C`), every Kirillov–Reshetikhin `T`-system operator
   `polygonFibSeq P A C m` and `eisensteinSeq P A C m` is strictly dressing-invariant for all `m : ℕ`;
3. **Dressed Square-Root Symbol Letters, Universal Cluster Adjacency `{R₊^U, R₋^U} = 2`, & Dressed Plabic Incidence (`dressed_kirillov_reshetikhin_t_system_and_symbol_alphabet_master_bridge`):**
   Under any two-sided invertible dressing field `(U, U_inv)`:
   - `dressedCurv U U_inv (radicalLetterPlus P A C) * dressedCurv U U_inv (radicalLetterPlus P A C) = 1 + (4 : ℤ) • dressedCurv U U_inv (genV P A C)`,
   - `dressedCurv U U_inv (radicalLetterMinus P A C) * dressedCurv U U_inv (radicalLetterMinus P A C) = 1 - (4 : ℤ) • dressedCurv U U_inv (genV P A C)`,
   - `anticomm (dressedCurv U U_inv (radicalLetterPlus P A C)) (dressedCurv U U_inv (radicalLetterMinus P A C)) = (2 : ℤ) • (1 : B)`,
   - `dressedCurv U U_inv (plabicBoundaryOp P A C) * dressedState U_inv (plabicTwistorSol P A C Z) = 0`,
   - and under `U = 1 + conePlus P A` (`U_inv = 1 - conePlus P A`), the dressed square-root letters
     satisfy the exact undressed discriminant equations `(R_±^U)² = 1 ± 4 • genV P A C` while shifting
     by the nilpotent horizon cocycle:
     `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (radicalLetterPlus P A C) = radicalLetterPlus P A C + (2 : ℤ) • conePlus P A - (2 : ℤ) • genSig P A C - (2 : ℤ) • (genV P A C * conePlus P A)`.
-/

/-- **Theorem 13.1 (`all_m_kirillov_reshetikhin_t_system_polygon_and_eisenstein`):**
All-`m` non-commutative Kirillov–Reshetikhin `T`-system (Cassini–Hirota bilinear cluster exchange)
for the Golden/Polygon sequence `polygonFibSeq P A C` and the Eisenstein/Chebyshev sequence
`eisensteinSeq P A C` over any `[Ring B]` with idempotent `P` (`P * P = P`). -/
theorem all_m_kirillov_reshetikhin_t_system_polygon_and_eisenstein
    (P A C : B) (m : ℕ) :
    polygonFibSeq P A C (m + 1) * polygonFibSeq P A C (m + 1) -
      polygonFibSeq P A C (m + 2) * polygonFibSeq P A C m =
      (-genV P A C) ^ m ∧
    eisensteinSeq P A C (m + 1) * eisensteinSeq P A C (m + 1) -
      eisensteinSeq P A C (m + 2) * eisensteinSeq P A C m =
      (genV P A C) ^ m := by
  induction m with
  | zero =>
    simp [polygonFibSeq, eisensteinSeq]
  | succ k ih =>
    rcases ih with ⟨ihPoly, ihEis⟩
    have hCommPoly :
        polygonFibSeq P A C (k + 2) * genV P A C =
          genV P A C * polygonFibSeq P A C (k + 2) :=
      polygonFibSeq_comm_of_genV_comm P A C (genV P A C) rfl (k + 2)
    have hCommEis :
        eisensteinSeq P A C (k + 2) * genV P A C =
          genV P A C * eisensteinSeq P A C (k + 2) :=
      eisensteinSeq_comm_of_genV_comm P A C (genV P A C) rfl (k + 2)
    refine ⟨?_, ?_⟩
    · have hStep1 :
          polygonFibSeq P A C (k + 2) * polygonFibSeq P A C (k + 2) -
            polygonFibSeq P A C (k + 3) * polygonFibSeq P A C (k + 1) =
          polygonFibSeq P A C (k + 2) *
            (polygonFibSeq P A C (k + 1) + genV P A C * polygonFibSeq P A C k) -
          (polygonFibSeq P A C (k + 2) + genV P A C * polygonFibSeq P A C (k + 1)) *
            polygonFibSeq P A C (k + 1) := by
        rw [show polygonFibSeq P A C (k + 3) =
              polygonFibSeq P A C (k + 2) + genV P A C * polygonFibSeq P A C (k + 1) from rfl]
        conv_lhs =>
           arg 1
           arg 2
           rw [show polygonFibSeq P A C (k + 2) =
                polygonFibSeq P A C (k + 1) + genV P A C * polygonFibSeq P A C k from rfl]
      have hCommTerm :
          polygonFibSeq P A C (k + 2) * (genV P A C * polygonFibSeq P A C k) =
            genV P A C * (polygonFibSeq P A C (k + 2) * polygonFibSeq P A C k) := by
        rw [← mul_assoc, hCommPoly, mul_assoc]
      calc
        polygonFibSeq P A C (k + 2) * polygonFibSeq P A C (k + 2) -
            polygonFibSeq P A C (k + 3) * polygonFibSeq P A C (k + 1)
            = (polygonFibSeq P A C (k + 2) * polygonFibSeq P A C (k + 1) +
                polygonFibSeq P A C (k + 2) * (genV P A C * polygonFibSeq P A C k)) -
              (polygonFibSeq P A C (k + 2) * polygonFibSeq P A C (k + 1) +
                genV P A C * (polygonFibSeq P A C (k + 1) * polygonFibSeq P A C (k + 1))) := by
              rw [hStep1, mul_add, add_mul, mul_assoc]
        _ = genV P A C * (polygonFibSeq P A C (k + 2) * polygonFibSeq P A C k) -
              genV P A C * (polygonFibSeq P A C (k + 1) * polygonFibSeq P A C (k + 1)) := by
              rw [hCommTerm]
              abel
        _ = (-genV P A C) *
              (polygonFibSeq P A C (k + 1) * polygonFibSeq P A C (k + 1) -
                polygonFibSeq P A C (k + 2) * polygonFibSeq P A C k) := by
              noncomm_ring
        _ = (-genV P A C) ^ (k + 1) := by
              rw [ihPoly, pow_succ']
    · have hStep2 :
          eisensteinSeq P A C (k + 2) * eisensteinSeq P A C (k + 2) -
            eisensteinSeq P A C (k + 3) * eisensteinSeq P A C (k + 1) =
          eisensteinSeq P A C (k + 2) *
            (eisensteinSeq P A C (k + 1) - genV P A C * eisensteinSeq P A C k) -
          (eisensteinSeq P A C (k + 2) - genV P A C * eisensteinSeq P A C (k + 1)) *
            eisensteinSeq P A C (k + 1) := by
        rw [show eisensteinSeq P A C (k + 3) =
              eisensteinSeq P A C (k + 2) - genV P A C * eisensteinSeq P A C (k + 1) from rfl]
        conv_lhs =>
          arg 1
          arg 2
          rw [show eisensteinSeq P A C (k + 2) =
                eisensteinSeq P A C (k + 1) - genV P A C * eisensteinSeq P A C k from rfl]
      have hCommTermE :
          eisensteinSeq P A C (k + 2) * (genV P A C * eisensteinSeq P A C k) =
            genV P A C * (eisensteinSeq P A C (k + 2) * eisensteinSeq P A C k) := by
        rw [← mul_assoc, hCommEis, mul_assoc]
      calc
        eisensteinSeq P A C (k + 2) * eisensteinSeq P A C (k + 2) -
            eisensteinSeq P A C (k + 3) * eisensteinSeq P A C (k + 1)
            = (eisensteinSeq P A C (k + 2) * eisensteinSeq P A C (k + 1) -
                eisensteinSeq P A C (k + 2) * (genV P A C * eisensteinSeq P A C k)) -
              (eisensteinSeq P A C (k + 2) * eisensteinSeq P A C (k + 1) -
                genV P A C * (eisensteinSeq P A C (k + 1) * eisensteinSeq P A C (k + 1))) := by
              rw [hStep2, mul_sub, sub_mul, mul_assoc]
        _ = genV P A C * (eisensteinSeq P A C (k + 1) * eisensteinSeq P A C (k + 1)) -
              genV P A C * (eisensteinSeq P A C (k + 2) * eisensteinSeq P A C k) := by
              rw [hCommTermE]
              abel
        _ = genV P A C *
              (eisensteinSeq P A C (k + 1) * eisensteinSeq P A C (k + 1) -
                eisensteinSeq P A C (k + 2) * eisensteinSeq P A C k) := by
              noncomm_ring
        _ = (genV P A C) ^ (k + 1) := by
              rw [ihEis, pow_succ']

/-- **Theorem 13.2 (`dressedCurv_polygonFibSeq_and_eisensteinSeq_of_genV_fixed`):**
For any invertible dressing pair `(U, U_inv)` (`U * U_inv = 1`, `U_inv * U = 1`) that preserves
the Peirce–Clifford horizon scale `genV P A C` (`dressedCurv U U_inv (genV P A C) = genV P A C`),
every Kirillov–Reshetikhin `T`-system cluster variable `polygonFibSeq P A C m` and
`eisensteinSeq P A C m` is strictly invariant under `dressedCurv U U_inv` for all `m : ℕ`. -/
theorem dressedCurv_polygonFibSeq_and_eisensteinSeq_of_genV_fixed
    {U U_inv : B} (hUUinv : U * U_inv = 1) (hUinvU : U_inv * U = 1)
    (P A C : B)
    (hV : dressedCurv U U_inv (genV P A C) = genV P A C) (m : ℕ) :
    dressedCurv U U_inv (polygonFibSeq P A C m) = polygonFibSeq P A C m ∧
    dressedCurv U U_inv (eisensteinSeq P A C m) = eisensteinSeq P A C m := by
  have hAdd : ∀ X Y : B,
      dressedCurv U U_inv (X + Y) = dressedCurv U U_inv X + dressedCurv U U_inv Y := by
    intro X Y; unfold dressedCurv; noncomm_ring
  have hSub : ∀ X Y : B,
      dressedCurv U U_inv (X - Y) = dressedCurv U U_inv X - dressedCurv U U_inv Y := by
    intro X Y; unfold dressedCurv; noncomm_ring
  have hMul : ∀ X Y : B,
      dressedCurv U U_inv (X * Y) = dressedCurv U U_inv X * dressedCurv U U_inv Y := by
    intro X Y
    unfold dressedCurv
    calc U_inv * (X * Y) * U
      _ = (U_inv * X) * (U * U_inv) * (Y * U) := by rw [hUUinv, mul_one]; noncomm_ring
      _ = (U_inv * X * U) * (U_inv * Y * U) := by noncomm_ring
  have hZero : dressedCurv U U_inv 0 = 0 := by unfold dressedCurv; simp
  have hOne : dressedCurv U U_inv 1 = 1 := by
    unfold dressedCurv; rw [mul_one, hUinvU]
  induction m using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | n
    · simp [polygonFibSeq, eisensteinSeq, hZero]
    · simp [polygonFibSeq, eisensteinSeq, hOne]
    · have ih1 := ih (n + 1) (Nat.lt_succ_self (n + 1))
      have ih0 := ih n (Nat.lt_trans (Nat.lt_succ_self n) (Nat.lt_succ_self (n + 1)))
      refine ⟨?_, ?_⟩
      · change dressedCurv U U_inv
            (polygonFibSeq P A C (n + 1) + genV P A C * polygonFibSeq P A C n) =
          polygonFibSeq P A C (n + 1) + genV P A C * polygonFibSeq P A C n
        rw [hAdd, hMul, ih1.1, hV, ih0.1]
      · change dressedCurv U U_inv
            (eisensteinSeq P A C (n + 1) - genV P A C * eisensteinSeq P A C n) =
          eisensteinSeq P A C (n + 1) - genV P A C * eisensteinSeq P A C n
        rw [hSub, hMul, ih1.2, hV, ih0.2]

/-- **Theorem 13.3 (`dressed_kirillov_reshetikhin_t_system_and_symbol_alphabet_master_bridge`):**
Master synthesis bridging Stage `D₂₆` (Relational Dressing Field Method) with Quantum Affine
Kirillov–Reshetikhin `T`-Systems, Cluster Algebras, and Scattering Amplitude Symbol Letters:
1. **All-`m` Kirillov–Reshetikhin `T`-Systems & Unipotent Horizon-Dressing Invariance:**
   - `polygonFibSeq P A C (m + 1) * polygonFibSeq P A C (m + 1) - polygonFibSeq P A C (m + 2) * polygonFibSeq P A C m = (-genV P A C) ^ m`,
   - `eisensteinSeq P A C (m + 1) * eisensteinSeq P A C (m + 1) - eisensteinSeq P A C (m + 2) * eisensteinSeq P A C m = (genV P A C) ^ m`,
   - `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (polygonFibSeq P A C m) = polygonFibSeq P A C m`,
   - `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (eisensteinSeq P A C m) = eisensteinSeq P A C m`;
2. **Dressed Square-Root Symbol Letters & Universal Dressed Cluster Adjacency (`{R₊^U, R₋^U} = 2`):**
   For any two-sided invertible dressing field `(U, U_inv)` (`U * U_inv = 1`, `U_inv * U = 1`):
   - `dressedCurv U U_inv (radicalLetterPlus P A C) * dressedCurv U U_inv (radicalLetterPlus P A C) = 1 + (4 : ℤ) • dressedCurv U U_inv (genV P A C)`,
   - `dressedCurv U U_inv (radicalLetterMinus P A C) * dressedCurv U U_inv (radicalLetterMinus P A C) = 1 - (4 : ℤ) • dressedCurv U U_inv (genV P A C)`,
   - `anticomm (dressedCurv U U_inv (radicalLetterPlus P A C)) (dressedCurv U U_inv (radicalLetterMinus P A C)) = (2 : ℤ) • (1 : B)`,
   - `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (radicalLetterPlus P A C) = radicalLetterPlus P A C + (2 : ℤ) • conePlus P A - (2 : ℤ) • genSig P A C - (2 : ℤ) • (genV P A C * conePlus P A)`;
3. **Dressed Plabic Momentum-Twistor Incidence Constraint (`P_plabic^U * Z_sol^U = 0`):**
   `dressedCurv U U_inv (plabicBoundaryOp P A C) * dressedState U_inv (plabicTwistorSol P A C Z) = 0`. -/
theorem dressed_kirillov_reshetikhin_t_system_and_symbol_alphabet_master_bridge
    {P U U_inv : B} (hP : P * P = P)
    (hUUinv : U * U_inv = 1) (hUinvU : U_inv * U = 1)
    (A C Z : B) (m : ℕ) :
    (polygonFibSeq P A C (m + 1) * polygonFibSeq P A C (m + 1) -
       polygonFibSeq P A C (m + 2) * polygonFibSeq P A C m =
       (-genV P A C) ^ m ∧
     eisensteinSeq P A C (m + 1) * eisensteinSeq P A C (m + 1) -
       eisensteinSeq P A C (m + 2) * eisensteinSeq P A C m =
       (genV P A C) ^ m ∧
     dressedCurv (1 + conePlus P A) (1 - conePlus P A) (polygonFibSeq P A C m) =
       polygonFibSeq P A C m ∧
     dressedCurv (1 + conePlus P A) (1 - conePlus P A) (eisensteinSeq P A C m) =
       eisensteinSeq P A C m) ∧
    (dressedCurv U U_inv (radicalLetterPlus P A C) *
       dressedCurv U U_inv (radicalLetterPlus P A C) =
       1 + (4 : ℤ) • dressedCurv U U_inv (genV P A C) ∧
     dressedCurv U U_inv (radicalLetterMinus P A C) *
       dressedCurv U U_inv (radicalLetterMinus P A C) =
       1 - (4 : ℤ) • dressedCurv U U_inv (genV P A C) ∧
     anticomm
       (dressedCurv U U_inv (radicalLetterPlus P A C))
       (dressedCurv U U_inv (radicalLetterMinus P A C)) =
       (2 : ℤ) • (1 : B) ∧
     dressedCurv (1 + conePlus P A) (1 - conePlus P A) (radicalLetterPlus P A C) =
       radicalLetterPlus P A C + (2 : ℤ) • conePlus P A -
         (2 : ℤ) • genSig P A C - (2 : ℤ) • (genV P A C * conePlus P A)) ∧
    dressedCurv U U_inv (plabicBoundaryOp P A C) *
      dressedState U_inv (plabicTwistorSol P A C Z) = 0 := by
  rcases all_m_kirillov_reshetikhin_t_system_polygon_and_eisenstein P A C m with
    ⟨hKRPoly, hKREis⟩
  have hUnip1 : (1 + conePlus P A) * (1 - conePlus P A) = 1 := by peirce_nf hP
  have hUnip2 : (1 - conePlus P A) * (1 + conePlus P A) = 1 := by peirce_nf hP
  have hUnipV :
      dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C :=
    (gribov_free_peirce_horizon_dressing hP A C).2.2.2
  rcases dressedCurv_polygonFibSeq_and_eisensteinSeq_of_genV_fixed hUnip1 hUnip2 P A C hUnipV m with
    ⟨hInvPoly, hInvEis⟩
  have hMul : ∀ X Y : B,
      dressedCurv U U_inv X * dressedCurv U U_inv Y = dressedCurv U U_inv (X * Y) := by
    intro X Y
    unfold dressedCurv
    calc (U_inv * X * U) * (U_inv * Y * U)
      _ = (U_inv * X) * (U * U_inv) * (Y * U) := by noncomm_ring
      _ = U_inv * (X * Y) * U := by rw [hUUinv, mul_one]; noncomm_ring
  rcases operator_square_root_symbol_letters hP A C with ⟨_, _, hSqP, hSqM, _, _, _, _, _, _⟩
  have hAnti := (radical_letter_rationalization_and_adjacency hP A C).2.2.2.2.2.1
  have hPlabZero := (plabic_boundary_constraint_and_twistor_solution hP A C Z).2.2.2.2.1
  refine ⟨⟨hKRPoly, hKREis, hInvPoly, hInvEis⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hMul, hSqP]
    unfold dressedCurv
    rw [mul_add, add_mul, mul_one, hUinvU]
    simp only [mul_smul_comm, smul_mul_assoc]
  · rw [hMul, hSqM]
    unfold dressedCurv
    rw [mul_sub, sub_mul, mul_one, hUinvU]
    simp only [mul_smul_comm, smul_mul_assoc]
  · unfold anticomm
    rw [hMul, hMul]
    have hAdd :
        dressedCurv U U_inv (radicalLetterPlus P A C * radicalLetterMinus P A C) +
          dressedCurv U U_inv (radicalLetterMinus P A C * radicalLetterPlus P A C) =
        dressedCurv U U_inv (anticomm (radicalLetterPlus P A C) (radicalLetterMinus P A C)) := by
      unfold dressedCurv anticomm; noncomm_ring
    rw [hAdd, hAnti]
    unfold dressedCurv
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, hUinvU]
  · unfold dressedCurv radicalLetterPlus peirceTransfer
    peirce_nf hP
  · unfold dressedCurv dressedState
    calc (U_inv * plabicBoundaryOp P A C * U) * (U_inv * plabicTwistorSol P A C Z)
      _ = U_inv * plabicBoundaryOp P A C * (U * U_inv) * plabicTwistorSol P A C Z := by
          noncomm_ring
      _ = U_inv * (plabicBoundaryOp P A C * plabicTwistorSol P A C Z) := by
          rw [hUUinv, mul_one]; noncomm_ring
      _ = 0 := by rw [hPlabZero, mul_zero]

/-!
## 14. Stage `D₂₇` (`Q₁ → Q₅`): Quantum Affine Drinfeld Loop Currents, Dual Canonical Imaginary
Square-Root Letters, Nested Partial Flag Variety Embedding & `2ⁿ × 2ⁿ` Inductive Colimit Bridge
-/

/-- **Theorem 14.1 (`limit_stage_D27_quantum_affine_dual_canonical_and_partial_flag_bridge`):**
Transports Stage `D₂₇` (`Q₁ → Q₅`: Drinfeld new presentation loop currents, Kirillov–Reshetikhin
`T`-system bilinear exchange, dual canonical imaginary square-excess defect & four-mass-box
square-root letter, and nested partial flag variety Grassmannian corner embedding) across the
`2ⁿ × 2ⁿ` tensor-tower bonding maps `bondMap stageBond n m hnm : Stage n →+* Stage m` and into the
inductive colimit `Limit`. -/
theorem limit_stage_D27_quantum_affine_dual_canonical_and_partial_flag_bridge
    {n m : ℕ} (hnm : n ≤ m)
    {P P₁ P₂ : Stage n}
    (hP : P * P = P)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = P₁) (h21 : P₂ * P₁ = P₁)
    (A C : Stage n) (k l : ℕ) :
    let P_lim := ofStage n P
    let P₁_lim := ofStage n P₁
    let P₂_lim := ofStage n P₂
    let A_lim := ofStage n A
    let C_lim := ofStage n C
    -- 1. Multi-step bonding & colimit compatibility:
    ofStage m (bondMap stageBond n m hnm (drinfeldXPlus k P A C)) =
      ofStage n (drinfeldXPlus k P A C) ∧
    ofStage m (bondMap stageBond n m hnm (fourMassBoxSqrt P A C)) =
      ofStage n (fourMassBoxSqrt P A C) ∧
    ofStage m (bondMap stageBond n m hnm (flagEmbeddedCorner P₁ P₂ A)) =
      ofStage n (flagEmbeddedCorner P₁ P₂ A) ∧
    -- 2. Colimit Drinfeld New Presentation Loop Relations (Q₁):
    invS P_lim * drinfeldXPlus k P_lim A_lim C_lim * invS P_lim =
      -drinfeldXPlus k P_lim A_lim C_lim ∧
    comm (drinfeldXPlus k P_lim A_lim C_lim) (drinfeldXMinus l P_lim A_lim C_lim) =
      drinfeldPhiPlus (k + l) P_lim A_lim C_lim - drinfeldPhiMinus (k + l) P_lim A_lim C_lim ∧
    anticomm (drinfeldXPlus k P_lim A_lim C_lim) (drinfeldXMinus l P_lim A_lim C_lim) =
      opPow (k + l + 1) (genV P_lim A_lim C_lim) ∧
    -- 3. Colimit Kirillov–Reshetikhin `T`-System Exchange & Four-Mass-Box Square-Root Letter (Q₂–Q₄):
    krModulePlus P_lim A_lim C_lim * krModuleMinus P_lim A_lim C_lim =
      krFrozenPlus P_lim A_lim C_lim * krFrozenMinus P_lim A_lim C_lim ∧
    krModulePlus P_lim A_lim C_lim * krModuleMinus P_lim A_lim C_lim =
      1 - genV P_lim A_lim C_lim ∧
    imaginaryModuleDefect P_lim A_lim C_lim = -genV P_lim A_lim C_lim ∧
    fourMassBoxSqrt P_lim A_lim C_lim * fourMassBoxSqrt P_lim A_lim C_lim =
      fourMassBoxDisc P_lim A_lim C_lim ∧
    algSymbolFactorPlus P_lim A_lim C_lim (genV P_lim A_lim C_lim) 1 *
      algSymbolFactorMinus P_lim A_lim C_lim (genV P_lim A_lim C_lim) 1 =
      genV P_lim A_lim C_lim * genV P_lim A_lim C_lim - fourMassBoxDisc P_lim A_lim C_lim ∧
    -- 4. Colimit Nested Partial Flag Variety Grassmannian Corner Embedding (Q₅):
    flagStratumIdem P₁_lim P₂_lim * flagStratumIdem P₁_lim P₂_lim =
      flagStratumIdem P₁_lim P₂_lim ∧
    P₁_lim + flagStratumIdem P₁_lim P₂_lim + (1 - P₂_lim) = 1 ∧
    flagEmbeddedCorner P₁_lim P₂_lim A_lim = P₁_lim * A_lim * (1 - P₂_lim) ∧
    flagEmbeddedCorner P₁_lim P₂_lim A_lim = conePlus P₂_lim (P₁_lim * A_lim) := by
  dsimp only
  have hPLim : ofStage n P * ofStage n P = ofStage n P := by
    rw [← map_mul, hP]
  have h1Lim : ofStage n P₁ * ofStage n P₁ = ofStage n P₁ := by
    rw [← map_mul, h1]
  have h2Lim : ofStage n P₂ * ofStage n P₂ = ofStage n P₂ := by
    rw [← map_mul, h2]
  have h12Lim : ofStage n P₁ * ofStage n P₂ = ofStage n P₁ := by
    rw [← map_mul, h12]
  have h21Lim : ofStage n P₂ * ofStage n P₁ = ofStage n P₁ := by
    rw [← map_mul, h21]
  rcases stage_D27_quantum_affine_dual_canonical_and_partial_flag_master_synthesis
      (A := ofStage n A) (C := ofStage n C)
      hPLim h1Lim h2Lim h12Lim h21Lim k l with
    ⟨hD1, _, _, _, hD5, hD6, hK1, hK2, hI1, hI2, hI3, hF1, hF2, hF3, hF4⟩
  exact ⟨directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         hD1, hD5, hD6, hK1, hK2, hI1, hI2, hI3, hF1, hF2, hF3, hF4⟩

/-!
## 15. Stage `D₂₈` (`U₁ → U₅`): UHF Operator Algebras, Affine Heisenberg Current Modes,
Sugawara Stress-Energy Construction, Virasoro Central Defect & `2ⁿ × 2ⁿ` Inductive Colimit Bridge
-/

/-- **Theorem 15.1 (`limit_stage_D28_uhf_heisenberg_sugawara_virasoro_bridge`):**
Transports Stage `D₂₈` (`U₁ → U₅`: Chiral Parity Charge & Current of the Chiral Parity Charge,
Affine Heisenberg Current Mode Algebra, Sugawara Quadratic Stress-Energy Construction & Conformal
Commutators, Virasoro Chiral Splitting, Central Defect Additivity & Mode Closure, and All-Scale
UHF Inductive Tower Invariance) across the `2ⁿ × 2ⁿ` tensor-tower bonding maps
`bondMap stageBond n m hnm : Stage n →+* Stage m` and into the inductive colimit `Limit`. -/
theorem limit_stage_D28_uhf_heisenberg_sugawara_virasoro_bridge
    {n m : ℕ} (hnm : n ≤ m)
    {P : Stage n} (hP : P * P = P)
    (A C : Stage n) (r k : ℕ) :
    let P_lim := ofStage n P
    let A_lim := ofStage n A
    let C_lim := ofStage n C
    -- 1. Multi-step bonding & colimit compatibility:
    ofStage m (bondMap stageBond n m hnm (heisenbergSourceMode r P A C)) =
      ofStage n (heisenbergSourceMode r P A C) ∧
    ofStage m (bondMap stageBond n m hnm (sugawaraTensor P A C)) =
      ofStage n (sugawaraTensor P A C) ∧
    ofStage m (bondMap stageBond n m hnm (uhfIdemTower k P A)) =
      ofStage n (uhfIdemTower k P A) ∧
    -- 2. Colimit Chiral Parity Charge & Current of the Chiral Parity Charge (U₁):
    chiralParityCharge P_lim * chiralParityCharge P_lim = 1 ∧
    comm (chiralParityCharge P_lim) (vectorCurrent P_lim A_lim C_lim) =
      (2 : ℤ) • axialCurrent P_lim A_lim C_lim ∧
    anticomm (chiralParityCharge P_lim) (vectorCurrent P_lim A_lim C_lim) = 0 ∧
    -- 3. Colimit Affine Heisenberg Current Mode Commutator & Anticommutator (U₂):
    comm (heisenbergSourceMode r P_lim A_lim C_lim) (chiralSink P_lim C_lim) =
      virasoroModeChiral r P_lim A_lim C_lim ∧
    anticomm (heisenbergSourceMode r P_lim A_lim C_lim) (chiralSink P_lim C_lim) =
      virasoroModeEven r P_lim A_lim C_lim ∧
    -- 4. Colimit Sugawara Stress-Energy & Conformal Commutators (U₃):
    vectorCurrent P_lim A_lim C_lim * vectorCurrent P_lim A_lim C_lim -
      axialCurrent P_lim A_lim C_lim * axialCurrent P_lim A_lim C_lim =
      (2 : ℤ) • sugawaraTensor P_lim A_lim C_lim ∧
    comm (chiralSchwinger P_lim A_lim C_lim) (chiralSource P_lim A_lim) =
      (2 : ℤ) • (sugawaraTensor P_lim A_lim C_lim * chiralSource P_lim A_lim) ∧
    comm (chiralSchwinger P_lim A_lim C_lim) (chiralSink P_lim C_lim) =
      -(2 : ℤ) • (sugawaraTensor P_lim A_lim C_lim * chiralSink P_lim C_lim) ∧
    -- 5. Colimit Virasoro Chiral Splitting, Central Defect & Mode Closure (U₄):
    sugawaraPlus P_lim A_lim C_lim * sugawaraMinus P_lim A_lim C_lim = 0 ∧
    idemDefect (sugawaraTensor P_lim A_lim C_lim) =
      idemDefect (sugawaraPlus P_lim A_lim C_lim) +
      idemDefect (sugawaraMinus P_lim A_lim C_lim) ∧
    virasoroModeChiral r P_lim A_lim C_lim * virasoroModeChiral k P_lim A_lim C_lim =
      virasoroModeEven (r + k + 1) P_lim A_lim C_lim ∧
    -- 6. Colimit All-Scale UHF Inductive Tower Preservation (U₅):
    chiralParityCharge (uhfIdemTower k P_lim A_lim) *
      chiralParityCharge (uhfIdemTower k P_lim A_lim) = 1 ∧
    idemDefect (sugawaraTensor (uhfIdemTower k P_lim A_lim) A_lim C_lim) =
      idemDefect (sugawaraPlus (uhfIdemTower k P_lim A_lim) A_lim C_lim) +
      idemDefect (sugawaraMinus (uhfIdemTower k P_lim A_lim) A_lim C_lim) := by
  dsimp only
  have hPLim : ofStage n P * ofStage n P = ofStage n P := by
    rw [← map_mul, hP]
  rcases stage_D28_uhf_heisenberg_sugawara_virasoro_and_chiral_parity_master_synthesis
      (A := ofStage n A) (C := ofStage n C) hPLim r k with
    ⟨hC1, hC6, hC8, hH5, hH6, hS1, hS5, hS6, hV1, hV3, hU2, hU4⟩
  have hModeClosure :=
    (virasoro_sugawara_mode_closure hPLim (ofStage n A) (ofStage n C) r k).2.1
  exact ⟨directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         hC1, hC6, hC8, hH5, hH6, hS1, hS5, hS6, hV1, hV3, hModeClosure, hU2, hU4⟩

/-!
## 16. Stages `D₂₉`–`D₃₁` & Multi-Period `Cl(5, 5)` Bott Spinor / Colimit Master Bridge
-/

/-- **Theorem 16.1 (`cl55_multi_period_bott_and_limit_stages_D29_D30_D31_master_bridge`):**
Transports Stages `D₂₉` (all-`(r, s)` Affine Heisenberg–Virasoro Witt derivations), `D₃₀` (length-3
nested partial flag variety filtration `P₁ ⊂ P₂ ⊂ P₃` & parabolic upper-triangular radical), and
`D₃₁` (all-scale `k`, all-depth `d` soldering of the local two-state chart sandwiches
`(P - N₊) · (P + N₋)` to the multiscale unipotent and UHF daughter towers) across the multi-period
`Cl(5, 5)` Bott spinor tower `cl55ToBottStage p : Cl55 →+* Stage (5 + 8 * p)` and into the
`Cl(1, 1)^{\otimes n}` inductive colimit `Limit`. -/
theorem cl55_multi_period_bott_and_limit_stages_D29_D30_D31_master_bridge
    {ω : InfoGeometry.Clifford.Clifford55.Cl55} (hω : ω * ω = ω)
    (A_cl C_cl : InfoGeometry.Clifford.Clifford55.Cl55)
    {n : ℕ} {P₁ P₂ P₃ : Stage n}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂) (h3 : P₃ * P₃ = P₃)
    (h12 : P₁ * P₂ = P₁) (h21 : P₂ * P₁ = P₁)
    (h23 : P₂ * P₃ = P₂) (h32 : P₃ * P₂ = P₂)
    (h13 : P₁ * P₃ = P₁) (h31 : P₃ * P₁ = P₁)
    (A_fl C_fl : Stage n)
    (p r s k d : ℕ) :
    let P_lim := ofStage 5 (cl55ToStage5 ω)
    let A_lim := ofStage 5 (cl55ToStage5 A_cl)
    let C_lim := ofStage 5 (cl55ToStage5 C_cl)
    let P_k := unipotentIdempotentTower (fun _ => A_lim) k P_lim
    let P₁_lim := ofStage n P₁
    let P₂_lim := ofStage n P₂
    let P₃_lim := ofStage n P₃
    let Af_lim := ofStage n A_fl
    let Cf_lim := ofStage n C_fl
    -- 1. Multi-period `Cl(5, 5)` Bott spinor coherence (`Stage (5 + 8 * p) → Limit`):
    ofStage (5 + 8 * p) (cl55ToBottStage p ω) = P_lim ∧
    -- 2. Stage D₂₉: All-mode `(r, s)` Heisenberg–Virasoro Witt derivations in `Limit`:
    comm (heisenbergSourceMode r P_lim A_lim C_lim) (heisenbergSinkMode s P_lim A_lim C_lim) =
      virasoroModeChiral (r + s) P_lim A_lim C_lim ∧
    anticomm (heisenbergSourceMode r P_lim A_lim C_lim) (heisenbergSinkMode s P_lim A_lim C_lim) =
      virasoroModeEven (r + s) P_lim A_lim C_lim ∧
    comm (virasoroModeChiral r P_lim A_lim C_lim) (heisenbergSourceMode s P_lim A_lim C_lim) =
      (2 : ℤ) • heisenbergSourceMode (r + s + 1) P_lim A_lim C_lim ∧
    comm (virasoroModeChiral r P_lim A_lim C_lim) (heisenbergSinkMode s P_lim A_lim C_lim) =
      -(2 : ℤ) • heisenbergSinkMode (r + s + 1) P_lim A_lim C_lim ∧
    -- 3. Stage D₃₀: Length-3 partial flag filtration & parabolic radical in `Limit`:
    P₁_lim + flagStratumIdem P₁_lim P₂_lim + flagStratumIdem P₂_lim P₃_lim + (1 - P₃_lim) = 1 ∧
    flagStepCorner P₁_lim (flagStratumIdem P₁_lim P₂_lim) Af_lim *
        flagStepCorner (flagStratumIdem P₁_lim P₂_lim) (flagStratumIdem P₂_lim P₃_lim) Cf_lim =
      flagStepCorner P₁_lim (flagStratumIdem P₂_lim P₃_lim)
        (Af_lim * flagStratumIdem P₁_lim P₂_lim * Cf_lim) ∧
    flagEmbeddedCorner P₁_lim P₂_lim Af_lim * (1 - P₃_lim) =
      conePlus P₃_lim (P₁_lim * Af_lim) ∧
    -- 4. Stage D₃₁: All-scale `k`, all-depth `d` UHF–unipotent tower & two-state chart soldering in `Limit`:
    P_k = uhfIdemTower k P_lim A_lim ∧
    unipotentIdempotentTower (fun _ => A_lim) (k + 1) P_lim *
        (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (B := Limit))^[d]
          (genV P_k A_lim C_lim) *
        conjMinus P_k C_lim P_k =
      (1 - genV P_k A_lim C_lim) *
        (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (B := Limit))^[d]
          (qgtPlus P_k A_lim C_lim) ∧
    unipotentIdempotentTower (fun _ => A_lim) (k + 1) P_lim *
        qgtDefectDiff P_k A_lim C_lim d *
        conjMinus P_k C_lim P_k =
      (1 + genV P_k A_lim C_lim) *
        (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (B := Limit))^[d]
          (qgtPlus P_k A_lim C_lim) := by
  dsimp only
  have hBott :
      ofStage (5 + 8 * p) (cl55ToBottStage p ω) = ofStage 5 (cl55ToStage5 ω) := by
    unfold cl55ToBottStage
    exact directLimitOf_bondMap stageBond 5 (5 + 8 * p) (Nat.le_add_right 5 (8 * p))
      (cl55ToStage5 ω)
  have hP5 : cl55ToStage5 ω * cl55ToStage5 ω = cl55ToStage5 ω :=
    map_idempotent cl55ToStage5 hω
  have hPLim :
      ofStage 5 (cl55ToStage5 ω) * ofStage 5 (cl55ToStage5 ω) =
        ofStage 5 (cl55ToStage5 ω) :=
    map_idempotent (ofStage 5) hP5
  have h1Lim : ofStage n P₁ * ofStage n P₁ = ofStage n P₁ := by rw [← map_mul, h1]
  have h2Lim : ofStage n P₂ * ofStage n P₂ = ofStage n P₂ := by rw [← map_mul, h2]
  have h3Lim : ofStage n P₃ * ofStage n P₃ = ofStage n P₃ := by rw [← map_mul, h3]
  have h12Lim : ofStage n P₁ * ofStage n P₂ = ofStage n P₁ := by rw [← map_mul, h12]
  have h21Lim : ofStage n P₂ * ofStage n P₁ = ofStage n P₁ := by rw [← map_mul, h21]
  have h23Lim : ofStage n P₂ * ofStage n P₃ = ofStage n P₂ := by rw [← map_mul, h23]
  have h32Lim : ofStage n P₃ * ofStage n P₂ = ofStage n P₂ := by rw [← map_mul, h32]
  have h13Lim : ofStage n P₁ * ofStage n P₃ = ofStage n P₁ := by rw [← map_mul, h13]
  have h31Lim : ofStage n P₃ * ofStage n P₁ = ofStage n P₁ := by rw [← map_mul, h31]
  rcases stage_D29_all_mode_heisenberg_virasoro_and_uhf_unipotent_bridge hPLim
      (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) r s k with
    ⟨hH1, hH2, hV1, hV2, _, _, hTowerEq⟩
  rcases stage_D30_three_step_partial_flag_and_parabolic_radical_bridge
      h1Lim h2Lim h3Lim h12Lim h21Lim h23Lim h32Lim h13Lim h31Lim
      (ofStage n A_fl) (ofStage n C_fl) with
    ⟨_, _, _, _, hFlagPart, hFlagStep, _, hFlagEmb12, hFlagEmb13, _⟩
  rcases stage_D31_uhf_unipotent_tower_and_two_state_chart_sandwich_soldering hPLim
      (fun _ => ofStage 5 (cl55ToStage5 A_cl))
      (fun _ => ofStage 5 (cl55ToStage5 C_cl))
      (ofStage 5 (cl55ToStage5 A_cl)) k d with
    ⟨_, _, _, _, _, hChartV, hChartSig, _, _⟩
  refine ⟨hBott, hH1, hH2, hV1, hV2, hFlagPart, hFlagStep, ?_, hTowerEq, hChartV, hChartSig⟩
  rw [hFlagEmb12, hFlagEmb13]

/-!
## 17. Stage `D₂₆` × `D₂₇` Three-Move Synthesis: Dressed Drinfeld Loop Currents, All-`(m, l)`
Symbol Letter Rationalization, Borel Flag 3-Idempotent Partition, and Multi-Period `Cl(5, 5)`
Bott Colimit Bridge
-/

/-- **Helper Lemma 17.1 (`dressedCurv_unipotent_opPow_genV`):**
For any idempotent `P` (`P * P = P`), any `A, C : B`, and any loop mode `n : ℕ`, the Gribov-free
unipotent Peirce horizon dressing `(1 + conePlus P A, 1 - conePlus P A)` leaves every mode power
`opPow n (genV P A C)` strictly invariant:
`dressedCurv (1 + conePlus P A) (1 - conePlus P A) (opPow n (genV P A C)) = opPow n (genV P A C)`. -/
theorem dressedCurv_unipotent_opPow_genV
    {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (opPow n (genV P A C)) =
      opPow n (genV P A C) := by
  have hComm : conePlus P A * opPow n (genV P A C) = opPow n (genV P A C) * conePlus P A :=
    (opPow_genV_comm_invS_and_cones hP A C n).2.1
  have hNpSq : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  unfold dressedCurv
  calc
    (1 - conePlus P A) * opPow n (genV P A C) * (1 + conePlus P A)
        = (opPow n (genV P A C) - conePlus P A * opPow n (genV P A C)) * (1 + conePlus P A) := by
          rw [sub_mul, one_mul]
    _ = (opPow n (genV P A C) - opPow n (genV P A C) * conePlus P A) * (1 + conePlus P A) := by
          rw [hComm]
    _ = opPow n (genV P A C) -
          opPow n (genV P A C) * (conePlus P A * conePlus P A) := by
          noncomm_ring
    _ = opPow n (genV P A C) := by
          rw [hNpSq, mul_zero, sub_zero]

/-- **Theorem 17.2 (`dressed_drinfeld_loop_currents_and_all_m_symbol_rationalization`, Move 1):**
For any idempotent `P` (`P * P = P`), any `A, C : B`, and all `n, m, l : ℕ`:
1. **Unipotent Horizon Dressing of Drinfeld Loop Currents (`X_{±, n}`, `Φ_{±, n}`):**
   - `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (drinfeldXPlus n P A C) = drinfeldXPlus n P A C`,
   - `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (drinfeldXMinus n P A C) =`
     `drinfeldXMinus n P A C - drinfeldPhiPlus n P A C + drinfeldPhiMinus n P A C - drinfeldXPlus (n + 1) P A C`,
   - `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (drinfeldPhiPlus n P A C) =`
     `drinfeldPhiPlus n P A C + drinfeldXPlus (n + 1) P A C`,
   - `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (drinfeldPhiMinus n P A C) =`
     `drinfeldPhiMinus n P A C - drinfeldXPlus (n + 1) P A C`,
   - `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (drinfeldPhiPlus n P A C + drinfeldPhiMinus n P A C) =`
     `opPow (n + 1) (genV P A C)`.
2. **All-`(m, l)` Kirillov–Reshetikhin Symbol Letter Rationalization:**
   - `algSymbolFactorPlus P A C (polygonFibSeq P A C m) (eisensteinSeq P A C l) *`
     `algSymbolFactorMinus P A C (polygonFibSeq P A C m) (eisensteinSeq P A C l) =`
     `polygonFibSeq P A C m * polygonFibSeq P A C m -`
     `eisensteinSeq P A C l * eisensteinSeq P A C l * fourMassBoxDisc P A C`. -/
theorem dressed_drinfeld_loop_currents_and_all_m_symbol_rationalization
    {P : B} (hP : P * P = P) (A C : B) (n m l : ℕ) :
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (drinfeldXPlus n P A C) =
      drinfeldXPlus n P A C ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (drinfeldXMinus n P A C) =
      drinfeldXMinus n P A C - drinfeldPhiPlus n P A C +
        drinfeldPhiMinus n P A C - drinfeldXPlus (n + 1) P A C ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (drinfeldPhiPlus n P A C) =
      drinfeldPhiPlus n P A C + drinfeldXPlus (n + 1) P A C ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (drinfeldPhiMinus n P A C) =
      drinfeldPhiMinus n P A C - drinfeldXPlus (n + 1) P A C ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A)
        (drinfeldPhiPlus n P A C + drinfeldPhiMinus n P A C) =
      opPow (n + 1) (genV P A C) ∧
    algSymbolFactorPlus P A C (polygonFibSeq P A C m) (eisensteinSeq P A C l) *
        algSymbolFactorMinus P A C (polygonFibSeq P A C m) (eisensteinSeq P A C l) =
      polygonFibSeq P A C m * polygonFibSeq P A C m -
        eisensteinSeq P A C l * eisensteinSeq P A C l * fourMassBoxDisc P A C := by
  have hUnip1 : (1 + conePlus P A) * (1 - conePlus P A) = 1 := by peirce_nf hP
  have hMul : ∀ X Y : B,
      dressedCurv (1 + conePlus P A) (1 - conePlus P A) (X * Y) =
        dressedCurv (1 + conePlus P A) (1 - conePlus P A) X *
          dressedCurv (1 + conePlus P A) (1 - conePlus P A) Y := by
    intro X Y
    unfold dressedCurv
    calc (1 - conePlus P A) * (X * Y) * (1 + conePlus P A)
      _ = ((1 - conePlus P A) * X) *
            ((1 + conePlus P A) * (1 - conePlus P A)) *
            (Y * (1 + conePlus P A)) := by
          rw [hUnip1, mul_one]; noncomm_ring
      _ = ((1 - conePlus P A) * X * (1 + conePlus P A)) *
            ((1 - conePlus P A) * Y * (1 + conePlus P A)) := by
          noncomm_ring
  have hVn := dressedCurv_unipotent_opPow_genV hP A C n
  have hConeP :
      dressedCurv (1 + conePlus P A) (1 - conePlus P A) (conePlus P A) = conePlus P A := by
    unfold dressedCurv; peirce_nf hP
  have hConeM :
      dressedCurv (1 + conePlus P A) (1 - conePlus P A) (coneMinus P C) =
        coneMinus P C - qgtPlus P A C + qgtMinus P A C - genV P A C * conePlus P A := by
    unfold dressedCurv qgtPlus qgtMinus; peirce_nf hP
  have hQgtP :
      dressedCurv (1 + conePlus P A) (1 - conePlus P A) (qgtPlus P A C) =
        qgtPlus P A C + genV P A C * conePlus P A := by
    unfold dressedCurv qgtPlus; peirce_nf hP
  have hQgtM :
      dressedCurv (1 + conePlus P A) (1 - conePlus P A) (qgtMinus P A C) =
        qgtMinus P A C - genV P A C * conePlus P A := by
    unfold dressedCurv qgtMinus; peirce_nf hP
  have hPhiSum :
      drinfeldPhiPlus n P A C + drinfeldPhiMinus n P A C = opPow (n + 1) (genV P A C) := by
    unfold drinfeldPhiPlus drinfeldPhiMinus qgtPlus qgtMinus
    rw [opPow_succ, ← mul_add]
    rfl
  have hEisV :
      eisensteinSeq P A C l * genV P A C = genV P A C * eisensteinSeq P A C l :=
    eisensteinSeq_comm_of_genV_comm P A C (genV P A C) rfl l
  have hPolyEis :
      polygonFibSeq P A C m * eisensteinSeq P A C l =
        eisensteinSeq P A C l * polygonFibSeq P A C m :=
    polygonFibSeq_comm_of_genV_comm P A C (eisensteinSeq P A C l) hEisV.symm m
  have hSqrtV :
      fourMassBoxSqrt P A C * genV P A C = genV P A C * fourMassBoxSqrt P A C := by
    unfold fourMassBoxSqrt; peirce_nf hP
  have hPolySqrt :
      polygonFibSeq P A C m * fourMassBoxSqrt P A C =
        fourMassBoxSqrt P A C * polygonFibSeq P A C m :=
    polygonFibSeq_comm_of_genV_comm P A C (fourMassBoxSqrt P A C) hSqrtV.symm m
  have hEisSqrt :
      eisensteinSeq P A C l * fourMassBoxSqrt P A C =
        fourMassBoxSqrt P A C * eisensteinSeq P A C l :=
    eisensteinSeq_comm_of_genV_comm P A C (fourMassBoxSqrt P A C) hSqrtV.symm l
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold drinfeldXPlus
    rw [hMul, hVn, hConeP]
  · unfold drinfeldXMinus
    rw [hMul, hVn, hConeM]
    unfold drinfeldPhiPlus drinfeldPhiMinus drinfeldXPlus
    rw [opPow_succ]
    noncomm_ring
  · unfold drinfeldPhiPlus
    rw [hMul, hVn, hQgtP]
    unfold drinfeldXPlus
    rw [opPow_succ]
    noncomm_ring
  · unfold drinfeldPhiMinus
    rw [hMul, hVn, hQgtM]
    unfold drinfeldXPlus
    rw [opPow_succ]
    noncomm_ring
  · rw [hPhiSum]
    exact dressedCurv_unipotent_opPow_genV hP A C (n + 1)
  · exact algSymbolFactor_rationalization_of_comm
      hP A C (polygonFibSeq P A C m) (eisensteinSeq P A C l)
      hPolyEis hPolySqrt hEisSqrt

/-- Upper `(1, 2)` Borel flag corner `P₁ * X * (P₂ - P₁)` associated to a nested partial flag `P₁ ⊂ P₂`. -/
def borelCorner12 (P₁ P₂ X : B) : B :=
  P₁ * X * flagStratumIdem P₁ P₂

/-- Middle-to-complement `(2, 3)` Borel flag corner `(P₂ - P₁) * Y * (1 - P₂)` associated to `P₁ ⊂ P₂`. -/
def borelCorner23 (P₁ P₂ Y : B) : B :=
  flagStratumIdem P₁ P₂ * Y * (1 - P₂)

/-- Top `(1, 3)` Borel flag corner `P₁ * Z * (1 - P₂)` associated to `P₁ ⊂ P₂`. -/
def borelCorner13 (P₁ P₂ Z : B) : B :=
  P₁ * Z * (1 - P₂)

/-- **Theorem 17.3 (`partial_flag_three_idempotent_partition_and_borel_dressing_bridge`, Move 2):**
For any nested pair of idempotents `P₁, P₂ : B` (`h1 : P₁ * P₁ = P₁`, `h2 : P₂ * P₂ = P₂`,
`h12 : P₁ * P₂ = P₁`, `h21 : P₂ * P₁ = P₁`) and any mutually orthogonal 3-idempotent partition
`(E₁, E₂, E₃)` (`hE1 : E₁ * E₁ = E₁`, `hE2 : E₂ * E₂ = E₂`, `hE12 : E₁ * E₂ = 0`,
`hE21 : E₂ * E₁ = 0`, `hPart : E₁ + E₂ + E₃ = 1`):
1. **Mutual Orthogonality of `(P₁, flagStratumIdem P₁ P₂, 1 - P₂)` & Converse Flag Reconstruction:**
   - `flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂`,
   - `(1 - P₂) * (1 - P₂) = 1 - P₂`,
   - `P₁ * flagStratumIdem P₁ P₂ = 0`, `flagStratumIdem P₁ P₂ * P₁ = 0`,
   - `P₁ * (1 - P₂) = 0`, `(1 - P₂) * P₁ = 0`,
   - `flagStratumIdem P₁ P₂ * (1 - P₂) = 0`, `(1 - P₂) * flagStratumIdem P₁ P₂ = 0`,
   - `P₁ + flagStratumIdem P₁ P₂ + (1 - P₂) = 1`,
   - Converse reconstruction (`P₁' := E₁`, `P₂' := E₁ + E₂`):
     `(E₁ + E₂) * (E₁ + E₂) = E₁ + E₂`, `E₁ * (E₁ + E₂) = E₁`, `(E₁ + E₂) * E₁ = E₁`,
     `flagStratumIdem E₁ (E₁ + E₂) = E₂`, and `1 - (E₁ + E₂) = E₃`.
2. **Borel Radical Square-Zero Nilpotency & Steinberg Corner Commutator:**
   - `borelCorner12 P₁ P₂ X * borelCorner12 P₁ P₂ X = 0`,
   - `borelCorner23 P₁ P₂ Y * borelCorner23 P₁ P₂ Y = 0`,
   - `borelCorner13 P₁ P₂ Z * borelCorner13 P₁ P₂ Z = 0`,
   - `borelCorner23 P₁ P₂ Y * borelCorner12 P₁ P₂ X = 0`,
   - `comm (borelCorner12 P₁ P₂ X) (borelCorner23 P₁ P₂ Y) =`
     `borelCorner13 P₁ P₂ (X * flagStratumIdem P₁ P₂ * Y)`.
3. **Borel Unipotent Maurer–Cartan Dressing Cocycles:**
   - `maurerCartanCocycle (comm P₁) (1 + borelCorner12 P₁ P₂ X) (1 - borelCorner12 P₁ P₂ X) =`
     `borelCorner12 P₁ P₂ X`,
   - `maurerCartanCocycle (comm P₂) (1 + borelCorner23 P₁ P₂ Y) (1 - borelCorner23 P₁ P₂ Y) =`
     `borelCorner23 P₁ P₂ Y`,
   - `maurerCartanCocycle (comm P₁) (1 + borelCorner13 P₁ P₂ Z) (1 - borelCorner13 P₁ P₂ Z) =`
     `borelCorner13 P₁ P₂ Z`. -/
theorem partial_flag_three_idempotent_partition_and_borel_dressing_bridge
    {P₁ P₂ E₁ E₂ E₃ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = P₁) (h21 : P₂ * P₁ = P₁)
    (hE1 : E₁ * E₁ = E₁) (hE2 : E₂ * E₂ = E₂)
    (hE12 : E₁ * E₂ = 0) (hE21 : E₂ * E₁ = 0)
    (hPart : E₁ + E₂ + E₃ = 1)
    (X Y Z : B) :
    (flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂ ∧
     (1 - P₂) * (1 - P₂) = 1 - P₂ ∧
     P₁ * flagStratumIdem P₁ P₂ = 0 ∧
     flagStratumIdem P₁ P₂ * P₁ = 0 ∧
     P₁ * (1 - P₂) = 0 ∧
     (1 - P₂) * P₁ = 0 ∧
     flagStratumIdem P₁ P₂ * (1 - P₂) = 0 ∧
     (1 - P₂) * flagStratumIdem P₁ P₂ = 0 ∧
     P₁ + flagStratumIdem P₁ P₂ + (1 - P₂) = 1 ∧
     (E₁ + E₂) * (E₁ + E₂) = E₁ + E₂ ∧
     E₁ * (E₁ + E₂) = E₁ ∧
     (E₁ + E₂) * E₁ = E₁ ∧
     flagStratumIdem E₁ (E₁ + E₂) = E₂ ∧
     1 - (E₁ + E₂) = E₃) ∧
    (borelCorner12 P₁ P₂ X * borelCorner12 P₁ P₂ X = 0 ∧
     borelCorner23 P₁ P₂ Y * borelCorner23 P₁ P₂ Y = 0 ∧
     borelCorner13 P₁ P₂ Z * borelCorner13 P₁ P₂ Z = 0 ∧
     borelCorner23 P₁ P₂ Y * borelCorner12 P₁ P₂ X = 0 ∧
     comm (borelCorner12 P₁ P₂ X) (borelCorner23 P₁ P₂ Y) =
       borelCorner13 P₁ P₂ (X * flagStratumIdem P₁ P₂ * Y)) ∧
    (maurerCartanCocycle (comm P₁)
       (1 + borelCorner12 P₁ P₂ X) (1 - borelCorner12 P₁ P₂ X) =
       borelCorner12 P₁ P₂ X ∧
     maurerCartanCocycle (comm P₂)
       (1 + borelCorner23 P₁ P₂ Y) (1 - borelCorner23 P₁ P₂ Y) =
       borelCorner23 P₁ P₂ Y ∧
     maurerCartanCocycle (comm P₁)
       (1 + borelCorner13 P₁ P₂ Z) (1 - borelCorner13 P₁ P₂ Z) =
       borelCorner13 P₁ P₂ Z) := by
  rcases partial_flag_to_grassmannian_embedding h1 h2 h12 h21 X with
    ⟨hStratIdem, hP1Strat, hStratP1, hStratComp, hCompStrat, hUnity, _, _⟩
  have hCompIdem : (1 - P₂) * (1 - P₂) = 1 - P₂ := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, h2]
    abel
  have hP1Comp : P₁ * (1 - P₂) = 0 := by
    rw [mul_sub, mul_one, h12, sub_self]
  have hCompP1 : (1 - P₂) * P₁ = 0 := by
    rw [sub_mul, one_mul, h21, sub_self]
  have hP2Strat : P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂ := by
    unfold flagStratumIdem
    rw [mul_sub, h2, h21]
  have hCompP2 : (1 - P₂) * P₂ = 0 := by
    rw [sub_mul, one_mul, h2, sub_self]
  have hB12Sq : borelCorner12 P₁ P₂ X * borelCorner12 P₁ P₂ X = 0 := by
    unfold borelCorner12
    calc (P₁ * X * flagStratumIdem P₁ P₂) * (P₁ * X * flagStratumIdem P₁ P₂)
      _ = P₁ * X * (flagStratumIdem P₁ P₂ * P₁) * X * flagStratumIdem P₁ P₂ := by
          simp only [mul_assoc]
      _ = 0 := by rw [hStratP1, mul_zero, zero_mul, zero_mul]
  have hB23Sq : borelCorner23 P₁ P₂ Y * borelCorner23 P₁ P₂ Y = 0 := by
    unfold borelCorner23
    calc (flagStratumIdem P₁ P₂ * Y * (1 - P₂)) * (flagStratumIdem P₁ P₂ * Y * (1 - P₂))
      _ = flagStratumIdem P₁ P₂ * Y * ((1 - P₂) * flagStratumIdem P₁ P₂) * Y * (1 - P₂) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hCompStrat, mul_zero, zero_mul, zero_mul]
  have hB13Sq : borelCorner13 P₁ P₂ Z * borelCorner13 P₁ P₂ Z = 0 := by
    unfold borelCorner13
    calc (P₁ * Z * (1 - P₂)) * (P₁ * Z * (1 - P₂))
      _ = P₁ * Z * ((1 - P₂) * P₁) * Z * (1 - P₂) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hCompP1, mul_zero, zero_mul, zero_mul]
  have hB23B12 : borelCorner23 P₁ P₂ Y * borelCorner12 P₁ P₂ X = 0 := by
    unfold borelCorner23 borelCorner12
    calc (flagStratumIdem P₁ P₂ * Y * (1 - P₂)) * (P₁ * X * flagStratumIdem P₁ P₂)
      _ = flagStratumIdem P₁ P₂ * Y * ((1 - P₂) * P₁) * X * flagStratumIdem P₁ P₂ := by
          simp only [mul_assoc]
      _ = 0 := by rw [hCompP1, mul_zero, zero_mul, zero_mul]
  have hB12B23 :
      borelCorner12 P₁ P₂ X * borelCorner23 P₁ P₂ Y =
        borelCorner13 P₁ P₂ (X * flagStratumIdem P₁ P₂ * Y) := by
    unfold borelCorner12 borelCorner23 borelCorner13
    calc (P₁ * X * flagStratumIdem P₁ P₂) * (flagStratumIdem P₁ P₂ * Y * (1 - P₂))
      _ = P₁ * (X * (flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂) * Y) * (1 - P₂) := by
          simp only [mul_assoc]
      _ = P₁ * (X * flagStratumIdem P₁ P₂ * Y) * (1 - P₂) := by
          rw [hStratIdem]
  refine ⟨⟨hStratIdem, hCompIdem, hP1Strat, hStratP1, hP1Comp, hCompP1,
           hStratComp, hCompStrat, hUnity, ?_, ?_, ?_, ?_, ?_⟩,
          ⟨hB12Sq, hB23Sq, hB13Sq, hB23B12, ?_⟩,
          ⟨?_, ?_, ?_⟩⟩
  · simp only [add_mul, mul_add, hE1, hE2, hE12, hE21]
    abel
  · rw [mul_add, hE1, hE12, add_zero]
  · rw [add_mul, hE1, hE21, add_zero]
  · unfold flagStratumIdem
    abel
  · rw [← hPart]
    abel
  · unfold OperatorAlgebra.PeirceSpine.comm
    rw [hB12B23, hB23B12, sub_zero]
  · have hP1B12 : P₁ * borelCorner12 P₁ P₂ X = borelCorner12 P₁ P₂ X := by
      unfold borelCorner12
      rw [← mul_assoc, ← mul_assoc, h1]
    have hB12P1 : borelCorner12 P₁ P₂ X * P₁ = 0 := by
      unfold borelCorner12
      rw [mul_assoc, hStratP1, mul_zero]
    have hComm12 : comm P₁ (1 + borelCorner12 P₁ P₂ X) = borelCorner12 P₁ P₂ X := by
      unfold OperatorAlgebra.PeirceSpine.comm
      rw [mul_add, add_mul, mul_one, one_mul, hP1B12, hB12P1]
      abel
    unfold maurerCartanCocycle
    rw [hComm12, sub_mul, one_mul, hB12Sq, sub_zero]
  · have hP2B23 : P₂ * borelCorner23 P₁ P₂ Y = borelCorner23 P₁ P₂ Y := by
      unfold borelCorner23
      rw [← mul_assoc, ← mul_assoc, hP2Strat]
    have hB23P2 : borelCorner23 P₁ P₂ Y * P₂ = 0 := by
      unfold borelCorner23
      rw [mul_assoc, hCompP2, mul_zero]
    have hComm23 : comm P₂ (1 + borelCorner23 P₁ P₂ Y) = borelCorner23 P₁ P₂ Y := by
      unfold OperatorAlgebra.PeirceSpine.comm
      rw [mul_add, add_mul, mul_one, one_mul, hP2B23, hB23P2]
      abel
    unfold maurerCartanCocycle
    rw [hComm23, sub_mul, one_mul, hB23Sq, sub_zero]
  · have hP1B13 : P₁ * borelCorner13 P₁ P₂ Z = borelCorner13 P₁ P₂ Z := by
      unfold borelCorner13
      rw [← mul_assoc, ← mul_assoc, h1]
    have hB13P1 : borelCorner13 P₁ P₂ Z * P₁ = 0 := by
      unfold borelCorner13
      rw [mul_assoc, hCompP1, mul_zero]
    have hComm13 : comm P₁ (1 + borelCorner13 P₁ P₂ Z) = borelCorner13 P₁ P₂ Z := by
      unfold OperatorAlgebra.PeirceSpine.comm
      rw [mul_add, add_mul, mul_one, one_mul, hP1B13, hB13P1]
      abel
    unfold maurerCartanCocycle
    rw [hComm13, sub_mul, one_mul, hB13Sq, sub_zero]

theorem map_opPow {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) (X : R) :
    f (opPow n X) = opPow n (f X) := by
  rw [opPow_eq_pow, opPow_eq_pow, map_pow]

theorem map_drinfeldXPlus {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (n : ℕ) (P A C : R) :
    f (drinfeldXPlus n P A C) = drinfeldXPlus n (f P) (f A) (f C) := by
  unfold drinfeldXPlus
  rw [map_mul, map_opPow, map_genV, map_conePlus]

theorem map_drinfeldXMinus {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (n : ℕ) (P A C : R) :
    f (drinfeldXMinus n P A C) = drinfeldXMinus n (f P) (f A) (f C) := by
  unfold drinfeldXMinus
  rw [map_mul, map_opPow, map_genV, map_coneMinus]

theorem map_fourMassBoxSqrt {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (P A C : R) :
    f (fourMassBoxSqrt P A C) = fourMassBoxSqrt (f P) (f A) (f C) := by
  unfold fourMassBoxSqrt
  rw [map_add, map_invS, map_zsmul, map_genPhi]

theorem map_flagStratumIdem {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (P₁ P₂ : R) :
    f (flagStratumIdem P₁ P₂) = flagStratumIdem (f P₁) (f P₂) := by
  unfold flagStratumIdem
  rw [map_sub]

theorem map_borelCorner12 {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (P₁ P₂ X : R) :
    f (borelCorner12 P₁ P₂ X) = borelCorner12 (f P₁) (f P₂) (f X) := by
  unfold borelCorner12
  rw [map_mul, map_mul, map_flagStratumIdem]

theorem map_borelCorner23 {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (P₁ P₂ Y : R) :
    f (borelCorner23 P₁ P₂ Y) = borelCorner23 (f P₁) (f P₂) (f Y) := by
  unfold borelCorner23
  rw [map_mul, map_mul, map_flagStratumIdem, map_sub, map_one]

theorem map_borelCorner13 {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (P₁ P₂ Z : R) :
    f (borelCorner13 P₁ P₂ Z) = borelCorner13 (f P₁) (f P₂) (f Z) := by
  unfold borelCorner13
  rw [map_mul, map_mul, map_sub, map_one]

/-- **Theorem 17.4 (`cl55_multi_period_bott_stage_D26_D27_dressing_and_quantum_affine_colimit_bridge`, Move 3):**
Transports Move 1, Move 2, and Stage `D₂₆`/`D₂₇` across all `8k` Bott periods
`ofStage (5 + 8 * k) ∘ cl55ToBottStage k : Cl55 →+* Limit` into the `Cl(1, 1)^{\otimes n}`
inductive colimit `Limit`. -/
theorem cl55_multi_period_bott_stage_D26_D27_dressing_and_quantum_affine_colimit_bridge
    {ω ω₁ ω₂ : InfoGeometry.Clifford.Clifford55.Cl55}
    (hω : ω * ω = ω)
    (h1 : ω₁ * ω₁ = ω₁) (h2 : ω₂ * ω₂ = ω₂)
    (h12 : ω₁ * ω₂ = ω₁) (h21 : ω₂ * ω₁ = ω₁)
    (k n m l : ℕ)
    (A_cl C_cl X_cl Y_cl Z_cl : InfoGeometry.Clifford.Clifford55.Cl55) :
    let P_lim := ofStage 5 (cl55ToStage5 ω)
    let P₁_lim := ofStage 5 (cl55ToStage5 ω₁)
    let P₂_lim := ofStage 5 (cl55ToStage5 ω₂)
    let A_lim := ofStage 5 (cl55ToStage5 A_cl)
    let C_lim := ofStage 5 (cl55ToStage5 C_cl)
    let X_lim := ofStage 5 (cl55ToStage5 X_cl)
    let Y_lim := ofStage 5 (cl55ToStage5 Y_cl)
    let Z_lim := ofStage 5 (cl55ToStage5 Z_cl)
    (ofStage (5 + 8 * k) (cl55ToBottStage k (drinfeldXPlus n ω A_cl C_cl)) =
       drinfeldXPlus n P_lim A_lim C_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (drinfeldXMinus n ω A_cl C_cl)) =
       drinfeldXMinus n P_lim A_lim C_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (fourMassBoxSqrt ω A_cl C_cl)) =
       fourMassBoxSqrt P_lim A_lim C_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (borelCorner12 ω₁ ω₂ X_cl)) =
       borelCorner12 P₁_lim P₂_lim X_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (borelCorner23 ω₁ ω₂ Y_cl)) =
       borelCorner23 P₁_lim P₂_lim Y_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (borelCorner13 ω₁ ω₂ Z_cl)) =
       borelCorner13 P₁_lim P₂_lim Z_lim) ∧
    (dressedCurv (1 + conePlus P_lim A_lim) (1 - conePlus P_lim A_lim)
       (drinfeldXPlus n P_lim A_lim C_lim) =
       drinfeldXPlus n P_lim A_lim C_lim ∧
     dressedCurv (1 + conePlus P_lim A_lim) (1 - conePlus P_lim A_lim)
       (drinfeldXMinus n P_lim A_lim C_lim) =
       drinfeldXMinus n P_lim A_lim C_lim - drinfeldPhiPlus n P_lim A_lim C_lim +
         drinfeldPhiMinus n P_lim A_lim C_lim - drinfeldXPlus (n + 1) P_lim A_lim C_lim ∧
     dressedCurv (1 + conePlus P_lim A_lim) (1 - conePlus P_lim A_lim)
       (drinfeldPhiPlus n P_lim A_lim C_lim + drinfeldPhiMinus n P_lim A_lim C_lim) =
       opPow (n + 1) (genV P_lim A_lim C_lim) ∧
     algSymbolFactorPlus P_lim A_lim C_lim
         (polygonFibSeq P_lim A_lim C_lim m) (eisensteinSeq P_lim A_lim C_lim l) *
       algSymbolFactorMinus P_lim A_lim C_lim
         (polygonFibSeq P_lim A_lim C_lim m) (eisensteinSeq P_lim A_lim C_lim l) =
       polygonFibSeq P_lim A_lim C_lim m * polygonFibSeq P_lim A_lim C_lim m -
         eisensteinSeq P_lim A_lim C_lim l * eisensteinSeq P_lim A_lim C_lim l *
           fourMassBoxDisc P_lim A_lim C_lim) ∧
    (P₁_lim + flagStratumIdem P₁_lim P₂_lim + (1 - P₂_lim) = 1 ∧
     comm (borelCorner12 P₁_lim P₂_lim X_lim) (borelCorner23 P₁_lim P₂_lim Y_lim) =
       borelCorner13 P₁_lim P₂_lim (X_lim * flagStratumIdem P₁_lim P₂_lim * Y_lim) ∧
     maurerCartanCocycle (comm P₁_lim)
       (1 + borelCorner12 P₁_lim P₂_lim X_lim) (1 - borelCorner12 P₁_lim P₂_lim X_lim) =
       borelCorner12 P₁_lim P₂_lim X_lim ∧
     maurerCartanCocycle (comm P₂_lim)
       (1 + borelCorner23 P₁_lim P₂_lim Y_lim) (1 - borelCorner23 P₁_lim P₂_lim Y_lim) =
       borelCorner23 P₁_lim P₂_lim Y_lim ∧
     maurerCartanCocycle (comm P₁_lim)
       (1 + borelCorner13 P₁_lim P₂_lim Z_lim) (1 - borelCorner13 P₁_lim P₂_lim Z_lim) =
       borelCorner13 P₁_lim P₂_lim Z_lim) ∧
    (polygonFibSeq P_lim A_lim C_lim (m + 1) * polygonFibSeq P_lim A_lim C_lim (m + 1) -
       polygonFibSeq P_lim A_lim C_lim (m + 2) * polygonFibSeq P_lim A_lim C_lim m =
       (-genV P_lim A_lim C_lim) ^ m ∧
     eisensteinSeq P_lim A_lim C_lim (m + 1) * eisensteinSeq P_lim A_lim C_lim (m + 1) -
       eisensteinSeq P_lim A_lim C_lim (m + 2) * eisensteinSeq P_lim A_lim C_lim m =
       (genV P_lim A_lim C_lim) ^ m ∧
     comm (drinfeldXPlus n P_lim A_lim C_lim) (drinfeldXMinus m P_lim A_lim C_lim) =
       drinfeldPhiPlus (n + m) P_lim A_lim C_lim - drinfeldPhiMinus (n + m) P_lim A_lim C_lim ∧
     anticomm (drinfeldXPlus n P_lim A_lim C_lim) (drinfeldXMinus m P_lim A_lim C_lim) =
       opPow (n + m + 1) (genV P_lim A_lim C_lim)) := by
  dsimp only
  have hCoherent : ∀ y : InfoGeometry.Clifford.Clifford55.Cl55,
      ofStage (5 + 8 * k) (cl55ToBottStage k y) = ofStage 5 (cl55ToStage5 y) := by
    intro y
    unfold cl55ToBottStage
    exact directLimitOf_bondMap stageBond 5 (5 + 8 * k) (Nat.le_add_right 5 (8 * k))
      (cl55ToStage5 y)
  have hP5 : cl55ToStage5 ω * cl55ToStage5 ω = cl55ToStage5 ω :=
    map_idempotent cl55ToStage5 hω
  have hPlim :
      ofStage 5 (cl55ToStage5 ω) * ofStage 5 (cl55ToStage5 ω) =
        ofStage 5 (cl55ToStage5 ω) :=
    map_idempotent (ofStage 5) hP5
  have h1_5 : cl55ToStage5 ω₁ * cl55ToStage5 ω₁ = cl55ToStage5 ω₁ :=
    map_idempotent cl55ToStage5 h1
  have h1_lim :
      ofStage 5 (cl55ToStage5 ω₁) * ofStage 5 (cl55ToStage5 ω₁) =
        ofStage 5 (cl55ToStage5 ω₁) :=
    map_idempotent (ofStage 5) h1_5
  have h2_5 : cl55ToStage5 ω₂ * cl55ToStage5 ω₂ = cl55ToStage5 ω₂ :=
    map_idempotent cl55ToStage5 h2
  have h2_lim :
      ofStage 5 (cl55ToStage5 ω₂) * ofStage 5 (cl55ToStage5 ω₂) =
        ofStage 5 (cl55ToStage5 ω₂) :=
    map_idempotent (ofStage 5) h2_5
  have h12_lim :
      ofStage 5 (cl55ToStage5 ω₁) * ofStage 5 (cl55ToStage5 ω₂) =
        ofStage 5 (cl55ToStage5 ω₁) := by
    rw [← map_mul, ← map_mul, h12]
  have h21_lim :
      ofStage 5 (cl55ToStage5 ω₂) * ofStage 5 (cl55ToStage5 ω₁) =
        ofStage 5 (cl55ToStage5 ω₁) := by
    rw [← map_mul, ← map_mul, h21]
  have hMapXP :
      ofStage (5 + 8 * k) (cl55ToBottStage k (drinfeldXPlus n ω A_cl C_cl)) =
        drinfeldXPlus n (ofStage 5 (cl55ToStage5 ω))
          (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) := by
    rw [hCoherent, map_drinfeldXPlus cl55ToStage5, map_drinfeldXPlus (ofStage 5)]
  have hMapXM :
      ofStage (5 + 8 * k) (cl55ToBottStage k (drinfeldXMinus n ω A_cl C_cl)) =
        drinfeldXMinus n (ofStage 5 (cl55ToStage5 ω))
          (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) := by
    rw [hCoherent, map_drinfeldXMinus cl55ToStage5, map_drinfeldXMinus (ofStage 5)]
  have hMapSqrt :
      ofStage (5 + 8 * k) (cl55ToBottStage k (fourMassBoxSqrt ω A_cl C_cl)) =
        fourMassBoxSqrt (ofStage 5 (cl55ToStage5 ω))
          (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) := by
    rw [hCoherent, map_fourMassBoxSqrt cl55ToStage5, map_fourMassBoxSqrt (ofStage 5)]
  have hMapB12 :
      ofStage (5 + 8 * k) (cl55ToBottStage k (borelCorner12 ω₁ ω₂ X_cl)) =
        borelCorner12 (ofStage 5 (cl55ToStage5 ω₁)) (ofStage 5 (cl55ToStage5 ω₂))
          (ofStage 5 (cl55ToStage5 X_cl)) := by
    rw [hCoherent, map_borelCorner12 cl55ToStage5, map_borelCorner12 (ofStage 5)]
  have hMapB23 :
      ofStage (5 + 8 * k) (cl55ToBottStage k (borelCorner23 ω₁ ω₂ Y_cl)) =
        borelCorner23 (ofStage 5 (cl55ToStage5 ω₁)) (ofStage 5 (cl55ToStage5 ω₂))
          (ofStage 5 (cl55ToStage5 Y_cl)) := by
    rw [hCoherent, map_borelCorner23 cl55ToStage5, map_borelCorner23 (ofStage 5)]
  have hMapB13 :
      ofStage (5 + 8 * k) (cl55ToBottStage k (borelCorner13 ω₁ ω₂ Z_cl)) =
        borelCorner13 (ofStage 5 (cl55ToStage5 ω₁)) (ofStage 5 (cl55ToStage5 ω₂))
          (ofStage 5 (cl55ToStage5 Z_cl)) := by
    rw [hCoherent, map_borelCorner13 cl55ToStage5, map_borelCorner13 (ofStage 5)]
  rcases dressed_drinfeld_loop_currents_and_all_m_symbol_rationalization
      hPlim (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) n m l with
    ⟨hM1_1, hM1_2, _, _, hM1_5, hM1_6⟩
  rcases partial_flag_to_grassmannian_embedding
      h1_lim h2_lim h12_lim h21_lim (ofStage 5 (cl55ToStage5 X_cl)) with
    ⟨hStratIdem, hP1Strat, hStratP1, _, _, hUnity, _, _⟩
  rcases partial_flag_three_idempotent_partition_and_borel_dressing_bridge
      h1_lim h2_lim h12_lim h21_lim
      h1_lim hStratIdem hP1Strat hStratP1 hUnity
      (ofStage 5 (cl55ToStage5 X_cl))
      (ofStage 5 (cl55ToStage5 Y_cl))
      (ofStage 5 (cl55ToStage5 Z_cl)) with
    ⟨_, ⟨_, _, _, _, hSteinberg⟩, ⟨hCoc12, hCoc23, hCoc13⟩⟩
  rcases all_m_kirillov_reshetikhin_t_system_polygon_and_eisenstein
      (ofStage 5 (cl55ToStage5 ω))
      (ofStage 5 (cl55ToStage5 A_cl))
      (ofStage 5 (cl55ToStage5 C_cl)) m with
    ⟨hKRPoly, hKREis⟩
  rcases drinfeld_new_presentation_loop_relations
      hPlim (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) n m with
    ⟨_, _, _, _, _, _, _, _, _, _, hDrinComm, hDrinAnti⟩
  exact ⟨⟨hMapXP, hMapXM, hMapSqrt, hMapB12, hMapB23, hMapB13⟩,
         ⟨hM1_1, hM1_2, hM1_5, hM1_6⟩,
         ⟨hUnity, hSteinberg, hCoc12, hCoc23, hCoc13⟩,
         ⟨hKRPoly, hKREis, hDrinComm, hDrinAnti⟩⟩

/-- Concrete `Cl(5, 5)` spinor-vacuum specialization of
`cl55_multi_period_bott_stage_D26_D27_dressing_and_quantum_affine_colimit_bridge` at
`ω = cl55VacuumIdempotent`. -/
theorem cl55VacuumIdempotent_multi_period_bott_stage_D26_D27_dressing_and_quantum_affine_colimit_bridge
    {ω₁ ω₂ : InfoGeometry.Clifford.Clifford55.Cl55}
    (h1 : ω₁ * ω₁ = ω₁) (h2 : ω₂ * ω₂ = ω₂)
    (h12 : ω₁ * ω₂ = ω₁) (h21 : ω₂ * ω₁ = ω₁)
    (k n m l : ℕ)
    (A_cl C_cl X_cl Y_cl Z_cl : InfoGeometry.Clifford.Clifford55.Cl55) :
    let ω := InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent
    let P_lim := ofStage 5 (cl55ToStage5 ω)
    let P₁_lim := ofStage 5 (cl55ToStage5 ω₁)
    let P₂_lim := ofStage 5 (cl55ToStage5 ω₂)
    let A_lim := ofStage 5 (cl55ToStage5 A_cl)
    let C_lim := ofStage 5 (cl55ToStage5 C_cl)
    let X_lim := ofStage 5 (cl55ToStage5 X_cl)
    let Y_lim := ofStage 5 (cl55ToStage5 Y_cl)
    let Z_lim := ofStage 5 (cl55ToStage5 Z_cl)
    (ofStage (5 + 8 * k) (cl55ToBottStage k (drinfeldXPlus n ω A_cl C_cl)) =
       drinfeldXPlus n P_lim A_lim C_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (drinfeldXMinus n ω A_cl C_cl)) =
       drinfeldXMinus n P_lim A_lim C_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (fourMassBoxSqrt ω A_cl C_cl)) =
       fourMassBoxSqrt P_lim A_lim C_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (borelCorner12 ω₁ ω₂ X_cl)) =
       borelCorner12 P₁_lim P₂_lim X_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (borelCorner23 ω₁ ω₂ Y_cl)) =
       borelCorner23 P₁_lim P₂_lim Y_lim ∧
     ofStage (5 + 8 * k) (cl55ToBottStage k (borelCorner13 ω₁ ω₂ Z_cl)) =
       borelCorner13 P₁_lim P₂_lim Z_lim) ∧
    (dressedCurv (1 + conePlus P_lim A_lim) (1 - conePlus P_lim A_lim)
       (drinfeldXPlus n P_lim A_lim C_lim) =
       drinfeldXPlus n P_lim A_lim C_lim ∧
     dressedCurv (1 + conePlus P_lim A_lim) (1 - conePlus P_lim A_lim)
       (drinfeldXMinus n P_lim A_lim C_lim) =
       drinfeldXMinus n P_lim A_lim C_lim - drinfeldPhiPlus n P_lim A_lim C_lim +
         drinfeldPhiMinus n P_lim A_lim C_lim - drinfeldXPlus (n + 1) P_lim A_lim C_lim ∧
     dressedCurv (1 + conePlus P_lim A_lim) (1 - conePlus P_lim A_lim)
       (drinfeldPhiPlus n P_lim A_lim C_lim + drinfeldPhiMinus n P_lim A_lim C_lim) =
       opPow (n + 1) (genV P_lim A_lim C_lim) ∧
     algSymbolFactorPlus P_lim A_lim C_lim
         (polygonFibSeq P_lim A_lim C_lim m) (eisensteinSeq P_lim A_lim C_lim l) *
       algSymbolFactorMinus P_lim A_lim C_lim
         (polygonFibSeq P_lim A_lim C_lim m) (eisensteinSeq P_lim A_lim C_lim l) =
       polygonFibSeq P_lim A_lim C_lim m * polygonFibSeq P_lim A_lim C_lim m -
         eisensteinSeq P_lim A_lim C_lim l * eisensteinSeq P_lim A_lim C_lim l *
           fourMassBoxDisc P_lim A_lim C_lim) ∧
    (P₁_lim + flagStratumIdem P₁_lim P₂_lim + (1 - P₂_lim) = 1 ∧
     comm (borelCorner12 P₁_lim P₂_lim X_lim) (borelCorner23 P₁_lim P₂_lim Y_lim) =
       borelCorner13 P₁_lim P₂_lim (X_lim * flagStratumIdem P₁_lim P₂_lim * Y_lim) ∧
     maurerCartanCocycle (comm P₁_lim)
       (1 + borelCorner12 P₁_lim P₂_lim X_lim) (1 - borelCorner12 P₁_lim P₂_lim X_lim) =
       borelCorner12 P₁_lim P₂_lim X_lim ∧
     maurerCartanCocycle (comm P₂_lim)
       (1 + borelCorner23 P₁_lim P₂_lim Y_lim) (1 - borelCorner23 P₁_lim P₂_lim Y_lim) =
       borelCorner23 P₁_lim P₂_lim Y_lim ∧
     maurerCartanCocycle (comm P₁_lim)
       (1 + borelCorner13 P₁_lim P₂_lim Z_lim) (1 - borelCorner13 P₁_lim P₂_lim Z_lim) =
       borelCorner13 P₁_lim P₂_lim Z_lim) ∧
    (polygonFibSeq P_lim A_lim C_lim (m + 1) * polygonFibSeq P_lim A_lim C_lim (m + 1) -
       polygonFibSeq P_lim A_lim C_lim (m + 2) * polygonFibSeq P_lim A_lim C_lim m =
       (-genV P_lim A_lim C_lim) ^ m ∧
     eisensteinSeq P_lim A_lim C_lim (m + 1) * eisensteinSeq P_lim A_lim C_lim (m + 1) -
       eisensteinSeq P_lim A_lim C_lim (m + 2) * eisensteinSeq P_lim A_lim C_lim m =
       (genV P_lim A_lim C_lim) ^ m ∧
     comm (drinfeldXPlus n P_lim A_lim C_lim) (drinfeldXMinus m P_lim A_lim C_lim) =
       drinfeldPhiPlus (n + m) P_lim A_lim C_lim - drinfeldPhiMinus (n + m) P_lim A_lim C_lim ∧
     anticomm (drinfeldXPlus n P_lim A_lim C_lim) (drinfeldXMinus m P_lim A_lim C_lim) =
       opPow (n + m + 1) (genV P_lim A_lim C_lim)) :=
  cl55_multi_period_bott_stage_D26_D27_dressing_and_quantum_affine_colimit_bridge
    InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdempotent_idempotent
    h1 h2 h12 h21 k n m l A_cl C_cl X_cl Y_cl Z_cl

/-!
## 18. Stage `D₂₉` (`Z₁ → Z₅`): Split Cayley / Zorn–Peirce Matrix Algebra, Quadratic Norm,
Complex Tetrad Gravito-Electromagnetic Decomposition & `2ⁿ × 2ⁿ` Inductive Colimit Bridge
-/

/-- **Theorem 18.1 (`zornMatrix_self_eq_and_chiralPlane_soldering`):**
1. For any idempotent `P` (`P * P = P`) and any `X : B`, the 4-block Peirce decomposition
   recovers `X` identically via `zornMatrix P X X (-X) X = X`.
2. In particular, for any spatial axis `i : Fin 3` and any `X : OperatorZornMatrix B`, the
   `2 × 2` chiral-plane matrix `zornChiralPlaneMatrix i X` is soldered directly to `zornMatrix`
   at `P = peirceSheetProj`. -/
theorem zornMatrix_self_eq_and_chiralPlane_soldering
    {P : B} (hP : P * P = P) (X : B)
    (i : Fin 3) (M : InfoGeometry.Canonical.OperatorZornMatrix B) :
    zornMatrix P X X (-X) X = X ∧
    zornConj P (zornMatrix P X X (-X) X) = zornMatrix P X X X (-X) ∧
    zornMatrix (peirceSheetProj (A := B))
        (zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)
        (-zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M) =
      zornChiralPlaneMatrix i M ∧
    zornConj (peirceSheetProj (A := B))
        (zornMatrix (peirceSheetProj (A := B))
          (zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)
          (-zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)) =
      zornMatrix (peirceSheetProj (A := B))
        (zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)
        (zornChiralPlaneMatrix i M) (-zornChiralPlaneMatrix i M) := by
  have hSelf1 : zornMatrix P X X (-X) X = X := by
    unfold zornMatrix OperatorAlgebra.PeirceSpine.peirce11 OperatorAlgebra.PeirceSpine.peirce00
      conePlus coneMinus
    noncomm_ring
  have hSelf2 :
      zornMatrix (peirceSheetProj (A := B))
        (zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)
        (-zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M) =
      zornChiralPlaneMatrix i M := by
    unfold zornMatrix OperatorAlgebra.PeirceSpine.peirce11 OperatorAlgebra.PeirceSpine.peirce00
      conePlus coneMinus
    noncomm_ring
  have hConj1 : zornConj P (zornMatrix P X X (-X) X) = zornMatrix P X X X (-X) := by
    rw [(zorn_conjugation_and_quadratic_norms hP X X (-X) X).1, neg_neg]
  have hConj2 :
      zornConj (peirceSheetProj (A := B))
        (zornMatrix (peirceSheetProj (A := B))
          (zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)
          (-zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)) =
      zornMatrix (peirceSheetProj (A := B))
        (zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)
        (zornChiralPlaneMatrix i M) (-zornChiralPlaneMatrix i M) := by
    rw [(zorn_conjugation_and_quadratic_norms (peirceSheetProj_idem (A := B))
      (zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)
      (-zornChiralPlaneMatrix i M) (zornChiralPlaneMatrix i M)).1, neg_neg]
  exact ⟨hSelf1, hConj1, hSelf2, hConj2⟩

/-- **Theorem 18.2 (`limit_stage_D29_zorn_matrix_algebra_and_complex_tetrad_bridge`):**
Transports Stage `D₂₉` (`Z₁ → Z₅`: Split Cayley / Zorn–Peirce matrix representation `zornMatrix`,
non-commutative Zorn block product, Zorn quadratic norm `zornNorm`, complex tetrad symmetric metric
`zornTetradSym` vs. antisymmetric 2-form `zornTetradSkew`, and the unified gravito-electromagnetic
square `(Φ₁ + J₂)² = (V₁ - V₂) - G_{[12]}`) across the `2ⁿ × 2ⁿ` tensor-tower bonding maps
`bondMap stageBond n m hnm : Stage n →+* Stage m` and into the inductive colimit `Limit`. -/
theorem limit_stage_D29_zorn_matrix_algebra_and_complex_tetrad_bridge
    {n m : ℕ} (hnm : n ≤ m)
    {P : Stage n} (hP : P * P = P) (hPsym : star P = P)
    (a b c d x y z w A₁ C₁ A₂ C₂ : Stage n) :
    let P_lim := ofStage n P
    let a_lim := ofStage n a
    let b_lim := ofStage n b
    let c_lim := ofStage n c
    let d_lim := ofStage n d
    let x_lim := ofStage n x
    let y_lim := ofStage n y
    let z_lim := ofStage n z
    let w_lim := ofStage n w
    let A₁_lim := ofStage n A₁
    let C₁_lim := ofStage n C₁
    let A₂_lim := ofStage n A₂
    let C₂_lim := ofStage n C₂
    -- 1. Multi-step bonding & colimit compatibility:
    ofStage m (bondMap stageBond n m hnm (zornMatrix P a b x y)) =
      ofStage n (zornMatrix P a b x y) ∧
    ofStage m (bondMap stageBond n m hnm (zornTetradSym P A₁ C₁ A₂ C₂)) =
      ofStage n (zornTetradSym P A₁ C₁ A₂ C₂) ∧
    ofStage m (bondMap stageBond n m hnm (zornTetradSkew P A₁ C₁ A₂ C₂)) =
      ofStage n (zornTetradSkew P A₁ C₁ A₂ C₂) ∧
    -- 2. Colimit Non-Commutative Zorn Matrix Multiplication Law (`Z₁` & `Z₂`):
    zornMatrix P_lim a_lim b_lim x_lim y_lim * zornMatrix P_lim c_lim d_lim z_lim w_lim =
      (OperatorAlgebra.PeirceSpine.peirce11 P_lim a_lim *
          OperatorAlgebra.PeirceSpine.peirce11 P_lim c_lim - qgtPlus P_lim x_lim w_lim) -
      (OperatorAlgebra.PeirceSpine.peirce11 P_lim a_lim * conePlus P_lim z_lim +
          conePlus P_lim x_lim * OperatorAlgebra.PeirceSpine.peirce00 P_lim d_lim) +
      (coneMinus P_lim y_lim * OperatorAlgebra.PeirceSpine.peirce11 P_lim c_lim +
          OperatorAlgebra.PeirceSpine.peirce00 P_lim b_lim * coneMinus P_lim w_lim) +
      (OperatorAlgebra.PeirceSpine.peirce00 P_lim b_lim *
          OperatorAlgebra.PeirceSpine.peirce00 P_lim d_lim - qgtMinus P_lim z_lim y_lim) ∧
    -- 3. Colimit Zorn Conjugation & Quadratic Norms (`Z₃`):
    zornNorm P_lim (zornMatrix P_lim 1 1 x_lim (-y_lim)) = 1 - genV P_lim x_lim y_lim ∧
    zornNorm P_lim (genV P_lim x_lim y_lim + genPhi P_lim x_lim y_lim) =
      idemDefect (genV P_lim x_lim y_lim) ∧
    -- 4. Colimit Complex Tetrad Symmetric Metric `G_{(12)}` vs. Antisymmetric 2-Form `G_{[12]}` (`Z₄`):
    anticomm (genPhi P_lim A₁_lim C₁_lim) (genPhi P_lim A₂_lim C₂_lim) =
      zornTetradSym P_lim A₁_lim C₁_lim A₂_lim C₂_lim ∧
    OperatorAlgebra.PeirceSpine.comm (genPhi P_lim A₁_lim C₁_lim) (genPhi P_lim A₂_lim C₂_lim) =
      zornTetradSkew P_lim A₁_lim C₁_lim A₂_lim C₂_lim ∧
    OperatorAlgebra.PeirceSpine.comm P_lim (zornTetradSym P_lim A₁_lim C₁_lim A₂_lim C₂_lim) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm P_lim (zornTetradSkew P_lim A₁_lim C₁_lim A₂_lim C₂_lim) = 0 ∧
    -- 5. Colimit Unified Gravito-Electromagnetic Squares & Star Reality (`Z₅`):
    (genPhi P_lim A₁_lim C₁_lim + genPhi P_lim A₂_lim C₂_lim) *
        (genPhi P_lim A₁_lim C₁_lim - genPhi P_lim A₂_lim C₂_lim) =
      (genV P_lim A₁_lim C₁_lim - genV P_lim A₂_lim C₂_lim) -
        zornTetradSkew P_lim A₁_lim C₁_lim A₂_lim C₂_lim ∧
    (genPhi P_lim A₁_lim C₁_lim + genJ P_lim A₂_lim C₂_lim) *
        (genPhi P_lim A₁_lim C₁_lim + genJ P_lim A₂_lim C₂_lim) =
      genV P_lim A₁_lim C₁_lim - genV P_lim A₂_lim C₂_lim -
        (anticomm (conePlus P_lim A₁_lim) (coneMinus P_lim C₂_lim) -
          anticomm (conePlus P_lim A₂_lim) (coneMinus P_lim C₁_lim)) ∧
    star (zornTetradSym P_lim A₁_lim (star A₁_lim) A₂_lim (star A₂_lim)) =
      zornTetradSym P_lim A₁_lim (star A₁_lim) A₂_lim (star A₂_lim) ∧
    star (zornTetradSkew P_lim A₁_lim (star A₁_lim) A₂_lim (star A₂_lim)) =
      -zornTetradSkew P_lim A₁_lim (star A₁_lim) A₂_lim (star A₂_lim) := by
  dsimp only
  have hPLim : ofStage n P * ofStage n P = ofStage n P := by
    rw [← map_mul, hP]
  have hPSymLim : star (ofStage n P) = ofStage n P := by
    rw [← ofStage_star, hPsym]
  rcases stage_D29_zorn_matrix_algebra_and_complex_tetrad_master_synthesis
      (a := ofStage n a) (b := ofStage n b) (c := ofStage n c) (d := ofStage n d)
      (x := ofStage n x) (y := ofStage n y) (z := ofStage n z) (w := ofStage n w)
      (A₁ := ofStage n A₁) (C₁ := ofStage n C₁) (A₂ := ofStage n A₂) (C₂ := ofStage n C₂)
      hPLim hPSymLim with
    ⟨hZ1, hZ2, hZ3, hZ4, hZ5, hZ6, hZ7, hZ8, hZ9, hZ10, hZ11⟩
  exact ⟨directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         hZ1, hZ2, hZ3, hZ4, hZ5, hZ6, hZ7, hZ8, hZ9, hZ10, hZ11⟩

/-- **Theorem 18.3 (`cl55_multi_period_bott_and_limit_stage_D29_D32_zorn_tetrad_drinfeld_master_bridge`):**
Transports Stage `D₃₂` (upper-sheet Zorn–Weyl gravito-electromagnetic square
`((Φ₁ + J₂)² ) · P = ((V₁ - V₂) - G_{[12]}) · P`, lower-sheet QGT residual
`-2 • (qgtMinus P A₁ C₂ - qgtMinus P A₂ C₁)`, mode-graded Zorn–Drinfeld–Virasoro matrix
`zornDrinfeldMatrix r r P A C`, and its Zorn norm `opPow (r + r) (genV P A C) - virasoroModeEven (r + r) P A C`)
across all `8p` Bott periods `ofStage (5 + 8 * p) ∘ cl55ToBottStage p : Cl55 →+* Limit` into `Limit`. -/
theorem cl55_multi_period_bott_and_limit_stage_D29_D32_zorn_tetrad_drinfeld_master_bridge
    {ω : InfoGeometry.Clifford.Clifford55.Cl55} (hω : ω * ω = ω)
    (A_cl C_cl A₁_cl C₁_cl A₂_cl C₂_cl : InfoGeometry.Clifford.Clifford55.Cl55)
    (p r : ℕ) :
    let P_lim := ofStage 5 (cl55ToStage5 ω)
    let A_lim := ofStage 5 (cl55ToStage5 A_cl)
    let C_lim := ofStage 5 (cl55ToStage5 C_cl)
    let A₁_lim := ofStage 5 (cl55ToStage5 A₁_cl)
    let C₁_lim := ofStage 5 (cl55ToStage5 C₁_cl)
    let A₂_lim := ofStage 5 (cl55ToStage5 A₂_cl)
    let C₂_lim := ofStage 5 (cl55ToStage5 C₂_cl)
    ofStage (5 + 8 * p) (cl55ToBottStage p ω) = P_lim ∧
    ((genPhi P_lim A₁_lim C₁_lim + genJ P_lim A₂_lim C₂_lim) *
        (genPhi P_lim A₁_lim C₁_lim + genJ P_lim A₂_lim C₂_lim)) * P_lim =
      ((genV P_lim A₁_lim C₁_lim - genV P_lim A₂_lim C₂_lim) -
        zornTetradSkew P_lim A₁_lim C₁_lim A₂_lim C₂_lim) * P_lim ∧
    (genPhi P_lim A₁_lim C₁_lim + genJ P_lim A₂_lim C₂_lim) *
        (genPhi P_lim A₁_lim C₁_lim + genJ P_lim A₂_lim C₂_lim) =
      ((genV P_lim A₁_lim C₁_lim - genV P_lim A₂_lim C₂_lim) -
        zornTetradSkew P_lim A₁_lim C₁_lim A₂_lim C₂_lim) -
        (2 : ℤ) • (qgtMinus P_lim A₁_lim C₂_lim - qgtMinus P_lim A₂_lim C₁_lim) ∧
    zornDrinfeldMatrix r r P_lim A_lim C_lim =
      opPow r (genV P_lim A_lim C_lim) +
        heisenbergSourceMode r P_lim A_lim C_lim +
        heisenbergSinkMode r P_lim A_lim C_lim ∧
    zornNorm P_lim (zornDrinfeldMatrix r r P_lim A_lim C_lim) =
      opPow (r + r) (genV P_lim A_lim C_lim) -
        virasoroModeEven (r + r) P_lim A_lim C_lim := by
  dsimp only
  have hBott :
      ofStage (5 + 8 * p) (cl55ToBottStage p ω) = ofStage 5 (cl55ToStage5 ω) := by
    unfold cl55ToBottStage
    exact directLimitOf_bondMap stageBond 5 (5 + 8 * p) (Nat.le_add_right 5 (8 * p))
      (cl55ToStage5 ω)
  have hP5 : cl55ToStage5 ω * cl55ToStage5 ω = cl55ToStage5 ω :=
    map_idempotent cl55ToStage5 hω
  have hPLim :
      ofStage 5 (cl55ToStage5 ω) * ofStage 5 (cl55ToStage5 ω) =
        ofStage 5 (cl55ToStage5 ω) :=
    map_idempotent (ofStage 5) hP5
  rcases zorn_tetrad_upper_sheet_and_lower_qgt_residual hPLim
      (ofStage 5 (cl55ToStage5 A₁_cl)) (ofStage 5 (cl55ToStage5 C₁_cl))
      (ofStage 5 (cl55ToStage5 A₂_cl)) (ofStage 5 (cl55ToStage5 C₂_cl)) with
    ⟨_, _, hRes, hUpper⟩
  rcases zornDrinfeldMatrix_eq_and_zornNorm hPLim
      (ofStage 5 (cl55ToStage5 A_cl)) (ofStage 5 (cl55ToStage5 C_cl)) r with
    ⟨hDrinEq, _, hDrinNorm⟩
  exact ⟨hBott, hUpper, hRes, hDrinEq, hDrinNorm⟩

/-!
## 19. Stage `D₃₀` (`N₁ → N₅`): Furey's Universal Lie–Jordan Product, Quaternionic Symmetry Breaking,
Associative-Ring Corner Map & Non-Commutative Operator Hopf Coordinate Identities in `Limit`
-/

/-- **Theorem 19.1 (`limit_stage_D30_furey_lie_jordan_corner_hopf_bridge`):**
Transports Stage `D₃₀` (`N₁ → N₅`: Furey's universal Lie–Jordan product `fureyProduct`,
quaternionic sector symmetry breaking `chargeQ6 - chargeY6 = 3 • quatChiralInv`, the
multiplicative corner map `inducedEndoRep` on an associative ring, and non-commutative operator Hopf coordinate identities
`hopfCoordZ`, `hopfCoordPerp`, `hopfRadiusSq`) across `bondMap stageBond n m hnm : Stage n →+* Stage m`
and into the `Cl(1, 1)^{\otimes n}` inductive colimit `Limit`. -/
theorem limit_stage_D30_furey_lie_jordan_corner_hopf_bridge
    {n m : ℕ} (hnm : n ≤ m)
    {P P_O2 P_H1 P_H2 P_C ι ι_inv h h' u u' X A : Stage n}
    (hP : P * P = P) (hPsym : star P = P)
    (hh : star h = h) (hh' : star h' = h')
    (hu : star u = -u) (hu' : star u' = -u')
    (hH1 : P_H1 * P_H1 = P_H1) (hH2 : P_H2 * P_H2 = P_H2)
    (hH12 : P_H1 * P_H2 = 0) (hH21 : P_H2 * P_H1 = 0)
    (hO_H1 : P_O2 * P_H1 = 0) (hH2_O : P_H2 * P_O2 = 0)
    (hC_H1 : P_C * P_H1 = 0) (hH2_C : P_H2 * P_C = 0)
    (hEmb : ι_inv * ι = 1) :
    let P_lim := ofStage n P
    let P_O2_lim := ofStage n P_O2
    let P_H1_lim := ofStage n P_H1
    let P_H2_lim := ofStage n P_H2
    let P_C_lim := ofStage n P_C
    let ι_lim := ofStage n ι
    let ι_inv_lim := ofStage n ι_inv
    let h_lim := ofStage n h
    let h'_lim := ofStage n h'
    let u_lim := ofStage n u
    let u'_lim := ofStage n u'
    let X_lim := ofStage n X
    let A_lim := ofStage n A
    -- 1. Multi-step bonding & colimit compatibility:
    ofStage m (bondMap stageBond n m hnm (fureyProduct h h')) =
      ofStage n (fureyProduct h h') ∧
    ofStage m (bondMap stageBond n m hnm (chargeY6 P_O2 P_H1 P_H2 P_C)) =
      ofStage n (chargeY6 P_O2 P_H1 P_H2 P_C) ∧
    ofStage m (bondMap stageBond n m hnm (chargeQ6 P_O2 P_H2 P_C)) =
      ofStage n (chargeQ6 P_O2 P_H2 P_C) ∧
    -- 2. Colimit Furey Universal Lie–Jordan Quartet & Tetraktys Realization (`N₁`):
    fureyProduct h_lim h'_lim = anticomm h_lim h'_lim ∧
    fureyProduct u_lim u'_lim = OperatorAlgebra.PeirceSpine.comm u_lim u'_lim ∧
    fureyProduct h_lim u_lim = anticomm h_lim u_lim ∧
    fureyProduct u_lim h_lim = OperatorAlgebra.PeirceSpine.comm u_lim h_lim ∧
    fureyProduct (genPhi P_lim A_lim (star A_lim)) (genPhi P_lim A_lim (star A_lim)) =
      (2 : ℤ) • genV P_lim A_lim (star A_lim) ∧
    fureyProduct (genJ P_lim A_lim (star A_lim)) (genPhi P_lim A_lim (star A_lim)) =
      (2 : ℤ) • genSig P_lim A_lim (star A_lim) ∧
    -- 3. Colimit Quaternionic Sector Symmetry Breaking (`N₂` & `N₃`):
    chargeQ6 P_O2_lim P_H2_lim P_C_lim - chargeY6 P_O2_lim P_H1_lim P_H2_lim P_C_lim =
      (3 : ℤ) • quatChiralInv P_H1_lim P_H2_lim ∧
    OperatorAlgebra.PeirceSpine.comm
        (chargeY6 P_O2_lim P_H1_lim P_H2_lim P_C_lim) (P_H1_lim * X_lim * P_H2_lim) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm
        (chargeQ6 P_O2_lim P_H2_lim P_C_lim) (P_H1_lim * X_lim * P_H2_lim) =
      -(6 : ℤ) • (P_H1_lim * X_lim * P_H2_lim) ∧
    -- 4. Colimit Equivariant Cayley–Dickson Embedding Intertwining (`N₄`):
    inducedEndoRep ι_lim ι_inv_lim X_lim * ι_lim = ι_lim * X_lim ∧
    Function.Injective (inducedEndoRep ι_lim ι_inv_lim) ∧
    -- 5. Colimit Non-Commutative Operator Hopf Coordinate Identities (`N₅`):
    hopfCoordZ P_lim (conePlus P_lim A_lim) = P_lim - qgtPlus P_lim A_lim (star A_lim) ∧
    hopfCoordPerp P_lim (conePlus P_lim A_lim) = 0 ∧
    hopfCoordZ (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim)) =
      genSig P_lim A_lim (star A_lim) ∧
    hopfCoordZ (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim)) *
      hopfCoordZ (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim)) +
      hopfCoordPerp (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim)) *
      hopfCoordPerp (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim)) =
      hopfRadiusSq (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim)) *
      hopfRadiusSq (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim)) ∧
    star (hopfRadiusSq (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim))) =
      hopfRadiusSq (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim)) := by
  dsimp only
  have hPLim : ofStage n P * ofStage n P = ofStage n P := by rw [← map_mul, hP]
  have hPSymLim : star (ofStage n P) = ofStage n P := by rw [← ofStage_star, hPsym]
  have hhLim : star (ofStage n h) = ofStage n h := by rw [← ofStage_star, hh]
  have hh'Lim : star (ofStage n h') = ofStage n h' := by rw [← ofStage_star, hh']
  have huLim : star (ofStage n u) = -ofStage n u := by rw [← ofStage_star, hu, map_neg]
  have hu'Lim : star (ofStage n u') = -ofStage n u' := by rw [← ofStage_star, hu', map_neg]
  have hH1Lim : ofStage n P_H1 * ofStage n P_H1 = ofStage n P_H1 := by rw [← map_mul, hH1]
  have hH2Lim : ofStage n P_H2 * ofStage n P_H2 = ofStage n P_H2 := by rw [← map_mul, hH2]
  have hH12Lim : ofStage n P_H1 * ofStage n P_H2 = 0 := by rw [← map_mul, hH12, map_zero]
  have hH21Lim : ofStage n P_H2 * ofStage n P_H1 = 0 := by rw [← map_mul, hH21, map_zero]
  have hOH1Lim : ofStage n P_O2 * ofStage n P_H1 = 0 := by rw [← map_mul, hO_H1, map_zero]
  have hH2OLim : ofStage n P_H2 * ofStage n P_O2 = 0 := by rw [← map_mul, hH2_O, map_zero]
  have hCH1Lim : ofStage n P_C * ofStage n P_H1 = 0 := by rw [← map_mul, hC_H1, map_zero]
  have hH2CLim : ofStage n P_H2 * ofStage n P_C = 0 := by rw [← map_mul, hH2_C, map_zero]
  have hEmbLim : ofStage n ι_inv * ofStage n ι = 1 := by rw [← map_mul, hEmb, map_one]
  have hEmbInjectiveLim := inducedEndoRep_injective_of_leftInverse hEmbLim
  rcases stage_D30_furey_lie_jordan_corner_hopf_master_synthesis
      (X := ofStage n X) (A := ofStage n A)
      hPLim hPSymLim hhLim hh'Lim huLim hu'Lim
      hH1Lim hH2Lim hH12Lim hH21Lim hOH1Lim hH2OLim hCH1Lim hH2CLim hEmbLim with
    ⟨hN1, hN2, hN3, hN4, hN5, hN6, hN7, hN8, hN9, hN10, hN11, hN12, hN13, hN14⟩
  rcases fureyProduct_genPhi_genJ_tetraktys hPLim hPSymLim (ofStage n A) with
    ⟨hTetV, _, _, hTetSig⟩
  exact ⟨directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         hN1, hN2, hN3, hN4, hTetV, hTetSig,
         hN5, hN6, hN7, hN8, hEmbInjectiveLim,
         hN10, hN11, hN12, hN13, hN14⟩

/-- **Theorem 19.2 (`cl55_multi_period_bott_and_limit_stages_D33_D34_D35_hopf_zorn_flag_virasoro_bridge`):**
Transports Stages `D₃₃`–`D₃₅` (Hopf–Zorn matrix soldering `hopf_zorn_matrix_soldering_and_norm`,
4-stratum partial-flag charge decomposition `partial_flag_sector_quaternionic_symmetry_breaking_and_step_charges`,
and the all-mode Heisenberg–Virasoro Hopf coordinate tower `all_mode_heisenberg_virasoro_hopf_coordinate_identity_and_furey_tower`)
into the inductive colimit `Limit` along `ofStage (5 + 8 * p) ∘ cl55ToBottStage p : Cl55 →+* Limit`. -/
theorem cl55_multi_period_bott_and_limit_stages_D33_D34_D35_hopf_zorn_flag_virasoro_bridge
    {n : ℕ} {P : Stage n} (hP : P * P = P) (hPsym : star P = P) (A : Stage n)
    {ω₁ ω₂ ω₃ : InfoGeometry.Clifford.Clifford55.Cl55}
    (h1 : ω₁ * ω₁ = ω₁) (h2 : ω₂ * ω₂ = ω₂) (h3 : ω₃ * ω₃ = ω₃)
    (h12 : ω₁ * ω₂ = ω₁) (h21 : ω₂ * ω₁ = ω₁)
    (h23 : ω₂ * ω₃ = ω₂) (h32 : ω₃ * ω₂ = ω₂)
    (h13 : ω₁ * ω₃ = ω₁) (h31 : ω₃ * ω₁ = ω₁)
    (X_cl : InfoGeometry.Clifford.Clifford55.Cl55)
    (p r : ℕ) :
    let P_lim := ofStage n P
    let A_lim := ofStage n A
    let P₁_lim := ofStage 5 (cl55ToStage5 ω₁)
    let P₂_lim := ofStage 5 (cl55ToStage5 ω₂)
    let P₃_lim := ofStage 5 (cl55ToStage5 ω₃)
    let X_lim := ofStage 5 (cl55ToStage5 X_cl)
    let P_O2 := P₁_lim
    let P_H1 := flagStratumIdem P₁_lim P₂_lim
    let P_H2 := flagStratumIdem P₂_lim P₃_lim
    let P_C := 1 - P₃_lim
    -- 1. `Cl(5, 5)` Multi-Period Bott Compatibility (`8p` shifts):
    ofStage (5 + 8 * p) (cl55ToBottStage p ω₁) = P₁_lim ∧
    ofStage (5 + 8 * p) (cl55ToBottStage p ω₂) = P₂_lim ∧
    ofStage (5 + 8 * p) (cl55ToBottStage p ω₃) = P₃_lim ∧
    -- 2. Stage `D₃₃`: Colimit Hopf–Zorn Matrix Soldering & Quadratic Norm:
    zornMatrix P_lim (hopfCoordZ P_lim (conePlus P_lim A_lim))
        (1 - qgtMinus P_lim A_lim (star A_lim)) (-A_lim) (star A_lim) =
      (1 - genV P_lim A_lim (star A_lim)) + genPhi P_lim A_lim (star A_lim) ∧
    zornNorm P_lim (genV P_lim A_lim (star A_lim) + genPhi P_lim A_lim (star A_lim)) =
      idemDefect (hopfRadiusSq (conePlus P_lim A_lim) (coneMinus P_lim (star A_lim))) ∧
    -- 3. Stage `D₃₄`: Colimit Partial-Flag 4-Sector Quaternionic Symmetry Breaking & Step Charges:
    P_O2 + P_H1 + P_H2 + P_C = 1 ∧
    chargeQ6 P_O2 P_H2 P_C - chargeY6 P_O2 P_H1 P_H2 P_C =
      (3 : ℤ) • quatChiralInv P_H1 P_H2 ∧
    OperatorAlgebra.PeirceSpine.comm (chargeY6 P_O2 P_H1 P_H2 P_C) (flagStepCorner P_H1 P_H2 X_lim) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (chargeQ6 P_O2 P_H2 P_C) (flagStepCorner P_H1 P_H2 X_lim) =
      -(6 : ℤ) • flagStepCorner P_H1 P_H2 X_lim ∧
    OperatorAlgebra.PeirceSpine.comm (chargeY6 P_O2 P_H1 P_H2 P_C) (flagStepCorner P_O2 P_H1 X_lim) =
      -flagStepCorner P_O2 P_H1 X_lim ∧
    OperatorAlgebra.PeirceSpine.comm (chargeQ6 P_O2 P_H2 P_C) (flagStepCorner P_O2 P_H1 X_lim) =
      (2 : ℤ) • flagStepCorner P_O2 P_H1 X_lim ∧
    -- 4. Stage `D₃₅`: Colimit All-Mode Heisenberg–Virasoro Hopf Coordinate Identity & Algebraic Square Relation:
    hopfCoordZ (heisenbergSourceMode r P_lim A_lim (star A_lim))
        (heisenbergSinkMode r P_lim A_lim (star A_lim)) =
      virasoroModeChiral (r + r) P_lim A_lim (star A_lim) ∧
    hopfCoordPerp (heisenbergSourceMode r P_lim A_lim (star A_lim))
        (heisenbergSinkMode r P_lim A_lim (star A_lim)) = 0 ∧
    hopfRadiusSq (heisenbergSourceMode r P_lim A_lim (star A_lim))
        (heisenbergSinkMode r P_lim A_lim (star A_lim)) =
      virasoroModeEven (r + r) P_lim A_lim (star A_lim) ∧
    hopfCoordZ (heisenbergSourceMode r P_lim A_lim (star A_lim))
          (heisenbergSinkMode r P_lim A_lim (star A_lim)) *
        hopfCoordZ (heisenbergSourceMode r P_lim A_lim (star A_lim))
          (heisenbergSinkMode r P_lim A_lim (star A_lim)) +
      hopfCoordPerp (heisenbergSourceMode r P_lim A_lim (star A_lim))
          (heisenbergSinkMode r P_lim A_lim (star A_lim)) *
        hopfCoordPerp (heisenbergSourceMode r P_lim A_lim (star A_lim))
          (heisenbergSinkMode r P_lim A_lim (star A_lim)) =
      virasoroModeEven (r + r + (r + r) + 1) P_lim A_lim (star A_lim) ∧
    fureyProduct (heisenbergSourceMode r P_lim A_lim (star A_lim))
        (heisenbergSourceMode r P_lim A_lim (star A_lim)) =
      heisenbergSourceMode r P_lim A_lim (star A_lim) *
        heisenbergSinkMode r P_lim A_lim (star A_lim) := by
  dsimp only
  have hBott : ∀ z : InfoGeometry.Clifford.Clifford55.Cl55,
      ofStage (5 + 8 * p) (cl55ToBottStage p z) = ofStage 5 (cl55ToStage5 z) := by
    intro z; unfold cl55ToBottStage
    exact directLimitOf_bondMap stageBond 5 (5 + 8 * p) (Nat.le_add_right 5 (8 * p))
      (cl55ToStage5 z)
  have hPLim : ofStage n P * ofStage n P = ofStage n P := by rw [← map_mul, hP]
  have hPSymLim : star (ofStage n P) = ofStage n P := by rw [← ofStage_star, hPsym]
  let φ : InfoGeometry.Clifford.Clifford55.Cl55 →+* Limit :=
    (ofStage 5).comp cl55ToStage5
  have h1L : φ ω₁ * φ ω₁ = φ ω₁ := map_idempotent φ h1
  have h2L : φ ω₂ * φ ω₂ = φ ω₂ := map_idempotent φ h2
  have h3L : φ ω₃ * φ ω₃ = φ ω₃ := map_idempotent φ h3
  have h12L : φ ω₁ * φ ω₂ = φ ω₁ := by rw [← map_mul, h12]
  have h21L : φ ω₂ * φ ω₁ = φ ω₁ := by rw [← map_mul, h21]
  have h23L : φ ω₂ * φ ω₃ = φ ω₂ := by rw [← map_mul, h23]
  have h32L : φ ω₃ * φ ω₂ = φ ω₂ := by rw [← map_mul, h32]
  have h13L : φ ω₁ * φ ω₃ = φ ω₁ := by rw [← map_mul, h13]
  have h31L : φ ω₃ * φ ω₁ = φ ω₁ := by rw [← map_mul, h31]
  rcases hopf_zorn_matrix_soldering_and_norm hPLim hPSymLim (ofStage n A) with
    ⟨hHZ1, _, hHZ3⟩
  rcases partial_flag_sector_quaternionic_symmetry_breaking_and_step_charges
      h1L h2L h3L h12L h21L h23L h32L h13L h31L (φ X_cl) with
    ⟨hPart, hDiff, _, hY23, hQ23, hY12, hQ12⟩
  rcases all_mode_heisenberg_virasoro_hopf_coordinate_identity_and_furey_tower
      hPLim hPSymLim (ofStage n A) r with
    ⟨_, _, hHVZ, hHVPerp, hHVRad, hHVSph, hHVFur⟩
  exact ⟨hBott ω₁, hBott ω₂, hBott ω₃,
         hHZ1, hHZ3,
         hPart, hDiff, hY23, hQ23, hY12, hQ12,
         hHVZ, hHVPerp, hHVRad, hHVSph, hHVFur⟩

/-!
## 20. Stage `D₃₁` (`G₁ → G₆`): Scale-12 / Scale-24 Kantor–Peirce Charge Frames, Scale-144 / Scale-576 Bilateral Compressions, and All-Scale Single-Sheet Decoders in `Limit`
-/

/-- **Theorem 20.1 (`limit_stage_D31_golay_leech_mog_sheet_decoders_bridge`):**
Transports Stage `D₃₁` (`G₁ → G₆`: Scale-12 3-sector and Scale-24 5-sector Kantor–Peirce charge
frames `golay12Core`, `golay12Root`, `golay12Ext`, `golay24G0..golay24Gm2`, Scale-144 / Scale-576
bilateral sandwich compressions, all-scale `(k, r) ∈ ℕ × ℕ` horizontal/vertical defect towers
`daughterIdemTower` and `mandelbrotTower`, and the single-sheet decoders `mog24SheetPlus` and
`mog24SheetMinus`) across `bondMap stageBond n m hnm : Stage n →+* Stage m` and into `Limit`. -/
theorem limit_stage_D31_golay_leech_mog_sheet_decoders_bridge
    {n m : ℕ} (hnm : n ≤ m)
    {P A C X : Stage n} (hP : P * P = P) (k r : ℕ) :
    let P_lim := ofStage n P
    let A_lim := ofStage n A
    let C_lim := ofStage n C
    let X_lim := ofStage n X
    let P_k := daughterIdemTower k P_lim A_lim
    let V_k := genV P_k A_lim C_lim
    let X_r := mandelbrotTower r (qgtPlus P_k A_lim C_lim)
    let Y_r := mandelbrotTower r (qgtMinus P_k A_lim C_lim)
    let V_kr := mandelbrotTower r V_k
    -- 1. Multi-step bonding & colimit compatibility:
    ofStage m (bondMap stageBond n m hnm (golay24G0 P A C X)) =
      ofStage n (golay24G0 P A C X) ∧
    ofStage m (bondMap stageBond n m hnm (mog24SheetPlus P A C X)) =
      ofStage n (mog24SheetPlus P A C X) ∧
    ofStage m (bondMap stageBond n m hnm (mog24SheetMinus P A C X)) =
      ofStage n (mog24SheetMinus P A C X) ∧
    -- 2. Scale-12 & Scale-24 Kantor–Peirce Frame Resolutions (`G₁`):
    golay12Core P_lim A_lim C_lim X_lim + golay12Root P_lim A_lim C_lim X_lim +
        golay12Ext P_lim A_lim C_lim X_lim =
      (12 : ℤ) • kantorTotal P_lim A_lim C_lim X_lim ∧
    golay24G0 P_lim A_lim C_lim X_lim + golay24Gp1 P_lim A_lim C_lim X_lim +
        golay24Gm1 P_lim A_lim C_lim X_lim + golay24Gp2 P_lim A_lim C_lim X_lim +
        golay24Gm2 P_lim A_lim C_lim X_lim =
      (24 : ℤ) • kantorTotal P_lim A_lim C_lim X_lim ∧
    -- 3. Scale-144 & Scale-576 Bilateral Compressions (`G₂`):
    golay12Core P_lim A_lim C_lim (golay12Core P_lim A_lim C_lim X_lim) +
        golay12Ext P_lim A_lim C_lim (golay12Ext P_lim A_lim C_lim X_lim) =
      (144 : ℤ) • (genV P_lim A_lim C_lim * X_lim * genV P_lim A_lim C_lim) ∧
    golay24G0 P_lim A_lim C_lim (golay24G0 P_lim A_lim C_lim X_lim) +
        golay24Gp2 P_lim A_lim C_lim (golay24Gm2 P_lim A_lim C_lim X_lim) +
        golay24Gm2 P_lim A_lim C_lim (golay24Gp2 P_lim A_lim C_lim X_lim) =
      (576 : ℤ) • (genV P_lim A_lim C_lim * X_lim * genV P_lim A_lim C_lim) ∧
    -- 4. All-Scale Single-Sheet Swap & Erasure Decoders (`G₅` & `G₆`):
    golay24G0 P_k A_lim C_lim X_r = (24 : ℤ) • (V_k * Y_r) ∧
    golay24G0 P_k A_lim C_lim Y_r = (24 : ℤ) • (V_k * X_r) ∧
    mog24SheetPlus P_k A_lim C_lim X_r = (24 : ℤ) • ((V_k * V_k * V_k) * V_kr) ∧
    mog24SheetPlus P_k A_lim C_lim Y_r = 0 ∧
    mog24SheetMinus P_k A_lim C_lim X_r = 0 ∧
    mog24SheetMinus P_k A_lim C_lim Y_r = (24 : ℤ) • ((V_k * V_k * V_k) * V_kr) := by
  dsimp only
  have hPLim : ofStage n P * ofStage n P = ofStage n P := by
    rw [← map_mul, hP]
  have hA61 :=
    archetype_A61_golay_12_and_leech_24_operator_error_correcting_codes
      hPLim (ofStage n A) (ofStage n C) (ofStage n X)
  have hA63 :=
    archetype_A63_golay_144_leech_576_quadratic_compression_and_eigen_algebra
      hPLim (ofStage n A) (ofStage n C) (ofStage n X)
  have hA68 :=
    archetype_A68_single_sheet_leech_swap_and_golay_12_24_projections
      hPLim (ofStage n A) (ofStage n C) k r
  have hA69 :=
    archetype_A69_all_scale_quantum_erasure_decoder_and_sheet_separation
      hPLim (ofStage n A) (ofStage n C) k r
  exact ⟨directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         directLimitOf_bondMap stageBond n m hnm _,
         hA61.1, hA61.2.2.2.2.1,
         hA63.2.2.2.2.2.2.2.2.2.1, hA63.2.2.2.2.2.2.2.2.2.2.2.1,
         hA68.2.2.2.2.1, hA68.2.2.2.2.2.1,
         hA69.2.2.2.2.1, hA69.2.2.2.2.2.1, hA69.2.2.2.2.2.2.1, hA69.2.2.2.2.2.2.2⟩

/-!
## 21. Stages `D₃₆`–`D₃₈`: Colimit Virasoro–Hopf & Zorn–Tetrad Trace Coercivity, Covariant Bianchi Constancy of Zorn–Drinfeld & Virasoro Modes, and `Cl(5, 5)` 3-Idempotent Gauge Flag Sector Charges
-/

/-- **Theorem 21.1 (`limit_stage_D36_virasoro_hopf_and_zorn_tetrad_trace_coercivity_bridge`):**
In the `Cl(1, 1)^{\otimes n}` inductive colimit `Limit`, for any linear trace extension
`tau : Limit →ₗ[ℝ] ℝ` of `normalizedTrace`, any self-adjoint idempotent `P : Limit`
(`P * P = P`, `star P = P`), any `A X : Limit`, and every mode index `r : ℕ`:
1. **Hopf Radius-Squared Trace Coercivity:**
   `0 ≤ tau (star X * hopfRadiusSq (heisenbergSourceMode r P A (star A)) (heisenbergSinkMode r P A (star A)) * X)`;
2. **Even Virasoro Mode Trace Coercivity & Exact Hopf Equality:**
   `tau (star X * virasoroModeEven (r + r) P A (star A) * X) =`
   `tau (star X * hopfRadiusSq (heisenbergSourceMode r P A (star A)) (heisenbergSinkMode r P A (star A)) * X)`
   and `0 ≤ tau (star X * virasoroModeEven (r + r) P A (star A) * X)`;
3. **Symmetric Zorn–Tetrad Metric Trace Coercivity:**
   `0 ≤ tau (star X * zornTetradSym P A (star A) A (star A) * X)`. -/
theorem limit_stage_D36_virasoro_hopf_and_zorn_tetrad_trace_coercivity_bridge
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ k (a : Stage k), tau (ofStage k a) = normalizedTrace k a)
    {P : Limit} (hP : P * P = P) (hPsym : star P = P)
    (A X : Limit) (r : ℕ) :
    0 ≤ tau (star X *
      hopfRadiusSq (heisenbergSourceMode r P A (star A))
        (heisenbergSinkMode r P A (star A)) * X) ∧
    tau (star X * virasoroModeEven (r + r) P A (star A) * X) =
      tau (star X *
        hopfRadiusSq (heisenbergSourceMode r P A (star A))
          (heisenbergSinkMode r P A (star A)) * X) ∧
    0 ≤ tau (star X * virasoroModeEven (r + r) P A (star A) * X) ∧
    0 ≤ tau (star X * zornTetradSym P A (star A) A (star A) * X) := by
  have hPos : ∀ Y : Limit, 0 ≤ tau (star Y * Y) :=
    trace_extension_positive tau htau
  rcases star_mul_hopfRadiusSq_and_zornTetradSym_eq_sum_squares hP hPsym A X r with
    ⟨hHopfSq, hVirSq, hZornSq⟩
  have hHopfNonneg :
      0 ≤ tau (star X *
        hopfRadiusSq (heisenbergSourceMode r P A (star A))
          (heisenbergSinkMode r P A (star A)) * X) := by
    rw [hHopfSq, map_add]
    exact add_nonneg (hPos (heisenbergSinkMode r P A (star A) * X))
      (hPos (heisenbergSourceMode r P A (star A) * X))
  have hVirEq :
      tau (star X * virasoroModeEven (r + r) P A (star A) * X) =
        tau (star X *
          hopfRadiusSq (heisenbergSourceMode r P A (star A))
            (heisenbergSinkMode r P A (star A)) * X) := by
    rw [hVirSq, hHopfSq]
  have hVirNonneg :
      0 ≤ tau (star X * virasoroModeEven (r + r) P A (star A) * X) := by
    rw [hVirEq]
    exact hHopfNonneg
  have hZornNonneg :
      0 ≤ tau (star X * zornTetradSym P A (star A) A (star A) * X) := by
    rw [hZornSq, map_add]
    exact add_nonneg (hPos (genPhi P A (star A) * X))
      (hPos (genPhi P A (star A) * X))
  exact ⟨hHopfNonneg, hVirEq, hVirNonneg, hZornNonneg⟩

/-- **Helper Theorem 21.2 (`peirceCovariantDeriv_zornDrinfeld_and_virasoroModeEven_eq_zero`):**
In any associative ring `[Ring B]` with idempotent `P` (`P * P = P`), any `A, C : B`, and any
mode indices `m, r : ℕ`, both `virasoroModeEven m P A C` and `zornNorm P (zornDrinfeldMatrix r r P A C)`
lie in the exact kernel of `peirceGradingDeriv P` and `peirceCovariantDeriv P A C`. -/
theorem peirceCovariantDeriv_zornDrinfeld_and_virasoroModeEven_eq_zero
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (m r : ℕ) :
    peirceGradingDeriv P (virasoroModeEven m P A C) = 0 ∧
    comm (genPhi P A C) (virasoroModeEven m P A C) = 0 ∧
    peirceCovariantDeriv P A C (virasoroModeEven m P A C) = 0 ∧
    peirceGradingDeriv P (zornNorm P (zornDrinfeldMatrix r r P A C)) = 0 ∧
    comm (genPhi P A C) (zornNorm P (zornDrinfeldMatrix r r P A C)) = 0 ∧
    peirceCovariantDeriv P A C (zornNorm P (zornDrinfeldMatrix r r P A C)) = 0 := by
  rcases zornDrinfeldMatrix_norm_and_virasoroModeEven_comm_idem_and_genPhi hP A C m r with
    ⟨_, _, hVP, hVPhi, hZP, hZPhi⟩
  have hGradV : peirceGradingDeriv P (virasoroModeEven m P A C) = 0 := hVP
  have hCovV : peirceCovariantDeriv P A C (virasoroModeEven m P A C) = 0 := by
    unfold peirceCovariantDeriv
    rw [hGradV, hVPhi, add_zero]
  have hGradZ : peirceGradingDeriv P (zornNorm P (zornDrinfeldMatrix r r P A C)) = 0 := hZP
  have hCovZ : peirceCovariantDeriv P A C (zornNorm P (zornDrinfeldMatrix r r P A C)) = 0 := by
    unfold peirceCovariantDeriv
    rw [hGradZ, hZPhi, add_zero]
  exact ⟨hGradV, hVPhi, hCovV, hGradZ, hZPhi, hCovZ⟩

/-- **Theorem 21.3 (`stage_D37_peirceCovariantDeriv_zornDrinfeld_virasoro_hopf_and_cross_carrier_yang_mills`):**
Unifies the Stage `D₃₇` covariant Bianchi constancy of the even Virasoro modes
`virasoroModeEven m P A C`, the Zorn–Drinfeld norm `zornNorm P (zornDrinfeldMatrix r r P A C)`,
and the self-adjoint Heisenberg–Hopf radius-squared operator
`hopfRadiusSq (heisenbergSourceMode r P A (star A)) (heisenbergSinkMode r P A (star A))` across:
1. Any `*`-ring `[Ring B] [StarRing B]` with self-adjoint idempotent `P` (`P * P = P`, `star P = P`);
2. The two-sheet Hestenes–Krein filtered colimit `Module.End ℝ (Carrier StageFunctor)`
   (`P_colim = twoSheetColimitEnd plusStage`);
3. `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)` (`A_conn = genPhi P_mat A_mat C_mat`). -/
theorem stage_D37_peirceCovariantDeriv_zornDrinfeld_virasoro_hopf_and_cross_carrier_yang_mills
    {B : Type*} [Ring B] [StarRing B]
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A C : B) (m r : ℕ)
    (A_colim C_colim :
      Module.End ℝ
        (InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.Carrier
          InfoGeometry.Categorical.TwoSheetKreinStageSystem.StageFunctor))
    {R : Type*} [CommRing R] {V_ext : Type*} [AddCommGroup V_ext] [Module R V_ext]
    {n : ℕ}
    {P_mat : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)}
    (hP_mat : P_mat * P_mat = P_mat)
    (A_mat C_mat : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)) :
    let P_colim :=
      InfoGeometry.Categorical.TwoSheetKreinStageSystem.twoSheetColimitEnd
        InfoGeometry.Categorical.TwoSheetKreinStageSystem.plusStage
    let A_conn := genPhi P_mat A_mat C_mat
    peirceCovariantDeriv P A C (virasoroModeEven m P A C) = 0 ∧
    peirceCovariantDeriv P A C (zornNorm P (zornDrinfeldMatrix r r P A C)) = 0 ∧
    peirceCovariantDeriv P A (star A)
      (hopfRadiusSq (heisenbergSourceMode r P A (star A))
        (heisenbergSinkMode r P A (star A))) = 0 ∧
    peirceCovariantDeriv P_colim A_colim C_colim
      (virasoroModeEven m P_colim A_colim C_colim) = 0 ∧
    peirceCovariantDeriv P_colim A_colim C_colim
      (zornNorm P_colim (zornDrinfeldMatrix r r P_colim A_colim C_colim)) = 0 ∧
    covariantDerivative A_conn 0 (virasoroModeEven m P_mat A_mat C_mat) = 0 ∧
    covariantDerivative A_conn 0
      (zornNorm P_mat (zornDrinfeldMatrix r r P_mat A_mat C_mat)) = 0 := by
  dsimp only
  rcases peirceCovariantDeriv_zornDrinfeld_and_virasoroModeEven_eq_zero hP A C m r with
    ⟨_, _, hCovV, _, _, hCovZ⟩
  rcases peirceCovariantDeriv_zornDrinfeld_and_virasoroModeEven_eq_zero
      hP A (star A) (r + r) r with
    ⟨_, _, hCovV_rr, _, _, _⟩
  have hHopfEq :=
    (all_mode_heisenberg_virasoro_hopf_coordinate_identity_and_furey_tower hP hPsym A r).2.2.2.2.1
  have hCovHopf :
      peirceCovariantDeriv P A (star A)
        (hopfRadiusSq (heisenbergSourceMode r P A (star A))
          (heisenbergSinkMode r P A (star A))) = 0 := by
    rw [hHopfEq]
    exact hCovV_rr
  rcases peirceCovariantDeriv_zornDrinfeld_and_virasoroModeEven_eq_zero
      InfoGeometry.Categorical.TwoSheetKreinStageSystem.twoSheetColimit_plus_idempotent
      A_colim C_colim m r with
    ⟨_, _, hCovV_colim, _, _, hCovZ_colim⟩
  rcases peirceCovariantDeriv_zornDrinfeld_and_virasoroModeEven_eq_zero
      hP_mat A_mat C_mat m r with
    ⟨_, hCommV_mat, _, _, hCommZ_mat, _⟩
  have hExtZero : ∀ M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext),
      matrixExteriorDerivative
        (0 : ExteriorAlgebra R V_ext →ₗ[R] ExteriorAlgebra R V_ext) M = 0 := by
    intro M
    ext i j
    simp [matrixExteriorDerivative]
  refine ⟨hCovV, hCovZ, hCovHopf, hCovV_colim, hCovZ_colim, ?_, ?_⟩
  · unfold covariantDerivative matrixCommutator
    rw [hExtZero, zero_add]
    exact hCommV_mat
  · unfold covariantDerivative matrixCommutator
    rw [hExtZero, zero_add]
    exact hCommZ_mat

open InfoGeometry.Algebra.Clifford55GaugeSubalgebra in
/-- **Theorem 21.4 (`stage_D38_three_idempotent_gauge_flag_sector_charges_and_cl55_traces`):**
Realizes the Stage `D₃₀` / `D₃₄` nested partial-flag filtration `P₁ ⊂ P₂ ⊂ P₃` and its
pre-breaking (`chargeY6`), post-breaking (`chargeQ6`), and quaternionic chiral involution
(`quatChiralInv`) operators on any 3-idempotent gauge partition `S : OrthogonalIdempotentSystem B`
(`P₁ := S.e1`, `P₂ := S.e1 + S.e2`, `P₃ := 1`, with strata `P_O2 = S.e1`, `P_H1 = S.e2`,
`P_H2 = S.e3`, `P_C = 0`), and evaluates their exact traces on the concrete $(6, 2, 2)$
hyperbolic realization `e1, e2, e3 : HMatrix` of $\operatorname{Cl}(5, 5)$:
1. **Cumulative Flag Filtration & Stratum Identification:**
   `flagStratumIdem S.e1 (S.e1 + S.e2) = S.e2` and `flagStratumIdem (S.e1 + S.e2) 1 = S.e3`;
2. **Pre-Breaking (`chargeY6`) vs. Post-Breaking (`chargeQ6`) Step-Corner Eigenvalues:**
   - `chargeQ6 S.e1 S.e3 0 - chargeY6 S.e1 S.e2 S.e3 0 = (3 : ℤ) • quatChiralInv S.e2 S.e3`,
   - `quatChiralInv S.e2 S.e3 * quatChiralInv S.e2 S.e3 = S.e2 + S.e3`,
   - `comm (chargeY6 S.e1 S.e2 S.e3 0) (flagStepCorner S.e2 S.e3 X) = 0`,
   - `comm (chargeQ6 S.e1 S.e3 0) (flagStepCorner S.e2 S.e3 X) = -(6 : ℤ) • flagStepCorner S.e2 S.e3 X`,
   - `comm (chargeY6 S.e1 S.e2 S.e3 0) (flagStepCorner S.e1 S.e2 X) = -flagStepCorner S.e1 S.e2 X`,
   - `comm (chargeQ6 S.e1 S.e3 0) (flagStepCorner S.e1 S.e2 X) = (2 : ℤ) • flagStepCorner S.e1 S.e2 X`;
3. **Concrete $\operatorname{Cl}(5, 5)$ $(6, 2, 2)$ Scale-24 Charge Traces & Chiral Tracelessness:**
   - `Matrix.trace (chargeY6 e1 e2 e3 0) = 24`,
   - `Matrix.trace (chargeQ6 e1 e3 0) = 24`,
   - `Matrix.trace (quatChiralInv e2 e3) = 0`. -/
theorem stage_D38_three_idempotent_gauge_flag_sector_charges_and_cl55_traces
    {B : Type*} [Ring B] (S : OrthogonalIdempotentSystem B) (X : B) :
    flagStratumIdem S.e1 (S.e1 + S.e2) = S.e2 ∧
    flagStratumIdem (S.e1 + S.e2) (1 : B) = S.e3 ∧
    chargeQ6 S.e1 S.e3 0 - chargeY6 S.e1 S.e2 S.e3 0 =
      (3 : ℤ) • quatChiralInv S.e2 S.e3 ∧
    quatChiralInv S.e2 S.e3 * quatChiralInv S.e2 S.e3 = S.e2 + S.e3 ∧
    comm (chargeY6 S.e1 S.e2 S.e3 0) (flagStepCorner S.e2 S.e3 X) = 0 ∧
    comm (chargeQ6 S.e1 S.e3 0) (flagStepCorner S.e2 S.e3 X) =
      -(6 : ℤ) • flagStepCorner S.e2 S.e3 X ∧
    comm (chargeY6 S.e1 S.e2 S.e3 0) (flagStepCorner S.e1 S.e2 X) =
      -flagStepCorner S.e1 S.e2 X ∧
    comm (chargeQ6 S.e1 S.e3 0) (flagStepCorner S.e1 S.e2 X) =
      (2 : ℤ) • flagStepCorner S.e1 S.e2 X ∧
    Matrix.trace (chargeY6 e1 e2 e3 0) = 24 ∧
    Matrix.trace (chargeQ6 e1 e3 0) = 24 ∧
    Matrix.trace (quatChiralInv e2 e3) = 0 := by
  have h1 : S.e1 * S.e1 = S.e1 := S.e1_idem
  have h2 : (S.e1 + S.e2) * (S.e1 + S.e2) = S.e1 + S.e2 := by
    calc
      (S.e1 + S.e2) * (S.e1 + S.e2) =
        S.e1 * S.e1 + S.e1 * S.e2 + S.e2 * S.e1 + S.e2 * S.e2 := by noncomm_ring
      _ = S.e1 + 0 + 0 + S.e2 := by
        rw [S.e1_idem, S.e1_e2_ortho, S.e2_e1_ortho, S.e2_idem]
      _ = S.e1 + S.e2 := by abel
  have h3 : (1 : B) * 1 = 1 := mul_one 1
  have h12 : S.e1 * (S.e1 + S.e2) = S.e1 := by
    rw [mul_add, S.e1_idem, S.e1_e2_ortho, add_zero]
  have h21 : (S.e1 + S.e2) * S.e1 = S.e1 := by
    rw [add_mul, S.e1_idem, S.e2_e1_ortho, add_zero]
  have h23 : (S.e1 + S.e2) * (1 : B) = S.e1 + S.e2 := mul_one _
  have h32 : (1 : B) * (S.e1 + S.e2) = S.e1 + S.e2 := one_mul _
  have h13 : S.e1 * (1 : B) = S.e1 := mul_one _
  have h31 : (1 : B) * S.e1 = S.e1 := one_mul _
  have hStrat12 : flagStratumIdem S.e1 (S.e1 + S.e2) = S.e2 := by
    unfold flagStratumIdem; abel
  have hStrat23 : flagStratumIdem (S.e1 + S.e2) (1 : B) = S.e3 := by
    unfold flagStratumIdem
    calc
      (1 : B) - (S.e1 + S.e2) = (S.e1 + S.e2 + S.e3) - (S.e1 + S.e2) := by
        rw [S.partition_unity]
      _ = S.e3 := by abel
  have hStratC : (1 : B) - 1 = 0 := sub_self 1
  rcases partial_flag_sector_quaternionic_symmetry_breaking_and_step_charges
      h1 h2 h3 h12 h21 h23 h32 h13 h31 X with
    ⟨_, hDiff, hSq, hY23, hQ23, hY12, hQ12⟩
  rw [hStrat12, hStrat23] at hSq
  rw [hStrat12, hStrat23, hStratC] at hDiff hY23 hQ23 hY12 hQ12
  have hTrY6 : Matrix.trace (chargeY6 e1 e2 e3 0) = 24 := by
    have hY6Add : chargeY6 e1 e2 e3 0 = e1 + e1 + (e2 + e3 + (e2 + e3) + (e2 + e3)) := by
      unfold chargeY6; abel
    rw [hY6Add]
    simp only [Matrix.trace_add, e1_trace, e2_trace, e3_trace]
    norm_num
  have hTrQ6 : Matrix.trace (chargeQ6 e1 e3 0) = 24 := by
    have hQ6Add : chargeQ6 e1 e3 0 = e1 + e1 + (e3 + e3 + e3 + e3 + e3 + e3) := by
      unfold chargeQ6; abel
    rw [hQ6Add]
    simp only [Matrix.trace_add, e1_trace, e3_trace]
    norm_num
  have hTrInv : Matrix.trace (quatChiralInv e2 e3) = 0 := by
    unfold quatChiralInv
    rw [Matrix.trace_sub, e3_trace, e2_trace, sub_self]
  exact ⟨hStrat12, hStrat23, hDiff, hSq, hY23, hQ23, hY12, hQ12, hTrY6, hTrQ6, hTrInv⟩

/-!
## 22. Stages `D₃₉`–`D₄₁`: Colimit Non-Associative Zorn Wedge Product & Square Alternativity, All-Mode Virasoro–Golay–Leech–MOG Ladder, and Connes–Higgs–Goldstone Unitary-Gauge Triad
-/

open CanonicalTwoSheetedInductiveColimit in
/-- **Theorem 22.1 (`limit_stages_D39_D40_D41_zorn_wedge_virasoro_golay_and_connes_higgs_bridge`):**
In the `Cl(1, 1)^{\otimes n}` inductive colimit `Limit`, for any stage transition `n ≤ m`,
any idempotent `P : Stage n` (`P * P = P`, `star P = P`), any `M a b x y c d z w A : Stage n`,
any mode index `r : ℕ`, and any integers `α, β : ℤ`
(with `P_lim := ofStage n P`, `A_lim := ofStage n A`, etc.):
1. **Colimit Transport, Square Alternativity, & Conjugate Norm of `zornNonAssocMul` (`Stage D₃₉`):**
   - `ofStage m (bondMap stageBond n m hnm (zornNonAssocMul P M a b x y c d z w)) =`
     `ofStage n (zornNonAssocMul P M a b x y c d z w)`,
   - `zornNonAssocMul P_lim M_lim a_lim b_lim x_lim y_lim a_lim b_lim x_lim y_lim = Z_lim * Z_lim`,
   - `zornNonAssocMul P_lim M_lim a_lim b_lim x_lim y_lim a_lim b_lim (-x_lim) (-y_lim) =`
     `zornNorm P_lim Z_lim`;
2. **Colimit All-Mode Scale-12 / Scale-24 Virasoro–Golay–Leech–MOG Ladder (`Stage D₄₀`):**
   - `golay12Core P_lim A_lim (star A_lim) (virasoroModeEven r P_lim A_lim (star A_lim)) =`
     `(12 : ℤ) • virasoroModeEven (r + 1) P_lim A_lim (star A_lim)`,
   - `golay24G0 P_lim A_lim (star A_lim) (virasoroModeEven r P_lim A_lim (star A_lim)) =`
     `(24 : ℤ) • virasoroModeEven (r + 1) P_lim A_lim (star A_lim)`,
   - `mog24V P_lim A_lim (star A_lim) (virasoroModeEven r P_lim A_lim (star A_lim)) =`
     `(24 : ℤ) • virasoroModeEven (r + 2) P_lim A_lim (star A_lim)`,
   - `golay24G0 P_lim A_lim (star A_lim) (hopfRadiusSq (heisenbergSourceMode r P_lim A_lim (star A_lim)) (heisenbergSinkMode r P_lim A_lim (star A_lim))) =`
     `(24 : ℤ) • virasoroModeEven (r + r + 1) P_lim A_lim (star A_lim)`;
3. **Colimit Connes–Higgs–Goldstone Unitary-Gauge Triad (`Stage D₄₁`):**
   - `opHiggsMassOperator P_lim A_lim (star A_lim) (opHiggsField P_lim A_lim (star A_lim)) = 0`,
   - `opHiggsMassOperator P_lim A_lim (star A_lim) (opHiggsVEVSq P_lim A_lim (star A_lim)) = 0`,
   - `opHiggsMassOperator P_lim A_lim (star A_lim) (opAxial P_lim A_lim (star A_lim)) =`
     `-((4 : ℤ) • (opHiggsVEVSq P_lim A_lim (star A_lim) * opAxial P_lim A_lim (star A_lim)))`,
   - `opHiggsMassOperator P_lim A_lim (star A_lim) (α • opHiggsField P_lim A_lim (star A_lim) + β • opAxial P_lim A_lim (star A_lim)) =`
     `β • (-((4 : ℤ) • (opHiggsVEVSq P_lim A_lim (star A_lim) * opAxial P_lim A_lim (star A_lim))))`. -/
theorem limit_stages_D39_D40_D41_zorn_wedge_virasoro_golay_and_connes_higgs_bridge
    {n m : ℕ} (hnm : n ≤ m)
    {P : Stage n} (hP : P * P = P) (hPsym : star P = P)
    (M a b x y c d z w A : Stage n) (r : ℕ) (α β : ℤ) :
    let P_lim : Limit := ofStage n P
    let M_lim : Limit := ofStage n M
    let a_lim : Limit := ofStage n a
    let b_lim : Limit := ofStage n b
    let x_lim : Limit := ofStage n x
    let y_lim : Limit := ofStage n y
    let A_lim : Limit := ofStage n A
    let Z_lim : Limit := zornMatrix P_lim a_lim b_lim x_lim y_lim
    -- 1. Stage D₃₉ Non-Associative Zorn Wedge Product & Square Alternativity in `Limit`:
    ofStage m (bondMap stageBond n m hnm (zornNonAssocMul P M a b x y c d z w)) =
      ofStage n (zornNonAssocMul P M a b x y c d z w) ∧
    zornNonAssocMul P_lim M_lim a_lim b_lim x_lim y_lim a_lim b_lim x_lim y_lim =
      Z_lim * Z_lim ∧
    zornNonAssocMul P_lim M_lim a_lim b_lim x_lim y_lim a_lim b_lim (-x_lim) (-y_lim) =
      zornNorm P_lim Z_lim ∧
    -- 2. Stage D₄₀ All-Mode Scale-12 / Scale-24 Virasoro–Golay–Leech–MOG Ladder in `Limit`:
    golay12Core P_lim A_lim (star A_lim) (virasoroModeEven r P_lim A_lim (star A_lim)) =
      (12 : ℤ) • virasoroModeEven (r + 1) P_lim A_lim (star A_lim) ∧
    golay24G0 P_lim A_lim (star A_lim) (virasoroModeEven r P_lim A_lim (star A_lim)) =
      (24 : ℤ) • virasoroModeEven (r + 1) P_lim A_lim (star A_lim) ∧
    mog24V P_lim A_lim (star A_lim) (virasoroModeEven r P_lim A_lim (star A_lim)) =
      (24 : ℤ) • virasoroModeEven (r + 2) P_lim A_lim (star A_lim) ∧
    golay24G0 P_lim A_lim (star A_lim)
        (hopfRadiusSq (heisenbergSourceMode r P_lim A_lim (star A_lim))
          (heisenbergSinkMode r P_lim A_lim (star A_lim))) =
      (24 : ℤ) • virasoroModeEven (r + r + 1) P_lim A_lim (star A_lim) ∧
    -- 3. Stage D₄₁ Connes–Higgs–Goldstone Unitary-Gauge Triad in `Limit`:
    opHiggsMassOperator P_lim A_lim (star A_lim) (opHiggsField P_lim A_lim (star A_lim)) = 0 ∧
    opHiggsMassOperator P_lim A_lim (star A_lim) (opHiggsVEVSq P_lim A_lim (star A_lim)) = 0 ∧
    opHiggsMassOperator P_lim A_lim (star A_lim) (opAxial P_lim A_lim (star A_lim)) =
      -((4 : ℤ) • (opHiggsVEVSq P_lim A_lim (star A_lim) *
        opAxial P_lim A_lim (star A_lim))) ∧
    opHiggsMassOperator P_lim A_lim (star A_lim)
        (α • opHiggsField P_lim A_lim (star A_lim) + β • opAxial P_lim A_lim (star A_lim)) =
      β • (-((4 : ℤ) • (opHiggsVEVSq P_lim A_lim (star A_lim) *
        opAxial P_lim A_lim (star A_lim)))) := by
  dsimp only
  have hPLim : ofStage n P * ofStage n P = ofStage n P := by
    rw [← map_mul, hP]
  have hPsymLim : star (ofStage n P) = ofStage n P := by
    rw [← ofStage_star, hPsym]
  have hD39 :=
    stage_D39_zorn_nonassociative_wedge_product_and_norm_invariance
      hPLim (ofStage n M) (ofStage n a) (ofStage n b) (ofStage n x) (ofStage n y)
      (ofStage n c) (ofStage n d) (ofStage n z) (ofStage n w)
  have hD40_r :=
    stage_D40_all_mode_virasoro_golay_leech_mog_ladder
      hPLim (ofStage n A) (star (ofStage n A)) r
  have hD40_rr :=
    stage_D40_all_mode_virasoro_golay_leech_mog_ladder
      hPLim (ofStage n A) (star (ofStage n A)) (r + r)
  have hHopfEq :=
    (all_mode_heisenberg_virasoro_hopf_coordinate_identity_and_furey_tower
      hPLim hPsymLim (ofStage n A) r).2.2.2.2.1
  have hGolayHopf :
      golay24G0 (ofStage n P) (ofStage n A) (star (ofStage n A))
          (hopfRadiusSq
            (heisenbergSourceMode r (ofStage n P) (ofStage n A) (star (ofStage n A)))
            (heisenbergSinkMode r (ofStage n P) (ofStage n A) (star (ofStage n A)))) =
        (24 : ℤ) • virasoroModeEven (r + r + 1) (ofStage n P) (ofStage n A) (star (ofStage n A)) := by
    rw [hHopfEq]
    exact hD40_rr.2.2.2.1
  rcases universal_higgs_goldstone_spin_triad hPLim (ofStage n A) (star (ofStage n A)) with
    ⟨_, _, _, _, _, _, _, _, _, hMPhi, hMV, hMJ, _⟩
  have hErl :=
    erlangen_unitary_gauge_higgs_projection hPLim (ofStage n A) (star (ofStage n A)) α β
  exact ⟨directLimitOf_bondMap stageBond n m hnm _,
         hD39.2.2.2.2.2.1, hD39.2.2.2.2.2.2.1,
         hD40_r.1, hD40_r.2.2.2.1, hD40_r.2.2.2.2.2.2.2.2.1, hGolayHopf,
         hMPhi, hMV, hMJ, hErl⟩

end NonCommutativeDressingFieldCocycleAndBRSTPoset

end InfoGeometry.Canonical.PeircePolygonKreinBottMasterSynthesis
