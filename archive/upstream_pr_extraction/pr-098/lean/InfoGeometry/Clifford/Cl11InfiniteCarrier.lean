import Mathlib.Tactic.NoncommRing
import InfoGeometry.Clifford.Cl11TensorTowerIteration
import InfoGeometry.Clifford.Cl11MarkovJonesEngine

set_option autoImplicit false

/-!
# InfoGeometry.Clifford.Cl11InfiniteCarrier

Application of the finite induction principle to the `Cl(1,1)` tensor tower and
identification of the compatible algebraic carrier for the infinite transition.

The compatible carrier is the repository-owned algebraic direct limit

`Cl11TensorTowerLimit.Limit`.

The compatibility map is the canonical cone

`Cl11TensorTowerLimit.ofStage n : Stage n →+* Limit`,

and finite induction is the iterated bonding map

`Cl11TensorTowerIteration.iteratedStageEmbed m k : Stage m →+* Stage (m+k)`.

This file proves that finite-stage commutator/derivation identities and Markov
trace readouts transport through every finite induction step and are represented
by the same element in the algebraic direct-limit carrier.

No bare topological completion, infinite matrix, Type II₁/Type III factor, or
new Virasoro theorem is asserted here.  The Hestenes--Krein phase-analytic
completion and the tripartite flow lane are composed in
`Cl11HestenesKreinTripartiteCompletion`.  Existing Super-Virasoro limit theorems
live in the canonical Super-Virasoro modules and can be composed with this
carrier separately.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11InfiniteCarrier

open InfoGeometry.Clifford.Cl11TensorTowerIteration

/-- Finite matrix stage of the `Cl(1,1)` tensor tower. -/
abbrev Stage (n : ℕ) : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n

/-- Compatible algebraic carrier for the finite-to-infinite transition. -/
abbrev CompatibleCarrier : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

/-- Canonical compatible cone from finite stages into the algebraic carrier. -/
def intoCarrier (n : ℕ) : Stage n →+* CompatibleCarrier :=
  InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n

/-- Finite induction/advance by `k` tensor steps. -/
def finiteAdvance (m k : ℕ) : Stage m →+* Stage (m + k) :=
  iteratedStageEmbed m k

/-- The canonical carrier is compatible with every finite induction step. -/
theorem intoCarrier_finiteAdvance
    (m k : ℕ) (A : Stage m) :
    intoCarrier (m + k) (finiteAdvance m k A) = intoCarrier m A := by
  exact ofStage_iteratedStageEmbed m k A

/-- Ring commutator used for finite and carrier-level derivations. -/
def ringCommutator {A : Type*} [Ring A] (K X : A) : A :=
  K * X - X * K

/-- Inner commutators are derivations in any ring. -/
theorem ringCommutator_isDerivation
    {A : Type*} [Ring A] (K X Y : A) :
    ringCommutator K (X * Y) = ringCommutator K X * Y + X * ringCommutator K Y := by
  unfold ringCommutator
  noncomm_ring

/-- Inner commutators are additive in the generator in any ring. -/
theorem ringCommutator_add_left
    {A : Type*} [Ring A] (K₁ K₂ X : A) :
    ringCommutator (K₁ + K₂) X = ringCommutator K₁ X + ringCommutator K₂ X := by
  unfold ringCommutator
  noncomm_ring

/-- Difference of generators gives difference of inner commutators in any ring. -/
theorem ringCommutator_sub_left
    {A : Type*} [Ring A] (K₁ K₂ X : A) :
    ringCommutator (K₁ - K₂) X = ringCommutator K₁ X - ringCommutator K₂ X := by
  unfold ringCommutator
  noncomm_ring

/-- Finite induction transports the inner commutator. -/
theorem finiteAdvance_ringCommutator
    (m k : ℕ) (K X : Stage m) :
    finiteAdvance m k (ringCommutator K X) =
      ringCommutator (finiteAdvance m k K) (finiteAdvance m k X) := by
  unfold ringCommutator finiteAdvance
  simp [map_sub, map_mul]

/-- The direct-limit carrier reads a finite commutator and any finite advance identically. -/
theorem intoCarrier_finiteAdvance_ringCommutator
    (m k : ℕ) (K X : Stage m) :
    intoCarrier (m + k)
        (ringCommutator (finiteAdvance m k K) (finiteAdvance m k X)) =
      intoCarrier m (ringCommutator K X) := by
  rw [← finiteAdvance_ringCommutator]
  exact intoCarrier_finiteAdvance m k (ringCommutator K X)

/-- The inner-commutator derivation identity holds in the algebraic carrier. -/
theorem carrier_ringCommutator_isDerivation
    (K X Y : CompatibleCarrier) :
    ringCommutator K (X * Y) = ringCommutator K X * Y + X * ringCommutator K Y :=
  ringCommutator_isDerivation K X Y

/-!
The chiral `plus/minus` generator difference is itself an inner derivation.  This is
proved directly on the algebraic colimit carrier; it does not introduce an
analytic completion or identify the generators with an unrelated finite model.
-/
theorem carrier_difference_ringCommutator_isDerivation
    (Kplus Kminus X Y : CompatibleCarrier) :
    ringCommutator (Kplus - Kminus) (X * Y) =
      ringCommutator (Kplus - Kminus) X * Y +
        X * ringCommutator (Kplus - Kminus) Y := by
  unfold ringCommutator
  noncomm_ring

/-- Difference of finite generators survives as difference of carrier commutators. -/
theorem carrier_ringCommutator_sub_left
    (K₁ K₂ X : CompatibleCarrier) :
    ringCommutator (K₁ - K₂) X = ringCommutator K₁ X - ringCommutator K₂ X :=
  ringCommutator_sub_left K₁ K₂ X

/-- Finite induction preserves the derivation identity at every advanced stage. -/
theorem finiteAdvance_ringCommutator_derivation
    (m k : ℕ) (K X Y : Stage m) :
    ringCommutator (finiteAdvance m k K)
        (finiteAdvance m k (X * Y)) =
      ringCommutator (finiteAdvance m k K) (finiteAdvance m k X) * finiteAdvance m k Y +
        finiteAdvance m k X * ringCommutator (finiteAdvance m k K) (finiteAdvance m k Y) := by
  rw [map_mul]
  exact ringCommutator_isDerivation (finiteAdvance m k K) (finiteAdvance m k X)
    (finiteAdvance m k Y)

/-!
The same Leibniz law is preserved when the finite-stage generator is a
plus/minus difference.  This is the stagewise statement needed before passing
to the compatible colimit cone.
-/
theorem finiteAdvance_difference_ringCommutator_derivation
    (m k : ℕ) (Kplus Kminus X Y : Stage m) :
    ringCommutator (finiteAdvance m k (Kplus - Kminus))
        (finiteAdvance m k (X * Y)) =
      ringCommutator (finiteAdvance m k (Kplus - Kminus))
          (finiteAdvance m k X) * finiteAdvance m k Y +
        finiteAdvance m k X *
          ringCommutator (finiteAdvance m k (Kplus - Kminus))
            (finiteAdvance m k Y) := by
  simp only [finiteAdvance, map_sub, map_mul]
  unfold ringCommutator
  noncomm_ring

/-- The Markov trace readout is stable along every finite stage embedding chain. -/
theorem compatibleMarkovTrace_stable
    (m n : ℕ) (h : m ≤ n) (A : Stage m) :
    InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace n
        (InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11InductiveAlgebraNet.embedMap m n h A) =
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace m A :=
  InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11_normalizedTrace_stable_embedMap m n h A

/-- Raw determinants square under one-step induction; normalized log-det is the compatible readout. -/
theorem compatibleLogDet_one_step
    (n : ℕ) (A : Stage n) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (n + 1)
        (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed n A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet n A :=
  InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11_normalizedLogAbsDet_one_step n A

/-- First-stage real Hestenes phase representative in the tensor tower. -/
def phaseAxisStage : Stage 1 :=
  InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseHead 0

/-- The first-stage real Hestenes phase representative squares to `-1`. -/
theorem phaseAxisStage_sq :
    phaseAxisStage * phaseAxisStage = -(1 : Stage 1) := by
  change InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseHead 0 *
      InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseHead 0 = -(1 : Stage 1)
  dsimp [InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseHead,
    InfoGeometry.Clifford.TowerMatrix.kronPow]
  rw [← Matrix.mul_kronecker_mul]
  rw [InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase_sq]
  ext i j
  cases i with
  | mk i0 i1 =>
      cases j with
      | mk j0 j1 =>
          have h0 : i0 = j0 := Subsingleton.elim _ _
          subst h0
          fin_cases i1 <;> fin_cases j1 <;> simp

/-- The global real bivector phase element in the algebraic direct-limit carrier. -/
def globalPhaseAxis : CompatibleCarrier :=
  intoCarrier 1 phaseAxisStage

/-- The global real bivector phase element squares to `-1` in the carrier. -/
theorem globalPhaseAxis_sq :
    globalPhaseAxis * globalPhaseAxis = -(1 : CompatibleCarrier) := by
  rw [globalPhaseAxis]
  calc
    intoCarrier 1 phaseAxisStage * intoCarrier 1 phaseAxisStage
        = intoCarrier 1 (phaseAxisStage * phaseAxisStage) := by
              rw [map_mul]
    _ = intoCarrier 1 (-(1 : Stage 1)) := by
          rw [phaseAxisStage_sq]
    _ = -(1 : CompatibleCarrier) := by
          simp [intoCarrier]

/-- The phase axis remains square-minus-one after any finite induction step. -/
theorem phaseAxis_finiteAdvance_sq (k : ℕ) :
    finiteAdvance 1 k phaseAxisStage * finiteAdvance 1 k phaseAxisStage =
      -(1 : Stage (1 + k)) := by
  calc
    finiteAdvance 1 k phaseAxisStage * finiteAdvance 1 k phaseAxisStage
        = finiteAdvance 1 k (phaseAxisStage * phaseAxisStage) := by
            symm
            exact map_mul (finiteAdvance 1 k) phaseAxisStage phaseAxisStage
    _ = finiteAdvance 1 k (-(1 : Stage 1)) := by
          rw [phaseAxisStage_sq]
    _ = -(1 : Stage (1 + k)) := by
          simp [finiteAdvance]

/-- The phase axis has stage-independent image in the compatible carrier. -/
theorem phaseAxis_limit_image (k : ℕ) :
    intoCarrier (1 + k) (finiteAdvance 1 k phaseAxisStage) = globalPhaseAxis := by
  rw [globalPhaseAxis]
  exact intoCarrier_finiteAdvance 1 k phaseAxisStage

/-! The finite scalar/phase plane and its direct-limit readout. -/

/-- The `a + K b` phase plane at the finite stage reached after `k` embeddings. -/
def phasePlaneStage (k : ℕ) (a b : ℝ) : Stage (1 + k) :=
  a • (1 : Stage (1 + k)) + b • finiteAdvance 1 k phaseAxisStage

theorem phasePlaneStage_mul (k : ℕ) (a b c d : ℝ) :
    phasePlaneStage k a b * phasePlaneStage k c d =
      phasePlaneStage k (a * c - b * d) (a * d + b * c) := by
  simp only [phasePlaneStage, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_smul, smul_neg, neg_smul,
    one_smul, one_mul, mul_one]
  rw [phaseAxis_finiteAdvance_sq]
  module

theorem phasePlaneStage_conj_mul (k : ℕ) (a b : ℝ) :
    phasePlaneStage k a b * phasePlaneStage k a (-b) =
      (a ^ 2 + b ^ 2) • (1 : Stage (1 + k)) := by
  rw [phasePlaneStage_mul]
  simp only [phasePlaneStage, mul_neg, neg_mul, neg_neg]
  rw [show -(a * b) + b * a = 0 by ring, zero_smul, add_zero]
  congr 1
  ring

theorem phasePlane_intoCarrier (k : ℕ) (a b : ℝ) :
    intoCarrier (1 + k) (phasePlaneStage k a b) =
      a • (1 : CompatibleCarrier) + b • globalPhaseAxis := by
  simp only [phasePlaneStage, Algebra.smul_def, map_add, map_mul, map_one]
  have ha :
      intoCarrier (1 + k) (algebraMap ℝ (Stage (1 + k)) a) =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.realAlgebraMap a := by
    simpa [intoCarrier] using
      (InfoGeometry.Clifford.Cl11TensorTowerLimit.realAlgebraMap_stage
        (1 + k) a).symm
  have hb :
      intoCarrier (1 + k) (algebraMap ℝ (Stage (1 + k)) b) =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.realAlgebraMap b := by
    simpa [intoCarrier] using
      (InfoGeometry.Clifford.Cl11TensorTowerLimit.realAlgebraMap_stage
        (1 + k) b).symm
  rw [ha, hb, phaseAxis_limit_image]
  rfl

theorem phasePlane_intoCarrier_conj_mul (k : ℕ) (a b : ℝ) :
    intoCarrier (1 + k) (phasePlaneStage k a b) *
      intoCarrier (1 + k) (phasePlaneStage k a (-b)) =
      (a ^ 2 + b ^ 2) • (1 : CompatibleCarrier) := by
  calc
    intoCarrier (1 + k) (phasePlaneStage k a b) *
          intoCarrier (1 + k) (phasePlaneStage k a (-b)) =
        intoCarrier (1 + k)
          (phasePlaneStage k a b * phasePlaneStage k a (-b)) := by
            symm
            exact map_mul (intoCarrier (1 + k)) _ _
    _ = intoCarrier (1 + k)
          ((a ^ 2 + b ^ 2) • (1 : Stage (1 + k))) := by
            rw [phasePlaneStage_conj_mul]
    _ = (a ^ 2 + b ^ 2) • (1 : CompatibleCarrier) := by
            simpa only [Algebra.smul_def, mul_one, intoCarrier] using
              (InfoGeometry.Clifford.Cl11TensorTowerLimit.realAlgebraMap_stage
                (1 + k) (a ^ 2 + b ^ 2)).symm

/-!
Summary:

* finite induction carrier: `finiteAdvance m k`;
* compatible infinite carrier: `CompatibleCarrier = Cl11TensorTowerLimit.Limit`;
* compatible cone: `intoCarrier n = Cl11TensorTowerLimit.ofStage n`;
* carrier compatibility: `intoCarrier_finiteAdvance`;
* finite commutator induction: `finiteAdvance_ringCommutator`;
* carrier derivation: `carrier_ringCommutator_isDerivation`;
* compatible readout: `compatibleMarkovTrace_stable` and `compatibleLogDet_one_step`.
-/

end InfoGeometry.Clifford.Cl11InfiniteCarrier
