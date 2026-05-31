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
