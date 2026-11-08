/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ChiralCondensateGMORBanksCasherNJLPoset

/-!
# Maurer–Cartan Spectral Annihilator `𝓚_{γ₅}`, Linear Death of Odd Forms, and the Multiplicative Defect Theorem (`𝔎₁ ≺ 𝔎₂ ≺ 𝔎₃ ≺ 𝔎₄ ≺ 𝔎₅ ≺ 𝔎₆ ≺ 𝔎₇`)

This module formalizes the 7-stage Acyclic Causal Poset
`MaurerCartanAnnihilatorStage` (`𝔎₁ ≺ 𝔎₂ ≺ 𝔎₃ ≺ 𝔎₄ ≺ 𝔎₅ ≺ 𝔎₆ ≺ 𝔎₇`)
distilled via `solve et coagula` over an arbitrary associative ring `[Ring B]` with
idempotent `P * P = P` and chiral involution `γ₅ = chiralGamma5 P = 2P - 1`:

1. **Stage `𝔎₁` (`K1_TripotentChiralDerivation` — Tripotency of the Chiral Derivation `ad_P³ = ad_P` & `ad_{γ₅}³ = 4 ad_{γ₅}`)**:
   - Proves that the inner Peirce derivation `ad_P(X) = [P, X] = peirceGradingDeriv P X` is
     tripotent (`ad_P³(X) = ad_P(X)`), while the chiral involution derivation `ad_{γ₅}(X) = [γ₅, X]`
     satisfies `ad_{γ₅}(X) = 2 • ad_P(X)`, `ad_{γ₅}²(X) = 4 • ad_P²(X)`, and
     `ad_{γ₅}³(X) = 4 • ad_{γ₅}(X)`.

2. **Stage `𝔎₂` (`K2_IdempotentAnnihilatorFilter` — The Idempotent Annihilator Filter `𝓚_{γ₅} = I - ad_P² = evenGrade P` & `𝒫_odd = ad_P² = oddGrade P`)**:
   - Defines `oddProjector P X := peirceAdSq P X = [P, [P, X]]` and
     `chiralAnnihilator P X := X - peirceAdSq P X`.
   - Proves that `chiralAnnihilator P X = evenGrade P X = P X P + (1 - P) X (1 - P)` and
     `oddProjector P X = oddGrade P X = P X (1 - P) + (1 - P) X P`, together with the
     characteristic-free identities:
     - `2 • chiralAnnihilator P X = X + γ₅ * X * γ₅`,
     - `2 • oddProjector P X = X - γ₅ * X * γ₅`,
     - `4 • chiralAnnihilator P X = 4 • X - [γ₅, [γ₅, X]]`,
     and complementary idempotency (`𝓚_{γ₅}² = 𝓚_{γ₅}`, `𝒫_odd² = 𝒫_odd`, `𝓚_{γ₅} ∘ 𝒫_odd = 0`).

3. **Stage `𝔎₃` (`K3_LinearAnnihilationOfOddMaurerCartanForms` — Universal Annihilation of Odd Maurer–Cartan Forms & Composite `𝔨 · 𝔭` / `𝔭 · 𝔨` Modules)**:
   - Proves that `chiralAnnihilator P` identically kills the primary odd Maurer–Cartan 1-forms
     `J = genJ P A C` and `Φ = genPhi P A C`, as well as every composite product, commutator,
     and anticommutator between an even operator `evenGrade P X ∈ 𝔨` and an odd form
     `oddGrade P Y ∈ 𝔭`:
     `𝓚_{γ₅}(evenGrade P X * oddGrade P Y) = 0`,
     `𝓚_{γ₅}(oddGrade P Y * evenGrade P X) = 0`,
     `𝓚_{γ₅}([evenGrade P X, oddGrade P Y]) = 0`, and
     `𝓚_{γ₅}({evenGrade P X, oddGrade P Y}) = 0`.

4. **Stage `𝔎₄` (`K4_MultiplicativeDefectCurvatureTheorem` — The Multiplicative Defect Theorem: Curvature as the Obstruction to Ring Homomorphism)**:
   - Proves the universal **Multiplicative Defect Theorem**: for any `X, Y : B`,
     $$\mathcal{K}_{\gamma_5}(X * Y) - \mathcal{K}_{\gamma_5}(X) * \mathcal{K}_{\gamma_5}(Y) = \mathcal{P}_{\mathrm{odd}}(X) * \mathcal{P}_{\mathrm{odd}}(Y).$$
   - Proves that evaluating this multiplicative defect on the killed odd Maurer–Cartan generators
     (`conePlus`, `coneMinus`, `genPhi`, `genJ`) recovers the entire **Quantum Geometric Tensor**:
     - `𝓚_{γ₅}(Φ²) - 𝓚_{γ₅}(Φ)² = V`,
     - `𝓚_{γ₅}(-J²) - 𝓚_{γ₅}(-J) 𝓚_{γ₅}(J) = V`,
     - `𝓚_{γ₅}(J * Φ) - 𝓚_{γ₅}(J) 𝓚_{γ₅}(Φ) = Σ`,
     - `𝓚_{γ₅}(N_+ * N_-) - 𝓚_{γ₅}(N_+) 𝓚_{γ₅}(N_-) = qgtPlus P A C`,
     - `𝓚_{γ₅}(N_- * N_+) - 𝓚_{γ₅}(N_-) 𝓚_{γ₅}(N_+) = qgtMinus P A C`.

5. **Stage `𝔎₅` (`K5_MaurerCartanOrbitGramianAndBianchiCentrality` — Filtering the Peirce Maurer–Cartan Curvature `𝓚_{γ₅}(J + V) = V` & Bianchi Centrality `[J, V] = [Φ, V] = 0`)**:
   - Proves that `chiralAnnihilator P (peirceMaurerCartanCurvature P A C) = genV P A C`
     (and `= orbitMassMode P a` when `P⋆ = P = P²`, `a⋆ = a`), while `oddProjector P` extracts `J`,
     and proves exact centrality `[J, V] = 0` and `[Φ, V] = 0` explaining `D_{P,A,C}(V) = 0`.

6. **Stage `𝔎₆` (`K6_ElieCartanTorsionAnnihilationAndMacDowellMansouri` — Killing Élie Cartan Torsion & Isolating Riemann–Cartan / MacDowell–Mansouri Curvature)**:
   - For two Cartan connections `𝒜₁ = Ω₁ + Φ₁` and `𝒜₂ = Ω₂ + Φ₂` (`Ω_i = evenGrade P X_i`,
     `Φ_i = oddGrade P Y_i`), proves that `[𝒜₁, 𝒜₂] = ℛ₁₂ + 𝒯₁₂`, that `chiralAnnihilator P`
     identically kills the Élie Cartan torsion `𝒯₁₂` (`𝓚_{γ₅}(𝒯₁₂) = 0`) and isolates the
     Riemann–Cartan curvature `ℛ₁₂ = [Ω₁, Ω₂] + [Φ₁, Φ₂]`, and that the Lie-bracket homomorphism
     defect of `𝓚_{γ₅}` is the quadratic MacDowell–Mansouri solder-form commutator `[Φ₁, Φ₂]`:
     `𝓚_{γ₅}([𝒜₁, 𝒜₂]) - [𝓚_{γ₅}(𝒜₁), 𝓚_{γ₅}(𝒜₂)] = [Φ₁, Φ₂]`.

7. **Stage `𝔎₇` (`K7_BanksCasherResolventDriftAnnihilationAndMasterSynthesis` — Killing the Odd Resolvent Drift `-J(V + η²)⁻¹` & Master Synthesis)**:
   - Proves that `chiralAnnihilator P` kills the odd Dirac resolvent drift
     `peirceDiracResolventOdd P A C R_η = -J * R_η` and isolates the pure Banks–Casher Lorentzian
     condensate kernel `peirceDiracResolventEven η R_η = η * R_η`:
     `𝓚_{γ₅}((J + η)⁻¹) = η * (V + η²)⁻¹`,
     so any cyclic trace `τ` satisfies `τ((J + η)⁻¹) = τ(𝓚_{γ₅}((J + η)⁻¹)) = τ(η * (V + η²)⁻¹)`.

### Three-Bucket Audit Map

#### BUCKET 1 — Unconditional Kernel Truth
- `MaurerCartanAnnihilatorStage`, `rank_injective`, `causalEdge_strict_rank`,
  `transGen_strict_rank`, `causalEdge_acyclic`, `causalEdge_chain`.

#### BUCKET 2 — Conditional Kernel Theorems with Explicit Hypotheses
- Stages `𝔎₁`–`𝔎₇` (`archetype_K1_tripotent_chiral_derivation` through
  `maurer_cartan_spectral_annihilator_defect_master_synthesis`) and native `Matrix.trace` theorems
  under explicit idempotent `hP : P * P = P` and resolvent hypotheses.

#### BUCKET 3 — Open / Beyond-Scope Obligations
- Infinite-dimensional principal-bundle Cartan connections and continuum functional determinants
  remain outside this algebraic and finite-matrix trace scope.

## i. Overview
Formalizes the 7-stage Maurer–Cartan spectral annihilator `𝓚_{γ₅}`, linear death of odd forms, and multiplicative defect poset (`𝔎₁ ≺ ⋯ ≺ 𝔎₇`).

## ii. Key results
- `MaurerCartanAnnihilatorStage.causalEdge_acyclic`
- `chiralAnnihilator_mul_defect_eq_oddProjector_mul`
- `maurer_cartan_spectral_annihilator_defect_master_synthesis`

## iii. Table of contents
- Section 0: The 7-Stage Acyclic Causal Poset (`𝔎₁ ≺ ⋯ ≺ 𝔎₇`)
- Sections 1–7: Stages `𝔎₁`–`𝔎₇` & Native `Matrix.trace` Theorems

## iv. References
- É. Cartan, *Sur les variétés à connexion affine et la théorie de la relativité généralisée* (1923).
- S. W. MacDowell and F. Mansouri, *Unified Geometric Theory of Gravity and Supergravity* (1977).
-/

noncomputable section

namespace InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian
open InfoGeometry.Canonical.ChiralCondensateGMORBanksCasherNJLPoset
open scoped Matrix

/-! ===========================================================================
    Section 0: The 7-Stage Acyclic Causal Poset (𝔎₁ ≺ 𝔎₂ ≺ ⋯ ≺ 𝔎₇)
    =========================================================================== -/

/-- The 7 stages of the Maurer–Cartan Spectral Annihilator & Multiplicative Defect Causal Poset. -/
inductive MaurerCartanAnnihilatorStage : Type
  | K1_TripotentChiralDerivation
  | K2_IdempotentAnnihilatorFilter
  | K3_LinearAnnihilationOfOddMaurerCartanForms
  | K4_MultiplicativeDefectCurvatureTheorem
  | K5_MaurerCartanOrbitGramianAndBianchiCentrality
  | K6_ElieCartanTorsionAnnihilationAndMacDowellMansouri
  | K7_BanksCasherResolventDriftAnnihilationAndMasterSynthesis
  deriving DecidableEq, Repr

namespace MaurerCartanAnnihilatorStage

/-- Topological rank embedding into `ℕ`. -/
def rank : MaurerCartanAnnihilatorStage → ℕ
  | .K1_TripotentChiralDerivation => 0
  | .K2_IdempotentAnnihilatorFilter => 1
  | .K3_LinearAnnihilationOfOddMaurerCartanForms => 2
  | .K4_MultiplicativeDefectCurvatureTheorem => 3
  | .K5_MaurerCartanOrbitGramianAndBianchiCentrality => 4
  | .K6_ElieCartanTorsionAnnihilationAndMacDowellMansouri => 5
  | .K7_BanksCasherResolventDriftAnnihilationAndMasterSynthesis => 6

/-- `rank` is injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrderMaurerCartanAnnihilatorStage :
    LinearOrder MaurerCartanAnnihilatorStage :=
  LinearOrder.lift' rank rank_injective

/-- Direct cover relation `s₁ ≺ s₂` in the 7-stage causal poset. -/
def causalEdge : MaurerCartanAnnihilatorStage → MaurerCartanAnnihilatorStage → Prop
  | .K1_TripotentChiralDerivation, .K2_IdempotentAnnihilatorFilter => True
  | .K2_IdempotentAnnihilatorFilter, .K3_LinearAnnihilationOfOddMaurerCartanForms => True
  | .K3_LinearAnnihilationOfOddMaurerCartanForms, .K4_MultiplicativeDefectCurvatureTheorem => True
  | .K4_MultiplicativeDefectCurvatureTheorem, .K5_MaurerCartanOrbitGramianAndBianchiCentrality => True
  | .K5_MaurerCartanOrbitGramianAndBianchiCentrality,
    .K6_ElieCartanTorsionAnnihilationAndMacDowellMansouri => True
  | .K6_ElieCartanTorsionAnnihilationAndMacDowellMansouri,
    .K7_BanksCasherResolventDriftAnnihilationAndMasterSynthesis => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

/-- Every direct causal edge strictly increases `rank`. -/
theorem causalEdge_strict_rank {a b : MaurerCartanAnnihilatorStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

/-- Every transitive path of causal edges strictly increases `rank`. -/
theorem transGen_strict_rank {a b : MaurerCartanAnnihilatorStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank hab
  | tail _ hbc ih =>
      have hlt := causalEdge_strict_rank hbc
      omega

/-- **Poset Acyclicity Theorem**: `causalEdge` has no directed cycles. -/
theorem causalEdge_acyclic (a : MaurerCartanAnnihilatorStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  have hlt := transGen_strict_rank h
  exact Nat.lt_irrefl (rank a) hlt

/-- **Complete 7-Stage Causal Chain Theorem**:
`𝔎₁ ≺ 𝔎₂ ≺ 𝔎₃ ≺ 𝔎₄ ≺ 𝔎₅ ≺ 𝔎₆ ≺ 𝔎₇`. -/
theorem causalEdge_chain :
    causalEdge .K1_TripotentChiralDerivation
      .K2_IdempotentAnnihilatorFilter ∧
    causalEdge .K2_IdempotentAnnihilatorFilter
      .K3_LinearAnnihilationOfOddMaurerCartanForms ∧
    causalEdge .K3_LinearAnnihilationOfOddMaurerCartanForms
      .K4_MultiplicativeDefectCurvatureTheorem ∧
    causalEdge .K4_MultiplicativeDefectCurvatureTheorem
      .K5_MaurerCartanOrbitGramianAndBianchiCentrality ∧
    causalEdge .K5_MaurerCartanOrbitGramianAndBianchiCentrality
      .K6_ElieCartanTorsionAnnihilationAndMacDowellMansouri ∧
    causalEdge .K6_ElieCartanTorsionAnnihilationAndMacDowellMansouri
      .K7_BanksCasherResolventDriftAnnihilationAndMasterSynthesis := by
  decide

end MaurerCartanAnnihilatorStage

/-! ===========================================================================
    Section 1: Stage 𝔎₁ — Tripotency of the Chiral Derivation
    ad_P³ = ad_P and ad_{γ₅}³ = 4 ad_{γ₅}
    =========================================================================== -/

section StageK1

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔎₁` (`archetype_K1_tripotent_chiral_derivation`)**:
Over any associative ring `[Ring B]` with idempotent `P * P = P` and `γ₅ = chiralGamma5 P = 2P - 1`:
1. `comm (chiralGamma5 P) X = (2 : ℤ) • peirceGradingDeriv P X`,
2. `comm (chiralGamma5 P) (comm (chiralGamma5 P) X) = (4 : ℤ) • peirceAdSq P X`,
3. `peirceGradingDeriv P (peirceGradingDeriv P (peirceGradingDeriv P X)) = peirceGradingDeriv P X`
   (`ad_P³ = ad_P`),
4. `comm (chiralGamma5 P) (comm (chiralGamma5 P) (comm (chiralGamma5 P) X)) = (4 : ℤ) • comm (chiralGamma5 P) X`
   (`ad_{γ₅}³ = 4 ad_{γ₅}`). -/
theorem archetype_K1_tripotent_chiral_derivation (X : B) :
    OperatorAlgebra.PeirceSpine.comm (chiralGamma5 P) X =
      (2 : ℤ) • peirceGradingDeriv P X ∧
    OperatorAlgebra.PeirceSpine.comm (chiralGamma5 P)
        (OperatorAlgebra.PeirceSpine.comm (chiralGamma5 P) X) =
      (4 : ℤ) • peirceAdSq P X ∧
    peirceGradingDeriv P (peirceGradingDeriv P (peirceGradingDeriv P X)) =
      peirceGradingDeriv P X ∧
    OperatorAlgebra.PeirceSpine.comm (chiralGamma5 P)
        (OperatorAlgebra.PeirceSpine.comm (chiralGamma5 P)
          (OperatorAlgebra.PeirceSpine.comm (chiralGamma5 P) X)) =
      (4 : ℤ) • OperatorAlgebra.PeirceSpine.comm (chiralGamma5 P) X := by
  unfold chiralGamma5 peirceGradingDeriv peirceAdSq
  simp only [two_zsmul, four_zsmul_eq]
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

end StageK1

/-! ===========================================================================
    Section 2: Stage 𝔎₂ — The Idempotent Annihilator Filter
    𝓚_{γ₅}(X) := X - [P, [P, X]] = evenGrade P X
    =========================================================================== -/

section StageK2

variable {B : Type*} [Ring B]

/-- The odd Maurer–Cartan projector `𝒫_odd(P, X) := [P, [P, X]] = peirceAdSq P X`. -/
def oddProjector (P X : B) : B :=
  peirceAdSq P X

/-- The chiral spectral annihilator filter `𝓚_{γ₅}(P, X) := X - [P, [P, X]] = X - peirceAdSq P X`. -/
def chiralAnnihilator (P X : B) : B :=
  X - peirceAdSq P X

variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔎₂` (`archetype_K2_idempotent_annihilator_filter`)**:
1. `chiralAnnihilator P X = evenGrade P X` and `oddProjector P X = oddGrade P X`,
2. Characteristic-free involution-conjugation forms:
   - `(2 : ℤ) • chiralAnnihilator P X = X + chiralGamma5 P * X * chiralGamma5 P`,
   - `(2 : ℤ) • oddProjector P X = X - chiralGamma5 P * X * chiralGamma5 P`,
   - `(4 : ℤ) • chiralAnnihilator P X = (4 : ℤ) • X - comm (chiralGamma5 P) (comm (chiralGamma5 P) X)`,
3. Complementary idempotency:
   - `chiralAnnihilator P (chiralAnnihilator P X) = chiralAnnihilator P X`,
   - `oddProjector P (oddProjector P X) = oddProjector P X`,
   - `chiralAnnihilator P (oddProjector P X) = 0`,
   - `oddProjector P (chiralAnnihilator P X) = 0`,
   - `chiralAnnihilator P X + oddProjector P X = X`. -/
theorem archetype_K2_idempotent_annihilator_filter (X : B) :
    chiralAnnihilator P X = evenGrade P X ∧
    oddProjector P X = oddGrade P X ∧
    (2 : ℤ) • chiralAnnihilator P X =
      X + chiralGamma5 P * X * chiralGamma5 P ∧
    (2 : ℤ) • oddProjector P X =
      X - chiralGamma5 P * X * chiralGamma5 P ∧
    (4 : ℤ) • chiralAnnihilator P X =
      (4 : ℤ) • X -
        OperatorAlgebra.PeirceSpine.comm (chiralGamma5 P)
          (OperatorAlgebra.PeirceSpine.comm (chiralGamma5 P) X) ∧
    chiralAnnihilator P (chiralAnnihilator P X) = chiralAnnihilator P X ∧
    oddProjector P (oddProjector P X) = oddProjector P X ∧
    chiralAnnihilator P (oddProjector P X) = 0 ∧
    oddProjector P (chiralAnnihilator P X) = 0 ∧
    chiralAnnihilator P X + oddProjector P X = X := by
  unfold chiralAnnihilator oddProjector peirceAdSq chiralGamma5
  simp only [two_zsmul, four_zsmul_eq]
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP⟩

/-- `chiralAnnihilator P X` equals the Peirce even-grade projection `evenGrade P X`. -/
theorem chiralAnnihilator_eq_evenGrade (X : B) :
    chiralAnnihilator P X = evenGrade P X := by
  unfold chiralAnnihilator peirceAdSq
  peirce_nf hP

end StageK2

/-! ===========================================================================
    Section 3: Stage 𝔎₃ — Universal Annihilation of Odd Maurer–Cartan Forms
    and Composite 𝔨 · 𝔭 / 𝔭 · 𝔨 Modules
    =========================================================================== -/

section StageK3

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔎₃` (`archetype_K3_linear_annihilation_of_odd_maurer_cartan_forms`)**:
The annihilator filter `chiralAnnihilator P` identically kills:
1. The horizon nilpotents `conePlus P A` and `coneMinus P C`,
2. The odd Maurer–Cartan 1-form `genJ P A C = [P, a]` and chiral condensate `genPhi P A C`,
3. Every composite product, commutator, and anticommutator between an even element
   `evenGrade P X ∈ 𝔨` and an odd Maurer–Cartan form `oddGrade P Y ∈ 𝔭`:
   - `chiralAnnihilator P (evenGrade P X * oddGrade P Y) = 0`,
   - `chiralAnnihilator P (oddGrade P Y * evenGrade P X) = 0`,
   - `chiralAnnihilator P (comm (evenGrade P X) (oddGrade P Y)) = 0`,
   - `chiralAnnihilator P (anticomm (evenGrade P X) (oddGrade P Y)) = 0`,
4. While leaving the even invariants `genV P A C` and `genSig P A C` completely untouched:
   `chiralAnnihilator P (genV P A C) = genV P A C` and
   `chiralAnnihilator P (genSig P A C) = genSig P A C`. -/
theorem archetype_K3_linear_annihilation_of_odd_maurer_cartan_forms (A C X Y : B) :
    chiralAnnihilator P (conePlus P A) = 0 ∧
    chiralAnnihilator P (coneMinus P C) = 0 ∧
    chiralAnnihilator P (genJ P A C) = 0 ∧
    chiralAnnihilator P (genPhi P A C) = 0 ∧
    chiralAnnihilator P (evenGrade P X * oddGrade P Y) = 0 ∧
    chiralAnnihilator P (oddGrade P Y * evenGrade P X) = 0 ∧
    chiralAnnihilator P (OperatorAlgebra.PeirceSpine.comm (evenGrade P X) (oddGrade P Y)) = 0 ∧
    chiralAnnihilator P (anticomm (evenGrade P X) (oddGrade P Y)) = 0 ∧
    chiralAnnihilator P (genV P A C) = genV P A C ∧
    chiralAnnihilator P (genSig P A C) = genSig P A C := by
  unfold chiralAnnihilator peirceAdSq
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP⟩

end StageK3

/-! ===========================================================================
    Section 4: Stage 𝔎₄ — The Multiplicative Defect Theorem:
    Curvature as the Obstruction to Ring Homomorphism
    =========================================================================== -/

section StageK4

variable {B : Type*} [Ring B]

/-- The multiplicative homomorphism defect of `chiralAnnihilator P`:
`mulDefect P X Y := chiralAnnihilator P (X * Y) - chiralAnnihilator P X * chiralAnnihilator P Y`. -/
def chiralAnnihilatorMulDefect (P X Y : B) : B :=
  chiralAnnihilator P (X * Y) - chiralAnnihilator P X * chiralAnnihilator P Y

variable {P : B} (hP : P * P = P)
include hP

/-- **Universal Multiplicative Defect Theorem (`chiralAnnihilator_mul_defect_eq_oddProjector_mul`)**:
For any `X, Y : B`, the failure of `chiralAnnihilator P` to be a multiplicative homomorphism
is identically the product of the killed odd Maurer–Cartan components:
$$\mathcal{K}_{\gamma_5}(X * Y) - \mathcal{K}_{\gamma_5}(X) * \mathcal{K}_{\gamma_5}(Y) = \mathcal{P}_{\mathrm{odd}}(X) * \mathcal{P}_{\mathrm{odd}}(Y).$$ -/
theorem chiralAnnihilator_mul_defect_eq_oddProjector_mul (X Y : B) :
    chiralAnnihilatorMulDefect P X Y = oddProjector P X * oddProjector P Y := by
  unfold chiralAnnihilatorMulDefect chiralAnnihilator oddProjector peirceAdSq
  peirce_nf hP

/-- **Quantum Geometric Tensor as the Multiplicative Defect of `chiralAnnihilator P`**:
Evaluating `chiralAnnihilatorMulDefect P` on the killed odd Maurer–Cartan forms (`conePlus`,
`coneMinus`, `genPhi`, `genJ`) generates the entire Peirce Quantum Geometric Tensor:
1. `chiralAnnihilatorMulDefect P (conePlus P A) (coneMinus P C) = qgtPlus P A C`,
2. `chiralAnnihilatorMulDefect P (coneMinus P C) (conePlus P A) = qgtMinus P A C`,
3. `chiralAnnihilatorMulDefect P (genPhi P A C) (genPhi P A C) = genV P A C`,
4. `chiralAnnihilatorMulDefect P (-genJ P A C) (genJ P A C) = genV P A C`,
5. `chiralAnnihilatorMulDefect P (genJ P A C) (genPhi P A C) = genSig P A C`. -/
theorem qgt_as_chiralAnnihilator_multiplicative_defect (A C : B) :
    chiralAnnihilatorMulDefect P (conePlus P A) (coneMinus P C) = qgtPlus P A C ∧
    chiralAnnihilatorMulDefect P (coneMinus P C) (conePlus P A) = qgtMinus P A C ∧
    chiralAnnihilatorMulDefect P (genPhi P A C) (genPhi P A C) = genV P A C ∧
    chiralAnnihilatorMulDefect P (-genJ P A C) (genJ P A C) = genV P A C ∧
    chiralAnnihilatorMulDefect P (genJ P A C) (genPhi P A C) = genSig P A C := by
  unfold chiralAnnihilatorMulDefect chiralAnnihilator peirceAdSq
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

/-- **Archetype `𝔎₄` Summary (`archetype_K4_multiplicative_defect_curvature_theorem`)**:
Combines the universal multiplicative defect identity with the Quantum Geometric Tensor
realizations. -/
theorem archetype_K4_multiplicative_defect_curvature_theorem (A C X Y : B) :
    chiralAnnihilatorMulDefect P X Y = oddProjector P X * oddProjector P Y ∧
    chiralAnnihilatorMulDefect P (genPhi P A C) (genPhi P A C) = genV P A C ∧
    chiralAnnihilatorMulDefect P (-genJ P A C) (genJ P A C) = genV P A C ∧
    chiralAnnihilatorMulDefect P (genJ P A C) (genPhi P A C) = genSig P A C := by
  unfold chiralAnnihilatorMulDefect chiralAnnihilator oddProjector peirceAdSq
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

end StageK4

/-! ===========================================================================
    Section 5: Stage 𝔎₅ — Filtering the Peirce Maurer–Cartan Curvature
    𝓚_{γ₅}(J + V) = V and Bianchi Centrality [J, V] = [Φ, V] = 0
    =========================================================================== -/

section StageK5

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔎₅` (`archetype_K5_maurer_cartan_orbit_gramian_and_bianchi_centrality`)**:
1. Filtering the Peirce Maurer–Cartan curvature `F_MC(P, A, C) = J + V` through `chiralAnnihilator P`
   kills the odd 1-form `J` and isolates the pure 2-form bandgap `V = genV P A C`:
   `chiralAnnihilator P (peirceMaurerCartanCurvature P A C) = genV P A C`,
2. Filtering through `oddProjector P` isolates `J = genJ P A C`:
   `oddProjector P (peirceMaurerCartanCurvature P A C) = genJ P A C`,
3. Both `J` and `Φ` commute centrally with the surviving curvature `V` (`[J, V] = 0`, `[Φ, V] = 0`),
   so `peirceCovariantDeriv P A C (genV P A C) = 0`. -/
theorem archetype_K5_maurer_cartan_orbit_gramian_and_bianchi_centrality (A C : B) :
    chiralAnnihilator P (peirceMaurerCartanCurvature P A C) = genV P A C ∧
    oddProjector P (peirceMaurerCartanCurvature P A C) = genJ P A C ∧
    OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genV P A C) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genV P A C) = 0 ∧
    peirceCovariantDeriv P A C (genV P A C) = 0 := by
  unfold chiralAnnihilator oddProjector peirceMaurerCartanCurvature
    peirceCovariantDeriv peirceAdSq peirceGradingDeriv
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

end StageK5

/-! ===========================================================================
    Section 6: Stage 𝔎₆ — Killing Élie Cartan Torsion and Isolating
    Riemann–Cartan / MacDowell–Mansouri Curvature
    =========================================================================== -/

section StageK6

variable {B : Type*} [Ring B]

/-- A split Cartan–Ehresmann connection `𝒜(P, X, Y) := evenGrade P X + oddGrade P Y = Ω + Φ`
combining an unbroken gauge connection `Ω = evenGrade P X ∈ 𝔨` and a broken solder form
`Φ = oddGrade P Y ∈ 𝔭`. -/
def cartanSplitConnection (P X Y : B) : B :=
  evenGrade P X + oddGrade P Y

/-- The even Riemann–Cartan curvature `ℛ₁₂ := [Ω₁, Ω₂] + [Φ₁, Φ₂]` of two split Cartan connections. -/
def riemannCartanCurvature (P X₁ Y₁ X₂ Y₂ : B) : B :=
  OperatorAlgebra.PeirceSpine.comm (evenGrade P X₁) (evenGrade P X₂) +
    OperatorAlgebra.PeirceSpine.comm (oddGrade P Y₁) (oddGrade P Y₂)

/-- The odd Élie Cartan torsion `𝒯₁₂ := [Ω₁, Φ₂] + [Φ₁, Ω₂] = [Ω₁, Φ₂] - [Ω₂, Φ₁]` of two split Cartan connections. -/
def elieCartanTorsion (P X₁ Y₁ X₂ Y₂ : B) : B :=
  OperatorAlgebra.PeirceSpine.comm (evenGrade P X₁) (oddGrade P Y₂) +
    OperatorAlgebra.PeirceSpine.comm (oddGrade P Y₁) (evenGrade P X₂)

variable {P : B} (hP : P * P = P)
include hP

set_option maxHeartbeats 600000 in
/-- **Archetype `𝔎₆` (`archetype_K6_elie_cartan_torsion_annihilation_and_macdowell_mansouri`)**:
For any two split Cartan connections `𝒜₁ = cartanSplitConnection P X₁ Y₁` and
`𝒜₂ = cartanSplitConnection P X₂ Y₂`:
1. **Cartan Structure Equation**:
   `[𝒜₁, 𝒜₂] = riemannCartanCurvature P X₁ Y₁ X₂ Y₂ + elieCartanTorsion P X₁ Y₁ X₂ Y₂`,
2. **Exact Torsion Annihilation**:
   `chiralAnnihilator P (elieCartanTorsion P X₁ Y₁ X₂ Y₂) = 0`,
3. **Exact Riemann–Cartan Isolation**:
   `chiralAnnihilator P [𝒜₁, 𝒜₂] = riemannCartanCurvature P X₁ Y₁ X₂ Y₂`,
4. **MacDowell–Mansouri Lie-Bracket Defect**:
   The failure of `chiralAnnihilator P` to commute with the Lie bracket is identically the
   quadratic solder-form commutator `[Φ₁, Φ₂]`:
   `chiralAnnihilator P [𝒜₁, 𝒜₂] - [chiralAnnihilator P 𝒜₁, chiralAnnihilator P 𝒜₂] = [oddGrade P Y₁, oddGrade P Y₂]`. -/
theorem archetype_K6_elie_cartan_torsion_annihilation_and_macdowell_mansouri
    (X₁ Y₁ X₂ Y₂ : B) :
    OperatorAlgebra.PeirceSpine.comm
        (cartanSplitConnection P X₁ Y₁)
        (cartanSplitConnection P X₂ Y₂) =
      riemannCartanCurvature P X₁ Y₁ X₂ Y₂ + elieCartanTorsion P X₁ Y₁ X₂ Y₂ ∧
    chiralAnnihilator P (elieCartanTorsion P X₁ Y₁ X₂ Y₂) = 0 ∧
    chiralAnnihilator P
        (OperatorAlgebra.PeirceSpine.comm
          (cartanSplitConnection P X₁ Y₁)
          (cartanSplitConnection P X₂ Y₂)) =
      riemannCartanCurvature P X₁ Y₁ X₂ Y₂ ∧
    chiralAnnihilator P
        (OperatorAlgebra.PeirceSpine.comm
          (cartanSplitConnection P X₁ Y₁)
          (cartanSplitConnection P X₂ Y₂)) -
      OperatorAlgebra.PeirceSpine.comm
        (chiralAnnihilator P (cartanSplitConnection P X₁ Y₁))
        (chiralAnnihilator P (cartanSplitConnection P X₂ Y₂)) =
      OperatorAlgebra.PeirceSpine.comm (oddGrade P Y₁) (oddGrade P Y₂) := by
  have hSplit :
      OperatorAlgebra.PeirceSpine.comm
          (cartanSplitConnection P X₁ Y₁)
          (cartanSplitConnection P X₂ Y₂) =
        riemannCartanCurvature P X₁ Y₁ X₂ Y₂ + elieCartanTorsion P X₁ Y₁ X₂ Y₂ := by
    unfold cartanSplitConnection riemannCartanCurvature elieCartanTorsion
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  have hAdd : ∀ U V : B,
      chiralAnnihilator P (U + V) = chiralAnnihilator P U + chiralAnnihilator P V := by
    intro U V
    unfold chiralAnnihilator peirceAdSq
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  have hEO1 :
      chiralAnnihilator P
        (OperatorAlgebra.PeirceSpine.comm (evenGrade P X₁) (oddGrade P Y₂)) = 0 := by
    rw [(archetype_K2_idempotent_annihilator_filter hP _).1]
    peirce_nf hP
  have hOE2 :
      chiralAnnihilator P
        (OperatorAlgebra.PeirceSpine.comm (oddGrade P Y₁) (evenGrade P X₂)) = 0 := by
    rw [(archetype_K2_idempotent_annihilator_filter hP _).1]
    peirce_nf hP
  have hTors : chiralAnnihilator P (elieCartanTorsion P X₁ Y₁ X₂ Y₂) = 0 := by
    unfold elieCartanTorsion
    rw [hAdd, hEO1, hOE2, add_zero]
  have hEE :
      chiralAnnihilator P
        (OperatorAlgebra.PeirceSpine.comm (evenGrade P X₁) (evenGrade P X₂)) =
        OperatorAlgebra.PeirceSpine.comm (evenGrade P X₁) (evenGrade P X₂) := by
    rw [(archetype_K2_idempotent_annihilator_filter hP _).1]
    peirce_nf hP
  have hOO :
      chiralAnnihilator P
        (OperatorAlgebra.PeirceSpine.comm (oddGrade P Y₁) (oddGrade P Y₂)) =
        OperatorAlgebra.PeirceSpine.comm (oddGrade P Y₁) (oddGrade P Y₂) := by
    rw [(archetype_K2_idempotent_annihilator_filter hP _).1]
    peirce_nf hP
  have hRiem :
      chiralAnnihilator P (riemannCartanCurvature P X₁ Y₁ X₂ Y₂) =
        riemannCartanCurvature P X₁ Y₁ X₂ Y₂ := by
    unfold riemannCartanCurvature
    rw [hAdd, hEE, hOO]
  have hIso :
      chiralAnnihilator P
          (OperatorAlgebra.PeirceSpine.comm
            (cartanSplitConnection P X₁ Y₁)
            (cartanSplitConnection P X₂ Y₂)) =
        riemannCartanCurvature P X₁ Y₁ X₂ Y₂ := by
    rw [hSplit, hAdd, hRiem, hTors, add_zero]
  have hConn : ∀ X Y : B,
      chiralAnnihilator P (cartanSplitConnection P X Y) = evenGrade P X := by
    intro X Y
    rw [(archetype_K2_idempotent_annihilator_filter hP _).1]
    unfold cartanSplitConnection
    peirce_nf hP
  refine ⟨hSplit, hTors, hIso, ?_⟩
  rw [hIso, hConn X₁ Y₁, hConn X₂ Y₂]
  unfold riemannCartanCurvature
  abel

end StageK6

/-! ===========================================================================
    Section 7: Stage 𝔎₇ — Killing the Odd Resolvent Drift -J(V + η²)⁻¹
    in the Banks–Casher Resolvent & Master Synthesis
    =========================================================================== -/

section StageK7

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔎₇` (`archetype_K7_banks_casher_resolvent_drift_annihilation`)**:
When `P * η = η * P` and `R_η` is a two-sided inverse of `peirceDiracDenom P A C η = V + η²`:
1. `chiralAnnihilator P` kills the odd Dirac resolvent drift `-J * R_η`:
   `chiralAnnihilator P (peirceDiracResolventOdd P A C R_η) = 0`,
2. `chiralAnnihilator P` preserves the even Lorentzian kernel `η * R_η`:
   `chiralAnnihilator P (peirceDiracResolventEven η R_η) = peirceDiracResolventEven η R_η`,
3. `chiralAnnihilator P` filters the full Peirce–Dirac resolvent `(J + η)⁻¹` directly onto the
   Banks–Casher condensate kernel `η * R_η`:
   `chiralAnnihilator P (peirceDiracResolvent P A C η R_η) = η * R_η`,
4. For any cyclically invariant additive map `τ : B →+ G`, `τ X = τ (chiralAnnihilator P X)` and
   `τ (peirceDiracResolvent P A C η R_η) = τ (chiralAnnihilator P (peirceDiracResolvent P A C η R_η)) = τ (η * R_η)`. -/
theorem archetype_K7_banks_casher_resolvent_drift_annihilation
    {G : Type*} [AddCommGroup G] (τ : B →+ G)
    (hτ_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (A C : B) {η R_η : B}
    (hPη : P * η = η * P)
    (hR_right : peirceDiracDenom P A C η * R_η = 1)
    (hR_left : R_η * peirceDiracDenom P A C η = 1) :
    chiralAnnihilator P (peirceDiracResolventOdd P A C R_η) = 0 ∧
    chiralAnnihilator P (peirceDiracResolventEven η R_η) =
      peirceDiracResolventEven η R_η ∧
    chiralAnnihilator P (peirceDiracResolvent P A C η R_η) = η * R_η ∧
    (∀ X : B, τ X = τ (chiralAnnihilator P X)) ∧
    τ (peirceDiracResolvent P A C η R_η) = τ (η * R_η) := by
  have hParity :=
    peirceDiracResolvent_chiral_parity_decomposition hP A C hPη hR_right hR_left
  have hEqEven : ∀ X : B, chiralAnnihilator P X = evenGrade P X :=
    fun X => (archetype_K2_idempotent_annihilator_filter hP X).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hEqEven]
    exact hParity.1
  · rw [hEqEven]
    exact hParity.2.2.1
  · rw [hEqEven]
    exact hParity.2.2.2.2.1
  · intro X
    rw [hEqEven]
    exact (cyclic_trace_oddGrade_zero_and_eq_evenGrade hP τ hτ_cyc X).2.2.2
  · exact (algebraic_banks_casher_resolvent_trace_identity
      hP τ hτ_cyc A C hPη hR_right hR_left).2

/-- **Master Maurer–Cartan Spectral Annihilator & Multiplicative Defect Theorem
(`maurer_cartan_spectral_annihilator_defect_master_synthesis`)**:
Coagulates the complete 7-stage Acyclic Causal Poset `𝔎₁ ≺ 𝔎₂ ≺ 𝔎₃ ≺ 𝔎₄ ≺ 𝔎₅ ≺ 𝔎₆ ≺ 𝔎₇`
into a single kernel-verified theorem. -/
theorem maurer_cartan_spectral_annihilator_defect_master_synthesis
    {G : Type*} [AddCommGroup G] (τ : B →+ G)
    (hτ_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (A C X₁ Y₁ X₂ Y₂ : B) {η R_η : B}
    (hPη : P * η = η * P)
    (hR_right : peirceDiracDenom P A C η * R_η = 1)
    (hR_left : R_η * peirceDiracDenom P A C η = 1) :
    -- (0) Acyclic 7-stage causal poset 𝔎₁ ≺ ⋯ ≺ 𝔎₇
    ((∀ st : MaurerCartanAnnihilatorStage,
        ¬ Relation.TransGen MaurerCartanAnnihilatorStage.causalEdge st st) ∧
     MaurerCartanAnnihilatorStage.causalEdge
       .K1_TripotentChiralDerivation .K2_IdempotentAnnihilatorFilter ∧
     MaurerCartanAnnihilatorStage.causalEdge
       .K6_ElieCartanTorsionAnnihilationAndMacDowellMansouri
       .K7_BanksCasherResolventDriftAnnihilationAndMasterSynthesis) ∧
    -- (1) Stage 𝔎₁ & 𝔎₂: Tripotent derivation & idempotent annihilator filter
    (peirceGradingDeriv P (peirceGradingDeriv P (peirceGradingDeriv P X₁)) =
       peirceGradingDeriv P X₁ ∧
     chiralAnnihilator P X₁ = evenGrade P X₁ ∧
     oddProjector P X₁ = oddGrade P X₁ ∧
     chiralAnnihilator P (chiralAnnihilator P X₁) = chiralAnnihilator P X₁ ∧
     chiralAnnihilator P (oddProjector P X₁) = 0) ∧
    -- (2) Stage 𝔎₃: Linear annihilation of odd Maurer–Cartan forms & composite 𝔨·𝔭 products
    (chiralAnnihilator P (genJ P A C) = 0 ∧
     chiralAnnihilator P (genPhi P A C) = 0 ∧
     chiralAnnihilator P (evenGrade P X₁ * oddGrade P Y₁) = 0 ∧
     chiralAnnihilator P (oddGrade P Y₁ * evenGrade P X₁) = 0) ∧
    -- (3) Stage 𝔎₄: Multiplicative defect = Quantum Geometric Tensor
    (chiralAnnihilatorMulDefect P X₁ Y₁ = oddProjector P X₁ * oddProjector P Y₁ ∧
     chiralAnnihilatorMulDefect P (genPhi P A C) (genPhi P A C) = genV P A C ∧
     chiralAnnihilatorMulDefect P (genJ P A C) (genPhi P A C) = genSig P A C) ∧
    -- (4) Stage 𝔎₅: Filtering Maurer–Cartan curvature & Bianchi centrality
    (chiralAnnihilator P (peirceMaurerCartanCurvature P A C) = genV P A C ∧
     OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genV P A C) = 0 ∧
     peirceCovariantDeriv P A C (genV P A C) = 0) ∧
    -- (5) Stage 𝔎₆: Élie Cartan torsion annihilation & MacDowell–Mansouri curvature isolation
    (chiralAnnihilator P (elieCartanTorsion P X₁ Y₁ X₂ Y₂) = 0 ∧
     chiralAnnihilator P
         (OperatorAlgebra.PeirceSpine.comm
           (cartanSplitConnection P X₁ Y₁)
           (cartanSplitConnection P X₂ Y₂)) =
       riemannCartanCurvature P X₁ Y₁ X₂ Y₂ ∧
     chiralAnnihilator P
         (OperatorAlgebra.PeirceSpine.comm
           (cartanSplitConnection P X₁ Y₁)
           (cartanSplitConnection P X₂ Y₂)) -
       OperatorAlgebra.PeirceSpine.comm
         (chiralAnnihilator P (cartanSplitConnection P X₁ Y₁))
         (chiralAnnihilator P (cartanSplitConnection P X₂ Y₂)) =
       OperatorAlgebra.PeirceSpine.comm (oddGrade P Y₁) (oddGrade P Y₂)) ∧
    -- (6) Stage 𝔎₇: Banks–Casher resolvent drift annihilation & trace reduction
    (chiralAnnihilator P (peirceDiracResolventOdd P A C R_η) = 0 ∧
     chiralAnnihilator P (peirceDiracResolvent P A C η R_η) = η * R_η ∧
     τ (peirceDiracResolvent P A C η R_η) = τ (η * R_η)) := by
  have hK1 := archetype_K1_tripotent_chiral_derivation hP X₁
  have hK2 := archetype_K2_idempotent_annihilator_filter hP X₁
  have hK3 := archetype_K3_linear_annihilation_of_odd_maurer_cartan_forms hP A C X₁ Y₁
  have hK4 := archetype_K4_multiplicative_defect_curvature_theorem hP A C X₁ Y₁
  have hK5 := archetype_K5_maurer_cartan_orbit_gramian_and_bianchi_centrality hP A C
  have hK6 := archetype_K6_elie_cartan_torsion_annihilation_and_macdowell_mansouri hP X₁ Y₁ X₂ Y₂
  have hK7 :=
    archetype_K7_banks_casher_resolvent_drift_annihilation hP τ hτ_cyc A C hPη hR_right hR_left
  exact ⟨⟨MaurerCartanAnnihilatorStage.causalEdge_acyclic,
          MaurerCartanAnnihilatorStage.causalEdge_chain.1,
          MaurerCartanAnnihilatorStage.causalEdge_chain.2.2.2.2.2⟩,
         ⟨hK1.2.2.1, hK2.1, hK2.2.1, hK2.2.2.2.2.2.1, hK2.2.2.2.2.2.2.2.1⟩,
         ⟨hK3.2.2.1, hK3.2.2.2.1, hK3.2.2.2.2.1, hK3.2.2.2.2.2.1⟩,
         ⟨hK4.1, hK4.2.1, hK4.2.2.2⟩,
         ⟨hK5.1, hK5.2.2.1, hK5.2.2.2.2⟩,
         ⟨hK6.2.1, hK6.2.2.1, hK6.2.2.2⟩,
         ⟨hK7.1, hK7.2.2.1, hK7.2.2.2.2⟩⟩

end StageK7

/-! ### Constructive Native Mathlib `Matrix.trace` Theorems (Unassumed Cyclic Trace & Resolvent) -/

section NativeMatrixTrace

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
variable {P : Matrix n n R} (hP : P * P = P)
include hP

/-- Vanishing of `Matrix.trace` on the upper Peirce corner `conePlus P A`, proved directly from
`Matrix.trace_mul_comm` without assuming any external trace axiom. -/
theorem matrix_trace_conePlus_zero (A : Matrix n n R) :
    Matrix.trace (conePlus P A) = 0 := by
  have h := cyclic_trace_oddGrade_zero_and_eq_evenGrade hP
    (Matrix.traceLinearMap n R R).toAddMonoidHom Matrix.trace_mul_comm A
  exact h.1

/-- Vanishing of `Matrix.trace` on the lower Peirce corner `coneMinus P C`, proved directly from
`Matrix.trace_mul_comm` without assuming any external trace axiom. -/
theorem matrix_trace_coneMinus_zero (C : Matrix n n R) :
    Matrix.trace (coneMinus P C) = 0 := by
  have h := cyclic_trace_oddGrade_zero_and_eq_evenGrade hP
    (Matrix.traceLinearMap n R R).toAddMonoidHom Matrix.trace_mul_comm C
  exact h.2.1

/-- Vanishing of `Matrix.trace` on `oddGrade P X`, proved directly from `Matrix.trace_mul_comm`. -/
theorem matrix_trace_oddGrade_zero (X : Matrix n n R) :
    Matrix.trace (oddGrade P X) = 0 := by
  have h := cyclic_trace_oddGrade_zero_and_eq_evenGrade hP
    (Matrix.traceLinearMap n R R).toAddMonoidHom Matrix.trace_mul_comm X
  exact h.2.2.1

/-- Invariance of `Matrix.trace` under `evenGrade P`, proved directly from `Matrix.trace_mul_comm`. -/
theorem matrix_trace_evenGrade_eq (X : Matrix n n R) :
    Matrix.trace (evenGrade P X) = Matrix.trace X := by
  have h := cyclic_trace_oddGrade_zero_and_eq_evenGrade hP
    (Matrix.traceLinearMap n R R).toAddMonoidHom Matrix.trace_mul_comm X
  exact h.2.2.2.symm

omit hP in
/-- Vanishing of `Matrix.trace` on the Heisenberg spin-dipole commutator `genSig P A C`, proved
directly from `Matrix.trace_mul_comm`. -/
theorem matrix_trace_genSig_zero (A C : Matrix n n R) :
    Matrix.trace (genSig P A C) = 0 := by
  unfold genSig OperatorAlgebra.PeirceSpine.comm
  rw [Matrix.trace_sub, Matrix.trace_mul_comm (conePlus P A) (coneMinus P C), sub_self]

/-- The chiral supertrace of `genSig P A C` equals the trace of the Fisher metric `genV P A C`:
`Matrix.trace (invS P * genSig P A C) = Matrix.trace (genV P A C)`. -/
theorem matrix_trace_invS_mul_genSig_eq_trace_genV (A C : Matrix n n R) :
    Matrix.trace (invS P * genSig P A C) = Matrix.trace (genV P A C) := by
  rw [invS_mul_genSig_eq_genV hP A C]

/-- Constructive operator GMOR trace identity on `Matrix n n R`:
`Matrix.trace (genPhi P A C * comm (invS P) (comm (invS P) (genPhi P A C))) =
 (4 : ℤ) • Matrix.trace (genV P A C)`. -/
theorem matrix_trace_gmor_condensate_identity (A C : Matrix n n R) :
    Matrix.trace
      (genPhi P A C *
        OperatorAlgebra.PeirceSpine.comm (invS P)
          (OperatorAlgebra.PeirceSpine.comm (invS P) (genPhi P A C))) =
      (4 : ℤ) • Matrix.trace (genV P A C) := by
  rw [genPhi_mul_comm_invS_comm_invS_genPhi hP A C]
  exact Matrix.trace_smul (4 : ℤ) (genV P A C)

/-- Constructive first-order Neumann Banks–Casher trace reduction on `Matrix n n R` (with no
assumed inverse `R_η` or trace hypothesis `hτ_cyc`):
`Matrix.trace ((-genJ P A C + 1) * (1 - genV P A C)) = Matrix.trace (1 - genV P A C)`. -/
theorem matrix_trace_neumann_resolvent_deg1 (A C : Matrix n n R) :
    Matrix.trace ((-genJ P A C + 1) * (1 - genV P A C)) =
      Matrix.trace (1 - genV P A C) := by
  rw [← matrix_trace_evenGrade_eq hP ((-genJ P A C + 1) * (1 - genV P A C)),
      evenGrade_neumann_resolvent_deg1 hP A C]

/-- Constructive second-order Neumann Banks–Casher trace reduction on `Matrix n n R` (with no
assumed inverse `R_η` or trace hypothesis `hτ_cyc`):
`Matrix.trace ((-genJ P A C + 1) * (1 - genV P A C + genV P A C * genV P A C)) =
 Matrix.trace (1 - genV P A C + genV P A C * genV P A C)`. -/
theorem matrix_trace_neumann_resolvent_deg2 (A C : Matrix n n R) :
    Matrix.trace
      ((-genJ P A C + 1) * (1 - genV P A C + genV P A C * genV P A C)) =
      Matrix.trace (1 - genV P A C + genV P A C * genV P A C) := by
  rw [← matrix_trace_evenGrade_eq hP
        ((-genJ P A C + 1) * (1 - genV P A C + genV P A C * genV P A C)),
      evenGrade_neumann_resolvent_deg2 hP A C]

end NativeMatrixTrace

end InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset

end
