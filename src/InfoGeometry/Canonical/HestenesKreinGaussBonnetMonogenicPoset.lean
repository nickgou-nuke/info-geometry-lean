/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
import InfoGeometry.Analytic.HKColimitStructures

/-!
# The Cauchy–Riemann / Hestenes–Krein Monogenicity / Directed Boundary Integral / Peirce Cauchy Resolvent / Lichnerowicz–Peirce Curvature Square / Universal McKean–Singer Commutator / Gauss–Bonnet Supertrace Poset (`𝔊₁ → 𝔊₈`)

This module formalizes in native Mathlib (Lean 4) the 8-stage acyclic causal poset
(`𝔊₁ ≺ 𝔊₂ ≺ 𝔊₃ ≺ 𝔊₄ ≺ 𝔊₅ ≺ 𝔊₆ ≺ 𝔊₇ ≺ 𝔊₈`) governing the **Cauchy–Riemann /
Hestenes–Krein Monogenicity and Gauss–Bonnet Supertrace Cancellation Cut** across arbitrary
non-commutative associative rings `[Ring B]` equipped with `[Algebra ℝ B]`, parameterized
2D Clifford–Krein even subalgebras (`I² = ε`), native Mathlib Fréchet Hestenes–Krein spaces,
1D interval-integral boundary flux calculus, and concrete non-commutative matrix / Zorn octonion
witnesses:

* **Phase I (The Fundamental Binary Cut `T ↔ S`)**:
  The 2D commutative complex scalar Cauchy–Riemann thesis (`[i, x] = 0`) vs. the $m$-dimensional
  Clifford–Krein pseudoscalar / Peirce involution shadow (`{S_P, Φ} = 0`, `S_P * Φ = J`,
  `2 S_P V^{k+1} = [J, Φ^{2k+1}]`).
* **Phase II (The Fourfold Relational Anatomy)**:
  1. *Internal Consistency*: The 2-component Clifford–Krein even subalgebra `KreinEven R` with
     signature `I² = ε` (`ε = -1` elliptic complex holomorphy vs. `ε = +1` hyperbolic Krein
     light-cone wave monogenicity) and the native Fréchet phase-commuting derivative
     `HKColimit_HKAnalyticAt`.
  2. *Outward Projection*: The inner/exterior vector derivative split `∇F = divPart + curlPart = 0`
     (`divPart = -curlPart`) and the 1D Fundamental Theorem of Calculus boundary-flux vanishing
     law `∫ x in a..b, f' x = f b - f a = 0`.
  3. *Inward Shadow-Intrusion*: The non-commutative Peirce–Dirac Cauchy resolvent kernels
     `K_Φ(z) = (Φ + z • 1) * U_z` (inverting `Φ - z • 1` when `U_z` inverts `V - z² • 1`) and
     `K_J(z) = -(J + z • 1) * W_z` (inverting `J - z • 1` when `W_z` inverts `V + z² • 1`),
     plus the Lichnerowicz–Peirce curvature square `2 • (N_+ * N_-) = V + Σ` and
     `[Φ, J] = -(2 : ℤ) • Σ`.
  4. *Autonomous Ground*: The **Universal McKean–Singer Commutator Identity**
     `[J, Φ^{2k+1}] = (2 : ℤ) • (S_P * V^{k+1})` and `[J, Φ * R] = (2 : ℤ) • (S_P * V * R)`,
     forcing every non-zero Casimir power `V^{k+1}` to have vanishing chiral supertrace
     `Str(V^{k+1}) = 0` and locking the chiral analytical index to the topological zero-mode
     sector `Str(1) = η² Str(R_η) = Str(P_ker)`.
* **Phase IV (Socratic Aporia & Rung 0)**:
  Proves that a reflection `e₁` (`e₁² = ε • 1`, `e₁ e₂ = -e₂ e₁`) anticommutes with the
  oriented area bivector `I₂ = e₁ e₂` (`e₁ I₂ + I₂ e₁ = 0`), just as the Peirce involution `S_P`
  anticommutes with the odd Dirac generator `Φ` (`S_P * Φ + Φ * S_P = 0`), while the
  Lichnerowicz–Peirce commutator `[Φ, J] = -(2 : ℤ) • Σ` exposes the symplectic curvature `Σ`.
* **Phase V (The 8-Stage Acyclic Causal Poset `𝔊₁ ≺ 𝔊₂ ≺ ⋯ ≺ 𝔊₈`, Theorems 1–5, and
  Master Synthesis)**.

### Three-Bucket Audit Map

#### BUCKET 1 — Unconditional Kernel Truth
- `HestenesKreinGaussBonnetStage`, `rank_injective`, `causalEdge_strict_rank_mono`,
  `causalEdge_irrefl`, `transGen_causalEdge_strict_rank_mono`, `causalEdge_acyclic`,
  `causalEdge_chain_and_diamond`.
- `KreinEven` Cauchy–Riemann algebra and Universal McKean–Singer commutator identities.

#### BUCKET 2 — Conditional Kernel Theorems with Explicit Hypotheses
- 1D FTC boundary-flux vanishing under `HasDerivAt`/`IntervalIntegrable`, Peirce–Dirac Cauchy
  resolvent identities under `hP : P * P = P`, and chiral supertrace zero-mode localization under
  commutator-vanishing trace hypotheses.

#### BUCKET 3 — Open / Beyond-Scope Obligations
- Full multidimensional Stokes theorem on curved Riemannian spin manifolds and heat-kernel
  asymptotic expansion remain outside this 1D FTC and algebraic McKean–Singer scope.

## i. Overview
Formalizes the 8-stage Hestenes–Krein monogenicity, directed boundary flux, Peirce–Dirac Cauchy resolvent, and McKean–Singer / Gauss–Bonnet supertrace poset (`𝔊₁ ≺ ⋯ ≺ 𝔊₈`).

## ii. Key results
- `HestenesKreinGaussBonnetStage.causalEdge_acyclic`
- `theorem1_generalized_hestenes_krein_cauchy_riemann`

## iii. Table of contents
- Section 1: The 8-Stage Acyclic Causal Poset (`𝔊₁ ≺ ⋯ ≺ 𝔊₈`)
- Sections 2–6: Rung 0 & Theorems 1–5

## iv. References
- D. Hestenes and G. Sobczyk, *Clifford Algebra to Geometric Calculus* (1984).
- H. P. McKean and I. M. Singer, *Curvature and the eigenvalues of the Laplacian* (1967).
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinGaussBonnetMonogenicPoset

open scoped Matrix BigOperators
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset
open InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume
open InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
open InfoGeometry.Carrier

/-!
## 1. The 8-Stage Acyclic Causal Poset (`𝔊₁ ≺ 𝔊₂ ≺ ⋯ ≺ 𝔊₈`)
-/

/-- The 8-stage causal poset governing the Cauchy–Riemann / Hestenes–Krein Monogenicity,
Directed Boundary Integral, Peirce Cauchy Resolvent, Lichnerowicz–Peirce Curvature Square,
Universal McKean–Singer Commutator, and Gauss–Bonnet Chiral Zero-Mode Index. -/
inductive HestenesKreinGaussBonnetStage : Type
  | G1_KreinCliffordPseudoscalarCut
  | G2_GeneralizedHestenesKreinCauchyRiemann
  | G3_DirectedBoundaryFluxMonogenicVanishing
  | G4_PeirceDiracCauchyResolventSplit
  | G5_LichnerowiczPeirceCurvatureSquare
  | G6_UniversalMcKeanSingerCommutator
  | G7_ResolventScaleInvarianceSupertrace
  | G8_GaussBonnetChiralZeroModeIndex
  deriving DecidableEq, Repr, Inhabited

namespace HestenesKreinGaussBonnetStage

/-- Strictly monotone integer rank `0..7` witnessing the topological ordering of the 8 stages. -/
def rank : HestenesKreinGaussBonnetStage → ℕ
  | .G1_KreinCliffordPseudoscalarCut => 0
  | .G2_GeneralizedHestenesKreinCauchyRiemann => 1
  | .G3_DirectedBoundaryFluxMonogenicVanishing => 2
  | .G4_PeirceDiracCauchyResolventSplit => 3
  | .G5_LichnerowiczPeirceCurvatureSquare => 4
  | .G6_UniversalMcKeanSingerCommutator => 5
  | .G7_ResolventScaleInvarianceSupertrace => 6
  | .G8_GaussBonnetChiralZeroModeIndex => 7

/-- The stage rank map `rank` is injective on `HestenesKreinGaussBonnetStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> revert h <;> decide

instance instLinearOrderHestenesKreinGaussBonnetStage :
    LinearOrder HestenesKreinGaussBonnetStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed edges of the 8-stage Hestenes–Krein / Gauss–Bonnet DAG:
the primary linear spine `𝔊₁ → 𝔊₂ → 𝔊₃ → 𝔊₄ → 𝔊₅ → 𝔊₆ → 𝔊₇ → 𝔊₈` together with the
boundary-to-index topological bridge `𝔊₃ → 𝔊₈` and the curvature-to-resolvent bridge `𝔊₅ → 𝔊₇`. -/
def causalEdge : HestenesKreinGaussBonnetStage → HestenesKreinGaussBonnetStage → Prop
  | .G1_KreinCliffordPseudoscalarCut, .G2_GeneralizedHestenesKreinCauchyRiemann => True
  | .G2_GeneralizedHestenesKreinCauchyRiemann, .G3_DirectedBoundaryFluxMonogenicVanishing => True
  | .G3_DirectedBoundaryFluxMonogenicVanishing, .G4_PeirceDiracCauchyResolventSplit => True
  | .G3_DirectedBoundaryFluxMonogenicVanishing, .G8_GaussBonnetChiralZeroModeIndex => True
  | .G4_PeirceDiracCauchyResolventSplit, .G5_LichnerowiczPeirceCurvatureSquare => True
  | .G5_LichnerowiczPeirceCurvatureSquare, .G6_UniversalMcKeanSingerCommutator => True
  | .G5_LichnerowiczPeirceCurvatureSquare, .G7_ResolventScaleInvarianceSupertrace => True
  | .G6_UniversalMcKeanSingerCommutator, .G7_ResolventScaleInvarianceSupertrace => True
  | .G7_ResolventScaleInvarianceSupertrace, .G8_GaussBonnetChiralZeroModeIndex => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

/-- Every directed causal edge strictly increases the stage rank. -/
theorem causalEdge_strict_rank_mono {a b : HestenesKreinGaussBonnetStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

/-- No stage has a self-loop under `causalEdge`. -/
theorem causalEdge_irrefl (a : HestenesKreinGaussBonnetStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

/-- Any transitive path of causal edges strictly increases the stage rank. -/
theorem transGen_causalEdge_strict_rank_mono {a b : HestenesKreinGaussBonnetStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hbc)

/-- The 8-stage `HestenesKreinGaussBonnetStage` poset is strictly acyclic. -/
theorem causalEdge_acyclic (a : HestenesKreinGaussBonnetStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

/-- Complete 8-stage diamond-and-chain edge witness for `𝔊₁ ≺ ⋯ ≺ 𝔊₈`. -/
theorem causalEdge_chain_and_diamond :
    causalEdge .G1_KreinCliffordPseudoscalarCut .G2_GeneralizedHestenesKreinCauchyRiemann ∧
    causalEdge .G2_GeneralizedHestenesKreinCauchyRiemann .G3_DirectedBoundaryFluxMonogenicVanishing ∧
    causalEdge .G3_DirectedBoundaryFluxMonogenicVanishing .G4_PeirceDiracCauchyResolventSplit ∧
    causalEdge .G3_DirectedBoundaryFluxMonogenicVanishing .G8_GaussBonnetChiralZeroModeIndex ∧
    causalEdge .G4_PeirceDiracCauchyResolventSplit .G5_LichnerowiczPeirceCurvatureSquare ∧
    causalEdge .G5_LichnerowiczPeirceCurvatureSquare .G6_UniversalMcKeanSingerCommutator ∧
    causalEdge .G5_LichnerowiczPeirceCurvatureSquare .G7_ResolventScaleInvarianceSupertrace ∧
    causalEdge .G6_UniversalMcKeanSingerCommutator .G7_ResolventScaleInvarianceSupertrace ∧
    causalEdge .G7_ResolventScaleInvarianceSupertrace .G8_GaussBonnetChiralZeroModeIndex := by
  decide

end HestenesKreinGaussBonnetStage

/-!
## 2. Phase IV / Rung 0: Bivector Reflection Anticommutation & Lichnerowicz Curvature Obstruction
-/

/-- Helper Peirce spine identities for `(Φ, J, V, Σ, S_P)` under `hP : P * P = P`. -/
theorem peirce_dirac_krein_identities {B : Type*} [Ring B] (P A C : B) (hP : P * P = P) :
    invS P * genPhi P A C = genJ P A C ∧
    genPhi P A C * invS P = -genJ P A C ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) = -(2 : ℤ) • genSig P A C ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    invS P * genV P A C = genSig P A C ∧
    genV P A C * invS P = genSig P A C := by
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
    by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

/-- **Rung 0 (Bivector Reflection Sign-Flip & Lichnerowicz Curvature Obstruction)**:
1. In any associative ring `[Ring B]`, if `e₁` and `e₂` anticommute (`e₁ * e₂ = -e₂ * e₁`)
   and `e₁ * e₁ = c` is central (`c * e₂ = e₂ * c`), then `e₁` anticommutes with the bivector
   `I₂ = e₁ * e₂`: `e₁ * (e₁ * e₂) + (e₁ * e₂) * e₁ = 0`.
2. For any idempotent `P * P = P`, the Peirce grading involution `S_P = 2 • P - 1` anticommutes
   with every off-diagonal Dirac generator `Φ = N_+ + N_-`: `invS P * Φ + Φ * invS P = 0`.
3. The chiral Lichnerowicz–Peirce curvature obstruction satisfies
   `2 • (N_+ * N_-) - V = Σ` and `[Φ, J] = -(2 : ℤ) • Σ`. -/
theorem rung0_bivector_reflection_and_lichnerowicz_obstruction
    {B : Type*} [Ring B] (e₁ e₂ c P A C : B)
    (he₁ : e₁ * e₁ = c) (hc : c * e₂ = e₂ * c) (hanti : e₁ * e₂ = -(e₂ * e₁))
    (hP : P * P = P) :
    e₁ * (e₁ * e₂) + (e₁ * e₂) * e₁ = 0 ∧
    invS P * genPhi P A C + genPhi P A C * invS P = 0 ∧
    (2 : ℤ) • (conePlus P A * coneMinus P C) - genV P A C = genSig P A C ∧
    OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) = -(2 : ℤ) • genSig P A C := by
  have hIds := peirce_dirac_krein_identities P A C hP
  refine ⟨?_, ?_, ?_, hIds.2.2.2.2.1⟩
  · calc
      e₁ * (e₁ * e₂) + (e₁ * e₂) * e₁
          = (e₁ * e₁) * e₂ + e₁ * (e₂ * e₁) := by noncomm_ring
      _ = c * e₂ + (e₁ * e₂) * e₁ := by rw [he₁]; noncomm_ring
      _ = c * e₂ + (-(e₂ * e₁)) * e₁ := by rw [hanti]
      _ = c * e₂ - e₂ * (e₁ * e₁) := by noncomm_ring
      _ = c * e₂ - e₂ * c := by rw [he₁]
      _ = 0 := sub_eq_zero.mpr hc
  · calc
      invS P * genPhi P A C + genPhi P A C * invS P
          = genJ P A C + (-genJ P A C) := by rw [hIds.1, hIds.2.1]
      _ = 0 := add_neg_cancel _
  · have hTwoJet := (chiralTwoJet_decomposition P A C).1
    unfold chiralTwoJetPlus at hTwoJet
    calc
      (2 : ℤ) • (conePlus P A * coneMinus P C) - genV P A C
          = (genV P A C + genSig P A C) - genV P A C := by rw [hTwoJet]
      _ = genSig P A C := by abel

/-!
## 3. Stages `𝔊₁` & `𝔊₂` (Theorem 1): Generalized Elliptic & Hyperbolic Hestenes–Krein Cauchy–Riemann System
-/

/-- The 2-component Clifford–Krein even subalgebra carrier `u + I v` over a commutative ring `R`,
where the unit bivector `I = e₁ e₂` satisfies `I² = ε`. -/
abbrev KreinEven (R : Type*) : Type _ := R × R

namespace KreinEven

variable {R : Type*} [CommRing R]

/-- Real (scalar) part `u` of `z = u + I v`. -/
def re (z : KreinEven R) : R := z.1

/-- Imaginary (bivector) part `v` of `z = u + I v`. -/
def im (z : KreinEven R) : R := z.2

/-- Addition in the 2D Clifford–Krein even subalgebra. -/
def add (z w : KreinEven R) : KreinEven R :=
  ⟨z.re + w.re, z.im + w.im⟩

/-- Subtraction in the 2D Clifford–Krein even subalgebra. -/
def sub (z w : KreinEven R) : KreinEven R :=
  ⟨z.re - w.re, z.im - w.im⟩

/-- Scalar multiplication in the 2D Clifford–Krein even subalgebra. -/
def scale (c : R) (z : KreinEven R) : KreinEven R :=
  ⟨c * z.re, c * z.im⟩

/-- Parameterized multiplication `(u₁ + I v₁)(u₂ + I v₂) = (u₁ u₂ + ε v₁ v₂) + I (u₁ v₂ + v₁ u₂)`
with bivector signature `I² = ε`. -/
def mul (ε : R) (z w : KreinEven R) : KreinEven R :=
  ⟨z.re * w.re + ε * z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- The unit bivector `I = ⟨0, 1⟩`. -/
def unitI : KreinEven R := ⟨0, 1⟩

/-- The zero element `⟨0, 0⟩`. -/
def zero : KreinEven R := ⟨0, 0⟩

/-- The pullback Hestenes–Krein Cauchy–Riemann operator
`D_ε(F) = (d₁ - ε I d₂)(u + I v) = (d₁u - ε² d₂v) + I (d₁v - ε d₂u)`. -/
def cauchyRiemannOp (ε d₁u d₁v d₂u d₂v : R) : KreinEven R :=
  ⟨d₁u - ε * ε * d₂v, d₁v - ε * d₂u⟩

end KreinEven

/-- **Theorem 1 (Generalized Elliptic & Hyperbolic Hestenes–Krein Cauchy–Riemann System &
Inner/Exterior Vector Derivative Split, Stages `𝔊₁ → 𝔊₂`)**:
1. The unit bivector `I = unitI` satisfies `I² = ⟨ε, 0⟩`.
2. Acting with `d₁ - ε I d₂` on `F = u + I v` (with partial derivatives `d₁F = ⟨d₁u, d₁v⟩` and
   `d₂F = ⟨d₂u, d₂v⟩`) produces the exact Clifford–Krein operator
   `⟨d₁u - ε² d₂v, d₁v - ε d₂u⟩`.
3. For any unit signature `ε² = 1`, `cauchyRiemannOp ε d₁u d₁v d₂u d₂v = 0` is equivalent to the
   generalized Hestenes–Krein Cauchy–Riemann system `d₁u - d₂v = 0 ∧ d₁v - ε * d₂u = 0`.
4. Specializing to `ε = -1` recovers the elliptic Cauchy–Riemann PDEs
   (`d₁u - d₂v = 0 ∧ d₁v + d₂u = 0`), while `ε = 1` recovers the hyperbolic Krein light-cone
   wave PDEs (`d₁u - d₂v = 0 ∧ d₁v - d₂u = 0`).
5. In any additive group `[AddCommGroup M]`, the Hestenes vector derivative `∇F = divPart + curlPart`
   vanishes (`divPart + curlPart = 0`) if and only if the inner divergence balances the negative
   exterior curl (`divPart = -curlPart`). -/
theorem theorem1_generalized_hestenes_krein_cauchy_riemann
    {R : Type*} [CommRing R] (ε d₁u d₁v d₂u d₂v : R)
    {M : Type*} [AddCommGroup M] (divPart curlPart : M) :
    KreinEven.mul ε (KreinEven.unitI (R := R)) (KreinEven.unitI (R := R)) = ⟨ε, 0⟩ ∧
    KreinEven.sub ⟨d₁u, d₁v⟩
      (KreinEven.scale ε (KreinEven.mul ε KreinEven.unitI ⟨d₂u, d₂v⟩)) =
      KreinEven.cauchyRiemannOp ε d₁u d₁v d₂u d₂v ∧
    (ε * ε = 1 →
      (KreinEven.cauchyRiemannOp ε d₁u d₁v d₂u d₂v = KreinEven.zero ↔
        (d₁u - d₂v = 0 ∧ d₁v - ε * d₂u = 0))) ∧
    (KreinEven.cauchyRiemannOp (-1 : R) d₁u d₁v d₂u d₂v = KreinEven.zero ↔
      (d₁u - d₂v = 0 ∧ d₁v + d₂u = 0)) ∧
    (KreinEven.cauchyRiemannOp (1 : R) d₁u d₁v d₂u d₂v = KreinEven.zero ↔
      (d₁u - d₂v = 0 ∧ d₁v - d₂u = 0)) ∧
    (divPart + curlPart = 0 ↔ divPart = -curlPart) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [KreinEven.mul, KreinEven.unitI, KreinEven.re, KreinEven.im]
  · ext <;> simp [KreinEven.sub, KreinEven.scale, KreinEven.mul, KreinEven.unitI,
      KreinEven.cauchyRiemannOp, KreinEven.re, KreinEven.im] <;> ring
  · intro hε
    simp only [KreinEven.cauchyRiemannOp, KreinEven.zero, Prod.ext_iff, hε, one_mul]
  · simp only [KreinEven.cauchyRiemannOp, KreinEven.zero, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linear_combination h1, by linear_combination h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linear_combination h1, by linear_combination h2⟩
  · simp only [KreinEven.cauchyRiemannOp, KreinEven.zero, Prod.ext_iff, mul_one, one_mul]
  · exact add_eq_zero_iff_eq_neg

/-!
## 4. Stages `𝔊₃` & `𝔊₄` (Theorems 2 & 3): Directed Boundary Flux Vanishing & Peirce–Dirac Cauchy Resolvent Split
-/

/-- **Theorem 2 (Directed Boundary Flux Vanishing & Native Hestenes–Krein Phase-Linearity,
Stage `𝔊₃`)**:
1. By the Fundamental Theorem of Calculus on `[a, b]`, if `f : ℝ → ℝ` has derivative `f'` on
   `Set.uIcc a b` and `f'` is interval-integrable, the interior derivative integral equals the
   directed boundary difference `∫ x in a..b, f' x = f b - f a`.
2. When `f` is monogenic (`∀ x, f' x = 0`), the directed boundary flux vanishes (`f b - f a = 0`
   and `f b = f a`).
3. On any native `JX : HestenesKreinSpace X`, the canonical Hestenes–Krein analytic identity witness
   `HKColimit_HKAnalyticAt.id JX x` satisfies phase-commutation
   `deriv.toLinearMap.comp JX.J = JX.J.comp deriv.toLinearMap`. -/
theorem theorem2_directed_boundary_flux_and_hk_phase_linearity
    (f f' : ℝ → ℝ) (a b : ℝ)
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' MeasureTheory.volume a b)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (JX : HestenesKreinSpace X) (x : X) :
    (∫ t in a..b, f' t) = f b - f a ∧
    ((∀ t, f' t = 0) → f b - f a = 0 ∧ f b = f a) ∧
    (HKColimit_HKAnalyticAt.id JX x).deriv.toLinearMap.comp JX.J =
      JX.J.comp (HKColimit_HKAnalyticAt.id JX x).deriv.toLinearMap := by
  have hFTC : (∫ t in a..b, f' t) = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  refine ⟨hFTC, ?_, (HKColimit_HKAnalyticAt.id JX x).phase_linear_deriv⟩
  intro hzero
  have hIntZero : (∫ t in a..b, f' t) = 0 := by
    simp [hzero]
  have hSubZero : f b - f a = 0 := hFTC.symm.trans hIntZero
  exact ⟨hSubZero, sub_eq_zero.mp hSubZero⟩

/-- **Theorem 3 (Non-Commutative Peirce–Dirac Cauchy Resolvent Split, Stage `𝔊₄`)**:
In any associative ring `[Ring B]` with `[Algebra ℝ B]` and idempotent `P * P = P`, let
`Φ = genPhi P A C`, `J = genJ P A C`, and `V = genV P A C`:
1. `(Φ - z • 1) * (Φ + z • 1) = V - (z ^ 2) • 1` and
   `(Φ + z • 1) * (Φ - z • 1) = V - (z ^ 2) • 1`.
2. If `U_z` is a two-sided inverse of `V - (z ^ 2) • 1`, then the chiral Cauchy kernel
   `K_Φ(z) = (Φ + z • 1) * U_z` is the exact two-sided inverse of `Φ - z • 1` and splits into
   odd (`Φ * U_z`) and even (`z • U_z`) Peirce components.
3. `(J - z • 1) * (-(J + z • 1)) = V + (z ^ 2) • 1` and
   `(-(J + z • 1)) * (J - z • 1) = V + (z ^ 2) • 1`.
4. If `W_z` is a two-sided inverse of `V + (z ^ 2) • 1`, then the Krein Cauchy kernel
   `K_J(z) = -(J + z • 1) * W_z` is the exact two-sided inverse of `J - z • 1`. -/
theorem theorem3_peirce_dirac_cauchy_resolvent_split
    {B : Type*} [Ring B] [Algebra ℝ B] (P A C U_z W_z : B) (z : ℝ)
    (hP : P * P = P)
    (hU_left : (genV P A C - (z ^ 2) • (1 : B)) * U_z = 1)
    (hU_right : U_z * (genV P A C - (z ^ 2) • (1 : B)) = 1)
    (hW_left : (genV P A C + (z ^ 2) • (1 : B)) * W_z = 1)
    (hW_right : W_z * (genV P A C + (z ^ 2) • (1 : B)) = 1) :
    (genPhi P A C - z • (1 : B)) * (genPhi P A C + z • (1 : B)) =
      genV P A C - (z ^ 2) • (1 : B) ∧
    (genPhi P A C - z • (1 : B)) * ((genPhi P A C + z • (1 : B)) * U_z) = 1 ∧
    ((genPhi P A C + z • (1 : B)) * U_z) * (genPhi P A C - z • (1 : B)) = 1 ∧
    (genPhi P A C + z • (1 : B)) * U_z = genPhi P A C * U_z + z • U_z ∧
    (genJ P A C - z • (1 : B)) * (-(genJ P A C + z • (1 : B))) =
      genV P A C + (z ^ 2) • (1 : B) ∧
    (genJ P A C - z • (1 : B)) * (-(genJ P A C + z • (1 : B)) * W_z) = 1 ∧
    (-(genJ P A C + z • (1 : B)) * W_z) * (genJ P A C - z • (1 : B)) = 1 := by
  have hIds := peirce_dirac_krein_identities P A C hP
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := hIds.2.2.1
  have hJSq : genJ P A C * genJ P A C = -genV P A C := hIds.2.2.2.1
  have hPhiFactor1 :
      (genPhi P A C - z • (1 : B)) * (genPhi P A C + z • (1 : B)) =
        genV P A C - (z ^ 2) • (1 : B) := by
    calc
      (genPhi P A C - z • (1 : B)) * (genPhi P A C + z • (1 : B))
          = genPhi P A C * genPhi P A C - (z * z) • (1 : B) := by
            rw [ Algebra.smul_def, Algebra.smul_def ]
            have hz := Algebra.commutes (z : ℝ) (genPhi P A C)
            calc
              (genPhi P A C - algebraMap ℝ B z * 1) * (genPhi P A C + algebraMap ℝ B z * 1)
                  = genPhi P A C * genPhi P A C +
                    (genPhi P A C * algebraMap ℝ B z - algebraMap ℝ B z * genPhi P A C) -
                    (algebraMap ℝ B z * algebraMap ℝ B z) * 1 := by noncomm_ring
              _ = genPhi P A C * genPhi P A C - algebraMap ℝ B (z * z) * 1 := by
                    rw [← hz, sub_self, add_zero, map_mul]
      _ = genV P A C - (z ^ 2) • (1 : B) := by rw [hPhiSq, sq]
  have hPhiFactor2 :
      (genPhi P A C + z • (1 : B)) * (genPhi P A C - z • (1 : B)) =
        genV P A C - (z ^ 2) • (1 : B) := by
    calc
      (genPhi P A C + z • (1 : B)) * (genPhi P A C - z • (1 : B))
          = genPhi P A C * genPhi P A C - (z * z) • (1 : B) := by
            rw [ Algebra.smul_def, Algebra.smul_def ]
            have hz := Algebra.commutes (z : ℝ) (genPhi P A C)
            calc
              (genPhi P A C + algebraMap ℝ B z * 1) * (genPhi P A C - algebraMap ℝ B z * 1)
                  = genPhi P A C * genPhi P A C +
                    (algebraMap ℝ B z * genPhi P A C - genPhi P A C * algebraMap ℝ B z) -
                    (algebraMap ℝ B z * algebraMap ℝ B z) * 1 := by noncomm_ring
              _ = genPhi P A C * genPhi P A C - algebraMap ℝ B (z * z) * 1 := by
                    rw [hz, sub_self, add_zero, map_mul]
      _ = genV P A C - (z ^ 2) • (1 : B) := by rw [hPhiSq, sq]
  have hJFactor1 :
      (genJ P A C - z • (1 : B)) * (-(genJ P A C + z • (1 : B))) =
        genV P A C + (z ^ 2) • (1 : B) := by
    calc
      (genJ P A C - z • (1 : B)) * (-(genJ P A C + z • (1 : B)))
          = -(genJ P A C * genJ P A C) + (z * z) • (1 : B) := by
            rw [ Algebra.smul_def, Algebra.smul_def ]
            have hz := Algebra.commutes (z : ℝ) (genJ P A C)
            calc
              (genJ P A C - algebraMap ℝ B z * 1) * (-(genJ P A C + algebraMap ℝ B z * 1))
                  = -(genJ P A C * genJ P A C) +
                    (algebraMap ℝ B z * genJ P A C - genJ P A C * algebraMap ℝ B z) +
                    (algebraMap ℝ B z * algebraMap ℝ B z) * 1 := by noncomm_ring
              _ = -(genJ P A C * genJ P A C) + algebraMap ℝ B (z * z) * 1 := by
                    rw [hz, sub_self, add_zero, map_mul]
      _ = genV P A C + (z ^ 2) • (1 : B) := by rw [hJSq, neg_neg, sq]
  have hJFactor2 :
      (-(genJ P A C + z • (1 : B))) * (genJ P A C - z • (1 : B)) =
        genV P A C + (z ^ 2) • (1 : B) := by
    calc
      (-(genJ P A C + z • (1 : B))) * (genJ P A C - z • (1 : B))
          = -(genJ P A C * genJ P A C) + (z * z) • (1 : B) := by
            rw [ Algebra.smul_def, Algebra.smul_def ]
            have hz := Algebra.commutes (z : ℝ) (genJ P A C)
            calc
              (-(genJ P A C + algebraMap ℝ B z * 1)) * (genJ P A C - algebraMap ℝ B z * 1)
                  = -(genJ P A C * genJ P A C) +
                    (genJ P A C * algebraMap ℝ B z - algebraMap ℝ B z * genJ P A C) +
                    (algebraMap ℝ B z * algebraMap ℝ B z) * 1 := by noncomm_ring
              _ = -(genJ P A C * genJ P A C) + algebraMap ℝ B (z * z) * 1 := by
                    rw [← hz, sub_self, add_zero, map_mul]
      _ = genV P A C + (z ^ 2) • (1 : B) := by rw [hJSq, neg_neg, sq]
  have hU_comm :
      (genPhi P A C + z • (1 : B)) * U_z = U_z * (genPhi P A C + z • (1 : B)) := by
    have hVPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by
      rw [← hPhiSq]; noncomm_ring
    have hVplusPhi :
        (genV P A C - (z ^ 2) • (1 : B)) * (genPhi P A C + z • (1 : B)) =
          (genPhi P A C + z • (1 : B)) * (genV P A C - (z ^ 2) • (1 : B)) := by
      rw [Algebra.smul_def, Algebra.smul_def]
      have hz1 := Algebra.commutes (z ^ 2 : ℝ) (genPhi P A C)
      have hz2 := Algebra.commutes (z : ℝ) (genV P A C)
      have hz3 := Algebra.commutes (z ^ 2 : ℝ) (algebraMap ℝ B z)
      calc
        (genV P A C - algebraMap ℝ B (z ^ 2) * 1) * (genPhi P A C + algebraMap ℝ B z * 1)
            = genV P A C * genPhi P A C + genV P A C * algebraMap ℝ B z -
              algebraMap ℝ B (z ^ 2) * genPhi P A C -
              algebraMap ℝ B (z ^ 2) * algebraMap ℝ B z := by noncomm_ring
        _ = genPhi P A C * genV P A C + algebraMap ℝ B z * genV P A C -
              genPhi P A C * algebraMap ℝ B (z ^ 2) -
              algebraMap ℝ B z * algebraMap ℝ B (z ^ 2) := by
              rw [hVPhi, ← hz2, hz1, hz3]
        _ = (genPhi P A C + algebraMap ℝ B z * 1) *
              (genV P A C - algebraMap ℝ B (z ^ 2) * 1) := by noncomm_ring
    calc
      (genPhi P A C + z • (1 : B)) * U_z
          = (U_z * (genV P A C - (z ^ 2) • (1 : B))) *
              ((genPhi P A C + z • (1 : B)) * U_z) := by rw [hU_right, one_mul]
      _ = U_z * ((genV P A C - (z ^ 2) • (1 : B)) * (genPhi P A C + z • (1 : B))) * U_z := by
            noncomm_ring
      _ = U_z * ((genPhi P A C + z • (1 : B)) * (genV P A C - (z ^ 2) • (1 : B))) * U_z := by
            rw [hVplusPhi]
      _ = U_z * (genPhi P A C + z • (1 : B)) *
            ((genV P A C - (z ^ 2) • (1 : B)) * U_z) := by noncomm_ring
      _ = U_z * (genPhi P A C + z • (1 : B)) := by rw [hU_left, mul_one]
  have hW_comm :
      (-(genJ P A C + z • (1 : B))) * W_z = W_z * (-(genJ P A C + z • (1 : B))) := by
    have hVJ : genV P A C * genJ P A C = genJ P A C * genV P A C := by
      calc
        genV P A C * genJ P A C = -(genJ P A C * genJ P A C) * genJ P A C := by
          rw [hJSq, neg_neg]
        _ = genJ P A C * (-(genJ P A C * genJ P A C)) := by noncomm_ring
        _ = genJ P A C * genV P A C := by rw [hJSq, neg_neg]
    have hVplusJ :
        (genV P A C + (z ^ 2) • (1 : B)) * (-(genJ P A C + z • (1 : B))) =
          (-(genJ P A C + z • (1 : B))) * (genV P A C + (z ^ 2) • (1 : B)) := by
      rw [Algebra.smul_def, Algebra.smul_def]
      have hz1 := Algebra.commutes (z ^ 2 : ℝ) (genJ P A C)
      have hz2 := Algebra.commutes (z : ℝ) (genV P A C)
      have hz3 := Algebra.commutes (z ^ 2 : ℝ) (algebraMap ℝ B z)
      calc
        (genV P A C + algebraMap ℝ B (z ^ 2) * 1) * (-(genJ P A C + algebraMap ℝ B z * 1))
            = -(genV P A C * genJ P A C) - genV P A C * algebraMap ℝ B z -
              algebraMap ℝ B (z ^ 2) * genJ P A C -
              algebraMap ℝ B (z ^ 2) * algebraMap ℝ B z := by noncomm_ring
        _ = -(genJ P A C * genV P A C) - algebraMap ℝ B z * genV P A C -
              genJ P A C * algebraMap ℝ B (z ^ 2) -
              algebraMap ℝ B z * algebraMap ℝ B (z ^ 2) := by
              rw [hVJ, ← hz2, hz1, hz3]
        _ = (-(genJ P A C + algebraMap ℝ B z * 1)) *
              (genV P A C + algebraMap ℝ B (z ^ 2) * 1) := by noncomm_ring
    calc
      (-(genJ P A C + z • (1 : B))) * W_z
          = (W_z * (genV P A C + (z ^ 2) • (1 : B))) *
              ((-(genJ P A C + z • (1 : B))) * W_z) := by rw [hW_right, one_mul]
      _ = W_z * ((genV P A C + (z ^ 2) • (1 : B)) * (-(genJ P A C + z • (1 : B)))) * W_z := by
            noncomm_ring
      _ = W_z * ((-(genJ P A C + z • (1 : B))) * (genV P A C + (z ^ 2) • (1 : B))) * W_z := by
            rw [hVplusJ]
      _ = W_z * (-(genJ P A C + z • (1 : B))) *
            ((genV P A C + (z ^ 2) • (1 : B)) * W_z) := by noncomm_ring
      _ = W_z * (-(genJ P A C + z • (1 : B))) := by rw [hW_left, mul_one]
  refine ⟨hPhiFactor1, ?_, ?_, ?_, hJFactor1, ?_, ?_⟩
  · calc
      (genPhi P A C - z • (1 : B)) * ((genPhi P A C + z • (1 : B)) * U_z)
          = ((genPhi P A C - z • (1 : B)) * (genPhi P A C + z • (1 : B))) * U_z := by
            noncomm_ring
      _ = (genV P A C - (z ^ 2) • (1 : B)) * U_z := by rw [hPhiFactor1]
      _ = 1 := hU_left
  · calc
      ((genPhi P A C + z • (1 : B)) * U_z) * (genPhi P A C - z • (1 : B))
          = (U_z * (genPhi P A C + z • (1 : B))) * (genPhi P A C - z • (1 : B)) := by
            rw [hU_comm]
      _ = U_z * ((genPhi P A C + z • (1 : B)) * (genPhi P A C - z • (1 : B))) := by
            noncomm_ring
      _ = U_z * (genV P A C - (z ^ 2) • (1 : B)) := by rw [hPhiFactor2]
      _ = 1 := hU_right
  · rw [add_mul, smul_mul_assoc, one_mul]
  · calc
      (genJ P A C - z • (1 : B)) * (-(genJ P A C + z • (1 : B)) * W_z)
          = ((genJ P A C - z • (1 : B)) * (-(genJ P A C + z • (1 : B)))) * W_z := by
            noncomm_ring
      _ = (genV P A C + (z ^ 2) • (1 : B)) * W_z := by rw [hJFactor1]
      _ = 1 := hW_left
  · calc
      (-(genJ P A C + z • (1 : B)) * W_z) * (genJ P A C - z • (1 : B))
          = (W_z * (-(genJ P A C + z • (1 : B)))) * (genJ P A C - z • (1 : B)) := by
            rw [hW_comm]
      _ = W_z * ((-(genJ P A C + z • (1 : B))) * (genJ P A C - z • (1 : B))) := by
            noncomm_ring
      _ = W_z * (genV P A C + (z ^ 2) • (1 : B)) := by rw [hJFactor2]
      _ = 1 := hW_right

/-!
## 5. Stage `𝔊₅`: Lichnerowicz–Peirce Curvature Square & Chiral Dirac Decomposition
-/

/-- **Stage `𝔊₅` (Lichnerowicz–Peirce Curvature Square & Chiral Dirac Decomposition)**:
For any idempotent `P * P = P` in `[Ring B]`, the chiral Dirac cones `N_+ = conePlus P A` and
`N_- = coneMinus P C` decompose the chiral 2-jets into the even Casimir metric `V` and the
symplectic curvature `Σ = S_P * V`:
1. `(2 : ℤ) • (N_+ * N_-) = V + Σ` and `(2 : ℤ) • (N_- * N_+) = V - Σ`;
2. `Φ * Φ = V` and `J * J = -V`;
3. `[Φ, J] = -(2 : ℤ) • Σ` and `{Φ, J} = 0`;
4. `invS P * V = Σ` and `V * invS P = Σ`. -/
theorem stage5_lichnerowicz_peirce_curvature_square
    {B : Type*} [Ring B] (P A C : B) (hP : P * P = P) :
    (2 : ℤ) • (conePlus P A * coneMinus P C) = genV P A C + genSig P A C ∧
    (2 : ℤ) • (coneMinus P C * conePlus P A) = genV P A C - genSig P A C ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) = -(2 : ℤ) • genSig P A C ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    invS P * genV P A C = genSig P A C ∧
    genV P A C * invS P = genSig P A C := by
  have hJet := chiralTwoJet_decomposition P A C
  have hIds := peirce_dirac_krein_identities P A C hP
  exact ⟨hJet.1, hJet.2, hIds.2.2.1, hIds.2.2.2.1,
    hIds.2.2.2.2.1, hIds.2.2.2.2.2.1, hIds.2.2.2.2.2.2.1, hIds.2.2.2.2.2.2.2⟩

/-!
## 6. Stage `𝔊₆` (Theorem 4): The Universal McKean–Singer Commutator Identity
-/

/-- Even powers of the off-diagonal Dirac generator `Φ` equal powers of the Casimir strain `V`:
`Φ ^ (2 * k) = genV P A C ^ k`. -/
theorem genPhi_pow_even {B : Type*} [Ring B] (P A C : B) (hP : P * P = P) (k : ℕ) :
    genPhi P A C ^ (2 * k) = genV P A C ^ k := by
  have hSq : genPhi P A C * genPhi P A C = genV P A C := (peirce_dirac_krein_identities P A C hP).2.2.1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, ih, sq, hSq, ← pow_succ]

/-- Every power of `V = Φ²` commutes with `Φ`. -/
theorem genV_pow_mul_genPhi {B : Type*} [Ring B] (P A C : B) (hP : P * P = P) (k : ℕ) :
    (genV P A C ^ k) * genPhi P A C = genPhi P A C * (genV P A C ^ k) := by
  rw [← genPhi_pow_even P A C hP k, ← pow_succ, ← pow_succ']

/-- Odd powers of `Φ` factor as `Φ ^ (2 * k + 1) = Φ * (V ^ k)`. -/
theorem genPhi_pow_odd {B : Type*} [Ring B] (P A C : B) (hP : P * P = P) (k : ℕ) :
    genPhi P A C ^ (2 * k + 1) = genPhi P A C * (genV P A C ^ k) := by
  rw [pow_succ, genPhi_pow_even P A C hP k, genV_pow_mul_genPhi P A C hP k]

/-- Every power of `V` commutes with the Peirce grading involution `S_P = invS P`. -/
theorem invS_mul_genV_pow {B : Type*} [Ring B] (P A C : B) (hP : P * P = P) (k : ℕ) :
    invS P * (genV P A C ^ k) = (genV P A C ^ k) * invS P := by
  have hComm := comm_invS_genV_pow hP A C k
  unfold OperatorAlgebra.PeirceSpine.comm at hComm
  exact sub_eq_zero.mp hComm

/-- **Theorem 4 (The Universal McKean–Singer Commutator Identity, Stage `𝔊₆`)**:
For any idempotent `P * P = P` in `[Ring B]`:
1. For every `k : ℕ`, the commutator of the skew-Hermitian Krein phase generator `J = S_P * Φ`
   with the odd power `Φ ^ (2 * k + 1)` equals twice the chiral-weighted Casimir power:
   `comm (genJ P A C) (genPhi P A C ^ (2 * k + 1)) = (2 : ℤ) • (invS P * (genV P A C ^ (k + 1)))`.
2. At `k = 0`, `comm (genJ P A C) (genPhi P A C) = (2 : ℤ) • genSig P A C`.
3. For any operator `R : B` commuting with `Φ` and `S_P` (`R * Φ = Φ * R` and `R * S_P = S_P * R`),
   `comm (genJ P A C) (genPhi P A C * R) = (2 : ℤ) • (invS P * genV P A C * R)`. -/
theorem theorem4_universal_mckean_singer_commutator_identity
    {B : Type*} [Ring B] (P A C R : B) (hP : P * P = P) (k : ℕ)
    (hRPhi : R * genPhi P A C = genPhi P A C * R)
    (hRS : R * invS P = invS P * R) :
    OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C ^ (2 * k + 1)) =
      (2 : ℤ) • (invS P * (genV P A C ^ (k + 1))) ∧
    OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C) = (2 : ℤ) • genSig P A C ∧
    OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C * R) =
      (2 : ℤ) • (invS P * genV P A C * R) := by
  have hIds := peirce_dirac_krein_identities P A C hP
  have hJ : genJ P A C = invS P * genPhi P A C := hIds.1.symm
  have hPhiS : genPhi P A C * invS P = -(invS P * genPhi P A C) := by
    rw [hIds.2.1, hJ]
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := hIds.2.2.1
  have hLeft :
      genJ P A C * (genPhi P A C ^ (2 * k + 1)) = invS P * (genV P A C ^ (k + 1)) := by
    calc
      genJ P A C * (genPhi P A C ^ (2 * k + 1))
          = (invS P * genPhi P A C) * (genPhi P A C * (genV P A C ^ k)) := by
            rw [hJ, genPhi_pow_odd P A C hP k]
      _ = invS P * ((genPhi P A C * genPhi P A C) * (genV P A C ^ k)) := by noncomm_ring
      _ = invS P * (genV P A C * (genV P A C ^ k)) := by rw [hPhiSq]
      _ = invS P * (genV P A C ^ (k + 1)) := by rw [← pow_succ']
  have hRight :
      (genPhi P A C ^ (2 * k + 1)) * genJ P A C = -(invS P * (genV P A C ^ (k + 1))) := by
    calc
      (genPhi P A C ^ (2 * k + 1)) * genJ P A C
          = (genPhi P A C * (genV P A C ^ k)) * (invS P * genPhi P A C) := by
            rw [genPhi_pow_odd P A C hP k, hJ]
      _ = ((genV P A C ^ k) * genPhi P A C) * (invS P * genPhi P A C) := by
            rw [genV_pow_mul_genPhi P A C hP k]
      _ = (genV P A C ^ k) * (genPhi P A C * invS P) * genPhi P A C := by noncomm_ring
      _ = (genV P A C ^ k) * (-(invS P * genPhi P A C)) * genPhi P A C := by rw [hPhiS]
      _ = -(((genV P A C ^ k) * invS P) * (genPhi P A C * genPhi P A C)) := by noncomm_ring
      _ = -((invS P * (genV P A C ^ k)) * genV P A C) := by
            rw [← invS_mul_genV_pow P A C hP k, hPhiSq]
      _ = -(invS P * ((genV P A C ^ k) * genV P A C)) := by noncomm_ring
      _ = -(invS P * (genV P A C ^ (k + 1))) := by rw [← pow_succ]
  have hPowComm :
      OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C ^ (2 * k + 1)) =
        (2 : ℤ) • (invS P * (genV P A C ^ (k + 1))) := by
    unfold OperatorAlgebra.PeirceSpine.comm
    rw [hLeft, hRight, sub_neg_eq_add, two_zsmul]
  have hBaseComm :
      OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C) =
        (2 : ℤ) • genSig P A C := by
    peirce_nf hP
  have hResComm :
      OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C * R) =
        (2 : ℤ) • (invS P * genV P A C * R) := by
    unfold OperatorAlgebra.PeirceSpine.comm
    have h1 : genJ P A C * (genPhi P A C * R) = invS P * genV P A C * R := by
      calc
        genJ P A C * (genPhi P A C * R)
            = (invS P * genPhi P A C) * (genPhi P A C * R) := by rw [hJ]
        _ = invS P * (genPhi P A C * genPhi P A C) * R := by noncomm_ring
        _ = invS P * genV P A C * R := by rw [hPhiSq]
    have h2 : (genPhi P A C * R) * genJ P A C = -(invS P * genV P A C * R) := by
      calc
        (genPhi P A C * R) * genJ P A C
            = genPhi P A C * R * (invS P * genPhi P A C) := by rw [hJ]
        _ = genPhi P A C * (R * invS P) * genPhi P A C := by noncomm_ring
        _ = genPhi P A C * (invS P * R) * genPhi P A C := by rw [hRS]
        _ = (genPhi P A C * invS P) * (R * genPhi P A C) := by noncomm_ring
        _ = (-(invS P * genPhi P A C)) * (genPhi P A C * R) := by rw [hPhiS, hRPhi]
        _ = -(invS P * (genPhi P A C * genPhi P A C) * R) := by noncomm_ring
        _ = -(invS P * genV P A C * R) := by rw [hPhiSq]
    rw [h1, h2, sub_neg_eq_add, two_zsmul]
  exact ⟨hPowComm, hBaseComm, hResComm⟩

/-!
## 7. Stages `𝔊₇` & `𝔊₈` (Theorem 5): Resolvent Scale Invariance of the Chiral Supertrace & Gauss–Bonnet Zero-Mode Index
-/

/-- The chiral supertrace `Str(Y) := tr (S_P * Y)` associated to a linear trace functional
`tr : B →ₗ[ℝ] ℝ` and an idempotent cut `P`. -/
def chiralSupertrace {B : Type*} [Ring B] [Algebra ℝ B]
    (tr : B →ₗ[ℝ] ℝ) (P Y : B) : ℝ :=
  tr (invS P * Y)

/-- Any cyclic trace functional vanishes on all commutators. -/
theorem tr_comm_eq_zero {B : Type*} [Ring B] [Algebra ℝ B]
    (tr : B →ₗ[ℝ] ℝ) (htr : ∀ X Y : B, tr (X * Y) = tr (Y * X)) (X Y : B) :
    tr (OperatorAlgebra.PeirceSpine.comm X Y) = 0 := by
  unfold OperatorAlgebra.PeirceSpine.comm
  rw [map_sub, htr X Y, sub_self]

/-- Every positive Casimir power `V ^ (k + 1)` has vanishing chiral supertrace:
`chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0`. -/
theorem chiralSupertrace_genV_pow_succ_eq_zero
    {B : Type*} [Ring B] [Algebra ℝ B]
    (tr : B →ₗ[ℝ] ℝ) (htr : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    (P A C : B) (hP : P * P = P) (k : ℕ) :
    chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0 := by
  have hMcKean :=
    (theorem4_universal_mckean_singer_commutator_identity P A C 1 hP k
      (by noncomm_ring) (by noncomm_ring)).1
  have hTrComm :
      tr (OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C ^ (2 * k + 1))) = 0 :=
    tr_comm_eq_zero tr htr (genJ P A C) (genPhi P A C ^ (2 * k + 1))
  rw [hMcKean, two_zsmul, map_add] at hTrComm
  unfold chiralSupertrace
  linarith

/-- Any two-sided inverse `R_η` of `genV P A C + c • 1` automatically commutes with `Φ` and `S_P`. -/
theorem peirceResolvent_commutes_genPhi_and_invS
    {B : Type*} [Ring B] [Algebra ℝ B] (P A C R_η : B) (c : ℝ)
    (hP : P * P = P)
    (hLeft : (genV P A C + c • (1 : B)) * R_η = 1)
    (hRight : R_η * (genV P A C + c • (1 : B)) = 1) :
    R_η * genPhi P A C = genPhi P A C * R_η ∧
    R_η * invS P = invS P * R_η := by
  have hIds := peirce_dirac_krein_identities P A C hP
  have hVPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by
    rw [← hIds.2.2.1]; noncomm_ring
  have hVS : genV P A C * invS P = invS P * genV P A C := by
    rw [hIds.2.2.2.2.2.2.2, hIds.2.2.2.2.2.2.1]
  have hOpPhi :
      (genV P A C + c • (1 : B)) * genPhi P A C =
        genPhi P A C * (genV P A C + c • (1 : B)) := by
    rw [Algebra.smul_def]
    have hc := Algebra.commutes c (genPhi P A C)
    calc
      (genV P A C + algebraMap ℝ B c * 1) * genPhi P A C
          = genV P A C * genPhi P A C + algebraMap ℝ B c * genPhi P A C := by noncomm_ring
      _ = genPhi P A C * genV P A C + genPhi P A C * algebraMap ℝ B c := by rw [hVPhi, hc]
      _ = genPhi P A C * (genV P A C + algebraMap ℝ B c * 1) := by noncomm_ring
  have hOpS :
      (genV P A C + c • (1 : B)) * invS P =
        invS P * (genV P A C + c • (1 : B)) := by
    rw [Algebra.smul_def]
    have hc := Algebra.commutes c (invS P)
    calc
      (genV P A C + algebraMap ℝ B c * 1) * invS P
          = genV P A C * invS P + algebraMap ℝ B c * invS P := by noncomm_ring
      _ = invS P * genV P A C + invS P * algebraMap ℝ B c := by rw [hVS, hc]
      _ = invS P * (genV P A C + algebraMap ℝ B c * 1) := by noncomm_ring
  refine ⟨?_, ?_⟩
  · calc
      R_η * genPhi P A C
          = R_η * genPhi P A C * ((genV P A C + c • (1 : B)) * R_η) := by rw [hLeft, mul_one]
      _ = R_η * (genPhi P A C * (genV P A C + c • (1 : B))) * R_η := by noncomm_ring
      _ = R_η * ((genV P A C + c • (1 : B)) * genPhi P A C) * R_η := by rw [← hOpPhi]
      _ = (R_η * (genV P A C + c • (1 : B))) * genPhi P A C * R_η := by noncomm_ring
      _ = genPhi P A C * R_η := by rw [hRight, one_mul]
  · calc
      R_η * invS P
          = R_η * invS P * ((genV P A C + c • (1 : B)) * R_η) := by rw [hLeft, mul_one]
      _ = R_η * (invS P * (genV P A C + c • (1 : B))) * R_η := by noncomm_ring
      _ = R_η * ((genV P A C + c • (1 : B)) * invS P) * R_η := by rw [← hOpS]
      _ = (R_η * (genV P A C + c • (1 : B))) * invS P * R_η := by noncomm_ring
      _ = invS P * R_η := by rw [hRight, one_mul]

/-- **Theorem 5 (Resolvent Scale Invariance of the Chiral Supertrace & Gauss–Bonnet Zero-Mode
Index Synthesis, Stages `𝔊₇ → 𝔊₈`)**:
Let `tr : B →ₗ[ℝ] ℝ` be any cyclic trace (`∀ X Y, tr (X * Y) = tr (Y * X)`) and `P * P = P`:
1. Every positive Casimir power has zero chiral supertrace:
   `chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0`, and in particular `tr (genSig P A C) = 0`.
2. If `R_η` is a two-sided resolvent of `genV P A C + (η ^ 2) • 1`, then the excited Casimir
   sector has vanishing chiral supertrace (`chiralSupertrace tr P (genV P A C * R_η) = 0`), and
   the chiral supertrace is strictly scale-invariant across all `η`:
   `chiralSupertrace tr P 1 = (η ^ 2) * chiralSupertrace tr P R_η`.
3. For any zero-mode / excited range decomposition `1 = P_ker + genV P A C * R_reg` where
   `R_reg` commutes with `Φ` and `S_P`, the full chiral supertrace localizes onto the zero-mode
   projector `P_ker`:
   `chiralSupertrace tr P 1 = chiralSupertrace tr P P_ker`. -/
theorem theorem5_resolvent_scale_invariance_and_gauss_bonnet_index
    {B : Type*} [Ring B] [Algebra ℝ B]
    (tr : B →ₗ[ℝ] ℝ) (htr : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    (P A C R_η P_ker R_reg : B) (η : ℝ) (k : ℕ)
    (hP : P * P = P)
    (hRes_left : (genV P A C + (η ^ 2) • (1 : B)) * R_η = 1)
    (hRes_right : R_η * (genV P A C + (η ^ 2) • (1 : B)) = 1)
    (hHodge : (1 : B) = P_ker + genV P A C * R_reg)
    (hRegPhi : R_reg * genPhi P A C = genPhi P A C * R_reg)
    (hRegS : R_reg * invS P = invS P * R_reg) :
    chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0 ∧
    tr (genSig P A C) = 0 ∧
    chiralSupertrace tr P (genV P A C * R_η) = 0 ∧
    chiralSupertrace tr P 1 = (η ^ 2) * chiralSupertrace tr P R_η ∧
    chiralSupertrace tr P 1 = chiralSupertrace tr P P_ker := by
  have hIds := peirce_dirac_krein_identities P A C hP
  have hPowZero := chiralSupertrace_genV_pow_succ_eq_zero tr htr P A C hP k
  have hSigZero : tr (genSig P A C) = 0 := by
    have h0 := chiralSupertrace_genV_pow_succ_eq_zero tr htr P A C hP 0
    unfold chiralSupertrace at h0
    rw [pow_one, hIds.2.2.2.2.2.2.1] at h0
    exact h0
  have hRComm := peirceResolvent_commutes_genPhi_and_invS P A C R_η (η ^ 2) hP hRes_left hRes_right
  have hVR_McKean :=
    (theorem4_universal_mckean_singer_commutator_identity P A C R_η hP 0
      hRComm.1 hRComm.2).2.2
  have hVRZero : chiralSupertrace tr P (genV P A C * R_η) = 0 := by
    have hTrComm :
        tr (OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C * R_η)) = 0 :=
      tr_comm_eq_zero tr htr (genJ P A C) (genPhi P A C * R_η)
    rw [hVR_McKean, two_zsmul, map_add, mul_assoc] at hTrComm
    unfold chiralSupertrace
    linarith
  have hScaleInv : chiralSupertrace tr P 1 = (η ^ 2) * chiralSupertrace tr P R_η := by
    have hDecomp : invS P * 1 = invS P * (genV P A C * R_η) + (η ^ 2) • (invS P * R_η) := by
      calc
        invS P * 1 = invS P * ((genV P A C + (η ^ 2) • (1 : B)) * R_η) := by rw [hRes_left]
        _ = invS P * (genV P A C * R_η + (η ^ 2) • R_η) := by
              rw [add_mul, smul_mul_assoc, one_mul]
        _ = invS P * (genV P A C * R_η) + (η ^ 2) • (invS P * R_η) := by
              rw [mul_add, mul_smul_comm]
    unfold chiralSupertrace at hVRZero ⊢
    calc
      tr (invS P * 1)
          = tr (invS P * (genV P A C * R_η) + (η ^ 2) • (invS P * R_η)) := by rw [hDecomp]
      _ = tr (invS P * (genV P A C * R_η)) + (η ^ 2) * tr (invS P * R_η) := by
            rw [map_add, map_smul, smul_eq_mul]
      _ = (η ^ 2) * tr (invS P * R_η) := by linarith
  have hVReg_McKean :=
    (theorem4_universal_mckean_singer_commutator_identity P A C R_reg hP 0
      hRegPhi hRegS).2.2
  have hVRegZero : chiralSupertrace tr P (genV P A C * R_reg) = 0 := by
    have hTrComm :
        tr (OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C * R_reg)) = 0 :=
      tr_comm_eq_zero tr htr (genJ P A C) (genPhi P A C * R_reg)
    rw [hVReg_McKean, two_zsmul, map_add, mul_assoc] at hTrComm
    unfold chiralSupertrace
    linarith
  have hZeroMode : chiralSupertrace tr P 1 = chiralSupertrace tr P P_ker := by
    have hDecomp : invS P * 1 = invS P * P_ker + invS P * (genV P A C * R_reg) := by
      calc
        invS P * 1 = invS P * (P_ker + genV P A C * R_reg) := by rw [hHodge]
        _ = invS P * P_ker + invS P * (genV P A C * R_reg) := mul_add _ _ _
    unfold chiralSupertrace at hVRegZero ⊢
    calc
      tr (invS P * 1)
          = tr (invS P * P_ker + invS P * (genV P A C * R_reg)) := by rw [hDecomp]
      _ = tr (invS P * P_ker) + tr (invS P * (genV P A C * R_reg)) := map_add _ _ _
      _ = tr (invS P * P_ker) := by linarith
  exact ⟨hPowZero, hSigZero, hVRZero, hScaleInv, hZeroMode⟩

/-!
## 8. Master Structural Synthesis (`𝔊₁ ≺ 𝔊₂ ≺ ⋯ ≺ 𝔊₈`) & Concrete Non-Commutative Witnesses
-/

/-- **Master Cauchy–Riemann / Hestenes–Krein Monogenicity & Gauss–Bonnet Supertrace Synthesis
(`𝔊₁ ≺ 𝔊₂ ≺ ⋯ ≺ 𝔊₈`)**:
Unifies the 8-stage DAG ordering, the generalized elliptic/hyperbolic Hestenes–Krein Cauchy–Riemann
system, the non-commutative Peirce–Dirac Cauchy resolvent kernels, the Universal McKean–Singer
commutator identity `comm J (Φ ^ (2 * k + 1)) = 2 • (S_P * V ^ (k + 1))`, and the resolvent scale
invariance of the chiral Gauss–Bonnet index `Str(1) = η² Str(R_η) = Str(P_ker)`. -/
theorem master_hestenes_krein_gauss_bonnet_monogenic_synthesis
    {B : Type*} [Ring B] [Algebra ℝ B]
    (tr : B →ₗ[ℝ] ℝ) (htr : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    (P A C U_z W_z R_η P_ker R_reg : B) (z η : ℝ) (k : ℕ)
    (hP : P * P = P)
    (hU_left : (genV P A C - (z ^ 2) • (1 : B)) * U_z = 1)
    (hU_right : U_z * (genV P A C - (z ^ 2) • (1 : B)) = 1)
    (hW_left : (genV P A C + (z ^ 2) • (1 : B)) * W_z = 1)
    (hW_right : W_z * (genV P A C + (z ^ 2) • (1 : B)) = 1)
    (hRes_left : (genV P A C + (η ^ 2) • (1 : B)) * R_η = 1)
    (hRes_right : R_η * (genV P A C + (η ^ 2) • (1 : B)) = 1)
    (hHodge : (1 : B) = P_ker + genV P A C * R_reg)
    (hRegPhi : R_reg * genPhi P A C = genPhi P A C * R_reg)
    (hRegS : R_reg * invS P = invS P * R_reg)
    (d₁u d₁v d₂u d₂v : ℝ) :
    (∀ s : HestenesKreinGaussBonnetStage,
      ¬ Relation.TransGen HestenesKreinGaussBonnetStage.causalEdge s s) ∧
    (KreinEven.cauchyRiemannOp (-1 : ℝ) d₁u d₁v d₂u d₂v = KreinEven.zero ↔
      (d₁u - d₂v = 0 ∧ d₁v + d₂u = 0)) ∧
    (KreinEven.cauchyRiemannOp (1 : ℝ) d₁u d₁v d₂u d₂v = KreinEven.zero ↔
      (d₁u - d₂v = 0 ∧ d₁v - d₂u = 0)) ∧
    (genPhi P A C - z • (1 : B)) * ((genPhi P A C + z • (1 : B)) * U_z) = 1 ∧
    (genJ P A C - z • (1 : B)) * (-(genJ P A C + z • (1 : B)) * W_z) = 1 ∧
    OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C ^ (2 * k + 1)) =
      (2 : ℤ) • (invS P * (genV P A C ^ (k + 1))) ∧
    chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0 ∧
    chiralSupertrace tr P 1 = (η ^ 2) * chiralSupertrace tr P R_η ∧
    chiralSupertrace tr P 1 = chiralSupertrace tr P P_ker := by
  have hCR := theorem1_generalized_hestenes_krein_cauchy_riemann (-1 : ℝ) d₁u d₁v d₂u d₂v
    (0 : ℝ) (0 : ℝ)
  have hCauchy := theorem3_peirce_dirac_cauchy_resolvent_split P A C U_z W_z z hP
    hU_left hU_right hW_left hW_right
  have hMcKean := theorem4_universal_mckean_singer_commutator_identity P A C R_reg hP k
    hRegPhi hRegS
  have hIndex := theorem5_resolvent_scale_invariance_and_gauss_bonnet_index tr htr
    P A C R_η P_ker R_reg η k hP hRes_left hRes_right hHodge hRegPhi hRegS
  exact ⟨HestenesKreinGaussBonnetStage.causalEdge_acyclic,
    hCR.2.2.2.1, hCR.2.2.2.2.1, hCauchy.2.1, hCauchy.2.2.2.2.2.1,
    hMcKean.1, hIndex.1, hIndex.2.2.2.1, hIndex.2.2.2.2⟩

/-- Concrete non-commutative `2 × 2` integer matrix witnesses verifying that the chiral Dirac
cones `rnMatrixPlus` and `rnMatrixMinus` are non-commuting and that the McKean–Singer commutator
`[J, Φ] = 2 • Σ` is strictly non-zero (`T16` non-commutativity witness). -/
theorem hkMatrix_noncommutative_and_mckean_singer_ne_zero :
    rnMatrixPlus * rnMatrixMinus ≠ rnMatrixMinus * rnMatrixPlus ∧
    OperatorAlgebra.PeirceSpine.comm (rnMatrixPlus - rnMatrixMinus)
      (rnMatrixPlus + rnMatrixMinus) ≠ 0 := by
  refine ⟨rnMatrix_noncommutative_and_schwarz_defect_ne_zero.1, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [OperatorAlgebra.PeirceSpine.comm, rnMatrixPlus, rnMatrixMinus, Matrix.mul_apply] at h00

end InfoGeometry.Canonical.HestenesKreinGaussBonnetMonogenicPoset
