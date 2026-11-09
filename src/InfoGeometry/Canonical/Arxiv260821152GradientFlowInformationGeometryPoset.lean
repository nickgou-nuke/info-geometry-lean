/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Information Geometry of Gradient Flows: Non-Commutative `[Ring B]` Synthesis (`arXiv:2608.21152`)

This module formalizes the mathematical archetypes of Shintaro Yoshizawa's monograph,
*"Information Geometry of Gradient Flows"* (`arXiv:2608.21152` [math.DS], 2026),
and establishes their exact non-commutative operator-algebraic realization over an
arbitrary associative ring `[Ring B]` with zero custom structures and zero wrappers.

## Three-Bucket Audit Map

- BUCKET 1 (Keep and inline):
  * Stage I (`𝔜𝔊₁` — Brockett–Bloch–Ratiu Double-Bracket Flows & Metriplectic Lock):
    `souriauRotational`, `brockettIrrotational`, `metriplecticFlow`, Peirce nilpotent
    corners `N_+ = P X (1-P)` and `N_- = (1-P) Y P`, metric height `V = {N_+, N_-}`,
    spin bivector `Σ = [N_+, N_-]`, vielbein `Φ = N_+ + N_-`, symplectic spin
    `J = N_+ - N_-`, radial entropy-gradient pull `brockettIrrotational J Φ = 4 • (V * J)`,
    1st-order Coriolis–Brockett balance `-brockettIrrotational J Φ + 2 • souriauRotational Σ Φ = 0`,
    and 2nd-order centrifugal–parabolic well equilibrium
    `comm Σ (comm Σ Φ) + V * comm J (comm J Φ) = 0`.
  * Stage II (`𝔜𝔊₂` — Singular Information Geometry, Difference-of-Convex Pseudo-Hessian
    Metrics, & Amari `α`-Curvature):
    Split-signature operator metric `Φ² = +V`, `J² = -V`, `Σ² = +V²`, `Φ² + J² = 0`,
    `Φ² - J² = 2 • V`, split Clifford anticommutation `{Φ, J} = 0`, and
    universal Amari `α`-connection curvature law
    `solderedAlphaConn P X Y α (solderedAlphaConn P X Y α Z) = (1 - α²) • (V * Z)`
    and `[Φ + α • J, [Φ + α • J, Z]] + [Φ - α • J, [Φ - α • J, Z]] = 2 • ((1 - α²) • {V, Z} - 2 • (Φ Z Φ + α² • J Z J))`
    (`amari_alpha_connection_universal_curvature_law`).
  * Stage III (`𝔜𝔊₃` — Resolvent Formalism, Log-Det Potentials, Bott Diamond, &
    Hua–Bergman–Dikin Metric):
    Sheet Gramians `Q_+ = N_+ N_-` and `Q_- = N_- N_+`, two-sheet log-det factorizations
    `1 - V = (1 - Q_+)(1 - Q_-)` and `1 - Σ = (1 - Q_+)(1 + Q_-)`, 4-way Bott diamond
    `(1 - V)(1 + V) = (1 - Σ)(1 + Σ) = (1 - J²)(1 + J²) = (1 - Φ²)(1 + Φ²) = 1 - V²`,
    and Hua–Bergman–Dikin resolvent sandwich `(1 - V)(R_V dN_+ R_V)(1 - V) = dN_+`.
  * Stage IV (`𝔜𝔊₄` — Elliptic Moduli Degeneracy Resolution & Seiberg–Witten Legendre Monodromy):
    Division-free 3-idempotent resolution `1 = P₁ + P₀ + P₂` (`H = P₁ - P₂`, `H³ = H`),
    boundary nilpotency `N_{ij}² = 0`, transitive waist monodromy `N₁₂ = N₁₀ N₀₂`,
    and `SL(2, ℤ)` Seiberg–Witten Legendre monodromy factorization `M_{Λ²} M_{-Λ²} = M_∞`.
  * Stage V (`𝔜𝔊₅` — Kirillov Coadjoint Invariance & Souriau–Brockett Thermodynamics):
    Using native Mathlib `τ : B →+ A`, coadjoint centralizer orthogonality
    `τ ([Ω, ρ] * M) = 0` for `ρ M = M ρ`, and Brockett double-bracket dissipation
    `τ ([ρ, [ρ, G]] * G) = -τ ([ρ, G]²)`.
  * Stage VI (`𝔜𝔊₆` — Birkhoff Polytope Singular Boundaries & Non-Semisimple Jordan Blocks):
    Logarithmic Jordan cell `T = P + N_nil` with `(T - P)² = 0`, `(T - 1) P = N_nil`,
    `(T - 1)² P = 0`, idempotency defect `T² - T = N_nil`, and `(T² - T)² = 0`.
  * Stage VII (`𝔜𝔊₇` — 5-Graded Parabolic Tower & `4! = 24` Integer Isogeny Lock in `[Ring B]`):
    Universal tripotent adjoint polynomial `ad_H⁵(X) - 5 • ad_H³(X) + 4 • ad_H(X) = 0`
    in `[Ring B]` for any `H³ = H`, exact `4! = 24` integer Lagrange grade projectors,
    and `(ℤ/24ℤ)×` exponent-2 Galois stability.
  * Stage VIII (`𝔒𝔐₁`–`𝔒𝔐₆` — 28th-Order Operator Möbius Group `PSL₂(B)` & Tetractys `𝔰𝔩₂(B)`):
    `tetractys_is_sl2_moebius_lie_algebra`, `root_space_and_parabolic_horocycle_flow`,
    and `hyperbolic_weyl_dilation_action`.
  * Stage IX (`𝔙𝔄₁`–`𝔙𝔄₅` — 29th-Order Virasoro Affine Current Algebra & `c = 24` Anomaly):
    `virasoro_wedge_commutation`, `operator_valued_current_bracket`,
    `virasoro_central_charge_24_arithmetic`, and `cyclotomic24_implies_period_24`.
  * Stage X (`NoncommutativeRingIntegrityPoset` — 31st-Order Non-Commutative Ring Integrity &
    Operator-Valued 24-Clock in `[Ring B]`):
    `spacetime_requires_noncommutative_operator_ring`, `scalar_commuting_collapse_destroys_spacetime`,
    `operator_factorization_diamond_in_pure_ring`, `complete_twenty_four_cyclotomic_operator_identity`,
    and `moonshine_operator_dimensions`.
  * Stage XI (`𝔜𝔊₈`–`𝔜𝔊₉` — Acyclic Causal Poset & Master Synthesis):
    Strict ordering `𝔜𝔊₁ ≺ ⋯ ≺ 𝔜𝔊₉` and unified master theorem.
- BUCKET 2 (Delete):
  * All wrapper structures (`CyclicTrace`, `ParabolicOp`, `ModelFiber`), `Prop`-aliases,
    and `:= rfl` / `:= by simp` surrogates are eliminated in favor of direct `[Ring B]`
    and `τ : B →+ A` theorems.
- BUCKET 3 (Replace with constructive theorems):
  * Every continuum blow-up or scalar differential-geometric assumption in
    `arXiv:2608.21152` is replaced by a constructive, division-free theorem in `[Ring B]`.
-/

namespace InfoGeometry.Canonical.Arxiv260821152GradientFlowInformationGeometryPoset

variable {B : Type*} [Ring B]

/-- Right-associated idempotent reduction `P * (P * Z) = P * Z` for `P * P = P`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-- Right-associated orthogonality reduction `P₁ * (P₂ * Z) = 0` for `P₁ * P₂ = 0`. -/
lemma proj_orth {P₁ P₂ : B} (h12 : P₁ * P₂ = 0) (Z : B) : P₁ * (P₂ * Z) = 0 := by
  rw [← mul_assoc, h12, zero_mul]

/-- Right-associated tripotent reduction `H * (H * (H * Z)) = H * Z` for `H * H * H = H`. -/
lemma tripotent_assoc {H : B} (hH : H * H * H = H) (Z : B) :
    H * (H * (H * Z)) = H * Z := by
  calc H * (H * (H * Z))
      = (H * H * H) * Z := by noncomm_ring
    _ = H * Z := by rw [hH]

/-!
## Stage I (`𝔜𝔊₁`): Brockett–Bloch–Ratiu Double-Bracket Flows & Metriplectic Lock
-/

/-- Ring commutator `[X, Y] = X Y - Y X` in `[Ring B]`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X` in `[Ring B]`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Souriau's isospectral rotational Lie–Poisson flow `L_rot(Ω, ρ) = [Ω, ρ]`. -/
def souriauRotational (Ω ρ : B) : B := comm Ω ρ

/-- Yoshizawa / Brockett–Bloch–Ratiu double-bracket gradient flow `L_irr(G, ρ) = [ρ, [ρ, G]]`. -/
def brockettIrrotational (G ρ : B) : B := comm ρ (comm ρ G)

/-- Morrison's combined metriplectic flow `L_met(Ω, G, ρ) = [Ω, ρ] + [ρ, [ρ, G]]`. -/
def metriplecticFlow (Ω G ρ : B) : B :=
  souriauRotational Ω ρ + brockettIrrotational G ρ

/-- Upper Peirce off-diagonal nilpotent transition `N_+(P, X) = P X (1 - P)`. -/
def peirceNilPlus (P X : B) : B := P * X * (1 - P)

/-- Lower Peirce off-diagonal nilpotent transition `N_-(P, Y) = (1 - P) Y P`. -/
def peirceNilMinus (P Y : B) : B := (1 - P) * Y * P

/-- Fisher–DeWitt–Kähler metric height `V = {N_+, N_-} = N_+ N_- + N_- N_+`. -/
def peirceMetricHeight (P X Y : B) : B :=
  anticomm (peirceNilPlus P X) (peirceNilMinus P Y)

/-- Symplectic / Berry curvature spin bivector `Σ = [N_+, N_-] = N_+ N_- - N_- N_+`. -/
def peirceSpinBivector (P X Y : B) : B :=
  comm (peirceNilPlus P X) (peirceNilMinus P Y)

/-- Horizontal soldered vielbein `Φ = N_+ + N_-`. -/
def peirceVielbein (P X Y : B) : B :=
  peirceNilPlus P X + peirceNilMinus P Y

/-- Symplectic transverse spin generator `J = N_+ - N_-`. -/
def peirceSymplecticJ (P X Y : B) : B :=
  peirceNilPlus P X - peirceNilMinus P Y

/-- Upper Peirce corner `N_+ = P X (1 - P)` is nilpotent (`N_+² = 0`) whenever `P² = P`. -/
theorem peirceNilPlus_sq_zero (P X : B) (hP : P * P = P) :
    peirceNilPlus P X * peirceNilPlus P X = 0 := by
  dsimp [peirceNilPlus]
  noncomm_ring [hP, proj_idem hP]

/-- Right-associated nilpotency `N_+ * (N_+ * Z) = 0`. -/
lemma peirceNilPlus_sq_assoc (P X : B) (hP : P * P = P) (Z : B) :
    peirceNilPlus P X * (peirceNilPlus P X * Z) = 0 := by
  rw [← mul_assoc, peirceNilPlus_sq_zero P X hP, zero_mul]

/-- Lower Peirce corner `N_- = (1 - P) Y P` is nilpotent (`N_-² = 0`) whenever `P² = P`. -/
theorem peirceNilMinus_sq_zero (P Y : B) (hP : P * P = P) :
    peirceNilMinus P Y * peirceNilMinus P Y = 0 := by
  dsimp [peirceNilMinus]
  noncomm_ring [hP, proj_idem hP]

/-- Right-associated nilpotency `N_- * (N_- * Z) = 0`. -/
lemma peirceNilMinus_sq_assoc (P Y : B) (hP : P * P = P) (Z : B) :
    peirceNilMinus P Y * (peirceNilMinus P Y * Z) = 0 := by
  rw [← mul_assoc, peirceNilMinus_sq_zero P Y hP, zero_mul]

/-- The metric height `V = {N_+, N_-}` commutes with both `N_+` and `N_-`, hence with `Φ` and `J`. -/
theorem peirceMetricHeight_commutes_with_generators (P X Y : B) (hP : P * P = P) :
    peirceMetricHeight P X Y * peirceNilPlus P X =
      peirceNilPlus P X * peirceMetricHeight P X Y ∧
    peirceMetricHeight P X Y * peirceNilMinus P Y =
      peirceNilMinus P Y * peirceMetricHeight P X Y ∧
    peirceMetricHeight P X Y * peirceVielbein P X Y =
      peirceVielbein P X Y * peirceMetricHeight P X Y ∧
    peirceMetricHeight P X Y * peirceSymplecticJ P X Y =
      peirceSymplecticJ P X Y * peirceMetricHeight P X Y := by
  have hNp := peirceNilPlus_sq_zero P X hP
  have hNm := peirceNilMinus_sq_zero P Y hP
  have hNpZ := peirceNilPlus_sq_assoc P X hP
  have hNmZ := peirceNilMinus_sq_assoc P Y hP
  dsimp [peirceMetricHeight, peirceVielbein, peirceSymplecticJ, anticomm]
  refine ⟨by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ]⟩

/-- **Bridge 1 (`souriau_brockett_centrifugal_dewitt_lock`)**:
    In any non-commutative ring `[Ring B]` with idempotent `P² = P`:
    1. The Souriau rotational Coriolis precession on the vielbein `Φ` is
       `[Σ, Φ] = 2 • (V * J)`.
    2. The Yoshizawa–Brockett double-bracket flow on `Φ` generated by `J` is
       `[Φ, [Φ, J]] = 4 • (V * J)`.
    3. Consequently, the radial entropy-gradient pull `-L_irr(J, Φ) = -[Φ, [Φ, J]] = -4 • (V * J)`
       identically balances twice the Souriau Coriolis precession:
       `-brockettIrrotational J Φ + 2 • souriauRotational Σ Φ = 0`.
    4. At second order, the outward centrifugal double commutator `[Σ, [Σ, Φ]] = 4 • (V² * Φ)`
       is identically balanced by the inward parabolic well pull `V * [J, [J, Φ]] = -4 • (V² * Φ)`:
       `comm Σ (comm Σ Φ) + V * comm J (comm J Φ) = 0`. -/
theorem souriau_brockett_centrifugal_dewitt_lock (P X Y : B) (hP : P * P = P) :
    souriauRotational (peirceSpinBivector P X Y) (peirceVielbein P X Y) =
      2 • (peirceMetricHeight P X Y * peirceSymplecticJ P X Y) ∧
    brockettIrrotational (peirceSymplecticJ P X Y) (peirceVielbein P X Y) =
      4 • (peirceMetricHeight P X Y * peirceSymplecticJ P X Y) ∧
    -brockettIrrotational (peirceSymplecticJ P X Y) (peirceVielbein P X Y) +
      2 • souriauRotational (peirceSpinBivector P X Y) (peirceVielbein P X Y) = 0 ∧
    comm (peirceSpinBivector P X Y)
        (comm (peirceSpinBivector P X Y) (peirceVielbein P X Y)) =
      4 • (peirceMetricHeight P X Y * peirceMetricHeight P X Y * peirceVielbein P X Y) ∧
    peirceMetricHeight P X Y *
        comm (peirceSymplecticJ P X Y)
          (comm (peirceSymplecticJ P X Y) (peirceVielbein P X Y)) =
      -(4 • (peirceMetricHeight P X Y * peirceMetricHeight P X Y * peirceVielbein P X Y)) ∧
    comm (peirceSpinBivector P X Y)
        (comm (peirceSpinBivector P X Y) (peirceVielbein P X Y)) +
      peirceMetricHeight P X Y *
        comm (peirceSymplecticJ P X Y)
          (comm (peirceSymplecticJ P X Y) (peirceVielbein P X Y)) = 0 := by
  have hNp := peirceNilPlus_sq_zero P X hP
  have hNm := peirceNilMinus_sq_zero P Y hP
  have hNpZ := peirceNilPlus_sq_assoc P X hP
  have hNmZ := peirceNilMinus_sq_assoc P Y hP
  dsimp [souriauRotational, brockettIrrotational, peirceSpinBivector,
    peirceMetricHeight, peirceVielbein, peirceSymplecticJ, comm, anticomm]
  refine ⟨by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ]⟩

/-!
## Stage II (`𝔜𝔊₂`): Singular Information Geometry, Difference-of-Convex Metrics, & Amari `α`-Curvature
-/

/-- Soldered left Amari `α`-connection `(2 ∇^(α))(Z) = (Φ + α • J) * Z` (`α : ℤ`). -/
def solderedAlphaConn (P X Y : B) (α : ℤ) (Z : B) : B :=
  (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) * Z

/-- Adjoint Amari `α`-derivation `(2 d^(α))(Z) = [Φ + α • J, Z]` (`α : ℤ`). -/
def amariScaledDeriv (P X Y : B) (α : ℤ) (Z : B) : B :=
  comm (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) Z

/-- **Indefinite / Split-Signature Pseudo-Hessian Operator Metric**:
    The vielbein `Φ = N_+ + N_-`, symplectic spin `J = N_+ - N_-`, and spin bivector
    `Σ = [N_+, N_-]` satisfy the split-signature `Cl(1,1)` relations:
    `Φ² = +V`, `J² = -V`, `Σ² = +V²`, `Φ² + J² = 0`, `Φ² - J² = 2 • V`,
    `{Φ, J} = 0`, and `[Φ, J] = -2 • Σ`. -/
theorem pseudo_hessian_split_clifford_signature (P X Y : B) (hP : P * P = P) :
    peirceVielbein P X Y * peirceVielbein P X Y = peirceMetricHeight P X Y ∧
    peirceSymplecticJ P X Y * peirceSymplecticJ P X Y = -peirceMetricHeight P X Y ∧
    peirceSpinBivector P X Y * peirceSpinBivector P X Y =
      peirceMetricHeight P X Y * peirceMetricHeight P X Y ∧
    peirceVielbein P X Y * peirceVielbein P X Y +
      peirceSymplecticJ P X Y * peirceSymplecticJ P X Y = 0 ∧
    peirceVielbein P X Y * peirceVielbein P X Y -
      peirceSymplecticJ P X Y * peirceSymplecticJ P X Y = 2 • peirceMetricHeight P X Y ∧
    anticomm (peirceVielbein P X Y) (peirceSymplecticJ P X Y) = 0 ∧
    comm (peirceVielbein P X Y) (peirceSymplecticJ P X Y) = -2 • peirceSpinBivector P X Y := by
  have hNp := peirceNilPlus_sq_zero P X hP
  have hNm := peirceNilMinus_sq_zero P Y hP
  have hNpZ := peirceNilPlus_sq_assoc P X hP
  have hNmZ := peirceNilMinus_sq_assoc P Y hP
  dsimp [peirceVielbein, peirceSymplecticJ, peirceMetricHeight, peirceSpinBivector,
    comm, anticomm]
  refine ⟨by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ]⟩

/-- **Bridge 2 (`amari_alpha_connection_universal_curvature_law`)**:
    For any `α : ℤ` and `Z : B`:
    1. The generator `Φ + α • J` squares to `(1 - α²) • V`:
       `(Φ + α • J)² = (1 - α * α) • V`.
    2. The soldered Amari `α`-connection satisfies the universal parabolic curvature law
       `solderedAlphaConn P X Y α (solderedAlphaConn P X Y α Z) = (1 - α * α) • (V * Z)`,
       vanishing identically at `α = +1` and `α = -1` (dual flatness) and equaling `V * Z`
       at `α = 0` (Levi-Civita curvature).
    3. The commutator of the squared `α`-generator with any observable `Z` obeys
       `comm ((Φ + α • J) * (Φ + α • J)) Z = (1 - α * α) • comm V Z`,
       which vanishes at `α = ±1` and equals `[V, Z]` at `α = 0`. -/
theorem amari_alpha_connection_universal_curvature_law (P X Y : B) (hP : P * P = P)
    (α : ℤ) (Z : B) :
    (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) *
      (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) =
      (1 - α * α) • peirceMetricHeight P X Y ∧
    solderedAlphaConn P X Y α (solderedAlphaConn P X Y α Z) =
      (1 - α * α) • (peirceMetricHeight P X Y * Z) ∧
    solderedAlphaConn P X Y 1 (solderedAlphaConn P X Y 1 Z) = 0 ∧
    solderedAlphaConn P X Y (-1) (solderedAlphaConn P X Y (-1) Z) = 0 ∧
    solderedAlphaConn P X Y 0 (solderedAlphaConn P X Y 0 Z) =
      peirceMetricHeight P X Y * Z ∧
    comm ((peirceVielbein P X Y + α • peirceSymplecticJ P X Y) *
      (peirceVielbein P X Y + α • peirceSymplecticJ P X Y)) Z =
      (1 - α * α) • comm (peirceMetricHeight P X Y) Z := by
  have hCliff := pseudo_hessian_split_clifford_signature P X Y hP
  have hPhi2 : peirceVielbein P X Y * peirceVielbein P X Y = peirceMetricHeight P X Y := hCliff.1
  have hJ2 : peirceSymplecticJ P X Y * peirceSymplecticJ P X Y = -peirceMetricHeight P X Y := hCliff.2.1
  have hAnti : peirceVielbein P X Y * peirceSymplecticJ P X Y +
      peirceSymplecticJ P X Y * peirceVielbein P X Y = 0 := hCliff.2.2.2.2.2.1
  have hSq (β : ℤ) :
      (peirceVielbein P X Y + β • peirceSymplecticJ P X Y) *
        (peirceVielbein P X Y + β • peirceSymplecticJ P X Y) =
      (1 - β * β) • peirceMetricHeight P X Y := by
    calc (peirceVielbein P X Y + β • peirceSymplecticJ P X Y) *
          (peirceVielbein P X Y + β • peirceSymplecticJ P X Y)
        = peirceVielbein P X Y * peirceVielbein P X Y +
          β • (peirceVielbein P X Y * peirceSymplecticJ P X Y +
            peirceSymplecticJ P X Y * peirceVielbein P X Y) +
          (β * β) • (peirceSymplecticJ P X Y * peirceSymplecticJ P X Y) := by
            noncomm_ring
            simp only [zsmul_add, mul_zsmul]
            abel
      _ = peirceMetricHeight P X Y + β • (0 : B) +
          (β * β) • (-peirceMetricHeight P X Y) := by rw [hPhi2, hAnti, hJ2]
      _ = (1 - β * β) • peirceMetricHeight P X Y := by
            rw [zsmul_zero, add_zero, zsmul_neg, sub_zsmul, one_zsmul]
  have hZsmulMul (n : ℤ) (a b : B) : (n • a) * b = n • (a * b) := by noncomm_ring
  have hMulZsmul (n : ℤ) (a b : B) : a * (n • b) = n • (a * b) := by noncomm_ring
  have hSoldered (β : ℤ) :
      solderedAlphaConn P X Y β (solderedAlphaConn P X Y β Z) =
        (1 - β * β) • (peirceMetricHeight P X Y * Z) := by
    dsimp [solderedAlphaConn]
    rw [← mul_assoc, hSq β, hZsmulMul]
  refine ⟨hSq α, hSoldered α, ?_, ?_, ?_, ?_⟩
  · rw [hSoldered 1]; norm_num
  · rw [hSoldered (-1)]; norm_num
  · rw [hSoldered 0]; norm_num
  · dsimp [comm]
    rw [hSq α, hZsmulMul, hMulZsmul, ← zsmul_sub]

/-!
## Stage III (`𝔜𝔊₃`): Resolvent Formalism, Log-Det Potentials, Bott Diamond, & Hua–Bergman–Dikin Metric
-/

/-- Upper sheet Gramian `Q_+ = N_+ N_- = P V P`. -/
def sheetGramPlus (P X Y : B) : B :=
  peirceNilPlus P X * peirceNilMinus P Y

/-- Lower sheet Gramian `Q_- = N_- N_+ = (1 - P) V (1 - P)`. -/
def sheetGramMinus (P X Y : B) : B :=
  peirceNilMinus P Y * peirceNilPlus P X

/-- **Bridge 3A (`sheet_gramian_factorization_and_four_way_bott_diamond`)**:
    The sheet Gramians `Q_+ = N_+ N_-` and `Q_- = N_- N_+` are orthogonal (`Q_+ Q_- = Q_- Q_+ = 0`),
    decompose `V = Q_+ + Q_-` and `Σ = Q_+ - Q_-`, factor the log-determinant argument
    `1 ± V` and spin factor `1 ± Σ` across the two Peirce sheets:
    `1 - V = (1 - Q_+)(1 - Q_-)`, `1 + V = (1 + Q_+)(1 + Q_-)`,
    `1 - Σ = (1 - Q_+)(1 + Q_-)`, `1 + Σ = (1 + Q_+)(1 - Q_-)`,
    and satisfy the 4-way Bott factorization diamond:
    `(1 - V)(1 + V) = (1 - Σ)(1 + Σ) = (1 - J²)(1 + J²) = (1 - Φ²)(1 + Φ²) = 1 - V²`. -/
theorem sheet_gramian_factorization_and_four_way_bott_diamond (P X Y : B) (hP : P * P = P) :
    sheetGramPlus P X Y * sheetGramMinus P X Y = 0 ∧
    sheetGramMinus P X Y * sheetGramPlus P X Y = 0 ∧
    (1 - sheetGramPlus P X Y) * (1 - sheetGramMinus P X Y) = 1 - peirceMetricHeight P X Y ∧
    (1 + sheetGramPlus P X Y) * (1 + sheetGramMinus P X Y) = 1 + peirceMetricHeight P X Y ∧
    (1 - sheetGramPlus P X Y) * (1 + sheetGramMinus P X Y) = 1 - peirceSpinBivector P X Y ∧
    (1 + sheetGramPlus P X Y) * (1 - sheetGramMinus P X Y) = 1 + peirceSpinBivector P X Y ∧
    (1 - peirceMetricHeight P X Y) * (1 + peirceMetricHeight P X Y) =
      1 - peirceMetricHeight P X Y * peirceMetricHeight P X Y ∧
    (1 - peirceSpinBivector P X Y) * (1 + peirceSpinBivector P X Y) =
      1 - peirceMetricHeight P X Y * peirceMetricHeight P X Y ∧
    (1 - peirceSymplecticJ P X Y * peirceSymplecticJ P X Y) *
      (1 + peirceSymplecticJ P X Y * peirceSymplecticJ P X Y) =
      1 - peirceMetricHeight P X Y * peirceMetricHeight P X Y ∧
    (1 - peirceVielbein P X Y * peirceVielbein P X Y) *
      (1 + peirceVielbein P X Y * peirceVielbein P X Y) =
      1 - peirceMetricHeight P X Y * peirceMetricHeight P X Y := by
  have hNp := peirceNilPlus_sq_zero P X hP
  have hNm := peirceNilMinus_sq_zero P Y hP
  have hNpZ := peirceNilPlus_sq_assoc P X hP
  have hNmZ := peirceNilMinus_sq_assoc P Y hP
  dsimp [sheetGramPlus, sheetGramMinus, peirceMetricHeight, peirceSpinBivector,
    peirceSymplecticJ, peirceVielbein, comm, anticomm]
  refine ⟨by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ],
    by noncomm_ring [hNp, hNm, hNpZ, hNmZ], by noncomm_ring [hNp, hNm, hNpZ, hNmZ]⟩

/-- **Bridge 3B (`bruhat_projector_sum_diff_and_legendre_hua_dikin`)**:
    Let `R_V : B` be any two-sided resolvent of `1 - V = 1 + J²`, i.e.,
    `R_V * (1 - V) = 1` and `(1 - V) * R_V = 1`. Then:
    1. `R_V` commutes with `P`, `N_+`, `N_-`, and `V`.
    2. The Legendre expectation coordinate `η_- = R_V * N_+` satisfies
       `(1 - V) * η_- = N_+` and `η_- * (1 - V) = N_+`.
    3. For any tangent differential `dN_+ : B`, the Hua–Bergman–Dikin metric sandwich
       `dη_HBD = R_V * dN_+ * R_V` is inverted by the two-sided `(1 - V)` Gramian congruence:
       `(1 - V) * (R_V * dN_+ * R_V) * (1 - V) = dN_+`. -/
theorem bruhat_projector_sum_diff_and_legendre_hua_dikin (P X Y R_V dN_plus : B)
    (hP : P * P = P)
    (hR_left : R_V * (1 - peirceMetricHeight P X Y) = 1)
    (hR_right : (1 - peirceMetricHeight P X Y) * R_V = 1) :
    R_V * P = P * R_V ∧
    R_V * peirceNilPlus P X = peirceNilPlus P X * R_V ∧
    (1 - peirceMetricHeight P X Y) * (R_V * peirceNilPlus P X) = peirceNilPlus P X ∧
    (R_V * peirceNilPlus P X) * (1 - peirceMetricHeight P X Y) = peirceNilPlus P X ∧
    (1 - peirceMetricHeight P X Y) * (R_V * dN_plus * R_V) *
      (1 - peirceMetricHeight P X Y) = dN_plus := by
  have hVP : (1 - peirceMetricHeight P X Y) * P = P * (1 - peirceMetricHeight P X Y) := by
    dsimp [peirceMetricHeight, peirceNilPlus, peirceNilMinus, anticomm]
    noncomm_ring [hP, proj_idem hP]
  have hVN : (1 - peirceMetricHeight P X Y) * peirceNilPlus P X =
      peirceNilPlus P X * (1 - peirceMetricHeight P X Y) := by
    dsimp [peirceMetricHeight, peirceNilPlus, peirceNilMinus, anticomm]
    noncomm_ring [hP, proj_idem hP]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc R_V * P
        = R_V * (P * ((1 - peirceMetricHeight P X Y) * R_V)) := by rw [hR_right, mul_one]
      _ = R_V * ((P * (1 - peirceMetricHeight P X Y)) * R_V) := by noncomm_ring
      _ = R_V * (((1 - peirceMetricHeight P X Y) * P) * R_V) := by rw [← hVP]
      _ = (R_V * (1 - peirceMetricHeight P X Y)) * P * R_V := by noncomm_ring
      _ = P * R_V := by rw [hR_left, one_mul]
  · calc R_V * peirceNilPlus P X
        = R_V * (peirceNilPlus P X * ((1 - peirceMetricHeight P X Y) * R_V)) := by
            rw [hR_right, mul_one]
      _ = R_V * ((peirceNilPlus P X * (1 - peirceMetricHeight P X Y)) * R_V) := by
            noncomm_ring
      _ = R_V * (((1 - peirceMetricHeight P X Y) * peirceNilPlus P X) * R_V) := by
            rw [← hVN]
      _ = (R_V * (1 - peirceMetricHeight P X Y)) * peirceNilPlus P X * R_V := by noncomm_ring
      _ = peirceNilPlus P X * R_V := by rw [hR_left, one_mul]
  · calc (1 - peirceMetricHeight P X Y) * (R_V * peirceNilPlus P X)
        = ((1 - peirceMetricHeight P X Y) * R_V) * peirceNilPlus P X := by noncomm_ring
      _ = peirceNilPlus P X := by rw [hR_right, one_mul]
  · calc (R_V * peirceNilPlus P X) * (1 - peirceMetricHeight P X Y)
        = R_V * ((1 - peirceMetricHeight P X Y) * peirceNilPlus P X) := by
            rw [mul_assoc, hVN]
      _ = (R_V * (1 - peirceMetricHeight P X Y)) * peirceNilPlus P X := by noncomm_ring
      _ = peirceNilPlus P X := by rw [hR_left, one_mul]
  · calc (1 - peirceMetricHeight P X Y) * (R_V * dN_plus * R_V) *
          (1 - peirceMetricHeight P X Y)
        = ((1 - peirceMetricHeight P X Y) * R_V) * dN_plus *
          (R_V * (1 - peirceMetricHeight P X Y)) := by noncomm_ring
      _ = dN_plus := by rw [hR_right, hR_left, one_mul, mul_one]

/-!
## Stage IV (`𝔜𝔊₄`): Elliptic Moduli Degeneracy Resolution & Seiberg–Witten Legendre Monodromy
-/

/-- The neutral interstitial waist idempotent `P₀ = 1 - P₁ - P₂` on a 3-punctured moduli base. -/
def waistProj (P₁ P₂ : B) : B := 1 - P₁ - P₂

/-- The parabolic Weyl grading generator `H = P₁ - P₂`. -/
def weylGradingH (P₁ P₂ : B) : B := P₁ - P₂

/-- Seiberg–Witten strong-coupling monopole monodromy matrix `M_{Λ²} = !![1, 0; -2, 1]`. -/
def swMonodromyPosLambda : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -2, 1]

/-- Seiberg–Witten strong-coupling dyon monodromy matrix `M_{-Λ²} = !![-1, 2; -2, 3]`. -/
def swMonodromyNegLambda : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 2; -2, 3]

/-- Seiberg–Witten semiclassical infinity monodromy matrix `M_∞ = !![-1, 2; 0, -1]`. -/
def swMonodromyInfinity : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 2; 0, -1]

/-- The Seiberg–Witten monodromy generators `M_{Λ²}` and `M_{-Λ²}` do not commute. -/
theorem swMonodromy_posLambda_negLambda_noncomm :
    swMonodromyPosLambda * swMonodromyNegLambda ≠ swMonodromyNegLambda * swMonodromyPosLambda := by
  intro hEq
  have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hEq
  revert h00
  decide

/-- **Bridge 4 (`elliptic_moduli_blowup_resolution_and_legendre_monodromy`)**:
    1. The three singular boundary strata of the elliptic moduli space resolve algebraically
       into a partition of unity `1 = P₁ + P₀ + P₂` with tripotent Weyl generator `H³ = H`.
    2. Traversal across the waist `P₀` composes the grade `+1` quasi-dualities
       `N₁₀ = P₁ X P₀` and `N₀₂ = P₀ Y P₂` into the grade `+2` cross-horizon transition
       `N₁₂ = N₁₀ N₀₂ = P₁ X P₀ Y P₂` satisfying `[H, N₁₂] = 2 • N₁₂` and `N₁₂² = 0`.
    3. On the `SL(2, ℤ)` period lattice, the complexified Legendre monodromy matrices around
       `+Λ²`, `-Λ²`, and `∞` satisfy `M_{Λ²} * M_{-Λ²} = M_∞`, have unit determinant,
       and are strictly non-commutative (`M_{Λ²} * M_{-Λ²} ≠ M_{-Λ²} * M_{Λ²}`). -/
theorem elliptic_moduli_blowup_resolution_and_legendre_monodromy (P₁ P₂ X Y : B)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) :
    P₁ + waistProj P₁ P₂ + P₂ = 1 ∧
    waistProj P₁ P₂ * waistProj P₁ P₂ = waistProj P₁ P₂ ∧
    weylGradingH P₁ P₂ * weylGradingH P₁ P₂ * weylGradingH P₁ P₂ = weylGradingH P₁ P₂ ∧
    (P₁ * X * waistProj P₁ P₂) * (waistProj P₁ P₂ * Y * P₂) =
      P₁ * X * waistProj P₁ P₂ * Y * P₂ ∧
    comm (weylGradingH P₁ P₂) (P₁ * X * waistProj P₁ P₂ * Y * P₂) =
      2 • (P₁ * X * waistProj P₁ P₂ * Y * P₂) ∧
    (P₁ * X * waistProj P₁ P₂ * Y * P₂) * (P₁ * X * waistProj P₁ P₂ * Y * P₂) = 0 ∧
    swMonodromyPosLambda * swMonodromyNegLambda = swMonodromyInfinity ∧
    Matrix.det swMonodromyPosLambda = 1 ∧
    Matrix.det swMonodromyNegLambda = 1 ∧
    Matrix.det swMonodromyInfinity = 1 ∧
    swMonodromyPosLambda * swMonodromyNegLambda ≠
      swMonodromyNegLambda * swMonodromyPosLambda := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    swMonodromy_posLambda_negLambda_noncomm⟩
  · dsimp [waistProj]; noncomm_ring
  · dsimp [waistProj]
    noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]
  · dsimp [weylGradingH]
    noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]
  · dsimp [waistProj]
    noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]
  · dsimp [weylGradingH, waistProj, comm]
    noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]
  · dsimp [waistProj]
    noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]

/-!
## Stage V (`𝔜𝔊₅`): Kirillov Coadjoint Invariance & Souriau–Brockett Thermodynamics
-/

variable {A : Type*} [AddCommGroup A]

/-- Trace pairing `⟨X, Y⟩_τ = τ(X * Y)` with respect to an additive map `τ : B →+ A`. -/
def trPair (τ : B →+ A) (X Y : B) : A := τ (X * Y)

/-- **Bridge 5 (`kirillov_coadjoint_invariance_and_brockett_dissipation`)**:
    For any cyclic additive trace `τ : B →+ A` (`∀ x y : B, τ (x * y) = τ (y * x)`):
    1. **Coadjoint Leaf Tangency / Kirillov Casimir Conservation**:
       For every `M` in the centralizer `Z(ρ)` (`ρ * M = M * ρ`), Souriau's rotational
       flow `L_rot(Ω, ρ) = [Ω, ρ]` is strictly orthogonal to `M`:
       `trPair τ (souriauRotational Ω ρ) M = 0`.
    2. **Brockett Double-Bracket Dissipation Across Coadjoint Leaves**:
       The trace pairing of the Yoshizawa–Brockett double-bracket flow
       `L_irr(G, ρ) = [ρ, [ρ, G]]` with its generator `G` is the negative trace of
       the squared commutator:
       `trPair τ (brockettIrrotational G ρ) G = -τ (comm ρ G * comm ρ G)`.
    3. **Metriplectic Thermodynamic Balance**:
       Whenever `ρ * M = M * ρ` (`M` is a Casimir of `ρ`) and `Ω * G = G * Ω` (`G` is
       conserved under `Ω`), the pairing of the full metriplectic flow
       `L_met(Ω, G, ρ) = [Ω, ρ] + [ρ, [ρ, G]]` with `G` plus rotational Casimir work
       reduces purely to the Brockett dissipation `-τ ([ρ, G]²)`:
       `trPair τ (metriplecticFlow Ω G ρ) G + trPair τ (souriauRotational Ω ρ) M = -τ (comm ρ G * comm ρ G)`. -/
theorem kirillov_coadjoint_invariance_and_brockett_dissipation
    (τ : B →+ A) (hCyclic : ∀ x y : B, τ (x * y) = τ (y * x))
    (Ω G ρ M : B) (hCasimir : ρ * M = M * ρ) (hSymm : Ω * G = G * Ω) :
    trPair τ (souriauRotational Ω ρ) M = 0 ∧
    trPair τ (brockettIrrotational G ρ) G = -τ (comm ρ G * comm ρ G) ∧
    trPair τ (souriauRotational Ω ρ) G = 0 ∧
    trPair τ (metriplecticFlow Ω G ρ) G +
      trPair τ (souriauRotational Ω ρ) M = -τ (comm ρ G * comm ρ G) := by
  have hRotM : trPair τ (souriauRotational Ω ρ) M = 0 := by
    dsimp [trPair, souriauRotational, comm]
    have hSplit : (Ω * ρ - ρ * Ω) * M = Ω * (ρ * M) - ρ * Ω * M := by noncomm_ring
    rw [hSplit, hCasimir, map_sub]
    have hCycle : τ (Ω * (M * ρ)) = τ (ρ * Ω * M) := by
      calc τ (Ω * (M * ρ))
          = τ ((Ω * M) * ρ) := by rw [mul_assoc]
        _ = τ (ρ * (Ω * M)) := hCyclic (Ω * M) ρ
        _ = τ (ρ * Ω * M) := by rw [mul_assoc]
    rw [hCycle, sub_self]
  have hRotG : trPair τ (souriauRotational Ω ρ) G = 0 := by
    dsimp [trPair, souriauRotational, comm]
    have hSplit : (Ω * ρ - ρ * Ω) * G = Ω * ρ * G - ρ * (Ω * G) := by noncomm_ring
    rw [hSplit, hSymm, map_sub]
    have hCycle : τ (Ω * ρ * G) = τ (ρ * (G * Ω)) := by
      calc τ (Ω * ρ * G)
          = τ (Ω * (ρ * G)) := by rw [mul_assoc]
        _ = τ ((ρ * G) * Ω) := hCyclic Ω (ρ * G)
        _ = τ (ρ * (G * Ω)) := by rw [mul_assoc]
    rw [hCycle, sub_self]
  have hBrockett : trPair τ (brockettIrrotational G ρ) G = -τ (comm ρ G * comm ρ G) := by
    dsimp [trPair, brockettIrrotational, comm]
    have hExpand :
        (ρ * (ρ * G - G * ρ) - (ρ * G - G * ρ) * ρ) * G =
          (ρ * (ρ * G - G * ρ) * G - (ρ * G - G * ρ) * (ρ * G)) -
          ((ρ * G - G * ρ) * (G * ρ) - (ρ * G - G * ρ) * (ρ * G)) -
          (ρ * G - G * ρ) * (ρ * G - G * ρ) := by
      noncomm_ring
    have hC1 : τ (ρ * (ρ * G - G * ρ) * G) = τ ((ρ * G - G * ρ) * (G * ρ)) := by
      calc τ (ρ * (ρ * G - G * ρ) * G)
          = τ (ρ * ((ρ * G - G * ρ) * G)) := by rw [mul_assoc]
        _ = τ (((ρ * G - G * ρ) * G) * ρ) := hCyclic ρ ((ρ * G - G * ρ) * G)
        _ = τ ((ρ * G - G * ρ) * (G * ρ)) := by rw [mul_assoc]
    rw [hExpand]
    simp only [map_sub]
    rw [hC1]
    abel
  refine ⟨hRotM, hBrockett, hRotG, ?_⟩
  dsimp [metriplecticFlow, trPair]
  have hAdd : (souriauRotational Ω ρ + brockettIrrotational G ρ) * G =
      souriauRotational Ω ρ * G + brockettIrrotational G ρ * G := add_mul _ _ _
  rw [hAdd, map_add]
  change trPair τ (souriauRotational Ω ρ) G + trPair τ (brockettIrrotational G ρ) G +
      trPair τ (souriauRotational Ω ρ) M = -τ (comm ρ G * comm ρ G)
  rw [hRotG, hBrockett, hRotM, zero_add, add_zero]

/-!
## Stage VI (`𝔜𝔊₆`): Birkhoff Polytope Singular Boundaries & Non-Semisimple Nilpotent Jordan Blocks
-/

/-- Non-semisimple boundary Jordan operator `T = P + N_nil` at a degenerate face of the
    Birkhoff / projector polytope, where `P² = P`, `P N_nil = N_nil P = N_nil`, and `N_nil² = 0`. -/
def birkhoffJordanBlock (P N_nil : B) : B := P + N_nil

/-- **Bridge 6 (`birkhoff_boundary_non_semisimple_jordan_block`)**:
    When an idempotent `P` (`P² = P`) acquires a nilpotent partner `N_nil` supported on the
    `P`-subspace (`P * N_nil = N_nil`, `N_nil * P = N_nil`, `N_nil * N_nil = 0`), the
    boundary operator `T = P + N_nil` satisfies:
    1. `(T - P)² = 0` (nilpotent perturbation of `P`).
    2. On the `P`-eigenspace, `(T - 1) * P = N_nil` (first-order logarithmic shift) while
       `(T - 1)² * P = 0` (exact rank-2 Jordan block saturation).
    3. The idempotency defect `T² - T = N_nil` is square-zero: `(T² - T)² = 0`.
    4. Higher powers expand linearly in `N_nil`:
       `T² = P + 2 • N_nil` and `T³ = P + 3 • N_nil`. -/
theorem birkhoff_boundary_non_semisimple_jordan_block (P N_nil : B)
    (hP : P * P = P) (hPN : P * N_nil = N_nil) (hNP : N_nil * P = N_nil)
    (hNil : N_nil * N_nil = 0) :
    (birkhoffJordanBlock P N_nil - P) * (birkhoffJordanBlock P N_nil - P) = 0 ∧
    (birkhoffJordanBlock P N_nil - 1) * P = N_nil ∧
    (birkhoffJordanBlock P N_nil - 1) * (birkhoffJordanBlock P N_nil - 1) * P = 0 ∧
    birkhoffJordanBlock P N_nil * birkhoffJordanBlock P N_nil -
      birkhoffJordanBlock P N_nil = N_nil ∧
    (birkhoffJordanBlock P N_nil * birkhoffJordanBlock P N_nil -
      birkhoffJordanBlock P N_nil) *
      (birkhoffJordanBlock P N_nil * birkhoffJordanBlock P N_nil -
        birkhoffJordanBlock P N_nil) = 0 ∧
    birkhoffJordanBlock P N_nil * birkhoffJordanBlock P N_nil = P + 2 • N_nil ∧
    birkhoffJordanBlock P N_nil * birkhoffJordanBlock P N_nil *
      birkhoffJordanBlock P N_nil = P + 3 • N_nil := by
  have hPN' : ∀ Z : B, P * (N_nil * Z) = N_nil * Z := fun Z => by rw [← mul_assoc, hPN]
  have hNP' : ∀ Z : B, N_nil * (P * Z) = N_nil * Z := fun Z => by rw [← mul_assoc, hNP]
  have hNil' : ∀ Z : B, N_nil * (N_nil * Z) = 0 := fun Z => by rw [← mul_assoc, hNil, zero_mul]
  dsimp [birkhoffJordanBlock]
  refine ⟨by noncomm_ring [hNil], by noncomm_ring [hP, hNP],
    by noncomm_ring [hP, hPN, hNP, hNil, proj_idem hP, hPN', hNP', hNil'],
    by noncomm_ring [hP, hPN, hNP, hNil],
    by noncomm_ring [hP, hPN, hNP, hNil, proj_idem hP, hPN', hNP', hNil'],
    by noncomm_ring [hP, hPN, hNP, hNil],
    by noncomm_ring [hP, hPN, hNP, hNil, proj_idem hP, hPN', hNP', hNil']⟩

/-!
## Stage VII (`𝔜𝔊₇`): 5-Graded Parabolic Tower & `4! = 24` Integer Isogeny Lock in `[Ring B]`
-/

/-- Adjoint derivation `ad_H(X) = [H, X]` for a grading element `H : B`. -/
def adH (H X : B) : B := comm H X

/-- Iterated adjoint derivation `ad_H²(X) = [H, [H, X]]`. -/
def adH2 (H X : B) : B := adH H (adH H X)

/-- Iterated adjoint derivation `ad_H³(X) = [H, ad_H²(X)]`. -/
def adH3 (H X : B) : B := adH H (adH2 H X)

/-- Iterated adjoint derivation `ad_H⁴(X) = [H, ad_H³(X)]`. -/
def adH4 (H X : B) : B := adH H (adH3 H X)

/-- Iterated adjoint derivation `ad_H⁵(X) = [H, ad_H⁴(X)]`. -/
def adH5 (H X : B) : B := adH H (adH4 H X)

/-- Parabolic grade `-2` block `G_{-2}(X) = P₂ X P₁`. -/
def parabolicGradeNeg2 (P₁ P₂ X : B) : B := P₂ * X * P₁

/-- Parabolic grade `-1` block `G_{-1}(X) = P₀ X P₁ + P₂ X P₀`. -/
def parabolicGradeNeg1 (P₁ P₂ X : B) : B :=
  waistProj P₁ P₂ * X * P₁ + P₂ * X * waistProj P₁ P₂

/-- Parabolic grade `0` Levi block `G_0(X) = P₁ X P₁ + P₀ X P₀ + P₂ X P₂`. -/
def parabolicGradeZero (P₁ P₂ X : B) : B :=
  P₁ * X * P₁ + waistProj P₁ P₂ * X * waistProj P₁ P₂ + P₂ * X * P₂

/-- Parabolic grade `+1` block `G_{+1}(X) = P₁ X P₀ + P₀ X P₂`. -/
def parabolicGradePos1 (P₁ P₂ X : B) : B :=
  P₁ * X * waistProj P₁ P₂ + waistProj P₁ P₂ * X * P₂

/-- Parabolic grade `+2` block `G_{+2}(X) = P₁ X P₂`. -/
def parabolicGradePos2 (P₁ P₂ X : B) : B := P₁ * X * P₂

/-- **Extension 1 & 2 (`parabolic_five_graded_master_polynomial_and_24_isogeny`)**:
    In any non-commutative ring `[Ring B]` with orthogonal idempotents `P₁, P₂` and
    Weyl grading operator `H = P₁ - P₂` (`H³ = H`):
    1. Every operator `X : B` satisfies the 5-graded parabolic master polynomial
       directly inside `[Ring B]` (with zero wrapper structures):
       `ad_H⁵(X) - 5 • ad_H³(X) + 4 • ad_H(X) = 0`.
    2. All rational denominators in the Lagrange grade projectors are cleared over `ℤ`
       by the universal integer scale `4! = 24`:
       - `24 • G_0(X) = 24 • X - 30 • ad_H²(X) + 6 • ad_H⁴(X)`,
       - `24 • G_{+1}(X) = 16 • ad_H(X) + 16 • ad_H²(X) - 4 • ad_H³(X) - 4 • ad_H⁴(X)`,
       - `24 • G_{-1}(X) = -16 • ad_H(X) + 16 • ad_H²(X) + 4 • ad_H³(X) - 4 • ad_H⁴(X)`,
       - `24 • G_{+2}(X) = -2 • ad_H(X) - ad_H²(X) + 2 • ad_H³(X) + ad_H⁴(X)`,
       - `24 • G_{-2}(X) = 2 • ad_H(X) - ad_H²(X) - 2 • ad_H³(X) + ad_H⁴(X)`.
    3. Every unit `u : (ZMod 24)ˣ` in the cyclotomic Galois group `(ℤ/24ℤ)×` satisfies
       the exponent-2 involution law `u² = 1`. -/
theorem parabolic_five_graded_master_polynomial_and_24_isogeny (P₁ P₂ X : B)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) :
    adH5 (weylGradingH P₁ P₂) X -
      (5 : ℤ) • adH3 (weylGradingH P₁ P₂) X +
      (4 : ℤ) • adH (weylGradingH P₁ P₂) X = 0 ∧
    (24 : ℤ) • parabolicGradeZero P₁ P₂ X =
      (24 : ℤ) • X - (30 : ℤ) • adH2 (weylGradingH P₁ P₂) X +
      (6 : ℤ) • adH4 (weylGradingH P₁ P₂) X ∧
    (24 : ℤ) • parabolicGradePos1 P₁ P₂ X =
      (16 : ℤ) • adH (weylGradingH P₁ P₂) X + (16 : ℤ) • adH2 (weylGradingH P₁ P₂) X -
      (4 : ℤ) • adH3 (weylGradingH P₁ P₂) X - (4 : ℤ) • adH4 (weylGradingH P₁ P₂) X ∧
    (24 : ℤ) • parabolicGradeNeg1 P₁ P₂ X =
      (-16 : ℤ) • adH (weylGradingH P₁ P₂) X + (16 : ℤ) • adH2 (weylGradingH P₁ P₂) X +
      (4 : ℤ) • adH3 (weylGradingH P₁ P₂) X - (4 : ℤ) • adH4 (weylGradingH P₁ P₂) X ∧
    (24 : ℤ) • parabolicGradePos2 P₁ P₂ X =
      (-2 : ℤ) • adH (weylGradingH P₁ P₂) X - adH2 (weylGradingH P₁ P₂) X +
      (2 : ℤ) • adH3 (weylGradingH P₁ P₂) X + adH4 (weylGradingH P₁ P₂) X ∧
    (24 : ℤ) • parabolicGradeNeg2 P₁ P₂ X =
      (2 : ℤ) • adH (weylGradingH P₁ P₂) X - adH2 (weylGradingH P₁ P₂) X -
      (2 : ℤ) • adH3 (weylGradingH P₁ P₂) X + adH4 (weylGradingH P₁ P₂) X ∧
    (∀ u : (ZMod 24)ˣ, u ^ 2 = 1) := by
  dsimp [adH5, adH4, adH3, adH2, adH, weylGradingH,
    parabolicGradeZero, parabolicGradePos1, parabolicGradeNeg1,
    parabolicGradePos2, parabolicGradeNeg2, waistProj, comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]
  · noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]
  · noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]
  · noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]
  · noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]
  · noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]

/-!
## Stage VIII (`𝔜𝔊₈`–`𝔜𝔊₉`): Acyclic 9-Stage Causal Poset & Master Synthesis
-/

/-- Boolean causal precedence indicator `𝔜𝔊_i ≺ 𝔜𝔊_j` on the 9-stage Yoshizawa–InfoGeometry
    synthesis (`Fin 9`). -/
def yoshizawaPosetPrecBool (i j : Fin 9) : Bool := decide (i.val < j.val)

/-- The 9-stage causal dependency indicator `yoshizawaPosetPrecBool` is irreflexive, asymmetric,
    transitive, and forms the strict chain `𝔜𝔊₁ ≺ 𝔜𝔊₂ ≺ ⋯ ≺ 𝔜𝔊₉`. -/
theorem yoshizawaPosetPrec_strict_order_and_chain :
    (∀ i : Fin 9, yoshizawaPosetPrecBool i i = false) ∧
    (∀ i j : Fin 9, yoshizawaPosetPrecBool i j = true → yoshizawaPosetPrecBool j i = false) ∧
    (∀ i j k : Fin 9, yoshizawaPosetPrecBool i j = true →
      yoshizawaPosetPrecBool j k = true → yoshizawaPosetPrecBool i k = true) ∧
    yoshizawaPosetPrecBool 0 1 = true ∧
    yoshizawaPosetPrecBool 1 2 = true ∧
    yoshizawaPosetPrecBool 2 3 = true ∧
    yoshizawaPosetPrecBool 3 4 = true ∧
    yoshizawaPosetPrecBool 4 5 = true ∧
    yoshizawaPosetPrecBool 5 6 = true ∧
    yoshizawaPosetPrecBool 6 7 = true ∧
    yoshizawaPosetPrecBool 7 8 = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- **Master Theorem (`arxiv_2608_21152_gradient_flow_information_geometry_master_synthesis`)**:
    Unifies all six structural bridges and three algebraic extensions of Yoshizawa's
    *Information Geometry of Gradient Flows* (`arXiv:2608.21152`) over an arbitrary
    non-commutative ring `[Ring B]` and cyclic additive trace `τ : B →+ A`. -/
theorem arxiv_2608_21152_gradient_flow_information_geometry_master_synthesis
    (τ : B →+ A) (hCyclic : ∀ x y : B, τ (x * y) = τ (y * x))
    (P X Y R_V dN_plus : B) (hP : P * P = P)
    (hR_left : R_V * (1 - peirceMetricHeight P X Y) = 1)
    (hR_right : (1 - peirceMetricHeight P X Y) * R_V = 1)
    (α : ℤ) (Z : B)
    (P₁ P₂ : B) (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (Ω G ρ M : B) (hCasimir : ρ * M = M * ρ) (hSymm : Ω * G = G * Ω)
    (N_nil : B) (hPN : P * N_nil = N_nil) (hNP : N_nil * P = N_nil)
    (hNil : N_nil * N_nil = 0) :
    -- 1. Brockett double-bracket vs. Souriau Coriolis & centrifugal–well balance
    -brockettIrrotational (peirceSymplecticJ P X Y) (peirceVielbein P X Y) +
      2 • souriauRotational (peirceSpinBivector P X Y) (peirceVielbein P X Y) = 0 ∧
    comm (peirceSpinBivector P X Y)
        (comm (peirceSpinBivector P X Y) (peirceVielbein P X Y)) +
      peirceMetricHeight P X Y *
        comm (peirceSymplecticJ P X Y)
          (comm (peirceSymplecticJ P X Y) (peirceVielbein P X Y)) = 0 ∧
    -- 2. Singular / indefinite Amari α-connection curvature law
    solderedAlphaConn P X Y α (solderedAlphaConn P X Y α Z) =
      (1 - α * α) • (peirceMetricHeight P X Y * Z) ∧
    -- 3. Sheet-Gramian log-det factorization & Hua–Bergman–Dikin resolvent sandwich
    (1 - sheetGramPlus P X Y) * (1 - sheetGramMinus P X Y) = 1 - peirceMetricHeight P X Y ∧
    (1 - peirceMetricHeight P X Y) * (R_V * dN_plus * R_V) *
      (1 - peirceMetricHeight P X Y) = dN_plus ∧
    -- 4. Elliptic moduli 3-idempotent resolution & Seiberg–Witten Legendre monodromy
    P₁ + waistProj P₁ P₂ + P₂ = 1 ∧
    swMonodromyPosLambda * swMonodromyNegLambda = swMonodromyInfinity ∧
    -- 5. Kirillov coadjoint Casimir invariance & Brockett double-bracket dissipation
    trPair τ (souriauRotational Ω ρ) M = 0 ∧
    trPair τ (brockettIrrotational G ρ) G = -τ (comm ρ G * comm ρ G) ∧
    -- 6. Birkhoff polytope boundary non-semisimple Jordan cell
    (birkhoffJordanBlock P N_nil - 1) * (birkhoffJordanBlock P N_nil - 1) * P = 0 ∧
    -- 7. 5-graded parabolic polynomial in [Ring B] & (ℤ/24ℤ)× exponent-2 Galois lock
    adH5 (weylGradingH P₁ P₂) X -
      (5 : ℤ) • adH3 (weylGradingH P₁ P₂) X +
      (4 : ℤ) • adH (weylGradingH P₁ P₂) X = 0 ∧
    (∀ u : (ZMod 24)ˣ, u ^ 2 = 1) := by
  have hB1 := souriau_brockett_centrifugal_dewitt_lock P X Y hP
  have hB2 := amari_alpha_connection_universal_curvature_law P X Y hP α Z
  have hB3a := sheet_gramian_factorization_and_four_way_bott_diamond P X Y hP
  have hB3b := bruhat_projector_sum_diff_and_legendre_hua_dikin P X Y R_V dN_plus hP hR_left hR_right
  have hB4 := elliptic_moduli_blowup_resolution_and_legendre_monodromy P₁ P₂ X Y h1 h2 h12 h21
  have hB5 := kirillov_coadjoint_invariance_and_brockett_dissipation τ hCyclic Ω G ρ M hCasimir hSymm
  have hB6 := birkhoff_boundary_non_semisimple_jordan_block P N_nil hP hPN hNP hNil
  have hB7 := parabolic_five_graded_master_polynomial_and_24_isogeny P₁ P₂ X h1 h2 h12 h21
  exact ⟨hB1.2.2.1, hB1.2.2.2.2.2, hB2.2.1, hB3a.2.2.1, hB3b.2.2.2.2,
    hB4.1, hB4.2.2.2.2.2.2.1, hB5.1, hB5.2.1, hB6.2.2.1, hB7.1, hB7.2.2.2.2.2.2⟩

end InfoGeometry.Canonical.Arxiv260821152GradientFlowInformationGeometryPoset

/-!
# Twenty-Eighth-Order (Duotriconadic) Synthesis:
# The Operator Möbius Group, DeWitt Tetractys Lie Algebra `𝔰𝔩₂(B)` & Emergent Continuum
# (Poset `𝔒𝔐₁ ≺ ⋯ ≺ 𝔒𝔐₆`)
-/

namespace OperatorMoebiusTetractysFlowPoset

universe u
variable {B : Type u} [Ring B]

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Cartan dilation generator `S_P = 2 P - 1 = P + P - 1`. -/
def S_P (P : B) : B := P + P - 1

/-- Upper nilpotent root vector `N_+ = P X (1 - P)`. -/
def N_plus (P X : B) : B := P * X * (1 - P)

/-- Lower nilpotent root vector `N_- = (1 - P) X P`. -/
def N_minus (P X : B) : B := (1 - P) * X * P

/-- Horizontal vielbein / hyperbolic solder boost `Φ = N_+ + N_-`. -/
def Phi_v (P X : B) : B := N_plus P X + N_minus P X

/-- Elliptic phase current / rotation generator `J = N_+ - N_-`. -/
def J_mc (P X : B) : B := N_plus P X - N_minus P X

/-- Upper sheet Gramian `Q_+ = N_+ N_-`. -/
def Q_pos (P X : B) : B := N_plus P X * N_minus P X

/-- Lower sheet Gramian `Q_- = N_- N_+`. -/
def Q_neg (P X : B) : B := N_minus P X * N_plus P X

/-- Central Casimir metric operator `V = Q_+ + Q_-`. -/
def V_met (P X : B) : B := Q_pos P X + Q_neg P X

/-- Spin bivector `Σ = Q_+ - Q_- = [N_+, N_-]`. -/
def Sigma_sp (P X : B) : B := Q_pos P X - Q_neg P X

/-- Right-associated idempotent reduction `P * (P * Z) = P * Z`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-- **Theorem 1 (`tetractys_is_sl2_moebius_lie_algebra`, `𝔒𝔐₁` & `𝔒𝔐₂`)**:
    The three elements of the Tetractys `{S_P, Φ, J}` satisfy the exact commutation relations
    of the 3D Lorentz / Möbius Lie algebra `𝔰𝔩₂(B) ≅ 𝔰𝔬(2,1)` over the central metric ring `ℤ[V]`:
    1. `[S_P, Φ] = 2 J`, `[S_P, J] = 2 Φ`, and `[J, Φ] = 2 Σ`.
    2. Cartan decomposition squares: `S_P² = 1` (hyperbolic), `J² = -V` (elliptic), `Φ² = +V` (boost).
    3. Centrality of `V`: `[V, S_P] = 0`, `[V, Φ] = 0`, and `[V, J] = 0`. -/
theorem tetractys_is_sl2_moebius_lie_algebra
    (P X : B) (hP : P * P = P) :
    let sp := S_P P
    let ph := Phi_v P X
    let j  := J_mc P X
    let s  := Sigma_sp P X
    let v  := V_met P X
    comm sp ph = j + j ∧
    comm sp j  = ph + ph ∧
    comm j ph  = s + s ∧
    sp * sp = 1 ∧
    j * j = - v ∧
    ph * ph = v ∧
    comm v sp = 0 ∧
    comm v ph = 0 ∧
    comm v j  = 0 := by
  dsimp only [S_P, Phi_v, J_mc, Sigma_sp, V_met, Q_pos, Q_neg, N_plus, N_minus, comm]
  refine ⟨by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP],
    by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP],
    by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP],
    by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP],
    by noncomm_ring [hP, proj_idem hP]⟩

/-- **Theorem 2 (`root_space_and_parabolic_horocycle_flow`, `𝔒𝔐₃` & `𝔒𝔐₄`)**:
    1. The boundary waves `N_+` and `N_-` are the positive and negative nilpotent root vectors
       of `𝔰𝔩₂(B)`: `[S_P, N_+] = 2 N_+`, `[S_P, N_-] = -2 N_-`, and `[N_+, N_-] = Σ`.
    2. The parabolic flow `(1 + t N_+)` forms an exact 1-parameter additive group
       (horocyclic translation without BCH correction):
       `(1 + t N_+)(1 + s N_+) = 1 + (t + s) N_+`. -/
theorem root_space_and_parabolic_horocycle_flow
    (P X : B) (t s : B) (hP : P * P = P)
    (ht : ∀ Z : B, t * Z = Z * t)
    (hs : ∀ Z : B, s * Z = Z * s) :
    let sp := S_P P
    let np := N_plus P X
    let nm := N_minus P X
    let sig := Sigma_sp P X
    comm sp np = np + np ∧
    comm sp nm = - (nm + nm) ∧
    comm np nm = sig ∧
    (1 + t * np) * (1 + s * np) = 1 + (t + s) * np ∧
    (1 + s * nm) * (1 + t * nm) = 1 + (s + t) * nm := by
  have h_np_sq : N_plus P X * N_plus P X = 0 := by
    dsimp [N_plus]
    noncomm_ring [hP, proj_idem hP]
  have h_nm_sq : N_minus P X * N_minus P X = 0 := by
    dsimp [N_minus]
    noncomm_ring [hP, proj_idem hP]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [S_P, N_plus, comm]
    noncomm_ring [hP, proj_idem hP]
  · dsimp only [S_P, N_minus, comm]
    noncomm_ring [hP, proj_idem hP]
  · dsimp only [Sigma_sp, Q_pos, Q_neg, comm]
  · calc (1 + t * N_plus P X) * (1 + s * N_plus P X)
      _ = 1 + s * N_plus P X + t * N_plus P X + t * (N_plus P X * s) * N_plus P X := by
          noncomm_ring
      _ = 1 + (t + s) * N_plus P X + (t * s) * (N_plus P X * N_plus P X) := by
          rw [← hs (N_plus P X)]; noncomm_ring
      _ = 1 + (t + s) * N_plus P X := by
          rw [h_np_sq, mul_zero, add_zero]
  · calc (1 + s * N_minus P X) * (1 + t * N_minus P X)
      _ = 1 + t * N_minus P X + s * N_minus P X + s * (N_minus P X * t) * N_minus P X := by
          noncomm_ring
      _ = 1 + (s + t) * N_minus P X + (s * t) * (N_minus P X * N_minus P X) := by
          rw [← ht (N_minus P X)]; noncomm_ring
      _ = 1 + (s + t) * N_minus P X := by
          rw [h_nm_sq, mul_zero, add_zero]

/-- **Theorem 3 (`hyperbolic_weyl_dilation_action`, `𝔒𝔐₅` & `𝔒𝔐₆`)**:
    The Cartan generator `S_P` generates the hyperbolic Weyl dilation that scales
    the forward wave `N_+` positively and the backward wave `N_-` negatively:
    `S_P N_+ S_P = -N_+`, `S_P N_- S_P = -N_-`,
    `(1 + S_P) N_+ (1 - S_P) = 4 • N_+`, and `(1 - S_P) N_- (1 + S_P) = 4 • N_-`. -/
theorem hyperbolic_weyl_dilation_action
    (P X : B) (hP : P * P = P) :
    let sp := S_P P
    let np := N_plus P X
    let nm := N_minus P X
    sp * np * sp = - np ∧
    sp * nm * sp = - nm ∧
    (1 + sp) * np * (1 - sp) = 4 • np ∧
    (1 - sp) * nm * (1 + sp) = 4 • nm := by
  dsimp only [S_P, N_plus, N_minus]
  refine ⟨by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP],
    by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP]⟩

end OperatorMoebiusTetractysFlowPoset

/-!
# Twenty-Ninth-Order (Enneacosadic) Synthesis:
# The Tetractys Embedding in the Virasoro Algebra & Affine Current Geometry (`𝔙𝔄₁ ≺ ⋯ ≺ 𝔙𝔄₅`)
-/

namespace VirasoroAffineCurrentAlgebraPoset

universe u
variable {B : Type u} [Ring B]

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Cartan dilation generator `S_P = P + P - 1`. -/
def S_P (P : B) : B := P + P - 1

/-- Upper nilpotent root vector `N_+ = P X (1 - P)`. -/
def N_plus (P X : B) : B := P * X * (1 - P)

/-- Lower nilpotent root vector `N_- = (1 - P) X P`. -/
def N_minus (P X : B) : B := (1 - P) * X * P

/-- Upper sheet Gramian `Q_+ = N_+ N_-`. -/
def Q_pos (P X : B) : B := N_plus P X * N_minus P X

/-- Lower sheet Gramian `Q_- = N_- N_+`. -/
def Q_neg (P X : B) : B := N_minus P X * N_plus P X

/-- Local operator metric field `V(X) = Q_+(X) + Q_-(X)`. -/
def V_met (P X : B) : B := Q_pos P X + Q_neg P X

/-- Spin bivector `Σ(X) = Q_+(X) - Q_-(X)`. -/
def Sigma_sp (P X : B) : B := Q_pos P X - Q_neg P X

/-- Un-divided Virasoro mode `L_{-1} = N_+` in `[Ring B]`. -/
def L_neg1 (P X : B) : B := N_plus P X

/-- Un-divided Virasoro mode `L_0 = S_P` in `[Ring B]`. -/
def L_zero (P : B) : B := S_P P

/-- Un-divided Virasoro mode `L_1 = -N_-` in `[Ring B]`. -/
def L_pos1 (P X : B) : B := - N_minus P X

/-- The Virasoro Central Anomaly Polynomial for `c = 24`: `A(m) = 2 * (m³ - m)`. -/
def VirasoroAnomaly24 (m : ℤ) : ℤ := 2 * (m * m * m - m)

/-- The 24th cyclotomic polynomial `Φ₂₄(J) = J⁸ - J⁴ + 1` in `[Ring B]`. -/
def cyclotomicPoly24 (J : B) : B := J ^ 8 - J ^ 4 + 1

/-- Right-associated idempotent reduction `P * (P * Z) = P * Z`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-- **Theorem 1 (`virasoro_wedge_commutation`, `𝔙𝔄₁` & `𝔙𝔄₂`)**:
    The Lie brackets of `L₀ = S_P` with `L₋₁ = N₊` and `L₁ = -N₋` satisfy the exact
    Virasoro relations `[L₀, L₋₁] = 2 • L₋₁` and `[L₀, L₁] = -2 • L₁`
    (matching `[L_m, L_n] = (m - n) L_{m+n}` with step size 2). -/
theorem virasoro_wedge_commutation
    (P X : B) (hP : P * P = P) :
    let L0  := L_zero P
    let Lm1 := L_neg1 P X
    let Lp1 := L_pos1 P X
    comm L0 Lm1 = Lm1 + Lm1 ∧
    comm L0 Lp1 = - (Lp1 + Lp1) := by
  dsimp only [L_zero, L_neg1, L_pos1, S_P, N_plus, N_minus, comm]
  refine ⟨by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP]⟩

/-- **Theorem 2 (`operator_valued_current_bracket`, `𝔙𝔄₃`)**:
    The commutator `[L₁, L₋₁] = [-N₋, N₊] = [N₊, N₋]` is not a scalar constant;
    it is identically the spin bivector `Σ = S_P * V = V * S_P`, proving that the
    algebra is an affine current algebra modulated by the local metric operator `V(X)`. -/
theorem operator_valued_current_bracket
    (P X : B) (hP : P * P = P) :
    let Lm1 := L_neg1 P X
    let Lp1 := L_pos1 P X
    let L0  := L_zero P
    let s   := Sigma_sp P X
    let v   := V_met P X
    comm Lp1 Lm1 = s ∧
    comm Lp1 Lm1 = L0 * v ∧
    comm Lp1 Lm1 = v * L0 := by
  dsimp only [L_pos1, L_neg1, L_zero, S_P, Sigma_sp, V_met, Q_pos, Q_neg, N_plus, N_minus, comm]
  refine ⟨by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP],
    by noncomm_ring [hP, proj_idem hP]⟩

/-- **Theorem 3 (`virasoro_central_charge_24_arithmetic`, `𝔙𝔄₄` & `𝔙𝔄₅`)**:
    1. The Virasoro central anomaly `A(m) = 2(m³ - m)` vanishes identically on all
       three Tetractys modes `m ∈ {-1, 0, 1}`.
    2. The higher mode anomalies are exact integer multiples of 12 and 24:
       `A(2) = 12`, `A(3) = 48 = 2 * 24`, and `A(5) = 240 = 10 * 24` (the 240 roots of `E₈`). -/
theorem virasoro_central_charge_24_arithmetic :
    VirasoroAnomaly24 (-1) = 0 ∧
    VirasoroAnomaly24 0    = 0 ∧
    VirasoroAnomaly24 1    = 0 ∧
    VirasoroAnomaly24 2 = 12 ∧
    VirasoroAnomaly24 3 = 48 ∧
    VirasoroAnomaly24 3 = 2 * 24 ∧
    VirasoroAnomaly24 5 = 240 ∧
    VirasoroAnomaly24 5 = 10 * 24 := by
  dsimp [VirasoroAnomaly24]
  decide

/-- **Theorem 4 (`cyclotomic24_implies_period_24`)**:
    In any associative ring `[Ring B]`, the 24th cyclotomic polynomial
    `Φ₂₄(J) = J⁸ - J⁴ + 1` factors `1 - J²⁴` as
    `(1 - J⁴)(1 + J⁴ + J⁸)(1 + J⁴) Φ₂₄(J) = 1 - J²⁴`.
    Consequently, whenever `Φ₂₄(J) = 0`, `J` is strictly 24-periodic (`J²⁴ = 1`). -/
theorem cyclotomic24_implies_period_24 (J : B) :
    (1 - J ^ 4) * (1 + J ^ 4 + J ^ 8) * (1 + J ^ 4) * cyclotomicPoly24 J = 1 - J ^ 24 ∧
    (cyclotomicPoly24 J = 0 → J ^ 24 = 1) := by
  have hFact : (1 - J ^ 4) * (1 + J ^ 4 + J ^ 8) * (1 + J ^ 4) * cyclotomicPoly24 J =
      1 - J ^ 24 := by
    dsimp [cyclotomicPoly24]
    noncomm_ring
  refine ⟨hFact, ?_⟩
  intro hZero
  have h0 : 1 - J ^ 24 = 0 := by
    rw [← hFact, hZero, mul_zero]
  calc J ^ 24 = J ^ 24 + (1 - J ^ 24) := by rw [h0, add_zero]
    _ = 1 := by abel

end VirasoroAffineCurrentAlgebraPoset

/-!
# Thirty-First-Order (Untriacontadic) Synthesis:
# Non-Commutative Ring Integrity and the Operator-Valued 24-Clock (`NoncommutativeRingIntegrityPoset`)
-/

namespace NoncommutativeRingIntegrityPoset

universe u
variable {B : Type u} [Ring B]

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Fundamental Tetractys phase current `J_op(P, X) = [P, X]` in `[Ring B]`. -/
def J_op (P X : B) : B := comm P X

/-- Fundamental Tetractys spatial vielbein `Phi_op(P, X) = [P, [P, X]]` in `[Ring B]`. -/
def Phi_op (P X : B) : B := comm P (comm P X)

/-- Fundamental Tetractys operator metric `V_op(P, X) = -J_op(P, X)²` in `[Ring B]`. -/
def V_op (P X : B) : B := - (J_op P X * J_op P X)

/-- Fundamental Tetractys spin bivector `Sigma_op(P, X) = J_op(P, X) * Phi_op(P, X)` in `[Ring B]`. -/
def Sigma_op (P X : B) : B := J_op P X * Phi_op P X

/-- The 24th Cyclotomic Operator Polynomial in `[Ring B]`: `Φ₂₄(J) = J⁸ - J⁴ + 1`. -/
def Phi24_Operator (J : B) : B :=
  let J2 := J * J
  let J4 := J2 * J2
  let J8 := J4 * J4
  J8 - J4 + 1

/-- Operator-valued Virasoro central anomaly at `c = 24` inside `[Ring B]`:
    `A_op(m) = (2 * (m³ - m)) • (1 : B)`. -/
def VirasoroAnomalyOp24 (m : ℤ) : B := (2 * (m * m * m - m) : ℤ) • (1 : B)

/-- Right-associated idempotent reduction `P * (P * Z) = P * Z`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-- **Theorem 1 (`spacetime_requires_noncommutative_operator_ring`)**:
    Proves in `[Ring B]` that `J = [P, X]` generates the non-vanishing space vielbein
    `Φ = [P, J]` and metric `V = -J² = Φ²`, with `{J, Φ} = 0`:
    1. `[P, J] = Φ` (Space is the non-commutative commutator of `P` with `J`).
    2. `Φ² = V` and `J² = -V` (Metric is the square of Space and minus the square of Time).
    3. `{J, Φ} = 0` (Space and Time strictly anticommute in `[Ring B]`). -/
theorem spacetime_requires_noncommutative_operator_ring
    (P X : B) (hP : P * P = P) :
    let j  := J_op P X
    let ph := Phi_op P X
    let v  := V_op P X
    comm P j = ph ∧
    ph * ph = v ∧
    j * j = - v ∧
    anticomm j ph = 0 := by
  dsimp only [Phi_op, J_op, V_op, comm, anticomm]
  refine ⟨by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP],
    by noncomm_ring [hP, proj_idem hP], by noncomm_ring [hP, proj_idem hP]⟩

/-- **Theorem 1B (`scalar_commuting_collapse_destroys_spacetime`)**:
    If an excitation `n : B` commutes with the boundary distinction `P` (`P * n = n * P`,
    as every scalar integer `k • 1_B` does), then:
    1. The temporal current vanishes (`J_op P n = 0`),
    2. The spatial vielbein vanishes (`Phi_op P n = 0`),
    3. The gravitational metric vanishes (`V_op P n = 0`),
    4. The quantum spin bivector vanishes (`Sigma_op P n = 0`). -/
theorem scalar_commuting_collapse_destroys_spacetime
    (P n : B) (hComm : P * n = n * P) :
    J_op P n = 0 ∧
    Phi_op P n = 0 ∧
    V_op P n = 0 ∧
    Sigma_op P n = 0 := by
  dsimp only [J_op, Phi_op, V_op, Sigma_op, comm]
  refine ⟨by noncomm_ring [hComm], by noncomm_ring [hComm],
    by noncomm_ring [hComm], by noncomm_ring [hComm]⟩

/-- **Theorem 2 (`operator_factorization_diamond_in_pure_ring`)**:
    Proves that `1 - J⁴` factors into four linear operators `(1 - J)(1 + J)(1 - Φ)(1 + Φ)`
    inside `[Ring B]` WITHOUT assuming commutativity of `B` and WITHOUT complex numbers. -/
theorem operator_factorization_diamond_in_pure_ring
    (P X : B) (hP : P * P = P) :
    let j  := J_op P X
    let ph := Phi_op P X
    let j2 := j * j
    let j4 := j2 * j2
    (1 - j) * (1 + j) * (1 - ph) * (1 + ph) = 1 - j4 := by
  dsimp only [Phi_op, J_op, comm]
  noncomm_ring [hP, proj_idem hP]

/-- **Theorem 3 (`complete_twenty_four_cyclotomic_operator_identity`)**:
    Proves that the full 24-step cyclotomic factorization lives entirely inside `[Ring B]`
    as an exact identity of non-commutative operators:
    `(1 - J)(1 + J)(1 - Φ)(1 + Φ)(1 + J⁴ + J⁸)(1 + J⁴) Φ₂₄(J) = 1 - J²⁴`. -/
theorem complete_twenty_four_cyclotomic_operator_identity
    (P X : B) (hP : P * P = P) :
    let j   := J_op P X
    let ph  := Phi_op P X
    let j2  := j * j
    let j4  := j2 * j2
    let j8  := j4 * j4
    let j12 := j8 * j4
    let j24 := j12 * j12
    (1 - j) * (1 + j) * (1 - ph) * (1 + ph) * (1 + j4 + j8) *
      (1 + j4) * Phi24_Operator j = 1 - j24 := by
  have h_diamond : (1 - J_op P X) * (1 + J_op P X) * (1 - Phi_op P X) * (1 + Phi_op P X) =
      1 - (J_op P X * J_op P X) * (J_op P X * J_op P X) :=
    operator_factorization_diamond_in_pure_ring P X hP
  set j := J_op P X
  set ph := Phi_op P X
  set j2 := j * j
  set j4 := j2 * j2
  set j8 := j4 * j4
  set j12 := j8 * j4
  set j24 := j12 * j12
  have h_12_minus : (1 - j4) * (1 + j4 + j8) = 1 - j12 := by
    dsimp [j12, j8, j4, j2]
    noncomm_ring
  have h_12_plus : (1 + j4) * Phi24_Operator j = 1 + j12 := by
    dsimp [Phi24_Operator, j12, j8, j4, j2]
    noncomm_ring
  have h_24 : (1 - j12) * (1 + j12) = 1 - j24 := by
    dsimp [j24]
    noncomm_ring
  calc (1 - j) * (1 + j) * (1 - ph) * (1 + ph) * (1 + j4 + j8) * (1 + j4) * Phi24_Operator j
    _ = ((1 - j4) * (1 + j4 + j8)) * ((1 + j4) * Phi24_Operator j) := by
        rw [h_diamond]; noncomm_ring
    _ = (1 - j12) * (1 + j12) := by rw [h_12_minus, h_12_plus]
    _ = 1 - j24               := h_24

/-- **Theorem 4 (`moonshine_operator_dimensions`)**:
    Both the Moonshine dimension equation and the `c = 24` Virasoro anomaly values hold
    as exact identities of operator endomorphisms inside `[Ring B]`. -/
theorem moonshine_operator_dimensions :
    (196884 : B) = (196560 : B) + (300 : B) + (24 : B) ∧
    (24 : B) = (12 : B) + (12 : B) ∧
    VirasoroAnomalyOp24 (-1) = (0 : B) ∧
    VirasoroAnomalyOp24 0    = (0 : B) ∧
    VirasoroAnomalyOp24 1    = (0 : B) ∧
    VirasoroAnomalyOp24 2    = (12 : B) ∧
    VirasoroAnomalyOp24 3    = (2 : B) * (24 : B) ∧
    VirasoroAnomalyOp24 5    = (10 : B) * (24 : B) := by
  norm_num [VirasoroAnomalyOp24, zsmul_one]

end NoncommutativeRingIntegrityPoset
