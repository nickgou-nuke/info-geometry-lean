/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixUnitAnomalyRealization
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge

/-!
# Non-Commutative Souriau Moment Maps, 3×3 Kaluza–Janus Extensions & Bimetric Operator Systems (`solve et coagula`)

This module formalizes the pure mathematical archetypes underlying non-commutative block-matrix
semidirect extensions, Souriau coadjoint moment maps, Souriau–Noether trace pairings, and
Krein-graded bimetric operator systems over an arbitrary non-commutative associative ring `B`
(`[Ring B]` and `[StarRing B]`), expressed natively on `Matrix (Fin 2) (Fin 2) B` and
`Matrix (Fin 3) (Fin 3) B` with zero commutative or scalar-toy reductions.

## Acyclic Causal Poset (`JanusBimetricEpistemicStage`)

1. **`J0_PrimordialBinaryCutAndSouriauMomentCongruence`** ($\mathcal{J}_0$):
   The $2 \times 2$ upper-triangular affine semidirect group `affGroup2 L C = !![L, C; 0, 1]`,
   its two-sided formal inverse `affInv2 L_inv C = !![L_inv, -(L_inv * C); 0, 1]`, and the
   non-commutative Souriau moment torsor matrix `momentTorsor2 M P = !![M, -P; star P, 0]`,
   whose star-congruence `G * Y * Gᴴ` produces the exact non-commutative coadjoint moment shifts
   `M' = L * M * star L - L * P * star C + C * star (L * P)` and `P' = L * P`.

2. **`J1_FourfoldAnatomyAndKaluzaJanusDoubleSemidirectAdjoint`** ($\mathcal{J}_1$):
   The $3 \times 3$ Kaluza–Janus upper-triangular double semidirect extension
   `janusGroup3 χ φ L C = !![χ, 0, φ; 0, L, C; 0, 0, 1]` and its strictly upper-triangular Lie
   algebra `janusLie3 Ω γ δφ = !![0, 0, δφ; 0, Ω, γ; 0, 0, 0]`, together with the exact
   non-commutative adjoint action `G⁻¹ * Z * G = janusLie3 (L_inv * Ω * L) (L_inv * Ω * C + L_inv * γ) (χ_inv * δφ)`,
   commutator closure, and 2-step nilpotency of the translation/gauge radical `janusLie3 0 γ δφ`.

3. **`J2_TranscendentFunctionAndSouriauNoetherTraceDuality`** ($\mathcal{J}_2$):
   The lower-triangular dual moment torsor matrix `janusDualMoment3 M P q = !![0, 0, 0; 0, M, 0; q, P, 0]`,
   whose native `Matrix.trace` pairing with `janusLie3 Ω γ δφ` yields the Souriau–Noether bilinear
   form `M * Ω + P * γ + q * δφ`, together with multiplicative conjugation equivariance, explicit
   coadjoint block transformations (`q' = q * χ`, `P' = P * L`, `M' = L_inv * M * L - L_inv * C * P * L`),
   and the exact non-commutative commutator defect `P * comm Ω C` under translation `C`.

4. **`J3_SocraticAporiaBimetricCouplingNilpotencyAndConservation`** ($\mathcal{J}_3$):
   The $2 \times 2$ Krein-graded bimetric coupling operator
   `bimetricCoupling2 b₁ b₂ = !![1, b₁; -b₂, -1]`, its Socratic aporia / square defect
   `bimetricCoupling2 b₁ b₂ ^ 2 = !![1 - b₁ * b₂, 0; 0, 1 - b₂ * b₁]` (which vanishes identically
   under mutual inverse duality `b₁ * b₂ = 1` and `b₂ * b₁ = 1`), the full $2 \times 2$ matrix
   Bianchi conservation annihilator `bimetricAnnihilator2 b₂ * (bimetricCoupling2 b₁ b₂ * T)`, and
   the non-diagonal $2 \times 2$ block stress-energy transformations under `cartanEz2`.

5. **`J4_PeirceKreinKKTZornTwistorBridge`** ($\mathcal{J}_4$):
   Exact non-commutative structural bridges connecting `cartanEz2` and `bimetricCoupling2` to the
   Peirce Spine (`peirceProj2`, `P Nplus`, `invS`, `conePlus`, `coneMinus`), connecting `janusLie3`
   and `janusDualMoment3` to the 5-graded Peirce–Kantor–Koecher–Tits (`Nplus3`) and operator-Zorn
   (`matrix3ToOpZorn`) gradings, establishing unconditional non-commutative Krein modulus, Nambu
   3-bracket, Kantor grade-`±2` sandwich, Socratic aporia, and chiral $\gamma_5$ anomaly identities,
   and proving explicit `Trap T16` non-commutativity witnesses over `[Nontrivial B]`.

6. **`J5_MasterSouriauKaluzaJanusBimetricCoagulation`** ($\mathcal{J}_5$):
   Coagulates the acyclic causal poset $\mathcal{J}_0 \prec \mathcal{J}_1 \prec \mathcal{J}_2 \prec \mathcal{J}_3 \prec \mathcal{J}_4 \prec \mathcal{J}_5$
   into a single self-verifying master theorem.
-/

namespace InfoGeometry.Canonical.SouriauKaluzaJanusBimetricSolveEtCoagula

open Matrix
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixUnitAnomalyRealization
open InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization
open InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge

/-! ===========================================================================
    Section 0: Acyclic Causal Poset (`JanusBimetricEpistemicStage`)
    =========================================================================== -/

/-- The 6-stage `solve et coagula` acyclic causal poset for non-commutative Souriau moment maps,
$3 \times 3$ Kaluza–Janus extensions, and Krein-graded bimetric operator systems. -/
inductive JanusBimetricEpistemicStage : Type
  | J0_PrimordialBinaryCutAndSouriauMomentCongruence
  | J1_FourfoldAnatomyAndKaluzaJanusDoubleSemidirectAdjoint
  | J2_TranscendentFunctionAndSouriauNoetherTraceDuality
  | J3_SocraticAporiaBimetricCouplingNilpotencyAndConservation
  | J4_PeirceKreinKKTZornTwistorBridge
  | J5_MasterSouriauKaluzaJanusBimetricCoagulation
  deriving DecidableEq, Repr, Inhabited

namespace JanusBimetricEpistemicStage

/-- Numerical topological depth of each stage in `JanusBimetricEpistemicStage`. -/
def rank : JanusBimetricEpistemicStage → ℕ
  | .J0_PrimordialBinaryCutAndSouriauMomentCongruence => 0
  | .J1_FourfoldAnatomyAndKaluzaJanusDoubleSemidirectAdjoint => 1
  | .J2_TranscendentFunctionAndSouriauNoetherTraceDuality => 2
  | .J3_SocraticAporiaBimetricCouplingNilpotencyAndConservation => 3
  | .J4_PeirceKreinKKTZornTwistorBridge => 4
  | .J5_MasterSouriauKaluzaJanusBimetricCoagulation => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance instLinearOrderJanusBimetricEpistemicStage : LinearOrder JanusBimetricEpistemicStage :=
  LinearOrder.lift' rank rank_injective

/-- Direct cover relation $\mathcal{J}_k \prec \mathcal{J}_{k+1}$ in the epistemic poset. -/
def causalEdge (x y : JanusBimetricEpistemicStage) : Prop :=
  rank y = rank x + 1

theorem causalEdge_strict_rank {x y : JanusBimetricEpistemicStage} (h : causalEdge x y) :
    rank x < rank y := by
  dsimp [causalEdge] at h
  omega

theorem transGen_strict_rank {x y : JanusBimetricEpistemicStage}
    (h : Relation.TransGen causalEdge x y) :
    rank x < rank y := by
  induction h with
  | single hxy => exact causalEdge_strict_rank hxy
  | tail _ hyz ih =>
      have hyz' := causalEdge_strict_rank hyz
      omega

/-- Strict acyclicity of the 6-stage `JanusBimetricEpistemicStage` causal poset. -/
theorem causalEdge_acyclic (x : JanusBimetricEpistemicStage) :
    ¬ Relation.TransGen causalEdge x x := by
  intro h
  have hlt := transGen_strict_rank h
  exact Nat.lt_irrefl (rank x) hlt

/-- The complete cover chain $\mathcal{J}_0 \prec \mathcal{J}_1 \prec \mathcal{J}_2 \prec \mathcal{J}_3 \prec \mathcal{J}_4 \prec \mathcal{J}_5$. -/
theorem causalEdge_chain :
    causalEdge .J0_PrimordialBinaryCutAndSouriauMomentCongruence
      .J1_FourfoldAnatomyAndKaluzaJanusDoubleSemidirectAdjoint ∧
    causalEdge .J1_FourfoldAnatomyAndKaluzaJanusDoubleSemidirectAdjoint
      .J2_TranscendentFunctionAndSouriauNoetherTraceDuality ∧
    causalEdge .J2_TranscendentFunctionAndSouriauNoetherTraceDuality
      .J3_SocraticAporiaBimetricCouplingNilpotencyAndConservation ∧
    causalEdge .J3_SocraticAporiaBimetricCouplingNilpotencyAndConservation
      .J4_PeirceKreinKKTZornTwistorBridge ∧
    causalEdge .J4_PeirceKreinKKTZornTwistorBridge
      .J5_MasterSouriauKaluzaJanusBimetricCoagulation := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

end JanusBimetricEpistemicStage

/-! ===========================================================================
    Section 1: Archetype J0 — 2×2 Affine Semidirect Group & Souriau Moment Congruence
    =========================================================================== -/

section ArchetypeJ0

variable {B : Type*} [Ring B]

/-- The $2 \times 2$ upper-triangular affine semidirect group element
$\begin{pmatrix} L & C \\ 0 & 1 \end{pmatrix} \in M_2(B)$. -/
def affGroup2 (L C : B) : Matrix (Fin 2) (Fin 2) B :=
  !![L, C; 0, 1]

/-- The $2 \times 2$ upper-triangular formal inverse
$\begin{pmatrix} L_{\mathrm{inv}} & -L_{\mathrm{inv}} C \\ 0 & 1 \end{pmatrix} \in M_2(B)$. -/
def affInv2 (L_inv C : B) : Matrix (Fin 2) (Fin 2) B :=
  !![L_inv, -(L_inv * C); 0, 1]

/-- Identity law for `affGroup2`: `affGroup2 1 0 = 1`. -/
theorem affGroup2_one : affGroup2 (1 : B) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Semidirect product law for $2 \times 2$ upper-triangular matrices:
`affGroup2 L₁ C₁ * affGroup2 L₂ C₂ = affGroup2 (L₁ * L₂) (L₁ * C₂ + C₁)`. -/
theorem affGroup2_mul (L₁ C₁ L₂ C₂ : B) :
    affGroup2 L₁ C₁ * affGroup2 L₂ C₂ = affGroup2 (L₁ * L₂) (L₁ * C₂ + C₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affGroup2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact left inverse law for `affGroup2` whenever `L_inv * L = 1`. -/
theorem affInv2_mul_affGroup2 {L L_inv : B} (C : B) (hL : L_inv * L = 1) :
    affInv2 L_inv C * affGroup2 L C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affGroup2, affInv2, Matrix.mul_apply, Fin.sum_univ_two]
  exact hL

/-- Exact right inverse law for `affGroup2` whenever `L * L_inv = 1`. -/
theorem affGroup2_mul_affInv2 {L L_inv : B} (C : B) (hL : L * L_inv = 1) :
    affGroup2 L C * affInv2 L_inv C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affGroup2, affInv2, Matrix.mul_apply, Fin.sum_univ_two]
  · exact hL
  · calc
      -(L * (L_inv * C)) + C = -((L * L_inv) * C) + C := by noncomm_ring
      _ = -(1 * C) + C := by rw [hL]
      _ = 0 := by noncomm_ring

variable [StarRing B]

/-- The $2 \times 2$ Souriau moment torsor matrix
$\begin{pmatrix} M & -P \\ P^\star & 0 \end{pmatrix} \in M_2(B)$. -/
def momentTorsor2 (M P : B) : Matrix (Fin 2) (Fin 2) B :=
  !![M, -P; star P, 0]

/-- **Souriau Moment Torsor Congruence**:
Conjugating `momentTorsor2 M P` by `affGroup2 L C` via the native Hermitian transpose
`(affGroup2 L C)ᴴ` yields the exact non-commutative Souriau coadjoint transformation
`M' = L * M * star L - L * P * star C + C * star (L * P)` and `P' = L * P`. -/
theorem momentTorsor2_coadjoint_congruence (L C M P : B) :
    affGroup2 L C * momentTorsor2 M P * (affGroup2 L C)ᴴ =
      momentTorsor2 (L * M * star L - L * P * star C + C * star (L * P)) (L * P) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [affGroup2, momentTorsor2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, star_mul]; try noncomm_ring)

/-- **Pure Translation Moment Shift (`L = 1`)**:
Under a pure translation `affGroup2 1 C`, the momentum entry `P` is invariant while the angular
moment `M` shifts by the non-commutative cross-product `-P * star C + C * star P`. -/
theorem momentTorsor2_pure_translation (C M P : B) :
    affGroup2 1 C * momentTorsor2 M P * (affGroup2 1 C)ᴴ =
      momentTorsor2 (M - P * star C + C * star P) P := by
  simpa [one_mul, mul_one, star_one] using momentTorsor2_coadjoint_congruence (1 : B) C M P

/-- **Discrete Inversion Moment Reversal (`L = -1, C = 0`)**:
Conjugating `momentTorsor2 M P` by the discrete inversion `affGroup2 (-1) 0` preserves `M` and
reverses the sign of the translational momentum `P ↦ -P`. -/
theorem momentTorsor2_discrete_inversion (M P : B) :
    affGroup2 (-1 : B) 0 * momentTorsor2 M P * (affGroup2 (-1 : B) 0)ᴴ =
      momentTorsor2 M (-P) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affGroup2, momentTorsor2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two]

/-- **Archetype $\mathcal{J}_0$ Package**:
Coagulates the $2 \times 2$ semidirect group law, two-sided inverse identities, Souriau coadjoint
congruence, pure translation shift, and discrete inversion reversal. -/
theorem archetype_J0_souriau_poincare_moment_torsor_congruence
    {L L_inv : B} (L₁ C₁ L₂ C₂ C M P : B)
    (hL_left : L_inv * L = 1) (hL_right : L * L_inv = 1) :
    affGroup2 L₁ C₁ * affGroup2 L₂ C₂ = affGroup2 (L₁ * L₂) (L₁ * C₂ + C₁) ∧
    affInv2 L_inv C * affGroup2 L C = 1 ∧
    affGroup2 L C * affInv2 L_inv C = 1 ∧
    affGroup2 L C * momentTorsor2 M P * (affGroup2 L C)ᴴ =
      momentTorsor2 (L * M * star L - L * P * star C + C * star (L * P)) (L * P) ∧
    affGroup2 1 C * momentTorsor2 M P * (affGroup2 1 C)ᴴ =
      momentTorsor2 (M - P * star C + C * star P) P ∧
    affGroup2 (-1 : B) 0 * momentTorsor2 M P * (affGroup2 (-1 : B) 0)ᴴ =
      momentTorsor2 M (-P) :=
  ⟨affGroup2_mul L₁ C₁ L₂ C₂,
   affInv2_mul_affGroup2 C hL_left,
   affGroup2_mul_affInv2 C hL_right,
   momentTorsor2_coadjoint_congruence L C M P,
   momentTorsor2_pure_translation C M P,
   momentTorsor2_discrete_inversion M P⟩

end ArchetypeJ0

/-! ===========================================================================
    Section 2: Archetype J1 — 3×3 Kaluza–Janus Double Semidirect Group & Adjoint Action
    =========================================================================== -/

section ArchetypeJ1

variable {B : Type*} [Ring B]

/-- The $3 \times 3$ Kaluza–Janus upper-triangular double semidirect group matrix
$\begin{pmatrix} \chi & 0 & \phi \\ 0 & L & C \\ 0 & 0 & 1 \end{pmatrix} \in M_3(B)$. -/
def janusGroup3 (χ φ L C : B) : Matrix (Fin 3) (Fin 3) B :=
  !![χ, 0, φ; 0, L, C; 0, 0, 1]

/-- The $3 \times 3$ Kaluza–Janus formal inverse matrix
$\begin{pmatrix} \chi_{\mathrm{inv}} & 0 & -\chi_{\mathrm{inv}}\phi \\ 0 & L_{\mathrm{inv}} & -L_{\mathrm{inv}} C \\ 0 & 0 & 1 \end{pmatrix} \in M_3(B)$. -/
def janusInv3 (χ_inv φ L_inv C : B) : Matrix (Fin 3) (Fin 3) B :=
  !![χ_inv, 0, -(χ_inv * φ); 0, L_inv, -(L_inv * C); 0, 0, 1]

/-- The $3 \times 3$ Kaluza–Janus Lie algebra matrix
$\begin{pmatrix} 0 & 0 & \delta\phi \\ 0 & \Omega & \gamma \\ 0 & 0 & 0 \end{pmatrix} \in M_3(B)$. -/
def janusLie3 (Ω γ δφ : B) : Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, δφ; 0, Ω, γ; 0, 0, 0]

/-- Identity law for `janusGroup3`: `janusGroup3 1 0 1 0 = 1`. -/
theorem janusGroup3_one : janusGroup3 (1 : B) 0 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Double semidirect product law for `janusGroup3`. -/
theorem janusGroup3_mul (χ₁ φ₁ L₁ C₁ χ₂ φ₂ L₂ C₂ : B) :
    janusGroup3 χ₁ φ₁ L₁ C₁ * janusGroup3 χ₂ φ₂ L₂ C₂ =
      janusGroup3 (χ₁ * χ₂) (χ₁ * φ₂ + φ₁) (L₁ * L₂) (L₁ * C₂ + C₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusGroup3, Matrix.mul_apply, Fin.sum_univ_three]

/-- Exact left inverse identity for `janusGroup3` whenever `χ_inv * χ = 1` and `L_inv * L = 1`. -/
theorem janusInv3_mul_janusGroup3 {χ χ_inv L L_inv : B} (φ C : B)
    (hχ : χ_inv * χ = 1) (hL : L_inv * L = 1) :
    janusInv3 χ_inv φ L_inv C * janusGroup3 χ φ L C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_three]
  · exact hχ
  · exact hL

/-- Exact right inverse identity for `janusGroup3` whenever `χ * χ_inv = 1` and `L * L_inv = 1`. -/
theorem janusGroup3_mul_janusInv3 {χ χ_inv L L_inv : B} (φ C : B)
    (hχ : χ * χ_inv = 1) (hL : L * L_inv = 1) :
    janusGroup3 χ φ L C * janusInv3 χ_inv φ L_inv C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_three]
  · exact hχ
  · calc
      -(χ * (χ_inv * φ)) + φ = -((χ * χ_inv) * φ) + φ := by noncomm_ring
      _ = -(1 * φ) + φ := by rw [hχ]
      _ = 0 := by noncomm_ring
  · exact hL
  · calc
      -(L * (L_inv * C)) + C = -((L * L_inv) * C) + C := by noncomm_ring
      _ = -(1 * C) + C := by rw [hL]
      _ = 0 := by noncomm_ring

/-- **Adjoint Action on the Kaluza–Janus Lie Algebra**:
Conjugating `janusLie3 Ω γ δφ` by `janusGroup3 χ φ L C` acts by `Ω ↦ L_inv * Ω * L`,
`γ ↦ L_inv * Ω * C + L_inv * γ`, and `δφ ↦ χ_inv * δφ`, completely independent of the
fifth-coordinate gauge translation `φ`. -/
theorem janusLie3_adjoint_action (χ χ_inv φ L L_inv C Ω γ δφ : B) :
    janusInv3 χ_inv φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 χ φ L C =
      janusLie3 (L_inv * Ω * L) (L_inv * Ω * C + L_inv * γ) (χ_inv * δφ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusGroup3, janusInv3, janusLie3, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Lie Bracket Closure of `janusLie3`**:
The commutator of two Kaluza–Janus Lie algebra matrices closes in `janusLie3` with
`[Ω₁, Ω₂]` in the `(1,1)` slot, `Ω₁ * γ₂ - Ω₂ * γ₁` in the `(1,2)` slot, and `0` in the `(0,2)`
gauge-translation slot (demonstrating that the fifth-coordinate generator `δφ` is central in
`janusLie3`). -/
theorem janusLie3_commutator (Ω₁ γ₁ δφ₁ Ω₂ γ₂ δφ₂ : B) :
    OperatorAlgebra.PeirceSpine.comm (janusLie3 Ω₁ γ₁ δφ₁) (janusLie3 Ω₂ γ₂ δφ₂) =
      janusLie3 (OperatorAlgebra.PeirceSpine.comm Ω₁ Ω₂) (Ω₁ * γ₂ - Ω₂ * γ₁) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OperatorAlgebra.PeirceSpine.comm, janusLie3]

/-- **Two-Step Nilpotency of the Translation/Gauge Radical**:
When the homogeneous generator vanishes (`Ω = 0`), the strictly upper-triangular translation/gauge
generator `janusLie3 0 γ δφ` squares to zero. -/
theorem janusLie3_radical_sq_zero (γ δφ : B) :
    janusLie3 0 γ δφ * janusLie3 0 γ δφ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusLie3, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Archetype $\mathcal{J}_1$ Package**:
Coagulates the $3 \times 3$ Kaluza–Janus double semidirect product law, left/right inverse
identities, exact adjoint Lie algebra transformation, Lie commutator closure, and radical
nilpotency. -/
theorem archetype_J1_kaluza_janus_3x3_group_and_lie_adjoint_action
    {χ χ_inv L L_inv : B} (χ₁ φ₁ L₁ C₁ χ₂ φ₂ L₂ C₂ φ C Ω γ δφ Ω₂ γ₂ δφ₂ : B)
    (hχ_left : χ_inv * χ = 1) (hL_left : L_inv * L = 1)
    (hχ_right : χ * χ_inv = 1) (hL_right : L * L_inv = 1) :
    janusGroup3 χ₁ φ₁ L₁ C₁ * janusGroup3 χ₂ φ₂ L₂ C₂ =
      janusGroup3 (χ₁ * χ₂) (χ₁ * φ₂ + φ₁) (L₁ * L₂) (L₁ * C₂ + C₁) ∧
    janusInv3 χ_inv φ L_inv C * janusGroup3 χ φ L C = 1 ∧
    janusGroup3 χ φ L C * janusInv3 χ_inv φ L_inv C = 1 ∧
    janusInv3 χ_inv φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 χ φ L C =
      janusLie3 (L_inv * Ω * L) (L_inv * Ω * C + L_inv * γ) (χ_inv * δφ) ∧
    OperatorAlgebra.PeirceSpine.comm (janusLie3 Ω γ δφ) (janusLie3 Ω₂ γ₂ δφ₂) =
      janusLie3 (OperatorAlgebra.PeirceSpine.comm Ω Ω₂) (Ω * γ₂ - Ω₂ * γ) 0 ∧
    janusLie3 0 γ δφ * janusLie3 0 γ δφ = 0 :=
  ⟨janusGroup3_mul χ₁ φ₁ L₁ C₁ χ₂ φ₂ L₂ C₂,
   janusInv3_mul_janusGroup3 φ C hχ_left hL_left,
   janusGroup3_mul_janusInv3 φ C hχ_right hL_right,
   janusLie3_adjoint_action χ χ_inv φ L L_inv C Ω γ δφ,
   janusLie3_commutator Ω γ δφ Ω₂ γ₂ δφ₂,
   janusLie3_radical_sq_zero γ δφ⟩

end ArchetypeJ1

/-! ===========================================================================
    Section 3: Archetype J2 — Souriau–Noether Trace Duality & Coadjoint Equivariance
    =========================================================================== -/

section ArchetypeJ2

variable {B : Type*} [Ring B]

/-- The $3 \times 3$ lower-triangular Souriau dual moment torsor matrix
$\begin{pmatrix} 0 & 0 & 0 \\ 0 & M & 0 \\ q & P & 0 \end{pmatrix} \in M_3(B)$,
carrying Lorentz moment `M`, translational momentum `P`, and Kaluza gauge charge `q`. -/
def janusDualMoment3 (M P q : B) : Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, 0; 0, M, 0; q, P, 0]

/-- The $3 \times 3$ dual translation-charge covector matrix (`M = 0`):
$\begin{pmatrix} 0 & 0 & 0 \\ 0 & 0 & 0 \\ q & P & 0 \end{pmatrix} \in M_3(B)$. -/
def janusDualCovector3 (P q : B) : Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, 0; 0, 0, 0; q, P, 0]

/-- **Souriau–Noether Trace Duality**:
The native `Matrix.trace` of the matrix product `janusDualMoment3 M P q * janusLie3 Ω γ δφ`
equals the exact non-commutative Souriau–Noether bilinear pairing `M * Ω + P * γ + q * δφ`. -/
theorem janus_noether_trace_pairing (M P q Ω γ δφ : B) :
    Matrix.trace (janusDualMoment3 M P q * janusLie3 Ω γ δφ) =
      M * Ω + P * γ + q * δφ := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply,
    janusDualMoment3, janusLie3]
  abel

/-- Specialization of `janus_noether_trace_pairing` to `janusDualCovector3 P q` (`M = 0`). -/
theorem janus_covector_trace_pairing (P q Ω γ δφ : B) :
    Matrix.trace (janusDualCovector3 P q * janusLie3 Ω γ δφ) =
      P * γ + q * δφ := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply,
    janusDualCovector3, janusLie3]
  abel

/-- **Multiplicative Equivariance of Kaluza–Janus Conjugation**:
Whenever `χ * χ_inv = 1` and `L * L_inv = 1`, simultaneous conjugation of any `3 × 3` dual
matrix `μ` and Lie algebra matrix `Z` by `janusGroup3 χ φ L C` intertwines matrix multiplication. -/
theorem janus_conjugation_mul_equivariance
    {χ χ_inv L L_inv : B} (φ C : B) (μ Z : Matrix (Fin 3) (Fin 3) B)
    (hχ : χ * χ_inv = 1) (hL : L * L_inv = 1) :
    (janusInv3 χ_inv φ L_inv C * μ * janusGroup3 χ φ L C) *
        (janusInv3 χ_inv φ L_inv C * Z * janusGroup3 χ φ L C) =
      janusInv3 χ_inv φ L_inv C * (μ * Z) * janusGroup3 χ φ L C := by
  have hG : janusGroup3 χ φ L C * janusInv3 χ_inv φ L_inv C = 1 :=
    janusGroup3_mul_janusInv3 φ C hχ hL
  calc
    (janusInv3 χ_inv φ L_inv C * μ * janusGroup3 χ φ L C) *
        (janusInv3 χ_inv φ L_inv C * Z * janusGroup3 χ φ L C) =
      janusInv3 χ_inv φ L_inv C * μ *
        (janusGroup3 χ φ L C * janusInv3 χ_inv φ L_inv C) * Z *
        janusGroup3 χ φ L C := by
      simp [Matrix.mul_assoc]
    _ = janusInv3 χ_inv φ L_inv C * (μ * Z) * janusGroup3 χ φ L C := by
      rw [hG]
      simp [Matrix.mul_assoc]

/-- **Coadjoint Sector Transformations of `janusDualMoment3`**:
Conjugating `janusDualMoment3 M P q` by `janusGroup3 χ φ L C` transforms the active dual
coordinates by:
- Charge sector `(2,0)`: `q ↦ q * χ` (so `χ = -1` reverses scalar charge `q ↦ -q`),
- Momentum sector `(2,1)`: `P ↦ P * L`,
- Angular moment sector `(1,1)`: `M ↦ L_inv * M * L - L_inv * C * P * L`. -/
theorem janus_coadjoint_moment_sectors (χ χ_inv φ L L_inv C M P q : B) :
    (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) 2 0 = q * χ ∧
    (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) 2 1 = P * L ∧
    (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) 1 1 =
      L_inv * M * L - L_inv * C * P * L := by
  refine ⟨?_, ?_, ?_⟩
  · simp [janusGroup3, janusInv3, janusDualMoment3, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [janusGroup3, janusInv3, janusDualMoment3, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [janusGroup3, janusInv3, janusDualMoment3, Matrix.mul_apply, Fin.sum_univ_three]
    noncomm_ring

/-- **Contragredient Souriau–Noether Pairing Defect under Translation `C` and Charge Reflection `χ`**:
When `χ * χ_inv = 1` and `L = L_inv = 1`, pairing the coadjoint-shifted dual moment
`janusDualMoment3 (M - P * C) P (q * χ)` with the adjoint-transformed Lie algebra element
`janusInv3 χ_inv φ 1 C * janusLie3 Ω γ δφ * janusGroup3 χ φ 1 C` reproduces the Souriau–Noether
pairing `M * Ω + P * γ + q * δφ` plus the exact non-commutative commutator defect
`P * OperatorAlgebra.PeirceSpine.comm Ω C`. -/
theorem janus_noether_contragredient_translation_defect
    {χ χ_inv : B} (φ C M P q Ω γ δφ : B) (hχ : χ * χ_inv = 1) :
    Matrix.trace
        (janusDualMoment3 (M - P * C) P (q * χ) *
          (janusInv3 χ_inv φ 1 C * janusLie3 Ω γ δφ * janusGroup3 χ φ 1 C)) =
      (M * Ω + P * γ + q * δφ) + P * OperatorAlgebra.PeirceSpine.comm Ω C := by
  rw [janusLie3_adjoint_action, janus_noether_trace_pairing]
  have hq : q * χ * (χ_inv * δφ) = q * δφ := by
    calc
      q * χ * (χ_inv * δφ) = q * (χ * χ_inv) * δφ := by noncomm_ring
      _ = q * 1 * δφ := by rw [hχ]
      _ = q * δφ := by noncomm_ring
  rw [hq]
  change (M - P * C) * (1 * Ω * 1) + P * (1 * Ω * C + 1 * γ) + q * δφ =
    M * Ω + P * γ + q * δφ + P * (Ω * C - C * Ω)
  noncomm_ring

/-- **Archetype $\mathcal{J}_2$ Package**:
Coagulates the Souriau–Noether trace pairing, multiplicative conjugation equivariance, coadjoint
moment sector laws, and contragredient non-commutative translation defect. -/
theorem archetype_J2_souriau_noether_duality_pairing_and_equivariance
    {χ χ_inv L L_inv : B} (φ C M P q Ω γ δφ : B)
    (hχ_right : χ * χ_inv = 1) (hL_right : L * L_inv = 1) :
    Matrix.trace (janusDualMoment3 M P q * janusLie3 Ω γ δφ) =
      M * Ω + P * γ + q * δφ ∧
    Matrix.trace (janusDualCovector3 P q * janusLie3 Ω γ δφ) =
      P * γ + q * δφ ∧
    (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) *
        (janusInv3 χ_inv φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 χ φ L C) =
      janusInv3 χ_inv φ L_inv C *
        (janusDualMoment3 M P q * janusLie3 Ω γ δφ) *
        janusGroup3 χ φ L C ∧
    ((janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) 2 0 = q * χ ∧
     (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) 2 1 = P * L ∧
     (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) 1 1 =
       L_inv * M * L - L_inv * C * P * L) ∧
    Matrix.trace
        (janusDualMoment3 (M - P * C) P (q * χ) *
          (janusInv3 χ_inv φ 1 C * janusLie3 Ω γ δφ * janusGroup3 χ φ 1 C)) =
      (M * Ω + P * γ + q * δφ) + P * OperatorAlgebra.PeirceSpine.comm Ω C :=
  ⟨janus_noether_trace_pairing M P q Ω γ δφ,
   janus_covector_trace_pairing P q Ω γ δφ,
   janus_conjugation_mul_equivariance φ C (janusDualMoment3 M P q) (janusLie3 Ω γ δφ)
     hχ_right hL_right,
   janus_coadjoint_moment_sectors χ χ_inv φ L L_inv C M P q,
   janus_noether_contragredient_translation_defect φ C M P q Ω γ δφ hχ_right⟩

end ArchetypeJ2

/-! ===========================================================================
    Section 4: Archetype J3 — Socratic Aporia, Bimetric Coupling Nilpotency & Block Stress Action
    =========================================================================== -/

section ArchetypeJ3

variable {B : Type*} [Ring B]

/-- The $2 \times 2$ Krein-graded bimetric coupling matrix
$\mathcal{C}(b_1, b_2) = \begin{pmatrix} 1 & b_1 \\ -b_2 & -1 \end{pmatrix} \in M_2(B)$,
where $b_1, b_2 \in B$ are the reciprocal volume-ratio coupling operators between the two sheets. -/
def bimetricCoupling2 (b₁ b₂ : B) : Matrix (Fin 2) (Fin 2) B :=
  !![1, b₁; -b₂, -1]

/-- The $2 \times 2$ Bianchi conservation annihilator matrix
$\mathcal{A}(b_2) = \begin{pmatrix} b_2 & 1 \\ 0 & 0 \end{pmatrix} \in M_2(B)$. -/
def bimetricAnnihilator2 (b₂ : B) : Matrix (Fin 2) (Fin 2) B :=
  !![b₂, 1; 0, 0]

/-- The $2 \times 2$ Cartan grading involution
$E_z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in M_2(B)$. -/
def cartanEz2 : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, -1]

/-- Full non-diagonal $2 \times 2$ self-sector stress-energy-flux block operator matrix
$\begin{pmatrix} \rho & J_+ \\ J_- & -p \end{pmatrix} \in M_2(B)$. -/
def stressSelfBlock2 (ρ J_plus J_minus p : B) : Matrix (Fin 2) (Fin 2) B :=
  !![ρ, J_plus; J_minus, -p]

/-- Full non-diagonal $2 \times 2$ induced-sector stress-energy-flux block operator matrix
$\begin{pmatrix} \rho & J_+ \\ -J_- & p \end{pmatrix} \in M_2(B)$ obtained by left Cartan
reflection `cartanEz2 * stressSelfBlock2 ρ J_plus J_minus p`. -/
def stressInducedBlock2 (ρ J_plus J_minus p : B) : Matrix (Fin 2) (Fin 2) B :=
  !![ρ, J_plus; -J_minus, p]

/-- Diagonal specialization `stressSelf2 ρ p = stressSelfBlock2 ρ 0 0 p`. -/
def stressSelf2 (ρ p : B) : Matrix (Fin 2) (Fin 2) B :=
  stressSelfBlock2 ρ 0 0 p

/-- Diagonal specialization `stressInduced2 ρ p = stressInducedBlock2 ρ 0 0 p`. -/
def stressInduced2 (ρ p : B) : Matrix (Fin 2) (Fin 2) B :=
  !![ρ, 0; 0, p]

/-- **Socratic Aporia of the Bimetric Coupling Matrix**:
The square of `bimetricCoupling2 b₁ b₂` is diagonal with entries `1 - b₁ * b₂` and `1 - b₂ * b₁`,
measuring the exact off-shell failure of `b₁` and `b₂` to be two-sided inverses. -/
theorem bimetricCoupling2_sq_defect (b₁ b₂ : B) :
    bimetricCoupling2 b₁ b₂ * bimetricCoupling2 b₁ b₂ =
      !![1 - b₁ * b₂, 0; 0, 1 - b₂ * b₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [bimetricCoupling2, Matrix.mul_apply, Fin.sum_univ_two]; try noncomm_ring)

/-- **Two-Step Nilpotency of the Bimetric Coupling Matrix on Shell (`b₁ * b₂ = 1`, `b₂ * b₁ = 1`)**:
Whenever the two volume-ratio operators are mutual two-sided inverses, `bimetricCoupling2 b₁ b₂`
squares identically to zero. -/
theorem bimetricCoupling2_sq_zero {b₁ b₂ : B}
    (h₁₂ : b₁ * b₂ = 1) (h₂₁ : b₂ * b₁ = 1) :
    bimetricCoupling2 b₁ b₂ * bimetricCoupling2 b₁ b₂ = 0 := by
  rw [bimetricCoupling2_sq_defect, h₁₂, h₂₁, sub_self]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The trace of `bimetricCoupling2 b₁ b₂` vanishes identically for all `b₁, b₂ : B`. -/
theorem bimetricCoupling2_trace_zero (b₁ b₂ : B) :
    Matrix.trace (bimetricCoupling2 b₁ b₂) = 0 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, bimetricCoupling2]

/-- **Matrix Operator Bianchi Conservation Defect on Full $2 \times 2$ Source Matrices**:
Acting with `bimetricAnnihilator2 b₂ * bimetricCoupling2 b₁ b₂` on any $2 \times 2$ source
operator matrix `T = !![T₁₁, T₁₂; T₂₁, T₂₂]` isolates the off-shell defect `(b₂ * b₁ - 1)` on the
second row `(T₂₁, T₂₂)` and annihilates `(T₁₁, T₁₂)` unconditionally. -/
theorem bimetric_matrix_bianchi_conservation_defect (b₁ b₂ T₁₁ T₁₂ T₂₁ T₂₂ : B) :
    bimetricAnnihilator2 b₂ * (bimetricCoupling2 b₁ b₂ * !![T₁₁, T₁₂; T₂₁, T₂₂]) =
      !![(b₂ * b₁ - 1) * T₂₁, (b₂ * b₁ - 1) * T₂₂; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [bimetricAnnihilator2, bimetricCoupling2, Matrix.mul_apply, Fin.sum_univ_two];
     try noncomm_ring)

/-- **Matrix Operator Bianchi Conservation Law (`b₂ * b₁ = 1`)**:
Whenever `b₂ * b₁ = 1`, `bimetricAnnihilator2 b₂` left-annihilates `bimetricCoupling2 b₁ b₂ * T`
for every $2 \times 2$ source matrix `T : Matrix (Fin 2) (Fin 2) B`. -/
theorem bimetric_matrix_bianchi_conservation_zero {b₁ b₂ : B}
    (T : Matrix (Fin 2) (Fin 2) B) (h₂₁ : b₂ * b₁ = 1) :
    bimetricAnnihilator2 b₂ * (bimetricCoupling2 b₁ b₂ * T) = 0 := by
  have hProd : bimetricAnnihilator2 b₂ * bimetricCoupling2 b₁ b₂ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bimetricAnnihilator2, bimetricCoupling2, Matrix.mul_apply, Fin.sum_univ_two]
    calc
      b₂ * b₁ + -1 = b₂ * b₁ - 1 := by noncomm_ring
      _ = 1 - 1 := by rw [h₂₁]
      _ = 0 := sub_self 1
  rw [← Matrix.mul_assoc, hProd, Matrix.zero_mul]

/-- **Coupled Bianchi Conservation Defect**:
For any coupled sources `G_plus = T_plus + b₁ * T_minus` and `G_minus = -(b₂ * T_plus) - T_minus`,
the weighted sum `b₂ * G_plus + G_minus` equals `(b₂ * b₁ - 1) * T_minus`. -/
theorem bimetric_bianchi_conservation_defect (b₁ b₂ T_plus T_minus : B) :
    b₂ * (T_plus + b₁ * T_minus) + (-(b₂ * T_plus) - T_minus) =
      (b₂ * b₁ - 1) * T_minus := by
  noncomm_ring

/-- **Exact Coupled Bianchi Conservation Law (`b₂ * b₁ = 1`)**:
When `b₂ * b₁ = 1`, the two coupled source equations are algebraically dependent:
`b₂ * (T_plus + b₁ * T_minus) + (-(b₂ * T_plus) - T_minus) = 0`. -/
theorem bimetric_bianchi_conservation_zero {b₁ b₂ : B} (T_plus T_minus : B)
    (h₂₁ : b₂ * b₁ = 1) :
    b₂ * (T_plus + b₁ * T_minus) + (-(b₂ * T_plus) - T_minus) = 0 := by
  rw [bimetric_bianchi_conservation_defect, h₂₁, sub_self, zero_mul]

/-- The Cartan grading involution `cartanEz2` squares to the identity matrix. -/
theorem cartanEz2_sq_one : (cartanEz2 : Matrix (Fin 2) (Fin 2) B) * cartanEz2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartanEz2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Cartan Involution Action on Full Non-Diagonal Block Stress Matrices**:
Left-multiplying `stressSelfBlock2 ρ J_plus J_minus p = !![ρ, J_plus; J_minus, -p]` by
`cartanEz2 = !![1, 0; 0, -1]` preserves the upper row `(ρ, J_plus)` and reverses the lower row
`(J_minus, -p) ↦ (-J_minus, p)`, producing `stressInducedBlock2 ρ J_plus J_minus p`. -/
theorem cartanEz2_mul_stressSelfBlock2 (ρ J_plus J_minus p : B) :
    cartanEz2 * stressSelfBlock2 ρ J_plus J_minus p = stressInducedBlock2 ρ J_plus J_minus p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartanEz2, stressSelfBlock2, stressInducedBlock2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Cartan Involution Pressure Reversal**:
Multiplying `stressSelf2 ρ p = !![ρ, 0; 0, -p]` by `cartanEz2` produces `stressInduced2 ρ p`. -/
theorem cartanEz2_mul_stressSelf2 (ρ p : B) :
    cartanEz2 * stressSelf2 ρ p = stressInduced2 ρ p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartanEz2, stressSelf2, stressSelfBlock2, stressInduced2,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Even-grade sum of self and induced stress tensors isolates the density sector `(0,0)`. -/
theorem stressSelf2_add_stressInduced2 (ρ p : B) :
    stressSelf2 ρ p + stressInduced2 ρ p = !![ρ + ρ, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stressSelf2, stressSelfBlock2, stressInduced2]

/-- Odd-grade difference of self and induced stress tensors isolates the pressure sector `(1,1)`. -/
theorem stressSelf2_sub_stressInduced2 (ρ p : B) :
    stressSelf2 ρ p - stressInduced2 ρ p = !![0, 0; 0, -(p + p)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [stressSelf2, stressSelfBlock2, stressInduced2]; try noncomm_ring)

/-- **Archetype $\mathcal{J}_3$ Package**:
Coagulates the bimetric coupling square defect, on-shell 2-step nilpotency, trace vanishing,
matrix and operator Bianchi conservation laws, and Cartan block reflection. -/
theorem archetype_J3_bimetric_coupling_nilpotency_conservation_and_pressure_flip
    {b₁ b₂ : B} (T : Matrix (Fin 2) (Fin 2) B) (T_plus T_minus ρ J_plus J_minus p : B)
    (h₁₂ : b₁ * b₂ = 1) (h₂₁ : b₂ * b₁ = 1) :
    bimetricCoupling2 b₁ b₂ * bimetricCoupling2 b₁ b₂ = 0 ∧
    Matrix.trace (bimetricCoupling2 b₁ b₂) = 0 ∧
    bimetricAnnihilator2 b₂ * (bimetricCoupling2 b₁ b₂ * T) = 0 ∧
    b₂ * (T_plus + b₁ * T_minus) + (-(b₂ * T_plus) - T_minus) = 0 ∧
    cartanEz2 * stressSelfBlock2 ρ J_plus J_minus p = stressInducedBlock2 ρ J_plus J_minus p ∧
    cartanEz2 * stressSelf2 ρ p = stressInduced2 ρ p ∧
    stressSelf2 ρ p + stressInduced2 ρ p = !![ρ + ρ, 0; 0, 0] ∧
    stressSelf2 ρ p - stressInduced2 ρ p = !![0, 0; 0, -(p + p)] :=
  ⟨bimetricCoupling2_sq_zero h₁₂ h₂₁,
   bimetricCoupling2_trace_zero b₁ b₂,
   bimetric_matrix_bianchi_conservation_zero T h₂₁,
   bimetric_bianchi_conservation_zero T_plus T_minus h₂₁,
   cartanEz2_mul_stressSelfBlock2 ρ J_plus J_minus p,
   cartanEz2_mul_stressSelf2 ρ p,
   stressSelf2_add_stressInduced2 ρ p,
   stressSelf2_sub_stressInduced2 ρ p⟩

end ArchetypeJ3

/-! ===========================================================================
    Section 5: Archetype J4 — Peirce–Krein, 3-Sheet KKT, Zorn & Non-Commutative Operator Bridges
    =========================================================================== -/

section ArchetypeJ4

variable {B : Type*} [Ring B]

/-- The fundamental $2 \times 2$ positive-sheet Peirce idempotent
$P_2 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix} \in M_2(B)$. -/
def peirceProj2 : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, 0]

/-- `peirceProj2` is an idempotent in `Matrix (Fin 2) (Fin 2) B`. -/
theorem peirceProj2_idem : (peirceProj2 : Matrix (Fin 2) (Fin 2) B) * peirceProj2 = peirceProj2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceProj2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Bridge 1 (`cartanEz2` = Peirce Spine Involution `invS peirceProj2`)**:
The $2 \times 2$ Cartan involution `cartanEz2 = !![1, 0; 0, -1]` coincides identically with the
Peirce Spine reflection `invS peirceProj2 = 2 peirceProj2 - 1`. -/
theorem cartanEz2_eq_invS_peirceProj2 :
    (cartanEz2 : Matrix (Fin 2) (Fin 2) B) = invS (peirceProj2 (B := B)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [cartanEz2, invS, peirceProj2]; try noncomm_ring)

/-- **Bridge 2 (Peirce Spine Decomposition of `bimetricCoupling2`)**:
The bimetric coupling matrix `bimetricCoupling2 b₁ b₂ = !![1, b₁; -b₂, -1]` decomposes into the
Peirce involution `invS peirceProj2` plus the upper nilpotent Peirce cone
`conePlus peirceProj2 !![0, b₁; 0, 0]` minus the lower nilpotent Peirce cone
`coneMinus peirceProj2 !![0, 0; b₂, 0]`. -/
theorem bimetricCoupling2_peirce_decomposition (b₁ b₂ : B) :
    bimetricCoupling2 b₁ b₂ =
      invS (peirceProj2 (B := B)) +
        conePlus (peirceProj2 (B := B)) !![0, b₁; 0, 0] -
        coneMinus (peirceProj2 (B := B)) !![0, 0; b₂, 0] := by
  have hQ : (1 - peirceProj2 : Matrix (Fin 2) (Fin 2) B) = !![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [peirceProj2]
  rw [← cartanEz2_eq_invS_peirceProj2]
  dsimp [conePlus, coneMinus]
  rw [hQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bimetricCoupling2, cartanEz2, peirceProj2]

/-- **Bridge 3 (Unconditional Non-Commutative Operatorial Elliptic vs. Hyperbolic Krein Modulus)**:
For any idempotent `P * P = P` in `[Ring B]` and any non-commuting elements `g, A, C : B`:
1. `(g + genJ P A C) * (g - genJ P A C) = g * g + genV P A C - comm g (genJ P A C)` (since `J² = -V`),
2. `(g + genPhi P A C) * (g - genPhi P A C) = g * g - genV P A C - comm g (genPhi P A C)` (since `Φ² = +V`). -/
theorem peirce_noncommutative_elliptic_and_hyperbolic_krein_modulus
    {P : B} (hP : P * P = P) (g A C : B) :
    (g + genJ P A C) * (g - genJ P A C) =
      g * g + genV P A C - OperatorAlgebra.PeirceSpine.comm g (genJ P A C) ∧
    (g + genPhi P A C) * (g - genPhi P A C) =
      g * g - genV P A C - OperatorAlgebra.PeirceSpine.comm g (genPhi P A C) := by
  have hJ2 : genJ P A C * genJ P A C = -genV P A C := by peirce_nf hP
  have hPhi2 : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
  constructor
  · calc
      (g + genJ P A C) * (g - genJ P A C)
        = g * g - genJ P A C * genJ P A C - OperatorAlgebra.PeirceSpine.comm g (genJ P A C) := by
          dsimp [OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
      _ = g * g - (-genV P A C) - OperatorAlgebra.PeirceSpine.comm g (genJ P A C) := by rw [hJ2]
      _ = g * g + genV P A C - OperatorAlgebra.PeirceSpine.comm g (genJ P A C) := by noncomm_ring
  · calc
      (g + genPhi P A C) * (g - genPhi P A C)
        = g * g - genPhi P A C * genPhi P A C -
            OperatorAlgebra.PeirceSpine.comm g (genPhi P A C) := by
          dsimp [OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
      _ = g * g - genV P A C - OperatorAlgebra.PeirceSpine.comm g (genPhi P A C) := by rw [hPhi2]

/-- **Bridge 4 (Universal Non-Commutative Left/Right Nambu Ternary 3-Bracket Symmetry)**:
Over any non-commutative associative ring `[Ring B]`, the left Nambu 3-bracket
`u₁ * comm u₂ u₃ + u₂ * comm u₃ u₁ + u₃ * comm u₁ u₂` and the right Nambu 3-bracket
`comm u₂ u₃ * u₁ + comm u₃ u₁ * u₂ + comm u₁ u₂ * u₃` are identically equal (`= nambu3`). -/
theorem universal_associative_left_eq_right_nambu_3bracket (u₁ u₂ u₃ : B) :
    u₁ * OperatorAlgebra.PeirceSpine.comm u₂ u₃ +
      u₂ * OperatorAlgebra.PeirceSpine.comm u₃ u₁ +
      u₃ * OperatorAlgebra.PeirceSpine.comm u₁ u₂ =
    OperatorAlgebra.PeirceSpine.comm u₂ u₃ * u₁ +
      OperatorAlgebra.PeirceSpine.comm u₃ u₁ * u₂ +
      OperatorAlgebra.PeirceSpine.comm u₁ u₂ * u₃ := by
  dsimp [OperatorAlgebra.PeirceSpine.comm]
  noncomm_ring

/-- Explicit Grade-`+2` Kantor sandwich operator
`(conePlus P A * coneMinus P C) * conePlus P X * (coneMinus P C * conePlus P A)`. -/
def kantorGp2 (P A C X : B) : B :=
  (conePlus P A * coneMinus P C) * conePlus P X * (coneMinus P C * conePlus P A)

/-- Explicit Grade-`-2` Kantor sandwich operator
`(coneMinus P C * conePlus P A) * coneMinus P X * (conePlus P A * coneMinus P C)`. -/
def kantorGm2 (P A C X : B) : B :=
  (coneMinus P C * conePlus P A) * coneMinus P X * (conePlus P A * coneMinus P C)

/-- **Bridge 5 (Explicit Grade-`±2` Kantor Sandwich Operators & Curvature Reconstruction)**:
For any idempotent `P * P = P` in `[Ring B]` and any `A, C, X : B`, the sum of the grade-`±2`
Kantor sandwich operators equals `-(genSig P A C * genPhi P X X * genSig P A C)`. -/
theorem kantorGp2_kantorGm2_curvature_sandwich_identity
    {P : B} (hP : P * P = P) (A C X : B) :
    kantorGp2 P A C X + kantorGm2 P A C X =
      -(genSig P A C * genPhi P X X * genSig P A C) := by
  dsimp [kantorGp2, kantorGm2]
  peirce_nf hP

/-- **Bridge 6 (Socratic Aporia Commutator & Ego-Closure Equivalences)**:
Over any associative ring `[Ring B]` with idempotent `P * P = P` and any `X : B`:
1. `genPhi P X X = 0 ↔ genJ P X X = 0`,
2. `genJ P X X = 0 ↔ (conePlus P X = 0 ∧ coneMinus P X = 0)`,
3. `P * X * P = X ↔ (genPhi P X X = 0 ∧ (1 - P) * X * (1 - P) = 0)`. -/
theorem socratic_aporia_commutator_and_ego_closure_iff
    {P : B} (hP : P * P = P) (X : B) :
    (genPhi P X X = 0 ↔ genJ P X X = 0) ∧
    (genJ P X X = 0 ↔ (conePlus P X = 0 ∧ coneMinus P X = 0)) ∧
    (P * X * P = X ↔ (genPhi P X X = 0 ∧ (1 - P) * X * (1 - P) = 0)) := by
  have hJ_eq : genJ P X X = OperatorAlgebra.PeirceSpine.comm P (genPhi P X X) := by
    peirce_nf hP
  have hPhi_eq : genPhi P X X = OperatorAlgebra.PeirceSpine.comm P (genJ P X X) := by
    peirce_nf hP
  have hCp : conePlus P X = P * genJ P X X := by peirce_nf hP
  have hCm : coneMinus P X = -(genJ P X X * P) := by peirce_nf hP
  have hJ_sum : genJ P X X = conePlus P X - coneMinus P X := rfl
  have hPhi_sum : genPhi P X X = conePlus P X + coneMinus P X := rfl
  have h_decomp : P * X * P + genPhi P X X + (1 - P) * X * (1 - P) = X := by
    dsimp [genPhi, conePlus, coneMinus]
    noncomm_ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hPhi
    rw [hJ_eq, hPhi]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  · intro hJ
    rw [hPhi_eq, hJ]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  · intro hJ
    refine ⟨?_, ?_⟩
    · rw [hCp, hJ, mul_zero]
    · rw [hCm, hJ, zero_mul, neg_zero]
  · rintro ⟨hp, hm⟩
    rw [hJ_sum, hp, hm, sub_self]
  · intro hPXP
    have hPX : P * X = X := by
      calc
        P * X = P * (P * X * P) := by nth_rw 1 [← hPXP]
        _ = (P * P) * X * P := by noncomm_ring
        _ = P * X * P := by rw [hP]
        _ = X := hPXP
    have hXP : X * P = X := by
      calc
        X * P = (P * X * P) * P := by nth_rw 1 [← hPXP]
        _ = P * X * (P * P) := by noncomm_ring
        _ = P * X * P := by rw [hP]
        _ = X := hPXP
    have hCp0 : conePlus P X = 0 := by
      dsimp [conePlus]
      calc
        P * X * (1 - P) = (P * X) - (P * X) * P := by noncomm_ring
        _ = X - X * P := by rw [hPX]
        _ = X - X := by rw [hXP]
        _ = 0 := sub_self X
    have hCm0 : coneMinus P X = 0 := by
      dsimp [coneMinus]
      calc
        (1 - P) * X * P = (X * P) - P * (X * P) := by noncomm_ring
        _ = X - P * X := by rw [hXP]
        _ = X - X := by rw [hPX]
        _ = 0 := sub_self X
    have hPhi0 : genPhi P X X = 0 := by
      rw [hPhi_sum, hCp0, hCm0, add_zero]
    have hD20 : (1 - P) * X * (1 - P) = 0 := by
      calc
        (1 - P) * X * (1 - P)
          = (P * X * P + genPhi P X X + (1 - P) * X * (1 - P)) - P * X * P - genPhi P X X := by
            noncomm_ring
        _ = X - X - 0 := by rw [h_decomp, hPXP, hPhi0]
        _ = 0 := by noncomm_ring
    exact ⟨hPhi0, hD20⟩
  · rintro ⟨hPhi0, hD20⟩
    calc
      P * X * P = P * X * P + genPhi P X X + (1 - P) * X * (1 - P) := by
        rw [hPhi0, hD20, add_zero, add_zero]
      _ = X := h_decomp

/-- **Bridge 7 (Chiral $\gamma_5 = \mathrm{invS}\;P$ Anomaly 2-Cocycle Operator Decomposition)**:
Over any associative ring `[Ring B]` with idempotent `P * P = P` and any `A₁ C₁ A₂ C₂ : B`:
1. The commutator of two odd tetrads `Φ₁ = genPhi P A₁ C₁` and `Φ₂ = genPhi P A₂ C₂` decomposes
   into the upper-block difference `(conePlus P A₁ * coneMinus P C₂ - conePlus P A₂ * coneMinus P C₁)`
   plus the lower-block difference `(coneMinus P C₁ * conePlus P A₂ - coneMinus P C₂ * conePlus P A₁)`,
2. Left multiplication by the chiral grading involution `invS P = 2 P - 1` flips the sign of the
   lower-block difference, producing the chiral anomaly operator
   `(conePlus P A₁ * coneMinus P C₂ - conePlus P A₂ * coneMinus P C₁) - (coneMinus P C₁ * conePlus P A₂ - coneMinus P C₂ * conePlus P A₁)`. -/
theorem chiral_gamma5_anomaly_2cocycle_operator_decomposition
    {P : B} (hP : P * P = P) (A₁ C₁ A₂ C₂ : B) :
    OperatorAlgebra.PeirceSpine.comm (genPhi P A₁ C₁) (genPhi P A₂ C₂) =
      (conePlus P A₁ * coneMinus P C₂ - conePlus P A₂ * coneMinus P C₁) +
        (coneMinus P C₁ * conePlus P A₂ - coneMinus P C₂ * conePlus P A₁) ∧
    invS P * OperatorAlgebra.PeirceSpine.comm (genPhi P A₁ C₁) (genPhi P A₂ C₂) =
      (conePlus P A₁ * coneMinus P C₂ - conePlus P A₂ * coneMinus P C₁) -
        (coneMinus P C₁ * conePlus P A₂ - coneMinus P C₂ * conePlus P A₁) := by
  constructor
  · dsimp [OperatorAlgebra.PeirceSpine.comm]
    peirce_nf hP
  · dsimp [OperatorAlgebra.PeirceSpine.comm]
    peirce_nf hP

variable [StarRing B]

/-- `peirceProj2` equals the anomaly-generated positive sheet `P Nplus = Nplus * star Nplus`
from `MatrixUnitAnomalyRealization`. -/
theorem peirceProj2_eq_anomaly_sheet_P :
    peirceProj2 (B := B) = P (Nplus (B := B)) :=
  (matrix_unit_peirce_sheets (B := B)).1.symm

/-- **Bridge 8 (Three-Sheet KKT 5-Grade Decomposition of `janusLie3`)**:
Under the 5-graded Peirce–Kantor–Koecher–Tits projections `peirceGrade*` generated by the
three-sheet tripotent `Nplus3 = !![0, 1, 0; 0, 0, 0; 0, 0, 0]`, the Kaluza–Janus Lie algebra
matrix `janusLie3 Ω γ δφ` decomposes cleanly into:
- Grade `+2`: `0`,
- Grade `+1`: the fifth-coordinate gauge generator `!![0, 0, δφ; 0, 0, 0; 0, 0, 0]`,
- Grade `0`: the homogeneous Lorentz generator `!![0, 0, 0; 0, Ω, 0; 0, 0, 0]`,
- Grade `-1`: the spacetime translation generator `!![0, 0, 0; 0, 0, γ; 0, 0, 0]`,
- Grade `-2`: `0`. -/
theorem janusLie3_peirce_five_grade_decomposition (Ω γ δφ : B) :
    peirceGradePlus2 (Nplus3 (B := B)) (janusLie3 Ω γ δφ) = 0 ∧
    peirceGradePlus1 (Nplus3 (B := B)) (janusLie3 Ω γ δφ) =
      !![0, 0, δφ; 0, 0, 0; 0, 0, 0] ∧
    peirceGradeZero (Nplus3 (B := B)) (janusLie3 Ω γ δφ) =
      !![0, 0, 0; 0, Ω, 0; 0, 0, 0] ∧
    peirceGradeMinus1 (Nplus3 (B := B)) (janusLie3 Ω γ δφ) =
      !![0, 0, 0; 0, 0, γ; 0, 0, 0] ∧
    peirceGradeMinus2 (Nplus3 (B := B)) (janusLie3 Ω γ δφ) = 0 := by
  rcases five_grade_matrix_coordinates (B := B) (janusLie3 Ω γ δφ) with
    ⟨h₂, h₁, h₀, hₘ₁, hₘ₂⟩
  rw [h₂, h₁, h₀, hₘ₁, hₘ₂]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp [janusLie3])

/-- **Bridge 9 (Three-Sheet KKT 5-Grade Decomposition of `janusDualMoment3`)**:
Under the 5-graded Peirce–KKT projections `peirceGrade* (Nplus3)`, the Souriau dual moment torsor
matrix `janusDualMoment3 M P q` decomposes into the dual grades:
- Grade `+2`: `0`,
- Grade `+1`: the translational momentum `!![0, 0, 0; 0, 0, 0; 0, P, 0]` (dual to `γ` in grade `-1`),
- Grade `0`: the Lorentz angular moment `!![0, 0, 0; 0, M, 0; 0, 0, 0]` (dual to `Ω` in grade `0`),
- Grade `-1`: the Kaluza gauge charge `!![0, 0, 0; 0, 0, 0; q, 0, 0]` (dual to `δφ` in grade `+1`),
- Grade `-2`: `0`. -/
theorem janusDualMoment3_peirce_five_grade_decomposition (M P q : B) :
    peirceGradePlus2 (Nplus3 (B := B)) (janusDualMoment3 M P q) = 0 ∧
    peirceGradePlus1 (Nplus3 (B := B)) (janusDualMoment3 M P q) =
      !![0, 0, 0; 0, 0, 0; 0, P, 0] ∧
    peirceGradeZero (Nplus3 (B := B)) (janusDualMoment3 M P q) =
      !![0, 0, 0; 0, M, 0; 0, 0, 0] ∧
    peirceGradeMinus1 (Nplus3 (B := B)) (janusDualMoment3 M P q) =
      !![0, 0, 0; 0, 0, 0; q, 0, 0] ∧
    peirceGradeMinus2 (Nplus3 (B := B)) (janusDualMoment3 M P q) = 0 := by
  rcases five_grade_matrix_coordinates (B := B) (janusDualMoment3 M P q) with
    ⟨h₂, h₁, h₀, hₘ₁, hₘ₂⟩
  rw [h₂, h₁, h₀, hₘ₁, hₘ₂]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp [janusDualMoment3])

omit [StarRing B] in
/-- **Bridge 10 (Zorn 5-Grade Projection of `janusLie3` and `janusDualMoment3`)**:
Under `matrix3ToOpZorn`, `janusLie3 Ω γ δφ` and `janusDualMoment3 M P q` land in complementary
grades `opGradeZero`, `opGradePlus1`, and `opGradeMinus1` of `OpZornMatrix B`. -/
theorem janus_zorn_five_grade_projections (Ω γ δφ M P q : B) :
    matrix3ToOpZorn (janusLie3 Ω γ δφ) =
      opGradeZero 0 Ω + opGradePlus1 δφ 0 + opGradeMinus1 γ 0 ∧
    matrix3ToOpZorn (janusDualMoment3 M P q) =
      opGradeZero 0 M + opGradePlus1 0 P + opGradeMinus1 0 q := by
  constructor <;>
    (ext <;>
      simp [matrix3ToOpZorn, janusLie3, janusDualMoment3,
        opGradeZero, opCartanDiag, opGradePlus1, opGradeMinus1])

/-- Helper: each three-sheet Peirce sheet support `P Nplus3`, `Q Nplus3`, and `peirceR Nplus3`
commutes with any diagonal matrix `Matrix.diagonal d` over `[Ring B]`. -/
theorem nplus3_sheets_comm_diagonal (d : Fin 3 → B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.P (Nplus3 (B := B)) *
        Matrix.diagonal d =
      Matrix.diagonal d *
        InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.P (Nplus3 (B := B)) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.Q (Nplus3 (B := B)) *
        Matrix.diagonal d =
      Matrix.diagonal d *
        InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.Q (Nplus3 (B := B)) ∧
    peirceR (Nplus3 (B := B)) * Matrix.diagonal d =
      Matrix.diagonal d * peirceR (Nplus3 (B := B)) := by
  have hS := Nplus3_sheets (B := B)
  have hR := Nplus3_peirceR (B := B)
  refine ⟨?_, ?_, ?_⟩
  · rw [hS.1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · rw [hS.2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · rw [hR]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [StarRing B] in
/-- Associative sandwich commutation lemma for two projections commuting with `U` and `U_inv`. -/
theorem sandwich_comm_of_comm {M : Type*} [Semiring M]
    {E₁ E₂ U U_inv X : M}
    (h₁ : E₁ * U = U * E₁) (h₂ : E₂ * U_inv = U_inv * E₂) :
    E₁ * (U * X * U_inv) * E₂ = U * (E₁ * X * E₂) * U_inv := by
  calc
    E₁ * (U * X * U_inv) * E₂ = (E₁ * U) * X * (U_inv * E₂) := by simp only [mul_assoc]
    _ = (U * E₁) * X * (E₂ * U_inv) := by rw [h₁, h₂.symm]
    _ = U * (E₁ * X * E₂) * U_inv := by simp only [mul_assoc]

/-- **Bridge 11 (Direct Operator-Erlangen Equivariance of All Five Three-Sheet Peirce–KKT Sector Projections)**:
For any diagonal frame unit `u : Fin 3 → Bˣ` and any operator matrix `X : Matrix (Fin 3) (Fin 3) B`
over a non-commutative star-ring `[Ring B] [StarRing B]`, all five Peirce–KKT grade projections
(`peirceGradePlus2`, `peirceGradePlus1`, `peirceGradeZero`, `peirceGradeMinus1`, `peirceGradeMinus2`)
commute directly with inner conjugation `X ↦ U * X * U⁻¹` by `U = diagonalFrameUnit u`. -/
theorem peirceGrade_five_sector_diagonalConjugation_equivariance
    (u : Fin 3 → Bˣ) (X : Matrix (Fin 3) (Fin 3) B) :
    let U : Matrix (Fin 3) (Fin 3) B := diagonalFrameUnit u
    let U_inv : Matrix (Fin 3) (Fin 3) B := ↑((diagonalFrameUnit u)⁻¹)
    peirceGradePlus2 (Nplus3 (B := B)) (U * X * U_inv) =
      U * peirceGradePlus2 (Nplus3 (B := B)) X * U_inv ∧
    peirceGradePlus1 (Nplus3 (B := B)) (U * X * U_inv) =
      U * peirceGradePlus1 (Nplus3 (B := B)) X * U_inv ∧
    peirceGradeZero (Nplus3 (B := B)) (U * X * U_inv) =
      U * peirceGradeZero (Nplus3 (B := B)) X * U_inv ∧
    peirceGradeMinus1 (Nplus3 (B := B)) (U * X * U_inv) =
      U * peirceGradeMinus1 (Nplus3 (B := B)) X * U_inv ∧
    peirceGradeMinus2 (Nplus3 (B := B)) (U * X * U_inv) =
      U * peirceGradeMinus2 (Nplus3 (B := B)) X * U_inv := by
  dsimp only
  have hU := nplus3_sheets_comm_diagonal (B := B) (fun i => (u i : B))
  have hUinv := nplus3_sheets_comm_diagonal (B := B) (fun i => (((u i)⁻¹ : Bˣ) : B))
  have hPU :
      InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.P (Nplus3 (B := B)) *
        (diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) =
      (diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.P (Nplus3 (B := B)) := hU.1
  have hQU :
      InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.Q (Nplus3 (B := B)) *
        (diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) =
      (diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.Q (Nplus3 (B := B)) := hU.2.1
  have hRU :
      peirceR (Nplus3 (B := B)) * (diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) =
      (diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) * peirceR (Nplus3 (B := B)) := hU.2.2
  have hPUinv :
      InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.P (Nplus3 (B := B)) *
        (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B) =
      (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.P (Nplus3 (B := B)) := hUinv.1
  have hQUinv :
      InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.Q (Nplus3 (B := B)) *
        (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B) =
      (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.Q (Nplus3 (B := B)) := hUinv.2.1
  have hRUinv :
      peirceR (Nplus3 (B := B)) * (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B) =
      (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B) * peirceR (Nplus3 (B := B)) := hUinv.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [peirceGradePlus2, peircePQ]
    exact sandwich_comm_of_comm hPU hQUinv
  · dsimp [peirceGradePlus1, peircePR, peirceRQ]
    rw [sandwich_comm_of_comm hPU hRUinv, sandwich_comm_of_comm hRU hQUinv]
    noncomm_ring
  · dsimp [peirceGradeZero, peircePP, peirceQQ, peirceRR]
    rw [sandwich_comm_of_comm hPU hPUinv, sandwich_comm_of_comm hQU hQUinv,
      sandwich_comm_of_comm hRU hRUinv]
    noncomm_ring
  · dsimp [peirceGradeMinus1, peirceRP, peirceQR]
    rw [sandwich_comm_of_comm hRU hPUinv, sandwich_comm_of_comm hQU hRUinv]
    noncomm_ring
  · dsimp [peirceGradeMinus2, peirceQP]
    exact sandwich_comm_of_comm hQU hPUinv

omit [StarRing B] in
/-- **Trap T16 Witness 1**: Non-commutativity of the $2 \times 2$ affine semidirect group `affGroup2`
over any `[Nontrivial B]`. -/
theorem affGroup2_noncommute_witness [Nontrivial B] :
    affGroup2 (1 : B) 1 * affGroup2 0 1 ≠ affGroup2 0 1 * affGroup2 (1 : B) 1 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [affGroup2, Matrix.mul_apply, Fin.sum_univ_two] at h01

omit [StarRing B] in
/-- **Trap T16 Witness 2**: Non-commutativity of the $3 \times 3$ Kaluza–Janus group `janusGroup3`
over any `[Nontrivial B]`. -/
theorem janusGroup3_noncommute_witness [Nontrivial B] :
    janusGroup3 (1 : B) 0 1 1 * janusGroup3 1 0 0 1 ≠
      janusGroup3 1 0 0 1 * janusGroup3 (1 : B) 0 1 1 := by
  intro h
  have h12 := congr_fun (congr_fun h 1) 2
  simp [janusGroup3, Matrix.mul_apply, Fin.sum_univ_three] at h12

omit [StarRing B] in
/-- **Trap T16 Witness 3**: Non-commutativity of the bimetric coupling operator
`bimetricCoupling2 1 1` with the Peirce idempotent `peirceProj2` over any `[Nontrivial B]`. -/
theorem bimetricCoupling2_noncommute_with_peirceProj2 [Nontrivial B] :
    bimetricCoupling2 (1 : B) 1 * peirceProj2 (B := B) ≠
      peirceProj2 (B := B) * bimetricCoupling2 (1 : B) 1 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [bimetricCoupling2, peirceProj2, Matrix.mul_apply, Fin.sum_univ_two] at h01

end ArchetypeJ4

/-! ===========================================================================
    Section 6: Archetype J5 — Master Solve-et-Coagula Synthesis
    =========================================================================== -/

section MasterSynthesis

variable {B : Type*} [Ring B] [StarRing B]

/-- **Master Souriau–Kaluza–Janus–Bimetric `solve et coagula` Theorem**:
Coagulates the 6-stage acyclic causal poset `JanusBimetricEpistemicStage` ($\mathcal{J}_0 \prec \dots \prec \mathcal{J}_5$),
the $2 \times 2$ Souriau moment torsor congruence ($\mathcal{J}_0$),
the $3 \times 3$ Kaluza–Janus double semidirect group and Lie adjoint action ($\mathcal{J}_1$),
the Souriau–Noether trace duality and coadjoint equivariance ($\mathcal{J}_2$),
the Krein-graded bimetric coupling nilpotency, Bianchi conservation law, and Cartan pressure
reversal ($\mathcal{J}_3$), and the Peirce–Krein / 3-sheet KKT / operator-Zorn bridges ($\mathcal{J}_4$)
into a single kernel-verified theorem. -/
theorem souriau_kaluza_janus_bimetric_solve_et_coagula_master_synthesis
    {χ χ_inv L L_inv b₁ b₂ : B}
    (φ C M P q Ω γ δφ T_plus T_minus ρ p : B)
    (hχ_left : χ_inv * χ = 1) (hL_left : L_inv * L = 1)
    (hχ_right : χ * χ_inv = 1) (hL_right : L * L_inv = 1)
    (hb₁₂ : b₁ * b₂ = 1) (hb₂₁ : b₂ * b₁ = 1) :
    -- (0) Acyclic causal poset J0 < J1 < J2 < J3 < J4 < J5
    ((∀ st : JanusBimetricEpistemicStage,
        ¬ Relation.TransGen JanusBimetricEpistemicStage.causalEdge st st) ∧
     JanusBimetricEpistemicStage.causalEdge
       .J0_PrimordialBinaryCutAndSouriauMomentCongruence
       .J1_FourfoldAnatomyAndKaluzaJanusDoubleSemidirectAdjoint ∧
     JanusBimetricEpistemicStage.causalEdge
       .J4_PeirceKreinKKTZornTwistorBridge
       .J5_MasterSouriauKaluzaJanusBimetricCoagulation) ∧
    -- (1) Archetype J0: 2×2 Souriau moment torsor star-congruence & discrete reversal
    (affInv2 L_inv C * affGroup2 L C = 1 ∧
     affGroup2 L C * affInv2 L_inv C = 1 ∧
     affGroup2 L C * momentTorsor2 M P * (affGroup2 L C)ᴴ =
       momentTorsor2 (L * M * star L - L * P * star C + C * star (L * P)) (L * P) ∧
     affGroup2 (-1 : B) 0 * momentTorsor2 M P * (affGroup2 (-1 : B) 0)ᴴ =
       momentTorsor2 M (-P)) ∧
    -- (2) Archetype J1: 3×3 Kaluza–Janus group inverse, Lie adjoint action & radical nilpotency
    (janusInv3 χ_inv φ L_inv C * janusGroup3 χ φ L C = 1 ∧
     janusGroup3 χ φ L C * janusInv3 χ_inv φ L_inv C = 1 ∧
     janusInv3 χ_inv φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 χ φ L C =
       janusLie3 (L_inv * Ω * L) (L_inv * Ω * C + L_inv * γ) (χ_inv * δφ) ∧
     janusLie3 0 γ δφ * janusLie3 0 γ δφ = 0) ∧
    -- (3) Archetype J2: Souriau–Noether trace pairing, coadjoint sectors & contragredient defect
    (Matrix.trace (janusDualMoment3 M P q * janusLie3 Ω γ δφ) =
       M * Ω + P * γ + q * δφ ∧
     (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) 2 0 = q * χ ∧
     (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) 2 1 = P * L ∧
     (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) 1 1 =
       L_inv * M * L - L_inv * C * P * L ∧
     Matrix.trace
         (janusDualMoment3 (M - P * C) P (q * χ) *
           (janusInv3 χ_inv φ 1 C * janusLie3 Ω γ δφ * janusGroup3 χ φ 1 C)) =
       (M * Ω + P * γ + q * δφ) + P * OperatorAlgebra.PeirceSpine.comm Ω C) ∧
    -- (4) Archetype J3: Bimetric coupling nilpotency, Bianchi conservation & Cartan pressure flip
    (bimetricCoupling2 b₁ b₂ * bimetricCoupling2 b₁ b₂ = 0 ∧
     Matrix.trace (bimetricCoupling2 b₁ b₂) = 0 ∧
     b₂ * (T_plus + b₁ * T_minus) + (-(b₂ * T_plus) - T_minus) = 0 ∧
     cartanEz2 * stressSelf2 ρ p = stressInduced2 ρ p) ∧
    -- (5) Archetype J4: Peirce–Krein, 3-sheet KKT & operator-Zorn bridges
    (bimetricCoupling2 b₁ b₂ =
       invS (peirceProj2 (B := B)) +
         conePlus (peirceProj2 (B := B)) !![0, b₁; 0, 0] -
         coneMinus (peirceProj2 (B := B)) !![0, 0; b₂, 0] ∧
     matrix3ToOpZorn (janusLie3 Ω γ δφ) =
       opGradeZero 0 Ω + opGradePlus1 δφ 0 + opGradeMinus1 γ 0 ∧
     matrix3ToOpZorn (janusDualMoment3 M P q) =
       opGradeZero 0 M + opGradePlus1 0 P + opGradeMinus1 0 q) := by
  refine ⟨⟨JanusBimetricEpistemicStage.causalEdge_acyclic,
           JanusBimetricEpistemicStage.causalEdge_chain.1,
           JanusBimetricEpistemicStage.causalEdge_chain.2.2.2.2⟩,
          ⟨affInv2_mul_affGroup2 C hL_left,
           affGroup2_mul_affInv2 C hL_right,
           momentTorsor2_coadjoint_congruence L C M P,
           momentTorsor2_discrete_inversion M P⟩,
          ⟨janusInv3_mul_janusGroup3 φ C hχ_left hL_left,
           janusGroup3_mul_janusInv3 φ C hχ_right hL_right,
           janusLie3_adjoint_action χ χ_inv φ L L_inv C Ω γ δφ,
           janusLie3_radical_sq_zero γ δφ⟩,
          ⟨janus_noether_trace_pairing M P q Ω γ δφ,
           (janus_coadjoint_moment_sectors χ χ_inv φ L L_inv C M P q).1,
           (janus_coadjoint_moment_sectors χ χ_inv φ L L_inv C M P q).2.1,
           (janus_coadjoint_moment_sectors χ χ_inv φ L L_inv C M P q).2.2,
           janus_noether_contragredient_translation_defect φ C M P q Ω γ δφ hχ_right⟩,
          ⟨bimetricCoupling2_sq_zero hb₁₂ hb₂₁,
           bimetricCoupling2_trace_zero b₁ b₂,
           bimetric_bianchi_conservation_zero T_plus T_minus hb₂₁,
           cartanEz2_mul_stressSelf2 ρ p⟩,
          ⟨bimetricCoupling2_peirce_decomposition b₁ b₂,
           (janus_zorn_five_grade_projections Ω γ δφ M P q).1,
           (janus_zorn_five_grade_projections Ω γ δφ M P q).2⟩⟩

end MasterSynthesis

end InfoGeometry.Canonical.SouriauKaluzaJanusBimetricSolveEtCoagula
