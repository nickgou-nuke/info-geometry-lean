/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Algebraic.CartanSouriauAffineCocycle
import InfoGeometry.Epistemology.JungianEpistemicCompiler
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge

/-!
# Non-Commutative Souriau Moment Maps, 3×3 Kaluza–Janus Extensions & Bimetric Operator Poset

This module executes the **Epistemic Compiler (`solve et coagula`)** on the pure mathematical
archetypes underlying non-commutative Souriau coadjoint moment torsors, $3 \times 3$
Kaluza–Janus double semidirect extensions, 5-graded Peirce–Kantor–Koecher–Tits trace pairings,
Krein-graded bimetric operator systems, Order-3 Jacobson–Morozov Lagrange sheet reconstructions,
and $4 \times 4$ Plücker–Hodge Nambu anomalies in native Mathlib (`Matrix (Fin n) (Fin n) B`).

## Acyclic Causal Poset (`SouriauKaluzaJanusStage`)

$$\mathcal{J}_0 \prec \mathcal{J}_1 \prec \mathcal{J}_2 \prec \mathcal{J}_3 \prec \mathcal{J}_4 \prec \mathcal{J}_5$$

1. **Stage $\mathcal{J}_0$ (`J0_SouriauPoincareMomentTorsor`)**:
   Upper-triangular $2 \times 2$ affine group `affGroup2 L C` and Souriau coadjoint moment torsor
   `souriauMoment2 M P` in `Matrix (Fin 2) (Fin 2) B` (`[Ring B] [StarRing B]`), proving the
   non-commutative Souriau coadjoint congruence
   $$g \cdot \mu(M, P) \cdot g^{\mathrm{H}} =
     \mu\!\bigl(L M L^\star - L P C^\star + C (L P)^\star,\; L P\bigr),$$
   time-reversal momentum inversion (`L = -1, C = 0 ↦ μ(M, -P)`), and an explicit bridge to
   `CartanSouriauAffineCocycle.Datum` and `CartanSouriauAffineCocycle.AffineMomentMap`.
2. **Stage $\mathcal{J}_1$ (`J1_KaluzaJanusGroupAndLieAdjoint`)**:
   $3 \times 3$ Kaluza–Janus double semidirect group `janusGroup3 χ φ L C`, two-sided inverse
   `janusInv3 χ_inv φ L_inv C`, and Lie algebra `janusLie3 Ω γ δφ` in `Matrix (Fin 3) (Fin 3) B`,
   proving Lie commutator closure and the non-commutative Adjoint representation
   $$g^{-1} Z(\Omega, \gamma, \delta\varphi) g =
     Z\!\bigl(L^{-1}\Omega L,\; L^{-1}\Omega C + L^{-1}\gamma,\; \chi^{-1}\delta\varphi\bigr).$$
3. **Stage $\mathcal{J}_2$ (`J2_SouriauNoetherTraceAndThreeSheetPeirce`)**:
   Dual moment matrix `janusDualMoment3 M P q` in `Matrix (Fin 3) (Fin 3) B`, proving the
   Souriau–Noether duality pairing as native `Matrix.trace (μ * Z) = M * Ω + P * γ + q * δφ`,
   coadjoint equivariance, the exact non-commutative translational trace anomaly
   $$\mathrm{Tr}\!\bigl(g_1^{-1} (\mu Z) g_1\bigr) =
     (M \Omega + P \gamma + q \delta\varphi) - [C, P \Omega],$$
   and the exact 5-graded Peirce-KKT (`MatrixThreeSheetKKTRealization`) and operator-Zorn
   (`matrix3ToOpZorn`) decomposition showing that the Souriau trace pairing is the sum of
   opposite-grade `(0,0)`, `(+1,-1)`, and `(-1,+1)` Peirce trace pairings.
4. **Stage $\mathcal{J}_3$ (`J3_KreinBimetricPeirceNilpotencyAndPressureFlip`)**:
   Krein-graded bimetric coupling matrix `janusCoupling2 b₁ b₂ = !![1, b₁; -b₂, -1]` in
   `Matrix (Fin 2) (Fin 2) B`, identifying it with the Peirce–Krein chiral sum
   `invS peirceCut2 + genJ peirceCut2 A C`, proving the universal Peirce identity
   `(invS P + genJ P A C)² = 1 - genV P A C`, strict nilpotency `(janusCoupling2 b₁ b₂)² = 0`
   under reciprocal volume ratio `b₁ * b₂ = 1 ∧ b₂ * b₁ = 1`, the bimetric Bianchi conservation
   law `b₂ * E_+ + E_- = (b₂ * b₁ - 1) * T_-`, and the Cartan grading pressure sign flip.
5. **Stage $\mathcal{J}_4$ (`J4_Order3JacobsonMorozovAndNativeMat4Plucker`)**:
   Order-3 Jacobson–Morozov $\mathfrak{sl}_2$ triple `(jmShiftPlus3, jmShiftMinus3, jmCartan3)`
   on `Matrix (Fin 3) (Fin 3) B` reconstructing the three orthogonal sheet projectors
   `archetypeCut3`, `sheetProj1`, `sheetProj2` via Lagrange interpolation polynomials in `jmCartan3`,
   paired with the native `Matrix (Fin 4) (Fin 4) B` Plücker–Hodge Nambu anomaly theorem.
6. **Stage $\mathcal{J}_5$ (`J5_NecessaryCoagulatedSynthesis`)**:
   Concrete non-commutative witnesses over `Matrix (Fin 2) (Fin 2) ℤ` (`T16`) and the master
   coagulated synthesis theorem across $\mathcal{J}_0 \prec \dots \prec \mathcal{J}_5$.

## i. Overview

Formalizes the 6-stage `SouriauKaluzaJanusStage` poset ($\mathcal{J}_0 \prec \dots \prec \mathcal{J}_5$)
connecting Souriau Poincaré moment torsor congruence, Kaluza–Janus semidirect groups, Noether
trace pairings, Krein bimetric Peirce nilpotency, and Jacobson–Morozov $\mathfrak{sl}_2$ triples.

## ii. Key results

- `souriauMoment2_coadjoint_congruence`
- `janusGroup3_mul`
- `souriauKaluzaJanusStage_causal_chain`

## iii. Table of contents

- Section I: Epistemic Compiler Acyclic Causal Poset (`SouriauKaluzaJanusStage`)
- Sections II–VII: Stages $\mathcal{J}_0$ through $\mathcal{J}_5$

## iv. References

- J.-M. Souriau, *Structure of Dynamical Systems* (1970).

#### BUCKET 1: CLOSED FINITE THEOREMS
- `souriauKaluzaJanusStage_causal_chain`, `affGroup2_one`, `janusGroup3_one`, `peirceCut2_idempotent`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `souriauMoment2_coadjoint_congruence` through Stage $\mathcal{J}_5$ synthesis over `[Ring B]`.

#### BUCKET 3: OPEN CLOSURE DEBT
- Curved pseudo-Riemannian bimetric field equations beyond finite matrix and Peirce operator rings.
-/

namespace InfoGeometry.Canonical.SouriauKaluzaJanusBimetricPoset

open Matrix
open InfoGeometry.Algebraic.CartanSouriauAffineCocycle
open InfoGeometry.Epistemology.JungianEpistemicCompiler
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization
open InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge

/-! ## Section I: Epistemic Compiler Acyclic Causal Poset (`SouriauKaluzaJanusStage`) -/

/-- The six stages of the Souriau–Kaluza–Janus–Bimetric `solve et coagula` poset. -/
inductive SouriauKaluzaJanusStage : Type
  | J0_SouriauPoincareMomentTorsor
  | J1_KaluzaJanusGroupAndLieAdjoint
  | J2_SouriauNoetherTraceAndThreeSheetPeirce
  | J3_KreinBimetricPeirceNilpotencyAndPressureFlip
  | J4_Order3JacobsonMorozovAndNativeMat4Plucker
  | J5_NecessaryCoagulatedSynthesis
  deriving DecidableEq, Repr

instance instInhabitedSouriauKaluzaJanusStage : Inhabited SouriauKaluzaJanusStage :=
  ⟨.J0_SouriauPoincareMomentTorsor⟩

/-- Topological causal rank of each stage in `SouriauKaluzaJanusStage`. -/
def SouriauKaluzaJanusStage.rank : SouriauKaluzaJanusStage → Nat
  | .J0_SouriauPoincareMomentTorsor => 0
  | .J1_KaluzaJanusGroupAndLieAdjoint => 1
  | .J2_SouriauNoetherTraceAndThreeSheetPeirce => 2
  | .J3_KreinBimetricPeirceNilpotencyAndPressureFlip => 3
  | .J4_Order3JacobsonMorozovAndNativeMat4Plucker => 4
  | .J5_NecessaryCoagulatedSynthesis => 5

/-- `SouriauKaluzaJanusStage.rank` is injective. -/
theorem SouriauKaluzaJanusStage.rank_injective :
    Function.Injective SouriauKaluzaJanusStage.rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instPartialOrderSouriauKaluzaJanusStage : PartialOrder SouriauKaluzaJanusStage where
  le a b := a.rank ≤ b.rank
  lt a b := a.rank < b.rank
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  le_antisymm _ _ hab hba :=
    SouriauKaluzaJanusStage.rank_injective (Nat.le_antisymm hab hba)
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge

/-- Complete strict acyclic causal chain $\mathcal{J}_0 \prec \mathcal{J}_1 \prec \mathcal{J}_2 \prec \mathcal{J}_3 \prec \mathcal{J}_4 \prec \mathcal{J}_5$. -/
theorem souriauKaluzaJanusStage_causal_chain :
    SouriauKaluzaJanusStage.J0_SouriauPoincareMomentTorsor <
      SouriauKaluzaJanusStage.J1_KaluzaJanusGroupAndLieAdjoint ∧
    SouriauKaluzaJanusStage.J1_KaluzaJanusGroupAndLieAdjoint <
      SouriauKaluzaJanusStage.J2_SouriauNoetherTraceAndThreeSheetPeirce ∧
    SouriauKaluzaJanusStage.J2_SouriauNoetherTraceAndThreeSheetPeirce <
      SouriauKaluzaJanusStage.J3_KreinBimetricPeirceNilpotencyAndPressureFlip ∧
    SouriauKaluzaJanusStage.J3_KreinBimetricPeirceNilpotencyAndPressureFlip <
      SouriauKaluzaJanusStage.J4_Order3JacobsonMorozovAndNativeMat4Plucker ∧
    SouriauKaluzaJanusStage.J4_Order3JacobsonMorozovAndNativeMat4Plucker <
      SouriauKaluzaJanusStage.J5_NecessaryCoagulatedSynthesis := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## Section II: Stage $\mathcal{J}_0$ — $2 \times 2$ Affine Group, Souriau Moment Torsor Congruence & `CartanSouriauAffineCocycle` Bridge -/

section StageJ0

variable {B : Type*} [Ring B]

/-- Positive $2 \times 2$ nilpotent matrix unit $E_{01}$. -/
def Nplus2 : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; 0, 0]

/-- Negative $2 \times 2$ nilpotent matrix unit $E_{10}$. -/
def Nminus2 : Matrix (Fin 2) (Fin 2) B :=
  !![0, 0; 1, 0]

/-- Non-commutativity of the $2 \times 2$ matrix units over any nontrivial ring `B`. -/
theorem Nplus2_mul_Nminus2_ne [Nontrivial B] :
    Nplus2 (B := B) * Nminus2 ≠ Nminus2 * Nplus2 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h
  simp [Nplus2, Nminus2] at h00

/-- Upper-triangular $2 \times 2$ affine/Poincaré group element
$$\mathrm{affGroup2}(L, C) = \begin{pmatrix} L & C \\ 0 & 1 \end{pmatrix}$$
in native Mathlib `Matrix (Fin 2) (Fin 2) B`. -/
def affGroup2 (L C : B) : Matrix (Fin 2) (Fin 2) B :=
  !![L, C; 0, 1]

/-- Candidate two-sided inverse of `affGroup2 L C` given an inverse `L_inv` of `L`:
$$\mathrm{affInv2}(L^{-1}, C) = \begin{pmatrix} L^{-1} & -L^{-1} C \\ 0 & 1 \end{pmatrix}.$$ -/
def affInv2 (L_inv C : B) : Matrix (Fin 2) (Fin 2) B :=
  !![L_inv, -(L_inv * C); 0, 1]

/-- Souriau coadjoint moment torsor in `Matrix (Fin 2) (Fin 2) B`:
$$\mu(M, P) = \begin{pmatrix} M & -P \\ P^\star & 0 \end{pmatrix}.$$ -/
def souriauMoment2 [StarRing B] (M P : B) : Matrix (Fin 2) (Fin 2) B :=
  !![M, -P; star P, 0]

/-- `affGroup2 1 0` is the $2 \times 2$ identity matrix. -/
theorem affGroup2_one : affGroup2 (1 : B) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [affGroup2]

/-- Semidirect product group law:
`affGroup2 L₁ C₁ * affGroup2 L₂ C₂ = affGroup2 (L₁ * L₂) (L₁ * C₂ + C₁)`. -/
theorem affGroup2_mul (L₁ C₁ L₂ C₂ : B) :
    affGroup2 L₁ C₁ * affGroup2 L₂ C₂ =
      affGroup2 (L₁ * L₂) (L₁ * C₂ + C₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affGroup2, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Left inversion law for `affGroup2` when `L_inv * L = 1`. -/
theorem affInv2_mul_affGroup2 (L L_inv C : B) (hL : L_inv * L = 1) :
    affInv2 L_inv C * affGroup2 L C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affGroup2, affInv2, Matrix.mul_apply, Fin.sum_univ_succ, hL]

/-- Right inversion law for `affGroup2` when `L * L_inv = 1`. -/
theorem affGroup2_mul_affInv2 (L L_inv C : B) (hR : L * L_inv = 1) :
    affGroup2 L C * affInv2 L_inv C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [affGroup2, affInv2, Matrix.mul_apply, Fin.sum_univ_succ, hR]
  · simp [affGroup2, affInv2, Matrix.mul_apply, Fin.sum_univ_succ]
    calc
      -(L * (L_inv * C)) + C = -((L * L_inv) * C) + C := by rw [mul_assoc]
      _ = -(1 * C) + C := by rw [hR]
      _ = 0 := by simp
  · simp [affGroup2, affInv2, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [affGroup2, affInv2, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Skew-Hermitian symmetry of `souriauMoment2 M P` under Mathlib's conjugate transpose `Xᴴ`
whenever the angular momentum block is skew-adjoint (`star M = -M`). -/
theorem souriauMoment2_conjTranspose_skew [StarRing B] (M P : B) (hM : star M = -M) :
    (souriauMoment2 M P)ᴴ = -souriauMoment2 M P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [souriauMoment2, Matrix.conjTranspose_apply, hM]

/-- **Archetype $\mathcal{J}_0$ (Non-Commutative Souriau Coadjoint Moment Torsor Congruence)**:
Over any `[Ring B] [StarRing B]`, the upper-triangular affine group `affGroup2 L C` acts on
`souriauMoment2 M P` by matrix congruence `g * μ * gᴴ`, transforming energy-momentum linearly as
`P' = L * P` and angular momentum affinely by the non-commutative Souriau 1-cocycle shift:
$$M' = L M L^\star - L P C^\star + C (L P)^\star.$$ -/
theorem souriauMoment2_coadjoint_congruence [StarRing B] (L C M P : B) :
    affGroup2 L C * souriauMoment2 M P * (affGroup2 L C)ᴴ =
      souriauMoment2 (L * M * star L - L * P * star C + C * star (L * P)) (L * P) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [affGroup2, souriauMoment2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]
    noncomm_ring
  · simp [affGroup2, souriauMoment2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]
  · simp [affGroup2, souriauMoment2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]
  · simp [affGroup2, souriauMoment2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]

/-- Pure reflection / time-reversal (`L = -1, C = 0`) reverses the energy-momentum block
`P ↦ -P` while preserving the angular momentum block `M ↦ +M`. -/
theorem souriauMoment2_time_reflection_energy_flip [StarRing B] (M P : B) :
    affGroup2 (-1 : B) 0 * souriauMoment2 M P * (affGroup2 (-1 : B) 0)ᴴ =
      souriauMoment2 M (-P) := by
  rw [souriauMoment2_coadjoint_congruence]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [souriauMoment2]

/-- **Socratic Aporia 0**: When translations vanish (`C = 0`), the affine orbital cross-torque
`-L * P * star C + C * star (L * P)` collapses identically to `0`. -/
theorem souriauMoment2_socratic_aporia_zero_translation [StarRing B] (L M P : B) :
    affGroup2 L 0 * souriauMoment2 M P * (affGroup2 L 0)ᴴ =
      souriauMoment2 (L * M * star L) (L * P) := by
  rw [souriauMoment2_coadjoint_congruence]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [souriauMoment2]

/-- The Souriau translational 1-cocycle $\theta_{P_0}(C) = C P_0^\star - P_0 C^\star$ for a fixed
momentum $P_0 \in B$, organized as a `CartanSouriauAffineCocycle.Datum` over the additive
translation group `G = Multiplicative B` acting on `M = B`. -/
def souriauTranslationDatum [StarRing B] (P₀ : B) :
    Datum (G := Multiplicative B) (M := B) where
  dualAction _ := AddMonoidHom.id B
  dualAction_one := rfl
  dualAction_mul _ _ := rfl
  theta c := Multiplicative.toAdd c * star P₀ - P₀ * star (Multiplicative.toAdd c)
  theta_one := by
    change (0 : B) * star P₀ - P₀ * star (0 : B) = 0
    simp
  theta_mul g h := by
    change (Multiplicative.toAdd g + Multiplicative.toAdd h) * star P₀ -
        P₀ * star (Multiplicative.toAdd g + Multiplicative.toAdd h) =
      (Multiplicative.toAdd g * star P₀ - P₀ * star (Multiplicative.toAdd g)) +
        (Multiplicative.toAdd h * star P₀ - P₀ * star (Multiplicative.toAdd h))
    rw [star_add]
    noncomm_ring

/-- Explicit `CartanSouriauAffineCocycle.AffineMomentMap` witnessing the translational Souriau
moment shift on angular momentum `M : B`. -/
def souriauTranslationMomentMap [StarRing B] (P₀ : B) :
    AffineMomentMap (souriauTranslationDatum P₀) B where
  stateAction g M := affineAction (souriauTranslationDatum P₀) g M
  stateAction_one := by
    funext M
    exact affineAction_one (souriauTranslationDatum P₀) M
  stateAction_mul g h := by
    funext M
    exact affineAction_mul (souriauTranslationDatum P₀) g h M
  moment := id
  moment_affine_equivariant _ _ := rfl

/-- **Bridge ($\mathcal{J}_0 \leftrightarrow$ `CartanSouriauAffineCocycle`)**:
For pure translations `affGroup2 1 C`, the $2 \times 2$ Souriau matrix congruence on
`souriauMoment2 M P₀` coincides with `CartanSouriauAffineCocycle.affineAction` of
`souriauTranslationDatum P₀`. -/
theorem affGroup2_translation_congruence_eq_affineAction [StarRing B] (C M P₀ : B) :
    affGroup2 1 C * souriauMoment2 M P₀ * (affGroup2 1 C)ᴴ =
      souriauMoment2
        (affineAction (souriauTranslationDatum P₀) (Multiplicative.ofAdd C) M) P₀ := by
  rw [souriauMoment2_coadjoint_congruence]
  congr 1
  · change 1 * M * star (1 : B) - 1 * P₀ * star C + C * star (1 * P₀) =
      M + (C * star P₀ - P₀ * star C)
    simp only [one_mul, star_one, mul_one]
    noncomm_ring
  · exact one_mul P₀

end StageJ0

/-! ## Section III: Stage $\mathcal{J}_1$ — $3 \times 3$ Kaluza–Janus Double Semidirect Group, Lie Bracket Closure & Non-Commutative Adjoint Action -/

section StageJ1

variable {B : Type*} [Ring B]

/-- The $3 \times 3$ Kaluza–Janus group element in `Matrix (Fin 3) (Fin 3) B`:
$$\mathrm{janusGroup3}(\chi, \varphi, L, C) =
  \begin{pmatrix} \chi & 0 & \varphi \\ 0 & L & C \\ 0 & 0 & 1 \end{pmatrix}.$$ -/
def janusGroup3 (χ φ L C : B) : Matrix (Fin 3) (Fin 3) B :=
  !![χ, 0, φ; 0, L, C; 0, 0, 1]

/-- Candidate two-sided inverse of `janusGroup3 χ φ L C`:
$$\mathrm{janusInv3}(\chi^{-1}, \varphi, L^{-1}, C) =
  \begin{pmatrix} \chi^{-1} & 0 & -\chi^{-1}\varphi \\ 0 & L^{-1} & -L^{-1}C \\ 0 & 0 & 1 \end{pmatrix}.$$ -/
def janusInv3 (χ_inv φ L_inv C : B) : Matrix (Fin 3) (Fin 3) B :=
  !![χ_inv, 0, -(χ_inv * φ); 0, L_inv, -(L_inv * C); 0, 0, 1]

/-- Lie algebra element of the Kaluza–Janus group in `Matrix (Fin 3) (Fin 3) B`:
$$Z(\Omega, \gamma, \delta\varphi) =
  \begin{pmatrix} 0 & 0 & \delta\varphi \\ 0 & \Omega & \gamma \\ 0 & 0 & 0 \end{pmatrix}.$$ -/
def janusLie3 (Ω γ δφ : B) : Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, δφ; 0, Ω, γ; 0, 0, 0]

/-- Canonical lower-right $2 \times 2 \hookrightarrow 3 \times 3$ block embedding of `affGroup2 L C`
into `janusGroup3 1 0 L C`. -/
def embedAffToJanus3 (L C : B) : Matrix (Fin 3) (Fin 3) B :=
  janusGroup3 1 0 L C

/-- `janusGroup3 1 0 1 0` is the $3 \times 3$ identity matrix. -/
theorem janusGroup3_one : janusGroup3 (1 : B) 0 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [janusGroup3]

/-- Double semidirect product multiplication law for `janusGroup3`. -/
theorem janusGroup3_mul (χ₁ φ₁ L₁ C₁ χ₂ φ₂ L₂ C₂ : B) :
    janusGroup3 χ₁ φ₁ L₁ C₁ * janusGroup3 χ₂ φ₂ L₂ C₂ =
      janusGroup3 (χ₁ * χ₂) (χ₁ * φ₂ + φ₁) (L₁ * L₂) (L₁ * C₂ + C₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusGroup3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The block embedding `embedAffToJanus3` is a multiplicative homomorphism matching `affGroup2_mul`. -/
theorem embedAffToJanus3_mul (L₁ C₁ L₂ C₂ : B) :
    embedAffToJanus3 L₁ C₁ * embedAffToJanus3 L₂ C₂ =
      embedAffToJanus3 (L₁ * L₂) (L₁ * C₂ + C₁) := by
  simp [embedAffToJanus3, janusGroup3_mul]

/-- Left inversion law: `janusInv3 χ_inv φ L_inv C * janusGroup3 χ φ L C = 1`
when `χ_inv * χ = 1` and `L_inv * L = 1`. -/
theorem janusInv3_mul_janusGroup3 (χ χ_inv φ L L_inv C : B)
    (hχ : χ_inv * χ = 1) (hL : L_inv * L = 1) :
    janusInv3 χ_inv φ L_inv C * janusGroup3 χ φ L C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ, hχ, hL]

/-- Right inversion law: `janusGroup3 χ φ L C * janusInv3 χ_inv φ L_inv C = 1`
when `χ * χ_inv = 1` and `L * L_inv = 1`. -/
theorem janusGroup3_mul_janusInv3 (χ χ_inv φ L L_inv C : B)
    (hχ : χ * χ_inv = 1) (hL : L * L_inv = 1) :
    janusGroup3 χ φ L C * janusInv3 χ_inv φ L_inv C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ, hχ]
  · simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ]
    calc
      -(χ * (χ_inv * φ)) + φ = -((χ * χ_inv) * φ) + φ := by rw [mul_assoc]
      _ = -(1 * φ) + φ := by rw [hχ]
      _ = 0 := by simp
  · simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ, hL]
  · simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ]
    calc
      -(L * (L_inv * C)) + C = -((L * L_inv) * C) + C := by rw [mul_assoc]
      _ = -(1 * C) + C := by rw [hL]
      _ = 0 := by simp
  · simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [janusGroup3, janusInv3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Lie algebra commutator closure of `janusLie3`:
$$[Z(\Omega_1, \gamma_1, \delta\varphi_1),\, Z(\Omega_2, \gamma_2, \delta\varphi_2)] =
  Z([\Omega_1, \Omega_2],\, \Omega_1\gamma_2 - \Omega_2\gamma_1,\, 0).$$ -/
theorem janusLie3_comm_closure (Ω₁ γ₁ δφ₁ Ω₂ γ₂ δφ₂ : B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (janusLie3 Ω₁ γ₁ δφ₁) (janusLie3 Ω₂ γ₂ δφ₂) =
      janusLie3 (InfoGeometry.OperatorAlgebra.PeirceSpine.comm Ω₁ Ω₂)
        (Ω₁ * γ₂ - Ω₂ * γ₁) 0 := by
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusLie3]

/-- **Archetype $\mathcal{J}_1$ (Non-Commutative Adjoint Action on the Kaluza–Janus Lie Algebra)**:
Conjugation of `janusLie3 Ω γ δφ` by `janusGroup3 χ φ L C` acts by:
$$\Omega' = L^{-1}\Omega L, \qquad \gamma' = L^{-1}\Omega C + L^{-1}\gamma, \qquad \delta\varphi' = \chi^{-1}\delta\varphi.$$ -/
theorem janusLie3_adjoint_action (χ χ_inv φ L L_inv C Ω γ δφ : B) :
    janusInv3 χ_inv φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 χ φ L C =
      janusLie3 (L_inv * Ω * L) (L_inv * Ω * C + L_inv * γ) (χ_inv * δφ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusGroup3, janusInv3, janusLie3, Matrix.mul_apply, Fin.sum_univ_three]

/-- In the reflective Janus sector (`χ = -1, χ_inv = -1`), the 5th-dimension gauge velocity reverses
sign (`δφ ↦ -δφ`) under Adjoint conjugation. -/
theorem janusLie3_charge_inversion (φ L L_inv C Ω γ δφ : B) :
    janusInv3 (-1 : B) φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 (-1 : B) φ L C =
      janusLie3 (L_inv * Ω * L) (L_inv * Ω * C + L_inv * γ) (-δφ) := by
  rw [janusLie3_adjoint_action]
  simp

end StageJ1

/-! ## Section IV: Stage $\mathcal{J}_2$ — Souriau–Noether `Matrix.trace` Duality Pairing, Coadjoint Equivariance, Commutator Anomaly & 5-Graded Peirce-KKT Bridge -/

section StageJ2

variable {B : Type*} [Ring B]

/-- Dual moment matrix in `Matrix (Fin 3) (Fin 3) B` carrying angular momentum `M` at `(1,1)`,
energy-momentum `P` at `(2,1)`, and gauge charge `q` at `(2,0)`:
$$\mu(M, P, q) = \begin{pmatrix} 0 & 0 & 0 \\ 0 & M & 0 \\ q & P & 0 \end{pmatrix}.$$ -/
def janusDualMoment3 (M P q : B) : Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, 0; 0, M, 0; q, P, 0]

/-- **Souriau–Noether Duality Pairing as Native `Matrix.trace`**:
$$\mathrm{Tr}\!\bigl(\mu(M, P, q) \cdot Z(\Omega, \gamma, \delta\varphi)\bigr) =
  M \Omega + P \gamma + q \delta\varphi.$$ -/
theorem souriau_noether_trace_pairing (M P q Ω γ δφ : B) :
    Matrix.trace (janusDualMoment3 M P q * janusLie3 Ω γ δφ) =
      M * Ω + P * γ + q * δφ := by
  simp [Matrix.trace, Matrix.diag, janusDualMoment3, janusLie3,
    Matrix.mul_apply, Fin.sum_univ_succ]
  abel

/-- Explicit transformed coadjoint blocks of
`μ' = janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C`:
- Charge block `(2,0)`: `q' = q * χ`,
- Energy-momentum block `(2,1)`: `P' = P * L`,
- Angular momentum block `(1,1)`: `M' = L_inv * M * L - L_inv * C * P * L`. -/
theorem janusDualMoment3_coadjoint_entries (χ χ_inv φ L L_inv C M P q : B) :
    let μ' := janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C
    μ' 2 0 = q * χ ∧
    μ' 2 1 = P * L ∧
    μ' 1 1 = L_inv * M * L - L_inv * C * P * L := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · simp [janusGroup3, janusInv3, janusDualMoment3, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [janusGroup3, janusInv3, janusDualMoment3, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [janusGroup3, janusInv3, janusDualMoment3, Matrix.mul_apply, Fin.sum_univ_three]
    noncomm_ring

/-- Simultaneous Janus inversion (`χ = -1, L = -1`) reverses both electric charge (`q ↦ -q`)
and energy-momentum (`P ↦ -P`), while shifting angular momentum to `M - C * P`. -/
theorem janusDualMoment3_coadjoint_charge_time_flip (φ C M P q : B) :
    let μ' := janusInv3 (-1 : B) φ (-1 : B) C *
      janusDualMoment3 M P q * janusGroup3 (-1 : B) φ (-1 : B) C
    μ' 2 0 = -q ∧
    μ' 2 1 = -P ∧
    μ' 1 1 = M - C * P := by
  rcases janusDualMoment3_coadjoint_entries (-1 : B) (-1 : B) φ (-1 : B) (-1 : B) C M P q with
    ⟨h20, h21, h11⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa using h20
  · simpa using h21
  · simpa [sub_eq_add_neg] using h11

/-- Full matrix conjugation equivariance of the product `(g⁻¹ * μ * g) * (g⁻¹ * Z * g) = g⁻¹ * (μ * Z) * g`
whenever `χ * χ_inv = 1` and `L * L_inv = 1`. -/
theorem janus_coadjoint_adjoint_product_equivariance
    (χ χ_inv φ L L_inv C M P q Ω γ δφ : B)
    (hχR : χ * χ_inv = 1) (hLR : L * L_inv = 1) :
    (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) *
      (janusInv3 χ_inv φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 χ φ L C) =
    janusInv3 χ_inv φ L_inv C *
      (janusDualMoment3 M P q * janusLie3 Ω γ δφ) * janusGroup3 χ φ L C := by
  have hgid : janusGroup3 χ φ L C * janusInv3 χ_inv φ L_inv C = 1 :=
    janusGroup3_mul_janusInv3 χ χ_inv φ L L_inv C hχR hLR
  calc
    (janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q * janusGroup3 χ φ L C) *
        (janusInv3 χ_inv φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 χ φ L C)
      = janusInv3 χ_inv φ L_inv C * janusDualMoment3 M P q *
          (janusGroup3 χ φ L C * janusInv3 χ_inv φ L_inv C) *
          janusLie3 Ω γ δφ * janusGroup3 χ φ L C := by
        simp only [Matrix.mul_assoc]
    _ = janusInv3 χ_inv φ L_inv C *
          (janusDualMoment3 M P q * janusLie3 Ω γ δφ) * janusGroup3 χ φ L C := by
        rw [hgid, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

/-- **Archetype $\mathcal{J}_2$ (Non-Commutative Translational Trace Anomaly)**:
Over an arbitrary non-commutative ring `B`, conjugation by a pure translation `C` and charge-time
factor `χ` (`L = L_inv = 1`) shifts the Souriau–Noether trace pairing by the exact ring commutator
`-[C, P * Ω] = -(C * (P * Ω) - (P * Ω) * C)`:
$$\mathrm{Tr}\!\bigl(g_1^{-1} (\mu Z) g_1\bigr) =
  \mathrm{Tr}(\mu Z) - [C, P \Omega].$$ -/
theorem souriau_noether_noncommutative_trace_anomaly
    (χ χ_inv φ C M P q Ω γ δφ : B) :
    Matrix.trace
      (janusInv3 χ_inv φ 1 C *
        (janusDualMoment3 M P q * janusLie3 Ω γ δφ) * janusGroup3 χ φ 1 C) =
      Matrix.trace (janusDualMoment3 M P q * janusLie3 Ω γ δφ) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm C (P * Ω) := by
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  simp [Matrix.trace, Matrix.diag, janusGroup3, janusInv3,
    janusDualMoment3, janusLie3, Matrix.mul_apply, Fin.sum_univ_three]
  noncomm_ring

/-- **Socratic Aporia 2**: Over any commutative ring `K`, the translational trace anomaly
`comm C (P * Ω)` vanishes identically, so the Souriau–Noether trace pairing is strictly
invariant under translation conjugation. -/
theorem souriau_noether_trace_invariant_commRing {K : Type*} [CommRing K]
    (χ χ_inv φ C M P q Ω γ δφ : K) :
    Matrix.trace
      (janusInv3 χ_inv φ 1 C *
        (janusDualMoment3 M P q * janusLie3 Ω γ δφ) * janusGroup3 χ φ 1 C) =
      Matrix.trace (janusDualMoment3 M P q * janusLie3 Ω γ δφ) := by
  rw [souriau_noether_noncommutative_trace_anomaly]
  have hcomm : InfoGeometry.OperatorAlgebra.PeirceSpine.comm C (P * Ω) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    ring
  rw [hcomm, sub_zero]

/-- Exact right-contragredient Noether invariance over any non-commutative ring `B` when
`χ * χ_inv = 1` and `L * L_inv = 1`: with the right-shifted angular momentum
`M_shifted = M - P * L * L_inv * Ω * C`, `P' = P * L`, and `q' = q * χ`, the Souriau–Noether
pairing is strictly preserved without requiring commutativity when `Ω = 1` (`L = 1`). -/
theorem souriau_noether_right_contragredient_invariance
    (χ χ_inv L L_inv C M P q γ δφ : B)
    (hχR : χ * χ_inv = 1) (hLR : L * L_inv = 1) :
    (M - P * C) * 1 + (P * L) * (L_inv * 1 * C + L_inv * γ) + (q * χ) * (χ_inv * δφ) =
      M * 1 + P * γ + q * δφ := by
  have hPL : P * L * (L_inv * 1 * C + L_inv * γ) = P * (L * L_inv) * C + P * (L * L_inv) * γ := by
    noncomm_ring
  have hqχ : (q * χ) * (χ_inv * δφ) = q * (χ * χ_inv) * δφ := by
    noncomm_ring
  rw [hPL, hqχ, hLR, hχR]
  noncomm_ring

/-- **Bridge ($\mathcal{J}_1 \leftrightarrow$ `MatrixThreeSheetKKTRealization`)**:
The Kaluza–Janus Lie algebra generator `janusLie3 Ω γ δφ` decomposes into the 5-graded Peirce-KKT
sectors of `Nplus3` as:
- Grade `+2`: `0`,
- Grade `+1`: `!![0, 0, δφ; 0, 0, 0; 0, 0, 0]` (Kaluza 5th-dimension gauge velocity `δφ`),
- Grade `0`: `!![0, 0, 0; 0, Ω, 0; 0, 0, 0]` (Lorentz/linear generator `Ω`),
- Grade `-1`: `!![0, 0, 0; 0, 0, γ; 0, 0, 0]` (spacetime translation generator `γ`),
- Grade `-2`: `0`. -/
theorem janusLie3_peirce_five_grade_decomposition [StarRing B] (Ω γ δφ : B) :
    peirceGradePlus2 (Nplus3 (B := B)) (janusLie3 Ω γ δφ) = 0 ∧
    peirceGradePlus1 (Nplus3 (B := B)) (janusLie3 Ω γ δφ) =
      !![0, 0, δφ; 0, 0, 0; 0, 0, 0] ∧
    peirceGradeZero (Nplus3 (B := B)) (janusLie3 Ω γ δφ) =
      !![0, 0, 0; 0, Ω, 0; 0, 0, 0] ∧
    peirceGradeMinus1 (Nplus3 (B := B)) (janusLie3 Ω γ δφ) =
      !![0, 0, 0; 0, 0, γ; 0, 0, 0] ∧
    peirceGradeMinus2 (Nplus3 (B := B)) (janusLie3 Ω γ δφ) = 0 := by
  rcases five_grade_matrix_coordinates (B := B) (janusLie3 Ω γ δφ) with
    ⟨h₂, h₁, h₀, hm₁, hm₂⟩
  rw [h₂, h₁, h₀, hm₁, hm₂]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [janusLie3]

/-- **Bridge ($\mathcal{J}_2 \leftrightarrow$ `MatrixThreeSheetKKTRealization`)**:
The Souriau dual moment matrix `janusDualMoment3 M P q` decomposes into the dual 5-graded
Peirce-KKT sectors of `Nplus3` as:
- Grade `+2`: `0`,
- Grade `+1`: `!![0, 0, 0; 0, 0, 0; 0, P, 0]` (energy-momentum `P`, dual to `γ` in grade `-1`),
- Grade `0`: `!![0, 0, 0; 0, M, 0; 0, 0, 0]` (angular momentum `M`, dual to `Ω` in grade `0`),
- Grade `-1`: `!![0, 0, 0; 0, 0, 0; q, 0, 0]` (electric charge `q`, dual to `δφ` in grade `+1`),
- Grade `-2`: `0`. -/
theorem janusDualMoment3_peirce_five_grade_decomposition [StarRing B] (M P q : B) :
    peirceGradePlus2 (Nplus3 (B := B)) (janusDualMoment3 M P q) = 0 ∧
    peirceGradePlus1 (Nplus3 (B := B)) (janusDualMoment3 M P q) =
      !![0, 0, 0; 0, 0, 0; 0, P, 0] ∧
    peirceGradeZero (Nplus3 (B := B)) (janusDualMoment3 M P q) =
      !![0, 0, 0; 0, M, 0; 0, 0, 0] ∧
    peirceGradeMinus1 (Nplus3 (B := B)) (janusDualMoment3 M P q) =
      !![0, 0, 0; 0, 0, 0; q, 0, 0] ∧
    peirceGradeMinus2 (Nplus3 (B := B)) (janusDualMoment3 M P q) = 0 := by
  rcases five_grade_matrix_coordinates (B := B) (janusDualMoment3 M P q) with
    ⟨h₂, h₁, h₀, hm₁, hm₂⟩
  rw [h₂, h₁, h₀, hm₁, hm₂]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [janusDualMoment3]

/-- **Opposite-Grade Peirce Decomposition of the Souriau–Noether Trace Pairing**:
In the 3-sheet Peirce-KKT grading of `Matrix (Fin 3) (Fin 3) B`, the Souriau–Noether trace pairing
is the exact sum of the `(0, 0)`, `(+1, -1)`, and `(-1, +1)` opposite-grade trace pairings. -/
theorem souriau_trace_eq_peirce_opposite_grade_pairing [StarRing B]
    (M P q Ω γ δφ : B) :
    Matrix.trace (janusDualMoment3 M P q * janusLie3 Ω γ δφ) =
      Matrix.trace
        (peirceGradeZero (Nplus3 (B := B)) (janusDualMoment3 M P q) *
          peirceGradeZero (Nplus3 (B := B)) (janusLie3 Ω γ δφ)) +
      Matrix.trace
        (peirceGradePlus1 (Nplus3 (B := B)) (janusDualMoment3 M P q) *
          peirceGradeMinus1 (Nplus3 (B := B)) (janusLie3 Ω γ δφ)) +
      Matrix.trace
        (peirceGradeMinus1 (Nplus3 (B := B)) (janusDualMoment3 M P q) *
          peirceGradePlus1 (Nplus3 (B := B)) (janusLie3 Ω γ δφ)) := by
  rcases janusLie3_peirce_five_grade_decomposition (B := B) Ω γ δφ with
    ⟨_, hZ1, hZ0, hZm1, _⟩
  rcases janusDualMoment3_peirce_five_grade_decomposition (B := B) M P q with
    ⟨_, hM1, hM0, hMm1, _⟩
  rw [hZ1, hZ0, hZm1, hM1, hM0, hMm1, souriau_noether_trace_pairing]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **Bridge ($\mathcal{J}_1, \mathcal{J}_2 \leftrightarrow$ `MatrixThreeSheetZornGradingBridge`)**:
The projection `matrix3ToOpZorn` carries `janusLie3 Ω γ δφ` and `janusDualMoment3 M P q` into the
canonical operator-valued Zorn algebra `OpZornMatrix B` without losing any of the six active
parameters `(Ω, γ, δφ, M, P, q)`. -/
theorem matrix3ToOpZorn_janusLie3_and_dualMoment3 (Ω γ δφ M P q : B) :
    matrix3ToOpZorn (janusLie3 Ω γ δφ) =
      ⟨0, ⟨0, δφ, 0⟩, ⟨0, γ, 0⟩, Ω⟩ ∧
    matrix3ToOpZorn (janusDualMoment3 M P q) =
      ⟨0, ⟨0, 0, P⟩, ⟨0, 0, q⟩, M⟩ := by
  constructor <;> rfl

end StageJ2

/-! ## Section V: Stage $\mathcal{J}_3$ — Krein-Graded Bimetric Coupling `janusCoupling2`, Peirce Decomposition `invS P + genJ`, Socratic Aporia, Conservation & Pressure Flip -/

section StageJ3

variable {B : Type*} [Ring B]

/-- Canonical $2 \times 2$ Peirce sheet projector
$$P_2 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}.$$ -/
def peirceCut2 : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, 0]

/-- Cartan / Krein $\mathbb{Z}_2$ sheet reflection matrix
$$E_z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}.$$ -/
def cartanEz2 : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, -1]

/-- Krein-graded bimetric coupling matrix in `Matrix (Fin 2) (Fin 2) B`:
$$K_{\mathrm{Janus}}(b_1, b_2) = \begin{pmatrix} 1 & b_1 \\ -b_2 & -1 \end{pmatrix}.$$ -/
def janusCoupling2 (b₁ b₂ : B) : Matrix (Fin 2) (Fin 2) B :=
  !![1, b₁; -b₂, -1]

/-- Diagonal self-sector stress-energy matrix in `Matrix (Fin 2) (Fin 2) B`:
$$T_{\mathrm{self}}(\rho, p) = \begin{pmatrix} \rho & 0 \\ 0 & -p \end{pmatrix}.$$ -/
def stressSelf2 (ρ p : B) : Matrix (Fin 2) (Fin 2) B :=
  !![ρ, 0; 0, -p]

/-- Diagonal induced-sector stress-energy matrix in `Matrix (Fin 2) (Fin 2) B`:
$$T_{\mathrm{ind}}(\rho, p) = \begin{pmatrix} \rho & 0 \\ 0 & p \end{pmatrix}.$$ -/
def stressInduced2 (ρ p : B) : Matrix (Fin 2) (Fin 2) B :=
  !![ρ, 0; 0, p]

/-- `peirceCut2` is idempotent (`P₂² = P₂`). -/
theorem peirceCut2_idempotent :
    peirceCut2 (B := B) * peirceCut2 = peirceCut2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceCut2, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The Cartan reflection `cartanEz2` is identically the Peirce involution `invS peirceCut2 = 2 P₂ - 1`. -/
theorem cartanEz2_eq_invS_peirceCut2 :
    cartanEz2 (B := B) = invS (peirceCut2 (B := B)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartanEz2, peirceCut2, invS]

/-- **Bridge ($\mathcal{J}_3 \leftrightarrow$ `PeirceSpine`)**:
The Krein-graded bimetric coupling matrix `janusCoupling2 b₁ b₂` is the exact sum of the Peirce
grading involution `invS peirceCut2` and the chiral Peirce generator
`genJ peirceCut2 !![0, b₁; 0, 0] !![0, 0; b₂, 0]`. -/
theorem janusCoupling2_eq_invS_add_genJ (b₁ b₂ : B) :
    janusCoupling2 b₁ b₂ =
      invS (peirceCut2 (B := B)) +
        genJ (peirceCut2 (B := B)) !![0, b₁; 0, 0] !![0, 0; b₂, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusCoupling2, peirceCut2, invS, genJ, conePlus, coneMinus,
      Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]

/-- **Universal Peirce–Krein Bimetric Square Theorem**:
In any associative ring `R`, for any idempotent `P * P = P`, the sum of the Peirce involution
`invS P = 2 P - 1` and the chiral off-diagonal generator `genJ P A C = N_+ - N_-` squares to
`1 - genV P A C` (`1 - (N_+ N_- + N_- N_+)`), because `{invS P, genJ P A C} = 0` and `(genJ P A C)² = -genV P A C`. -/
theorem peirce_invS_add_genJ_sq {R : Type*} [Ring R] (P A C : R) (hP : P * P = P) :
    (invS P + genJ P A C) * (invS P + genJ P A C) = 1 - genV P A C := by
  peirce_nf hP

/-- **Chiral Socratic Aporia Identity**:
While the symmetric Peirce perturbation `P + genPhi P A C` has Socratic aporia `+genV P A C`, the
chiral Krein-bimetric perturbation `P + genJ P A C` has opposite Socratic aporia `-genV P A C`:
$$(P + J)^2 - (P + J) = -V.$$ -/
theorem peirce_chiral_aporia_eq_neg_genV {R : Type*} [Ring R] (P A C : R) (hP : P * P = P) :
    (P + genJ P A C) * (P + genJ P A C) - (P + genJ P A C) = -genV P A C := by
  peirce_nf hP

/-- **Archetype $\mathcal{J}_3$ (Krein-Graded Bimetric Coupling Square)**:
Over any non-commutative ring `B`, the square of `janusCoupling2 b₁ b₂` is the diagonal defect
matrix `!![1 - b₁ * b₂, 0; 0, 1 - b₂ * b₁]`. -/
theorem janusCoupling2_sq (b₁ b₂ : B) :
    janusCoupling2 b₁ b₂ * janusCoupling2 b₁ b₂ =
      !![1 - b₁ * b₂, 0; 0, 1 - b₂ * b₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [janusCoupling2, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    noncomm_ring

/-- Strict square-zero nilpotency of `janusCoupling2 b₁ b₂` under the reciprocal volume-ratio
condition `b₁ * b₂ = 1` and `b₂ * b₁ = 1`. -/
theorem janusCoupling2_sq_eq_zero_of_reciprocal (b₁ b₂ : B)
    (h12 : b₁ * b₂ = 1) (h21 : b₂ * b₁ = 1) :
    janusCoupling2 b₁ b₂ * janusCoupling2 b₁ b₂ = 0 := by
  rw [janusCoupling2_sq, h12, h21]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Under `b₁ * b₂ = 1` and `b₂ * b₁ = 1`, `1 + janusCoupling2 b₁ b₂` is unipotent with explicit
two-sided inverse `1 - janusCoupling2 b₁ b₂`:
$$(1 + K_{\mathrm{Janus}})(1 - K_{\mathrm{Janus}}) = 1.$$ -/
theorem janusCoupling2_unipotent_inv_of_reciprocal (b₁ b₂ : B)
    (h12 : b₁ * b₂ = 1) (h21 : b₂ * b₁ = 1) :
    (1 + janusCoupling2 b₁ b₂) * (1 - janusCoupling2 b₁ b₂) = 1 := by
  have hsq : janusCoupling2 b₁ b₂ * janusCoupling2 b₁ b₂ = 0 :=
    janusCoupling2_sq_eq_zero_of_reciprocal b₁ b₂ h12 h21
  calc
    (1 + janusCoupling2 b₁ b₂) * (1 - janusCoupling2 b₁ b₂)
      = 1 - janusCoupling2 b₁ b₂ * janusCoupling2 b₁ b₂ := by
        noncomm_ring
    _ = 1 := by
        rw [hsq, sub_zero]

/-- **Bimetric Bianchi Conservation Identity**:
For the coupled field tensors `E_plus = T_plus + b₁ * T_minus` and
`E_minus = -(b₂ * T_plus) - T_minus`, the weighted sum `b₂ * E_plus + E_minus` equals the
reciprocity defect `(b₂ * b₁ - 1) * T_minus`. -/
theorem bimetric_bianchi_conservation_defect (b₁ b₂ T_plus T_minus : B) :
    let E_plus := T_plus + b₁ * T_minus
    let E_minus := -(b₂ * T_plus) - T_minus
    b₂ * E_plus + E_minus = (b₂ * b₁ - 1) * T_minus := by
  dsimp
  noncomm_ring

/-- Exact vanishing of the coupled bimetric divergence `b₂ * E_plus + E_minus = 0` whenever
`b₂ * b₁ = 1`. -/
theorem bimetric_bianchi_conservation_zero_of_left_inv (b₁ b₂ T_plus T_minus : B)
    (h21 : b₂ * b₁ = 1) :
    let E_plus := T_plus + b₁ * T_minus
    let E_minus := -(b₂ * T_plus) - T_minus
    b₂ * E_plus + E_minus = 0 := by
  dsimp
  rw [bimetric_bianchi_conservation_defect, h21, sub_self, zero_mul]

/-- **Cartan Pressure Sign Reversal**:
Multiplying the self-sector stress tensor `stressSelf2 ρ p = !![ρ, 0; 0, -p]` by the Cartan/Krein
grading `cartanEz2 = !![1, 0; 0, -1]` reverses the sign of the spatial pressure component (`-p ↦ +p`)
while preserving the energy density component (`ρ ↦ +ρ`). -/
theorem cartan_pressure_sign_reversal (ρ p : B) :
    cartanEz2 * stressSelf2 ρ p = stressInduced2 ρ p ∧
    stressSelf2 ρ p + stressInduced2 ρ p = !![ρ + ρ, 0; 0, 0] ∧
    stressSelf2 ρ p - stressInduced2 ρ p = !![0, 0; 0, -(p + p)] := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cartanEz2, stressSelf2, stressInduced2, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stressSelf2, stressInduced2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [stressSelf2, stressInduced2]; try abel)

end StageJ3

/-! ## Section VI: Stage $\mathcal{J}_4$ — Order-3 Jacobson–Morozov Lagrange Sheet Reconstruction (`Matrix (Fin 3) (Fin 3) B`) & Native `Matrix (Fin 4) (Fin 4) B` Plücker–Hodge Nambu Anomaly -/

section StageJ4

variable {B : Type*} [Ring B]

/-- Order-3 nilpotent raising shift $N_3 = E_{01} + E_{12}$ on `Matrix (Fin 3) (Fin 3) B`. -/
def jmShiftPlus3 : Matrix (Fin 3) (Fin 3) B :=
  !![0, 1, 0; 0, 0, 1; 0, 0, 0]

/-- Order-3 nilpotent lowering shift $M_3 = 2(E_{10} + E_{21})$ on `Matrix (Fin 3) (Fin 3) B`. -/
def jmShiftMinus3 : Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, 0; 2, 0, 0; 0, 2, 0]

/-- Neutral Cartan diagonal generator $H_3 = \mathrm{diag}(2, 0, -2)$ on `Matrix (Fin 3) (Fin 3) B`. -/
def jmCartan3 : Matrix (Fin 3) (Fin 3) B :=
  !![2, 0, 0; 0, 0, 0; 0, 0, -2]

/-- Second orthogonal sheet projector $P_1 = E_{11}$ on `Matrix (Fin 3) (Fin 3) B`. -/
def sheetProj1 : Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, 0; 0, 1, 0; 0, 0, 0]

/-- Third orthogonal sheet projector $P_2 = E_{22}$ on `Matrix (Fin 3) (Fin 3) B`. -/
def sheetProj2 : Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, 0; 0, 0, 0; 0, 0, 1]

/-- **Order-3 Jacobson–Morozov $\mathfrak{sl}_2$ Triple & Lagrange Sheet Projector Reconstruction**:
Over any non-commutative ring `B`, `(jmShiftPlus3, jmShiftMinus3, jmCartan3)` forms an order-3
nilpotent $\mathfrak{sl}_2$ triple on `Matrix (Fin 3) (Fin 3) B` (`N_3^3 = 0`, `M_3^3 = 0`,
`[N_3, M_3] = H_3`, `[H_3, N_3] = 2 • N_3`, `[H_3, M_3] = -(2 • M_3)`), and the three orthogonal
sheet projectors `archetypeCut3`, `sheetProj1`, `sheetProj2` are reconstructed as Lagrange
interpolation polynomials in `jmCartan3`:
$$H_3 (H_3 + 2 I_3) = 8 P_0, \qquad 4 I_3 - H_3^2 = 4 P_1, \qquad H_3 (H_3 - 2 I_3) = 8 P_2.$$ -/
theorem order3_jacobson_morozov_lagrange_sheet_reconstruction :
    jmShiftPlus3 (B := B) * jmShiftPlus3 * jmShiftPlus3 = 0 ∧
    jmShiftMinus3 (B := B) * jmShiftMinus3 * jmShiftMinus3 = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (jmShiftPlus3 (B := B)) jmShiftMinus3 = jmCartan3 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (jmCartan3 (B := B)) jmShiftPlus3 = (2 : ℤ) • jmShiftPlus3 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (jmCartan3 (B := B)) jmShiftMinus3 = -((2 : ℤ) • jmShiftMinus3) ∧
    jmCartan3 (B := B) * (jmCartan3 + Matrix.diagonal (fun _ : Fin 3 => (2 : B))) =
      (8 : ℤ) • archetypeCut3 (B := B) ∧
    Matrix.diagonal (fun _ : Fin 3 => (4 : B)) - jmCartan3 (B := B) * jmCartan3 =
      (4 : ℤ) • sheetProj1 (B := B) ∧
    jmCartan3 (B := B) * (jmCartan3 - Matrix.diagonal (fun _ : Fin 3 => (2 : B))) =
      (8 : ℤ) • sheetProj2 (B := B) ∧
    archetypeCut3 (B := B) + sheetProj1 + sheetProj2 = 1 := by
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [jmShiftPlus3, jmShiftMinus3, jmCartan3, archetypeCut3, sheetProj1, sheetProj2,
        Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three]; try norm_num)

/-- Order-3 $\mathfrak{sl}_2$ quadratic Casimir operator on `Matrix (Fin 3) (Fin 3) B`:
$$C_2 = H_3^2 + 2(N_3 M_3 + M_3 N_3).$$ -/
def jmCasimir3 : Matrix (Fin 3) (Fin 3) B :=
  jmCartan3 * jmCartan3 +
    (2 : ℤ) • (jmShiftPlus3 * jmShiftMinus3 + jmShiftMinus3 * jmShiftPlus3)

/-- **Order-3 Erlangen 2.0 Casimir & Metric Reconstruction (`Matrix (Fin 3) (Fin 3) B`)**:
Over any non-commutative ring `B`, the quadratic Casimir `jmCasimir3` equals the central scalar
matrix `Matrix.diagonal (fun _ => 8)`, commutes with all three $\mathfrak{sl}_2$ generators
`(jmShiftPlus3, jmShiftMinus3, jmCartan3)`, and reconstructs the Jordan anticommutator metric
`2 • {N₃, M₃} = jmCasimir3 - jmCartan3² = !![4, 0, 0; 0, 8, 0; 0, 0, 4]`. -/
theorem order3_sl2_casimir_and_erlangen_metric_reconstruction :
    jmCasimir3 (B := B) = Matrix.diagonal (fun _ : Fin 3 => (8 : B)) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (jmCasimir3 (B := B)) jmShiftPlus3 = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (jmCasimir3 (B := B)) jmShiftMinus3 = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (jmCasimir3 (B := B)) jmCartan3 = 0 ∧
    (2 : ℤ) • (jmShiftPlus3 (B := B) * jmShiftMinus3 + jmShiftMinus3 * jmShiftPlus3) =
      jmCasimir3 (B := B) - jmCartan3 * jmCartan3 ∧
    jmCasimir3 (B := B) - jmCartan3 * jmCartan3 =
      !![(4 : B), 0, 0; 0, 8, 0; 0, 0, 4] := by
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [jmCasimir3, jmShiftPlus3, jmShiftMinus3, jmCartan3]; try norm_num)

/-- Positive $4 \times 4$ nilpotent matrix unit $E_{01}$. -/
def Nplus4 : Matrix (Fin 4) (Fin 4) B :=
  !![0, 1, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

/-- Negative $4 \times 4$ nilpotent matrix unit $E_{10}$. -/
def Nminus4 : Matrix (Fin 4) (Fin 4) B :=
  !![0, 0, 0, 0;
    1, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

/-- Non-commutativity of the $4 \times 4$ matrix units over any nontrivial ring `B`. -/
theorem Nplus4_mul_Nminus4_ne [Nontrivial B] :
    Nplus4 (B := B) * Nminus4 ≠ Nminus4 * Nplus4 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) B => M 0 0) h
  simp [Nplus4, Nminus4] at h00

/-- Native $4 \times 4$ skew-symmetric Plücker bivector matrix in `Matrix (Fin 4) (Fin 4) B`:
$$P_4(\mathbf{u}, \mathbf{v}) = \begin{pmatrix}
  0 & u_x & u_y & u_z \\
  -u_x & 0 & -v_z & v_y \\
  -u_y & v_z & 0 & -v_x \\
  -u_z & -v_y & v_x & 0
\end{pmatrix}.$$ -/
def pluckerMat4 (u v : OpVec3 B) : Matrix (Fin 4) (Fin 4) B :=
  !![0, u.x, u.y, u.z;
    -u.x, 0, -v.z, v.y;
    -u.y, v.z, 0, -v.x;
    -u.z, -v.y, v.x, 0]

/-- Hodge dual of `pluckerMat4 u v` in `Matrix (Fin 4) (Fin 4) B`, swapping electric `u` and
magnetic `v` 3-vectors: $\star P_4(\mathbf{u}, \mathbf{v}) = P_4(\mathbf{v}, \mathbf{u})$. -/
def hodgePluckerMat4 (u v : OpVec3 B) : Matrix (Fin 4) (Fin 4) B :=
  pluckerMat4 v u

/-- **Native `Matrix (Fin 4) (Fin 4) B` Plücker–Hodge Chromomagnetic & Nambu Anomaly**:
Over any non-commutative ring `B`, the negated Plücker–Hodge matrix product
`M_PH := -(pluckerMat4 u v * hodgePluckerMat4 u v)` satisfies:
1. `(0,0)` entry equals the inner product `OpVec3.dot u v`,
2. Row `0` spatial entries `(0,1..3)` equal `-(OpVec3.naiveCross u u)` (electric self-commutator),
3. Column `0` spatial entries `(1..3,0)` equal `OpVec3.naiveCross v v` (magnetic self-commutator),
4. For the self-Plücker configuration `v = OpVec3.naiveCross u u`, the `(0,0)` entry is the
   non-commutative Nambu 3-bracket `OpVec3.dot u (OpVec3.naiveCross u u)`. -/
theorem pluckerMat4_hodge_product_anomalies (u v : OpVec3 B) :
    let M_PH := -(pluckerMat4 u v * hodgePluckerMat4 u v)
    M_PH 0 0 = OpVec3.dot u v ∧
    M_PH 0 1 = -(OpVec3.naiveCross u u).x ∧
    M_PH 0 2 = -(OpVec3.naiveCross u u).y ∧
    M_PH 0 3 = -(OpVec3.naiveCross u u).z ∧
    M_PH 1 0 = (OpVec3.naiveCross v v).x ∧
    M_PH 2 0 = (OpVec3.naiveCross v v).y ∧
    M_PH 3 0 = (OpVec3.naiveCross v v).z ∧
    (-(pluckerMat4 u (OpVec3.naiveCross u u) *
        hodgePluckerMat4 u (OpVec3.naiveCross u u))) 0 0 =
      OpVec3.dot u (OpVec3.naiveCross u u) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pluckerMat4, hodgePluckerMat4, OpVec3.dot, Matrix.mul_apply, Fin.sum_univ_succ]
    abel
  · simp [pluckerMat4, hodgePluckerMat4, OpVec3.naiveCross, Matrix.mul_apply, Fin.sum_univ_succ]
    abel
  · simp [pluckerMat4, hodgePluckerMat4, OpVec3.naiveCross, Matrix.mul_apply, Fin.sum_univ_succ]
    abel
  · simp [pluckerMat4, hodgePluckerMat4, OpVec3.naiveCross, Matrix.mul_apply, Fin.sum_univ_succ]
    abel
  · simp [pluckerMat4, hodgePluckerMat4, OpVec3.naiveCross, Matrix.mul_apply, Fin.sum_univ_succ]
    abel
  · simp [pluckerMat4, hodgePluckerMat4, OpVec3.naiveCross, Matrix.mul_apply, Fin.sum_univ_succ]
    abel
  · simp [pluckerMat4, hodgePluckerMat4, OpVec3.naiveCross, Matrix.mul_apply, Fin.sum_univ_succ]
    abel
  · simp [pluckerMat4, hodgePluckerMat4, OpVec3.dot, OpVec3.naiveCross,
      Matrix.mul_apply, Fin.sum_univ_succ]
    noncomm_ring

/-- Over any commutative ring, all non-commutative self-cross anomalies vanish and
`-(pluckerMat4 u v * hodgePluckerMat4 u v)` collapses to the scalar Klein-quadric multiple of the
$4 \times 4$ identity matrix `(OpVec3.dot u v) • 1`. -/
theorem pluckerMat4_hodge_product_commRing {B : Type*} [CommRing B] (u v : OpVec3 B) :
    -(pluckerMat4 u v * hodgePluckerMat4 u v) =
      (OpVec3.dot u v) • (1 : Matrix (Fin 4) (Fin 4) B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pluckerMat4, hodgePluckerMat4, OpVec3.dot] <;>
    ring

/-- Non-commutative Nambu 3-bracket on `OpVec3 B`:
$$\llbracket \mathbf{u} \rrbracket =
  u_x u_y u_z - u_x u_z u_y + u_y u_z u_x - u_y u_x u_z + u_z u_x u_y - u_z u_y u_x.$$ -/
def opNambu3 (u : OpVec3 B) : B :=
  u.x * u.y * u.z - u.x * u.z * u.y +
  u.y * u.z * u.x - u.y * u.x * u.z +
  u.z * u.x * u.y - u.z * u.y * u.x

/-- 3-quark baryon singlet determinant on `OpVec3 B`:
$$B(\mathbf{u}_1, \mathbf{u}_2, \mathbf{u}_3) = (\mathbf{u}_1 \times \mathbf{u}_2) \cdot \mathbf{u}_3.$$ -/
def opBaryonDet3 (u₁ u₂ u₃ : OpVec3 B) : B :=
  OpVec3.dot (OpVec3.naiveCross u₁ u₂) u₃

/-- 3-simplex boundary operator $\partial_3$ on a 3-point baryon function $F$:
$$(\partial_3 F)(\mathbf{u}_0, \mathbf{u}_1, \mathbf{u}_2, \mathbf{u}_3) =
  F(\mathbf{u}_1, \mathbf{u}_2, \mathbf{u}_3) - F(\mathbf{u}_0, \mathbf{u}_2, \mathbf{u}_3) +
  F(\mathbf{u}_0, \mathbf{u}_1, \mathbf{u}_3) - F(\mathbf{u}_0, \mathbf{u}_1, \mathbf{u}_2).$$ -/
def simplexBoundary3 (F : OpVec3 B → OpVec3 B → OpVec3 B → B)
    (u₀ u₁ u₂ u₃ : OpVec3 B) : B :=
  F u₁ u₂ u₃ - F u₀ u₂ u₃ + F u₀ u₁ u₃ - F u₀ u₁ u₂

/-- 4-simplex boundary operator $\partial_4 \circ \partial_3$ on 5 vertices. -/
def simplexBoundary4 (F : OpVec3 B → OpVec3 B → OpVec3 B → B)
    (u₀ u₁ u₂ u₃ u₄ : OpVec3 B) : B :=
  simplexBoundary3 F u₁ u₂ u₃ u₄ -
  simplexBoundary3 F u₀ u₂ u₃ u₄ +
  simplexBoundary3 F u₀ u₁ u₃ u₄ -
  simplexBoundary3 F u₀ u₁ u₂ u₄ +
  simplexBoundary3 F u₀ u₁ u₂ u₃

/-- **Nambu 3-Bracket Plücker–Hodge Identity & Homological Simplex Boundary ($\partial^2 = 0$)**:
Over any non-commutative ring `B`:
1. `OpVec3.dot u (OpVec3.naiveCross u u) = opNambu3 u`,
2. The `(0,0)` entry of `-(pluckerMat4 u (OpVec3.naiveCross u u) * hodgePluckerMat4 u (OpVec3.naiveCross u u))`
   in `Matrix (Fin 4) (Fin 4) B` equals `opNambu3 u`,
3. The 5-vertex 4-simplex holographic boundary of `opBaryonDet3` vanishes identically
   (`simplexBoundary4 opBaryonDet3 u₀ u₁ u₂ u₃ u₄ = 0`). -/
theorem pluckerMat4_nambu3_and_simplex_boundary_sq_zero
    (u u₀ u₁ u₂ u₃ u₄ : OpVec3 B) :
    OpVec3.dot u (OpVec3.naiveCross u u) = opNambu3 u ∧
    (-(pluckerMat4 u (OpVec3.naiveCross u u) *
        hodgePluckerMat4 u (OpVec3.naiveCross u u))) 0 0 = opNambu3 u ∧
    simplexBoundary4 (B := B) opBaryonDet3 u₀ u₁ u₂ u₃ u₄ = 0 := by
  have hNambu : OpVec3.dot u (OpVec3.naiveCross u u) = opNambu3 u := by
    dsimp [OpVec3.dot, OpVec3.naiveCross, opNambu3]
    noncomm_ring
  refine ⟨hNambu, ?_, ?_⟩
  · rw [(pluckerMat4_hodge_product_anomalies u (OpVec3.naiveCross u u)).2.2.2.2.2.2.2]
    exact hNambu
  · dsimp [simplexBoundary4, simplexBoundary3]
    abel

/-- Over a commutative ring, the relative-chord baryon determinant
`opBaryonDet3 (u₁ - u₀) (u₂ - u₀) (u₃ - u₀)` equals the 4-facet cyclic simplex boundary
`simplexBoundary3 opBaryonDet3 u₀ u₁ u₂ u₃`. -/
theorem opBaryonDet3_relative_chord_eq_simplexBoundary3
    {B : Type*} [CommRing B] (u₀ u₁ u₂ u₃ : OpVec3 B) :
    opBaryonDet3
      ⟨u₁.x - u₀.x, u₁.y - u₀.y, u₁.z - u₀.z⟩
      ⟨u₂.x - u₀.x, u₂.y - u₀.y, u₂.z - u₀.z⟩
      ⟨u₃.x - u₀.x, u₃.y - u₀.y, u₃.z - u₀.z⟩ =
      simplexBoundary3 opBaryonDet3 u₀ u₁ u₂ u₃ := by
  dsimp [opBaryonDet3, simplexBoundary3, OpVec3.dot, OpVec3.naiveCross]
  ring

end StageJ4

/-! ## Section VII: Concrete Non-Commutative Witnesses (`T16`) over `ℤ` & Master Structural Synthesis (`Stage J₅`) -/

section StageJ5

/-- Concrete non-commutative $2 \times 2$ integer matrix `E₀₁ = !![0, 1; 0, 0]`. -/
def ncWitnessC : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 0, 0]

/-- Concrete non-commutative $2 \times 2$ integer matrix `E₁₀ = !![0, 0; 1, 0]`. -/
def ncWitnessPOmega : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 0; 1, 0]

/-- Standalone non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℤ`. -/
theorem ncWitness_mul_ne :
    ncWitnessC * ncWitnessPOmega ≠ ncWitnessPOmega * ncWitnessC := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  simp [ncWitnessC, ncWitnessPOmega] at h00

/-- **Concrete Non-Commutative Witness (`T16`)**:
Over `B = Matrix (Fin 2) (Fin 2) ℤ`:
1. The Souriau–Noether translational trace anomaly `comm ncWitnessC ncWitnessPOmega` is non-zero,
2. The two diagonal entries `1 - b₁ * b₂` and `1 - b₂ * b₁` of `(janusCoupling2 b₁ b₂)²` are
   distinct (`1 - ncWitnessC * ncWitnessPOmega ≠ 1 - ncWitnessPOmega * ncWitnessC`),
3. The Plücker–Hodge electric self-cross product `OpVec3.naiveCross u u` is non-zero. -/
theorem concrete_noncommutative_witnesses_int :
    ncWitnessC * ncWitnessPOmega ≠ ncWitnessPOmega * ncWitnessC ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm ncWitnessC ncWitnessPOmega ≠ 0 ∧
    (1 - ncWitnessC * ncWitnessPOmega) ≠ (1 - ncWitnessPOmega * ncWitnessC) ∧
    OpVec3.naiveCross ⟨ncWitnessC, ncWitnessPOmega, 0⟩ ⟨ncWitnessC, ncWitnessPOmega, 0⟩ ≠
      (⟨0, 0, 0⟩ : OpVec3 (Matrix (Fin 2) (Fin 2) ℤ)) := by
  refine ⟨ncWitness_mul_ne, ?_, ?_, ?_⟩
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
    simp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, ncWitnessC, ncWitnessPOmega] at h00
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
    simp [ncWitnessC, ncWitnessPOmega] at h00
  · intro h
    have hz := congrArg OpVec3.z h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hz
    simp [OpVec3.naiveCross, ncWitnessC, ncWitnessPOmega] at h00

/-- **Stage $\mathcal{J}_5$ (Master Coagulated Synthesis of the Souriau–Kaluza–Janus–Bimetric Poset)**:
Unifies the entire acyclic causal poset $\mathcal{J}_0 \prec \mathcal{J}_1 \prec \mathcal{J}_2 \prec \mathcal{J}_3 \prec \mathcal{J}_4 \prec \mathcal{J}_5$
over an arbitrary non-commutative `[Ring B] [StarRing B]`:
1. **Strict Causal Chain**: $\mathcal{J}_0 \prec \mathcal{J}_1 \prec \mathcal{J}_2 \prec \mathcal{J}_3 \prec \mathcal{J}_4 \prec \mathcal{J}_5$,
2. **Stage $\mathcal{J}_0$ (Souriau Coadjoint Congruence & Affine Cocycle Bridge)**:
   `affGroup2 L C * souriauMoment2 M P * (affGroup2 L C)ᴴ = souriauMoment2 (L * M * star L - L * P * star C + C * star (L * P)) (L * P)`
   and `affGroup2 1 C` acts via `CartanSouriauAffineCocycle.affineAction`,
3. **Stage $\mathcal{J}_1$ ($3 \times 3$ Kaluza–Janus Adjoint Representation)**:
   `janusInv3 χ_inv φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 χ φ L C = janusLie3 (L_inv * Ω * L) (L_inv * Ω * C + L_inv * γ) (χ_inv * δφ)`,
4. **Stage $\mathcal{J}_2$ (Souriau–Noether Trace Pairing, Non-Commutative Anomaly & Peirce Opposite-Grade Decomposition)**:
   `Matrix.trace (janusDualMoment3 M P q * janusLie3 Ω γ δφ) = M * Ω + P * γ + q * δφ` and its
   translation anomaly `-comm C (P * Ω)`,
5. **Stage $\mathcal{J}_3$ (Krein-Bimetric Peirce Decomposition, Square-Zero Nilpotency & Conservation)**:
   `janusCoupling2 b₁ b₂ = invS peirceCut2 + genJ peirceCut2 !![0, b₁; 0, 0] !![0, 0; b₂, 0]`,
   `(janusCoupling2 b₁ b₂)² = !![1 - b₁ * b₂, 0; 0, 1 - b₂ * b₁]`, and `cartanEz2 * stressSelf2 ρ p = stressInduced2 ρ p`,
6. **Stage $\mathcal{J}_4$ (Order-3 Jacobson–Morozov Sheet Reconstruction & Native `Matrix (Fin 4) (Fin 4) B` Plücker Anomaly)**:
   `archetypeCut3 + sheetProj1 + sheetProj2 = 1` and `(-(pluckerMat4 u v * hodgePluckerMat4 u v)) 0 0 = OpVec3.dot u v`. -/
theorem souriau_kaluza_janus_bimetric_master_synthesis
    {B : Type*} [Ring B] [StarRing B]
    (χ χ_inv φ L L_inv C M P q Ω γ δφ b₁ b₂ ρ p : B)
    (u v : OpVec3 B) :
    (SouriauKaluzaJanusStage.J0_SouriauPoincareMomentTorsor <
      SouriauKaluzaJanusStage.J5_NecessaryCoagulatedSynthesis) ∧
    (affGroup2 L C * souriauMoment2 M P * (affGroup2 L C)ᴴ =
      souriauMoment2 (L * M * star L - L * P * star C + C * star (L * P)) (L * P)) ∧
    (janusInv3 χ_inv φ L_inv C * janusLie3 Ω γ δφ * janusGroup3 χ φ L C =
      janusLie3 (L_inv * Ω * L) (L_inv * Ω * C + L_inv * γ) (χ_inv * δφ)) ∧
    (Matrix.trace
      (janusInv3 χ_inv φ 1 C *
        (janusDualMoment3 M P q * janusLie3 Ω γ δφ) * janusGroup3 χ φ 1 C) =
      (M * Ω + P * γ + q * δφ) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm C (P * Ω)) ∧
    (janusCoupling2 b₁ b₂ * janusCoupling2 b₁ b₂ =
      !![1 - b₁ * b₂, 0; 0, 1 - b₂ * b₁]) ∧
    (cartanEz2 * stressSelf2 ρ p = stressInduced2 ρ p) ∧
    (archetypeCut3 (B := B) + sheetProj1 + sheetProj2 = 1) ∧
    ((-(pluckerMat4 u v * hodgePluckerMat4 u v)) 0 0 = OpVec3.dot u v) := by
  refine ⟨by decide,
    souriauMoment2_coadjoint_congruence L C M P,
    janusLie3_adjoint_action χ χ_inv φ L L_inv C Ω γ δφ,
    ?_,
    janusCoupling2_sq b₁ b₂,
    (cartan_pressure_sign_reversal ρ p).1,
    order3_jacobson_morozov_lagrange_sheet_reconstruction.2.2.2.2.2.2.2.2,
    (pluckerMat4_hodge_product_anomalies u v).1⟩
  rw [souriau_noether_noncommutative_trace_anomaly, souriau_noether_trace_pairing]

end StageJ5

end InfoGeometry.Canonical.SouriauKaluzaJanusBimetricPoset
