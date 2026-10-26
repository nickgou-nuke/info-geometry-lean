/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Non-Commutative Flag Hierarchy

Formalizes the complete causal poset (α₀ ≺ … ≺ α₆) of non-commutative
projection flag archetypes over the matrix ring Mat_n(R):

- **α₀**: Inner derivation [D, X] = DX − XD with trace vanishing.
- **α₁**: Halmos–Connes subprojection poset P ≼ G (two-sided absorption).
- **α₂**: Three-level projection flag P ≼ G ≼ M with orthogonal shell resolution.
- **α₃**: Coarse-graining conditional expectations (pinching maps).
- **α₄**: Commutativity of flag expectations & four-stratum pinching.
- **α₅**: Corner-confined Connes curvature [D, S]² commutes with S.
- **α₆**: Three-stratum Gauss–Codazzi decomposition & cyclic cocycle partition.

All proofs are constructive, kernel-checked, zero sorry/admit/axiom.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NonCommutativeFlagHierarchy

open Matrix

variable {R : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-!
### Archetype α₀: Primordial Matrix Substrate & Inner Derivation
-/

/-- The non-commutative inner derivation δ_D(X) = [D, X] = D * X - X * D on M_n(R). -/
def commutator [Ring R] (D X : Matrix n n R) : Matrix n n R :=
  D * X - X * D

/-- Right subtraction linearity of the evolutionary derivation:
[D, X - Y] = [D, X] - [D, Y]. -/
lemma commutator_sub_right [Ring R] (D X Y : Matrix n n R) :
    commutator D (X - Y) = commutator D X - commutator D Y := by
  dsimp [commutator]
  noncomm_ring

/-- Homological Trace Vanishing: tr([D, X]) = 0. -/
theorem trace_commutator_zero [CommRing R] (D X : Matrix n n R) :
    Matrix.trace (commutator D X) = 0 := by
  dsimp [commutator]
  rw [Matrix.trace_sub, Matrix.trace_mul_comm D X, sub_self]

/-!
### Archetype α₁: The Halmos-Connes Taxonomic Subprojection Poset
Causal Dependency: α₀ ≺ α₁
-/

/-- An idempotent projection operator (taxonomic stratum) P² = P in M_n(R). -/
structure IsIdempotent [Ring R] (P : Matrix n n R) : Prop where
  idem : P * P = P

/-- Non-commutative taxonomic subprojection relation P ≼ G:
P is absorbed on both the right and left by the coarser projection G. -/
structure Subprojection [Ring R] (P G : Matrix n n R) : Prop where
  mul_right : P * G = P
  mul_left  : G * P = P

/-- Reflexivity of the taxonomic subprojection order on idempotent strata. -/
lemma subprojection_refl [Ring R] (P : Matrix n n R) (hP : IsIdempotent P) :
    Subprojection P P :=
  ⟨hP.idem, hP.idem⟩

/-- Antisymmetry of the taxonomic subprojection order: P ≼ Q and Q ≼ P imply P = Q. -/
theorem subprojection_antisymm [Ring R] (P Q : Matrix n n R)
    (hPQ : Subprojection P Q) (hQP : Subprojection Q P) :
    P = Q := by
  rw [← hPQ.mul_right, hQP.mul_left]

/-- Transitivity of the taxonomic subprojection order across a multi-level flag P ≼ G ≼ M. -/
theorem subprojection_trans [Ring R] (P G M : Matrix n n R)
    (hPG : Subprojection P G) (hGM : Subprojection G M) :
    Subprojection P M := by
  refine ⟨?_, ?_⟩
  · calc
      P * M = (P * G) * M := by rw [hPG.mul_right]
      _ = P * (G * M) := by rw [mul_assoc]
      _ = P * G := by rw [hGM.mul_right]
      _ = P := hPG.mul_right
  · calc
      M * P = M * (G * P) := by rw [hPG.mul_left]
      _ = (M * G) * P := by rw [mul_assoc]
      _ = G * P := by rw [hGM.mul_left]
      _ = P := hPG.mul_left

/-- Relative Complement Idempotence:
If P ≼ G are idempotent strata, the relative shell G - P is idempotent. -/
theorem idempotent_relative_complement [Ring R] (P G : Matrix n n R)
    (hP : IsIdempotent P) (hG : IsIdempotent G) (hPG : Subprojection P G) :
    IsIdempotent (G - P) := by
  refine ⟨?_⟩
  calc
    (G - P) * (G - P)
      = G * G - G * P - P * G + P * P := by noncomm_ring
    _ = G - P - P + P := by rw [hG.idem, hPG.mul_left, hPG.mul_right, hP.idem]
    _ = G - P := by noncomm_ring

/-!
### Archetype α₂: Three-Level Projection Flag & Orthogonal Shell Resolution
Causal Dependency: α₀ ≺ α₁ ≺ α₂
-/

/-- Two operator strata P and Q are mutually orthogonal if P * Q = 0 and Q * P = 0. -/
structure IsOrthogonalPair [Ring R] (P Q : Matrix n n R) : Prop where
  mul_eq_zero : P * Q = 0
  rev_eq_zero : Q * P = 0

/-- A 3-level non-commutative taxonomic projection flag P ≼ G ≼ M in M_n(R). -/
structure IsThreeLevelFlag [Ring R] (P G M : Matrix n n R) : Prop where
  idem_P : IsIdempotent P
  idem_G : IsIdempotent G
  idem_M : IsIdempotent M
  sub_PG : Subprojection P G
  sub_GM : Subprojection G M

/-- Transitive absorption P ≼ M induced by a 3-level flag P ≼ G ≼ M. -/
lemma IsThreeLevelFlag.sub_PM [Ring R] {P G M : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M) :
    Subprojection P M :=
  subprojection_trans P G M hFlag.sub_PG hFlag.sub_GM

/-- Telescoping 3-Stratum Resolution of the Macro-Projection M:
P + (G - P) + (M - G) = M. -/
theorem three_stratum_resolution_of_macro [Ring R] (P G M : Matrix n n R) :
    P + (G - P) + (M - G) = M := by
  noncomm_ring

/-- Telescoping 4-Stratum Resolution of the Identity 1 ∈ M_n(R):
P + (G - P) + (M - G) + (1 - M) = 1. -/
theorem four_stratum_resolution_of_one [Ring R] (P G M : Matrix n n R) :
    P + (G - P) + (M - G) + (1 - M) = 1 := by
  noncomm_ring

/-- Mutual orthogonality of the fine stratum P and intermediate shell G - P. -/
theorem orthogonal_fine_middle_shell [Ring R] (P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    IsOrthogonalPair P (G - P) := by
  refine ⟨?_, ?_⟩
  · calc
      P * (G - P) = P * G - P * P := by noncomm_ring
      _ = P - P := by rw [hFlag.sub_PG.mul_right, hFlag.idem_P.idem]
      _ = 0 := sub_self P
  · calc
      (G - P) * P = G * P - P * P := by noncomm_ring
      _ = P - P := by rw [hFlag.sub_PG.mul_left, hFlag.idem_P.idem]
      _ = 0 := sub_self P

/-- Mutual orthogonality of the fine stratum P and outer shell M - G. -/
theorem orthogonal_fine_outer_shell [Ring R] (P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    IsOrthogonalPair P (M - G) := by
  have hPM := hFlag.sub_PM
  refine ⟨?_, ?_⟩
  · calc
      P * (M - G) = P * M - P * G := by noncomm_ring
      _ = P - P := by rw [hPM.mul_right, hFlag.sub_PG.mul_right]
      _ = 0 := sub_self P
  · calc
      (M - G) * P = M * P - G * P := by noncomm_ring
      _ = P - P := by rw [hPM.mul_left, hFlag.sub_PG.mul_left]
      _ = 0 := sub_self P

/-- Mutual orthogonality of the intermediate shell G - P and outer shell M - G. -/
theorem orthogonal_middle_outer_shell [Ring R] (P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    IsOrthogonalPair (G - P) (M - G) := by
  have hPM := hFlag.sub_PM
  refine ⟨?_, ?_⟩
  · calc
      (G - P) * (M - G)
        = G * M - G * G - P * M + P * G := by noncomm_ring
      _ = G - G - P + P := by
          rw [hFlag.sub_GM.mul_right, hFlag.idem_G.idem, hPM.mul_right, hFlag.sub_PG.mul_right]
      _ = 0 := by noncomm_ring
  · calc
      (M - G) * (G - P)
        = M * G - M * P - G * G + G * P := by noncomm_ring
      _ = G - P - G + P := by
          rw [hFlag.sub_GM.mul_left, hPM.mul_left, hFlag.idem_G.idem, hFlag.sub_PG.mul_left]
      _ = 0 := by noncomm_ring

/-!
### Archetype α₃: Coarse-Graining Conditional Expectation & Boundary Absorptions
Causal Dependency: α₀, α₁ ≺ α₃
-/

/-- Single-stratum coarse-graining (pinching) conditional expectation:
E_P(X) = P * X * P + (1 - P) * X * (1 - P). -/
def coarseGrain [Ring R] (P X : Matrix n n R) : Matrix n n R :=
  P * X * P + (1 - P) * X * (1 - P)

/-- Two-level flag coarse-graining conditional expectation across P ≼ G:
E_{P,G}(X) = P * X * P + (G - P) * X * (G - P) + (1 - G) * X * (1 - G). -/
def coarseGrain2 [Ring R] (P G X : Matrix n n R) : Matrix n n R :=
  P * X * P + (G - P) * X * (G - P) + (1 - G) * X * (1 - G)

/-- Three-level flag coarse-graining conditional expectation across P ≼ G ≼ M:
E_{P,G,M}(X) = P * X * P + (G - P) * X * (G - P) + (M - G) * X * (M - G) + (1 - M) * X * (1 - M). -/
def coarseGrain3 [Ring R] (P G M X : Matrix n n R) : Matrix n n R :=
  P * X * P + (G - P) * X * (G - P) + (M - G) * X * (M - G) + (1 - M) * X * (1 - M)

lemma one_sub_mul_of_subprojection [Ring R] (P G : Matrix n n R)
    (hPG : Subprojection P G) :
    (1 - P) * G = G - P := by
  calc
    (1 - P) * G = G - P * G := by noncomm_ring
    _ = G - P := by rw [hPG.mul_right]

lemma mul_one_sub_of_subprojection [Ring R] (P G : Matrix n n R)
    (hPG : Subprojection P G) :
    G * (1 - P) = G - P := by
  calc
    G * (1 - P) = G - G * P := by noncomm_ring
    _ = G - P := by rw [hPG.mul_left]

lemma mul_one_sub_coarse_zero [Ring R] (P G : Matrix n n R)
    (hPG : Subprojection P G) :
    P * (1 - G) = 0 := by
  calc
    P * (1 - G) = P - P * G := by noncomm_ring
    _ = P - P := by rw [hPG.mul_right]
    _ = 0 := sub_self P

lemma one_sub_coarse_mul_zero [Ring R] (P G : Matrix n n R)
    (hPG : Subprojection P G) :
    (1 - G) * P = 0 := by
  calc
    (1 - G) * P = P - G * P := by noncomm_ring
    _ = P - P := by rw [hPG.mul_left]
    _ = 0 := sub_self P

lemma one_sub_mul_one_sub_of_subprojection [Ring R] (P G : Matrix n n R)
    (hPG : Subprojection P G) :
    (1 - P) * (1 - G) = 1 - G := by
  calc
    (1 - P) * (1 - G) = 1 - G - P + P * G := by noncomm_ring
    _ = 1 - G - P + P := by rw [hPG.mul_right]
    _ = 1 - G := by noncomm_ring

lemma one_sub_coarse_mul_one_sub_of_subprojection [Ring R] (P G : Matrix n n R)
    (hPG : Subprojection P G) :
    (1 - G) * (1 - P) = 1 - G := by
  calc
    (1 - G) * (1 - P) = 1 - G - P + G * P := by noncomm_ring
    _ = 1 - G - P + P := by rw [hPG.mul_left]
    _ = 1 - G := by noncomm_ring

/-!
### Archetype α₄: Commuting Flag Expectations & Four-Stratum Pinching
Causal Dependency: α₂, α₃ ≺ α₄
-/

/-- Fine-after-coarse composition of conditional expectations when P ≼ G:
E_P(E_G(X)) = E_{P,G}(X). -/
theorem coarseGrain_comp_of_subprojection [Ring R] (P G X : Matrix n n R)
    (hPG : Subprojection P G) :
    coarseGrain P (coarseGrain G X) = coarseGrain2 P G X := by
  dsimp [coarseGrain, coarseGrain2]
  calc
    P * (G * X * G + (1 - G) * X * (1 - G)) * P +
      (1 - P) * (G * X * G + (1 - G) * X * (1 - G)) * (1 - P)
      = (P * G) * X * (G * P) + (P * (1 - G)) * X * ((1 - G) * P) +
        ((1 - P) * G) * X * (G * (1 - P)) +
        ((1 - P) * (1 - G)) * X * ((1 - G) * (1 - P)) := by noncomm_ring
    _ = P * X * P + 0 * X * 0 + (G - P) * X * (G - P) + (1 - G) * X * (1 - G) := by
        rw [hPG.mul_right, hPG.mul_left,
            mul_one_sub_coarse_zero P G hPG, one_sub_coarse_mul_zero P G hPG,
            one_sub_mul_of_subprojection P G hPG, mul_one_sub_of_subprojection P G hPG,
            one_sub_mul_one_sub_of_subprojection P G hPG,
            one_sub_coarse_mul_one_sub_of_subprojection P G hPG]
    _ = P * X * P + (G - P) * X * (G - P) + (1 - G) * X * (1 - G) := by noncomm_ring

/-- Coarse-after-fine composition of conditional expectations when P ≼ G:
E_G(E_P(X)) = E_{P,G}(X). -/
theorem coarseGrain_comp_symm_of_subprojection [Ring R] (P G X : Matrix n n R)
    (hPG : Subprojection P G) :
    coarseGrain G (coarseGrain P X) = coarseGrain2 P G X := by
  dsimp [coarseGrain, coarseGrain2]
  calc
    G * (P * X * P + (1 - P) * X * (1 - P)) * G +
      (1 - G) * (P * X * P + (1 - P) * X * (1 - P)) * (1 - G)
      = (G * P) * X * (P * G) + (G * (1 - P)) * X * ((1 - P) * G) +
        ((1 - G) * P) * X * (P * (1 - G)) +
        ((1 - G) * (1 - P)) * X * ((1 - P) * (1 - G)) := by noncomm_ring
    _ = P * X * P + (G - P) * X * (G - P) + 0 * X * 0 + (1 - G) * X * (1 - G) := by
        rw [hPG.mul_left, hPG.mul_right,
            mul_one_sub_of_subprojection P G hPG, one_sub_mul_of_subprojection P G hPG,
            one_sub_coarse_mul_zero P G hPG, mul_one_sub_coarse_zero P G hPG,
            one_sub_coarse_mul_one_sub_of_subprojection P G hPG,
            one_sub_mul_one_sub_of_subprojection P G hPG]
    _ = P * X * P + (G - P) * X * (G - P) + (1 - G) * X * (1 - G) := by noncomm_ring

/-- Commutativity of Coarse-Graining Projections under Taxonomic Inclusion P ≼ G:
E_P(E_G(X)) = E_G(E_P(X)). -/
theorem coarseGrain_comm_of_subprojection [Ring R] (P G X : Matrix n n R)
    (hPG : Subprojection P G) :
    coarseGrain P (coarseGrain G X) = coarseGrain G (coarseGrain P X) := by
  rw [coarseGrain_comp_of_subprojection P G X hPG,
      coarseGrain_comp_symm_of_subprojection P G X hPG]

/-- In a 3-level flag P ≼ G ≼ M, E_P and E_G commute. -/
theorem coarseGrain_comm_PG [Ring R] (P G M X : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    coarseGrain P (coarseGrain G X) = coarseGrain G (coarseGrain P X) :=
  coarseGrain_comm_of_subprojection P G X hFlag.sub_PG

/-- In a 3-level flag P ≼ G ≼ M, E_G and E_M commute. -/
theorem coarseGrain_comm_GM [Ring R] (P G M X : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    coarseGrain G (coarseGrain M X) = coarseGrain M (coarseGrain G X) :=
  coarseGrain_comm_of_subprojection G M X hFlag.sub_GM

/-- In a 3-level flag P ≼ G ≼ M, E_P and E_M commute. -/
theorem coarseGrain_comm_PM [Ring R] (P G M X : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    coarseGrain P (coarseGrain M X) = coarseGrain M (coarseGrain P X) :=
  coarseGrain_comm_of_subprojection P M X hFlag.sub_PM

lemma one_sub_mul_shell_of_flag [Ring R] (P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    (1 - P) * (M - G) = M - G := by
  have hOrth := orthogonal_fine_outer_shell P G M hFlag
  calc
    (1 - P) * (M - G) = (M - G) - P * (M - G) := by noncomm_ring
    _ = (M - G) - 0 := by rw [hOrth.mul_eq_zero]
    _ = M - G := sub_zero (M - G)

lemma shell_mul_one_sub_of_flag [Ring R] (P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    (M - G) * (1 - P) = M - G := by
  have hOrth := orthogonal_fine_outer_shell P G M hFlag
  calc
    (M - G) * (1 - P) = (M - G) - (M - G) * P := by noncomm_ring
    _ = (M - G) - 0 := by rw [hOrth.rev_eq_zero]
    _ = M - G := sub_zero (M - G)

/-- Three-Level Flag Coarse-Graining Theorem:
Composing the three commuting conditional expectations E_P ∘ E_G ∘ E_M along a
3-level flag P ≼ G ≼ M produces the 4-stratum Peirce flag projection E_{P,G,M}. -/
theorem coarseGrain_three_level_flag [Ring R] (P G M X : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    coarseGrain P (coarseGrain G (coarseGrain M X)) = coarseGrain3 P G M X := by
  have hPM := hFlag.sub_PM
  have hOrth := orthogonal_fine_outer_shell P G M hFlag
  rw [coarseGrain_comp_of_subprojection G M X hFlag.sub_GM]
  dsimp [coarseGrain, coarseGrain2, coarseGrain3]
  calc
    P * (G * X * G + (M - G) * X * (M - G) + (1 - M) * X * (1 - M)) * P +
      (1 - P) * (G * X * G + (M - G) * X * (M - G) + (1 - M) * X * (1 - M)) * (1 - P)
      = (P * G) * X * (G * P) +
        (P * (M - G)) * X * ((M - G) * P) +
        (P * (1 - M)) * X * ((1 - M) * P) +
        ((1 - P) * G) * X * (G * (1 - P)) +
        ((1 - P) * (M - G)) * X * ((M - G) * (1 - P)) +
        ((1 - P) * (1 - M)) * X * ((1 - M) * (1 - P)) := by noncomm_ring
    _ = P * X * P + 0 * X * 0 + 0 * X * 0 +
        (G - P) * X * (G - P) + (M - G) * X * (M - G) + (1 - M) * X * (1 - M) := by
        rw [hFlag.sub_PG.mul_right, hFlag.sub_PG.mul_left,
            hOrth.mul_eq_zero, hOrth.rev_eq_zero,
            mul_one_sub_coarse_zero P M hPM, one_sub_coarse_mul_zero P M hPM,
            one_sub_mul_of_subprojection P G hFlag.sub_PG,
            mul_one_sub_of_subprojection P G hFlag.sub_PG,
            one_sub_mul_shell_of_flag P G M hFlag,
            shell_mul_one_sub_of_flag P G M hFlag,
            one_sub_mul_one_sub_of_subprojection P M hPM,
            one_sub_coarse_mul_one_sub_of_subprojection P M hPM]
    _ = P * X * P + (G - P) * X * (G - P) + (M - G) * X * (M - G) + (1 - M) * X * (1 - M) := by
        noncomm_ring

/-- Order-Invariance of Three-Level Flag Coarse-Graining:
E_M(E_G(E_P(X))) = E_P(E_G(E_M(X))) = E_{P,G,M}(X). -/
theorem coarseGrain_three_level_flag_rev [Ring R] (P G M X : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    coarseGrain M (coarseGrain G (coarseGrain P X)) = coarseGrain3 P G M X := by
  rw [← coarseGrain_comm_of_subprojection P G X hFlag.sub_PG]
  rw [← coarseGrain_comm_of_subprojection P M (coarseGrain G X) hFlag.sub_PM]
  rw [← coarseGrain_comm_of_subprojection G M X hFlag.sub_GM]
  exact coarseGrain_three_level_flag P G M X hFlag

/-!
### Archetype α₅: Corner-Confined Connes Curvature
Causal Dependency: α₀, α₁ ≺ α₅
-/

/-- The local Chern-Connes 2-chain operator density C(D, S) = S * [D, S] * [D, S]. -/
def connesDensity [Ring R] (D S : Matrix n n R) : Matrix n n R :=
  S * (commutator D S * commutator D S)

/-- The Connes cyclic cocycle pairing τ(S * [D, S] * [D, S]) = tr(S * [D, S]²). -/
def connesCocycle [CommRing R] (D S : Matrix n n R) : R :=
  Matrix.trace (connesDensity D S)

/-- Connes Curvature Commutation Theorem:
For any idempotent stratum S² = S, the curvature [D, S]² commutes with S:
S * [D, S]² = [D, S]² * S. -/
theorem connes_curvature_commutes_with_stratum [Ring R] (D S : Matrix n n R)
    (hS : IsIdempotent S) :
    S * (commutator D S * commutator D S) = (commutator D S * commutator D S) * S := by
  dsimp [commutator]
  have hL : S * ((D * S - S * D) * (D * S - S * D)) = S * D * S * D * S - S * D * D * S := by
    calc
      S * ((D * S - S * D) * (D * S - S * D))
        = S * D * S * D * S - S * D * (S * S) * D - (S * S) * D * D * S + (S * S) * D * S * D := by
          noncomm_ring
      _ = S * D * S * D * S - S * D * S * D - S * D * D * S + S * D * S * D := by
          rw [hS.idem]
      _ = S * D * S * D * S - S * D * D * S := by
          noncomm_ring
  have hR : (D * S - S * D) * (D * S - S * D) * S = S * D * S * D * S - S * D * D * S := by
    calc
      (D * S - S * D) * (D * S - S * D) * S
        = D * S * D * (S * S) - D * (S * S) * D * S - S * D * D * (S * S) + S * D * S * D * S := by
          noncomm_ring
      _ = D * S * D * S - D * S * D * S - S * D * D * S + S * D * S * D * S := by
          rw [hS.idem]
      _ = S * D * S * D * S - S * D * D * S := by
          noncomm_ring
  rw [hL, hR]

/-- Corner Self-Compression of Connes Curvature:
For any idempotent stratum S² = S, the two-sided Peirce corner compression
S * [D, S]² * S equals the left-compressed Chern-Connes density S * [D, S]². -/
theorem connes_curvature_corner_self [Ring R] (D S : Matrix n n R)
    (hS : IsIdempotent S) :
    S * (commutator D S * commutator D S) * S =
    S * (commutator D S * commutator D S) := by
  calc
    S * (commutator D S * commutator D S) * S
      = ((commutator D S * commutator D S) * S) * S := by
        rw [connes_curvature_commutes_with_stratum D S hS]
    _ = (commutator D S * commutator D S) * (S * S) := by noncomm_ring
    _ = (commutator D S * commutator D S) * S := by rw [hS.idem]
    _ = S * (commutator D S * commutator D S) := by
        rw [← connes_curvature_commutes_with_stratum D S hS]

/-!
### Archetype α₆: Three-Stratum Curvature & Cyclic Cocycle Decomposition
Causal Dependency: α₂, α₄, α₅ ≺ α₆
-/

/-- The total 3-stratum Chern-Connes flag density across S₁ = P, S₂ = G - P, S₃ = M - G. -/
def flagConnesDensity [Ring R] (D P G M : Matrix n n R) : Matrix n n R :=
  connesDensity D P + connesDensity D (G - P) + connesDensity D (M - G)

/-- Diagonal Peirce Corner Decomposition of the 3-Stratum Chern-Connes Density:
Across a 3-level flag P ≼ G ≼ M, the total flag density decomposes into the sum of
the three mutually orthogonal Peirce corner compressions S_i * [D, S_i]² * S_i. -/
theorem flagConnesDensity_corner_decomp [Ring R] (D P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    flagConnesDensity D P G M =
    P * (commutator D P * commutator D P) * P +
    (G - P) * (commutator D (G - P) * commutator D (G - P)) * (G - P) +
    (M - G) * (commutator D (M - G) * commutator D (M - G)) * (M - G) := by
  have hGP : IsIdempotent (G - P) :=
    idempotent_relative_complement P G hFlag.idem_P hFlag.idem_G hFlag.sub_PG
  have hMG : IsIdempotent (M - G) :=
    idempotent_relative_complement G M hFlag.idem_G hFlag.idem_M hFlag.sub_GM
  dsimp [flagConnesDensity, connesDensity]
  rw [connes_curvature_corner_self D P hFlag.idem_P,
      connes_curvature_corner_self D (G - P) hGP,
      connes_curvature_corner_self D (M - G) hMG]

/-- Unconditional 3-Stratum Partition of Any Macro-Compressed Curvature M * Ω:
M * [D, P]² = P * [D, P]² + (G - P) * [D, P]² + (M - G) * [D, P]². -/
theorem macro_curvature_three_stratum_split [Ring R] (D P G M : Matrix n n R) :
    M * (commutator D P * commutator D P) =
    P * (commutator D P * commutator D P) +
    (G - P) * (commutator D P * commutator D P) +
    (M - G) * (commutator D P * commutator D P) := by
  noncomm_ring

/-- Three-Stratum Derivation Balance:
[D, P] + [D, G - P] + [D, M - G] = [D, M]. -/
theorem three_stratum_derivation_sum [Ring R] (D P G M : Matrix n n R) :
    commutator D P + commutator D (G - P) + commutator D (M - G) =
    commutator D M := by
  dsimp [commutator]
  noncomm_ring

/-- Conservation of Total Derivation under Macro-Stratum Invariance ([D, M] = 0):
[D, P] + [D, G - P] + [D, M - G] = 0. -/
theorem three_stratum_derivation_sum_zero [Ring R] (D P G M : Matrix n n R)
    (hDM : commutator D M = 0) :
    commutator D P + commutator D (G - P) + commutator D (M - G) = 0 := by
  rw [three_stratum_derivation_sum D P G M, hDM]

/-- When [D, G] = 0, the sibling stratum G - P satisfies [D, G - P] = -[D, P]. -/
theorem commutator_relative_complement [Ring R] (D P G : Matrix n n R)
    (hDG : commutator D G = 0) :
    commutator D (G - P) = - commutator D P := by
  rw [commutator_sub_right, hDG, zero_sub]

/-- Connes Curvature Equality of Complementary Strata:
When [D, G] = 0, [D, G - P]² = [D, P]². -/
theorem curvature_relative_complement_eq [Ring R] (D P G : Matrix n n R)
    (hDG : commutator D G = 0) :
    commutator D (G - P) * commutator D (G - P) =
    commutator D P * commutator D P := by
  rw [commutator_relative_complement D P G hDG, neg_mul_neg]

/-- Non-Commutative Gauss-Codazzi Curvature Decomposition of the Intermediate Stratum G:
The Connes curvature [D, G]² decomposes into the curvatures of P and G - P plus their
anticommutator cross-curvature {[D, P], [D, G - P]}. -/
theorem connes_curvature_genus_decomp [Ring R] (D P G : Matrix n n R) :
    commutator D G * commutator D G =
    commutator D P * commutator D P +
    commutator D (G - P) * commutator D (G - P) +
    (commutator D P * commutator D (G - P) +
     commutator D (G - P) * commutator D P) := by
  dsimp [commutator]
  noncomm_ring

/-- Three-Stratum Gauss-Codazzi Curvature Decomposition ([D, M] = 0):
When the Dirac operator preserves the macro-stratum M, the Connes curvature of the
outer shell M - G decomposes into the curvatures of the two inner shells P and G - P
plus their anticommutator interference term. -/
theorem connes_curvature_outer_shell_decomp [Ring R] (D P G M : Matrix n n R)
    (hDM : commutator D M = 0) :
    commutator D (M - G) * commutator D (M - G) =
    commutator D P * commutator D P +
    commutator D (G - P) * commutator D (G - P) +
    (commutator D P * commutator D (G - P) +
     commutator D (G - P) * commutator D P) := by
  rw [curvature_relative_complement_eq D G M hDM]
  exact connes_curvature_genus_decomp D P G

/-- Genus-Confined Evolutionary Derivation:
If P ≼ G and [D, G] = 0, then G * [D, P] * G = [D, P]. -/
theorem genus_confined_derivation [Ring R] (D P G : Matrix n n R)
    (hPG : Subprojection P G) (hDG : commutator D G = 0) :
    G * commutator D P * G = commutator D P := by
  have h1 : G * commutator D P * G = G * D * (P * G) - (G * P) * D * G := by
    dsimp [commutator]
    noncomm_ring
  rw [hPG.mul_right, hPG.mul_left] at h1
  have h2 : commutator D P = D * (G * P) - (P * G) * D := by
    rw [hPG.mul_left, hPG.mul_right]
    rfl
  have h3 : (G * D * P - P * D * G) - (D * (G * P) - (P * G) * D) =
      -(commutator D G * P) - P * commutator D G := by
    dsimp [commutator]
    noncomm_ring
  rw [← h1, ← h2, hDG] at h3
  have h4 : G * commutator D P * G - commutator D P = 0 := by
    calc
      G * commutator D P * G - commutator D P
        = -(0 * P) - P * 0 := h3
      _ = 0 := by noncomm_ring
  exact sub_eq_zero.mp h4

/-- Outer-Shell Annihilation of Genus-Confined Derivation:
In a 3-level flag P ≼ G ≼ M with [D, G] = 0, the outer shell M - G annihilates [D, P]. -/
theorem outer_shell_mul_derivation_zero [Ring R] (D P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) (hDG : commutator D G = 0) :
    (M - G) * commutator D P = 0 := by
  have h_conf := genus_confined_derivation D P G hFlag.sub_PG hDG
  have hMG : (M - G) * G = 0 := by
    calc (M - G) * G = M * G - G * G := by noncomm_ring
    _ = G - G := by rw [hFlag.sub_GM.mul_left, hFlag.idem_G.idem]
    _ = 0 := sub_self G
  calc
    (M - G) * commutator D P
      = (M - G) * (G * commutator D P * G) := by nth_rw 1 [← h_conf]
    _ = ((M - G) * G) * (commutator D P * G) := by noncomm_ring
    _ = 0 * (commutator D P * G) := by rw [hMG]
    _ = 0 := by noncomm_ring

/-- Outer-Shell Annihilation of Fine Connes Curvature:
In a 3-level flag P ≼ G ≼ M with [D, G] = 0, (M - G) * [D, P]² = 0. -/
theorem outer_shell_mul_curvature_zero [Ring R] (D P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) (hDG : commutator D G = 0) :
    (M - G) * (commutator D P * commutator D P) = 0 := by
  calc
    (M - G) * (commutator D P * commutator D P)
      = ((M - G) * commutator D P) * commutator D P := by noncomm_ring
    _ = 0 * commutator D P := by
        rw [outer_shell_mul_derivation_zero D P G M hFlag hDG]
    _ = 0 := by noncomm_ring

/-- Two-Stratum Partition of the Connes Cyclic Cocycle when [D, G] = 0. -/
theorem connes_cocycle_taxonomic_partition [CommRing R] (D P G : Matrix n n R)
    (hDG : commutator D G = 0) :
    connesCocycle D P + connesCocycle D (G - P) =
    Matrix.trace (G * (commutator D P * commutator D P)) := by
  dsimp [connesCocycle, connesDensity]
  rw [curvature_relative_complement_eq D P G hDG]
  rw [← Matrix.trace_add]
  have h_sum :
      P * (commutator D P * commutator D P) +
      (G - P) * (commutator D P * commutator D P) =
      G * (commutator D P * commutator D P) := by
    noncomm_ring
  rw [h_sum]

/-- Trace Decomposition of the 3-Stratum Flag Density into Connes Cyclic Cocycles. -/
theorem trace_flagConnesDensity_decomp [CommRing R] (D P G M : Matrix n n R) :
    Matrix.trace (flagConnesDensity D P G M) =
    connesCocycle D P + connesCocycle D (G - P) + connesCocycle D (M - G) := by
  dsimp [flagConnesDensity, connesCocycle]
  rw [Matrix.trace_add, Matrix.trace_add]

/-- Master Three-Stratum Connes Cyclic Cocycle Decomposition Theorem:
In a 3-level flag P ≼ G ≼ M where the Dirac generator preserves both coarse strata
([D, G] = 0 and [D, M] = 0), the sum of the Connes cyclic cocycles across all three
strata (P, G - P, M - G) equals the macro-compressed curvature trace tr(M * [D, P]²). -/
theorem three_stratum_cocycle_macro_partition [CommRing R] (D P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M)
    (hDG : commutator D G = 0) (hDM : commutator D M = 0) :
    connesCocycle D P + connesCocycle D (G - P) + connesCocycle D (M - G) =
    Matrix.trace (M * (commutator D P * commutator D P)) := by
  have h_third : connesCocycle D (M - G) = 0 := by
    dsimp [connesCocycle, connesDensity]
    rw [curvature_relative_complement_eq D G M hDM, hDG, mul_zero, mul_zero,
        Matrix.trace_zero]
  rw [h_third, add_zero, connes_cocycle_taxonomic_partition D P G hDG]
  have h_outer := outer_shell_mul_curvature_zero D P G M hFlag hDG
  have h_split :
      M * (commutator D P * commutator D P) =
      G * (commutator D P * commutator D P) +
      (M - G) * (commutator D P * commutator D P) := by
    noncomm_ring
  rw [h_split, h_outer, add_zero]

end NonCommutativeFlagHierarchy
