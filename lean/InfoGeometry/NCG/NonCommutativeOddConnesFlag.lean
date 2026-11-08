/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NonCommutativeOddConnesFlag

open Matrix

variable {R : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-!
### Archetype α₀: The Primordial Non-Abelian Substrate & Inner Derivation
-/

/-- The non-commutative inner derivation δ_D(X) = [D, X] = D * X - X * D on M_n(R). -/
def commutator [Ring R] (D X : Matrix n n R) : Matrix n n R :=
  D * X - X * D

/-- Right addition linearity of the evolutionary derivation:
[D, X + Y] = [D, X] + [D, Y]. -/
lemma commutator_add_right [Ring R] (D X Y : Matrix n n R) :
    commutator D (X + Y) = commutator D X + commutator D Y := by
  dsimp [commutator]
  noncomm_ring

/-- Left addition linearity of the evolutionary derivation:
[D₁ + D₂, X] = [D₁, X] + [D₂, X]. -/
lemma commutator_add_left [Ring R] (D₁ D₂ X : Matrix n n R) :
    commutator (D₁ + D₂) X = commutator D₁ X + commutator D₂ X := by
  dsimp [commutator]
  noncomm_ring

/-- The non-commutative Leibniz cocycle rule: [D, X * Y] = [D, X] * Y + X * [D, Y]. -/
theorem commutator_leibniz [Ring R] (D X Y : Matrix n n R) :
    commutator D (X * Y) = commutator D X * Y + X * commutator D Y := by
  dsimp [commutator]
  noncomm_ring

/-- Homological Trace Vanishing: tr([D, X]) = 0. -/
theorem trace_commutator_zero [CommRing R] (D X : Matrix n n R) :
    Matrix.trace (commutator D X) = 0 := by
  dsimp [commutator]
  rw [Matrix.trace_sub, Matrix.trace_mul_comm D X, sub_self]

/-!
### Archetype α₁: The Three-Level Projection Flag (P ≼ G ≼ M)
Causal Dependency: α₀ ≺ α₁
-/

/-- An idempotent projection operator (taxonomic stratum) S² = S in M_n(R). -/
structure IsIdempotent [Ring R] (S : Matrix n n R) : Prop where
  idem : S * S = S

/-- Non-commutative taxonomic subprojection relation P ≼ G:
P is absorbed on both the right and left by the coarser projection G. -/
structure Subprojection [Ring R] (P G : Matrix n n R) : Prop where
  mul_right : P * G = P
  mul_left  : G * P = P

/-- Transitivity of the taxonomic subprojection order across P ≼ G ≼ M. -/
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

/-- Two operator strata S₁ and S₂ are mutually orthogonal if S₁ * S₂ = 0 and S₂ * S₁ = 0. -/
structure IsOrthogonalPair [Ring R] (S₁ S₂ : Matrix n n R) : Prop where
  mul_eq_zero : S₁ * S₂ = 0
  rev_eq_zero : S₂ * S₁ = 0

/-- Symmetry of the mutual orthogonality relation. -/
lemma IsOrthogonalPair.symm [Ring R] {S₁ S₂ : Matrix n n R}
    (h : IsOrthogonalPair S₁ S₂) : IsOrthogonalPair S₂ S₁ :=
  ⟨h.rev_eq_zero, h.mul_eq_zero⟩

/-- Any idempotent stratum S is mutually orthogonal to its unital complement 1 - S. -/
theorem orthogonal_complement_one [Ring R] (S : Matrix n n R)
    (hS : IsIdempotent S) :
    IsOrthogonalPair S (1 - S) := by
  refine ⟨?_, ?_⟩
  · calc
      S * (1 - S) = S - S * S := by noncomm_ring
      _ = S - S := by rw [hS.idem]
      _ = 0 := sub_self S
  · calc
      (1 - S) * S = S - S * S := by noncomm_ring
      _ = S - S := by rw [hS.idem]
      _ = 0 := sub_self S

/-- The unital complement 1 - S of an idempotent S is idempotent. -/
theorem idempotent_complement_one [Ring R] (S : Matrix n n R)
    (hS : IsIdempotent S) :
    IsIdempotent (1 - S) := by
  refine ⟨?_⟩
  calc
    (1 - S) * (1 - S) = 1 - S - S + S * S := by noncomm_ring
    _ = 1 - S - S + S := by rw [hS.idem]
    _ = 1 - S := by noncomm_ring

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
### Archetype α₂: The Corner Unitary Group U(S * A * S)
Causal Dependency: α₀ ≺ α₁ ≺ α₂
-/

/-- A corner unitary pair (U, U_star) inside the Peirce corner algebra S * M_n(R) * S
of an idempotent stratum S. -/
structure IsCornerUnitary [Ring R] (U U_star S : Matrix n n R) : Prop where
  star_mul_self    : U_star * U = S
  mul_star_self    : U * U_star = S
  mul_stratum      : U * S = U
  stratum_mul      : S * U = U
  star_mul_stratum : U_star * S = U_star
  stratum_mul_star : S * U_star = U_star

/-- Every idempotent stratum S is the identity corner unitary of its own corner algebra. -/
theorem cornerUnitary_id [Ring R] (S : Matrix n n R) (hS : IsIdempotent S) :
    IsCornerUnitary S S S :=
  ⟨hS.idem, hS.idem, hS.idem, hS.idem, hS.idem, hS.idem⟩

/-- Inversion Symmetry of Corner Unitaries:
If (U, U_star) is a corner unitary on S, then (U_star, U) is also a corner unitary on S. -/
theorem cornerUnitary_symm [Ring R] {U U_star S : Matrix n n R}
    (hU : IsCornerUnitary U U_star S) :
    IsCornerUnitary U_star U S :=
  ⟨hU.mul_star_self, hU.star_mul_self, hU.star_mul_stratum,
   hU.stratum_mul_star, hU.mul_stratum, hU.stratum_mul⟩

/-- Non-Abelian Group Closure of Corner Unitaries:
If (U₁, U₁_star) and (U₂, U₂_star) are corner unitaries on S, then their composition
(U₁ * U₂, U₂_star * U₁_star) is a corner unitary on S. -/
theorem cornerUnitary_mul [Ring R] {U₁ U₁_star U₂ U₂_star S : Matrix n n R}
    (hU₁ : IsCornerUnitary U₁ U₁_star S)
    (hU₂ : IsCornerUnitary U₂ U₂_star S) :
    IsCornerUnitary (U₁ * U₂) (U₂_star * U₁_star) S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (U₂_star * U₁_star) * (U₁ * U₂)
        = U₂_star * (U₁_star * U₁) * U₂ := by noncomm_ring
      _ = (U₂_star * S) * U₂ := by rw [hU₁.star_mul_self, mul_assoc]
      _ = U₂_star * U₂ := by rw [hU₂.star_mul_stratum]
      _ = S := hU₂.star_mul_self
  · calc
      (U₁ * U₂) * (U₂_star * U₁_star)
        = U₁ * (U₂ * U₂_star) * U₁_star := by noncomm_ring
      _ = (U₁ * S) * U₁_star := by rw [hU₂.mul_star_self, mul_assoc]
      _ = U₁ * U₁_star := by rw [hU₁.mul_stratum]
      _ = S := hU₁.mul_star_self
  · calc
      (U₁ * U₂) * S = U₁ * (U₂ * S) := by rw [mul_assoc]
      _ = U₁ * U₂ := by rw [hU₂.mul_stratum]
  · calc
      S * (U₁ * U₂) = (S * U₁) * U₂ := by rw [mul_assoc]
      _ = U₁ * U₂ := by rw [hU₁.stratum_mul]
  · calc
      (U₂_star * U₁_star) * S = U₂_star * (U₁_star * S) := by rw [mul_assoc]
      _ = U₂_star * U₁_star := by rw [hU₁.star_mul_stratum]
  · calc
      S * (U₂_star * U₁_star) = (S * U₂_star) * U₁_star := by rw [mul_assoc]
      _ = U₂_star * U₁_star := by rw [hU₂.stratum_mul_star]

/-!
### Archetype α₃: Orthogonal Block-Sum Fusion & Unitalization
Causal Dependency: α₁, α₂ ≺ α₃
-/

/-- Orthogonal Annihilation of Corner Unitaries:
If S₁ and S₂ are orthogonal strata, any corner element on S₁ annihilates any corner
element on S₂. -/
lemma corner_mul_zero_of_orthogonal [Ring R] {A B S₁ S₂ : Matrix n n R}
    (hA : A * S₁ = A) (hB : S₂ * B = B) (hOrth : IsOrthogonalPair S₁ S₂) :
    A * B = 0 := by
  calc
    A * B = (A * S₁) * (S₂ * B) := by rw [hA, hB]
    _ = A * (S₁ * S₂) * B := by noncomm_ring
    _ = A * 0 * B := by rw [hOrth.mul_eq_zero]
    _ = 0 := by noncomm_ring

/-- Direct-Sum Block Fusion of Orthogonal Corner Unitaries:
If (U₁, U₁_star) is a corner unitary on S₁, (U₂, U₂_star) is a corner unitary on S₂,
and S₁ ⊥ S₂, then (U₁ + U₂, U₁_star + U₂_star) is a corner unitary on S₁ + S₂. -/
theorem cornerUnitary_orthogonal_add [Ring R]
    {U₁ U₁_star S₁ U₂ U₂_star S₂ : Matrix n n R}
    (hU₁ : IsCornerUnitary U₁ U₁_star S₁)
    (hU₂ : IsCornerUnitary U₂ U₂_star S₂)
    (hOrth : IsOrthogonalPair S₁ S₂) :
    IsCornerUnitary (U₁ + U₂) (U₁_star + U₂_star) (S₁ + S₂) := by
  have h12 : U₁_star * U₂ = 0 :=
    corner_mul_zero_of_orthogonal hU₁.star_mul_stratum hU₂.stratum_mul hOrth
  have h21 : U₂_star * U₁ = 0 :=
    corner_mul_zero_of_orthogonal hU₂.star_mul_stratum hU₁.stratum_mul hOrth.symm
  have h12' : U₁ * U₂_star = 0 :=
    corner_mul_zero_of_orthogonal hU₁.mul_stratum hU₂.stratum_mul_star hOrth
  have h21' : U₂ * U₁_star = 0 :=
    corner_mul_zero_of_orthogonal hU₂.mul_stratum hU₁.stratum_mul_star hOrth.symm
  have hU1S2 : U₁ * S₂ = 0 := by
    calc U₁ * S₂ = (U₁ * S₁) * S₂ := by rw [hU₁.mul_stratum]
    _ = U₁ * (S₁ * S₂) := by rw [mul_assoc]
    _ = U₁ * 0 := by rw [hOrth.mul_eq_zero]
    _ = 0 := mul_zero U₁
  have hU2S1 : U₂ * S₁ = 0 := by
    calc U₂ * S₁ = (U₂ * S₂) * S₁ := by rw [hU₂.mul_stratum]
    _ = U₂ * (S₂ * S₁) := by rw [mul_assoc]
    _ = U₂ * 0 := by rw [hOrth.rev_eq_zero]
    _ = 0 := mul_zero U₂
  have hS2U1 : S₂ * U₁ = 0 := by
    calc S₂ * U₁ = S₂ * (S₁ * U₁) := by rw [hU₁.stratum_mul]
    _ = (S₂ * S₁) * U₁ := by rw [mul_assoc]
    _ = 0 * U₁ := by rw [hOrth.rev_eq_zero]
    _ = 0 := zero_mul U₁
  have hS1U2 : S₁ * U₂ = 0 := by
    calc S₁ * U₂ = S₁ * (S₂ * U₂) := by rw [hU₂.stratum_mul]
    _ = (S₁ * S₂) * U₂ := by rw [mul_assoc]
    _ = 0 * U₂ := by rw [hOrth.mul_eq_zero]
    _ = 0 := zero_mul U₂
  have hU1sS2 : U₁_star * S₂ = 0 := by
    calc U₁_star * S₂ = (U₁_star * S₁) * S₂ := by rw [hU₁.star_mul_stratum]
    _ = U₁_star * (S₁ * S₂) := by rw [mul_assoc]
    _ = U₁_star * 0 := by rw [hOrth.mul_eq_zero]
    _ = 0 := mul_zero U₁_star
  have hU2sS1 : U₂_star * S₁ = 0 := by
    calc U₂_star * S₁ = (U₂_star * S₂) * S₁ := by rw [hU₂.star_mul_stratum]
    _ = U₂_star * (S₂ * S₁) := by rw [mul_assoc]
    _ = U₂_star * 0 := by rw [hOrth.rev_eq_zero]
    _ = 0 := mul_zero U₂_star
  have hS2U1s : S₂ * U₁_star = 0 := by
    calc S₂ * U₁_star = S₂ * (S₁ * U₁_star) := by rw [hU₁.stratum_mul_star]
    _ = (S₂ * S₁) * U₁_star := by rw [mul_assoc]
    _ = 0 * U₁_star := by rw [hOrth.rev_eq_zero]
    _ = 0 := zero_mul U₁_star
  have hS1U2s : S₁ * U₂_star = 0 := by
    calc S₁ * U₂_star = S₁ * (S₂ * U₂_star) := by rw [hU₂.stratum_mul_star]
    _ = (S₁ * S₂) * U₂_star := by rw [mul_assoc]
    _ = 0 * U₂_star := by rw [hOrth.mul_eq_zero]
    _ = 0 := zero_mul U₂_star
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (U₁_star + U₂_star) * (U₁ + U₂)
        = U₁_star * U₁ + U₁_star * U₂ + U₂_star * U₁ + U₂_star * U₂ := by noncomm_ring
      _ = S₁ + 0 + 0 + S₂ := by rw [hU₁.star_mul_self, h12, h21, hU₂.star_mul_self]
      _ = S₁ + S₂ := by abel
  · calc
      (U₁ + U₂) * (U₁_star + U₂_star)
        = U₁ * U₁_star + U₁ * U₂_star + U₂ * U₁_star + U₂ * U₂_star := by noncomm_ring
      _ = S₁ + 0 + 0 + S₂ := by rw [hU₁.mul_star_self, h12', h21', hU₂.mul_star_self]
      _ = S₁ + S₂ := by abel
  · calc
      (U₁ + U₂) * (S₁ + S₂)
        = U₁ * S₁ + U₁ * S₂ + U₂ * S₁ + U₂ * S₂ := by noncomm_ring
      _ = U₁ + 0 + 0 + U₂ := by rw [hU₁.mul_stratum, hU1S2, hU2S1, hU₂.mul_stratum]
      _ = U₁ + U₂ := by abel
  · calc
      (S₁ + S₂) * (U₁ + U₂)
        = S₁ * U₁ + S₁ * U₂ + S₂ * U₁ + S₂ * U₂ := by noncomm_ring
      _ = U₁ + 0 + 0 + U₂ := by rw [hU₁.stratum_mul, hS1U2, hS2U1, hU₂.stratum_mul]
      _ = U₁ + U₂ := by abel
  · calc
      (U₁_star + U₂_star) * (S₁ + S₂)
        = U₁_star * S₁ + U₁_star * S₂ + U₂_star * S₁ + U₂_star * S₂ := by noncomm_ring
      _ = U₁_star + 0 + 0 + U₂_star := by
          rw [hU₁.star_mul_stratum, hU1sS2, hU2sS1, hU₂.star_mul_stratum]
      _ = U₁_star + U₂_star := by abel
  · calc
      (S₁ + S₂) * (U₁_star + U₂_star)
        = S₁ * U₁_star + S₁ * U₂_star + S₂ * U₁_star + S₂ * U₂_star := by noncomm_ring
      _ = U₁_star + 0 + 0 + U₂_star := by
          rw [hU₁.stratum_mul_star, hS1U2s, hS2U1s, hU₂.stratum_mul_star]
      _ = U₁_star + U₂_star := by abel

/-- Canonical Unitalization of a Corner Unitary:
U_tilde = U + (1 - S) extends a corner unitary on S by the identity on 1 - S. -/
def unitalizeCorner [Ring R] (U S : Matrix n n R) : Matrix n n R :=
  U + (1 - S)

/-- Global Unital Unitary Theorem for Corner Unitalizations:
If (U, U_star) is a corner unitary on an idempotent stratum S, then
(U + (1 - S), U_star + (1 - S)) is a global unital unitary on M_n(R) (stratum 1). -/
theorem cornerUnitary_unitalize [Ring R] {U U_star S : Matrix n n R}
    (hS : IsIdempotent S) (hU : IsCornerUnitary U U_star S) :
    IsCornerUnitary (unitalizeCorner U S) (unitalizeCorner U_star S) 1 := by
  have hComp := cornerUnitary_id (1 - S) (idempotent_complement_one S hS)
  have hOrth := orthogonal_complement_one S hS
  have hSum := cornerUnitary_orthogonal_add hU hComp hOrth
  have hOne : S + (1 - S) = (1 : Matrix n n R) := by noncomm_ring
  dsimp [unitalizeCorner]
  rw [hOne] at hSum
  exact hSum

/-!
### Archetype α₄: The Non-Abelian Maurer–Cartan 1-Form ω_D(U*, U) = U* [D, U]
Causal Dependency: α₀, α₂ ≺ α₄
-/

/-- The non-commutative Maurer–Cartan 1-form (odd Connes operator density)
ω_D(U_star, U) = U_star * [D, U]. -/
def oddConnesDensity [Ring R] (D U_star U : Matrix n n R) : Matrix n n R :=
  U_star * commutator D U

/-- Left Stratum Absorption of the Odd Connes Operator Density:
For any corner unitary on S, S * ω_D(U_star, U) = ω_D(U_star, U). -/
lemma stratum_mul_oddConnesDensity [Ring R] (D : Matrix n n R)
    {U U_star S : Matrix n n R} (hU : IsCornerUnitary U U_star S) :
    S * oddConnesDensity D U_star U = oddConnesDensity D U_star U := by
  dsimp [oddConnesDensity]
  rw [← mul_assoc, hU.stratum_mul_star]

/-- Operator-Level Non-Abelian 1-Cocycle Law for the Maurer–Cartan 1-Form:
For any two corner unitaries (U₁, U₁_star) and (U₂, U₂_star) on S,
ω_D(U₂_star * U₁_star, U₁ * U₂) = U₂_star * ω_D(U₁_star, U₁) * U₂ + ω_D(U₂_star, U₂). -/
theorem oddConnesDensity_mul_cocycle [Ring R] (D : Matrix n n R)
    {U₁ U₁_star U₂ U₂_star S : Matrix n n R}
    (hU₁ : IsCornerUnitary U₁ U₁_star S)
    (hU₂ : IsCornerUnitary U₂ U₂_star S) :
    oddConnesDensity D (U₂_star * U₁_star) (U₁ * U₂) =
    U₂_star * oddConnesDensity D U₁_star U₁ * U₂ +
    oddConnesDensity D U₂_star U₂ := by
  dsimp [oddConnesDensity]
  calc
    (U₂_star * U₁_star) * commutator D (U₁ * U₂)
      = (U₂_star * U₁_star) * (commutator D U₁ * U₂ + U₁ * commutator D U₂) := by
        rw [commutator_leibniz D U₁ U₂]
    _ = U₂_star * (U₁_star * commutator D U₁) * U₂ +
        U₂_star * (U₁_star * U₁) * commutator D U₂ := by noncomm_ring
    _ = U₂_star * (U₁_star * commutator D U₁) * U₂ +
        (U₂_star * S) * commutator D U₂ := by
        rw [hU₁.star_mul_self, mul_assoc U₂_star S]
    _ = U₂_star * (U₁_star * commutator D U₁) * U₂ +
        U₂_star * commutator D U₂ := by rw [hU₂.star_mul_stratum]

/-- Operator-Level Inversion Law for the Maurer–Cartan 1-Form:
U * ω_D(U_star, U) * U_star + ω_D(U, U_star) * S = U * [D, S] * U_star. -/
theorem oddConnesDensity_inv_relation [Ring R] (D : Matrix n n R)
    {U U_star S : Matrix n n R} (hU : IsCornerUnitary U U_star S) :
    U * oddConnesDensity D U_star U * U_star + oddConnesDensity D U U_star * S =
    U * commutator D S * U_star := by
  dsimp [oddConnesDensity]
  calc
    U * (U_star * commutator D U) * U_star + (U * commutator D U_star) * S
      = U * (U_star * commutator D U) * U_star +
        (U * commutator D U_star) * (U * U_star) := by rw [← hU.mul_star_self]
    _ = U * (commutator D U_star * U + U_star * commutator D U) * U_star := by
        noncomm_ring
    _ = U * commutator D (U_star * U) * U_star := by
        rw [← commutator_leibniz D U_star U]
    _ = U * commutator D S * U_star := by rw [hU.star_mul_self]

/-- Corner Compression Identity for the Odd Connes Operator Density:
Compressing ω_D(U_star, U) on the right by S equals the density of the corner-compressed
Dirac operator S * D * S: ω_D(U_star, U) * S = ω_{S * D * S}(U_star, U). -/
theorem oddConnesDensity_mul_stratum_eq_compressed [Ring R] (D : Matrix n n R)
    {U U_star S : Matrix n n R} (hU : IsCornerUnitary U U_star S) :
    oddConnesDensity D U_star U * S = oddConnesDensity (S * D * S) U_star U := by
  have hS_idem : S * S = S := by
    calc S * S = S * (U * U_star) := by rw [hU.mul_star_self]
    _ = (S * U) * U_star := by rw [mul_assoc]
    _ = U * U_star := by rw [hU.stratum_mul]
    _ = S := hU.mul_star_self
  dsimp [oddConnesDensity, commutator]
  have h1 : (U_star * (D * U - U * D)) * S = U_star * D * U - S * D * S := by
    calc (U_star * (D * U - U * D)) * S
      = U_star * D * (U * S) - (U_star * U) * D * S := by noncomm_ring
      _ = U_star * D * U - S * D * S := by rw [hU.mul_stratum, hU.star_mul_self]
  have h2 : U_star * ((S * D * S) * U - U * (S * D * S)) = U_star * D * U - S * D * S := by
    calc U_star * ((S * D * S) * U - U * (S * D * S))
      = (U_star * S) * D * (S * U) - (U_star * U) * S * D * S := by noncomm_ring
      _ = U_star * D * U - S * S * D * S := by
          rw [hU.star_mul_stratum, hU.stratum_mul, hU.star_mul_self]
      _ = U_star * D * U - (S * S) * D * S := by noncomm_ring
      _ = U_star * D * U - S * D * S := by rw [hS_idem]
  rw [h1, h2]

/-!
### Archetype α₅: Logarithmic Additivity & Inversion of the Odd Connes 1-Cocycle
Causal Dependency: α₂, α₄ ≺ α₅
-/

/-- The odd Connes 1-cocycle pairing τ₁(D; U_star, U) = tr(U_star * [D, U]). -/
def oddConnesCocycle [CommRing R] (D U_star U : Matrix n n R) : R :=
  Matrix.trace (oddConnesDensity D U_star U)

/-- Trace Vanishing of Idempotent Self-Derivation:
For any idempotent stratum S² = S, τ₁(D; S, S) = tr(S * [D, S]) = 0. -/
theorem oddConnesCocycle_idempotent_zero [CommRing R] (D S : Matrix n n R)
    (hS : IsIdempotent S) :
    oddConnesCocycle D S S = 0 := by
  dsimp [oddConnesCocycle, oddConnesDensity, commutator]
  have h_alg : S * (D * S - S * D) = S * (D * S) - (S * S) * D := by noncomm_ring
  rw [h_alg, hS.idem, Matrix.trace_sub, Matrix.trace_mul_comm S (D * S)]
  have h_assoc : D * S * S = D * (S * S) := by noncomm_ring
  rw [h_assoc, hS.idem, Matrix.trace_mul_comm D S, sub_self]

/-- Unitary Conjugation Invariance of Trace on Stratum-Supported Operators:
If (U, U_star) is a corner unitary on S and S * X = X, then tr(U_star * X * U) = tr(X). -/
theorem trace_cornerUnitary_conj [CommRing R] {U U_star S X : Matrix n n R}
    (hU : IsCornerUnitary U U_star S) (hX : S * X = X) :
    Matrix.trace (U_star * X * U) = Matrix.trace X := by
  rw [Matrix.trace_mul_comm (U_star * X) U]
  have h_assoc : U * (U_star * X) = (U * U_star) * X := by noncomm_ring
  rw [h_assoc, hU.mul_star_self, hX]

/-- Logarithmic Additivity of the Odd Connes 1-Cocycle under Corner Unitary Composition:
For any two corner unitaries (U₁, U₁_star) and (U₂, U₂_star) on S,
τ₁(D; U₂_star * U₁_star, U₁ * U₂) = τ₁(D; U₁_star, U₁) + τ₁(D; U₂_star, U₂). -/
theorem oddConnesCocycle_mul_additive [CommRing R] (D : Matrix n n R)
    {U₁ U₁_star U₂ U₂_star S : Matrix n n R}
    (hU₁ : IsCornerUnitary U₁ U₁_star S)
    (hU₂ : IsCornerUnitary U₂ U₂_star S) :
    oddConnesCocycle D (U₂_star * U₁_star) (U₁ * U₂) =
    oddConnesCocycle D U₁_star U₁ + oddConnesCocycle D U₂_star U₂ := by
  dsimp [oddConnesCocycle]
  rw [oddConnesDensity_mul_cocycle D hU₁ hU₂, Matrix.trace_add]
  rw [trace_cornerUnitary_conj hU₂ (stratum_mul_oddConnesDensity D hU₁)]

/-- Abstract K₁-Pairing Additivity for Any S-Conjugation-Invariant Additive Functional τ:
Demonstrates that logarithmic additivity holds in arbitrary (including infinite-dimensional
Fredholm) settings where τ cycles corner unitaries without splitting [D, U]. -/
theorem oddConnesPairing_mul_additive [Ring R] (τ : Matrix n n R →+ R) (D : Matrix n n R)
    {U₁ U₁_star U₂ U₂_star S : Matrix n n R}
    (hU₁ : IsCornerUnitary U₁ U₁_star S)
    (hU₂ : IsCornerUnitary U₂ U₂_star S)
    (hτ_conj : ∀ X, S * X = X → τ (U₂_star * X * U₂) = τ X) :
    τ (oddConnesDensity D (U₂_star * U₁_star) (U₁ * U₂)) =
    τ (oddConnesDensity D U₁_star U₁) + τ (oddConnesDensity D U₂_star U₂) := by
  rw [oddConnesDensity_mul_cocycle D hU₁ hU₂, map_add]
  rw [hτ_conj (oddConnesDensity D U₁_star U₁) (stratum_mul_oddConnesDensity D hU₁)]

/-- Inversion Anti-Symmetry of the Odd Connes 1-Cocycle:
For any corner unitary (U, U_star) on an idempotent stratum S,
τ₁(D; U, U_star) = - τ₁(D; U_star, U). -/
theorem oddConnesCocycle_inv_neg [CommRing R] (D : Matrix n n R)
    {U U_star S : Matrix n n R}
    (hS : IsIdempotent S) (hU : IsCornerUnitary U U_star S) :
    oddConnesCocycle D U U_star = - oddConnesCocycle D U_star U := by
  have h_sum := oddConnesCocycle_mul_additive D (cornerUnitary_symm hU) hU
  rw [hU.star_mul_self, oddConnesCocycle_idempotent_zero D S hS] at h_sum
  exact eq_neg_of_add_eq_zero_left h_sum.symm

/-!
### Archetype α₆: Coarse-Graining, Unitalization & Three-Stratum Block Additivity
Causal Dependency: α₁, α₃, α₄, α₅ ≺ α₆
-/

/-- Single-stratum coarse-graining (pinching) conditional expectation:
E_S(D) = S * D * S + (1 - S) * D * (1 - S). -/
def coarseGrain [Ring R] (S D : Matrix n n R) : Matrix n n R :=
  S * D * S + (1 - S) * D * (1 - S)

/-- Three-level flag coarse-graining conditional expectation across P ≼ G ≼ M:
E_{P,G,M}(D) = P * D * P + (G - P) * D * (G - P) + (M - G) * D * (M - G) + (1 - M) * D * (1 - M). -/
def coarseGrain3 [Ring R] (P G M D : Matrix n n R) : Matrix n n R :=
  P * D * P + (G - P) * D * (G - P) + (M - G) * D * (M - G) + (1 - M) * D * (1 - M)

/-- Annihilation of Orthogonal Stratum Perturbations by Corner Unitaries:
If S₁ ⊥ S₂ and (U, U_star) is a corner unitary on S₁, then any operator S₂ * A * S₂
supported on S₂ commutes identically with U: [S₂ * A * S₂, U] = 0. -/
theorem commutator_orthogonal_corner_zero [Ring R] (A : Matrix n n R)
    {U U_star S₁ S₂ : Matrix n n R}
    (hU : IsCornerUnitary U U_star S₁) (hOrth : IsOrthogonalPair S₁ S₂) :
    commutator (S₂ * A * S₂) U = 0 := by
  dsimp [commutator]
  calc
    (S₂ * A * S₂) * U - U * (S₂ * A * S₂)
      = S₂ * A * (S₂ * (S₁ * U)) - (U * S₁) * S₂ * A * S₂ := by
        rw [hU.stratum_mul, hU.mul_stratum]
        noncomm_ring
    _ = S₂ * A * ((S₂ * S₁) * U) - U * (S₁ * S₂) * A * S₂ := by noncomm_ring
    _ = S₂ * A * (0 * U) - U * 0 * A * S₂ := by
        rw [hOrth.rev_eq_zero, hOrth.mul_eq_zero]
    _ = 0 := by noncomm_ring

/-- Operator-Level Coarse-Graining Identity for the Maurer–Cartan 1-Form:
ω_{E_S(D)}(U_star, U) = ω_D(U_star, U) * S. -/
theorem oddConnesDensity_coarseGrain [Ring R] (D : Matrix n n R)
    {U U_star S : Matrix n n R}
    (hS : IsIdempotent S) (hU : IsCornerUnitary U U_star S) :
    oddConnesDensity (coarseGrain S D) U_star U = oddConnesDensity D U_star U * S := by
  have hOrth := orthogonal_complement_one S hS
  dsimp [coarseGrain, oddConnesDensity]
  rw [commutator_add_left,
      commutator_orthogonal_corner_zero D hU hOrth,
      add_zero]
  exact (oddConnesDensity_mul_stratum_eq_compressed D hU).symm

/-- Coarse-Graining Invariance of the Odd Connes 1-Cocycle:
For ANY Dirac operator D ∈ M_n(R) and corner unitary (U, U_star) on S,
τ₁(E_S(D); U_star, U) = τ₁(D; U_star, U). -/
theorem oddConnesCocycle_coarseGrain_invariant [CommRing R] (D : Matrix n n R)
    {U U_star S : Matrix n n R}
    (hS : IsIdempotent S) (hU : IsCornerUnitary U U_star S) :
    oddConnesCocycle (coarseGrain S D) U_star U = oddConnesCocycle D U_star U := by
  dsimp [oddConnesCocycle]
  rw [oddConnesDensity_coarseGrain D hS hU]
  rw [Matrix.trace_mul_comm (oddConnesDensity D U_star U) S]
  rw [stratum_mul_oddConnesDensity D hU]

/-- Three-Level Flag Coarse-Graining Invariance of the Odd Connes 1-Cocycle:
In a 3-level flag P ≼ G ≼ M, replacing D by E_{P,G,M}(D) leaves the odd Connes 1-cocycle
of any fine-stratum unitary (U, U_star) on P strictly invariant. -/
theorem oddConnesCocycle_coarseGrain3_invariant [CommRing R] (D P G M : Matrix n n R)
    {U U_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M) (hU : IsCornerUnitary U U_star P) :
    oddConnesCocycle (coarseGrain3 P G M D) U_star U = oddConnesCocycle D U_star U := by
  have hOrth1 := orthogonal_fine_middle_shell P G M hFlag
  have hOrth2 := orthogonal_fine_outer_shell P G M hFlag
  have hOrth3 := orthogonal_complement_one M hFlag.idem_M
  have hOrthPM : IsOrthogonalPair P (1 - M) := by
    have hPM := hFlag.sub_PM
    refine ⟨?_, ?_⟩
    · calc P * (1 - M) = P - P * M := by noncomm_ring
      _ = P - P := by rw [hPM.mul_right]
      _ = 0 := sub_self P
    · calc (1 - M) * P = P - M * P := by noncomm_ring
      _ = P - P := by rw [hPM.mul_left]
      _ = 0 := sub_self P
  dsimp [coarseGrain3, oddConnesCocycle, oddConnesDensity]
  rw [commutator_add_left, commutator_add_left, commutator_add_left]
  rw [commutator_orthogonal_corner_zero D hU hOrth1,
      commutator_orthogonal_corner_zero D hU hOrth2,
      commutator_orthogonal_corner_zero D hU hOrthPM]
  rw [add_zero, add_zero, add_zero]
  change Matrix.trace (oddConnesDensity (P * D * P) U_star U) =
         Matrix.trace (oddConnesDensity D U_star U)
  rw [← oddConnesDensity_mul_stratum_eq_compressed D hU]
  rw [Matrix.trace_mul_comm (oddConnesDensity D U_star U) P]
  rw [stratum_mul_oddConnesDensity D hU]

/-- Cross-Term Trace Vanishing for Orthogonal Corner Unitaries:
If S₁ ⊥ S₂, (U₁, U₁_star) is a corner unitary on S₁, and (U₂, U₂_star) is a corner
unitary on S₂, then tr(U₁_star * [D, U₂]) = 0 for EVERY Dirac operator D ∈ M_n(R). -/
theorem trace_oddConnesDensity_cross_zero [CommRing R] (D : Matrix n n R)
    {U₁ U₁_star S₁ U₂ U₂_star S₂ : Matrix n n R}
    (hU₁ : IsCornerUnitary U₁ U₁_star S₁)
    (hU₂ : IsCornerUnitary U₂ U₂_star S₂)
    (hOrth : IsOrthogonalPair S₁ S₂) :
    Matrix.trace (oddConnesDensity D U₁_star U₂) = 0 := by
  have h12 : U₁_star * U₂ = 0 :=
    corner_mul_zero_of_orthogonal hU₁.star_mul_stratum hU₂.stratum_mul hOrth
  have h_expand : oddConnesDensity D U₁_star U₂ = (S₁ * (U₁_star * D * U₂)) * S₂ := by
    dsimp [oddConnesDensity, commutator]
    calc
      U₁_star * (D * U₂ - U₂ * D)
        = U₁_star * D * U₂ - (U₁_star * U₂) * D := by noncomm_ring
      _ = (S₁ * U₁_star) * D * (U₂ * S₂) - 0 * D := by
          rw [h12, hU₁.stratum_mul_star, hU₂.mul_stratum]
      _ = (S₁ * (U₁_star * D * U₂)) * S₂ := by noncomm_ring
  rw [h_expand, Matrix.trace_mul_comm (S₁ * (U₁_star * D * U₂)) S₂]
  have h_assoc : S₂ * (S₁ * (U₁_star * D * U₂)) = (S₂ * S₁) * (U₁_star * D * U₂) := by
    noncomm_ring
  rw [h_assoc, hOrth.rev_eq_zero, zero_mul, Matrix.trace_zero]

/-- Two-Stratum Block Additivity of the Odd Connes 1-Cocycle:
For any two orthogonal strata S₁ ⊥ S₂ and corner unitaries U₁ on S₁ and U₂ on S₂,
τ₁(D; U₁_star + U₂_star, U₁ + U₂) = τ₁(D; U₁_star, U₁) + τ₁(D; U₂_star, U₂). -/
theorem oddConnesCocycle_orthogonal_add [CommRing R] (D : Matrix n n R)
    {U₁ U₁_star S₁ U₂ U₂_star S₂ : Matrix n n R}
    (hU₁ : IsCornerUnitary U₁ U₁_star S₁)
    (hU₂ : IsCornerUnitary U₂ U₂_star S₂)
    (hOrth : IsOrthogonalPair S₁ S₂) :
    oddConnesCocycle D (U₁_star + U₂_star) (U₁ + U₂) =
    oddConnesCocycle D U₁_star U₁ + oddConnesCocycle D U₂_star U₂ := by
  have h_decomp :
      oddConnesDensity D (U₁_star + U₂_star) (U₁ + U₂) =
      oddConnesDensity D U₁_star U₁ + oddConnesDensity D U₂_star U₂ +
      oddConnesDensity D U₁_star U₂ + oddConnesDensity D U₂_star U₁ := by
    dsimp [oddConnesDensity]
    rw [commutator_add_right]
    noncomm_ring
  dsimp [oddConnesCocycle]
  rw [h_decomp, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
  rw [trace_oddConnesDensity_cross_zero D hU₁ hU₂ hOrth,
      trace_oddConnesDensity_cross_zero D hU₂ hU₁ hOrth.symm,
      add_zero, add_zero]

/-- Unitalization Invariance of the Odd Connes 1-Cocycle:
For ANY Dirac operator D ∈ M_n(R) and corner unitary (U, U_star) on S, extending U
to the global unital unitary U + (1 - S) preserves the odd Connes 1-cocycle identically:
τ₁(D; U_star + (1 - S), U + (1 - S)) = τ₁(D; U_star, U). -/
theorem oddConnesCocycle_unitalize_invariant [CommRing R] (D : Matrix n n R)
    {U U_star S : Matrix n n R}
    (hS : IsIdempotent S) (hU : IsCornerUnitary U U_star S) :
    oddConnesCocycle D (unitalizeCorner U_star S) (unitalizeCorner U S) =
    oddConnesCocycle D U_star U := by
  have hIdemComp := idempotent_complement_one S hS
  have hComp := cornerUnitary_id (1 - S) hIdemComp
  have hOrth := orthogonal_complement_one S hS
  dsimp [unitalizeCorner]
  rw [oddConnesCocycle_orthogonal_add D hU hComp hOrth]
  rw [oddConnesCocycle_idempotent_zero D (1 - S) hIdemComp, add_zero]

/-- Master Three-Stratum Block Additivity of the Odd Connes 1-Cocycle across P ≼ G ≼ M:
For ANY Dirac operator D ∈ M_n(R) and corner unitaries U₁ on P, U₂ on G - P, and
U₃ on M - G, the odd Connes 1-cocycle of the fused flag unitary U₁ + U₂ + U₃ decomposes
into the sum of the three stratum 1-cocycles. -/
theorem oddConnesCocycle_three_stratum_additive [CommRing R] (D P G M : Matrix n n R)
    {U₁ U₁_star U₂ U₂_star U₃ U₃_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hU₁ : IsCornerUnitary U₁ U₁_star P)
    (hU₂ : IsCornerUnitary U₂ U₂_star (G - P))
    (hU₃ : IsCornerUnitary U₃ U₃_star (M - G)) :
    oddConnesCocycle D (U₁_star + U₂_star + U₃_star) (U₁ + U₂ + U₃) =
    oddConnesCocycle D U₁_star U₁ +
    oddConnesCocycle D U₂_star U₂ +
    oddConnesCocycle D U₃_star U₃ := by
  have hOrth12 := orthogonal_fine_middle_shell P G M hFlag
  have hOrth13 := orthogonal_fine_outer_shell P G M hFlag
  have hOrth23 := orthogonal_middle_outer_shell P G M hFlag
  have hU12 := cornerUnitary_orthogonal_add hU₁ hU₂ hOrth12
  have hOrth12_3 : IsOrthogonalPair (P + (G - P)) (M - G) := by
    refine ⟨?_, ?_⟩
    · calc (P + (G - P)) * (M - G) = P * (M - G) + (G - P) * (M - G) := by noncomm_ring
      _ = 0 + 0 := by rw [hOrth13.mul_eq_zero, hOrth23.mul_eq_zero]
      _ = 0 := add_zero 0
    · calc (M - G) * (P + (G - P)) = (M - G) * P + (M - G) * (G - P) := by noncomm_ring
      _ = 0 + 0 := by rw [hOrth13.rev_eq_zero, hOrth23.rev_eq_zero]
      _ = 0 := add_zero 0
  rw [oddConnesCocycle_orthogonal_add D hU12 hU₃ hOrth12_3]
  rw [oddConnesCocycle_orthogonal_add D hU₁ hU₂ hOrth12]

/-!
### Archetype α₇: Partial-Isometry Intertwining Invariance of the Odd Connes 1-Cocycle
Causal Dependency: α₂, α₅, α₆ ≺ α₇
-/

/-- A Murray–von Neumann sibling partial isometry pair (V, V_star) intertwining P and G - P. -/
structure IsSiblingPartialIsometry [Ring R] (V V_star P G : Matrix n n R) : Prop where
  source_eq       : V_star * V = P
  target_eq       : V * V_star = G - P
  mul_source      : V * P = V
  source_mul_star : P * V_star = V_star

/-- Left target absorption of V by G - P: (G - P) * V = V. -/
lemma target_mul_partial_isometry [Ring R] {V V_star P G : Matrix n n R}
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    (G - P) * V = V := by
  calc
    (G - P) * V = (V * V_star) * V := by rw [← hPI.target_eq]
    _ = V * (V_star * V) := by noncomm_ring
    _ = V * P := by rw [hPI.source_eq]
    _ = V := hPI.mul_source

/-- Right target absorption of V_star by G - P: V_star * (G - P) = V_star. -/
lemma partial_isometry_star_mul_target [Ring R] {V V_star P G : Matrix n n R}
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    V_star * (G - P) = V_star := by
  calc
    V_star * (G - P) = V_star * (V * V_star) := by rw [← hPI.target_eq]
    _ = (V_star * V) * V_star := by noncomm_ring
    _ = P * V_star := by rw [hPI.source_eq]
    _ = V_star := hPI.source_mul_star

/-- Partial-Isometry Transport of Corner Unitaries across Sibling Strata:
If (U, U_star) is a corner unitary on P and (V, V_star) is a sibling partial isometry
from P to G - P, then (V * U * V_star, V * U_star * V_star) is a corner unitary on G - P. -/
theorem cornerUnitary_partial_isometry_transport [Ring R]
    {U U_star V V_star P G : Matrix n n R}
    (hU : IsCornerUnitary U U_star P)
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    IsCornerUnitary (V * U * V_star) (V * U_star * V_star) (G - P) := by
  have h_tgt_V := target_mul_partial_isometry hPI
  have h_Vstar_tgt := partial_isometry_star_mul_target hPI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (V * U_star * V_star) * (V * U * V_star)
        = V * U_star * (V_star * V) * U * V_star := by noncomm_ring
      _ = V * (U_star * (V_star * V)) * U * V_star := by noncomm_ring
      _ = V * (U_star * P) * U * V_star := by rw [hPI.source_eq]
      _ = V * U_star * U * V_star := by rw [hU.star_mul_stratum]
      _ = V * (U_star * U) * V_star := by noncomm_ring
      _ = V * P * V_star := by rw [hU.star_mul_self]
      _ = (V * P) * V_star := by rw [mul_assoc]
      _ = V * V_star := by rw [hPI.mul_source]
      _ = G - P := hPI.target_eq
  · calc
      (V * U * V_star) * (V * U_star * V_star)
        = V * U * (V_star * V) * U_star * V_star := by noncomm_ring
      _ = V * (U * (V_star * V)) * U_star * V_star := by noncomm_ring
      _ = V * (U * P) * U_star * V_star := by rw [hPI.source_eq]
      _ = V * U * U_star * V_star := by rw [hU.mul_stratum]
      _ = V * (U * U_star) * V_star := by noncomm_ring
      _ = V * P * V_star := by rw [hU.mul_star_self]
      _ = (V * P) * V_star := by rw [mul_assoc]
      _ = V * V_star := by rw [hPI.mul_source]
      _ = G - P := hPI.target_eq
  · calc
      (V * U * V_star) * (G - P) = V * U * (V_star * (G - P)) := by noncomm_ring
      _ = V * U * V_star := by rw [h_Vstar_tgt]
  · calc
      (G - P) * (V * U * V_star) = ((G - P) * V) * U * V_star := by noncomm_ring
      _ = V * U * V_star := by rw [h_tgt_V]
  · calc
      (V * U_star * V_star) * (G - P) = V * U_star * (V_star * (G - P)) := by noncomm_ring
      _ = V * U_star * V_star := by rw [h_Vstar_tgt]
  · calc
      (G - P) * (V * U_star * V_star) = ((G - P) * V) * U_star * V_star := by noncomm_ring
      _ = V * U_star * V_star := by rw [h_tgt_V]

/-- Direct Partial-Isometry Transport Invariance of the Odd Connes 1-Cocycle:
Transporting the odd Connes density ω_D(U_star, U) from P to G - P via V * ω_D(U_star, U) * V_star
preserves the odd Connes 1-cocycle τ₁(D; U_star, U) identically. -/
theorem trace_oddConnesDensity_partial_isometry_transport [CommRing R]
    (D : Matrix n n R) {U U_star V V_star P G : Matrix n n R}
    (hU : IsCornerUnitary U U_star P)
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    Matrix.trace (V * oddConnesDensity D U_star U * V_star) =
    oddConnesCocycle D U_star U := by
  dsimp [oddConnesCocycle]
  rw [Matrix.trace_mul_comm (V * oddConnesDensity D U_star U) V_star]
  have h_assoc :
      V_star * (V * oddConnesDensity D U_star U) =
      (V_star * V) * oddConnesDensity D U_star U := by noncomm_ring
  rw [h_assoc, hPI.source_eq, stratum_mul_oddConnesDensity D hU]

/-- Global Involution Covariant Invariance of the Odd Connes 1-Cocycle:
For any global involution W² = 1, conjugating D, U_star, and U by W preserves the
odd Connes 1-cocycle τ₁(W * D * W; W * U_star * W, W * U * W) = τ₁(D; U_star, U). -/
theorem oddConnesCocycle_involution_conj [CommRing R] (W D U_star U : Matrix n n R)
    (hW : W * W = 1) :
    oddConnesCocycle (W * D * W) (W * U_star * W) (W * U * W) =
    oddConnesCocycle D U_star U := by
  have h_dens :
      oddConnesDensity (W * D * W) (W * U_star * W) (W * U * W) =
      W * oddConnesDensity D U_star U * W := by
    dsimp [oddConnesDensity, commutator]
    calc
      (W * U_star * W) * ((W * D * W) * (W * U * W) - (W * U * W) * (W * D * W))
        = W * U_star * (W * W) * D * (W * W) * U * W -
          W * U_star * (W * W) * U * (W * W) * D * W := by noncomm_ring
      _ = W * U_star * 1 * D * 1 * U * W -
          W * U_star * 1 * U * 1 * D * W := by rw [hW]
      _ = W * (U_star * (D * U - U * D)) * W := by noncomm_ring
  dsimp [oddConnesCocycle]
  rw [h_dens, Matrix.trace_mul_comm (W * oddConnesDensity D U_star U) W]
  have h_assoc :
      W * (W * oddConnesDensity D U_star U) =
      (W * W) * oddConnesDensity D U_star U := by noncomm_ring
  rw [h_assoc, hW, one_mul]

/-- Genus-Confined Partial-Isometry Intertwining Invariance of the Odd Connes 1-Cocycle:
For any corner unitary (U, U_star) on P and sibling partial isometry (V, V_star) between P
and G - P, transporting D ↦ V * D * V_star and U ↦ V * U * V_star preserves the odd
Connes 1-cocycle unconditionally:
τ₁(V * D * V_star; V * U_star * V_star, V * U * V_star) = τ₁(D; U_star, U). -/
theorem oddConnesCocycle_partial_isometry_intertwining [CommRing R]
    (D : Matrix n n R) {U U_star V V_star P G : Matrix n n R}
    (hU : IsCornerUnitary U U_star P)
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    oddConnesCocycle (V * D * V_star) (V * U_star * V_star) (V * U * V_star) =
    oddConnesCocycle D U_star U := by
  have hP_idem : P * P = P := by
    calc P * P = P * (U * U_star) := by rw [hU.mul_star_self]
    _ = (P * U) * U_star := by rw [mul_assoc]
    _ = U * U_star := by rw [hU.stratum_mul]
    _ = P := hU.mul_star_self
  have h_term1 : V * U_star * (V_star * V) * D * (V_star * V) * U * V_star =
      V * (U_star * (P * D * P) * U) * V_star := by
    rw [hPI.source_eq]
    noncomm_ring
  have h_term2 : V * U_star * (V_star * V) * U * (V_star * V) * D * V_star =
      V * (U_star * U * (P * D * P)) * V_star := by
    have h_prod : U_star * U * (P * D * P) = P * D * P := by
      calc U_star * U * (P * D * P) = P * (P * D * P) := by rw [hU.star_mul_self]
      _ = (P * P) * D * P := by noncomm_ring
      _ = P * D * P := by rw [hP_idem]
    have hP_D_V : V * (P * D * P) * V_star = V * P * D * V_star := by
      calc V * (P * D * P) * V_star = V * ((P * D) * (P * V_star)) := by noncomm_ring
      _ = V * ((P * D) * V_star) := by rw [hPI.source_mul_star]
      _ = V * P * D * V_star := by noncomm_ring
    calc V * U_star * (V_star * V) * U * (V_star * V) * D * V_star
      = V * (U_star * P) * U * P * D * V_star := by rw [hPI.source_eq]; noncomm_ring
      _ = V * U_star * U * P * D * V_star := by rw [hU.star_mul_stratum]
      _ = V * (U_star * U) * P * D * V_star := by noncomm_ring
      _ = V * P * P * D * V_star := by rw [hU.star_mul_self]
      _ = V * (P * P) * D * V_star := by noncomm_ring
      _ = V * P * D * V_star := by rw [hP_idem]
      _ = V * (P * D * P) * V_star := by rw [hP_D_V]
      _ = V * (U_star * U * (P * D * P)) * V_star := by rw [h_prod]
  have h_dens :
      oddConnesDensity (V * D * V_star) (V * U_star * V_star) (V * U * V_star) =
      V * (oddConnesDensity (P * D * P) U_star U) * V_star := by
    dsimp [oddConnesDensity, commutator]
    calc
      (V * U_star * V_star) *
        ((V * D * V_star) * (V * U * V_star) - (V * U * V_star) * (V * D * V_star))
        = V * U_star * (V_star * V) * D * (V_star * V) * U * V_star -
          V * U_star * (V_star * V) * U * (V_star * V) * D * V_star := by noncomm_ring
      _ = V * (U_star * (P * D * P) * U) * V_star -
          V * (U_star * U * (P * D * P)) * V_star := by rw [h_term1, h_term2]
      _ = V * (U_star * ((P * D * P) * U - U * (P * D * P))) * V_star := by noncomm_ring
  dsimp [oddConnesCocycle]
  rw [h_dens]
  have h_trans := trace_oddConnesDensity_partial_isometry_transport (P * D * P) hU hPI
  dsimp [oddConnesCocycle] at h_trans
  rw [h_trans]
  rw [← oddConnesDensity_mul_stratum_eq_compressed D hU]
  rw [Matrix.trace_mul_comm (oddConnesDensity D U_star U) P]
  rw [stratum_mul_oddConnesDensity D hU]

end NonCommutativeOddConnesFlag
