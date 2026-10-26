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

namespace NonCommutativeCayleyBott

open Matrix

variable {R : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-!
### Archetype α₀: The Primordial Matrix Substrate & Inner Derivation
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

/-- Right subtraction linearity of the evolutionary derivation:
[D, X - Y] = [D, X] - [D, Y]. -/
lemma commutator_sub_right [Ring R] (D X Y : Matrix n n R) :
    commutator D (X - Y) = commutator D X - commutator D Y := by
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
### Archetype α₁: Three-Level Projection Flag & Sibling Partial Isometries
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

/-- A Murray–von Neumann sibling partial isometry pair (V, V_star) intertwining P and G - P. -/
structure IsSiblingPartialIsometry [Ring R] (V V_star P G : Matrix n n R) : Prop where
  source_eq       : V_star * V = P
  target_eq       : V * V_star = G - P
  mul_source      : V * P = V
  source_mul_star : P * V_star = V_star

/-- Left target absorption of V by G - P: (G - P) * V = V. -/
theorem target_mul_partial_isometry [Ring R] {V V_star P G : Matrix n n R}
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    (G - P) * V = V := by
  calc
    (G - P) * V = (V * V_star) * V := by rw [← hPI.target_eq]
    _ = V * (V_star * V) := by noncomm_ring
    _ = V * P := by rw [hPI.source_eq]
    _ = V := hPI.mul_source

/-- Right target absorption of V_star by G - P: V_star * (G - P) = V_star. -/
theorem partial_isometry_star_mul_target [Ring R] {V V_star P G : Matrix n n R}
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    V_star * (G - P) = V_star := by
  calc
    V_star * (G - P) = V_star * (V * V_star) := by rw [← hPI.target_eq]
    _ = (V_star * V) * V_star := by noncomm_ring
    _ = P * V_star := by rw [hPI.source_eq]
    _ = V_star := hPI.source_mul_star

/-- Left annihilation of V by P in a 3-level flag: P * V = 0. -/
theorem source_mul_partial_isometry_zero [Ring R] (P G M : Matrix n n R)
    {V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    P * V = 0 := by
  have hOrth := orthogonal_fine_middle_shell P G M hFlag
  calc
    P * V = P * ((G - P) * V) := by rw [target_mul_partial_isometry hPI]
    _ = (P * (G - P)) * V := by noncomm_ring
    _ = 0 * V := by rw [hOrth.mul_eq_zero]
    _ = 0 := zero_mul V

/-- Right annihilation of V_star by P in a 3-level flag: V_star * P = 0. -/
theorem partial_isometry_star_mul_source_zero [Ring R] (P G M : Matrix n n R)
    {V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    V_star * P = 0 := by
  have hOrth := orthogonal_fine_middle_shell P G M hFlag
  calc
    V_star * P = (V_star * (G - P)) * P := by rw [partial_isometry_star_mul_target hPI]
    _ = V_star * ((G - P) * P) := by noncomm_ring
    _ = V_star * 0 := by rw [hOrth.rev_eq_zero]
    _ = 0 := mul_zero V_star

/-- Left Genus Confinement of V: G * V = V. -/
theorem genus_mul_partial_isometry [Ring R] (P G M : Matrix n n R)
    {V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    G * V = V := by
  calc
    G * V = G * ((G - P) * V) := by rw [target_mul_partial_isometry hPI]
    _ = (G * G - G * P) * V := by noncomm_ring
    _ = (G - P) * V := by rw [hFlag.idem_G.idem, hFlag.sub_PG.mul_left]
    _ = V := target_mul_partial_isometry hPI

/-- Right Genus Confinement of V_star: V_star * G = V_star. -/
theorem partial_isometry_star_mul_genus [Ring R] (P G M : Matrix n n R)
    {V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G) :
    V_star * G = V_star := by
  calc
    V_star * G = (V_star * (G - P)) * G := by rw [partial_isometry_star_mul_target hPI]
    _ = V_star * (G * G - P * G) := by noncomm_ring
    _ = V_star * (G - P) := by rw [hFlag.idem_G.idem, hFlag.sub_PG.mul_right]
    _ = V_star := partial_isometry_star_mul_target hPI

/-!
### Archetype α₂: Corner Unitaries in K₁(P * A * P) & The Cayley–Connes Reflection
Causal Dependency: α₀ ≺ α₁ ≺ α₂
-/

/-- A corner unitary pair (U, U_star) inside the Peirce corner algebra S * M_n(R) * S. -/
structure IsCornerUnitary [Ring R] (U U_star S : Matrix n n R) : Prop where
  star_mul_self    : U_star * U = S
  mul_star_self    : U * U_star = S
  mul_stratum      : U * S = U
  stratum_mul      : S * U = U
  star_mul_stratum : U_star * S = U_star
  stratum_mul_star : S * U_star = U_star

/-- Left Genus Absorption of a Fine-Stratum Corner Unitary: G * U = U. -/
lemma genus_mul_cornerUnitary [Ring R] {U U_star P G : Matrix n n R}
    (hPG : Subprojection P G) (hU : IsCornerUnitary U U_star P) :
    G * U = U := by
  calc
    G * U = G * (P * U) := by rw [hU.stratum_mul]
    _ = (G * P) * U := by rw [mul_assoc]
    _ = P * U := by rw [hPG.mul_left]
    _ = U := hU.stratum_mul

/-- Right Genus Absorption of a Fine-Stratum Corner Unitary Adjoint: U_star * G = U_star. -/
lemma cornerUnitary_star_mul_genus [Ring R] {U U_star P G : Matrix n n R}
    (hPG : Subprojection P G) (hU : IsCornerUnitary U U_star P) :
    U_star * G = U_star := by
  calc
    U_star * G = (U_star * P) * G := by rw [hU.star_mul_stratum]
    _ = U_star * (P * G) := by rw [mul_assoc]
    _ = U_star * P := by rw [hPG.mul_right]
    _ = U_star := hU.star_mul_stratum

/-- The Cayley–Connes reflection operator U_CC(P, G) = P - (G - P) mapping a
subprojection P ≼ G in K₀ to a self-adjoint involutive corner unitary in K₁(G * A * G). -/
def cayleyConnesReflection [Ring R] (P G : Matrix n n R) : Matrix n n R :=
  P - (G - P)

/-- The Cayley–Connes reflection U_CC(P, G) = P - (G - P) is a self-adjoint involutive
corner unitary on the coarse genus stratum G. -/
theorem isCornerUnitary_cayleyConnesReflection [Ring R] (P G M : Matrix n n R)
    (hFlag : IsThreeLevelFlag P G M) :
    IsCornerUnitary (cayleyConnesReflection P G) (cayleyConnesReflection P G) G := by
  have hOrth := orthogonal_fine_middle_shell P G M hFlag
  have hGP : IsIdempotent (G - P) :=
    idempotent_relative_complement P G hFlag.idem_P hFlag.idem_G hFlag.sub_PG
  have h_sq : cayleyConnesReflection P G * cayleyConnesReflection P G = G := by
    dsimp [cayleyConnesReflection]
    calc
      (P - (G - P)) * (P - (G - P))
        = P * P - P * (G - P) - (G - P) * P + (G - P) * (G - P) := by noncomm_ring
      _ = P - 0 - 0 + (G - P) := by
          rw [hFlag.idem_P.idem, hOrth.mul_eq_zero, hOrth.rev_eq_zero, hGP.idem]
      _ = G := by noncomm_ring
  have h_right : cayleyConnesReflection P G * G = cayleyConnesReflection P G := by
    dsimp [cayleyConnesReflection]
    calc
      (P - (G - P)) * G = P * G - (G * G - P * G) := by noncomm_ring
      _ = P - (G - P) := by rw [hFlag.sub_PG.mul_right, hFlag.idem_G.idem]
  have h_left : G * cayleyConnesReflection P G = cayleyConnesReflection P G := by
    dsimp [cayleyConnesReflection]
    calc
      G * (P - (G - P)) = G * P - (G * G - G * P) := by noncomm_ring
      _ = P - (G - P) := by rw [hFlag.sub_PG.mul_left, hFlag.idem_G.idem]
  exact ⟨h_sq, h_sq, h_right, h_left, h_right, h_left⟩

/-!
### Archetype α₃: The Non-Commutative Cayley–Bott Boundary Map (K₁ → K₀)
Causal Dependency: α₁, α₂ ≺ α₃
-/

/-- The Upper Cayley–Bott Boundary Map β_CB(U, V) = P + U * V_star, embedding a corner
unitary U ∈ K₁(P * A * P) into the idempotent projection grassmannian K₀(G * A * G). -/
def cayleyBottBoundary [Ring R] (P U V_star : Matrix n n R) : Matrix n n R :=
  P + U * V_star

/-- The Lower (Dual) Cayley–Bott Boundary Map β_CB*(U, V) = P + V * U_star. -/
def cayleyBottBoundaryDual [Ring R] (P V U_star : Matrix n n R) : Matrix n n R :=
  P + V * U_star

/-- Annihilation of a fine corner unitary U by V_star: V_star * U = 0. -/
lemma partial_isometry_star_mul_cornerUnitary_zero [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    V_star * U = 0 := by
  calc
    V_star * U = V_star * (P * U) := by rw [hU.stratum_mul]
    _ = (V_star * P) * U := by rw [mul_assoc]
    _ = 0 * U := by rw [partial_isometry_star_mul_source_zero P G M hFlag hPI]
    _ = 0 := zero_mul U

/-- Strict Index-2 Nilpotence of the Off-Diagonal Cayley–Bott Transition U * V_star:
(U * V_star)² = 0. -/
theorem cayleyBott_transition_sq_zero [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    (U * V_star) * (U * V_star) = 0 := by
  calc
    (U * V_star) * (U * V_star)
      = U * (V_star * U) * V_star := by noncomm_ring
    _ = U * 0 * V_star := by
        rw [partial_isometry_star_mul_cornerUnitary_zero P G M hFlag hPI hU]
    _ = 0 := by noncomm_ring

/-- Idempotence of the Cayley–Bott Boundary Map (K₁ → K₀):
For any corner unitary (U, U_star) on P and sibling partial isometry (V, V_star),
β_CB(U, V) = P + U * V_star is strictly idempotent: β_CB(U, V)² = β_CB(U, V). -/
theorem isIdempotent_cayleyBottBoundary [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    IsIdempotent (cayleyBottBoundary P U V_star) := by
  refine ⟨?_⟩
  dsimp [cayleyBottBoundary]
  calc
    (P + U * V_star) * (P + U * V_star)
      = P * P + (P * U) * V_star + U * (V_star * P) +
        (U * V_star) * (U * V_star) := by noncomm_ring
    _ = P + U * V_star + U * 0 + 0 := by
        rw [hFlag.idem_P.idem, hU.stratum_mul,
            partial_isometry_star_mul_source_zero P G M hFlag hPI,
            cayleyBott_transition_sq_zero P G M hFlag hPI hU]
    _ = P + U * V_star := by noncomm_ring

/-- Idempotence of the Dual Cayley–Bott Boundary Map:
β_CB*(U, V) = P + V * U_star is strictly idempotent. -/
theorem isIdempotent_cayleyBottBoundaryDual [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    IsIdempotent (cayleyBottBoundaryDual P V U_star) := by
  have h_zero : U_star * V = 0 := by
    calc
      U_star * V = (U_star * P) * V := by rw [hU.star_mul_stratum]
      _ = U_star * (P * V) := by rw [mul_assoc]
      _ = U_star * 0 := by rw [source_mul_partial_isometry_zero P G M hFlag hPI]
      _ = 0 := mul_zero U_star
  refine ⟨?_⟩
  dsimp [cayleyBottBoundaryDual]
  calc
    (P + V * U_star) * (P + V * U_star)
      = P * P + (P * V) * U_star + V * (U_star * P) +
        V * (U_star * V) * U_star := by noncomm_ring
    _ = P + 0 * U_star + V * U_star + V * 0 * U_star := by
        rw [hFlag.idem_P.idem,
            source_mul_partial_isometry_zero P G M hFlag hPI,
            hU.star_mul_stratum, h_zero]
    _ = P + V * U_star := by noncomm_ring

/-- Taxonomic Genus Inclusion of the Cayley–Bott Boundary Projection:
β_CB(U, V) ≼ G. -/
theorem subprojection_cayleyBottBoundary_genus [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    Subprojection (cayleyBottBoundary P U V_star) G := by
  refine ⟨?_, ?_⟩
  · dsimp [cayleyBottBoundary]
    calc
      (P + U * V_star) * G = P * G + U * (V_star * G) := by noncomm_ring
      _ = P + U * V_star := by
          rw [hFlag.sub_PG.mul_right, partial_isometry_star_mul_genus P G M hFlag hPI]
  · dsimp [cayleyBottBoundary]
    calc
      G * (P + U * V_star) = G * P + (G * U) * V_star := by noncomm_ring
      _ = P + U * V_star := by
          rw [hFlag.sub_PG.mul_left, genus_mul_cornerUnitary hFlag.sub_PG hU]

/-- Taxonomic Macro-Stratum Inclusion of the Cayley–Bott Boundary Projection:
β_CB(U, V) ≼ M. -/
theorem subprojection_cayleyBottBoundary_macro [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    Subprojection (cayleyBottBoundary P U V_star) M :=
  subprojection_trans (cayleyBottBoundary P U V_star) G M
    (subprojection_cayleyBottBoundary_genus P G M hFlag hPI hU) hFlag.sub_GM

/-- The positive unipotent Cayley–Bott shear operator T_+(U, V) = 1 - U * V_star. -/
def cayleyBottShearPos [Ring R] (U V_star : Matrix n n R) : Matrix n n R :=
  1 - U * V_star

/-- The negative unipotent Cayley–Bott shear operator T_-(U, V) = 1 + U * V_star. -/
def cayleyBottShearNeg [Ring R] (U V_star : Matrix n n R) : Matrix n n R :=
  1 + U * V_star

/-- Right invertibility of the Cayley–Bott unipotent shear pair:
T_+(U, V) * T_-(U, V) = 1. -/
theorem cayleyBottShear_mul_inv [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    cayleyBottShearPos U V_star * cayleyBottShearNeg U V_star = 1 := by
  dsimp [cayleyBottShearPos, cayleyBottShearNeg]
  calc
    (1 - U * V_star) * (1 + U * V_star)
      = 1 - (U * V_star) * (U * V_star) := by noncomm_ring
    _ = 1 - 0 := by rw [cayleyBott_transition_sq_zero P G M hFlag hPI hU]
    _ = 1 := sub_zero 1

/-- Left invertibility of the Cayley–Bott unipotent shear pair:
T_-(U, V) * T_+(U, V) = 1. -/
theorem cayleyBottShear_inv_mul [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    cayleyBottShearNeg U V_star * cayleyBottShearPos U V_star = 1 := by
  dsimp [cayleyBottShearPos, cayleyBottShearNeg]
  calc
    (1 + U * V_star) * (1 - U * V_star)
      = 1 - (U * V_star) * (U * V_star) := by noncomm_ring
    _ = 1 - 0 := by rw [cayleyBott_transition_sq_zero P G M hFlag hPI hU]
    _ = 1 := sub_zero 1

/-- Unipotent Shear Factorization of the Cayley–Bott Boundary Projection:
β_CB(U, V) = T_+(U, V) * P * T_-(U, V). -/
theorem cayleyBottBoundary_eq_shear_conj [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    cayleyBottShearPos U V_star * P * cayleyBottShearNeg U V_star =
    cayleyBottBoundary P U V_star := by
  dsimp [cayleyBottShearPos, cayleyBottShearNeg, cayleyBottBoundary]
  calc
    (1 - U * V_star) * P * (1 + U * V_star)
      = P + (P * U) * V_star - U * (V_star * P) -
        U * (V_star * P) * U * V_star := by noncomm_ring
    _ = P + U * V_star - U * 0 - U * 0 * U * V_star := by
        rw [hU.stratum_mul, partial_isometry_star_mul_source_zero P G M hFlag hPI]
    _ = P + U * V_star := by noncomm_ring

/-- Reverse Shear Recovery of the Base Stratum P from β_CB(U, V):
T_-(U, V) * β_CB(U, V) * T_+(U, V) = P. -/
theorem shear_conj_cayleyBottBoundary_eq_source [Ring R] (P G M : Matrix n n R)
    {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    cayleyBottShearNeg U V_star * cayleyBottBoundary P U V_star *
      cayleyBottShearPos U V_star = P := by
  rw [← cayleyBottBoundary_eq_shear_conj P G M hFlag hPI hU]
  calc
    cayleyBottShearNeg U V_star *
      (cayleyBottShearPos U V_star * P * cayleyBottShearNeg U V_star) *
      cayleyBottShearPos U V_star
      = (cayleyBottShearNeg U V_star * cayleyBottShearPos U V_star) * P *
        (cayleyBottShearNeg U V_star * cayleyBottShearPos U V_star) := by noncomm_ring
    _ = 1 * P * 1 := by rw [cayleyBottShear_inv_mul P G M hFlag hPI hU]
    _ = P := by noncomm_ring

/-!
### Archetype α₄: Peirce Splitting of the Odd Maurer–Cartan 1-Form ω_D(U*, U)
Causal Dependency: α₀, α₁, α₂ ≺ α₄
-/

/-- The odd Connes operator density (Maurer–Cartan 1-form) ω_D(U_star, U) = U_star * [D, U]. -/
def oddConnesDensity [Ring R] (D U_star U : Matrix n n R) : Matrix n n R :=
  U_star * commutator D U

/-- The odd Connes 1-cocycle pairing τ₁(D; U_star, U) = tr(U_star * [D, U]). -/
def oddConnesCocycle [CommRing R] (D U_star U : Matrix n n R) : R :=
  Matrix.trace (oddConnesDensity D U_star U)

/-- The even Chern–Connes 2-cocycle operator density C(D, S) = S * [D, S] * [D, S]. -/
def connesDensity [Ring R] (D S : Matrix n n R) : Matrix n n R :=
  S * (commutator D S * commutator D S)

/-- The even Connes 2-cocycle pairing τ₂(D; S) = tr(S * [D, S]²). -/
def connesCocycle [CommRing R] (D S : Matrix n n R) : R :=
  Matrix.trace (connesDensity D S)

/-- Left Stratum Absorption of the Odd Connes Operator Density:
S * ω_D(U_star, U) = ω_D(U_star, U). -/
lemma stratum_mul_oddConnesDensity [Ring R] (D : Matrix n n R)
    {U U_star S : Matrix n n R} (hU : IsCornerUnitary U U_star S) :
    S * oddConnesDensity D U_star U = oddConnesDensity D U_star U := by
  dsimp [oddConnesDensity]
  rw [← mul_assoc, hU.stratum_mul_star]

/-- Peirce Decomposition of the Odd Connes Maurer–Cartan 1-Form:
ω_D(U_star, U) = ω_D(U_star, U) * P + ω_D(U_star, U) * (1 - P). -/
theorem oddConnesDensity_peirce_decomp [Ring R] (D U_star U P : Matrix n n R) :
    oddConnesDensity D U_star U =
    oddConnesDensity D U_star U * P + oddConnesDensity D U_star U * (1 - P) := by
  noncomm_ring

/-- Internal (P, P) Gauge Current Identity:
The diagonal Peirce block ω_D(U_star, U) * P equals the spectral corner shift
U_star * D * U - P * D * P. -/
theorem oddConnesDensity_internal_eq_gauge_shift [Ring R] (D : Matrix n n R)
    {U U_star P : Matrix n n R} (hU : IsCornerUnitary U U_star P) :
    oddConnesDensity D U_star U * P = U_star * D * U - P * D * P := by
  dsimp [oddConnesDensity, commutator]
  calc
    (U_star * (D * U - U * D)) * P
      = U_star * D * (U * P) - (U_star * U) * D * P := by noncomm_ring
    _ = U_star * D * U - P * D * P := by rw [hU.mul_stratum, hU.star_mul_self]

/-- The Odd Connes 1-Cocycle is the Spectral Trace of the Internal Gauge Current:
tr(ω_D(U_star, U) * P) = τ₁(D; U_star, U). -/
theorem trace_oddConnesDensity_internal [CommRing R] (D : Matrix n n R)
    {U U_star P : Matrix n n R} (hU : IsCornerUnitary U U_star P) :
    Matrix.trace (oddConnesDensity D U_star U * P) = oddConnesCocycle D U_star U := by
  dsimp [oddConnesCocycle]
  rw [Matrix.trace_mul_comm (oddConnesDensity D U_star U) P]
  rw [stratum_mul_oddConnesDensity D hU]

/-- Universal Transverse (P, 1 - P) Connection Theorem:
For ANY corner unitary (U, U_star) on an idempotent stratum P and ANY Dirac operator D,
the transverse Peirce block ω_D(U_star, U) * (1 - P) is independent of U and equals the
first-order idempotent derivation P * [D, P]. -/
theorem oddConnesDensity_transverse_eq_derivation [Ring R] (D : Matrix n n R)
    {U U_star P : Matrix n n R}
    (hP : IsIdempotent P) (hU : IsCornerUnitary U U_star P) :
    oddConnesDensity D U_star U * (1 - P) = P * commutator D P := by
  dsimp [oddConnesDensity, commutator]
  calc
    (U_star * (D * U - U * D)) * (1 - P)
      = U_star * D * U - U_star * D * (U * P) -
        (U_star * U) * D + (U_star * U) * D * P := by noncomm_ring
    _ = U_star * D * U - U_star * D * U - P * D + P * D * P := by
        rw [hU.mul_stratum, hU.star_mul_self]
    _ = P * D * P - (P * P) * D := by
        rw [hP.idem]
        noncomm_ring
    _ = P * (D * P - P * D) := by noncomm_ring

/-- Dual Vertical Transverse (1 - P, P) Connection Theorem:
For ANY corner unitary (U, U_star) on P and ANY Dirac operator D,
(1 - P) * [D, U] * U_star = [D, P] * P. -/
theorem transverse_derivation_mul_star_eq [Ring R] (D : Matrix n n R)
    {U U_star P : Matrix n n R}
    (hP : IsIdempotent P) (hU : IsCornerUnitary U U_star P) :
    (1 - P) * commutator D U * U_star = commutator D P * P := by
  dsimp [commutator]
  calc
    (1 - P) * (D * U - U * D) * U_star
      = D * (U * U_star) - P * D * (U * U_star) -
        U * D * U_star + (P * U) * D * U_star := by noncomm_ring
    _ = D * P - P * D * P - U * D * U_star + U * D * U_star := by
        rw [hU.mul_star_self, hU.stratum_mul]
    _ = D * (P * P) - P * D * P := by
        rw [hP.idem]
        noncomm_ring
    _ = (D * P - P * D) * P := by noncomm_ring

/-!
### Archetype α₅: Compatibility of the Odd and Even Connes Cocycles
Causal Dependency: α₃, α₄ ≺ α₅
-/

/-- Factorization of the Even Chern–Connes Density into Left and Right Idempotent Derivations:
(P * [D, P]) * ([D, P] * P) = C(D, P). -/
theorem mul_idempotent_derivations_eq_connesDensity [Ring R] (D P : Matrix n n R)
    (hP : IsIdempotent P) :
    (P * commutator D P) * (commutator D P * P) = connesDensity D P := by
  dsimp [connesDensity, commutator]
  have hL : (P * (D * P - P * D)) * ((D * P - P * D) * P) =
      P * D * P * D * P - P * D * D * P := by
    have h1 : P * (D * P - P * D) = P * D * P - P * D := by
      calc P * (D * P - P * D) = P * D * P - (P * P) * D := by noncomm_ring
      _ = P * D * P - P * D := by rw [hP.idem]
    have h2 : (D * P - P * D) * P = D * P - P * D * P := by
      calc (D * P - P * D) * P = D * (P * P) - P * D * P := by noncomm_ring
      _ = D * P - P * D * P := by rw [hP.idem]
    calc (P * (D * P - P * D)) * ((D * P - P * D) * P)
      = (P * D * P - P * D) * (D * P - P * D * P) := by rw [h1, h2]
      _ = (P * D * P) * (D * P) - (P * D * P) * (P * D * P) -
          P * D * D * P + P * D * (P * D * P) := by noncomm_ring
      _ = P * D * (P * D * P) - P * D * (P * P) * D * P -
          P * D * D * P + P * D * (P * D * P) := by noncomm_ring
      _ = P * D * (P * D * P) - P * D * P * D * P -
          P * D * D * P + P * D * (P * D * P) := by rw [hP.idem]
      _ = P * D * P * D * P - P * D * D * P := by noncomm_ring
  have hR : P * ((D * P - P * D) * (D * P - P * D)) =
      P * D * P * D * P - P * D * D * P := by
    calc
      P * ((D * P - P * D) * (D * P - P * D))
        = P * D * P * D * P - P * D * (P * P) * D -
          (P * P) * D * D * P + (P * P) * D * P * D := by noncomm_ring
      _ = P * D * P * D * P - P * D * P * D -
          P * D * D * P + P * D * P * D := by rw [hP.idem]
      _ = P * D * P * D * P - P * D * D * P := by noncomm_ring
  rw [hL, hR]

/-- Master Theorem 1 (Universal Odd-to-Even Operator Density Factorization):
For ANY corner unitary (U, U_star) on P and ANY Dirac operator D ∈ M_n(R), multiplying
the transverse Peirce blocks of the odd Connes 1-form ω_D(U_star, U) reconstructs the
exact even Chern–Connes 2-cocycle density C(D, P) = P * [D, P]². -/
theorem odd_to_even_connesDensity_factorization [Ring R] (D : Matrix n n R)
    {U U_star P : Matrix n n R}
    (hP : IsIdempotent P) (hU : IsCornerUnitary U U_star P) :
    (oddConnesDensity D U_star U * (1 - P)) * ((1 - P) * commutator D U * U_star) =
    connesDensity D P := by
  rw [oddConnesDensity_transverse_eq_derivation D hP hU,
      transverse_derivation_mul_star_eq D hP hU,
      mul_idempotent_derivations_eq_connesDensity D P hP]

/-- Master Theorem 2 (Universal Odd-to-Even Connes Cocycle Compatibility):
For ANY corner unitary (U, U_star) on P and ANY Dirac operator D ∈ M_n(R), the trace
pairing of the transverse odd Connes 1-form blocks equals the even Connes 2-cocycle τ₂(D; P). -/
theorem odd_to_even_connesCocycle_compatibility [CommRing R] (D : Matrix n n R)
    {U U_star P : Matrix n n R}
    (hP : IsIdempotent P) (hU : IsCornerUnitary U U_star P) :
    Matrix.trace
      ((oddConnesDensity D U_star U * (1 - P)) * ((1 - P) * commutator D U * U_star)) =
    connesCocycle D P := by
  dsimp [connesCocycle]
  rw [odd_to_even_connesDensity_factorization D hP hU]

/-- Operator-Level Extraction of the Odd Connes 1-Form from the Cayley–Bott Boundary Map:
For ANY Dirac operator D ∈ M_n(R), compressing the relative boundary derivation
[D, β_CB(U, V)] - [D, P] between U_star on the left and V on the right yields the
internal odd Connes 1-cocycle density ω_D(U_star, U) * P plus the background connection
term P * [D, V_star] * V. -/
theorem cayleyBottBoundary_derivation_extraction [Ring R]
    (D P G : Matrix n n R) {U U_star V V_star : Matrix n n R}
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    U_star * (commutator D (cayleyBottBoundary P U V_star) - commutator D P) * V =
    oddConnesDensity D U_star U * P + P * commutator D V_star * V := by
  have h_diff :
      commutator D (cayleyBottBoundary P U V_star) - commutator D P =
      commutator D U * V_star + U * commutator D V_star := by
    dsimp [cayleyBottBoundary]
    rw [commutator_add_right, add_sub_cancel_left, commutator_leibniz]
  rw [h_diff]
  dsimp [oddConnesDensity]
  calc
    U_star * (commutator D U * V_star + U * commutator D V_star) * V
      = (U_star * commutator D U) * (V_star * V) +
        (U_star * U) * commutator D V_star * V := by noncomm_ring
    _ = (U_star * commutator D U) * P + P * commutator D V_star * V := by
        rw [hPI.source_eq, hU.star_mul_self]

/-- Master Theorem 3 (Odd Connes 1-Cocycle Extraction from the Cayley–Bott Boundary Map):
Whenever the Dirac operator D is horizontal with respect to the reference partial isometry
([D, V_star] = 0), the odd Connes 1-cocycle τ₁(D; U_star, U) equals the trace of the
compressed relative derivation of the Cayley–Bott boundary projection β_CB(U, V). -/
theorem oddConnesCocycle_from_cayleyBottBoundary [CommRing R]
    (D P G : Matrix n n R) {U U_star V V_star : Matrix n n R}
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P)
    (hDV : commutator D V_star = 0) :
    Matrix.trace
      (U_star * (commutator D (cayleyBottBoundary P U V_star) - commutator D P) * V) =
    oddConnesCocycle D U_star U := by
  rw [cayleyBottBoundary_derivation_extraction D P G hPI hU]
  rw [hDV, mul_zero, zero_mul, add_zero]
  exact trace_oddConnesDensity_internal D hU

/-- Master Theorem 4 (Even Connes 2-Cocycle Gauge-Bott Compatibility):
For ANY Dirac operator D ∈ M_n(R) and corner unitary (U, U_star) on P, the even Connes
2-cocycle τ₂ of the Cayley–Bott boundary projection β_CB(U, V) under the unipotent shear
gauge transformation T_+(U, V) * D * T_-(U, V) equals the even Connes 2-cocycle τ₂(D; P). -/
theorem evenConnesCocycle_cayleyBottBoundary_compatibility [CommRing R]
    (D P G M : Matrix n n R) {U U_star V V_star : Matrix n n R}
    (hFlag : IsThreeLevelFlag P G M)
    (hPI : IsSiblingPartialIsometry V V_star P G)
    (hU : IsCornerUnitary U U_star P) :
    connesCocycle
      (cayleyBottShearPos U V_star * D * cayleyBottShearNeg U V_star)
      (cayleyBottBoundary P U V_star) =
    connesCocycle D P := by
  have h_inv_mul := cayleyBottShear_inv_mul P G M hFlag hPI hU
  have h_conj := cayleyBottBoundary_eq_shear_conj P G M hFlag hPI hU
  rw [← h_conj]
  have h_comm :
      commutator
        (cayleyBottShearPos U V_star * D * cayleyBottShearNeg U V_star)
        (cayleyBottShearPos U V_star * P * cayleyBottShearNeg U V_star) =
      cayleyBottShearPos U V_star * commutator D P * cayleyBottShearNeg U V_star := by
    dsimp [commutator]
    calc
      (cayleyBottShearPos U V_star * D * cayleyBottShearNeg U V_star) *
        (cayleyBottShearPos U V_star * P * cayleyBottShearNeg U V_star) -
        (cayleyBottShearPos U V_star * P * cayleyBottShearNeg U V_star) *
        (cayleyBottShearPos U V_star * D * cayleyBottShearNeg U V_star)
        = cayleyBottShearPos U V_star * D *
          (cayleyBottShearNeg U V_star * cayleyBottShearPos U V_star) * P *
          cayleyBottShearNeg U V_star -
          cayleyBottShearPos U V_star * P *
          (cayleyBottShearNeg U V_star * cayleyBottShearPos U V_star) * D *
          cayleyBottShearNeg U V_star := by noncomm_ring
      _ = cayleyBottShearPos U V_star * D * 1 * P * cayleyBottShearNeg U V_star -
          cayleyBottShearPos U V_star * P * 1 * D * cayleyBottShearNeg U V_star := by
          rw [h_inv_mul]
      _ = cayleyBottShearPos U V_star * (D * P - P * D) *
          cayleyBottShearNeg U V_star := by noncomm_ring
  have h_dens :
      connesDensity
        (cayleyBottShearPos U V_star * D * cayleyBottShearNeg U V_star)
        (cayleyBottShearPos U V_star * P * cayleyBottShearNeg U V_star) =
      cayleyBottShearPos U V_star * connesDensity D P * cayleyBottShearNeg U V_star := by
    dsimp [connesDensity]
    rw [h_comm]
    calc
      (cayleyBottShearPos U V_star * P * cayleyBottShearNeg U V_star) *
        ((cayleyBottShearPos U V_star * commutator D P * cayleyBottShearNeg U V_star) *
         (cayleyBottShearPos U V_star * commutator D P * cayleyBottShearNeg U V_star))
        = cayleyBottShearPos U V_star * P *
          (cayleyBottShearNeg U V_star * cayleyBottShearPos U V_star) * commutator D P *
          (cayleyBottShearNeg U V_star * cayleyBottShearPos U V_star) * commutator D P *
          cayleyBottShearNeg U V_star := by noncomm_ring
      _ = cayleyBottShearPos U V_star * P * 1 * commutator D P * 1 * commutator D P *
          cayleyBottShearNeg U V_star := by rw [h_inv_mul]
      _ = cayleyBottShearPos U V_star * (P * (commutator D P * commutator D P)) *
          cayleyBottShearNeg U V_star := by noncomm_ring
  dsimp [connesCocycle]
  rw [h_dens]
  rw [Matrix.trace_mul_comm (cayleyBottShearPos U V_star * connesDensity D P)
      (cayleyBottShearNeg U V_star)]
  have h_assoc :
      cayleyBottShearNeg U V_star * (cayleyBottShearPos U V_star * connesDensity D P) =
      (cayleyBottShearNeg U V_star * cayleyBottShearPos U V_star) * connesDensity D P := by
    noncomm_ring
  rw [h_assoc, h_inv_mul, one_mul]

/-- Master Theorem 5 (Cayley–Connes Reflection Pairing with Connes Curvature):
When the Dirac operator preserves the coarse genus stratum ([D, G] = 0), pairing the
Cayley–Connes reflection unitary U_CC(P, G) = P - (G - P) ∈ K₁(G * A * G) with the
Connes curvature [D, P]² yields the relative even Connes 2-cocycle difference
τ₂(D; P) - τ₂(D; G - P). -/
theorem cayleyConnesReflection_curvature_pairing [CommRing R]
    (D P G : Matrix n n R) (hDG : commutator D G = 0) :
    Matrix.trace (cayleyConnesReflection P G * (commutator D P * commutator D P)) =
    connesCocycle D P - connesCocycle D (G - P) := by
  have h_curv :
      commutator D (G - P) * commutator D (G - P) =
      commutator D P * commutator D P := by
    rw [commutator_sub_right, hDG, zero_sub, neg_mul_neg]
  dsimp [cayleyConnesReflection, connesCocycle, connesDensity]
  rw [h_curv, ← Matrix.trace_sub]
  have h_alg :
      (P - (G - P)) * (commutator D P * commutator D P) =
      P * (commutator D P * commutator D P) -
      (G - P) * (commutator D P * commutator D P) := by noncomm_ring
  rw [h_alg]

end NonCommutativeCayleyBott
