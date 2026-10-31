/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Algebra.Star.Basic

/-!
# Star reversal and grading-twisted anti-involution

Algebraic content of transcript turns 222 and 227. The carrier is an arbitrary
star-ring, not a scalar model. A self-adjoint idempotent supplies the grading.
No positivity, norm, probability, or Hilbert-space assertion is made.
Dependency order: star reversal of corners → star table of generators;
self-adjoint grading → twisted anti-involution → principal-ideal/chart duality.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B] {P : B} (hPs : star P = P)
include hPs

theorem star_conePlus (A : B) : star (conePlus P A) = coneMinus P (star A) := by
  simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPs, mul_assoc]

theorem star_coneMinus (A : B) : star (coneMinus P A) = conePlus P (star A) := by
  simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPs, mul_assoc]

theorem star_invS : star (invS P) = invS P := by
  simp only [invS, star_sub, star_one, hPs]

theorem star_genPhi (A : B) : star (genPhi P A (star A)) = genPhi P A (star A) := by
  simp only [genPhi, star_add, star_conePlus hPs, star_coneMinus hPs, star_star]
  exact add_comm _ _

theorem star_genJ (A : B) : star (genJ P A (star A)) = -genJ P A (star A) := by
  simp only [genJ, star_sub, star_conePlus hPs, star_coneMinus hPs, star_star, neg_sub]

theorem star_genV (A : B) : star (genV P A (star A)) = genV P A (star A) := by
  simp only [genV, anticomm, star_add, star_mul, star_conePlus hPs,
    star_coneMinus hPs, star_star]

theorem star_genSig (A : B) : star (genSig P A (star A)) = genSig P A (star A) := by
  simp only [genSig, comm, star_sub, star_mul, star_conePlus hPs,
    star_coneMinus hPs, star_star]

variable (hP : P * P = P)
include hP

theorem grading_star_involutive (X : B) :
    invS P * star (invS P * star X * invS P) * invS P = X := by
  simp only [star_mul, star_invS hPs, star_star]
  peirce_nf hP

omit hPs in
/-- Product reversal requires the grading square, not self-adjointness. -/
theorem grading_star_mul (X Y : B) :
    invS P * star (X * Y) * invS P =
      (invS P * star Y * invS P) * (invS P * star X * invS P) := by
  rw [star_mul]
  peirce_nf hP

theorem grading_star_left_ideal (X : B) :
    invS P * star (X * P) * invS P = P * (invS P * star X * invS P) := by
  rw [star_mul, hPs]
  peirce_nf hP

theorem grading_star_right_ideal (X : B) :
    invS P * star (P * X) * invS P = (invS P * star X * invS P) * P := by
  rw [star_mul, hPs]
  peirce_nf hP

theorem grading_star_upper_chart (A : B) :
    invS P * star (P - conePlus P A) * invS P = P + coneMinus P (star A) := by
  rw [star_sub, hPs, star_conePlus hPs]
  peirce_nf hP

theorem grading_star_lower_chart (A : B) :
    invS P * star (P + coneMinus P A) * invS P = P - conePlus P (star A) := by
  rw [star_add, hPs, star_coneMinus hPs]
  peirce_nf hP

theorem grading_star_genPhi (A : B) :
    invS P * star (genPhi P A (star A)) * invS P = -genPhi P A (star A) := by
  rw [star_genPhi hPs]
  peirce_nf hP

theorem grading_star_genJ (A : B) :
    invS P * star (genJ P A (star A)) * invS P = genJ P A (star A) := by
  rw [star_genJ hPs]
  peirce_nf hP

theorem grading_star_genV (A : B) :
    invS P * star (genV P A (star A)) * invS P = genV P A (star A) := by
  rw [star_genV hPs]
  peirce_nf hP

theorem grading_star_genSig (A : B) :
    invS P * star (genSig P A (star A)) * invS P = genSig P A (star A) := by
  rw [star_genSig hPs]
  peirce_nf hP

omit hPs hP

/-- Symmetric part `W + W⋆` of an operator in a star-ring (DIGRAC symmetric component). -/
def digracSym (W : B) : B := W + star W

/-- Skew-adjoint part `W - W⋆` of an operator in a star-ring (DIGRAC flow-imbalance component). -/
def digracImb (W : B) : B := W - star W

/-- Parity-twisted self-adjoint sum `S N₊ + N₊⋆ S` (MagNet adjacency operator). -/
def magnetAdj (P A : B) : B :=
  invS P * conePlus P A + star (conePlus P A) * invS P

/-- Operator difference `D - (S N₊ + N₊⋆ S)` (MagNet Laplacian operator). -/
def magnetLaplacian (P D A : B) : B := D - magnetAdj P A

include hPs hP

/-- **DIGRAC Directed Adjacency Decomposition & MagNet Magnetic Laplacian**:
1. Any operator `W` splits into its symmetric part `digracSym W = W + W⋆` and
   skew-adjoint flow-imbalance part `digracImb W = W - W⋆`, with
   `digracSym W + digracImb W = 2 W`, `(digracSym W)⋆ = digracSym W`, and
   `(digracImb W)⋆ = -digracImb W`.
2. On the directed corner `W = N₊ = P A (1 - P)` with self-adjoint `P`, the
   symmetric and skew-adjoint components recover `Φ = N₊ + N₋` and `J = N₊ - N₋`
   with `C = A⋆`, and `(digracImb N₊)² = -V`.
3. Twisting `N₊` by the grading involution `S = 2P - 1` produces the self-adjoint
   operator `magnetAdj P A = S N₊ + N₊⋆ S = J S` whose square is `+V`, and for
   any self-adjoint degree operator `D⋆ = D`, `magnetLaplacian P D A` is
   self-adjoint. -/
theorem digrac_flow_imbalance_and_magnet_laplacian (W A D : B) :
    digracSym W + digracImb W = (2 : ℤ) • W ∧
    star (digracSym W) = digracSym W ∧
    star (digracImb W) = -digracImb W ∧
    digracSym (conePlus P A) = genPhi P A (star A) ∧
    digracImb (conePlus P A) = genJ P A (star A) ∧
    digracImb (conePlus P A) * digracImb (conePlus P A) = -genV P A (star A) ∧
    magnetAdj P A = invS P * genJ P A (star A) ∧
    star (magnetAdj P A) = magnetAdj P A ∧
    (star D = D → star (magnetLaplacian P D A) = magnetLaplacian P D A) ∧
    magnetAdj P A * magnetAdj P A = genV P A (star A) := by
  have hMagStar : star (magnetAdj P A) = magnetAdj P A := by
    simp only [magnetAdj, star_add, star_mul, star_invS hPs, star_star, add_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hMagStar, ?_, ?_⟩
  · unfold digracSym digracImb
    abel_nf
  · simp only [digracSym, star_add, star_star, add_comm]
  · simp only [digracImb, star_sub, star_star, neg_sub]
  · rw [digracSym, star_conePlus hPs, genPhi]
  · rw [digracImb, star_conePlus hPs, genJ]
  · rw [digracImb, star_conePlus hPs]
    peirce_nf hP
  · rw [magnetAdj, star_conePlus hPs]
    peirce_nf hP
  · intro hD
    simp only [magnetLaplacian, star_sub, hD, hMagStar]
  · rw [magnetAdj, star_conePlus hPs]
    peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
