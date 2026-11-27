/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.DeWittPeirceSuperalgebra
import InfoGeometry.Canonical.KleinBottleTomitaCrosscapBridge

/-!
# Peirce–DeWitt ↔ Tomita–Klein–Crosscap obstruction

The Tomita datum in `CrosscapDatum` is anti-multiplicative. This owner records
two exact ring-general consequences on the DeWitt/Peirce soul corners:

* anti-multiplicative `J` maps a left-to-right soul corner to the opposite
  right-to-left corner after star;
* if the same crosscap condition is imposed with a multiplicative `J` while
  the glide swaps the two Peirce sheets, the off-diagonal fermion soul must
  vanish.

These are direct algebra theorems in the existing owner carriers. No wrapper,
packet, witness or certificate field is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.DeWittPeirceCrosscapObstruction

open InfoGeometry.Algebra.DeWittPeirceSuperalgebra
open InfoGeometry.Canonical.KleinBottleTomitaCrosscap

variable {M : Type*} [Ring M] [StarRing M] [S : ChiralPeirceSystem M]

/-- Anti-multiplicative Tomita transport sends the left-to-right DeWitt soul
corner to the opposite right-to-left corner after star. -/
theorem crosscap_anti_maps_soulLR_to_RL
    (D : CrosscapDatum M)
    (hJ_PL : D.J.toFun S.PL = S.PR) (hJ_PR : D.J.toFun S.PR = S.PL)
    (hstar_PL : star S.PL = S.PL) (hstar_PR : star S.PR = S.PR)
    (X : M) :
    D.J.toFun (star (soul_LR X)) = soul_RL (star (D.J.toFun X)) := by
  dsimp [soul_LR, soul_RL]
  simp [star_mul, hstar_PL, hstar_PR, D.J.map_mul, D.J_star, hJ_PL, hJ_PR,
    mul_assoc]

/-- A multiplicative Tomita map is incompatible with a sheet-swapping glide
on the crosscap fixed locus: a left-to-right soul element satisfying the
crosscap condition must vanish. This is the obstruction that forces the
Tomita datum to be anti-multiplicative if fermionic corners are to survive. -/
theorem crosscap_soul_vanishes_of_multiplicative_J
    (D : CrosscapDatum M)
    (hJ_zero : D.J.toFun 0 = 0)
    (hJ_mul : ∀ x y : M, D.J.toFun (x * y) = D.J.toFun x * D.J.toFun y)
    (hJ_PL : D.J.toFun S.PL = S.PR) (hJ_PR : D.J.toFun S.PR = S.PL)
    (hΩ_PL : D.glide S.PL = S.PR) (hΩ_PR : D.glide S.PR = S.PL)
    (hstar_PL : star S.PL = S.PL) (hstar_PR : star S.PR = S.PR)
    (X : M) (hX : InCrosscapSubalgebra D (soul_LR X)) :
    soul_LR X = 0 := by
  let U := soul_LR X
  have hglideU : D.glide U = S.PR * D.glide X * S.PL := by
    dsimp [U, soul_LR]
    simp [map_mul, hΩ_PL, hΩ_PR]
  have hJstarU : D.J.toFun (star U) = S.PL * D.J.toFun (star X) * S.PR := by
    dsimp [U, soul_LR]
    simp [star_mul, hstar_PL, hstar_PR, hJ_mul, hJ_PL, hJ_PR, mul_assoc]
  have hproj_glide : S.PL * D.glide U * S.PR = 0 := by
    rw [hglideU]
    calc
      S.PL * (S.PR * D.glide X * S.PL) * S.PR
          = (S.PL * S.PR) * (D.glide X * S.PL * S.PR) := by noncomm_ring
      _ = 0 := by rw [S.h_PL_PR]; simp
  have hproj_J : S.PL * D.J.toFun (star U) * S.PR = D.J.toFun (star U) := by
    rw [hJstarU]
    calc
      S.PL * (S.PL * D.J.toFun (star X) * S.PR) * S.PR
          = (S.PL * S.PL) * D.J.toFun (star X) * (S.PR * S.PR) := by noncomm_ring
      _ = S.PL * D.J.toFun (star X) * S.PR := by rw [S.h_PL_sq, S.h_PR_sq]
  have hproj_eq := congrArg (fun Z : M => S.PL * Z * S.PR) hX
  have hJzero : D.J.toFun (star U) = 0 := by
    have hleft : S.PL * D.glide U * S.PR = 0 := hproj_glide
    have hright : S.PL * D.J.toFun (star U) * S.PR = D.J.toFun (star U) := hproj_J
    calc
      D.J.toFun (star U) = S.PL * D.J.toFun (star U) * S.PR := hright.symm
      _ = S.PL * D.glide U * S.PR := hproj_eq.symm
      _ = 0 := hleft
  have hJ_inj : Function.Injective D.J.toFun := by
    intro x y hxy
    calc
      x = D.J.toFun (D.J.toFun x) := (D.J.inv x).symm
      _ = D.J.toFun (D.J.toFun y) := by rw [hxy]
      _ = y := D.J.inv y
  have hJstarU_eq_J0 : D.J.toFun (star U) = D.J.toFun 0 := by
    simpa [hJ_zero] using hJzero
  have hstarU : star U = 0 := hJ_inj hJstarU_eq_J0
  have hU : U = 0 := by
    have h := congrArg star hstarU
    simpa using h
  simpa [U] using hU

/-! ### Exact 2 × 2 Peirce corner involution table (ring-general) -/

/-- The chiral grading acts by `-1` on the left-to-right soul corner. -/
theorem chiral_grading_soulLR_parity_odd (X : M) :
    G (A := M) * soul_LR X * G = -soul_LR X := by
  dsimp [soul_LR]
  calc
    G * (S.PL * X * S.PR) * G
        = (G * S.PL) * X * (S.PR * G) := by repeat rw [mul_assoc]
    _ = S.PL * X * (-S.PR) := by rw [G_mul_PL, PR_mul_G]
    _ = -(S.PL * X * S.PR) := by rw [mul_neg]

/-- A soul corner fixed by chiral grading is 2-torsion. -/
theorem chiral_grading_soulLR_fixed_two_nsmul_zero (X : M)
    (hfix : G (A := M) * soul_LR X * G = soul_LR X) :
    (2 : ℕ) • soul_LR X = 0 := by
  have hodd : G (A := M) * soul_LR X * G = -soul_LR X :=
    chiral_grading_soulLR_parity_odd X
  have hneg : -soul_LR X = soul_LR X := by rw [← hodd, hfix]
  have htwo : soul_LR X + soul_LR X = 0 := by
    calc
      soul_LR X + soul_LR X = -soul_LR X + soul_LR X := by rw [hneg]
      _ = 0 := neg_add_cancel _
  show (2 : ℕ) • soul_LR X = 0
  rw [two_nsmul]
  exact htwo

/-- A multiplicative involution swapping the sheets swaps the two soul corners. -/
theorem soulLR_mul_swap_to_soulRL
    (φ : M → M) (hφ : ∀ x y, φ (x * y) = φ x * φ y)
    (hφL : φ S.PL = S.PR) (hφR : φ S.PR = S.PL) (X : M) :
    φ (soul_LR X) = soul_RL (φ X) := by
  dsimp [soul_LR, soul_RL]
  rw [hφ, hφ, hφL, hφR]

/-- A multiplicative sheet-swap fixes no nonzero soul corner. -/
theorem soulLR_mul_swap_fixed_eq_zero
    (φ : M → M) (hφ : ∀ x y, φ (x * y) = φ x * φ y)
    (hφL : φ S.PL = S.PR) (hφR : φ S.PR = S.PL) (X : M)
    (hfix : φ (soul_LR X) = soul_LR X) : soul_LR X = 0 := by
  have hswap : φ (soul_LR X) = soul_RL (φ X) :=
    soulLR_mul_swap_to_soulRL φ hφ hφL hφR X
  have hx01 : soul_LR X = soul_RL (φ X) := hfix ▸ hswap
  have hproj : soul_LR X = S.PL * soul_LR X * S.PR := by
    dsimp [soul_LR]
    calc
      S.PL * X * S.PR = (S.PL * S.PL) * X * (S.PR * S.PR) := by
        rw [S.h_PL_sq, S.h_PR_sq]
      _ = S.PL * (S.PL * X * S.PR) * S.PR := by noncomm_ring
  calc
    soul_LR X = S.PL * soul_RL (φ X) * S.PR := by rw [hproj, hx01]
    _ = 0 := by
      dsimp [soul_RL]
      calc
        S.PL * (S.PR * φ X * S.PL) * S.PR
            = (S.PL * S.PR) * (φ X * S.PL * S.PR) := by noncomm_ring
        _ = 0 := by rw [S.h_PL_PR]; simp

/-- Star with fixed projectors swaps the two soul corners. -/
theorem star_soulLR_swap_to_soulRL
    (hstarL : star S.PL = S.PL) (hstarR : star S.PR = S.PR) (X : M) :
    star (soul_LR X) = soul_RL (star X) := by
  dsimp [soul_LR, soul_RL]
  rw [star_mul, star_mul, hstarR, hstarL]
  rw [mul_assoc]

/-- A self-adjoint soul corner vanishes: Majorana pairing needs both corners. -/
theorem soulLR_selfAdjoint_eq_zero
    (hstarL : star S.PL = S.PL) (hstarR : star S.PR = S.PR) (X : M)
    (hsa : star (soul_LR X) = soul_LR X) : soul_LR X = 0 := by
  have hswap : star (soul_LR X) = soul_RL (star X) :=
    star_soulLR_swap_to_soulRL hstarL hstarR X
  have hx01 : soul_LR X = soul_RL (star X) := hsa ▸ hswap
  have hproj : soul_LR X = S.PL * soul_LR X * S.PR := by
    dsimp [soul_LR]
    calc
      S.PL * X * S.PR = (S.PL * S.PL) * X * (S.PR * S.PR) := by
        rw [S.h_PL_sq, S.h_PR_sq]
      _ = S.PL * (S.PL * X * S.PR) * S.PR := by noncomm_ring
  calc
    soul_LR X = S.PL * soul_RL (star X) * S.PR := by rw [hproj, hx01]
    _ = 0 := by
      dsimp [soul_RL]
      calc
        S.PL * (S.PR * star X * S.PL) * S.PR
            = (S.PL * S.PR) * (star X * S.PL * S.PR) := by noncomm_ring
        _ = 0 := by rw [S.h_PL_PR]; simp

/-- An anti-multiplicative sheet-swap preserves each soul corner: the double
reversal cancels, so nonzero fermionic corners are allowed. -/
theorem soulLR_anti_swap_preserves
    (φ : M → M) (hφ : ∀ x y, φ (x * y) = φ y * φ x)
    (hφL : φ S.PL = S.PR) (hφR : φ S.PR = S.PL) (X : M) :
    φ (soul_LR X) = soul_LR (φ X) := by
  dsimp [soul_LR]
  rw [hφ, hφ, hφR, hφL]
  rw [mul_assoc]

/-- Star after an anti-multiplicative map is multiplicative. This is the
operator-level guardrail distinguishing `Ad_J` from `j(A) = J A^* J`. -/
theorem star_comp_anti_is_multiplicative
    (φ : M → M) (hφ : ∀ x y, φ (x * y) = φ y * φ x) (X Y : M) :
    star (φ (X * Y)) = star (φ X) * star (φ Y) := by
  rw [hφ, star_mul]

end InfoGeometry.Canonical.DeWittPeirceCrosscapObstruction
