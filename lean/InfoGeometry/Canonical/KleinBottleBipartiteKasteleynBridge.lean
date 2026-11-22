/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Ring

namespace InfoGeometry.Canonical.KleinBottleBipartiteKasteleynBridge

/-- Division-free `ℤ/2` parity character `(-1)^k` in any commutative ring `R`. -/
def paritySign (R : Type*) [CommRing R] (k : ℤ) : R :=
  if k % 2 = 0 then 1 else -1

section SignLemmas
variable {R : Type*} [CommRing R]

theorem paritySign_sq (k : ℤ) : paritySign R k * paritySign R k = 1 := by
  dsimp [paritySign]; split_ifs <;> ring

theorem paritySign_add_one (k : ℤ) : paritySign R (k + 1) = -paritySign R k := by
  dsimp [paritySign]; split_ifs <;> first | omega | ring

theorem paritySign_sub_one (k : ℤ) : paritySign R (k - 1) = -paritySign R k := by
  dsimp [paritySign]; split_ifs <;> first | omega | ring

theorem paritySign_neg (k : ℤ) : paritySign R (-k) = paritySign R k := by
  dsimp [paritySign]; split_ifs <;> first | omega | ring

theorem paritySign_glide_bipartite (m n : ℤ) :
    paritySign R (m + 1 + -n) = -paritySign R (m + n) := by
  dsimp [paritySign]; split_ifs <;> first | omega | ring

end SignLemmas

abbrev LatticeState (R : Type*) := ℤ × ℤ → R

section Operators
variable (R : Type*) [CommRing R]

/-- Bipartite / CPT vertex grading `B(m, n) = (-1)^(m + n)`. -/
def bipartiteB : Module.End R (LatticeState R) where
  toFun ψ p := paritySign R (p.1 + p.2) * ψ p
  map_add' _ _ := by ext p; simp [mul_add]
  map_smul' _ _ := by ext p; simp [mul_left_comm]

/-- Row-parity seam cocycle `τ_y(m, n) = (-1)^n`. -/
def rowParityTau : Module.End R (LatticeState R) where
  toFun ψ p := paritySign R p.2 * ψ p
  map_add' _ _ := by ext p; simp [mul_add]
  map_smul' _ _ := by ext p; simp [mul_left_comm]

/-- Horizontal nearest-neighbor hopping `H_x`. -/
def kastHx : Module.End R (LatticeState R) where
  toFun ψ p := ψ (p.1 + 1, p.2) + ψ (p.1 - 1, p.2)
  map_add' _ _ := by ext p; simp; ring
  map_smul' _ _ := by ext p; simp [mul_add]

/-- Staggered Kasteleyn vertical hopping `H_y` with `π`-flux sign `(-1)^m`. -/
def kastHy : Module.End R (LatticeState R) where
  toFun ψ p := paritySign R p.1 * (ψ (p.1, p.2 + 1) + ψ (p.1, p.2 - 1))
  map_add' _ _ := by ext p; simp; ring
  map_smul' _ _ := by ext p; simp; ring

/-- Kasteleyn–Dirac bipartite operator `D = H_x + H_y`. -/
def kastDirac : Module.End R (LatticeState R) :=
  kastHx R + kastHy R

/-- Bare Klein-bottle glide pullback `(U_G ψ)(m, n) = ψ(m + 1, -n)`. -/
def bareGlideUG : Module.End R (LatticeState R) where
  toFun ψ p := ψ (p.1 + 1, -p.2)
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl

/-- Cocycle-dressed glide `Ũ_G = τ_y ∘ U_G` preserving Kasteleyn flux. -/
def dressedGlideUG : Module.End R (LatticeState R) :=
  rowParityTau R * bareGlideUG R

/-- Period-2 horizontal torus translation `T_{(2, 0)}`. -/
def transX2 : Module.End R (LatticeState R) where
  toFun ψ p := ψ (p.1 + 2, p.2)
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl

/-- Order-2 seam-twist involution `α(A) = τ_y A τ_y`. -/
def seamTwistAlpha (A : Module.End R (LatticeState R)) :
    Module.End R (LatticeState R) :=
  rowParityTau R * A * rowParityTau R

end Operators

section BridgeTheorems
variable {R : Type*} [CommRing R]

/-- Kasteleyn `π`-flux anticommutation `{H_x, H_y} = 0`. -/
theorem kastHx_anticomm_kastHy :
    kastHx R * kastHy R + kastHy R * kastHx R = 0 := by
  ext ψ p
  rcases p with ⟨m, n⟩
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    Pi.add_apply, Pi.zero_apply,
    kastHx, kastHy, LinearMap.coe_mk, AddHom.coe_mk,
    paritySign_add_one, paritySign_sub_one]
  ring

/-- Bare glide `U_G` twisted-commutes with `D` (`U_G D = α(D) U_G`). -/
theorem bareGlide_twistedCommutes_kastDirac :
    bareGlideUG R * kastDirac R = seamTwistAlpha R (kastDirac R) * bareGlideUG R := by
  ext ψ p
  rcases p with ⟨m, n⟩
  simp only [kastDirac, seamTwistAlpha, LinearMap.add_apply, Module.End.mul_apply,
    Pi.add_apply,
    bareGlideUG, rowParityTau, kastHx, kastHy, LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : (m + 1 - 1, -n) = (m, -n) := Prod.ext (by omega) rfl
  have h2 : (m - 1 + 1, -n) = (m, -n) := Prod.ext (by omega) rfl
  have h3 : (m + 1, -(n + 1)) = (m + 1, -n - 1) := Prod.ext rfl (by omega)
  have h4 : (m + 1, -(n - 1)) = (m + 1, -n + 1) := Prod.ext rfl (by omega)
  rw [h1, h2, h3, h4, paritySign_add_one, paritySign_sub_one]
  have hn_mul : paritySign R n * paritySign R n = 1 := paritySign_sq (R := R) n
  have hn_pow : paritySign R n ^ 2 = 1 := by simpa [pow_two] using hn_mul
  have hp1 : paritySign R (1 + n) = -paritySign R n := by
    rw [add_comm, paritySign_add_one]
  ring_nf
  rw [hp1]
  ring_nf
  rw [hn_pow]
  ring

/-- Cocycle-dressed glide satisfies `Ũ_G² = T_{(2, 0)}`, `[Ũ_G, D] = 0`, and `{Ũ_G, B} = 0`. -/
theorem dressedGlide_sq_comm_dirac_anticomm_grading :
    dressedGlideUG R * dressedGlideUG R = transX2 R ∧
    dressedGlideUG R * kastDirac R = kastDirac R * dressedGlideUG R ∧
    dressedGlideUG R * bipartiteB R + bipartiteB R * dressedGlideUG R = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext ψ p
    rcases p with ⟨m, n⟩
    simp only [dressedGlideUG, transX2, Module.End.mul_apply, rowParityTau,
      bareGlideUG, LinearMap.coe_mk, AddHom.coe_mk, paritySign_neg]
    have h : (m + 1 + 1, - -n) = (m + 2, n) := Prod.ext (by omega) (by omega)
    rw [h, ← mul_assoc, paritySign_sq, one_mul]
  · ext ψ p
    rcases p with ⟨m, n⟩
    simp only [dressedGlideUG, kastDirac, LinearMap.add_apply, Module.End.mul_apply,
      Pi.add_apply,
      rowParityTau, bareGlideUG, kastHx, kastHy, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : (m + 1 - 1, -n) = (m, -n) := Prod.ext (by omega) rfl
    have h2 : (m - 1 + 1, -n) = (m, -n) := Prod.ext (by omega) rfl
    have h3 : (m + 1, -(n + 1)) = (m + 1, -n - 1) := Prod.ext rfl (by omega)
    have h4 : (m + 1, -(n - 1)) = (m + 1, -n + 1) := Prod.ext rfl (by omega)
    rw [h1, h2, h3, h4, paritySign_add_one, paritySign_sub_one]
    have hn_mul : paritySign R n * paritySign R n = 1 := paritySign_sq (R := R) n
    have hn_pow : paritySign R n ^ 2 = 1 := by simpa [pow_two] using hn_mul
    have hp1 : paritySign R (1 + n) = -paritySign R n := by
      rw [add_comm, paritySign_add_one]
    ring_nf
    simp [hn_pow, hp1] <;> ring
  · ext ψ p
    rcases p with ⟨m, n⟩
    simp only [dressedGlideUG, bipartiteB, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.zero_apply, Pi.add_apply, Pi.zero_apply, Pi.neg_apply,
      rowParityTau, bareGlideUG, LinearMap.coe_mk, AddHom.coe_mk,
      paritySign_glide_bipartite]
    ring

end BridgeTheorems

end InfoGeometry.Canonical.KleinBottleBipartiteKasteleynBridge
