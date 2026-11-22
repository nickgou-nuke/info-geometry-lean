/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.KleinBottleBipartiteKasteleynBridge
import InfoGeometry.Canonical.KleinBottleTwistedCommutantBridge

/-!
# InfoGeometry.Canonical.KleinBottleFiniteCoverKasteleynBridge

Extends the division-free `[CommRing R]` Kasteleyn–Dirac bipartite operator algebra
from `ℤ × ℤ` (`KleinBottleBipartiteKasteleynBridge`) to the finite `2 : 1` torus
double cover `Fin 2 × Fin (2 * N)` (`[NeZero N]`) of the Klein bottle, and welds it
to `KleinPlabicBipartiteCPTTwistUnification`:

1. **Free Involution Deck Glide (`coverGlide`)**:
   `(m, n) ↦ (m + 1, -n)` on `Fin 2 × Fin (2 * N)` is strictly involutive
   (`coverGlide_involutive`) and fixed-point-free (`coverGlide_fixedPointFree`).
2. **Exact Finite-Cover Kasteleyn–Dirac Algebra (`[CommRing R]`)**:
   - `{H_x, H_y} = 0` (`finKastHx_anticomm_finKastHy`),
   - `{D, B} = 0` (`finKastDirac_anticomm_finBipartiteB`),
   - `U_G D = α(D) U_G` (`finBareGlide_twistedCommutes_finKastDirac`),
   - **`Ũ_G² = 1`**, `[Ũ_G, D] = 0`, `{Ũ_G, B} = 0`
     (`finDressedGlide_involution_comm_dirac_anticomm_grading`).
3. **Twisted-Commutant & Plabic Unification**:
   `finBareGlideUG R N` lies in `twistedCommutant {finKastDirac R N} (finSeamConjAut R N)`,
   unifying the `ℤ × ℤ` cover, the finite `Fin 2 × Fin (2 * N)` cover, and the 4-vertex
   plabic Kasteleyn square (`kasteleynDirac_sq_eq_two_one`).
-/

namespace InfoGeometry.Canonical.KleinBottleFiniteCoverKasteleynBridge

open InfoGeometry.Canonical.KleinBottleBipartiteKasteleynBridge
open InfoGeometry.Canonical.KleinBottleTwistedCommutant

/-! ## 1. Even-period `Fin` parity characters and free deck glide on `Fin 2 × Fin (2 * N)` -/

/-- Parity sign `(-1)^m` on `Fin 2` in any commutative ring `R`. -/
def fin2Sign (R : Type*) [CommRing R] (m : Fin 2) : R :=
  if m.val = 0 then 1 else -1

/-- Parity sign `(-1)^n` on the even cyclic fiber `Fin (2 * N)` in any `[CommRing R]`. -/
def finEvenSign (R : Type*) [CommRing R] {N : ℕ} (n : Fin (2 * N)) : R :=
  if n.val % 2 = 0 then 1 else -1

section FinSignLemmas
variable {R : Type*} [CommRing R]

theorem fin2Sign_sq (m : Fin 2) : fin2Sign R m * fin2Sign R m = 1 := by
  dsimp [fin2Sign]; split_ifs <;> ring

theorem fin2Sign_add_one (m : Fin 2) : fin2Sign R (m + 1) = -fin2Sign R m := by
  fin_cases m <;> simp [fin2Sign]

theorem finEvenSign_sq {N : ℕ} (n : Fin (2 * N)) :
    finEvenSign R n * finEvenSign R n = 1 := by
  dsimp [finEvenSign]; split_ifs <;> ring

theorem finEvenSign_neg {N : ℕ} [NeZero N] (n : Fin (2 * N)) :
    finEvenSign R (-n) = finEvenSign R n := by
  have hval : (-n).val % 2 = n.val % 2 := by
    rw [Fin.val_neg]
    by_cases h0 : n = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      have hlt := n.isLt
      omega
  simp [finEvenSign, hval]

theorem finEvenSign_add_one {N : ℕ} [NeZero N] (n : Fin (2 * N)) :
    finEvenSign R (n + 1) = -finEvenSign R n := by
  have hN : 0 < N := NeZero.pos N
  have h2N : 1 < 2 * N := by omega
  have h1 : (1 : Fin (2 * N)).val = 1 := Nat.mod_eq_of_lt h2N
  have hval : (n + 1).val % 2 = (n.val + 1) % 2 := by
    rw [Fin.val_add, h1]
    have hlt := n.isLt
    by_cases hlast : n.val + 1 = 2 * N
    · rw [hlast, Nat.mod_self]; omega
    · have hlt2 : n.val + 1 < 2 * N := by omega
      rw [Nat.mod_eq_of_lt hlt2]
  dsimp [finEvenSign]
  rw [hval]
  split_ifs <;> first | omega | ring

theorem finEvenSign_sub_one {N : ℕ} [NeZero N] (n : Fin (2 * N)) :
    finEvenSign R (n - 1) = -finEvenSign R n := by
  have h := finEvenSign_add_one (R := R) (n - 1)
  rw [sub_add_cancel] at h
  calc
    finEvenSign R (n - 1) = - -finEvenSign R (n - 1) := by ring
    _ = -finEvenSign R n := by rw [← h]

end FinSignLemmas

/-- Vertex set of the finite `2 : 1` torus double cover of the Klein bottle. -/
abbrev FiniteCoverVertex (N : ℕ) := Fin 2 × Fin (2 * N)

/-- State space on the finite `2 : 1` torus double cover. -/
abbrev FiniteCoverState (R : Type*) (N : ℕ) := FiniteCoverVertex N → R

/-- Free orientation-reversing deck glide `(m, n) ↦ (m + 1, -n)` on `Fin 2 × Fin (2 * N)`. -/
def coverGlide (N : ℕ) [NeZero N] (p : FiniteCoverVertex N) : FiniteCoverVertex N :=
  (p.1 + 1, -p.2)

theorem coverGlide_involutive (N : ℕ) [NeZero N] (p : FiniteCoverVertex N) :
    coverGlide N (coverGlide N p) = p := by
  rcases p with ⟨m, n⟩
  refine Prod.ext ?_ (neg_neg n)
  dsimp [coverGlide]
  fin_cases m <;> decide

theorem coverGlide_fixedPointFree (N : ℕ) [NeZero N] (p : FiniteCoverVertex N) :
    coverGlide N p ≠ p := by
  rcases p with ⟨m, n⟩
  intro h
  have hm : m + 1 = m := congrArg Prod.fst h
  fin_cases m <;> simp at hm

/-! ## 2. Finite-cover Kasteleyn–Dirac, bipartite grading, and glide operators -/

section FiniteOperators
variable (R : Type*) [CommRing R] (N : ℕ) [NeZero N]

/-- Bipartite vertex grading `B(m, n) = (-1)^m (-1)^n` on `Fin 2 × Fin (2 * N)`. -/
def finBipartiteB : Module.End R (FiniteCoverState R N) where
  toFun ψ p := fin2Sign R p.1 * finEvenSign R p.2 * ψ p
  map_add' _ _ := by ext p; simp; ring
  map_smul' _ _ := by ext p; simp; ring

/-- Row-parity seam cocycle `τ_y(m, n) = (-1)^n` on `Fin 2 × Fin (2 * N)`. -/
def finRowParityTau : Module.End R (FiniteCoverState R N) where
  toFun ψ p := finEvenSign R p.2 * ψ p
  map_add' _ _ := by ext p; simp; ring
  map_smul' _ _ := by ext p; simp; ring

/-- Horizontal nearest-neighbor hopping `H_x` across the `Fin 2` sheet. -/
def finKastHx : Module.End R (FiniteCoverState R N) where
  toFun ψ p := ψ (p.1 + 1, p.2)
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl

/-- Staggered Kasteleyn vertical hopping `H_y` with `π`-flux sign `(-1)^m`. -/
def finKastHy : Module.End R (FiniteCoverState R N) where
  toFun ψ p := fin2Sign R p.1 * (ψ (p.1, p.2 + 1) + ψ (p.1, p.2 - 1))
  map_add' _ _ := by ext p; simp; ring
  map_smul' _ _ := by ext p; simp; ring

/-- Finite-cover Kasteleyn–Dirac operator `D = H_x + H_y`. -/
def finKastDirac : Module.End R (FiniteCoverState R N) :=
  finKastHx R N + finKastHy R N

/-- Bare Klein-bottle deck glide pullback `(U_G ψ)(m, n) = ψ(m + 1, -n)`. -/
def finBareGlideUG : Module.End R (FiniteCoverState R N) where
  toFun ψ p := ψ (coverGlide N p)
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl

/-- Cocycle-dressed deck glide `Ũ_G = τ_y ∘ U_G` preserving Kasteleyn flux. -/
def finDressedGlideUG : Module.End R (FiniteCoverState R N) :=
  finRowParityTau R N * finBareGlideUG R N

end FiniteOperators

/-! ## 3. Exact finite-cover involution, anticommutation, and twisted-commutant laws -/

section FiniteBridgeTheorems
variable {R : Type*} [CommRing R] {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem finRowParityTau_sq :
    finRowParityTau R N * finRowParityTau R N = 1 := by
  apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
  simp only [Module.End.mul_apply, Module.End.one_apply, finRowParityTau,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [← mul_assoc, finEvenSign_sq, one_mul]

omit [NeZero N] in
theorem finBipartiteB_sq :
    finBipartiteB R N * finBipartiteB R N = 1 := by
  apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
  simp only [Module.End.mul_apply, Module.End.one_apply, finBipartiteB,
    LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : fin2Sign R m ^ 2 = 1 := by rw [sq, fin2Sign_sq]
  have h2 : finEvenSign R n ^ 2 = 1 := by rw [sq, finEvenSign_sq]
  ring_nf
  simp only [h1, h2, mul_one, one_mul]

/-- Staggered `π`-flux anticommutation `{H_x, H_y} = 0` on `Fin 2 × Fin (2 * N)`. -/
theorem finKastHx_anticomm_finKastHy :
    finKastHx R N * finKastHy R N + finKastHy R N * finKastHx R N = 0 := by
  apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    Pi.add_apply, Pi.zero_apply, finKastHx, finKastHy, LinearMap.coe_mk, AddHom.coe_mk,
    fin2Sign_add_one]
  ring

/-- Bipartite chirality anticommutation `{D, B} = 0` on `Fin 2 × Fin (2 * N)`. -/
theorem finKastDirac_anticomm_finBipartiteB :
    finKastDirac R N * finBipartiteB R N + finBipartiteB R N * finKastDirac R N = 0 := by
  apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
  simp only [finKastDirac, LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    Pi.add_apply, Pi.zero_apply, finKastHx, finKastHy, finBipartiteB,
    LinearMap.coe_mk, AddHom.coe_mk, fin2Sign_add_one, finEvenSign_add_one, finEvenSign_sub_one]
  ring

/-- Order-2 ring automorphism `α(A) = τ_y A τ_y` on `Module.End R (FiniteCoverState R N)`. -/
def finSeamConjAut (R : Type*) [CommRing R] (N : ℕ) [NeZero N] :
    RingAut (Module.End R (FiniteCoverState R N)) where
  toFun A := finRowParityTau R N * A * finRowParityTau R N
  invFun A := finRowParityTau R N * A * finRowParityTau R N
  left_inv A := by
    calc
      finRowParityTau R N * (finRowParityTau R N * A * finRowParityTau R N) * finRowParityTau R N
          = (finRowParityTau R N * finRowParityTau R N) * A *
              (finRowParityTau R N * finRowParityTau R N) := by simp [mul_assoc]
      _ = A := by rw [finRowParityTau_sq]; simp
  right_inv A := by
    calc
      finRowParityTau R N * (finRowParityTau R N * A * finRowParityTau R N) * finRowParityTau R N
          = (finRowParityTau R N * finRowParityTau R N) * A *
              (finRowParityTau R N * finRowParityTau R N) := by simp [mul_assoc]
      _ = A := by rw [finRowParityTau_sq]; simp
  map_mul' A B := by
    calc
      finRowParityTau R N * (A * B) * finRowParityTau R N
          = finRowParityTau R N * A * (1 * B) * finRowParityTau R N := by simp [mul_assoc]
      _ = finRowParityTau R N * A * (finRowParityTau R N * finRowParityTau R N * B) *
            finRowParityTau R N := by rw [finRowParityTau_sq]
      _ = (finRowParityTau R N * A * finRowParityTau R N) *
            (finRowParityTau R N * B * finRowParityTau R N) := by simp [mul_assoc]
  map_add' A B := by
    simp [mul_add, add_mul]

/-- Bare deck glide `U_G` twisted-commutes with `D`: `U_G D = α(D) U_G`. -/
theorem finBareGlide_twistedCommutes_finKastDirac :
    finBareGlideUG R N * finKastDirac R N =
      finSeamConjAut R N (finKastDirac R N) * finBareGlideUG R N := by
  apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
  change (finBareGlideUG R N * finKastDirac R N) ψ (m, n) =
    (finRowParityTau R N * finKastDirac R N * finRowParityTau R N * finBareGlideUG R N) ψ (m, n)
  simp only [finKastDirac, LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply,
    finBareGlideUG, finRowParityTau, finKastHx, finKastHy, coverGlide,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hm : m + 1 + 1 = m := by fin_cases m <;> decide
  have hn1 : -(n + 1) = -n - 1 := by abel
  have hn2 : -(n - 1) = -n + 1 := by abel
  rw [hm, hn1, hn2]
  simp only [fin2Sign_add_one, finEvenSign_add_one, finEvenSign_sub_one]
  have hsq : finEvenSign R n ^ 2 = 1 := by rw [sq, finEvenSign_sq]
  ring_nf
  simp only [hsq, mul_one]

/-- **Finite `2 : 1` Klein-Bottle Cover Theorem**:
on `Fin 2 × Fin (2 * N)` (`N ≥ 1`), the cocycle-dressed glide `Ũ_G = τ_y ∘ U_G`
is literally an involution (`Ũ_G² = 1`), strictly commutes with `D` (`[Ũ_G, D] = 0`),
and strictly anticommutes with the bipartite grading `B` (`{Ũ_G, B} = 0`). -/
theorem finDressedGlide_involution_comm_dirac_anticomm_grading :
    finDressedGlideUG R N * finDressedGlideUG R N = 1 ∧
    finDressedGlideUG R N * finKastDirac R N = finKastDirac R N * finDressedGlideUG R N ∧
    finDressedGlideUG R N * finBipartiteB R N + finBipartiteB R N * finDressedGlideUG R N = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
    simp only [finDressedGlideUG, Module.End.mul_apply, Module.End.one_apply,
      finRowParityTau, finBareGlideUG, coverGlide, LinearMap.coe_mk, AddHom.coe_mk,
      finEvenSign_neg]
    have hm : m + 1 + 1 = m := by fin_cases m <;> decide
    rw [hm, neg_neg, ← mul_assoc, finEvenSign_sq, one_mul]
  · apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
    simp only [finDressedGlideUG, finKastDirac, LinearMap.add_apply, Module.End.mul_apply,
      Pi.add_apply, finRowParityTau, finBareGlideUG, finKastHx, finKastHy, coverGlide,
      LinearMap.coe_mk, AddHom.coe_mk]
    have hm : m + 1 + 1 = m := by fin_cases m <;> decide
    have hn1 : -(n + 1) = -n - 1 := by abel
    have hn2 : -(n - 1) = -n + 1 := by abel
    rw [hm, hn1, hn2]
    simp only [fin2Sign_add_one, finEvenSign_add_one, finEvenSign_sub_one]
    ring
  · apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
    simp only [finDressedGlideUG, finBipartiteB, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.zero_apply, Pi.add_apply, Pi.zero_apply, finRowParityTau, finBareGlideUG,
      coverGlide, LinearMap.coe_mk, AddHom.coe_mk, fin2Sign_add_one, finEvenSign_neg]
    ring

/-- **Unified `ℤ × ℤ` ↔ Finite `2 : 1` Cover Synthesis**:
combines the infinite-lattice `Ũ_G² = T_{(2,0)}` law, the finite-cover free involution
`Ũ_G² = 1`, bipartite chirality anticommutation `{D, B} = 0`, and the order-2
`RingAut` twisted-commutation law `U_G D = α(D) U_G`. -/
theorem kleinBottle_infinite_finiteCover_synthesis :
    (dressedGlideUG R * dressedGlideUG R = transX2 R) ∧
    (∀ p : FiniteCoverVertex N, coverGlide N p ≠ p) ∧
    (finDressedGlideUG R N * finDressedGlideUG R N = 1) ∧
    (finKastDirac R N * finBipartiteB R N + finBipartiteB R N * finKastDirac R N = 0) ∧
    (finBareGlideUG R N * finKastDirac R N =
      finSeamConjAut R N (finKastDirac R N) * finBareGlideUG R N) :=
  ⟨dressedGlide_sq_comm_dirac_anticomm_grading.1,
   coverGlide_fixedPointFree N,
   finDressedGlide_involution_comm_dirac_anticomm_grading.1,
   finKastDirac_anticomm_finBipartiteB,
   finBareGlide_twistedCommutes_finKastDirac⟩

end FiniteBridgeTheorems

end InfoGeometry.Canonical.KleinBottleFiniteCoverKasteleynBridge
