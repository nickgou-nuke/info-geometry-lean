/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
import Mathlib.Data.ZMod.Basic

/-!
# Order-ten sign and stride action on source-ordered quintic coordinates

This file proves representation-level identities for a degree-five diagonal
weight and signed shifts of five-tuples. A separate owner proves a
Brioschi-shaped root identity from binary forms, but does not identify these
representations with each other or with the resolvent of an input quintic.
-/

namespace InfoGeometry.Erlangen.KleinQuinticOrderTenAction

/-- The diagonal weight on the source-ordered monomial `z₁^(5-j) z₂^j`. -/
def quinticWeight {R : Type*} [CommRing R] (ω ωInv : R) (j : Fin 6) : R :=
  ω ^ (5 - j.val) * ωInv ^ j.val

/-- The monomial weight separates into the odd-degree central sign and its
order-five phase. -/
theorem quinticWeight_factor {R : Type*} [CommRing R]
    (ω ωInv : R) (hω : ω ^ 5 = -1) (hInv : ω * ωInv = 1) (j : Fin 6) :
    quinticWeight ω ωInv j = -(ωInv ^ (2 * j.val)) := by
  have hj : 5 - j.val + j.val = 5 := by omega
  unfold quinticWeight
  calc
    ω ^ (5 - j.val) * ωInv ^ j.val
        = ω ^ (5 - j.val) * (ω * ωInv) ^ j.val * ωInv ^ j.val := by
            rw [hInv, one_pow, mul_one]
    _ = (ω ^ (5 - j.val) * ω ^ j.val) *
          (ωInv ^ j.val * ωInv ^ j.val) := by rw [mul_pow]; ring
    _ = ω ^ 5 * ωInv ^ (2 * j.val) := by
          rw [← pow_add, hj, ← pow_add, two_mul]
    _ = -(ωInv ^ (2 * j.val)) := by rw [hω]; simp

/-- Under reciprocal weights and `ω⁵ = -1`, each source-ordered monomial
weight has fifth power `-1` and tenth power `1`. This does not assert each
weight has exact order ten: the `j = 0` weight is `-1`. -/
theorem quinticWeight_fifth_tenth {R : Type*} [CommRing R]
    (ω ωInv : R) (hω : ω ^ 5 = -1) (hInv : ω * ωInv = 1) (j : Fin 6) :
    (quinticWeight ω ωInv j) ^ 5 = -1 ∧
      (quinticWeight ω ωInv j) ^ 10 = 1 := by
  have hInv5 : ωInv ^ 5 = -1 := by
    have h := congrArg (fun x : R => x * (-1))
      (show ω ^ 5 * ωInv ^ 5 = 1 by rw [← mul_pow, hInv, one_pow])
    rw [hω] at h
    linear_combination h
  have hFactor := quinticWeight_factor ω ωInv hω hInv j
  have hInv10 : ωInv ^ 10 = 1 := by
    calc
      ωInv ^ 10 = (ωInv ^ 5) ^ 2 := by rw [show 10 = 5 * 2 by norm_num, ← pow_mul]
      _ = 1 := by rw [hInv5]; ring
  have hPhase : (ωInv ^ (2 * j.val)) ^ 5 = 1 := by
    calc
      (ωInv ^ (2 * j.val)) ^ 5 = ((ωInv ^ j.val) ^ 2) ^ 5 := by
        rw [show 2 * j.val = j.val * 2 by omega, pow_mul]
      _ = (ωInv ^ j.val) ^ (5 * 2) := by rw [← pow_mul]
      _ = (ωInv ^ j.val) ^ (2 * 5) := by rw [show 5 * 2 = 2 * 5 by norm_num]
      _ = (ωInv ^ 10) ^ j.val := by
        rw [show 2 * 5 = 10 by norm_num, ← pow_mul, Nat.mul_comm]
        exact pow_mul ωInv 10 j.val
      _ = 1 := by rw [hInv10, one_pow]
  have hFive : (quinticWeight ω ωInv j) ^ 5 = -1 := by
    rw [hFactor, Odd.neg_pow (by decide : Odd 5), hPhase]
  refine ⟨hFive, ?_⟩
  calc
    (quinticWeight ω ωInv j) ^ 10 =
        ((quinticWeight ω ωInv j) ^ 5) ^ 2 := by rw [← pow_mul]
    _ = (-1 : R) ^ 2 := by rw [hFive]
    _ = 1 := by ring

/-- Signed stride-`s` cyclic action on five source-ordered coordinates. -/
def signedQuinticShift {W : Type*} [AddGroup W] (s : ZMod 5)
    (Q : ZMod 5 → W) : ZMod 5 → W :=
  fun i => -Q (i + s)

/-- Reindex a five-tuple by multiplication by `s`. This is an equivalence
when `s` is nonzero in the prime field `ZMod 5`. -/
def quinticStrideEquiv {W : Type*} (s : (ZMod 5)ˣ) :
    (ZMod 5 → W) ≃ (ZMod 5 → W) where
  toFun Q i := Q ((s : ZMod 5) * i)
  invFun Q i := Q ((↑s⁻¹ : ZMod 5) * i)
  left_inv Q := by
    funext i
    dsimp
    congr 1
    calc
      (s : ZMod 5) * ((↑s⁻¹ : ZMod 5) * i) =
          ((s : ZMod 5) * (↑s⁻¹ : ZMod 5)) * i := by ring
      _ = i := by simp
  right_inv Q := by
    funext i
    dsimp
    congr 1
    calc
      (↑s⁻¹ : ZMod 5) * ((s : ZMod 5) * i) =
          ((↑s⁻¹ : ZMod 5) * (s : ZMod 5)) * i := by ring
      _ = i := by simp

/-- The signed shift has fifth power equal to central negation and tenth
power equal to the identity. Its fifth-power law holds for every stride. -/
theorem signedQuinticShift_period {W : Type*} [AddGroup W]
    (s : ZMod 5) (Q : ZMod 5 → W) :
    (∀ i, signedQuinticShift s (signedQuinticShift s Q) i = Q (i + 2 * s)) ∧
    (signedQuinticShift s)^[5] Q = -Q ∧
    (signedQuinticShift s)^[10] Q = Q := by
  have h2 (P : ZMod 5 → W) (i : ZMod 5) :
      signedQuinticShift s (signedQuinticShift s P) i = P (i + 2 * s) := by
    simp [signedQuinticShift, neg_neg]
    congr 1
    ring
  have h5 : ∀ P : ZMod 5 → W, (signedQuinticShift s)^[5] P = -P := by
    intro P
    ext i
    have hmod : (5 : ZMod 5) = 0 := ZMod.natCast_self 5
    have hi : i + s + s + s + s + s = i := by
      calc
        i + s + s + s + s + s = i + (5 : ZMod 5) * s := by ring
        _ = i := by rw [hmod]; ring
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      signedQuinticShift, Pi.neg_apply, neg_neg]
    exact congrArg (fun k => -P k) hi
  have h10 : (signedQuinticShift s)^[10] Q = Q := by
    change ((signedQuinticShift s)^[5] ∘ (signedQuinticShift s)^[5]) Q = Q
    rw [Function.comp_apply, h5, h5]
    simp
  exact ⟨h2 Q, h5 Q, h10⟩

/-- The stride equivalence conjugates the stride-`s` signed shift to the
source-order unit shift. -/
theorem quinticStrideEquiv_intertwines {W : Type*} [AddGroup W]
    (s : (ZMod 5)ˣ) (Q : ZMod 5 → W) :
    quinticStrideEquiv s (signedQuinticShift (s : ZMod 5) Q) =
      signedQuinticShift 1 (quinticStrideEquiv s Q) := by
  funext i
  simp only [quinticStrideEquiv, Equiv.coe_fn_mk, signedQuinticShift]
  congr 1
  ring_nf

/-- Central-character obstruction to identifying the binary quintic representation
with an ordinary five-root permutation representation.  If the fifth power of
the generator is `-1` on the source and `+1` on the target, every equivariant
linear map is zero.  Thus an identification with an ordinary resolvent root
module cannot be an isomorphism; a nonzero bridge must instead use a target
with the same central sign (or first pass through a separately defined
quotient/subrepresentation).

The theorem is stated for actual complex vector spaces and linear operators;
it does not assume that a resolvent carrier has already been constructed. -/
theorem equivariant_linearMap_eq_zero_of_opposite_fifth_powers
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (g : V →ₗ[ℂ] V) (h : W →ₗ[ℂ] W) (f : V →ₗ[ℂ] W)
    (hg5 : ∀ v, g (g (g (g (g v)))) = -v)
    (hh5 : ∀ w, h (h (h (h (h w)))) = w)
    (hintertwine : ∀ v, f (g v) = h (f v)) : f = 0 := by
  ext v
  have hiter : f (g (g (g (g (g v))))) = h (h (h (h (h (f v))))) := by
    calc
      f (g (g (g (g (g v))))) = h (f (g (g (g (g v))))) := hintertwine _
      _ = h (h (f (g (g (g v))))) := by rw [hintertwine]
      _ = h (h (h (f (g (g v))))) := by rw [hintertwine]
      _ = h (h (h (h (f (g v))))) := by rw [hintertwine]
      _ = h (h (h (h (h (f v))))) := by rw [hintertwine]
  rw [hg5, map_neg, hh5] at hiter
  have hsum : f v + f v = 0 := (neg_eq_iff_add_eq_zero).mp hiter
  have htwo : (2 : ℂ) • f v = 0 := by simpa [two_smul] using hsum
  calc
    f v = (2 : ℂ)⁻¹ • ((2 : ℂ) • f v) := by
      rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
    _ = 0 := by rw [htwo]; simp

end InfoGeometry.Erlangen.KleinQuinticOrderTenAction
