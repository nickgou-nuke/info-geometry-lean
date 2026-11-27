/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Physics.Octonion.ChiralZornAlgebra

/-!
# Reciprocal colour scaling on the noncommutative chiral Zorn carrier

For central reciprocal weights `q` and `q⁻¹`, the three-colour scaling
preserves the Zorn product exactly when `q ^ 3 = 1`.  This is stated on the
operator-coefficient carrier over an arbitrary nontrivial ring, not only on a
commutative scalar model.
-/

namespace InfoGeometry.Physics.Octonion.ChiralZornMatrix

variable {A : Type*} [Ring A]

private theorem chiralZorn_ext {X Y : ChiralZornMatrix A}
    (hnp : X.n_plus = Y.n_plus) (hnm : X.n_minus = Y.n_minus)
    (hsp : X.sigma_plus = Y.sigma_plus)
    (hsm : X.sigma_minus = Y.sigma_minus) : X = Y := by
  cases X
  cases Y
  simp_all

/-- Reciprocal scaling of the two vector channels, leaving the two scalar
channels fixed. -/
def reciprocalScale (q qi : A) (X : ChiralZornMatrix A) : ChiralZornMatrix A where
  n_plus := X.n_plus
  n_minus := X.n_minus
  sigma_plus := fun i => q * X.sigma_plus i
  sigma_minus := fun i => qi * X.sigma_minus i

private theorem centralPair (s t x y : A) (ht : ∀ z : A, t * z = z * t)
    (hst : s * t = 1) : (s * x) * (t * y) = x * y := by
  calc
    (s * x) * (t * y) = s * (x * t) * y := by noncomm_ring
    _ = s * (t * x) * y := by rw [ht x]
    _ = (s * t) * (x * y) := by noncomm_ring
    _ = x * y := by rw [hst]; noncomm_ring

private theorem centralPairSame (s x y : A) (hs : ∀ z : A, s * z = z * s) :
    (s * x) * (s * y) = (s * s) * (x * y) := by
  calc
    (s * x) * (s * y) = s * (x * s) * y := by noncomm_ring
    _ = s * (s * x) * y := by rw [hs x]
    _ = (s * s) * (x * y) := by noncomm_ring

private theorem colorDot_reciprocal (q qi : A)
    (hqi : ∀ x : A, qi * x = x * qi)
    (hqr : q * qi = 1) (x y : Fin 3 → A) :
    colorDot (fun i => q * x i) (fun i => qi * y i) = colorDot x y := by
  unfold colorDot
  rw [centralPair q qi (x 0) (y 0) hqi hqr,
    centralPair q qi (x 1) (y 1) hqi hqr,
    centralPair q qi (x 2) (y 2) hqi hqr]

private theorem colorCross_scale (s : A) (hs : ∀ x : A, s * x = x * s)
    (x y : Fin 3 → A) (c : Fin 3) :
    colorCross (fun i => s * x i) (fun i => s * y i) c =
      (s * s) * colorCross x y c := by
  unfold colorCross
  rw [centralPairSame s (x (nextColor c)) (y (prevColor c)) hs,
    centralPairSame s (x (prevColor c)) (y (nextColor c)) hs]
  noncomm_ring

private theorem colorPlusLinear (s a x y b : A) (hs : ∀ z : A, s * z = z * s) :
    a * (s * y) + (s * x) * b = s * (a * y + x * b) := by
  calc
    a * (s * y) + (s * x) * b = (a * s) * y + (s * x) * b := by noncomm_ring
    _ = (s * a) * y + (s * x) * b := by rw [hs a]
    _ = s * (a * y + x * b) := by noncomm_ring

private theorem colorMinusLinear (s x a b y : A) (hs : ∀ z : A, s * z = z * s) :
    (s * x) * a + b * (s * y) = s * (x * a + b * y) := by
  calc
    (s * x) * a + b * (s * y) = s * (x * a) + (b * s) * y := by noncomm_ring
    _ = s * (x * a) + (s * b) * y := by rw [hs b]
    _ = s * (x * a + b * y) := by noncomm_ring

private theorem reciprocalScale_mul_of_cube
    (q qi : A)
    (hq : ∀ x : A, q * x = x * q)
    (hqi : ∀ x : A, qi * x = x * qi)
    (hqr : q * qi = 1) (hql : qi * q = 1)
    (hcube : q ^ 3 = 1)
    (X Y : ChiralZornMatrix A) :
    reciprocalScale q qi (X * Y) =
      reciprocalScale q qi X * reciprocalScale q qi Y := by
  have hq2qi : q ^ 2 = qi := by
    calc
      q ^ 2 = q ^ 2 * (q * qi) := by rw [hqr, mul_one]
      _ = q ^ 3 * qi := by simp [pow_succ, mul_assoc]
      _ = qi := by rw [hcube]; simp
  have hqi2q : qi * qi = q := by
    calc
      qi * qi = (q * q) * (q * q) := by
        simpa [pow_two] using congrArg (fun z : A => z * z) hq2qi.symm
      _ = q ^ 3 * q := by noncomm_ring
      _ = q := by rw [hcube]; simp
  have hq2 : q * q = qi := by simpa [pow_two] using hq2qi
  apply chiralZorn_ext
  · change X.n_plus * Y.n_plus + colorDot X.sigma_plus Y.sigma_minus =
      X.n_plus * Y.n_plus + colorDot (fun i => q * X.sigma_plus i)
        (fun i => qi * Y.sigma_minus i)
    rw [colorDot_reciprocal q qi hqi hqr]
  · change colorDot X.sigma_minus Y.sigma_plus + X.n_minus * Y.n_minus =
      colorDot (fun i => qi * X.sigma_minus i)
        (fun i => q * Y.sigma_plus i) + X.n_minus * Y.n_minus
    rw [colorDot_reciprocal qi q hq hql]
  · funext c
    change q * (X.n_plus * Y.sigma_plus c + X.sigma_plus c * Y.n_minus -
        colorCross X.sigma_minus Y.sigma_minus c) =
      X.n_plus * (q * Y.sigma_plus c) + (q * X.sigma_plus c) * Y.n_minus -
        colorCross (fun i => qi * X.sigma_minus i)
          (fun i => qi * Y.sigma_minus i) c
    rw [colorPlusLinear q X.n_plus (X.sigma_plus c) (Y.sigma_plus c)
      Y.n_minus hq,
      colorCross_scale qi hqi X.sigma_minus Y.sigma_minus c,
      hqi2q]
    noncomm_ring
  · funext c
    change qi * (X.sigma_minus c * Y.n_plus + X.n_minus * Y.sigma_minus c +
        colorCross X.sigma_plus Y.sigma_plus c) =
      (qi * X.sigma_minus c) * Y.n_plus + X.n_minus * (qi * Y.sigma_minus c) +
        colorCross (fun i => q * X.sigma_plus i)
          (fun i => q * Y.sigma_plus i) c
    rw [colorMinusLinear qi (X.sigma_minus c) Y.n_plus X.n_minus
      (Y.sigma_minus c) hqi,
      colorCross_scale q hq X.sigma_plus Y.sigma_plus c,
      hq2]
    noncomm_ring

/-- On an arbitrary, possibly noncommutative coefficient ring,
reciprocal colour scaling preserves the full chiral Zorn product iff its
central unit weight has cube one.  The inverse weight is supplied explicitly
so the theorem does not impose commutativity on `A`. -/
theorem reciprocalScale_mul_iff_cube_eq_one
    (q qi : A)
    (hq : ∀ x : A, q * x = x * q)
    (hqi : ∀ x : A, qi * x = x * qi)
    (hqr : q * qi = 1) (hql : qi * q = 1) :
    (∀ X Y : ChiralZornMatrix A,
      reciprocalScale q qi (X * Y) =
        reciprocalScale q qi X * reciprocalScale q qi Y) ↔
      q ^ 3 = 1 := by
  constructor
  · intro hmul
    let X : ChiralZornMatrix A :=
      ⟨0, 0, fun _ => 0, fun i => if i = 0 then 1 else 0⟩
    let Y : ChiralZornMatrix A :=
      ⟨0, 0, fun _ => 0, fun i => if i = 1 then 1 else 0⟩
    have hcoord := congrArg (fun Z : ChiralZornMatrix A => Z.sigma_plus 2)
      (hmul X Y)
    have hXY : (X * Y).sigma_plus 2 = -1 := by
      change (ChiralZornMatrix.mul X Y).sigma_plus 2 = -1
      simp [X, Y, ChiralZornMatrix.mul, colorDot, colorCross, nextColor, prevColor]
    have hscaled :
        (reciprocalScale q qi X * reciprocalScale q qi Y).sigma_plus 2 =
          -(qi * qi) := by
      change (ChiralZornMatrix.mul (reciprocalScale q qi X)
        (reciprocalScale q qi Y)).sigma_plus 2 = -(qi * qi)
      simp [X, Y, reciprocalScale, ChiralZornMatrix.mul, colorDot,
        colorCross, nextColor, prevColor]
    have hleft : (reciprocalScale q qi (X * Y)).sigma_plus 2 = -q := by
      change q * (X * Y).sigma_plus 2 = -q
      rw [hXY]
      simp
    have hcoord' : -q = -(qi * qi) := hleft.symm.trans (hcoord.trans hscaled)
    have hrel : q = qi * qi := neg_injective hcoord'
    calc
      q ^ 3 = q ^ 2 * q := by simp [pow_succ, mul_assoc]
      _ = q ^ 2 * (qi * qi) := by rw [hrel]
      _ = q * (q * qi) * qi := by simp [pow_succ, mul_assoc]
      _ = q * qi := by
        calc
          q * (q * qi) * qi = q * 1 * qi := by rw [hqr]
          _ = q * qi := by simp
      _ = 1 := hqr
  · intro hcube X Y
    exact reciprocalScale_mul_of_cube q qi hq hqi hqr hql hcube X Y

private theorem reciprocalScale_mul_sigmaMinus_zero_test
    (q qi x y : A)
    (hmul : ∀ X Y : ChiralZornMatrix A,
      reciprocalScale q qi (X * Y) =
        reciprocalScale q qi X * reciprocalScale q qi Y) :
    qi * (x * y) = (q * x) * (q * y) := by
  let X : ChiralZornMatrix A :=
    ⟨0, 0, fun i => if i = 1 then x else 0, fun _ => 0⟩
  let Y : ChiralZornMatrix A :=
    ⟨0, 0, fun i => if i = 2 then y else 0, fun _ => 0⟩
  have hcoord := congrArg (fun Z : ChiralZornMatrix A => Z.sigma_minus 0)
    (hmul X Y)
  change qi * (ChiralZornMatrix.mul X Y).sigma_minus 0 =
    (ChiralZornMatrix.mul (reciprocalScale q qi X)
      (reciprocalScale q qi Y)).sigma_minus 0 at hcoord
  simpa [X, Y, reciprocalScale, ChiralZornMatrix.mul, colorCross,
    nextColor, prevColor] using hcoord

/-- On the full noncommutative three-channel carrier, multiplicativity of
reciprocal colour scaling forces centrality of the weight as well as the cubic
relation. The existing sufficient construction therefore has the exact
criterion: with a specified two-sided inverse `qi`, the scale is multiplicative
iff `q` is central and `q^3 = 1`. -/
theorem reciprocalScale_mul_iff_central_cube_eq_one
    (q qi : A) (hqr : q * qi = 1) (hql : qi * q = 1) :
    (∀ X Y : ChiralZornMatrix A,
      reciprocalScale q qi (X * Y) =
        reciprocalScale q qi X * reciprocalScale q qi Y) ↔
      (∀ x : A, q * x = x * q) ∧ q ^ 3 = 1 := by
  constructor
  · intro hmul
    have hqiSquare : qi = q * q := by
      simpa using reciprocalScale_mul_sigmaMinus_zero_test q qi 1 1 hmul
    have hqCentral : ∀ x : A, q * x = x * q := by
      intro x
      have htest := reciprocalScale_mul_sigmaMinus_zero_test q qi x 1 hmul
      have hrel : (q * q) * x = (q * x) * q := by
        simpa [hqiSquare] using htest
      calc
        q * x = (qi * q) * (q * x) := by rw [hql]; simp
        _ = qi * (q * (q * x)) := by noncomm_ring
        _ = qi * ((q * q) * x) := by simp [mul_assoc]
        _ = qi * ((q * x) * q) := by rw [hrel]
        _ = (qi * q) * x * q := by noncomm_ring
        _ = x * q := by rw [hql]; noncomm_ring
    have hcube : q ^ 3 = 1 := by
      calc
        q ^ 3 = q * (q * q) := by simp [pow_succ, mul_assoc]
        _ = q * qi := by rw [← hqiSquare]
        _ = 1 := hqr
    exact ⟨hqCentral, hcube⟩
  · rintro ⟨hq, hcube⟩
    have hqiCentral : ∀ x : A, qi * x = x * qi := by
      intro x
      calc
        qi * x = qi * x * (q * qi) := by rw [hqr]; noncomm_ring
        _ = qi * (x * q) * qi := by noncomm_ring
        _ = qi * (q * x) * qi := by rw [hq x]
        _ = (qi * q) * x * qi := by noncomm_ring
        _ = x * qi := by rw [hql]; noncomm_ring
    exact reciprocalScale_mul_of_cube q qi hq hqiCentral hqr hql hcube

end InfoGeometry.Physics.Octonion.ChiralZornMatrix
