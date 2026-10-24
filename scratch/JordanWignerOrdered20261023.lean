/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceDeWittChiralSplit
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Omega

/-!
Uncompiled sandbox proposal. Existing owners: Core.PeirceGrading and
Algebra.PeirceDeWittChiralSplit (division-free grading), Core.DiracSuperalgebra
(one MP pair), Clifford.Cl11JordanWignerCARBridge (finite matrix CAR), and
Physics.JordanWignerMultiDyads (categorical dyads). This addition is only the
ordered-prefix construction in an arbitrary ring from commuting local pairs.

`site d B i false = d i`, `site d B i true = B i`. Locality quantifies over
both Boolean choices: precisely the four cross-site commutations, not CAR.
No star assumptions enter the ring CAR proof. Adjoints require explicit duality.
The prefix recurrence multiplies on the right in increasing natural order.
-/
namespace InfoGeometry.Core.JordanWignerOrdered

open InfoGeometry.Algebra.PeirceDeWittChiralSplit

variable {R : Type*} [Ring R]

/-- Increasing ordered product; no commutative product instance is used. -/
def orderedPrefix (p : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => orderedPrefix p n * p n

theorem prefix_commute (p : ℕ → R) (n : ℕ) (x : R)
    (h : ∀ k, k < n → Commute (p k) x) : Commute (orderedPrefix p n) x := by
  induction n with
  | zero => exact Commute.one_left x
  | succ n ih =>
    exact (ih (fun k hk => h k (by omega))).mul_left (h n (by omega))

theorem prefix_pair_commute (p : ℕ → R)
    (h : ∀ k l, Commute (p k) (p l)) (n m : ℕ) :
    Commute (orderedPrefix p n) (orderedPrefix p m) := by
  apply prefix_commute
  intro k _
  exact (prefix_commute p m (p k) (fun l _ => h l k)).symm

theorem prefix_square (p : ℕ → R) (hs : ∀ k, p k * p k = 1)
    (hc : ∀ k l, Commute (p k) (p l)) (n : ℕ) :
    orderedPrefix p n * orderedPrefix p n = 1 := by
  induction n with
  | zero => simp [orderedPrefix]
  | succ n ih =>
    have h := (prefix_commute p n (p n) (fun k _ => hc k n)).eq
    calc
      orderedPrefix p (n + 1) * orderedPrefix p (n + 1) =
          orderedPrefix p n * (p n * orderedPrefix p n) * p n := by
            simp only [orderedPrefix]; noncomm_ring
      _ = (orderedPrefix p n * orderedPrefix p n) * (p n * p n) := by
        rw [← h]; noncomm_ring
      _ = 1 := by rw [ih, hs]; simp

/-- One exceptional factor contributes exactly one minus sign. -/
theorem prefix_sign (p : ℕ → R) (x : R) (i : ℕ)
    (hi : p i * x = -(x * p i))
    (ho : ∀ k, k ≠ i → p k * x = x * p k) (n : ℕ) :
    orderedPrefix p n * x =
      if i < n then -(x * orderedPrefix p n) else x * orderedPrefix p n := by
  induction n with
  | zero => simp [orderedPrefix]
  | succ n ih =>
    by_cases h : i < n
    · have hni : n ≠ i := by omega
      simp only [if_pos h] at ih
      rw [orderedPrefix, mul_assoc, ho n hni, ← mul_assoc, ih]
      simp [show i < n + 1 by omega, orderedPrefix, mul_assoc]
    · simp only [if_neg h] at ih
      by_cases he : n = i
      · subst n
        rw [orderedPrefix, mul_assoc, hi, mul_neg, ← mul_assoc, ih]
        simp [orderedPrefix, mul_assoc]
      · rw [orderedPrefix, mul_assoc, ho n he, ← mul_assoc, ih]
        simp [show ¬i < n + 1 by omega, orderedPrefix, mul_assoc]

/-- Two local choices, not an additional operator carrier. -/
def site {N : ℕ} (d B : Fin N → R) (i : Fin N) (s : Bool) : R :=
  if s then B i else d i

def parityFactor {N : ℕ} (d B : Fin N → R) (k : ℕ) : R :=
  if h : k < N then grading (d ⟨k, h⟩ * B ⟨k, h⟩) else 1

def prefix {N : ℕ} (d B : Fin N → R) (i : Fin N) : R :=
  orderedPrefix (parityFactor d B) i.val

def dressed {N : ℕ} (d B : Fin N → R) (i : Fin N) (s : Bool) : R :=
  prefix d B i * site d B i s

section Local
variable {d B : R}

theorem local_recover (hd : d * d = 0) (hn : d * B + B * d = 1) :
    d * B * d = d := by
  simpa [mul_add, ← mul_assoc, hd] using congrArg (fun z : R => d * z) hn

theorem local_projection (hd : d * d = 0) (hn : d * B + B * d = 1) :
    IsIdempotent (d * B) := by
  change d * B * (d * B) = d * B
  rw [← mul_assoc, local_recover hd hn]

theorem local_parity_d (hd : d * d = 0) (hn : d * B + B * d = 1) :
    grading (d * B) * d = -(d * grading (d * B)) := by
  have hr := local_recover hd hn
  unfold grading compIdempotent
  noncomm_ring [hd, hr]

theorem local_parity_B (hB : B * B = 0) (hn : d * B + B * d = 1) :
    grading (d * B) * B = -(B * grading (d * B)) := by
  have hr := local_recover hB (show B * d + d * B = 1 by simpa [add_comm] using hn)
  unfold grading compIdempotent
  noncomm_ring [hB, hr]

theorem parity_commute_of (a b x : R) (ha : Commute a x) (hb : Commute b x) :
    Commute (grading (a * b)) x := by
  exact (ha.mul_left hb).sub_left ((Commute.one_left x).sub_left (ha.mul_left hb))
end Local

section Chain
variable {N : ℕ} (d B : Fin N → R)
variable (hd : ∀ i, d i * d i = 0) (hB : ∀ i, B i * B i = 0)
variable (hn : ∀ i, d i * B i + B i * d i = 1)
variable (hc : ∀ i j, i ≠ j → ∀ s t, Commute (site d B i s) (site d B j t))

theorem parity_site_commute (i j : Fin N) (hij : i ≠ j) (s : Bool) :
    Commute (grading (d i * B i)) (site d B j s) :=
  parity_commute_of _ _ _ (hc i j hij false s) (hc i j hij true s)

theorem factors_commute (k l : ℕ) : Commute (parityFactor d B k) (parityFactor d B l) := by
  unfold parityFactor
  split_ifs with hk hl hl
  · by_cases he : (⟨k, hk⟩ : Fin N) = ⟨l, hl⟩
    · cases he; exact Commute.refl _
    · have ha := parity_site_commute d B hc ⟨k, hk⟩ ⟨l, hl⟩ he false
      have hb := parity_site_commute d B hc ⟨k, hk⟩ ⟨l, hl⟩ he true
      exact (ha.mul_right hb).sub_right ((Commute.one_right _).sub_right (ha.mul_right hb))
  · exact Commute.one_right _
  · exact Commute.one_left _
  · exact Commute.refl _

theorem factors_square (k : ℕ) : parityFactor d B k * parityFactor d B k = 1 := by
  unfold parityFactor
  split_ifs with hk
  · exact grading_sq _ (local_projection (hd _) (hn _))
  · simp

theorem prefix_sq (i : Fin N) : prefix d B i * prefix d B i = 1 :=
  prefix_square _ (factors_square d B hd hn) (factors_commute d B hc) _

theorem prefix_site_sign (i j : Fin N) (s : Bool) :
    prefix d B j * site d B i s =
      if i.val < j.val then -(site d B i s * prefix d B j)
      else site d B i s * prefix d B j := by
  apply prefix_sign
  · simp only [parityFactor, dif_pos i.isLt]
    cases s
    · exact local_parity_d (hd i) (hn i)
    · exact local_parity_B (hB i) (hn i)
  · intro k hki
    unfold parityFactor
    split_ifs with hk
    · exact (parity_site_commute d B hc ⟨k, hk⟩ i
        (fun he => hki (congrArg Fin.val he)) s).eq
    · simp

theorem prefix_own_commute (i : Fin N) (s : Bool) :
    Commute (prefix d B i) (site d B i s) := by
  change prefix d B i * site d B i s = site d B i s * prefix d B i
  simpa using prefix_site_sign d B hd hB hn hc i i s

/-- Dressing is an involution on each local operator. -/
theorem inverse_dressing (i : Fin N) (s : Bool) :
    prefix d B i * dressed d B i s = site d B i s := by
  rw [dressed, ← mul_assoc, prefix_sq d B hd hn hc, one_mul]

theorem dressed_same_product (i : Fin N) (s t : Bool) :
    dressed d B i s * dressed d B i t = site d B i s * site d B i t := by
  have h := (prefix_own_commute d B hd hB hn hc i s).eq
  calc
    dressed d B i s * dressed d B i t =
        prefix d B i * (site d B i s * prefix d B i) * site d B i t := by
          unfold dressed; noncomm_ring
    _ = (prefix d B i * prefix d B i) * (site d B i s * site d B i t) := by
      rw [← h]; noncomm_ring
    _ = _ := by rw [prefix_sq d B hd hn hc, one_mul]

theorem dressed_cross_of_lt (i j : Fin N) (hij : i.val < j.val) (s t : Bool) :
    dressed d B i s * dressed d B j t + dressed d B j t * dressed d B i s = 0 := by
  have hi := prefix_site_sign d B hd hB hn hc i j s
  simp only [if_pos hij] at hi
  have hj := prefix_site_sign d B hd hB hn hc j i t
  simp only [if_neg (show ¬j.val < i.val by omega)] at hj
  have hp := (prefix_pair_commute _ (factors_commute d B hc) i.val j.val).eq
  have hxy := (hc i j (fun he => by subst j; omega) s t).eq
  have hi' : site d B i s * prefix d B j = -(prefix d B j * site d B i s) := by
    simpa using (congrArg (fun z : R => -z) hi).symm
  have hab : dressed d B i s * dressed d B j t =
      -(dressed d B j t * dressed d B i s) := by
    calc
      dressed d B i s * dressed d B j t =
          prefix d B i * (site d B i s * prefix d B j) * site d B j t := by
            unfold dressed; noncomm_ring
      _ = -((prefix d B i * prefix d B j) * (site d B i s * site d B j t)) := by
        rw [hi']; noncomm_ring
      _ = -((prefix d B j * prefix d B i) * (site d B j t * site d B i s)) := by
        rw [hp, hxy]
      _ = -(dressed d B j t * dressed d B i s) := by
        unfold dressed
        rw [show (prefix d B j * prefix d B i) * (site d B j t * site d B i s) =
          prefix d B j * (prefix d B i * site d B j t) * site d B i s by noncomm_ring,
          hj]
        noncomm_ring
  rw [hab, neg_add_cancel]

/-- Full CAR for both local choices; nilpotence below is stronger than self-CAR
in characteristic two. The Kronecker value is nonzero only for opposite choices. -/
theorem dressed_car (i j : Fin N) (s t : Bool) :
    dressed d B i s * dressed d B j t + dressed d B j t * dressed d B i s =
      if i = j then (if s = t then 0 else 1) else 0 := by
  by_cases he : i = j
  · subst j
    rw [dressed_same_product d B hd hB hn hc, dressed_same_product d B hd hB hn hc]
    cases s <;> cases t <;> simp [site, hd, hB, hn, add_comm]
  · simp only [if_neg he]
    have hv : i.val ≠ j.val := fun h => he (Fin.ext h)
    by_cases hlt : i.val < j.val
    · exact dressed_cross_of_lt d B hd hB hn hc i j hlt s t
    · simpa [add_comm] using
        dressed_cross_of_lt d B hd hB hn hc j i (by omega) t s

theorem dressed_square_zero (i : Fin N) (s : Bool) :
    dressed d B i s * dressed d B i s = 0 := by
  rw [dressed_same_product d B hd hB hn hc]
  cases s <;> simp [site, hd, hB]

section Star
variable [StarRing R] (hdual : ∀ i, B i = star (d i))

theorem factor_star (k : ℕ) : star (parityFactor d B k) = parityFactor d B k := by
  unfold parityFactor
  split_ifs with hk
  · simp [grading, compIdempotent, hdual, star_mul]
  · simp

theorem prefix_star (i : Fin N) : star (prefix d B i) = prefix d B i := by
  have hall (n : ℕ) : star (orderedPrefix (parityFactor d B) n) =
      orderedPrefix (parityFactor d B) n := by
    induction n with
    | zero => simp [orderedPrefix]
    | succ n ih =>
      rw [orderedPrefix, star_mul, factor_star d B hdual, ih]
      exact (prefix_commute _ n (parityFactor d B n)
        (fun k _ => factors_commute d B hc k n)).symm.eq
  exact hall i.val

/-- The symbol `B` becomes an adjoint only under the explicit star-duality premise. -/
theorem dressed_star (i : Fin N) :
    star (dressed d B i false) = dressed d B i true := by
  simp only [dressed, star_mul, prefix_star d B hc hdual]
  change star (d i) * prefix d B i = prefix d B i * B i
  rw [← hdual i]
  exact (prefix_own_commute d B hd hB hn hc i true).symm.eq

/-- Reverse adjoint duality follows from involutivity of the given star. -/
theorem dressed_star_reverse (i : Fin N) :
    star (dressed d B i true) = dressed d B i false := by
  simpa using (congrArg star (dressed_star d B hd hB hn hc hdual i)).symm
end Star
end Chain
end InfoGeometry.Core.JordanWignerOrdered
