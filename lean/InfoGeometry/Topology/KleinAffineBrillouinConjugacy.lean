/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinAffineOrbitQuotient
import InfoGeometry.Topology.KleinBottleOrbitQuotient
import InfoGeometry.Topology.KleinBrillouinBase
import InfoGeometry.Topology.KleinDeckNormalForm
import Mathlib.Tactic

/-!
# Coordinate comparison of the Klein covering actions

The affine deck model reflects the first coordinate and translates the second,
whereas the Brillouin glide translates the first coordinate and reflects the
second.  A coordinate swap with period rescaling identifies the two generator
actions.  We also prove that each affine deck element maps to either the
identity or the glide after passage to the Brillouin torus.  Quotient
fibers are characterized exactly, and the induced quotient map is bijective.
The affine quotient's quotient-map property, needed to establish continuity of
the inverse, is not asserted here.
-/

namespace InfoGeometry.Topology.KleinAffineBrillouinConjugacy

open InfoGeometry.Topology.KleinAffineOrbitQuotient
open InfoGeometry.Topology.KleinQuotientDeckInvariants
open KleinBrillouinBase

/-- The coordinate swap and period rescaling from the affine cover to the
Brillouin cover. -/
noncomputable def affineToBrillouinCover
    (p : KleinAffineOrbitQuotient.Plane) : KleinBrillouinBase.Cover :=
  (Real.pi * p.2, (2 * Real.pi) * p.1)

/-- The inverse coordinate change. -/
noncomputable def brillouinToAffineCover
    (p : KleinBrillouinBase.Cover) : KleinAffineOrbitQuotient.Plane :=
  (p.2 / (2 * Real.pi), p.1 / Real.pi)

/-- The coordinate change is a bijection of covering planes. -/
noncomputable def coverEquiv :
    KleinAffineOrbitQuotient.Plane ≃ KleinBrillouinBase.Cover where
  toFun := affineToBrillouinCover
  invFun := brillouinToAffineCover
  left_inv := by
    rintro ⟨u, v⟩
    simp only [affineToBrillouinCover, brillouinToAffineCover, Prod.mk.injEq]
    constructor <;> field_simp
  right_inv := by
    rintro ⟨x, y⟩
    simp only [affineToBrillouinCover, brillouinToAffineCover, Prod.mk.injEq]
    constructor <;> field_simp

private theorem circle_add_int_period (x : ℝ) (n : ℤ) :
    ((x + (n : ℝ) * (2 * Real.pi) : ℝ) : MomentumCircle) =
      (x : MomentumCircle) := by
  have hperiod : ((n • (2 * Real.pi : ℝ) : ℝ) : MomentumCircle) = 0 := by
    rw [AddCircle.coe_zsmul, two_pi_eq_zero, zsmul_zero]
  have hmul : (n • (2 * Real.pi : ℝ) : ℝ) =
      (n : ℝ) * (2 * Real.pi) := by
    rw [zsmul_eq_mul]
  rw [← hmul, AddCircle.coe_add, hperiod, add_zero]

private theorem circle_eq_iff_period {x y : ℝ} :
    (x : MomentumCircle) = (y : MomentumCircle) ↔
      ∃ n : ℤ, n • (2 * Real.pi : ℝ) = x - y := by
  constructor
  · intro h
    have hz : ((x - y : ℝ) : MomentumCircle) = 0 := by
      rw [AddCircle.coe_sub]
      exact sub_eq_zero.mpr h
    exact (AddCircle.coe_eq_zero_iff (p := 2 * Real.pi)).mp hz
  · rintro ⟨n, hn⟩
    have hz : ((x - y : ℝ) : MomentumCircle) = 0 :=
      (AddCircle.coe_eq_zero_iff (p := 2 * Real.pi)).2 ⟨n, hn⟩
    rw [AddCircle.coe_sub] at hz
    exact sub_eq_zero.mp hz

/-- The affine horizontal translation becomes the Brillouin transverse period. -/
theorem affineToBrillouinCover_deckA
    (p : KleinAffineOrbitQuotient.Plane) :
    affineToBrillouinCover (KleinAffineOrbitQuotient.deckAct
      KleinDeckNormalForm.a p) =
      KleinBrillouinBase.ty (affineToBrillouinCover p) := by
  rcases p with ⟨u, v⟩
  apply Prod.ext
  · simp [affineToBrillouinCover, KleinAffineOrbitQuotient.deckAct,
      KleinQuotientDeckInvariants.deckAction, KleinDeckNormalForm.a,
      KleinDeckGroup.a, signR, signZ, KleinBrillouinBase.ty]
  · simp [affineToBrillouinCover, KleinAffineOrbitQuotient.deckAct,
      KleinQuotientDeckInvariants.deckAction, KleinDeckNormalForm.a,
      KleinDeckGroup.a, signR, signZ, KleinBrillouinBase.ty]
    ring

/-- The affine reflection-and-translation generator becomes the Brillouin
glide. -/
theorem affineToBrillouinCover_deckB
    (p : KleinAffineOrbitQuotient.Plane) :
    affineToBrillouinCover (KleinAffineOrbitQuotient.deckAct
      KleinDeckNormalForm.b p) =
      KleinBrillouinBase.glide (affineToBrillouinCover p) := by
  rcases p with ⟨u, v⟩
  apply Prod.ext
  · simp [affineToBrillouinCover, KleinAffineOrbitQuotient.deckAct,
      KleinQuotientDeckInvariants.deckAction, KleinDeckNormalForm.b,
      KleinDeckGroup.b, signR, signZ, KleinBrillouinBase.glide]
    ring
  · simp [affineToBrillouinCover, KleinAffineOrbitQuotient.deckAct,
      KleinQuotientDeckInvariants.deckAction, KleinDeckNormalForm.b,
      KleinDeckGroup.b, signR, signZ, KleinBrillouinBase.glide]

/-- Every affine deck transformation becomes either the identity or the
Brillouin glide after passage to the Brillouin torus.  The parity of the
vertical deck coordinate is the only remaining datum. -/
theorem coverToTorus_deckAct_orbit (g : KleinAffineOrbitQuotient.Deck)
    (p : KleinAffineOrbitQuotient.Plane) :
    coverToTorus (affineToBrillouinCover
      (KleinAffineOrbitQuotient.deckAct g p)) =
        coverToTorus (affineToBrillouinCover p) ∨
    coverToTorus (affineToBrillouinCover
      (KleinAffineOrbitQuotient.deckAct g p)) =
        torusGlide (coverToTorus (affineToBrillouinCover p)) := by
  rcases p with ⟨u, v⟩
  by_cases heven : g.n % 2 = 0
  · left
    have hnZ : g.n = 2 * (g.n / 2) := by omega
    have hnR : (g.n : ℝ) = 2 * ((g.n / 2 : ℤ) : ℝ) := by
      exact_mod_cast hnZ
    have hsign : signR g.n = 1 := by
      simp [signR, signZ, heven]
    apply Prod.ext
    · dsimp [coverToTorus, affineToBrillouinCover,
        KleinAffineOrbitQuotient.deckAct, KleinQuotientDeckInvariants.deckAction]
      have hreal : Real.pi * (v + (g.n : ℝ)) =
          Real.pi * v + ((g.n / 2 : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hnR]
        ring
      rw [hreal]
      exact circle_add_int_period (Real.pi * v) (g.n / 2)
    · dsimp [coverToTorus, affineToBrillouinCover,
        KleinAffineOrbitQuotient.deckAct, KleinQuotientDeckInvariants.deckAction]
      rw [hsign]
      simp only [one_mul]
      have hreal : (2 * Real.pi) * (u + (g.m : ℝ)) =
          (2 * Real.pi) * u + (g.m : ℝ) * (2 * Real.pi) := by ring
      rw [hreal]
      exact circle_add_int_period ((2 * Real.pi) * u) g.m
  · right
    have hodd : g.n % 2 = 1 := by omega
    have hnZ : g.n = 2 * (g.n / 2) + 1 := by omega
    have hnR : (g.n : ℝ) = 2 * ((g.n / 2 : ℤ) : ℝ) + 1 := by
      exact_mod_cast hnZ
    have hsign : signR g.n = -1 := by
      simp [signR, signZ, hodd]
    apply Prod.ext
    · dsimp [coverToTorus, affineToBrillouinCover,
        KleinAffineOrbitQuotient.deckAct, KleinQuotientDeckInvariants.deckAction,
        torusGlide]
      have hreal : Real.pi * (v + (g.n : ℝ)) =
          (Real.pi * v + Real.pi) + ((g.n / 2 : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hnR]
        ring
      rw [hreal]
      exact (circle_add_int_period (Real.pi * v + Real.pi) (g.n / 2)).trans
        (by rw [AddCircle.coe_add])
    · dsimp [coverToTorus, affineToBrillouinCover,
        KleinAffineOrbitQuotient.deckAct, KleinQuotientDeckInvariants.deckAction,
        torusGlide]
      rw [hsign]
      simp only [neg_one_mul]
      have hreal : (2 * Real.pi) * (-(u) + (g.m : ℝ)) =
          -(2 * Real.pi * u) + (g.m : ℝ) * (2 * Real.pi) := by ring
      rw [hreal]
      exact (circle_add_int_period (-(2 * Real.pi * u)) g.m).trans
        (by rw [AddCircle.coe_neg])

/-- The Brillouin orbit projection is constant on every affine deck orbit. -/
theorem orbitProjection_deckAct (g : KleinAffineOrbitQuotient.Deck)
    (p : KleinAffineOrbitQuotient.Plane) :
    KleinBottleOrbitQuotient.quotientMap
        (coverToTorus (affineToBrillouinCover
          (KleinAffineOrbitQuotient.deckAct g p))) =
      KleinBottleOrbitQuotient.quotientMap
        (coverToTorus (affineToBrillouinCover p)) := by
  rcases coverToTorus_deckAct_orbit g p with h | h
  · rw [h]
  · rw [h, KleinBottleOrbitQuotient.quotientMap_glide]

/-- Equality in the Brillouin glide quotient after the coordinate change is
exactly equality up to the affine Klein deck action.  The even and odd cases
of the vertical deck coordinate correspond respectively to the identity and
glide branches of the torus orbit relation. -/
theorem quotientMap_affineToBrillouinCover_eq_iff_deckOrbit
    (p q : KleinAffineOrbitQuotient.Plane) :
    KleinBottleOrbitQuotient.quotientMap
        (coverToTorus (affineToBrillouinCover p)) =
      KleinBottleOrbitQuotient.quotientMap
        (coverToTorus (affineToBrillouinCover q)) ↔
      ∃ g : KleinAffineOrbitQuotient.Deck,
        KleinAffineOrbitQuotient.deckAct g p = q := by
  constructor
  · intro h
    rcases p with ⟨u, v⟩
    rcases q with ⟨x, y⟩
    have horbit := (KleinBottleOrbitQuotient.quotientMap_eq_iff
      (coverToTorus (affineToBrillouinCover (u, v)))
      (coverToTorus (affineToBrillouinCover (x, y)))).mp h
    rcases horbit with hid | hglide
    · have hfirst :
          (Real.pi * y : MomentumCircle) = (Real.pi * v : MomentumCircle) := by
        simpa [affineToBrillouinCover, coverToTorus] using
          congrArg Prod.fst hid
      have hsecond :
          ((2 * Real.pi) * x : MomentumCircle) =
            ((2 * Real.pi) * u : MomentumCircle) := by
        simpa [affineToBrillouinCover, coverToTorus] using
          congrArg Prod.snd hid
      obtain ⟨n, hn⟩ := circle_eq_iff_period.mp hfirst
      obtain ⟨m, hm⟩ := circle_eq_iff_period.mp hsecond
      have hn' : (n : ℝ) * (2 * Real.pi) = Real.pi * y - Real.pi * v := by
        simpa only [zsmul_eq_mul] using hn
      have hm' : (m : ℝ) * (2 * Real.pi) =
          (2 * Real.pi) * x - (2 * Real.pi) * u := by
        simpa only [zsmul_eq_mul] using hm
      have hy : y = v + 2 * (n : ℝ) := by
        apply mul_left_cancel₀ Real.pi_ne_zero
        calc
          Real.pi * y = (n : ℝ) * (2 * Real.pi) + Real.pi * v := by
            rw [hn']
            ring
          _ = Real.pi * (v + 2 * (n : ℝ)) := by ring
      have hx : x = u + (m : ℝ) := by
        apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
          Real.pi_ne_zero)
        calc
          (2 * Real.pi) * x = (m : ℝ) * (2 * Real.pi) +
              (2 * Real.pi) * u := by rw [hm']; ring
          _ = (2 * Real.pi) * (u + (m : ℝ)) := by ring
      have hsign : signR (2 * n) = 1 := by
        have heven : (2 * n) % 2 = 0 := by omega
        simp [signR, signZ, heven]
      refine ⟨⟨m, 2 * n⟩, ?_⟩
      change (signR (2 * n) * u + (m : ℝ),
        v + ((2 * n : ℤ) : ℝ)) = (x, y)
      rw [hsign]
      apply Prod.ext
      · simpa using hx.symm
      · rw [show ((2 * n : ℤ) : ℝ) = 2 * (n : ℝ) by norm_num]
        exact hy.symm
    · have hfirst :
          (Real.pi * y : MomentumCircle) =
            ((Real.pi * v + Real.pi : ℝ) : MomentumCircle) := by
        simpa [affineToBrillouinCover, coverToTorus, torusGlide,
          AddCircle.coe_add] using congrArg Prod.fst hglide
      have hsecond :
          ((2 * Real.pi) * x : MomentumCircle) =
            (-(2 * Real.pi * u) : MomentumCircle) := by
        simpa [affineToBrillouinCover, coverToTorus, torusGlide] using
          congrArg Prod.snd hglide
      obtain ⟨n, hn⟩ := circle_eq_iff_period.mp hfirst
      obtain ⟨m, hm⟩ := circle_eq_iff_period.mp hsecond
      have hn' : (n : ℝ) * (2 * Real.pi) =
          Real.pi * y - (Real.pi * v + Real.pi) := by
        simpa only [zsmul_eq_mul] using hn
      have hm' : (m : ℝ) * (2 * Real.pi) =
          (2 * Real.pi) * x - (-(2 * Real.pi * u)) := by
        simpa only [zsmul_eq_mul] using hm
      have hy : y = v + 1 + 2 * (n : ℝ) := by
        apply mul_left_cancel₀ Real.pi_ne_zero
        calc
          Real.pi * y = (n : ℝ) * (2 * Real.pi) +
              (Real.pi * v + Real.pi) := by rw [hn']; ring
          _ = Real.pi * (v + 1 + 2 * (n : ℝ)) := by ring
      have hx : x = -u + (m : ℝ) := by
        apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
          Real.pi_ne_zero)
        calc
          (2 * Real.pi) * x = (m : ℝ) * (2 * Real.pi) -
              (2 * Real.pi) * u := by rw [hm']; ring
          _ = (2 * Real.pi) * (-u + (m : ℝ)) := by ring
      have hsign : signR (2 * n + 1) = -1 := by
        have hodd : (2 * n + 1) % 2 = 1 := by omega
        simp [signR, signZ, hodd]
      refine ⟨⟨m, 2 * n + 1⟩, ?_⟩
      change (signR (2 * n + 1) * u + (m : ℝ),
        v + ((2 * n + 1 : ℤ) : ℝ)) = (x, y)
      rw [hsign]
      apply Prod.ext
      · simpa using hx.symm
      · rw [show ((2 * n + 1 : ℤ) : ℝ) = 2 * (n : ℝ) + 1 by norm_num]
        nlinarith [hy]
  · rintro ⟨g, hg⟩
    rw [← hg]
    exact (orbitProjection_deckAct g p).symm

/-- The coordinate comparison descends to a map from the affine orbit
quotient to the Brillouin orbit quotient. -/
noncomputable def affineQuotientToBrillouinQuotient :
    KleinAffineOrbitQuotient.KleinAffineQuotient →
      KleinBottleOrbitQuotient.KleinBrillouinQuotient :=
  Quotient.lift
    (fun p => KleinBottleOrbitQuotient.quotientMap
      (coverToTorus (affineToBrillouinCover p)))
    (by
      intro p q hpq
      rcases hpq with ⟨g, hg⟩
      rw [← hg]
      exact (orbitProjection_deckAct g p).symm)

/-- The map between orbit quotients is continuous for their quotient
topologies. -/
theorem affineQuotientToBrillouinQuotient_continuous :
    Continuous affineQuotientToBrillouinQuotient := by
  exact continuous_quot_lift
    (by
      intro p q hpq
      rcases hpq with ⟨g, hg⟩
      rw [← hg]
      exact (orbitProjection_deckAct g p).symm)
    (KleinBottleOrbitQuotient.quotientMap_continuous.comp <| by
      apply Continuous.prodMk
      · exact (AddCircle.continuous_mk' (2 * Real.pi)).comp
          (continuous_const.mul continuous_snd)
      · exact (AddCircle.continuous_mk' (2 * Real.pi)).comp
          (continuous_const.mul continuous_fst))

/-- The descended map is injective because its fibers are exactly the affine
deck orbits. -/
theorem affineQuotientToBrillouinQuotient_injective :
    Function.Injective affineQuotientToBrillouinQuotient := by
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro p q hpq
  apply Quotient.sound
  exact (quotientMap_affineToBrillouinCover_eq_iff_deckOrbit p q).mp hpq

/-- Every point of the Brillouin orbit quotient has an affine-quotient
preimage.  Surjectivity follows by lifting each circle coordinate to the
cover and applying the inverse coordinate change. -/
theorem affineQuotientToBrillouinQuotient_surjective :
    Function.Surjective affineQuotientToBrillouinQuotient := by
  intro q
  refine Quotient.inductionOn q ?_
  intro k
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective k.1
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective k.2
  refine ⟨KleinAffineOrbitQuotient.quotientMap
    (brillouinToAffineCover (x, y)), ?_⟩
  change KleinBottleOrbitQuotient.quotientMap
      (coverToTorus (affineToBrillouinCover
        (brillouinToAffineCover (x, y)))) =
    KleinBottleOrbitQuotient.quotientMap k
  have hk : k = ((x : MomentumCircle), (y : MomentumCircle)) :=
    Prod.ext hx.symm hy.symm
  have hcoords : affineToBrillouinCover (brillouinToAffineCover (x, y)) =
      (x, y) := by
    apply Prod.ext <;>
      simp [affineToBrillouinCover, brillouinToAffineCover] <;> field_simp
  rw [hcoords, hk]
  rfl

/-- The descended map is a bijection of the two quotient carriers. -/
theorem affineQuotientToBrillouinQuotient_bijective :
    Function.Bijective affineQuotientToBrillouinQuotient :=
  ⟨affineQuotientToBrillouinQuotient_injective,
    affineQuotientToBrillouinQuotient_surjective⟩

end InfoGeometry.Topology.KleinAffineBrillouinConjugacy
