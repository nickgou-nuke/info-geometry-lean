/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinQuotientDeckInvariants
import InfoGeometry.Topology.KleinBottleOrbitQuotient
import Mathlib

/-!
# Representations of the existing affine Klein deck group

The affine glide is not an involution on the covering plane. The normal form
and multiplication are reused, and the Brillouin cover convention is related
by an explicit scale-and-swap map. No fundamental-group classification is assumed.
-/
noncomputable section
namespace InfoGeometry.Topology.KleinDeckRepresentation
open KleinQuotientDeckInvariants

scoped instance deckGroupStructure : Group KleinDeckGroup where
  mul := KleinDeckGroup.mul
  one := KleinDeckGroup.one
  inv := KleinDeckGroup.inv
  mul_assoc := KleinDeckGroup.mul_assoc
  one_mul := KleinDeckGroup.one_mul
  mul_one := KleinDeckGroup.mul_one
  inv_mul_cancel := KleinDeckGroup.mul_left_inv

/-- Actual action by invertible maps of the already-owned covering plane. -/
def planeAction (g : KleinDeckGroup) : Equiv.Perm PlanePoint where
  toFun := deckAction g
  invFun := fun p => deckAction (KleinDeckGroup.inv g) p
  left_inv p := by
    change deckAction (KleinDeckGroup.inv g) (deckAction g p) = p
    rw [← deckAction_mul, KleinDeckGroup.mul_left_inv, deckAction_one]
  right_inv p := by
    change deckAction g (deckAction (KleinDeckGroup.inv g) p) = p
    rw [← deckAction_mul]
    have hri : KleinDeckGroup.mul g (KleinDeckGroup.inv g) = KleinDeckGroup.one := by
      rcases g with ⟨m, n⟩
      simp only [KleinDeckGroup.mul, KleinDeckGroup.inv, KleinDeckGroup.one,
        KleinDeckGroup.mk.injEq]
      constructor
      · have hs : signZ n * signZ n = 1 := by
          have h : signZ n = 1 ∨ signZ n = -1 := by simp [signZ]; omega
          rcases h with h | h <;> simp [h]
        calc
          m + signZ n * (-signZ n * m) = m - (signZ n * signZ n) * m := by ring
          _ = 0 := by rw [hs]; ring
      · omega
    rw [hri, deckAction_one]

def planeRepresentation : KleinDeckGroup →* Equiv.Perm PlanePoint where
  toFun := planeAction
  map_one' := by
    apply Equiv.ext
    intro p
    exact deckAction_one p
  map_mul' g h := by
    apply Equiv.ext
    intro p
    exact deckAction_mul g h p

theorem planeRepresentation_faithful : Function.Injective planeRepresentation := by
  intro g h he
  have hx := congrArg (fun e : Equiv.Perm PlanePoint => (e (0,0)).1) he
  have hy := congrArg (fun e : Equiv.Perm PlanePoint => (e (0,0)).2) he
  have hm : g.m=h.m := by
    exact_mod_cast (show (g.m : ℝ) = (h.m : ℝ) by
      simpa [planeRepresentation, planeAction, deckAction] using hx)
  have hn : g.n=h.n := by
    exact_mod_cast (show (g.n : ℝ) = (h.n : ℝ) by
      simpa [planeRepresentation, planeAction, deckAction] using hy)
  cases g; cases h; simp_all

/-- The two existing cover conventions are related, not conflated. -/
def scaleSwap (p : PlanePoint) : KleinBrillouinBase.Cover :=
  (Real.pi*p.2, (2*Real.pi)*p.1)

theorem scaleSwap_glide (p : PlanePoint) :
    scaleSwap (deckB p)=KleinBrillouinBase.glide (scaleSwap p) := by
  ext <;> simp [scaleSwap,deckB,KleinBrillouinBase.glide] <;> ring

theorem scaleSwap_translation (p : PlanePoint) :
    scaleSwap (deckA p)=KleinBrillouinBase.ty (scaleSwap p) := by
  ext <;> simp [scaleSwap,deckA,KleinBrillouinBase.ty] <;> ring

def kleinPoint (p : PlanePoint) : KleinBottleOrbitQuotient.KleinBrillouinQuotient :=
  KleinBottleOrbitQuotient.quotientMap (KleinBrillouinBase.coverToTorus (scaleSwap p))

@[simp] theorem kleinPoint_glide (p : PlanePoint) : kleinPoint (deckB p)=kleinPoint p := by
  unfold kleinPoint
  rw [scaleSwap_glide, KleinBrillouinBase.coverToTorus_glide,
    KleinBottleOrbitQuotient.quotientMap_glide]

@[simp] theorem kleinPoint_translation (p : PlanePoint) : kleinPoint (deckA p)=kleinPoint p := by
  unfold kleinPoint
  rw [scaleSwap_translation, KleinBrillouinBase.coverToTorus_ty]

section Representation
variable {H : Type*} [Group H]

private theorem involution_inverse (A : H) (hA : A*A=1) : A⁻¹=A := by
  calc A⁻¹ = A⁻¹*1 := (mul_one _).symm
    _ = A⁻¹*(A*A) := by rw [hA]
    _ = A := by simp [← mul_assoc]

/-- The sign action on the horizontal exponent disappears precisely for an involution. -/
theorem involution_zpow_sign (A : H) (hA : A*A=1) (n m : ℤ) :
    A ^ (signZ n * m)=A^m := by
  have hi := involution_inverse A hA
  unfold signZ
  split_ifs
  · simp
  · simp only [neg_one_mul, zpow_neg, ← inv_zpow, hi]

/-- A flat lift of the semidirect deck group, allowing either horizontal sign. -/
def flatRepresentation (A R : H) (hA : A*A=1) (hAR : Commute A R) :
    KleinDeckGroup →* H where
  toFun g := A^g.m * R^g.n
  map_one' := by
    change A ^ (0 : ℤ) * R ^ (0 : ℤ) = 1
    simp
  map_mul' g h := by
    change A^(g.m+signZ g.n*h.m)*R^(g.n+h.n)=(A^g.m*R^g.n)*(A^h.m*R^h.n)
    rw [zpow_add, zpow_add, involution_zpow_sign A hA]
    calc
      (A^g.m*A^h.m)*(R^g.n*R^h.n) = A^g.m*(A^h.m*R^g.n)*R^h.n := by group
      _ = A^g.m*(R^g.n*A^h.m)*R^h.n := by rw [(hAR.zpow_zpow h.m g.n).eq]
      _ = (A^g.m*R^g.n)*(A^h.m*R^h.n) := by group

@[simp] theorem flatRepresentation_a (A R : H) (hA : A*A=1) (hAR : Commute A R) :
    flatRepresentation A R hA hAR KleinDeckGroup.a=A := by
  change A ^ (1 : ℤ) * R ^ (0 : ℤ) = A
  simp

@[simp] theorem flatRepresentation_b (A R : H) (hA : A*A=1) (hAR : Commute A R) :
    flatRepresentation A R hA hAR KleinDeckGroup.b=R := by
  change A ^ (0 : ℤ) * R ^ (1 : ℤ) = R
  simp

theorem flatRepresentation_double_glide (A R : H) (hA : A*A=1) (hAR : Commute A R) :
    flatRepresentation A R hA hAR (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b)=R*R := by
  change flatRepresentation A R hA hAR (KleinDeckGroup.b*KleinDeckGroup.b)=R*R
  rw [map_mul,flatRepresentation_b]

end Representation
end InfoGeometry.Topology.KleinDeckRepresentation
