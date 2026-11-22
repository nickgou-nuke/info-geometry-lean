/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Canonical.KreinProjectorLattice
import InfoGeometry.Clifford.SplitQ11PhaseFlip

/-!
# Finite operator Boolean algebra

The Boolean algebra of a finite family of commuting split-Clifford sectors.
`KreinSector` is the one-generator Boolean algebra of the `Cl(1,1)` projectors;
a function `Fin P → KreinSector` is the P-generator Boolean algebra, with
operations taken pointwise. Its embedding into `Fin P → CliffordAlgebra splitQ11`
realizes meet as multiplication, complement as `1 -`, and every generator as an
idempotent.
-/
namespace InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra

open InfoGeometry.Clifford.SplitQ11PhaseFlip
open InfoGeometry.Clifford.SplitQ11Projectors
open InfoGeometry.Canonical.KreinProjectorLattice

/-- The P-generator sector algebra. -/
abbrev Sector (P : ℕ) := Fin P → KreinSector

/-- The pointwise operator carrier. -/
abbrev Ops (P : ℕ) := Fin P → Alg

/-- The operator realization of a sector family. -/
noncomputable def toOps {P : ℕ} (s : Sector P) : Ops P :=
  fun i => KreinSector.toAlg (s i)

@[simp] theorem toOps_apply {P : ℕ} (s : Sector P) (i : Fin P) :
    toOps s i = KreinSector.toAlg (s i) := rfl

theorem toOps_idempotent {P : ℕ} (s : Sector P) (i : Fin P) :
    IsIdempotentElem (toOps s i) := by
  exact KreinSector.toAlg_idempotent (s i)

theorem toOps_inf_eq_mul {P : ℕ} (s t : Sector P) :
    toOps (s ⊓ t) = toOps s * toOps t := by
  funext i
  exact KreinSector.toAlg_inf_eq_mul (s i) (t i)

theorem toOps_sup_eq_add_sub_mul {P : ℕ} (s t : Sector P) :
    toOps (s ⊔ t) = toOps s + toOps t - toOps s * toOps t := by
  funext i
  exact KreinSector.toAlg_sup_eq_add_sub_mul (s i) (t i)

theorem toOps_compl_eq_one_sub {P : ℕ} (s : Sector P) :
    toOps sᶜ = 1 - toOps s := by
  funext i
  exact KreinSector.toAlg_compl_eq_one_sub (s i)

/-- Permutation action on a sector family: the coordinate permutation of a Boolean product. -/
instance instPermAction (P : ℕ) : MulAction (Equiv.Perm (Fin P)) (Sector P) where
  smul σ s := fun i => s (σ.symm i)
  one_smul s := by
    funext i
    change s ((1 : Equiv.Perm (Fin P)).symm i) = s i
    rfl
  mul_smul σ τ s := by
    funext i
    change s ((σ * τ).symm i) = s (τ.symm (σ.symm i))
    rfl

theorem perm_meet (P : ℕ) (σ : Equiv.Perm (Fin P)) (s t : Sector P) :
    σ • (s ⊓ t) = (σ • s) ⊓ (σ • t) := by
  rfl

theorem perm_sup (P : ℕ) (σ : Equiv.Perm (Fin P)) (s t : Sector P) :
    σ • (s ⊔ t) = (σ • s) ⊔ (σ • t) := by
  rfl

theorem perm_compl (P : ℕ) (σ : Equiv.Perm (Fin P)) (s : Sector P) :
    σ • sᶜ = (σ • s)ᶜ := by
  rfl

/-- Coordinatewise complement (XOR) action. It is an involution and preserves
    complement, but it is order-reversing: it is not a Boolean automorphism. -/
def flip {P : ℕ} (ε : Fin P → Bool) (s : Sector P) : Sector P :=
  fun i => if ε i then (s i)ᶜ else s i

theorem flip_zero {P : ℕ} (s : Sector P) : flip (0 : Fin P → Bool) s = s := by
  funext i
  simp [flip]

theorem flip_self {P : ℕ} (ε : Fin P → Bool) (s : Sector P) : flip ε (flip ε s) = s := by
  funext i
  by_cases h : ε i = true <;> simp [flip, h]

/-- Clifford sign flip on one factor: `ω ↦ -ω` exchanges the two atoms and
    fixes the bottom and top elements. Unlike complement this is order-preserving. -/
def signFlip : KreinSector → KreinSector
  | KreinSector.bot => KreinSector.bot
  | KreinSector.minus => KreinSector.plus
  | KreinSector.plus => KreinSector.minus
  | KreinSector.top => KreinSector.top

theorem signFlip_involutive : Function.Involutive signFlip := by
  intro a
  cases a <;> rfl

theorem signFlip_inf (a b : KreinSector) : signFlip (a ⊓ b) = signFlip a ⊓ signFlip b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem signFlip_sup (a b : KreinSector) : signFlip (a ⊔ b) = signFlip a ⊔ signFlip b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem signFlip_compl (a : KreinSector) : signFlip aᶜ = (signFlip a)ᶜ := by
  cases a <;> rfl

/-- Coordinatewise sign flip: the `ℤ/2` part of the hyperoctahedral action. -/
def signFlipSector {P : ℕ} (ε : Fin P → Bool) (s : Sector P) : Sector P :=
  fun i => if ε i = true then signFlip (s i) else s i

theorem signFlipSector_involutive {P : ℕ} (ε : Fin P → Bool) :
    Function.Involutive (signFlipSector ε) := by
  intro s
  funext i
  by_cases h : ε i = true
  · simp [signFlipSector, h]
    exact signFlip_involutive (s i)
  · simp [signFlipSector, h]

theorem signFlipSector_inf {P : ℕ} (ε : Fin P → Bool) (s t : Sector P) :
    signFlipSector ε (s ⊓ t) = signFlipSector ε s ⊓ signFlipSector ε t := by
  funext i
  by_cases h : ε i = true
  · simp [signFlipSector, h, signFlip_inf]
  · simp [signFlipSector, h]

theorem signFlipSector_sup {P : ℕ} (ε : Fin P → Bool) (s t : Sector P) :
    signFlipSector ε (s ⊔ t) = signFlipSector ε s ⊔ signFlipSector ε t := by
  funext i
  by_cases h : ε i = true
  · simp [signFlipSector, h, signFlip_sup]
  · simp [signFlipSector, h]

theorem signFlipSector_compl {P : ℕ} (ε : Fin P → Bool) (s : Sector P) :
    signFlipSector ε sᶜ = (signFlipSector ε s)ᶜ := by
  funext i
  by_cases h : ε i = true
  · simp [signFlipSector, h, signFlip_compl]
  · simp [signFlipSector, h]

/-- The signed-permutation group is a group of Boolean automorphisms of the sector
    algebra: sign flips are the wreath-product `S₂` factors and permutations are `S_P`. -/
abbrev FlipGroup (P : ℕ) := Multiplicative (Fin P → Bool)

def flipPermAut (P : ℕ) (σ : Equiv.Perm (Fin P)) : MulAut (FlipGroup P) where
  toFun ε := Multiplicative.ofAdd (fun i => Multiplicative.toAdd ε (σ.symm i))
  invFun ε := Multiplicative.ofAdd (fun i => Multiplicative.toAdd ε (σ i))
  left_inv ε := by ext i; simp
  right_inv ε := by ext i; simp
  map_mul' a b := by ext i; simp

def flipPermHom (P : ℕ) : Equiv.Perm (Fin P) →* MulAut (FlipGroup P) where
  toFun := flipPermAut P
  map_one' := by ext ε i; rfl
  map_mul' σ τ := by ext ε i; rfl

abbrev SignedPerm (P : ℕ) := FlipGroup P ⋊[flipPermHom P] Equiv.Perm (Fin P)

/-- Permutation action evaluated at a coordinate. -/
theorem perm_apply (P : ℕ) (σ : Equiv.Perm (Fin P)) (s : Sector P) (i : Fin P) :
    (σ • s) i = s (σ.symm i) := rfl

/-- The hyperoctahedral group acts on the P-generator Boolean algebra.
    The action law is proved by the four sign cases; the two cases with an
    odd number of flips close by `signFlip_involutive`. -/
instance instSignedSectorAction (P : ℕ) : MulAction (SignedPerm P) (Sector P) where
  smul g s := signFlipSector (Multiplicative.toAdd g.left) (g.right • s)
  one_smul s := by
    funext i
    change signFlipSector (Multiplicative.toAdd (1 : SignedPerm P).left)
      ((1 : SignedPerm P).right • s) i = s i
    simp [signFlipSector]
  mul_smul g h s := by
    funext i
    change signFlipSector (Multiplicative.toAdd (g * h).left) ((g * h).right • s) i =
      signFlipSector (Multiplicative.toAdd g.left)
        (g.right • signFlipSector (Multiplicative.toAdd h.left) (h.right • s)) i
    rw [SemidirectProduct.mul_right]
    rw [mul_smul]
    cases hbg : Multiplicative.toAdd g.left i <;>
      cases hbh : Multiplicative.toAdd h.left (g.right.symm i) <;>
      simp [signFlipSector, SemidirectProduct.mul_left, flipPermAut, flipPermHom,
        perm_apply, hbg, hbh]
    all_goals
      try rw [signFlip_involutive]
      try simp
      first
      | intro hb; cases hb
      | skip

theorem signed_inf (P : ℕ) (g : SignedPerm P) (s t : Sector P) :
    g • (s ⊓ t) = (g • s) ⊓ (g • t) := by
  change signFlipSector (Multiplicative.toAdd g.left) (g.right • (s ⊓ t)) =
    signFlipSector (Multiplicative.toAdd g.left) (g.right • s) ⊓
      signFlipSector (Multiplicative.toAdd g.left) (g.right • t)
  rw [perm_meet]
  exact signFlipSector_inf _ _ _

theorem signed_sup (P : ℕ) (g : SignedPerm P) (s t : Sector P) :
    g • (s ⊔ t) = (g • s) ⊔ (g • t) := by
  change signFlipSector (Multiplicative.toAdd g.left) (g.right • (s ⊔ t)) =
    signFlipSector (Multiplicative.toAdd g.left) (g.right • s) ⊔
      signFlipSector (Multiplicative.toAdd g.left) (g.right • t)
  rw [perm_sup]
  exact signFlipSector_sup _ _ _

theorem signed_compl (P : ℕ) (g : SignedPerm P) (s : Sector P) :
    g • sᶜ = (g • s)ᶜ := by
  change signFlipSector (Multiplicative.toAdd g.left) (g.right • sᶜ) =
    (signFlipSector (Multiplicative.toAdd g.left) (g.right • s))ᶜ
  rw [perm_compl]
  exact signFlipSector_compl _ _

end InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra
