/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SandwichLocalization
import InfoGeometry.Algebra.CentralPowerLocalizationColimit
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.Hom

/-!
# Localized centralizer actions on the two-sided additive localization

The scalar ring is the existing native Ore localization of the actual
centralizer of `s`. The ambient numerators remain in the original ring `B`.
Left and right scalar actions are native module structures, with commuting
actions and explicit representative formulas. No ambient multiplication is
postulated on the additive localization.
-/

namespace InfoGeometry.Algebra.SandwichLocalization

variable {B : Type*} [Ring B]

/-- The actual centralizer of the denominator, as a native subring. -/
abbrev Centralizer (s : B) := Subring.centralizer ({s} : Set B)

theorem centralizer_commute (s : B) (u : Centralizer s) : Commute s (u : B) :=
  u.property s (Set.mem_singleton s)

/-- The denominator considered inside its own centralizer. -/
def denominator (s : B) : Centralizer s :=
  ⟨s, by intro x hx; rcases Set.mem_singleton_iff.mp hx with rfl; rfl⟩

@[simp] theorem coe_denominator (s : B) : ((denominator s : Centralizer s) : B) = s := rfl

instance denominatorCentral (s : B) :
    Fact (∀ u : Centralizer s, Commute (denominator s) u) where
  out u := Subtype.ext (centralizer_commute s u).eq

/-- Only the scalar centralizer is localized as a ring. -/
abbrev Scalars (s : B) := CentralPowerLocalization.Away (denominator s)

private theorem sandwich_reorder (s u v x : B) (hu : Commute s u) (hv : Commute s v)
    (a b : ℕ) :
    u * (s ^ a * x * s ^ b) * v = s ^ a * (u * x * v) * s ^ b := by
  calc
    _ = (u * s ^ a) * x * (s ^ b * v) := by noncomm_ring
    _ = (s ^ a * u) * x * (v * s ^ b) := by
      rw [← (hu.pow_left a).eq, (hv.pow_left b).eq]
    _ = _ := by noncomm_ring

/-- An ordered numerator sandwich with independent denominator shifts. -/
noncomputable def sandwich (s : B) (a b : ℕ) (u v : B)
    (hu : Commute s u) (hv : Commute s v) : AddMonoid.End (Space s) :=
  additiveDesc s (fun k l =>
    { toFun := fun x => repr s (k + a) (u * x * v) (l + b)
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [mul_add, add_mul, repr_add_same] }) (by
    intro k l c d x
    change repr s (k + c + a) (u * (s ^ c * x * s ^ d) * v) (l + d + b) =
      repr s (k + a) (u * x * v) (l + b)
    rw [sandwich_reorder s u v x hu hv]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      repr_bond s (k + a) (l + b) c d (u * x * v))

@[simp] theorem sandwich_repr (s : B) (a b : ℕ) (u v : B)
    (hu : Commute s u) (hv : Commute s v) (k l : ℕ) (x : B) :
    sandwich s a b u v hu hv (repr s k x l) =
      repr s (k + a) (u * x * v) (l + b) := rfl

/-- Composition retains the opposite ordering of the right factors. -/
theorem sandwich_comp (s : B) (a b c d : ℕ) (u v w z : B)
    (hu : Commute s u) (hv : Commute s v) (hw : Commute s w) (hz : Commute s z) :
    (sandwich s a b u v hu hv).comp (sandwich s c d w z hw hz) =
      sandwich s (c + a) (d + b) (u * w) (z * v) (hu.mul_right hw) (hz.mul_right hv) := by
  ext q
  obtain ⟨k, x, l, rfl⟩ := exists_repr s q
  change sandwich s a b u v hu hv
      (sandwich s c d w z hw hz (repr s k x l)) =
    sandwich s (c + a) (d + b) (u * w) (z * v)
      (hu.mul_right hw) (hz.mul_right hv) (repr s k x l)
  simp only [sandwich_repr, Nat.add_assoc, mul_assoc]

private noncomputable def leftStage (s : B) (a : ℕ) :
    Centralizer s →+ AddMonoid.End (Space s) where
  toFun u := sandwich s a 0 (u : B) 1 (centralizer_commute s u) (Commute.one_right s)
  map_zero' := by
    ext q
    obtain ⟨k, x, l, rfl⟩ := exists_repr s q
    simp only [sandwich_repr, Subring.coe_zero, zero_mul, mul_one, repr_zero,
      AddMonoid.End.zero_apply]
  map_add' u v := by
    ext q
    obtain ⟨k, x, l, rfl⟩ := exists_repr s q
    change repr s (k + a) (((u : B) + (v : B)) * x * 1) (l + 0) =
      repr s (k + a) ((u : B) * x * 1) (l + 0) +
        repr s (k + a) ((v : B) * x * 1) (l + 0)
    simp only [add_mul, mul_one, repr_add_same]

private theorem leftStage_bond (s : B) (a n : ℕ) (u : Centralizer s) :
    leftStage s (a + n) (denominator s ^ n * u) = leftStage s a u := by
  ext q
  obtain ⟨k, x, l, rfl⟩ := exists_repr s q
  change repr s (k + (a + n)) (((s ^ n * (u : B)) * x) * 1) (l + 0) =
    repr s (k + a) ((u : B) * x * 1) (l + 0)
  simpa only [Nat.add_assoc, Nat.add_zero, pow_zero, mul_one, mul_assoc] using
    repr_bond s (k + a) l n 0 ((u : B) * x)

private noncomputable def leftActionAdd (s : B) : Scalars s →+ AddMonoid.End (Space s) :=
  CentralPowerLocalization.additiveDesc (denominator s) (leftStage s) (leftStage_bond s)

private theorem leftActionAdd_repr (s : B) (a : ℕ) (u : Centralizer s) :
    leftActionAdd s (CentralPowerLocalization.repr (denominator s) a u) =
      sandwich s a 0 (u : B) 1 (centralizer_commute s u) (Commute.one_right s) :=
  CentralPowerLocalization.additiveDesc_repr (denominator s) (leftStage s) (leftStage_bond s) a u

/-- The localized left action is a constructed ring homomorphism to additive endomorphisms. -/
noncomputable def leftAction (s : B) : Scalars s →+* AddMonoid.End (Space s) where
  toFun q := leftActionAdd s q
  map_zero' := (leftActionAdd s).map_zero
  map_add' q r := (leftActionAdd s).map_add q r
  map_one' := by
    have hone : (1 : Scalars s) = CentralPowerLocalization.repr (denominator s) 0 1 := by
      simp only [CentralPowerLocalization.repr_zero, map_one]
    rw [hone, leftActionAdd_repr]
    ext q
    obtain ⟨k, x, l, rfl⟩ := exists_repr s q
    simp only [sandwich_repr, Subring.coe_one, one_mul, mul_one, Nat.add_zero,
      AddMonoid.End.one_apply]
  map_mul' q r := by
    obtain ⟨a, u, rfl⟩ := CentralPowerLocalization.exists_repr (denominator s) q
    obtain ⟨b, v, rfl⟩ := CentralPowerLocalization.exists_repr (denominator s) r
    rw [CentralPowerLocalization.repr_mul, leftActionAdd_repr, leftActionAdd_repr,
      leftActionAdd_repr]
    ext z
    obtain ⟨k, x, l, rfl⟩ := exists_repr s z
    simp only [AddMonoid.End.coe_mul, Function.comp_apply, sandwich_repr, Subring.coe_mul,
      mul_one, Nat.add_zero, mul_assoc]
    congr 1
    omega

/-- The native left module over the localized, possibly noncommutative scalar ring. -/
noncomputable instance leftModule (s : B) : Module (Scalars s) (Space s) :=
  Module.compHom (Space s) (leftAction s)

@[simp] theorem left_smul_repr (s : B) (a k l : ℕ) (u : Centralizer s) (x : B) :
    CentralPowerLocalization.repr (denominator s) a u • repr s k x l =
      repr s (k + a) ((u : B) * x) l := by
  change leftActionAdd s (CentralPowerLocalization.repr (denominator s) a u)
    (repr s k x l) = _
  rw [leftActionAdd_repr, sandwich_repr, Nat.add_zero, mul_one]

private noncomputable def rightStage (s : B) (a : ℕ) :
    Centralizer s →+ AddMonoid.End (Space s) where
  toFun u := sandwich s 0 a 1 (u : B) (Commute.one_right s) (centralizer_commute s u)
  map_zero' := by
    ext q
    obtain ⟨k, x, l, rfl⟩ := exists_repr s q
    simp only [sandwich_repr, Subring.coe_zero, mul_zero, repr_zero, AddMonoid.End.zero_apply]
  map_add' u v := by
    ext q
    obtain ⟨k, x, l, rfl⟩ := exists_repr s q
    change repr s (k + 0) (1 * x * ((u : B) + (v : B))) (l + a) =
      repr s (k + 0) (1 * x * (u : B)) (l + a) +
        repr s (k + 0) (1 * x * (v : B)) (l + a)
    simp only [mul_add, repr_add_same]

private theorem rightStage_bond (s : B) (a n : ℕ) (u : Centralizer s) :
    rightStage s (a + n) (denominator s ^ n * u) = rightStage s a u := by
  ext q
  obtain ⟨k, x, l, rfl⟩ := exists_repr s q
  change repr s (k + 0) (1 * x * (s ^ n * (u : B))) (l + (a + n)) =
    repr s (k + 0) (1 * x * (u : B)) (l + a)
  rw [(centralizer_commute s u).pow_left n |>.eq]
  simpa only [Nat.add_assoc, Nat.add_zero, pow_zero, one_mul, mul_assoc] using
    repr_bond s k (l + a) 0 n (x * (u : B))

private noncomputable def rightActionAdd (s : B) : Scalars s →+ AddMonoid.End (Space s) :=
  CentralPowerLocalization.additiveDesc (denominator s) (rightStage s) (rightStage_bond s)

private theorem rightActionAdd_repr (s : B) (a : ℕ) (u : Centralizer s) :
    rightActionAdd s (CentralPowerLocalization.repr (denominator s) a u) =
      sandwich s 0 a 1 (u : B) (Commute.one_right s) (centralizer_commute s u) :=
  CentralPowerLocalization.additiveDesc_repr (denominator s) (rightStage s) (rightStage_bond s) a u

/-- Right multiplication is a ring action of the opposite localized scalar ring. -/
noncomputable def rightAction (s : B) : (Scalars s)ᵐᵒᵖ →+* AddMonoid.End (Space s) where
  toFun q := rightActionAdd s q.unop
  map_zero' := (rightActionAdd s).map_zero
  map_add' q r := (rightActionAdd s).map_add q.unop r.unop
  map_one' := by
    change rightActionAdd s 1 = 1
    have hone : (1 : Scalars s) = CentralPowerLocalization.repr (denominator s) 0 1 := by
      simp only [CentralPowerLocalization.repr_zero, map_one]
    rw [hone, rightActionAdd_repr]
    ext q
    obtain ⟨k, x, l, rfl⟩ := exists_repr s q
    simp only [sandwich_repr, Subring.coe_one, one_mul, mul_one, Nat.add_zero,
      AddMonoid.End.one_apply]
  map_mul' q r := by
    change rightActionAdd s (r.unop * q.unop) = rightActionAdd s q.unop * rightActionAdd s r.unop
    obtain ⟨a, u, hu⟩ := CentralPowerLocalization.exists_repr (denominator s) q.unop
    obtain ⟨b, v, hv⟩ := CentralPowerLocalization.exists_repr (denominator s) r.unop
    rw [← hu, ← hv, CentralPowerLocalization.repr_mul, rightActionAdd_repr,
      rightActionAdd_repr, rightActionAdd_repr]
    ext z
    obtain ⟨k, x, l, rfl⟩ := exists_repr s z
    simp only [AddMonoid.End.coe_mul, Function.comp_apply, sandwich_repr, Subring.coe_mul,
      one_mul, Nat.add_zero, mul_assoc, Nat.add_assoc]

/-- The native right module, expressed as a left module over the opposite ring. -/
noncomputable instance rightModule (s : B) : Module (Scalars s)ᵐᵒᵖ (Space s) :=
  Module.compHom (Space s) (rightAction s)

@[simp] theorem right_smul_repr (s : B) (a k l : ℕ) (u : Centralizer s) (x : B) :
    MulOpposite.op (CentralPowerLocalization.repr (denominator s) a u) • repr s k x l =
      repr s k (x * (u : B)) (l + a) := by
  change rightActionAdd s (CentralPowerLocalization.repr (denominator s) a u)
    (repr s k x l) = _
  rw [rightActionAdd_repr, sandwich_repr, Nat.add_zero, one_mul]

/-- Left and right scalar actions commute on every ambient numerator. -/
noncomputable instance scalarActionsCommute (s : B) :
    SMulCommClass (Scalars s) (Scalars s)ᵐᵒᵖ (Space s) where
  smul_comm q r z := by
    obtain ⟨a, u, rfl⟩ := CentralPowerLocalization.exists_repr (denominator s) q
    obtain ⟨b, v, hv⟩ := CentralPowerLocalization.exists_repr (denominator s) r.unop
    have hr : r = MulOpposite.op (CentralPowerLocalization.repr (denominator s) b v) := by
      exact congrArg MulOpposite.op hv.symm
    rw [hr]
    obtain ⟨k, x, l, rfl⟩ := exists_repr s z
    simp only [left_smul_repr, right_smul_repr, mul_assoc]

/-- Both scalar actions together have the submitted two-sided representative formula. -/
theorem bimodule_repr (s : B) (a b k l : ℕ) (u v : Centralizer s) (x : B) :
    CentralPowerLocalization.repr (denominator s) a u •
        (MulOpposite.op (CentralPowerLocalization.repr (denominator s) b v) • repr s k x l) =
      repr s (k + a) ((u : B) * x * (v : B)) (l + b) := by
  simp only [left_smul_repr, right_smul_repr, mul_assoc]

end InfoGeometry.Algebra.SandwichLocalization
