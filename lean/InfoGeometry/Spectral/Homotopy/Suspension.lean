import Mathlib
import InfoGeometry.Spectral.Spectrum.Basic

/-!
# Finite pointed readouts for the spectral homotopy port

This module keeps the old suspension/loop names available as finite pointed
readouts.  It does not claim a topological suspension-loop adjunction.
-/

noncomputable section

namespace InfoGeometry.Spectral.Homotopy.Suspension

open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge

set_option linter.dupNamespace false

/-- Minimal pointed carrier used by the finite spectral homotopy readouts. -/
abbrev PointedReadout := Pointed

abbrev PointedReadout.carrier (X : PointedReadout) : Type _ := X.X

abbrev PointedReadout.base (X : PointedReadout) : X.carrier := X.point

/-- Basepoint-preserving map between finite pointed readouts. -/
structure PointedMap (X Y : PointedReadout) where
  toFun : X.carrier → Y.carrier
  map_base : toFun X.base = Y.base

namespace PointedMap

instance (X Y : PointedReadout) : CoeFun (PointedMap X Y) (fun _ => X.carrier → Y.carrier) where
  coe f := f.toFun

/-- Identity pointed map. -/
def id (X : PointedReadout) : PointedMap X X where
  toFun := fun x => x
  map_base := rfl

/-- Composition of pointed maps. -/
def comp {X Y Z : PointedReadout} (g : PointedMap Y Z) (f : PointedMap X Y) :
    PointedMap X Z where
  toFun x := g (f x)
  map_base := by
    rw [f.map_base]
    exact g.map_base

@[simp]
theorem id_apply (X : PointedReadout) (x : X.carrier) :
    PointedMap.id X x = x :=
  rfl

@[simp]
theorem comp_apply {X Y Z : PointedReadout} (g : PointedMap Y Z) (f : PointedMap X Y)
    (x : X.carrier) :
    PointedMap.comp g f x = g (f x) :=
  rfl

theorem ext {X Y : PointedReadout} {f g : PointedMap X Y}
    (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          congr
          funext x
          exact h x

@[simp] theorem comp_id {X Y : PointedReadout} (f : PointedMap X Y) :
    comp (id Y) f = f := by
  apply ext
  intro x
  rfl

@[simp] theorem id_comp {X Y : PointedReadout} (f : PointedMap X Y) :
    comp f (id X) = f := by
  apply ext
  intro x
  rfl

theorem comp_assoc {W X Y Z : PointedReadout}
    (h : PointedMap Z W) (g : PointedMap Y Z) (f : PointedMap X Y) :
    comp h (comp g f) = comp (comp h g) f := by
  apply ext
  intro x
  rfl

end PointedMap

/-- Basepoint-preserving equivalence between finite pointed readouts. -/
structure PointedEquiv (X Y : PointedReadout) where
  toEquiv : X.carrier ≃ Y.carrier
  map_base : toEquiv X.base = Y.base

namespace PointedEquiv

instance (X Y : PointedReadout) : CoeFun (PointedEquiv X Y) (fun _ => X.carrier → Y.carrier) where
  coe e := e.toEquiv

/-- Identity pointed equivalence. -/
def refl (X : PointedReadout) : PointedEquiv X X where
  toEquiv := Equiv.refl X.carrier
  map_base := rfl

/-- Inverse pointed equivalence. -/
def symm {X Y : PointedReadout} (e : PointedEquiv X Y) : PointedEquiv Y X where
  toEquiv := e.toEquiv.symm
  map_base := by
    apply e.toEquiv.injective
    simp [e.map_base]

/-- Composition of pointed equivalences. -/
def comp {X Y Z : PointedReadout} (g : PointedEquiv Y Z) (f : PointedEquiv X Y) :
    PointedEquiv X Z where
  toEquiv := f.toEquiv.trans g.toEquiv
  map_base := by
    simp [f.map_base, g.map_base]

@[simp]
theorem refl_apply (X : PointedReadout) (x : X.carrier) :
    PointedEquiv.refl X x = x :=
  rfl

theorem ext {X Y : PointedReadout} {f g : PointedEquiv X Y}
    (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          congr
          apply Equiv.ext
          exact h

@[simp] theorem comp_refl {X Y : PointedReadout} (f : PointedEquiv X Y) :
    comp (refl Y) f = f := by
  apply ext
  intro x
  rfl

@[simp] theorem refl_comp {X Y : PointedReadout} (f : PointedEquiv X Y) :
    comp f (refl X) = f := by
  apply ext
  intro x
  rfl

@[simp] theorem comp_symm_self {X Y : PointedReadout} (f : PointedEquiv X Y) :
    comp f.symm f = refl X := by
  apply ext
  intro x
  exact f.toEquiv.left_inv x

@[simp] theorem comp_self_symm {X Y : PointedReadout} (f : PointedEquiv X Y) :
    comp f f.symm = refl Y := by
  apply ext
  intro y
  exact f.toEquiv.right_inv y

end PointedEquiv

/-- Finite readout standing in the old port for suspension bookkeeping. -/
abbrev Suspension (X : PointedReadout) : PointedReadout := X

/-- Finite readout standing in the old port for loop-space bookkeeping. -/
abbrev LoopSpace (X : PointedReadout) : PointedReadout := X

/-- Suspension functoriality for the finite readout. -/
def Suspension.map {X Y : PointedReadout} (f : PointedMap X Y) :
    PointedMap (Suspension X) (Suspension Y) :=
  f

/-- Loop functoriality for the finite readout. -/
def LoopSpace.map {X Y : PointedReadout} (f : PointedMap X Y) :
    PointedMap (LoopSpace X) (LoopSpace Y) :=
  f

@[simp]
theorem Suspension_map_apply {X Y : PointedReadout} (f : PointedMap X Y) (x : X.carrier) :
    Suspension.map f x = f x :=
  rfl

@[simp]
theorem LoopSpace_map_apply {X Y : PointedReadout} (f : PointedMap X Y) (x : X.carrier) :
    LoopSpace.map f x = f x :=
  rfl

/-- The finite suspension-loop unit readout is identity. -/
def SuspensionLoopUnit (X : PointedReadout) : PointedMap X (LoopSpace (Suspension X)) :=
  PointedMap.id X

/-- The finite suspension-loop counit readout is identity. -/
def SuspensionLoopCounit (X : PointedReadout) : PointedMap (Suspension (LoopSpace X)) X :=
  PointedMap.id X

/-- Iterate suspension bookkeeping. -/
def IteratedSuspension : ℕ → PointedReadout → PointedReadout
  | 0, X => X
  | n + 1, X => Suspension (IteratedSuspension n X)

/-- Iterate loop bookkeeping. -/
def IteratedLoopSpace : ℕ → PointedReadout → PointedReadout
  | 0, X => X
  | n + 1, X => LoopSpace (IteratedLoopSpace n X)

@[simp]
theorem IteratedSuspension_zero (X : PointedReadout) :
    IteratedSuspension 0 X = X :=
  rfl

@[simp]
theorem IteratedLoopSpace_zero (X : PointedReadout) :
    IteratedLoopSpace 0 X = X :=
  rfl

@[simp]
theorem IteratedSuspension_succ (n : ℕ) (X : PointedReadout) :
    IteratedSuspension (n + 1) X = Suspension (IteratedSuspension n X) :=
  rfl

@[simp]
theorem IteratedLoopSpace_succ (n : ℕ) (X : PointedReadout) :
    IteratedLoopSpace (n + 1) X = LoopSpace (IteratedLoopSpace n X) :=
  rfl

/-- Split-Clifford stage as a pointed finite readout, based at zero. -/
def SplitCliffordSuspension (n : ℕ) : PointedReadout where
  X := SplitClNNAlg n
  point := 0

/-- The split-Clifford one-step map as a pointed readout map. -/
def SplitCliffordSuspensionMap (n : ℕ) :
    PointedMap (SplitCliffordSuspension n) (SplitCliffordSuspension (n + 1)) where
  toFun := splitCliffordStep n
  map_base := by
    change splitCliffordStep n 0 = 0
    simpa using (map_zero (splitCliffordStep n))

@[simp]
theorem SplitCliffordSuspensionMap_apply (n : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordSuspensionMap n x = splitCliffordStep n x :=
  rfl

@[simp]
theorem SplitCliffordSuspension_base (n : ℕ) :
    (SplitCliffordSuspension n).base = (0 : SplitClNNAlg n) :=
  rfl

end InfoGeometry.Spectral.Homotopy.Suspension
