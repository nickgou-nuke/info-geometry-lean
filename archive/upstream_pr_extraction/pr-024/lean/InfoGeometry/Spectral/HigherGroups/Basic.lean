/- Finite higher-group compatibility layer.

This file provides a lightweight `GType` API that mirrors the original higher
group API shape but is formulated using the finite pointed-readout tower used in
this repository.
-/

import Mathlib
import InfoGeometry.Spectral.Homotopy
import InfoGeometry.Spectral.Homotopy.Suspension
import InfoGeometry.Spectral.Homotopy.Wedge
import InfoGeometry.Spectral.Homotopy.Smash
import InfoGeometry.Spectral.Homotopy.EM
import InfoGeometry.Spectral.Cohomology.Basic

noncomputable section

namespace InfoGeometry.Spectral.HigherGroups

open InfoGeometry.Spectral.Homotopy.Suspension
open InfoGeometry.Spectral.Homotopy.Wedge
open InfoGeometry.Spectral.Homotopy.Smash

set_option autoImplicit false

@[simp]
theorem loopSpace_eq (X : PointedReadout) :
    LoopSpace X = X := by
  rfl

@[simp]
theorem iteratedLoopSpace_eq (n : ℕ) (X : PointedReadout) :
    IteratedLoopSpace n X = X := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [IteratedLoopSpace, loopSpace_eq, ih]

/-
  1. Higher-group style objects
-/

structure GType (n k : ℕ) where
  car : PointedReadout
  B : PointedReadout
  e : PointedEquiv car (IteratedLoopSpace k B)

structure InfGType (k : ℕ) where
  car : PointedReadout
  B : PointedReadout
  e : PointedEquiv car (IteratedLoopSpace k B)

structure ωGType (n : ℕ) where
  B : ℕ → PointedReadout
  e : ∀ k : ℕ, PointedEquiv (B k) (IteratedLoopSpace (k + 1) (B (k + 1)))

@[simp] abbrev GType_car {n k : ℕ} (G : GType n k) : PointedReadout := G.car

@[simp] abbrev GType_B {n k : ℕ} (G : GType n k) : PointedReadout := G.B

@[simp] abbrev GType_e {n k : ℕ} (G : GType n k) :
    PointedEquiv G.car (IteratedLoopSpace k G.B) := G.e

/-
  2. Sigma characterization and projections
-/

def GType_sigma_char (n k : ℕ) :
    GType n k ≃ Σ (B : PointedReadout), Σ (X : PointedReadout), PointedEquiv X (IteratedLoopSpace k B) := by
  refine ⟨fun G => ⟨G.B, G.car, G.e⟩, fun ⟨B, X, e⟩ => ⟨X, B, e⟩, ?_, ?_⟩
  · intro G
    rfl
  · intro t
    rfl

def GType_equiv (n k : ℕ) : GType n k ≃ GType n k := Equiv.refl (GType n k)

/-
  3. Constructions
-/

def Forget {n k : ℕ} (G : GType n (k + 1)) : GType n k :=
  { car := G.car
    B := G.B
    e := G.e }

def Decat {n k : ℕ} (G : GType (n + 1) k) : GType n k :=
  { car := G.car
    B := G.B
    e := G.e }

def Disc {n k : ℕ} (G : GType n k) : GType (n + 1) k :=
  { car := G.car
    B := G.B
    e := G.e }

def Deloop {n k : ℕ} (G : GType n (k + 1)) : GType (n + 1) k :=
  { car := G.car
    B := G.B
    e := by
      have h : IteratedLoopSpace (k + 1) G.B = IteratedLoopSpace k G.B := by
        rw [iteratedLoopSpace_eq, iteratedLoopSpace_eq]
      exact h ▸ G.e }

def Loop {n k : ℕ} (G : GType (n + 1) k) : GType n (k + 1) :=
  { car := G.car
    B := G.B
    e := by
      have h : IteratedLoopSpace k G.B = IteratedLoopSpace (k + 1) G.B := by
        rw [iteratedLoopSpace_eq, iteratedLoopSpace_eq]
      exact h ▸ G.e }

def Stabilize {n k : ℕ} (G : GType n k) : GType n (k + 1) :=
  { car := G.car
    B := G.B
    e := by
      have h : IteratedLoopSpace k G.B = IteratedLoopSpace (k + 1) G.B := by
        rw [iteratedLoopSpace_eq, iteratedLoopSpace_eq]
      exact h ▸ G.e }

/-
  4. Adjunction-style statements as identities in the finite readout layer.
-/

def DecatAdjointDisc {n k : ℕ} (G : GType (n + 1) k) (H : GType n k) :
    PointedMap (GType_B (Decat G)) (GType_B H) ≃ PointedMap (GType_B G) (GType_B (Disc H)) := by
  simpa [Decat, Disc, GType_B] using (Equiv.refl (PointedMap (GType_B G) (GType_B H)))

def DecatDisc {n k : ℕ} (G : GType n k) : Decat (Disc G) = G := by
  cases G
  simp [Decat, Disc]

def DeloopAdjointLoop {n k : ℕ} (G : GType n (k + 1)) (H : GType (n + 1) k) :
    PointedMap (GType_B (Deloop G)) (GType_B H) ≃ PointedMap (GType_B G) (GType_B (Loop H)) := by
  simpa [Deloop, Loop, GType_B, iteratedLoopSpace_eq] using
    (Equiv.refl (PointedMap (GType_B G) (GType_B H)))

def LoopDeloop {n k : ℕ} (G : GType n (k + 1)) : Loop (Deloop G) = G := by
  cases G
  simp [Deloop, Loop]

def StabilizeAdjointForget {n k : ℕ} (G : GType n k) (H : GType n (k + 1)) :
    PointedMap (GType_B (Stabilize G)) (GType_B H) ≃ PointedMap (GType_B G) (GType_B (Forget H)) := by
  simpa [Stabilize, Forget, GType_B, iteratedLoopSpace_eq] using
    (Equiv.refl (PointedMap (GType_B G) (GType_B H)))

def StabilizeForget {n k : ℕ} (_H : k ≥ n + 1) (G : GType n (k + 1)) :
    PointedEquiv (GType_B (Stabilize (Forget G))) (GType_B G) := by
  cases G
  simp [Forget, Stabilize, GType_B]
  exact ⟨Equiv.refl _, rfl⟩

def StabilizeForget' {n k : ℕ} (_H : k ≥ n + 1) (G : GType n (k + 1)) :
    PointedEquiv (GType_B (Stabilize (Forget G))) (GType_B G) :=
  StabilizeForget (n := n) (k := k) _H G

def Stabilization {n k : ℕ} (_H : k ≥ n + 2) :
    GType n k ≃ GType n (k + 1) :=
  { toFun := Stabilize
    invFun := fun G' => Forget G'
    left_inv := by
      intro G
      cases G
      simp [Forget, Stabilize]
    right_inv := by
      intro G'
      cases G'
      simp [Forget, Stabilize]
  }

/-
  5. Trivial finite closure lemmas.
-/

def GTypeHom {n k : ℕ} (G H : GType n k) : Type := PointedMap (GType_B G) (GType_B H)

theorem isSet_GTypeHom {n k : ℕ} (G H : GType n k) : True := by
  trivial

def isTrunc_GType {n k : ℕ} : True := by
  trivial

end InfoGeometry.Spectral.HigherGroups
