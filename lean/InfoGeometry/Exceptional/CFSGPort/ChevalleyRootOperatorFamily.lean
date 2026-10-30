/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from AxiomMath/CFSG LieType/Chevalley/RootOps/Family.lean.
This owner states the exceptional root-operator family contract on the local
root-module endomorphism algebra; its checked data instance is built from the
Weyl-row certificates in `ChevalleyFastChecks`.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorMirror
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastChecksE8

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

universe u

/-- A root of a tagged exceptional root system, retaining its proof of
membership in the inductively generated root set. -/
abbrev RootCarrier (τ : Tag) := {α : Fin τ.rank → ℤ // IsRoot τ α}

/-- The group-indexed coefficient API used to turn sparse root-operator
certificates into identities between pinned root-group units. Coefficients
act on the genuine endomorphism algebra of the exceptional root module. -/
structure RootOperatorFamily (τ : Tag) where
  D : (R : Type u) → [CommRing R] → RootCarrier τ → ℕ →
    Module.End R (RootModule τ R)
  D_zero : ∀ (R : Type u) [CommRing R] (α : RootCarrier τ), D R α 0 = 1
  D_eq_zero : ∀ (R : Type u) [CommRing R] (α : RootCarrier τ) (k : ℕ),
    4 ≤ k → D R α k = 0
  D_simple : ∀ (R : Type u) [CommRing R] (j : Fin τ.rank) (k : ℕ),
    D R ⟨Pi.single j 1, IsRoot.basis j⟩ k = xCoeff τ R j k
  D_neg_simple : ∀ (R : Type u) [CommRing R] (j : Fin τ.rank) (k : ℕ),
    D R ⟨-Pi.single j 1, isRoot_neg_single τ j⟩ k = yCoeff τ R j k
  sign : Fin τ.rank → RootCarrier τ → ℤ
  sign_eq : ∀ (i : Fin τ.rank) (α : RootCarrier τ),
    sign i α = 1 ∨ sign i α = -1
  conj : ∀ (R : Type u) [CommRing R] (i : Fin τ.rank) (α : RootCarrier τ) (k : ℕ),
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * D R α k =
      ((sign i α ^ k : ℤ) : R) •
        (D R ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩ k *
          (weylElt τ R i 1 : Module.End R (RootModule τ R)))

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
