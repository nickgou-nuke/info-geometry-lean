/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Topological.DonaldsonWittenNonassociativeBRST

/-!
# Companion Audit for `DonaldsonWittenNonassociativeBRST` (Section 142b)

Provides concrete `ℤ` kernel-checked instantiations (`by decide`) of the `NonUnitalNonAssocRing`
Akivis identity, non-zero associator, non-zero Jacobiator anomaly, and two-step BRST closure
on `SplitOctonion ℤ`.
-/

set_option autoImplicit false

namespace InfoGeometry.Topological.DonaldsonWittenAudit

open InfoGeometry.Topological.DonaldsonWitten
open InfoGeometry.Topological.DonaldsonWitten.SplitOctonion

/-- Basis quark vectors over `ℤ`. -/
def u1Int : ColorVec3 ℤ := ⟨1, 0, 0⟩
def u2Int : ColorVec3 ℤ := ⟨0, 1, 0⟩
def u3Int : ColorVec3 ℤ := ⟨0, 0, 1⟩

/-- Concrete verification that the associator of three quark basis elements in `SplitOctonion ℤ` is `-K₀ ≠ 0`. -/
theorem audit_splitOctonion_associator_nonzero_int :
    associator (quark u1Int) (quark u2Int) (quark u3Int) =
      scale (-1) paraSymplecticK0 ∧
    associator (quark u1Int) (quark u2Int) (quark u3Int) ≠ 0 := by
  decide

/-- Concrete verification of the 6-term Akivis identity on `SplitOctonion ℤ` with non-zero Jacobiator `-6 K₀`. -/
theorem audit_akivis_identity_splitOctonion_int :
    let x := quark u1Int
    let y := quark u2Int
    let z := quark u3Int
    jacobiator x y z = scale (-6) paraSymplecticK0 ∧
    jacobiator x y z =
      associator x y z + associator y z x + associator z x y -
      associator y x z - associator x z y - associator z y x := by
  decide

/-- Concrete color-diagonal derivation on `SplitOctonion ℤ` with weights `(1, -1, 0)`. -/
def colorDeriv1Int (X : SplitOctonion ℤ) : SplitOctonion ℤ :=
  ⟨0, ⟨X.u.c1, -X.u.c2, 0⟩, ⟨-X.v.c1, X.v.c2, 0⟩, 0⟩

/-- Concrete two-step BRST closure check on `SplitOctonion ℤ`. -/
theorem audit_brst_two_step_closure_int :
    let M : BRSTMultiplet (SplitOctonion ℤ) := ⟨canonicalSplitOctonionInt, quark u1Int⟩
    (brstStep colorDeriv1Int M.A_conn (brstStep colorDeriv1Int M.A_conn M)).A_conn =
      - colorDeriv1Int M.A_conn ∧
    colorDeriv1Int M.A_conn ≠ 0 := by
  decide

/-- Concrete Leibniz check for `colorDeriv1Int` on `SplitOctonion ℤ`. -/
theorem audit_colorDeriv1Int_leibniz_int :
    let X := canonicalSplitOctonionInt
    let Y := quark u2Int
    colorDeriv1Int (X * Y) = colorDeriv1Int X * Y + X * colorDeriv1Int Y := by
  decide

end InfoGeometry.Topological.DonaldsonWittenAudit
