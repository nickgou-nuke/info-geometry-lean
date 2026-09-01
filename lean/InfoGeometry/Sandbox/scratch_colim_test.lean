import Mathlib

/-!
# Compatibility tombstone for historical colimit scratch module

The root Lake build currently enumerates `InfoGeometry.Sandbox.scratch_colim_test`
on clean checkouts even though the historical scratch source was removed.  This
empty module restores that module path without introducing definitions,
axioms, theorems, or imports into canonical owners.

It is build-surface compatibility only; categorical colimit results belong in
the theorem-owned `InfoGeometry` modules.
-/
