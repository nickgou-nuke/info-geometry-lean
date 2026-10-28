/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# The existing ordered operator Berezinian

These definitions are relocated unchanged from `AlbertCayleyDickson`, preserving
their public namespace. The ratio and its ordered inverse need only native units
in an associative ring, independently of the later Zorn elimination theorems.
-/

namespace InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {A : Type*} [Ring A]

/-- Noncommutative operator Berezinian $\mathrm{Ber}_{\mathrm{nc}}(u, \Delta) = (u : A) * (\uparrow \Delta^{-1} : A)$. -/
@[simp] def opNoncommBerezinian (u Δ : Aˣ) : A :=
  (u : A) * (↑Δ⁻¹ : A)

/-- Inverse noncommutative operator Berezinian $\mathrm{Ber}_{\mathrm{nc}}^{-1}(u, \Delta) = (\Delta : A) * (\uparrow u^{-1} : A)$. -/
@[simp] def opNoncommBerezinianInv (u Δ : Aˣ) : A :=
  (Δ : A) * (↑u⁻¹ : A)

end InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
