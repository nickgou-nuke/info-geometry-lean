/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-!
# Range actions of a group inverse

Consumer-minimal consequences of the canonical Hartwig group-inverse laws for
an endomorphism of a finite-dimensional real vector space.
-/

namespace InfoGeometry.QuantumContext.GroupInverseRangeActionsCandidate

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The image of a group inverse is contained in the range of the original map. -/
theorem groupInverse_apply_mem_range
    (A D : Module.End ℝ V) (hD : IsGroupInverse A D) (x : V) :
    D x ∈ A.range := by
  have hcomm : A (D (D x)) = D (A (D x)) := by
    exact congrArg (fun f : Module.End ℝ V => f (D x)) hD.2.2
  have hDAD : D (A (D x)) = D x := by
    exact congrArg (fun f : Module.End ℝ V => f x) hD.2.1
  exact ⟨D (D x), hcomm.trans hDAD⟩

/-- On the range of `A`, the group inverse followed by `A` recovers the input. -/
theorem apply_groupInverse_eq_of_mem_range
    (A D : Module.End ℝ V) (hD : IsGroupInverse A D) (b : V)
    (hb : b ∈ A.range) :
    A (D b) = b := by
  obtain ⟨y, rfl⟩ := hb
  have hADAx : A (D (A y)) = A y := by
    simpa [mul_assoc] using congrArg (fun f : Module.End ℝ V => f y) hD.1
  exact hADAx

end InfoGeometry.QuantumContext.GroupInverseRangeActionsCandidate
