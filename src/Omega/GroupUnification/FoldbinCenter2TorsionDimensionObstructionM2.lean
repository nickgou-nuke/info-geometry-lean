/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

namespace FiniteDimensional

/-- Compatibility alias for the `finrank` API used by paper-facing theorem statements. -/
noncomputable abbrev finrank (K : Type*) (V : Type*) [Semiring K] [AddCommMonoid V] [Module K V] :
    ℕ :=
  Module.finrank K V

end FiniteDimensional

namespace Omega.GroupUnification

/-- A finite-dimensional vector space of dimension below `n` admits no injective linear map from
the `n`-coordinate space. This is the general rank obstruction underlying the center
`2`-torsion instance below. -/
theorem no_injective_linearMap_fin_fun_of_finrank_lt
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n : ℕ) (hdim : Module.finrank K V < n) :
    ¬ ∃ f : (Fin n → K) →ₗ[K] V, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hrank : n ≤ Module.finrank K V := by
    simpa [Module.finrank_fin_fun (R := K)] using
      (LinearMap.finrank_le_finrank_of_injective hf :
        Module.finrank K (Fin n → K) ≤ Module.finrank K V)
  omega

set_option maxHeartbeats 400000 in
/-- If the center `2`-torsion has `F₂`-dimension at most `1`, then it cannot contain an injective
copy of `(Z/2)^3`.
    cor:foldbin-center-2torsion-dimension-obstruction-m2 -/
theorem paper_foldbin_center_2torsion_dimension_obstruction_m2
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hV : FiniteDimensional.finrank (ZMod 2) V ≤ 1) :
    ¬ ∃ f : (Fin 3 → ZMod 2) →ₗ[ZMod 2] V, Function.Injective f := by
  change Module.finrank (ZMod 2) V ≤ 1 at hV
  apply no_injective_linearMap_fin_fun_of_finrank_lt (ZMod 2) V 3
  omega

end Omega.GroupUnification
