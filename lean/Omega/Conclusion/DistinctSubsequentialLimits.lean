/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

namespace Omega.Conclusion

open Filter Topology

/-- A sequence with two subsequences converging to distinct limits cannot converge.

The maps `m` and `n` are required to tend to infinity, so composition with a
convergent sequence preserves the corresponding subsequential limits. -/
theorem not_tendsto_of_distinct_subsequential_limits
    (u : ℕ → ℝ) (m n : ℕ → ℕ) (a b : ℝ) (hab : a ≠ b)
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hmu : Tendsto (u ∘ m) atTop (𝓝 a))
    (hnu : Tendsto (u ∘ n) atTop (𝓝 b)) :
    ¬ Tendsto u atTop (𝓝 a) ∧ ¬ Tendsto u atTop (𝓝 b) := by
  constructor
  · intro hu
    have hEq : a = b :=
      tendsto_nhds_unique (f := u ∘ n) (l := atTop) (a := a) (b := b)
        (hu.comp hn) hnu
    exact hab hEq
  · intro hu
    have hEq : b = a :=
      tendsto_nhds_unique (f := u ∘ m) (l := atTop) (a := b) (b := a)
        (hu.comp hm) hmu
    exact hab hEq.symm

end Omega.Conclusion
