/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

namespace Omega.Conclusion

/-- A decoder through an observation must be constant on every observation fiber. -/
theorem decoder_eq_on_observation_fiber
    {State Observation Value : Type*}
    (observe : State → Observation) (target : State → Value)
    (decode : Observation → Value)
    (hdecode : ∀ s, target s = decode (observe s))
    {s t : State} (hst : observe s = observe t) :
    target s = target t := by
  calc
    target s = decode (observe s) := hdecode s
    _ = decode (observe t) := congrArg decode hst
    _ = target t := (hdecode t).symm

/-- A collision of observations with distinct target values rules out a decoder. -/
theorem no_decoder_of_observation_collision
    {State Observation Value : Type*}
    (observe : State → Observation) (target : State → Value)
    {s t : State} (hst : observe s = observe t)
    (htarget : target s ≠ target t) :
    ¬ ∃ decode : Observation → Value, ∀ u, target u = decode (observe u) := by
  rintro ⟨decode, hdecode⟩
  exact htarget (decoder_eq_on_observation_fiber observe target decode hdecode hst)

/-- The same obstruction holds when decoding is required only on a specified valid domain. -/
theorem no_valid_decoder_of_observation_collision
    {State Observation Value : Type*}
    (observe : State → Observation) (target : State → Value) (valid : State → Prop)
    {s t : State} (hs : valid s) (ht : valid t)
    (hst : observe s = observe t) (htarget : target s ≠ target t) :
    ¬ ∃ decode : Observation → Value,
      ∀ u, valid u → target u = decode (observe u) := by
  rintro ⟨decode, hdecode⟩
  apply htarget
  calc
    target s = decode (observe s) := hdecode s hs
    _ = decode (observe t) := congrArg decode hst
    _ = target t := (hdecode t ht).symm

/-- The product of two observations is still a single observation for the collision criterion. -/
theorem no_decoder_of_paired_observation_collision
    {State First Second Value : Type*}
    (observe₁ : State → First) (observe₂ : State → Second)
    (target : State → Value) {s t : State}
    (h₁ : observe₁ s = observe₁ t) (h₂ : observe₂ s = observe₂ t)
    (htarget : target s ≠ target t) :
    ¬ ∃ decode : First × Second → Value,
      ∀ u, target u = decode (observe₁ u, observe₂ u) := by
  apply no_decoder_of_observation_collision
    (fun u => (observe₁ u, observe₂ u)) target
  · exact Prod.ext h₁ h₂
  · exact htarget

end Omega.Conclusion
