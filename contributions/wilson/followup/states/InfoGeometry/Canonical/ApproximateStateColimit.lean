/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
import CoreLean.ApproximateStateLimits
import InfoGeometry.Canonical.CStarAlgebraStateColimit

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-!
# Summable approximate compatibility supplies the existing GNS state interface

This adapter constructs the repository's actual `CompatibleStateFamily`
on an existing `ContinuousStarInductiveSystem`. No GNS carrier is replaced by
a scalar surrogate; the constructed functionals remain complex-linear and
positive on the full, possibly noncommutative C-star stages.
-/

noncomputable section

open Filter
open scoped Topology ComplexOrder

namespace CStarStateColimit.Native

open ApproximateCompatibility ContinuousStarInductiveSystem

variable (A : ℕ → Type)
variable [∀ n, CStarAlgebra (A n)] [∀ n, PartialOrder (A n)]
variable [∀ n, StarOrderedRing (A n)]

/-- Summable adjacent-state errors construct a genuinely compatible state family
for every transition of the existing sequential C-star system. -/
theorem exists_compatibleStateFamily_of_summable_errors
    (sys : ContinuousStarInductiveSystem A) (ω : ∀ n, State (A n)) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hSum : Summable ε)
    (hApprox : ∀ n (a : A n),
      ‖(ω (n + 1)).functional (sys.map (Nat.le_succ n) a) - (ω n).functional a‖ ≤
        ε n * ‖a‖) :
    ∃ ν : CompatibleStateFamily A sys,
      (∀ n (a : A n),
        Tendsto (evaluationSequence (A := A) (E := ℂ)
          (fun n (a : A n) => sys.map (Nat.le_succ n) a)
          (fun n => (ω n).functional) n a) atTop (𝓝 ((ν.state n).functional a))) ∧
      (∀ n (a : A n) k,
        ‖(ν.state n).functional a -
          evaluationSequence (A := A) (E := ℂ)
            (fun n (a : A n) => sys.map (Nat.le_succ n) a)
            (fun n => (ω n).functional) n a k‖ ≤
          (∑' j : ℕ, ε (n + k + j)) * ‖a‖) := by
  obtain ⟨v, hOne, hLimit, hCompatible, hTail⟩ :=
    exists_normalized_positive_limits (A := A)
      (fun n => (sys.map (Nat.le_succ n) : A n →⋆ₐ[ℂ] A (n + 1)))
      (fun n => (ω n).functional)
      (fun n => (ω n).normalized) ε hε hSum hApprox
  let state : ∀ n, State (A n) := fun n => ⟨v n, hOne n⟩
  have hAdjacent (n : ℕ) :
      (state (n + 1)).restrict (sys.map (Nat.le_succ n)) = state n := by
    apply State.ext
    ext a
    exact hCompatible n a
  have hAll (i j : ℕ) (hij : i ≤ j) :
      (state j).restrict (sys.map hij) = state i := by
    induction j, hij using Nat.le_induction with
    | base => rw [sys.map_id, State.restrict_id]
    | succ k hik ih =>
      rw [← sys.map_comp hik (Nat.le_succ k), ← State.restrict_comp,
        hAdjacent, ih]
  exact ⟨⟨state, fun hij => hAll _ _ hij⟩, hLimit, hTail⟩

end CStarStateColimit.Native
