/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import CoreLean.ApproximateCompatibility
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in

/-!
# Limits of approximately compatible normalized positive functionals

For genuine complex C-star algebras and unital star-algebra homomorphisms,
summable approximate compatibility gives exactly compatible limit states.
Linearity, positivity, and normalization are proved from the finite-stage
maps. Contractivity of the transitions is derived from Mathlib's C-star API.

No injectivity, commutativity, or finite dimensionality is assumed. The
theorem supplies compatible functionals; a GNS or algebraic colimit is a
separate construction that may consume them.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology ComplexOrder

namespace ApproximateCompatibility

variable {A : ℕ → Type*}
variable [∀ n, CStarAlgebra (A n)] [∀ n, PartialOrder (A n)]
variable [∀ n, StarOrderedRing (A n)]

variable (ι : ∀ n, A n →⋆ₐ[ℂ] A (n + 1)) (ω : ∀ n, A n →ₚ[ℂ] ℂ)

omit [∀ n, StarOrderedRing (A n)] in
/-- Each finite-horizon evaluation is complex-linear in its initial observable. -/
theorem evaluationSequence_add (k n : ℕ) (a b : A n) :
    evaluationSequence (fun n => ι n) (fun n => ω n) n (a + b) k =
      evaluationSequence (fun n => ι n) (fun n => ω n) n a k +
        evaluationSequence (fun n => ι n) (fun n => ω n) n b k := by
  induction k generalizing n with
  | zero => exact map_add (ω n) a b
  | succ k ih =>
    simpa only [evaluationSequence_succ, map_add] using ih (n + 1) (ι n a) (ι n b)

omit [∀ n, StarOrderedRing (A n)] in
/-- Complex scalar multiplication is retained at every finite horizon. -/
theorem evaluationSequence_smul (k n : ℕ) (c : ℂ) (a : A n) :
    evaluationSequence (fun n => ι n) (fun n => ω n) n (c • a) k =
      c • evaluationSequence (fun n => ι n) (fun n => ω n) n a k := by
  induction k generalizing n with
  | zero => exact map_smul (ω n) c a
  | succ k ih =>
    simpa only [evaluationSequence_succ, map_smul] using ih (n + 1) (ι n a)

omit [∀ n, StarOrderedRing (A n)] in
/-- Normalization is retained by the unital refinement homomorphisms. -/
theorem evaluationSequence_one (hOne : ∀ n, ω n 1 = 1) (k n : ℕ) :
    evaluationSequence (fun n => ι n) (fun n => ω n) n 1 k = 1 := by
  induction k generalizing n with
  | zero => exact hOne n
  | succ k ih => simpa only [evaluationSequence_succ, map_one] using ih (n + 1)

/-- The full complex value is nonnegative in the native C-star order. -/
theorem evaluationSequence_nonneg (k n : ℕ) (a : A n) (ha : 0 ≤ a) :
    0 ≤ evaluationSequence (fun n => ι n) (fun n => ω n) n a k := by
  induction k generalizing n with
  | zero => exact (ω n).map_nonneg ha
  | succ k ih =>
    apply ih (n + 1) (ι n a)
    exact map_nonneg (ι n) ha

/-- Summable RG compatibility errors produce native normalized positive linear
functionals with exact compatibility and a quantitative bound at every horizon. -/
theorem exists_normalized_positive_limits
    (hOne : ∀ n, ω n 1 = 1) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hSum : Summable ε)
    (hApprox : ∀ n (a : A n), ‖ω (n + 1) (ι n a) - ω n a‖ ≤ ε n * ‖a‖) :
    ∃ ωLimit : ∀ n, A n →ₚ[ℂ] ℂ,
      (∀ n, ωLimit n 1 = 1) ∧
      (∀ n (a : A n),
        Tendsto (evaluationSequence (fun n => ι n) (fun n => ω n) n a)
          atTop (𝓝 (ωLimit n a))) ∧
      (∀ n (a : A n), ωLimit (n + 1) (ι n a) = ωLimit n a) ∧
      (∀ n (a : A n) k,
        ‖ωLimit n a - evaluationSequence (fun n => ι n) (fun n => ω n) n a k‖ ≤
          (∑' j : ℕ, ε (n + k + j)) * ‖a‖) := by
  obtain ⟨v, hv, hCompatible, hTail⟩ := exists_compatible_limit
    (fun n => ι n) (fun n => ω n) ε hε hSum
    (fun n a => NonUnitalStarAlgHom.norm_apply_le (ι n) a)
    (fun n a => by
      rw [dist_eq_norm, norm_sub_rev]
      exact hApprox n a)
  have hAdd (n : ℕ) (a b : A n) : v n (a + b) = v n a + v n b := by
    apply tendsto_nhds_unique (hv n (a + b))
    exact Tendsto.congr'
      (Eventually.of_forall (fun k => (evaluationSequence_add ι ω k n a b).symm))
      ((hv n a).add (hv n b))
  have hSmul (n : ℕ) (c : ℂ) (a : A n) : v n (c • a) = c • v n a := by
    apply tendsto_nhds_unique (hv n (c • a))
    exact Tendsto.congr'
      (Eventually.of_forall (fun k => (evaluationSequence_smul ι ω k n c a).symm))
      ((hv n a).const_smul c)
  let ωLimit : ∀ n, A n →ₚ[ℂ] ℂ := fun n =>
    PositiveLinearMap.mk₀
      { toFun := v n
        map_add' := hAdd n
        map_smul' := hSmul n }
      (fun a ha => ge_of_tendsto (hv n a)
        (Eventually.of_forall (fun k => evaluationSequence_nonneg ι ω k n a ha)))
  refine ⟨ωLimit, ?_, hv, hCompatible, ?_⟩
  · intro n
    change v n 1 = 1
    apply tendsto_nhds_unique (hv n 1)
    exact Tendsto.congr'
      (Eventually.of_forall (fun k => (evaluationSequence_one ι ω hOne k n).symm))
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
  · intro n a k
    change ‖v n a - evaluationSequence (fun n => ι n) (fun n => ω n) n a k‖ ≤ _
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hTail n a k

end ApproximateCompatibility
