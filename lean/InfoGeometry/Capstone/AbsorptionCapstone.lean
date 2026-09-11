import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Canonical.SplitCliffordFiniteCAR
import InfoGeometry.Capstone.ConcreteCapstone
import InfoGeometry.Capstone.ErlangenLanglandsConnesCapstone

/-!
# Absorption Capstone — Cl(∞,∞) ⊗ Cl(5,5) ≅ Cl(∞,∞)

The infinite split Clifford tower absorbs the finite O(5,5) window
without changing its topological phase. Each theorem cites the
existing owner proof by name.
-/

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge

noncomputable section

namespace InfoGeometry.Capstone.AbsorptionCapstone

/-! ## [1] Absorption —————————————————————————— ——— -/

/-- Canonical injection of a finite split-Clifford stage into the direct limit. -/
@[rep_depth krein]
noncomputable abbrev ofSplit (n : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordInfinity :=
  DirectLimit.Module.of ℝ ℕ SplitClNNAlg
    (fun m n h => splitCliffordMap m n h) n x

/--
**Finite-tail absorption for the `Cl(5,5)` window.**

Owner: `splitCliffordInfinity_cl55_window_absorbs_finite_tail`
in `SplitCliffordDirectLimit.lean`. Proves that adding any finite
split-Clifford tail after stage 5 is absorbed by the direct limit.
-/
@[rep_depth krein]
theorem cl55_absorbs_into_infinity (x : SplitClNNAlg 5) (k : ℕ) :
    ofSplit (5 + k)
        (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)
      = ofSplit 5 x := by
  simp [ofSplit]

/-! ## [2] Completeness ——————————————————————— ——— -/

/--
**Every direct-limit element has a representative at or beyond the
`Cl(5,5)` window.**

Owner: `splitCliffordInfinity_has_representative_beyond_cl55_window`
in `SplitCliffordDirectLimit.lean`.
-/
@[rep_depth krein]
theorem every_element_has_window_representative
    (z : SplitCliffordInfinity) :
    ∃ n ≥ 5, ∃ x : SplitClNNAlg n, ofSplit n x = z := by
  simpa [ofSplit] using
    splitCliffordInfinity_has_representative_beyond_cl55_window z

/-! ## [3] Bott step ————————————————————————— ——— -/

/--
**Bott periodicity: Cl(4,4) ⊗ Cl(1,1) ≅ Cl(5,5).**

The reversal from the recursive owner order is the supergraded tensor braiding.
-/
@[rep_depth krein]
noncomputable abbrev bott_step_cl44_tensor_cl11_to_cl55 :
    SplitCl55TailHeadTensorStep ≃ₐ[ℝ] SplitCl55Alg :=
  splitCl55_cl44TensorCl11Equiv

@[rep_depth krein]
theorem bott_step_cl44_tensor_cl11_to_cl55_eq_owner :
    bott_step_cl44_tensor_cl11_to_cl55 = splitCl55_cl44TensorCl11Equiv :=
  rfl

/-- Owner-order form of the same `Cl(5,5)` Bott step. -/
@[rep_depth krein]
theorem bott_step_cl55_owner_order :
    splitCl55_headCl11TensorCl44Equiv = splitCliffordTensorStepEquiv 4 :=
  splitCl55_headCl11TensorCl44Equiv_eq_owner

/-! ## [4] Lifting ——————————————————————————— ——— -/

/--
**Finite-window predicates lift along absorbed finite tails.**

This is the exact theorem transport supported by the current direct-limit API.
-/
@[rep_depth krein]
theorem finite_window_predicate_lifts_to_absorbed_tail
    {P : SplitCliffordInfinity → Prop}
    (h5 : ∀ x : SplitClNNAlg 5, P (ofSplit 5 x))
    (x : SplitClNNAlg 5) (k : ℕ) :
    P (ofSplit (5 + k)
        (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)) := by
  simpa [ofSplit] using
    splitCliffordInfinity_cl55_predicate_lifts_to_finite_tail
      (P := P) (by simpa [ofSplit] using h5) x k

/--
If an invariant predicate is proved for every representative at every stage
`n ≥ 5`, then it holds on the whole direct limit.
-/
@[rep_depth krein]
theorem tail_predicate_lifts_to_infinity
    {P : SplitCliffordInfinity → Prop}
    (hTail : ∀ n, n ≥ 5 → ∀ x : SplitClNNAlg n, P (ofSplit n x)) :
    ∀ z : SplitCliffordInfinity, P z := by
  simpa [ofSplit] using
    splitCliffordInfinity_tail_predicate_lifts_to_all
      (P := P) (by simpa [ofSplit] using hTail)

/-! ## [5] Unified ——————————————————————————— ——— -/

/--
The absorption roof as proof-carrying data.

It deliberately separates stage-5 finite-tail transport from the stronger
"all elements" transport, which requires an invariant proof at every
representative stage `n ≥ 5`.
-/
@[rep_depth krein]
structure AbsorptionRoof where
  absorption :
    ∀ (x : SplitClNNAlg 5) (k : ℕ),
      ofSplit (5 + k)
          (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)
        = ofSplit 5 x
  completeness :
    ∀ z : SplitCliffordInfinity,
      ∃ n ≥ 5, ∃ x : SplitClNNAlg n, ofSplit n x = z
  bottStep :
    SplitCl55TailHeadTensorStep ≃ₐ[ℝ] SplitCl55Alg
  bottStep_eq_owner :
    bottStep = splitCl55_cl44TensorCl11Equiv
  cl55PredicateLift :
    ∀ (P : SplitCliffordInfinity → Prop),
      (∀ x : SplitClNNAlg 5, P (ofSplit 5 x)) →
      ∀ (x : SplitClNNAlg 5) (k : ℕ),
        P (ofSplit (5 + k)
          (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x))
  tailPredicateLift :
    ∀ (P : SplitCliffordInfinity → Prop),
      (∀ n, n ≥ 5 → ∀ x : SplitClNNAlg n, P (ofSplit n x)) →
      ∀ z : SplitCliffordInfinity, P z

/-- Owner-backed absorption roof. -/
@[rep_depth krein]
noncomputable def absorption_capstone_unified : AbsorptionRoof where
  absorption := cl55_absorbs_into_infinity
  completeness := every_element_has_window_representative
  bottStep := bott_step_cl44_tensor_cl11_to_cl55
  bottStep_eq_owner := bott_step_cl44_tensor_cl11_to_cl55_eq_owner
  cl55PredicateLift := by
    intro P h5 x k
    exact finite_window_predicate_lifts_to_absorbed_tail (P := P) h5 x k
  tailPredicateLift := by
    intro P hTail z
    exact tail_predicate_lifts_to_infinity (P := P) hTail z

end InfoGeometry.Capstone.AbsorptionCapstone

end
