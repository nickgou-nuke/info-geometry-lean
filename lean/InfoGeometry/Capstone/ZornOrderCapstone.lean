import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.BraidColimitZornBarrier
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.OperatorAlgebra.FiniteJkoJaynesContinuumBridge

/-!
# Zorn–Order Capstone — Global and Local Ordering on the Cantor Boundary

Chains the two Zorn theorems, the finite JKO/Jaynes readout, and the split
Clifford absorption theorem into a single capstone surface.

This file is deliberately limited to the theorem surfaces currently owned by
the repository: symbolic Cantor boundary Zorn closure, braid-colimit Zorn
closure, exact finite nilpotent JKO/Jaynes readout, and direct-limit
`Cl(5,5)` absorption. It does not assert a Devil's staircase theorem or a
general analytic Wasserstein/KMS limit.
-/

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.BraidColimitZornBarrier
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge

noncomputable section

namespace InfoGeometry.Capstone.ZornOrderCapstone

/-! ## [1] Zorn global — maximal boundary attractor ———————— ——— -/

/--
**Global order: Zorn's lemma guarantees a maximal symbolic boundary subsystem.**

Wraps `FractalCantorCliffordFockBridge.zorn_maximal_boundarySubsystem`.
The poset of prefix/tail-invariant symbolic boundary subsystems under
inclusion has a maximal element between a seed subsystem and an ambient
subsystem.
-/
theorem maximal_boundary_attractor_exists
    (seed U : Set (ℕ → Bool))
    (hseedU : seed ⊆ U)
    (hseed : BoundarySubsystem seed) :
    ∃ M : Set (ℕ → Bool),
      seed ⊆ M ∧ M ⊆ U ∧ BoundarySubsystem M ∧
      ∀ N : Set (ℕ → Bool),
        seed ⊆ N → N ⊆ U → BoundarySubsystem N →
        M ⊆ N → N = M :=
  zorn_maximal_boundarySubsystem seed U hseedU hseed

/-! ## [1b] Zorn / direct-limit package — symbolic boundary plus arbitrary-depth reps -/

/--
**Global order plus split direct-limit compatibility.**

Wraps `FractalCantorCliffordFockBridge.splitCliffordInfinity_zornBoundarySubsystem_package`.
The Zorn-maximal symbolic boundary subsystem remains closed under finite
prefix/tail reconstruction, and every split-Clifford direct-limit point has
arbitrarily deep finite representatives.
-/
theorem maximal_boundary_with_splitClifford_representatives
    (z : SplitCliffordInfinity)
    (seed U : Set (ℕ → Bool))
    (hseedU : seed ⊆ U)
    (hseed : BoundarySubsystem seed) :
    ∃ M : Set (ℕ → Bool),
      seed ⊆ M ∧
        M ⊆ U ∧
          BoundarySubsystem M ∧
            (∀ ξ ∈ M, ∀ n : ℕ,
              boundaryConsList (boundaryPrefix n ξ) (boundaryIterateTail n ξ) ∈ M) ∧
            (∀ N : ℕ, ∃ n ≥ N, ∃ x : SplitClNNAlg n,
              DirectLimit.Module.of ℝ ℕ SplitClNNAlg
                (fun m n h => splitCliffordMap m n h) n x = z) ∧
            ∀ N : Set (ℕ → Bool),
              seed ⊆ N →
                N ⊆ U →
                  BoundarySubsystem N →
                    M ⊆ N →
                      N = M :=
  splitCliffordInfinity_zornBoundarySubsystem_package z seed U hseedU hseed

/-! ## [2] Zorn fusion — maximal fusion subset ——————————— ——— -/

/--
**Fusion order: the braid colimit has a maximal fusion-closed subset.**

Wraps `BraidColimitZornBarrier.zorn_maximal_fusion_subset`.
The Braid tower has a maximal element under `fusionInclusion`.
-/
theorem maximal_fusion_subset_exists
    (C0 : FibFusionSubset) :
    ∃ C_max : FibFusionSubset,
      fusionInclusion C0 C_max ∧
      ∀ D : FibFusionSubset,
        fusionInclusion C_max D → D = C_max :=
  zorn_maximal_fusion_subset C0

/-! ## [3] Local finite JKO/Jaynes readout — exact nilpotent continuum law -/

/--
**Local finite order: exact finite JKO/Jaynes readout.**

Wraps
`FiniteJkoJaynesContinuumBridge.finiteEmpiricalState_projection_scaledParabolicStep_pow_eq_flow`.
This is the finite algebraic continuum bridge actually proved in the repo:
after projection, the `n`-fold rescaled nilpotent parabolic step has the same
finite empirical readout as the continuum parabolic flow.
-/
theorem finite_jko_jaynes_readout
    {K A ι : Type*}
    [Field K] [Ring A] [Algebra K A] [Fintype ι]
    (weight : K)
    (sample :
      InfoGeometry.OperatorAlgebra.JaynesFiniteState.FiniteObservableSample K A ι)
    (hweight : weight * (Fintype.card ι : K) = 1)
    (P :
      InfoGeometry.OperatorAlgebra.ContinuumLimit.ParabolicContinuumProjectionPacket
        (K := K) (A := A))
    (t : K) {n : ℕ} (hn : (n : K) ≠ 0) :
    InfoGeometry.OperatorAlgebra.JaynesFiniteState.finiteEmpiricalState
        weight sample hweight
        (P.projection
          ((InfoGeometry.OperatorAlgebra.ContinuumLimit.scaledParabolicStep
            P.generator t n) ^ n)) =
      InfoGeometry.OperatorAlgebra.JaynesFiniteState.finiteEmpiricalState
        weight sample hweight
        (InfoGeometry.OperatorAlgebra.ContinuumLimit.continuumParabolicFlow
          P.generator t) :=
  InfoGeometry.OperatorAlgebra.FiniteJkoJaynesContinuumBridge.finiteEmpiricalState_projection_scaledParabolicStep_pow_eq_flow
      weight sample hweight P t hn

/-! ## [4] Tower absorption — Cl(5,5) window in Cl(∞,∞) ————— ——— -/

/--
**Tower order: the finite Cl(5,5) window absorbs finite tails in Cl(∞,∞).**

Wraps `SplitCliffordDirectLimit.splitCliffordInfinity_cl55_window_absorbs_finite_tail`.
Adding a finite tail after stage 5 does not change the direct-limit element.
-/
theorem cl55_window_absorbs
    (x : SplitClNNAlg 5) (k : ℕ) :
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) (5 + k)
        (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)
      =
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 5 x :=
  splitCliffordInfinity_cl55_window_absorbs_finite_tail x k

/-! ## [5] Completeness — every ∞-element has a representative beyond stage 5 -/

/--
**Every direct-limit element is represented at some stage `n ≥ 5`.**

Wraps `SplitCliffordDirectLimit.splitCliffordInfinity_has_representative_beyond_cl55_window`.
This is the precise non-truncation statement available from the direct-limit
API.
-/
theorem every_element_has_window_rep
    (z : SplitCliffordInfinity) :
    ∃ n ≥ 5, ∃ x : SplitClNNAlg n,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z :=
  splitCliffordInfinity_has_representative_beyond_cl55_window z

/-! ## [6] Unified package — the proved order surfaces stabilize together -/

/--
**The proved Zorn/order theorem surfaces together.**

This bundles only the currently formalized statements:

* symbolic Cantor boundary Zorn closure with arbitrary-depth split-Clifford
  representatives;
* braid-colimit Zorn closure;
* finite JKO/Jaynes exact nilpotent readout;
* stage-5 direct-limit absorption and representative completeness.
-/
structure TwinOrderStability where
  boundary :
    ∀ (z : SplitCliffordInfinity)
      (seed U : Set (ℕ → Bool))
      (_ : seed ⊆ U)
      (_ : BoundarySubsystem seed),
      ∃ M : Set (ℕ → Bool),
        seed ⊆ M ∧
          M ⊆ U ∧
            BoundarySubsystem M ∧
              (∀ ξ ∈ M, ∀ n : ℕ,
                boundaryConsList (boundaryPrefix n ξ) (boundaryIterateTail n ξ) ∈ M) ∧
              (∀ N : ℕ, ∃ n ≥ N, ∃ x : SplitClNNAlg n,
                DirectLimit.Module.of ℝ ℕ SplitClNNAlg
                  (fun m n h => splitCliffordMap m n h) n x = z) ∧
              ∀ N : Set (ℕ → Bool),
                seed ⊆ N →
                  N ⊆ U →
                    BoundarySubsystem N →
                      M ⊆ N →
                        N = M
  fusion :
    ∀ C0 : FibFusionSubset,
      ∃ C_max : FibFusionSubset,
        fusionInclusion C0 C_max ∧
        ∀ D : FibFusionSubset,
          fusionInclusion C_max D → D = C_max
  finiteJko :
    ∀ {K A ι : Type*}
      [Field K] [Ring A] [Algebra K A] [Fintype ι]
      (weight : K)
      (sample :
        InfoGeometry.OperatorAlgebra.JaynesFiniteState.FiniteObservableSample K A ι)
      (hweight : weight * (Fintype.card ι : K) = 1)
      (P :
        InfoGeometry.OperatorAlgebra.ContinuumLimit.ParabolicContinuumProjectionPacket
          (K := K) (A := A))
      (t : K) {n : ℕ} (_ : (n : K) ≠ 0),
      InfoGeometry.OperatorAlgebra.JaynesFiniteState.finiteEmpiricalState
          weight sample hweight
          (P.projection
            ((InfoGeometry.OperatorAlgebra.ContinuumLimit.scaledParabolicStep
              P.generator t n) ^ n)) =
        InfoGeometry.OperatorAlgebra.JaynesFiniteState.finiteEmpiricalState
          weight sample hweight
          (InfoGeometry.OperatorAlgebra.ContinuumLimit.continuumParabolicFlow
            P.generator t)
  absorption :
    ∀ (x : SplitClNNAlg 5) (k : ℕ),
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) (5 + k)
          (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k) x)
        =
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 5 x
  representative :
    ∀ z : SplitCliffordInfinity,
      ∃ n ≥ 5, ∃ x : SplitClNNAlg n,
        DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) n x = z

/-- Bundled owner-backed capstone, with no vacuous `True` fields. -/
theorem twin_orders_stabilize : TwinOrderStability where
  boundary := maximal_boundary_with_splitClifford_representatives
  fusion := maximal_fusion_subset_exists
  finiteJko := finite_jko_jaynes_readout
  absorption := cl55_window_absorbs
  representative := every_element_has_window_rep

end InfoGeometry.Capstone.ZornOrderCapstone
