import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Volume.ConnesCocycle

/-!
# InfoGeometry.Canonical.BekensteinBound

Constructive entropy-bound layer from the Sinkhorn Radon-Nikodym barrier.

The key statement is a trajectorywise lower bound:
the pre-step RN barrier is always nonnegative, obtained from
the monotone step inequality plus the exact post-step zero identity.
-/

namespace InfoGeometry.Canonical.BekensteinBound

open InfoGeometry.Canonical.MoE
open InfoGeometry.Volume.ConnesCocycle

section RNBarrierBound

variable (n : Nat)

/-- Trajectorywise nonnegativity of the pre-step RN barrier. -/
theorem trajectoryRNBarrier_nonneg
    (T : SinkhornTrajectory n) (k : Nat) :
    0 ≤ trajectoryRNBarrier n T k := by
  have hmono : trajectoryRNBarrierNext n T k ≤ trajectoryRNBarrier n T k :=
    trajectoryRNBarrier_monotone (n := n) T k
  have hzero : trajectoryRNBarrierNext n T k = 0 :=
    trajectoryRNBarrierNext_eq_zero (n := n) T k
  simpa [hzero] using hmono

/--
Topological Bekenstein bound: every Sinkhorn step has nonnegative
RN-barrier entropy budget on the pre-step state.
-/
def TopologicalBekensteinBound (T : SinkhornTrajectory n) : Prop :=
  ∀ k : Nat, 0 ≤ trajectoryRNBarrier n T k

/-- Every admissible Sinkhorn trajectory satisfies the topological Bekenstein bound. -/
theorem topologicalBekensteinBound_of_sinkhornTrajectory
    (T : SinkhornTrajectory n) :
    TopologicalBekensteinBound n T := by
  intro k
  exact trajectoryRNBarrier_nonneg (n := n) T k

end RNBarrierBound

section CocycleBridge

variable (n : Nat)
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
Phase-aligned RN generator (without absolute value), chosen on the same axis as
the pre-step RN barrier.
-/
noncomputable def phaseRNGeneratorBefore (phase : SinkhornPhase) (M : SinkhornMatrix n) : ℝ :=
  match phase with
  | .row => colRadonNikodymGenerator n M
  | .col => rowRadonNikodymGenerator n M

lemma abs_trajectoryRNGenerator_le_trajectoryRNBarrier
    (T : SinkhornTrajectory n) (k : Nat) :
    |phaseRNGeneratorBefore n (phaseAt k) (T.state k)| ≤ trajectoryRNBarrier n T k := by
  unfold trajectoryRNBarrier
  cases phaseAt k <;> simp [phaseRNGeneratorBefore]
  · exact Finset.abs_sum_le_sum_abs _ _
  · exact Finset.abs_sum_le_sum_abs _ _

/--
Cocycle Entropy Potential.
The additive potential Φ derived from the Connes RN-cocycle.
The absolute increment |Φ(k+1) - Φ(k)| represents the information-theoretic
work done during a Sinkhorn step.
-/
noncomputable def CocycleEntropyPotential
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (t : ℝ) : ℝ :=
  cocycleLogPotential (H := H) σ u hBridge t

/--
Barrier-lift route to the topological Bekenstein bound: once the RN barrier is
identified with an absolute cocycle-potential increment, nonnegativity follows
without carrying an explicit `IsConnesCocycle` packet.
-/
theorem topologicalBekensteinBound_of_barrierLift
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hBarrierLift : ∀ k : Nat, trajectoryRNBarrier n T k =
      |CocycleEntropyPotential σ u hBridge (k + 1) - CocycleEntropyPotential σ u hBridge k|) :
    TopologicalBekensteinBound n T := by
  intro k
  rw [hBarrierLift]
  exact abs_nonneg _

/--
Compatibility cocycle-to-bound theorem.  The `IsConnesCocycle` hypothesis is
retained for named-argument callers, but the proof now routes through the
smaller barrier-lift theorem above; the bound itself does not use the additive
cocycle law.
-/
theorem topologicalBekensteinBound_of_connesCocycle
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hBarrierLift : ∀ k : Nat, trajectoryRNBarrier n T k =
      |CocycleEntropyPotential σ u hBridge (k + 1) - CocycleEntropyPotential σ u hBridge k|) :
    TopologicalBekensteinBound n T := by
  have _ : IsConnesCocycle σ u := hCocycle
  exact topologicalBekensteinBound_of_barrierLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge) (hBarrierLift := hBarrierLift)

/--
Concrete generator lift from a cocycle potential to the trajectory RN generator.
-/
def CocycleGeneratorLift
    (T : SinkhornTrajectory n) (Φ : ℝ → ℝ) : Prop :=
  ∀ k : Nat,
    Φ (k + 1) - Φ k = phaseRNGeneratorBefore n (phaseAt k) (T.state k)

/--
Canonical discrete RN-generator potential on natural steps:
`Ψ(0)=0`, `Ψ(k+1)=Ψ(k)+g_k` with `g_k` the concrete phase-aligned RN generator.
-/
noncomputable def trajectoryRNGeneratorPotentialNat
    (T : SinkhornTrajectory n) : Nat → ℝ
  | 0 => 0
  | k + 1 =>
      trajectoryRNGeneratorPotentialNat T k
        + phaseRNGeneratorBefore n (phaseAt k) (T.state k)

/--
Canonical real-valued lift of the discrete RN-generator potential.
It is evaluated at integer times via `Int.floor`.
-/
noncomputable def trajectoryRNGeneratorPotential
    (T : SinkhornTrajectory n) : ℝ → ℝ :=
  fun t => trajectoryRNGeneratorPotentialNat (n := n) T (Int.toNat (Int.floor t))

@[simp] lemma trajectoryRNGeneratorPotential_natCast
    (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryRNGeneratorPotential (n := n) T k
      = trajectoryRNGeneratorPotentialNat (n := n) T k := by
  simp [trajectoryRNGeneratorPotential]

/--
The canonical RN-generator potential satisfies the cocycle lift relation.
-/
theorem cocycleGeneratorLift_of_trajectoryRNGeneratorPotential
    (T : SinkhornTrajectory n) :
    CocycleGeneratorLift n T (trajectoryRNGeneratorPotential (n := n) T) := by
  intro k
  have hk1 :
      trajectoryRNGeneratorPotential (n := n) T (k + 1 : ℝ)
        = trajectoryRNGeneratorPotentialNat (n := n) T (k + 1) := by
    simp [trajectoryRNGeneratorPotential]
  have hk0 :
      trajectoryRNGeneratorPotential (n := n) T (k : ℝ)
        = trajectoryRNGeneratorPotentialNat (n := n) T k := by
    simp [trajectoryRNGeneratorPotential]
  calc
    trajectoryRNGeneratorPotential (n := n) T (k + 1)
      - trajectoryRNGeneratorPotential (n := n) T k
        =
      trajectoryRNGeneratorPotentialNat (n := n) T (k + 1)
        - trajectoryRNGeneratorPotentialNat (n := n) T k := by
          rw [hk1, hk0]
    _ =
      (trajectoryRNGeneratorPotentialNat (n := n) T k
        + phaseRNGeneratorBefore n (phaseAt k) (T.state k))
        - trajectoryRNGeneratorPotentialNat (n := n) T k := by
          simp [trajectoryRNGeneratorPotentialNat]
    _ = phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
          ring

/--
If a cocycle entropy potential agrees on integer times with the canonical
RN-generator potential, then the generator-lift condition is derived internally.
-/
theorem cocycleGeneratorLift_of_cocycleEntropyPotential_match
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (hMatch :
      ∀ k : Nat,
        CocycleEntropyPotential (H := H) σ u hBridge k
          = trajectoryRNGeneratorPotential (n := n) T k) :
    CocycleGeneratorLift n T (CocycleEntropyPotential (H := H) σ u hBridge) := by
  intro k
  have hk1 :
      CocycleEntropyPotential (H := H) σ u hBridge (k + 1 : ℝ)
        = trajectoryRNGeneratorPotential (n := n) T (k + 1 : ℝ) := by
    simpa [Nat.cast_add] using hMatch (k + 1)
  have hk0 :
      CocycleEntropyPotential (H := H) σ u hBridge (k : ℝ)
        = trajectoryRNGeneratorPotential (n := n) T (k : ℝ) := by
    simpa using hMatch k
  calc
    CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
      - CocycleEntropyPotential (H := H) σ u hBridge k
        =
      trajectoryRNGeneratorPotential (n := n) T (k + 1)
        - trajectoryRNGeneratorPotential (n := n) T k := by
          rw [hk1, hk0]
    _ = phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
          exact cocycleGeneratorLift_of_trajectoryRNGeneratorPotential
            (n := n) (T := T) k

/--
Zero-anchored uniqueness on integer times:
if a cocycle entropy potential satisfies the concrete generator-lift relation
and is normalized at time `0`, then it matches the canonical trajectory
RN-generator potential on all natural steps.
-/
theorem cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (hLift :
      CocycleGeneratorLift n T (CocycleEntropyPotential (H := H) σ u hBridge))
    (hZero :
      CocycleEntropyPotential (H := H) σ u hBridge 0 = 0) :
    ∀ k : Nat,
      CocycleEntropyPotential (H := H) σ u hBridge k
        = trajectoryRNGeneratorPotential (n := n) T k := by
  intro k
  induction k with
  | zero =>
      simpa [trajectoryRNGeneratorPotential, trajectoryRNGeneratorPotentialNat] using hZero
  | succ k ih =>
      have hStepΦ :
          CocycleEntropyPotential (H := H) σ u hBridge ((k : ℝ) + 1)
            = CocycleEntropyPotential (H := H) σ u hBridge k
              + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
        have hLiftk :
            CocycleEntropyPotential (H := H) σ u hBridge ((k : ℝ) + 1)
              - CocycleEntropyPotential (H := H) σ u hBridge k
              = phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
          simpa [Nat.cast_add, Nat.cast_one] using hLift k
        linarith
      have hStepΨ :
          trajectoryRNGeneratorPotential (n := n) T ((k : ℝ) + 1)
            = trajectoryRNGeneratorPotential (n := n) T k
              + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
        calc
          trajectoryRNGeneratorPotential (n := n) T ((k : ℝ) + 1)
              = trajectoryRNGeneratorPotential (n := n) T (k + 1 : Nat) := by
                  have hcast : ((k : ℝ) + 1) = (k + 1 : Nat) := by
                    norm_num [Nat.cast_add]
                  exact congrArg (trajectoryRNGeneratorPotential (n := n) T) hcast
          _ =
            trajectoryRNGeneratorPotentialNat (n := n) T (k + 1) := by
                  simpa using trajectoryRNGeneratorPotential_natCast (n := n) (T := T) (k := k + 1)
          _ = trajectoryRNGeneratorPotentialNat (n := n) T k
                + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
                simp [trajectoryRNGeneratorPotentialNat]
          _ = trajectoryRNGeneratorPotential (n := n) T k
                + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
                exact (congrArg
                  (fun r : ℝ => r + phaseRNGeneratorBefore n (phaseAt k) (T.state k))
                  (trajectoryRNGeneratorPotential_natCast (n := n) (T := T) (k := k)).symm)
      calc
        CocycleEntropyPotential (H := H) σ u hBridge (k + 1 : Nat)
            = CocycleEntropyPotential (H := H) σ u hBridge ((k : ℝ) + 1) := by
                have hcast : (k + 1 : Nat) = ((k : ℝ) + 1) := by
                  norm_num [Nat.cast_add]
                exact congrArg (CocycleEntropyPotential (H := H) σ u hBridge) hcast
        _ = CocycleEntropyPotential (H := H) σ u hBridge k
                + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := hStepΦ
        _ = trajectoryRNGeneratorPotential (n := n) T k
              + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
              rw [ih]
        _ = trajectoryRNGeneratorPotential (n := n) T ((k : ℝ) + 1) := by
              linarith [hStepΨ]
        _ = trajectoryRNGeneratorPotential (n := n) T (k + 1 : Nat) := by
              have hcast : ((k : ℝ) + 1) = (k + 1 : Nat) := by
                norm_num [Nat.cast_add]
              exact congrArg (trajectoryRNGeneratorPotential (n := n) T) hcast

/--
Connes-cocycle owner route to zero-normalization of the selected cocycle
entropy potential.

This names the constructive discharge of the older bare `hZero :
CocycleEntropyPotential ... 0 = 0` surface.  Compatibility theorems can keep
their `IsConnesCocycle` arguments, but downstream proofs no longer need to
rebuild the zero-normalization proof inline.
-/
theorem cocycleEntropyPotential_zero_of_connesCocycle
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ) :
    CocycleEntropyPotential (H := H) σ u hBridge 0 = 0 := by
  simpa [CocycleEntropyPotential] using
    (cocycleLogPotential_zero (H := H) (σ := σ) (u := u) hCocycle hBridge)

/--
Nat-step cocycle potential matching derived from cocycle law and generator lift.
The zero-time normalization is discharged from `IsConnesCocycle`.
-/
theorem cocycleEntropyPotential_natMatch_of_connesCocycle_generatorLift
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T (CocycleEntropyPotential (H := H) σ u hBridge)) :
    ∀ k : Nat,
      CocycleEntropyPotential (H := H) σ u hBridge k
        = trajectoryRNGeneratorPotential (n := n) T k := by
  exact cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero
    (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge) (T := T)
    hLift
    (cocycleEntropyPotential_zero_of_connesCocycle
      (H := H) (σ := σ) (u := u)
      (hCocycle := hCocycle) (hBridge := hBridge))

/--
Zero-normalized route for generator-lift equivalence.

The integer-time matching equivalence only needs the concrete generator lift and
zero-time normalization of the selected entropy potential; it does not need the
full `IsConnesCocycle` packet.
-/
theorem cocycleGeneratorLift_iff_natMatch_of_cocyclePotential_zero
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hZero : CocycleEntropyPotential (H := H) σ u hBridge 0 = 0) :
    CocycleGeneratorLift n T (CocycleEntropyPotential (H := H) σ u hBridge)
      ↔
    (∀ k : Nat,
      CocycleEntropyPotential (H := H) σ u hBridge k
        = trajectoryRNGeneratorPotential (n := n) T k) := by
  constructor
  · intro hLift
    exact cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero
      (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge) (T := T)
      hLift hZero
  · intro hMatch
    exact cocycleGeneratorLift_of_cocycleEntropyPotential_match
      (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge) (T := T) hMatch

/--
Under a Connes cocycle law, the concrete generator-lift condition is equivalent
to integer-time matching with the canonical trajectory RN-generator potential.

This compatibility wrapper keeps the older `IsConnesCocycle` surface, but now
routes through the zero-normalized theorem above.
-/
theorem cocycleGeneratorLift_iff_natMatch_of_connesCocycle
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ) :
    CocycleGeneratorLift n T (CocycleEntropyPotential (H := H) σ u hBridge)
      ↔
    (∀ k : Nat,
      CocycleEntropyPotential (H := H) σ u hBridge k
        = trajectoryRNGeneratorPotential (n := n) T k) := by
  exact cocycleGeneratorLift_iff_natMatch_of_cocyclePotential_zero
    (n := n) (H := H) (σ := σ) (u := u) (T := T) (hBridge := hBridge)
    (cocycleEntropyPotential_zero_of_connesCocycle
      (H := H) (σ := σ) (u := u)
      (hCocycle := hCocycle) (hBridge := hBridge))

/--
Constructive generator-lift route to the topological Bekenstein bound:
once the cocycle potential increments are identified with the concrete
trajectory RN generator, no separate `IsConnesCocycle` packet is needed for the
bound itself.
-/
theorem topologicalBekensteinBound_of_cocycleGeneratorLift
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T
        (CocycleEntropyPotential (H := H) σ u hBridge)) :
    TopologicalBekensteinBound n T := by
  intro k
  have hle :
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
    rw [hLift k]
    exact abs_trajectoryRNGenerator_le_trajectoryRNBarrier n T k
  exact le_trans (abs_nonneg _) hle

/--
Compatibility wrapper for the older Connes-cocycle theorem surface.  The
`IsConnesCocycle` hypothesis is retained for callers but the proof routes
through the smaller generator-lift theorem above.
-/
theorem topologicalBekensteinBound_of_connesCocycle_generatorLift
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T
        (CocycleEntropyPotential (H := H) σ u hBridge)) :
    TopologicalBekensteinBound n T := by
  have _ : IsConnesCocycle σ u := hCocycle
  exact topologicalBekensteinBound_of_cocycleGeneratorLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge) (hLift := hLift)

/--
Increment-level generator-lift control:
under the concrete generator-lift condition, each cocycle increment is bounded
by the corresponding trajectory RN barrier.  This is the hypothesis-minimal
route; no additive cocycle law is used.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_cocycleGeneratorLift
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T
        (CocycleEntropyPotential (H := H) σ u hBridge)) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  intro k
  rw [hLift k]
  exact abs_trajectoryRNGenerator_le_trajectoryRNBarrier n T k

/--
Compatibility wrapper for the older Connes-cocycle increment-control surface.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_connesCocycle_generatorLift
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T
        (CocycleEntropyPotential (H := H) σ u hBridge)) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  have _ : IsConnesCocycle σ u := hCocycle
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_cocycleGeneratorLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge) (hLift := hLift)

/--
Nat-match route to increment-level control:
if the cocycle entropy potential is already identified on integer times with the
canonical trajectory RN-generator potential, the concrete generator lift is
recovered directly.  No separate `CocycleGeneratorLift` or `IsConnesCocycle`
packet is needed for the increment bound.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_natMatch
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hMatch :
      ∀ k : Nat,
        CocycleEntropyPotential (H := H) σ u hBridge k
          = trajectoryRNGeneratorPotential (n := n) T k) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_cocycleGeneratorLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge)
    (hLift :=
      cocycleGeneratorLift_of_cocycleEntropyPotential_match
        (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge) (T := T) hMatch)

/--
Compatibility wrapper for the older cocycle/nat-match increment-control surface.
The `IsConnesCocycle` argument is retained for named-argument callers, but the
proof routes through the smaller nat-match theorem above.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_connesCocycle_natMatch
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hMatch :
      ∀ k : Nat,
        CocycleEntropyPotential (H := H) σ u hBridge k
          = trajectoryRNGeneratorPotential (n := n) T k) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  have _ : IsConnesCocycle σ u := hCocycle
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_natMatch
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge) (hMatch := hMatch)

/--
Nat-match route to the topological Bekenstein bound:
if the cocycle entropy potential is already identified on integer times with the
canonical trajectory RN-generator potential, the concrete generator lift is
recovered directly.  No `IsConnesCocycle` packet is needed for this bound.
-/
theorem topologicalBekensteinBound_of_natMatch
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hMatch :
      ∀ k : Nat,
        CocycleEntropyPotential (H := H) σ u hBridge k
          = trajectoryRNGeneratorPotential (n := n) T k) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_cocycleGeneratorLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge)
    (hLift :=
      cocycleGeneratorLift_of_cocycleEntropyPotential_match
        (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge) (T := T) hMatch)

/--
Compatibility wrapper for the older cocycle/nat-match theorem surface.  The
`IsConnesCocycle` argument is retained for named-argument callers, but the proof
routes through `topologicalBekensteinBound_of_natMatch`.
-/
theorem topologicalBekensteinBound_of_connesCocycle_natMatch
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hMatch :
      ∀ k : Nat,
        CocycleEntropyPotential (H := H) σ u hBridge k
          = trajectoryRNGeneratorPotential (n := n) T k) :
    TopologicalBekensteinBound n T := by
  have _ : IsConnesCocycle σ u := hCocycle
  exact topologicalBekensteinBound_of_natMatch
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge) (hMatch := hMatch)

/--
Proof-carrying zero-normalized cocycle generator packet.

This bundles the bridge, concrete generator lift, and zero-time normalization
needed for the smallest constructive Bekenstein route in this lane.
-/
structure ZeroNormalizedCocycleGeneratorWitness
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n) where
  hBridge : ScalarCocycleBridge (H := H) σ
  hLift :
    CocycleGeneratorLift n T
      (CocycleEntropyPotential (H := H) σ u hBridge)
  hZero : CocycleEntropyPotential (H := H) σ u hBridge 0 = 0

/--
Zero-normalized witness route to integer-time matching.

This reduces the explicit `hBridge`, `hLift`, and `hZero` hypothesis surface of
`cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero` to one
proof-carrying witness packet.
-/
theorem cocycleEntropyPotential_natMatch_of_zeroNormalizedCocycleGeneratorWitness
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (W : ZeroNormalizedCocycleGeneratorWitness (n := n) (H := H) σ u T) :
    ∀ k : Nat,
      CocycleEntropyPotential (H := H) σ u W.hBridge k
        = trajectoryRNGeneratorPotential (n := n) T k := by
  exact cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero
    (n := n) (H := H) (σ := σ) (u := u) (hBridge := W.hBridge) (T := T)
    W.hLift W.hZero

/--
Zero-normalized witness route to increment-level RN-barrier control.

This removes the explicit `hBridge`, `hLift`, and `hZero` inputs from the
increment bound: one proof-carrying packet supplies the selected cocycle bridge,
the concrete generator lift, and zero-time normalization.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_zeroNormalizedCocycleGeneratorWitness
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (W : ZeroNormalizedCocycleGeneratorWitness (n := n) (H := H) σ u T) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u W.hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u W.hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_cocycleGeneratorLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := W.hBridge) (hLift := W.hLift)

/--
Zero-normalized witness route to the topological Bekenstein bound.

This is the smallest constructive surface behind the older Connes-cocycle
wrapper: one proof-carrying packet supplies the bridge, the concrete generator
lift, and zero-time normalization.
-/
theorem topologicalBekensteinBound_of_zeroNormalizedCocycleGeneratorWitness
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (W : ZeroNormalizedCocycleGeneratorWitness (n := n) (H := H) σ u T) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_natMatch
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := W.hBridge)
    (hMatch :=
      cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero
        (n := n) (H := H) (σ := σ) (u := u) (hBridge := W.hBridge) (T := T)
        W.hLift W.hZero)

/--
Zero-normalized generator-lift route to increment-level RN-barrier control.

Once the selected entropy potential is normalized at zero, the concrete
generator lift supplies the increment bound without a separate
`IsConnesCocycle` packet.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_cocycleGeneratorLift_zero
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T
        (CocycleEntropyPotential (H := H) σ u hBridge))
    (hZero : CocycleEntropyPotential (H := H) σ u hBridge 0 = 0) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_zeroNormalizedCocycleGeneratorWitness
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    { hBridge := hBridge, hLift := hLift, hZero := hZero }

/--
Compatibility wrapper for the older zero-anchored Connes-cocycle increment
control surface. The `IsConnesCocycle` packet is retained for named-argument
callers, but it is used only to derive zero-normalization before routing through
`cocycleIncrement_abs_le_trajectoryRNBarrier_of_cocycleGeneratorLift_zero`.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_connesCocycle_generatorLift_zero
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T
        (CocycleEntropyPotential (H := H) σ u hBridge)) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_zeroNormalizedCocycleGeneratorWitness
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    { hBridge := hBridge
      hLift := hLift
      hZero := cocycleEntropyPotential_zero_of_connesCocycle
        (H := H) (σ := σ) (u := u)
        (hCocycle := hCocycle) (hBridge := hBridge) }

/--
Zero-normalized generator-lift route to the topological Bekenstein bound.

This is the smaller constructive surface behind the older Connes-cocycle wrapper:
once the selected entropy potential is normalized at zero, the concrete generator
lift produces the integer-time match directly.  No `IsConnesCocycle` packet is
needed for this theorem.
-/
theorem topologicalBekensteinBound_of_cocycleGeneratorLift_zero
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T
        (CocycleEntropyPotential (H := H) σ u hBridge))
    (hZero : CocycleEntropyPotential (H := H) σ u hBridge 0 = 0) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_zeroNormalizedCocycleGeneratorWitness
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    { hBridge := hBridge, hLift := hLift, hZero := hZero }

/--
Compatibility wrapper for the older zero-anchored Connes-cocycle theorem surface.
The `IsConnesCocycle` packet is retained for named-argument callers, but it is
used only to derive zero-normalization before routing through
`topologicalBekensteinBound_of_cocycleGeneratorLift_zero`.
-/
theorem topologicalBekensteinBound_of_connesCocycle_generatorLift_zero
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T
        (CocycleEntropyPotential (H := H) σ u hBridge)) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_zeroNormalizedCocycleGeneratorWitness
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    { hBridge := hBridge
      hLift := hLift
      hZero := cocycleEntropyPotential_zero_of_connesCocycle
        (H := H) (σ := σ) (u := u)
        (hCocycle := hCocycle) (hBridge := hBridge) }

/--
Casini-style relative-entropy profile on discrete Sinkhorn steps.
-/
abbrev RelativeEntropyProfile := Nat → ℝ

/--
Casini bridge data: cocycle increment is identified with relative-entropy drop,
and that drop is identified with the concrete phase-aligned RN generator.
-/
structure CasiniIncrementBridge
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile) : Prop where
  cocycle_increment_eq_relEnt_drop :
    ∀ k : Nat,
      CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k
        = relEnt k - relEnt (k + 1)
  relEnt_drop_eq_phaseRN :
    ∀ k : Nat,
      relEnt k - relEnt (k + 1)
        = phaseRNGeneratorBefore n (phaseAt k) (T.state k)
  relEnt_monotone :
    ∀ k : Nat, relEnt (k + 1) ≤ relEnt k

/--
Minimal Casini increment bridge data needed for the generator-lift route.

The older `CasiniIncrementBridge` also carries relative-entropy monotonicity.
That field is only needed for relative-entropy drop nonnegativity; the cocycle
increment route to the RN barrier needs just the two concrete increment
identifications below.
-/
structure MinimalCasiniIncrementBridge
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile) : Prop where
  cocycle_increment_eq_relEnt_drop :
    ∀ k : Nat,
      CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k
        = relEnt k - relEnt (k + 1)
  relEnt_drop_eq_phaseRN :
    ∀ k : Nat,
      relEnt k - relEnt (k + 1)
        = phaseRNGeneratorBefore n (phaseAt k) (T.state k)

/--
Proof-carrying minimal Casini increment packet.

This bundles the cocycle bridge, the selected relative-entropy profile, and the
minimal two-field Casini increment witness needed for the smallest constructive
Casini route to the RN-barrier Bekenstein bound.
-/
structure MinimalCasiniIncrementWitness
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n) where
  hBridge : ScalarCocycleBridge (H := H) σ
  relEnt : RelativeEntropyProfile
  hCasini : MinimalCasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt

/--Recover the minimal Casini increment bridge from the legacy monotone packet. -/
theorem minimalCasiniIncrementBridge_of_casiniIncrementBridge
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    MinimalCasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt where
  cocycle_increment_eq_relEnt_drop := hCasini.cocycle_increment_eq_relEnt_drop
  relEnt_drop_eq_phaseRN := hCasini.relEnt_drop_eq_phaseRN

/--
From minimal Casini bridge data we derive the concrete cocycle generator-lift
condition; no relative-entropy monotonicity field is required.
-/
theorem cocycleGeneratorLift_of_minimalCasiniIncrementBridge
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile)
    (hCasini : MinimalCasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    CocycleGeneratorLift n T (CocycleEntropyPotential (H := H) σ u hBridge) := by
  intro k
  calc
    CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
      - CocycleEntropyPotential (H := H) σ u hBridge k
        = relEnt k - relEnt (k + 1) :=
          hCasini.cocycle_increment_eq_relEnt_drop k
    _ = phaseRNGeneratorBefore n (phaseAt k) (T.state k) :=
          hCasini.relEnt_drop_eq_phaseRN k

/--
From Casini bridge data we derive the concrete cocycle generator-lift condition.
-/
theorem cocycleGeneratorLift_of_casiniIncrementBridge
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    CocycleGeneratorLift n T (CocycleEntropyPotential (H := H) σ u hBridge) := by
  exact cocycleGeneratorLift_of_minimalCasiniIncrementBridge
    (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge)
    (T := T) (relEnt := relEnt)
    (minimalCasiniIncrementBridge_of_casiniIncrementBridge
      (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge)
      (T := T) (relEnt := relEnt) hCasini)

/--
Relative-entropy drops are nonnegative under the Casini monotonicity condition.
-/
theorem relEnt_drop_nonneg_of_casiniIncrementBridge
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    ∀ k : Nat, 0 ≤ relEnt k - relEnt (k + 1) := by
  intro k
  linarith [hCasini.relEnt_monotone k]

/--
Minimal Casini-route increment control: the old increment-bound surface needed a
bare `CocycleGeneratorLift` hypothesis.  On this narrowed relative-entropy
branch the lift is recovered from the two increment-identification fields only;
no additive cocycle, generator-lift, or relative-entropy monotonicity packet is
carried.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_minimalCasiniIncrement
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (relEnt : RelativeEntropyProfile)
    (hCasini : MinimalCasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_cocycleGeneratorLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge)
    (hLift :=
      cocycleGeneratorLift_of_minimalCasiniIncrementBridge
        (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge)
        (T := T) (relEnt := relEnt) hCasini)

/--
Casini-route increment control compatibility wrapper.  The legacy monotone
`CasiniIncrementBridge` packet is retained for named callers, but the proof now
routes through the smaller `MinimalCasiniIncrementBridge` theorem above.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_casiniIncrement
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (relEnt : RelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_minimalCasiniIncrement
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge) (relEnt := relEnt)
    (hCasini :=
      minimalCasiniIncrementBridge_of_casiniIncrementBridge
        (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge)
        (T := T) (relEnt := relEnt) hCasini)

/--
Compatibility wrapper for the Connes/Casini increment-control surface.  The
`IsConnesCocycle` argument is kept for named callers, but the proof now goes
through the constructive Casini bridge rather than a free generator-lift packet.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_connesCocycle_casiniIncrement
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (relEnt : RelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  have _ : IsConnesCocycle σ u := hCocycle
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_casiniIncrement
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge) (relEnt := relEnt) (hCasini := hCasini)

/--
Minimal Casini witness route to cocycle increment control.

This removes the explicit `hBridge`, `relEnt`, and `hCasini` arguments from
`cocycleIncrement_abs_le_trajectoryRNBarrier_of_minimalCasiniIncrement` in
favor of one proof-carrying witness packet.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_minimalCasiniIncrementWitness
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (W : MinimalCasiniIncrementWitness (n := n) (H := H) σ u T) :
    ∀ k : Nat,
      |CocycleEntropyPotential (H := H) σ u W.hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u W.hBridge k|
        ≤ trajectoryRNBarrier n T k := by
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_minimalCasiniIncrement
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := W.hBridge) (relEnt := W.relEnt) (hCasini := W.hCasini)

/--
Minimal Casini-route cocycle-to-bound theorem through a proof-carrying witness
packet.

This is the smallest constructive Casini branch: one witness bundles the bridge,
relative-entropy profile, and the two increment-identification fields needed to
reconstruct the cocycle generator lift and hence the RN-barrier bound.
-/
theorem topologicalBekensteinBound_of_minimalCasiniIncrementWitness
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (W : MinimalCasiniIncrementWitness (n := n) (H := H) σ u T) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_cocycleGeneratorLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := W.hBridge)
    (hLift :=
      cocycleGeneratorLift_of_minimalCasiniIncrementBridge
        (n := n) (H := H) (σ := σ) (u := u) (hBridge := W.hBridge)
        (T := T) (relEnt := W.relEnt) W.hCasini)

/--
Minimal Casini-route cocycle-to-bound theorem: the generator lift is derived
internally from two increment-identification fields.  This branch does not carry
an additive `IsConnesCocycle`, a free `CocycleGeneratorLift`, or the legacy
relative-entropy monotonicity field.
-/
theorem topologicalBekensteinBound_of_minimalCasiniIncrement
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (relEnt : RelativeEntropyProfile)
    (hCasini : MinimalCasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_minimalCasiniIncrementWitness
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    { hBridge := hBridge, relEnt := relEnt, hCasini := hCasini }

/--
Casini-route cocycle-to-bound compatibility wrapper:
`hLift` is derived internally from relative-entropy bridge data.  The legacy
monotone `CasiniIncrementBridge` packet is kept for named callers, but the bound
itself now routes through `topologicalBekensteinBound_of_minimalCasiniIncrement`.
-/
theorem topologicalBekensteinBound_of_casiniIncrement
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (relEnt : RelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_minimalCasiniIncrement
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge) (relEnt := relEnt)
    (hCasini :=
      minimalCasiniIncrementBridge_of_casiniIncrementBridge
        (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge)
        (T := T) (relEnt := relEnt) hCasini)

/--
Compatibility wrapper for the older Casini/Connes theorem surface.  The
`IsConnesCocycle` argument is retained for named-argument callers, but the proof
now routes through `topologicalBekensteinBound_of_casiniIncrement`.
-/
theorem topologicalBekensteinBound_of_connesCocycle_casiniIncrement
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (relEnt : RelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge (n := n) (H := H) σ u hBridge T relEnt) :
    TopologicalBekensteinBound n T := by
  have _ : IsConnesCocycle σ u := hCocycle
  exact topologicalBekensteinBound_of_casiniIncrement
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hBridge := hBridge) (relEnt := relEnt) (hCasini := hCasini)

end CocycleBridge

section TomitaSpecialization

variable (n : Nat)
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
Tomita-specialized cocycle entropy potential driven by the modular-sign flow.
-/
noncomputable abbrev TomitaCocycleEntropyPotential
    (u : ℝ → AlgebraEnd H)
    (hBridge :
      ScalarCocycleBridge (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (t : ℝ) : ℝ :=
  CocycleEntropyPotential (H := H)
    (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    u hBridge t

/--
Tomita-specialized generator-lift route to the Bekenstein bound.

This is the hypothesis-minimal modular-sign branch: once the concrete generator
lift is present, the proof uses the already-owned RN-barrier comparison and does
not carry an explicit `IsConnesCocycle` packet.
-/
theorem topologicalBekensteinBound_of_tomitaGeneratorLift
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hBridge :
      ScalarCocycleBridge (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (hLift :
      CocycleGeneratorLift n T
        (TomitaCocycleEntropyPotential (H := H) u hBridge)) :
    TopologicalBekensteinBound n T := by
  simpa [TomitaCocycleEntropyPotential] using
    topologicalBekensteinBound_of_cocycleGeneratorLift
      (n := n) (H := H)
      (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (u := u) (T := T) (hBridge := hBridge) (hLift := hLift)

/--
Compatibility Tomita/Connes wrapper.  The `IsConnesCocycle` hypothesis is kept
for named-argument callers, but the proof now routes through the smaller
`topologicalBekensteinBound_of_tomitaGeneratorLift` theorem above.
-/
theorem topologicalBekensteinBound_of_tomitaConnesCocycle_generatorLift
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle :
      IsConnesCocycle
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        u)
    (hBridge :
      ScalarCocycleBridge (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (hLift :
      CocycleGeneratorLift n T
        (TomitaCocycleEntropyPotential (H := H) u hBridge)) :
    TopologicalBekensteinBound n T := by
  have _ :
      IsConnesCocycle
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        u := hCocycle
  exact topologicalBekensteinBound_of_tomitaGeneratorLift
    (n := n) (H := H) (u := u) (T := T) (hBridge := hBridge) (hLift := hLift)

/--
Tomita flow-unit generator-lift endpoint on the canonical welded cocycle lane.

This removes the explicit `IsConnesCocycle` and `ScalarCocycleBridge` arguments
from the Tomita generator-lift surface by using the owned flow-unit cocycle and
unit scalar bridge.
-/
theorem topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_generatorLift
    (T : SinkhornTrajectory n)
    (hLift :
      CocycleGeneratorLift n T
        (TomitaCocycleEntropyPotential (H := H)
          (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))))) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_tomitaGeneratorLift
    (n := n) (H := H)
    (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (T := T)
    (hBridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (hLift := hLift)

/--
Tomita-specialized cocycle-to-bound theorem with internally derived generator lift:
it suffices to match integer-time cocycle potential values with the canonical
trajectory RN-generator potential.
-/
theorem topologicalBekensteinBound_of_tomitaConnesCocycle_natMatch
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle :
      IsConnesCocycle
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        u)
    (hBridge :
      ScalarCocycleBridge (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (hMatch :
      ∀ k : Nat,
        TomitaCocycleEntropyPotential (H := H) u hBridge k
          = trajectoryRNGeneratorPotential (n := n) T k) :
    TopologicalBekensteinBound n T := by
  simpa [TomitaCocycleEntropyPotential] using
    topologicalBekensteinBound_of_connesCocycle_natMatch
      (n := n) (H := H)
      (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (u := u) (T := T)
      (hCocycle := hCocycle) (hBridge := hBridge) (hMatch := hMatch)

/--
Tomita-specialized zero-normalized witness route to the topological Bekenstein bound.

This narrows the specialized zero-anchored Tomita lane to the existing
proof-carrying `ZeroNormalizedCocycleGeneratorWitness` packet instead of
rethreading separate bridge, lift, and zero-normalization hypotheses.
-/
theorem topologicalBekensteinBound_of_tomitaZeroNormalizedCocycleGeneratorWitness
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (W : ZeroNormalizedCocycleGeneratorWitness (n := n) (H := H)
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      u T) :
    TopologicalBekensteinBound n T := by
  simpa [TomitaCocycleEntropyPotential] using
    topologicalBekensteinBound_of_zeroNormalizedCocycleGeneratorWitness
      (n := n) (H := H)
      (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (u := u) (T := T) (W := W)

/--
Tomita-specialized zero-anchored cocycle-to-bound theorem.
-/
theorem topologicalBekensteinBound_of_tomitaConnesCocycle_generatorLift_zero
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle :
      IsConnesCocycle
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        u)
    (hBridge :
      ScalarCocycleBridge (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (hLift :
      CocycleGeneratorLift n T
        (TomitaCocycleEntropyPotential (H := H) u hBridge)) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_tomitaZeroNormalizedCocycleGeneratorWitness
    (n := n) (H := H) (u := u) (T := T)
    { hBridge := hBridge
      hLift := hLift
      hZero := cocycleEntropyPotential_zero_of_connesCocycle
        (H := H)
        (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (u := u)
        (hCocycle := hCocycle) (hBridge := hBridge) }

/--
Tomita-specialized Casini-route cocycle-to-bound theorem.
-/
theorem topologicalBekensteinBound_of_tomitaConnesCocycle_casiniIncrement
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle :
      IsConnesCocycle
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        u)
    (hBridge :
      ScalarCocycleBridge (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (relEnt : RelativeEntropyProfile)
    (hCasini :
      CasiniIncrementBridge (n := n) (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        u hBridge T relEnt) :
    TopologicalBekensteinBound n T := by
  simpa [TomitaCocycleEntropyPotential] using
    topologicalBekensteinBound_of_connesCocycle_casiniIncrement
      (n := n) (H := H)
      (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (u := u) (T := T) (hCocycle := hCocycle) (hBridge := hBridge)
      (relEnt := relEnt) (hCasini := hCasini)

/--
Tomita-specialized nat-match endpoint on the canonical flow-unit cocycle lane.

This discharges both the explicit `IsConnesCocycle` witness and the scalar bridge
packet by using the canonical flow-unit cocycle and unit scalar bridge.
-/
theorem topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_natMatch
    (T : SinkhornTrajectory n)
    (hMatch :
      ∀ k : Nat,
        TomitaCocycleEntropyPotential (H := H)
          (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          k
          = trajectoryRNGeneratorPotential (n := n) T k) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_tomitaConnesCocycle_natMatch
    (n := n) (H := H)
    (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (T := T)
    (hCocycle := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_isConnesCocycle
      (H := H)
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (hBridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (hMatch := hMatch)

/--
Tomita-specialized Casini-route endpoint on the canonical flow-unit cocycle
lane.

This discharges the cocycle witness from the welded Tomita flow surface and
keeps only the Casini bridge as input data.
-/
theorem topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_casiniIncrement
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile)
    (hCasini :
      CasiniIncrementBridge (n := n) (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        T relEnt) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_tomitaConnesCocycle_casiniIncrement
    (n := n) (H := H)
    (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (T := T)
    (hCocycle := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_isConnesCocycle
      (H := H)
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (hBridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (relEnt := relEnt)
    (hCasini := hCasini)

/--
Tomita flow-unit endpoint through the minimal Casini increment packet.

This is the narrowed constructive branch beneath
`topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_casiniIncrement`:
it uses the owned Tomita flow-unit cocycle and unit scalar bridge, and it no
longer carries the legacy `relEnt_monotone` field from `CasiniIncrementBridge`.
The two increment-identification fields in `MinimalCasiniIncrementBridge` are
enough to reconstruct the generator lift and hence the RN-barrier bound.
-/
structure TomitaFlowUnitMinimalCasiniWitness
    (T : SinkhornTrajectory n) where
  relEnt : RelativeEntropyProfile
  hCasini :
    MinimalCasiniIncrementBridge (n := n) (H := H)
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
      (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
      T relEnt

/--
Tomita flow-unit endpoint through a proof-carrying minimal Casini witness.

This removes the explicit `{relEnt, hCasini}` pair on the canonical Tomita
flow-unit lane while keeping the older specialized theorem as a compatibility
wrapper.
-/
theorem topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_minimalCasiniWitness
    (T : SinkhornTrajectory n)
    (W : TomitaFlowUnitMinimalCasiniWitness (n := n) (H := H) T) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_minimalCasiniIncrement
    (n := n) (H := H)
    (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (T := T)
    (hBridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (relEnt := W.relEnt)
    (hCasini := W.hCasini)

/--
Tomita flow-unit endpoint through the minimal Casini increment packet.

This is the narrowed constructive branch beneath
`topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_casiniIncrement`:
it uses the owned Tomita flow-unit cocycle and unit scalar bridge, and it no
longer carries the legacy `relEnt_monotone` field from `CasiniIncrementBridge`.
The two increment-identification fields in `MinimalCasiniIncrementBridge` are
enough to reconstruct the generator lift and hence the RN-barrier bound.
-/
theorem topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_minimalCasiniIncrement
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile)
    (hCasini :
      MinimalCasiniIncrementBridge (n := n) (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        T relEnt) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_minimalCasiniWitness
    (n := n) (H := H) (T := T)
    { relEnt := relEnt, hCasini := hCasini }

/--
Tomita flow-unit endpoint for increment control through the minimal Casini
packet.  This is the increment-level companion to
`topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_minimalCasiniIncrement`:
it discharges the explicit Tomita `IsConnesCocycle`, scalar-bridge, free
`CocycleGeneratorLift`, and legacy `relEnt_monotone` fields, leaving only the
minimal two-field Casini increment identification.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_tomitaFlowUnitConnesCocycle_minimalCasiniIncrement
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile)
    (hCasini :
      MinimalCasiniIncrementBridge (n := n) (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        T relEnt) :
    ∀ k : Nat,
      |TomitaCocycleEntropyPotential (H := H)
          (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          (k + 1)
        - TomitaCocycleEntropyPotential (H := H)
          (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          k|
        ≤ trajectoryRNBarrier n T k := by
  simpa [TomitaCocycleEntropyPotential] using
    cocycleIncrement_abs_le_trajectoryRNBarrier_of_minimalCasiniIncrement
      (n := n) (H := H)
      (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
      (T := T)
      (hBridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
      (relEnt := relEnt)
      (hCasini := hCasini)

/--
Tomita flow-unit endpoint for increment control from the legacy Casini packet.

This compatibility theorem keeps the broad `CasiniIncrementBridge` input for
callers, but its proof immediately descends to
`MinimalCasiniIncrementBridge`; the explicit Tomita cocycle witness, scalar
bridge, free `CocycleGeneratorLift`, and direct use of the legacy
`relEnt_monotone` field are all avoided on the increment-control route.
-/
theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_tomitaFlowUnitConnesCocycle_casiniIncrement
    (T : SinkhornTrajectory n)
    (relEnt : RelativeEntropyProfile)
    (hCasini :
      CasiniIncrementBridge (n := n) (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        T relEnt) :
    ∀ k : Nat,
      |TomitaCocycleEntropyPotential (H := H)
          (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          (k + 1)
        - TomitaCocycleEntropyPotential (H := H)
          (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
            (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
          k|
        ≤ trajectoryRNBarrier n T k := by
  exact cocycleIncrement_abs_le_trajectoryRNBarrier_of_tomitaFlowUnitConnesCocycle_minimalCasiniIncrement
    (n := n) (H := H) (T := T) (relEnt := relEnt)
    (hCasini :=
      minimalCasiniIncrementBridge_of_casiniIncrementBridge
        (n := n) (H := H)
        (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        (hBridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        (T := T) (relEnt := relEnt) hCasini)

end TomitaSpecialization

end InfoGeometry.Canonical.BekensteinBound
