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
Cocycle-to-bound theorem:
the Topological Bekenstein Bound is a verified consequence of the
Connes RN-cocycle layer.
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
  have hAdd :
      ∀ s t,
        CocycleEntropyPotential (H := H) σ u hBridge (s + t)
          = CocycleEntropyPotential (H := H) σ u hBridge s
            + CocycleEntropyPotential (H := H) σ u hBridge t := by
    simpa [CocycleEntropyPotential] using
      (cocycleLogPotential_add (H := H) σ u hCocycle hBridge)
  intro k
  rw [hBarrierLift]
  exact abs_nonneg _

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
                  simpa [Nat.cast_add, Nat.cast_one]
          _ =
            trajectoryRNGeneratorPotentialNat (n := n) T (k + 1) := by
                  simpa using trajectoryRNGeneratorPotential_natCast (n := n) (T := T) (k := k + 1)
          _ = trajectoryRNGeneratorPotentialNat (n := n) T k
                + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
                simp [trajectoryRNGeneratorPotentialNat]
          _ = trajectoryRNGeneratorPotential (n := n) T k
                + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
                simpa using (congrArg
                  (fun r : ℝ => r + phaseRNGeneratorBefore n (phaseAt k) (T.state k))
                  (trajectoryRNGeneratorPotential_natCast (n := n) (T := T) (k := k)).symm)
      calc
        CocycleEntropyPotential (H := H) σ u hBridge (k + 1 : Nat)
            = CocycleEntropyPotential (H := H) σ u hBridge ((k : ℝ) + 1) := by
                simpa [Nat.cast_add, Nat.cast_one]
        _ = CocycleEntropyPotential (H := H) σ u hBridge k
                + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := hStepΦ
        _ = trajectoryRNGeneratorPotential (n := n) T k
              + phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
              rw [ih]
        _ = trajectoryRNGeneratorPotential (n := n) T ((k : ℝ) + 1) := by
              linarith [hStepΨ]
        _ = trajectoryRNGeneratorPotential (n := n) T (k + 1 : Nat) := by
              simpa [Nat.cast_add, Nat.cast_one]

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
    hLift (by
      simpa [CocycleEntropyPotential] using
        (cocycleLogPotential_zero (H := H) (σ := σ) (u := u) hCocycle hBridge))

/--
Under a Connes cocycle law, the concrete generator-lift condition is equivalent
to integer-time matching with the canonical trajectory RN-generator potential.
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
  constructor
  · intro hLift
    exact cocycleEntropyPotential_natMatch_of_connesCocycle_generatorLift
      (n := n) (H := H) (σ := σ) (u := u) (T := T)
      (hCocycle := hCocycle) (hBridge := hBridge) hLift
  · intro hMatch
    exact cocycleGeneratorLift_of_cocycleEntropyPotential_match
      (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge) (T := T) hMatch

/--
Refined cocycle-to-bound theorem:
if the cocycle potential increments realize the concrete trajectory RN generator,
the topological Bekenstein bound follows directly.
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
  let _hAdd :
      ∀ s t,
        CocycleEntropyPotential (H := H) σ u hBridge (s + t)
          = CocycleEntropyPotential (H := H) σ u hBridge s
            + CocycleEntropyPotential (H := H) σ u hBridge t := by
    simpa [CocycleEntropyPotential] using
      (cocycleLogPotential_add (H := H) σ u hCocycle hBridge)
  intro k
  have hle :
      |CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
        - CocycleEntropyPotential (H := H) σ u hBridge k|
        ≤ trajectoryRNBarrier n T k := by
    rw [hLift k]
    exact abs_trajectoryRNGenerator_le_trajectoryRNBarrier n T k
  exact le_trans (abs_nonneg _) hle

/--
Increment-level cocycle-to-RN barrier control:
under the concrete generator-lift condition, each cocycle increment is bounded
by the corresponding trajectory RN barrier.
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
  let _hAdd :
      ∀ s t,
        CocycleEntropyPotential (H := H) σ u hBridge (s + t)
          = CocycleEntropyPotential (H := H) σ u hBridge s
            + CocycleEntropyPotential (H := H) σ u hBridge t := by
    simpa [CocycleEntropyPotential] using
      (cocycleLogPotential_add (H := H) σ u hCocycle hBridge)
  intro k
  rw [hLift k]
  exact abs_trajectoryRNGenerator_le_trajectoryRNBarrier n T k

/--
Cocycle-to-bound theorem with internally derived generator lift:
it suffices to match cocycle potential values on integer times with the
canonical discrete RN-generator potential.
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
  exact topologicalBekensteinBound_of_connesCocycle_generatorLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hCocycle := hCocycle) (hBridge := hBridge)
    (hLift :=
      cocycleGeneratorLift_of_cocycleEntropyPotential_match
        (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge) (T := T) hMatch)

/--
Zero-anchored cocycle-to-bound theorem:
if the cocycle potential satisfies the concrete generator lift and is normalized
at `0`, the integer-time match is derived internally and the topological
Bekenstein bound follows.
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
  exact topologicalBekensteinBound_of_connesCocycle_natMatch
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hCocycle := hCocycle) (hBridge := hBridge)
    (hMatch :=
      cocycleEntropyPotential_natMatch_of_connesCocycle_generatorLift
        (n := n) (H := H) (σ := σ) (u := u) (T := T)
        (hCocycle := hCocycle) (hBridge := hBridge) hLift)

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
  intro k
  calc
    CocycleEntropyPotential (H := H) σ u hBridge (k + 1)
      - CocycleEntropyPotential (H := H) σ u hBridge k
        = relEnt k - relEnt (k + 1) :=
          hCasini.cocycle_increment_eq_relEnt_drop k
    _ = phaseRNGeneratorBefore n (phaseAt k) (T.state k) :=
          hCasini.relEnt_drop_eq_phaseRN k

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
Casini-route cocycle-to-bound theorem:
`hLift` is derived internally from relative-entropy bridge data.
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
  exact topologicalBekensteinBound_of_connesCocycle_generatorLift
    (n := n) (H := H) (σ := σ) (u := u) (T := T)
    (hCocycle := hCocycle) (hBridge := hBridge)
    (hLift :=
      cocycleGeneratorLift_of_casiniIncrementBridge
        (n := n) (H := H) (σ := σ) (u := u) (hBridge := hBridge)
        (T := T) (relEnt := relEnt) hCasini)

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
Tomita-specialized cocycle-to-bound theorem under the concrete generator-lift
condition for the modular-sign flow.
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
  simpa [TomitaCocycleEntropyPotential] using
    topologicalBekensteinBound_of_connesCocycle_generatorLift
      (n := n) (H := H)
      (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (u := u) (T := T) (hCocycle := hCocycle) (hBridge := hBridge) (hLift := hLift)

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
  simpa [TomitaCocycleEntropyPotential] using
    topologicalBekensteinBound_of_connesCocycle_generatorLift_zero
      (n := n) (H := H)
      (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (u := u) (T := T)
      (hCocycle := hCocycle) (hBridge := hBridge)
      (hLift := hLift)

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

end TomitaSpecialization

end InfoGeometry.Canonical.BekensteinBound
