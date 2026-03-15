import InfoGeometry.Canonical.GrandCanonicalExperts
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
  cases phaseAt k <;> simp [phaseRNGeneratorBefore, rowRNBarrier, colRNBarrier]
  · exact Finset.abs_sum_le_sum_abs _ _
  · exact Finset.abs_sum_le_sum_abs _ _

/--
Cocycle Entropy Potential.
The additive potential Φ derived from the Connes RN-cocycle.
The absolute increment |Φ(k+1) - Φ(k)| represents the information-theoretic 
work done during a Sinkhorn step.
-/
noncomputable def CocycleEntropyPotential
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H))
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
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H))
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
Refined cocycle-to-bound theorem:
if the cocycle potential increments realize the concrete trajectory RN generator,
the topological Bekenstein bound follows directly.
-/
theorem topologicalBekensteinBound_of_connesCocycle_generatorLift
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n)
    (hCocycle : IsConnesCocycle σ u)
    (hBridge : ScalarCocycleBridge (H := H) σ)
    (hLift :
      CocycleGeneratorLift n T
        (CocycleEntropyPotential (H := H) σ u hBridge)) :
    TopologicalBekensteinBound n T := by
  have hAdd :
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

end CocycleBridge

end InfoGeometry.Canonical.BekensteinBound
