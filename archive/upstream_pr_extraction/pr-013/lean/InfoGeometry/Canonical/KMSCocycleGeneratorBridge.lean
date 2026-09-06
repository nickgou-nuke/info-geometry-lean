import InfoGeometry.Canonical.BekensteinBound
import InfoGeometry.Canonical.SinkhornKMSCore

/-!
# InfoGeometry.Canonical.KMSCocycleGeneratorBridge

Bridge from exact Sinkhorn-step KMS closure to the cocycle generator-lift lane.

This file isolates the missing "entropy-time weld" as a concrete witness surface:
if cocycle increments and phase generators are represented by opposite KMS pairing
defects, then exact KMS closure forces the concrete cocycle generator lift.
-/

namespace InfoGeometry.Canonical.KMSCocycleBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.BekensteinBound
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Volume.ConnesCocycle

section Core

variable (n : Nat)
variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
KMS pairing witness for the cocycle/phase corridor:
- cocycle increment is represented by a forward KMS pairing defect;
- phase RN generator is represented by the corresponding backward defect.
-/
structure KMSPairingWitness
    (T : SinkhornTrajectory n)
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd E)
    (bridge : ScalarCocycleBridge (H := E) σ)
    (K : KMSSinkhornBridge.AlgebraEnd E)
    (ω : Nat → KMSSinkhornBridge.AlgebraEnd E →L[ℝ] ℝ)
    (β : ℝ) where
  leftObs : Nat → KMSSinkhornBridge.AlgebraEnd E
  rightObs : Nat → KMSSinkhornBridge.AlgebraEnd E
  cocycle_increment_eq_forward :
    ∀ k : Nat,
      CocycleEntropyPotential (H := E) σ u bridge (k + 1)
        - CocycleEntropyPotential (H := E) σ u bridge k
        =
      ω (k + 1) (leftObs k * modularShift (E := E) K β (rightObs k))
        - ω (k + 1) (rightObs k * leftObs k)
  phase_eq_backward :
    ∀ k : Nat,
      phaseRNGeneratorBefore n (phaseAt k) (T.state k)
        =
      ω (k + 1) (rightObs k * leftObs k)
        - ω (k + 1) (leftObs k * modularShift (E := E) K β (rightObs k))

/--
Exact Sinkhorn-step KMS closure plus a pairing witness yields the concrete
cocycle generator-lift identity.
-/
theorem cocycleGeneratorLift_of_sinkhornKMSClosure_pairingWitness
    (T : SinkhornTrajectory n)
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd E)
    (bridge : ScalarCocycleBridge (H := E) σ)
    (K : KMSSinkhornBridge.AlgebraEnd E)
    (ω : Nat → KMSSinkhornBridge.AlgebraEnd E →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure (F := E) n T K ω β)
    (hPair : KMSPairingWitness
      (n := n) (E := E) T σ u bridge K ω β) :
    CocycleGeneratorLift n T (CocycleEntropyPotential (H := E) σ u bridge) := by
  intro k
  let A := hPair.leftObs k
  let B := hPair.rightObs k
  have hEq : ω (k + 1) (A * modularShift (E := E) K β B) = ω (k + 1) (B * A) :=
    hClosure k A B
  have hForwardZero :
      ω (k + 1) (A * modularShift (E := E) K β B) - ω (k + 1) (B * A) = 0 :=
    sub_eq_zero.mpr hEq
  have hBackwardZero :
      ω (k + 1) (B * A) - ω (k + 1) (A * modularShift (E := E) K β B) = 0 := by
    linarith [hEq]
  calc
    CocycleEntropyPotential (H := E) σ u bridge (k + 1)
      - CocycleEntropyPotential (H := E) σ u bridge k
        =
      ω (k + 1) (A * modularShift (E := E) K β B) - ω (k + 1) (B * A) := by
          simpa [A, B] using hPair.cocycle_increment_eq_forward k
    _ = 0 := hForwardZero
    _ = ω (k + 1) (B * A) - ω (k + 1) (A * modularShift (E := E) K β B) := by
          simpa using hBackwardZero.symm
    _ = phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
          simpa [A, B] using (hPair.phase_eq_backward k).symm

/--
Control-form variant:
Sinkhorn KMS control first closes to exact stepwise KMS, then yields the same
cocycle generator-lift conclusion under the pairing witness.
-/
theorem cocycleGeneratorLift_of_sinkhornKMSControl_pairingWitness
    (T : SinkhornTrajectory n)
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd E)
    (bridge : ScalarCocycleBridge (H := E) σ)
    (K : KMSSinkhornBridge.AlgebraEnd E)
    (ω : Nat → KMSSinkhornBridge.AlgebraEnd E →L[ℝ] ℝ)
    (β : ℝ)
    (hControl : SinkhornKMSControl n T K ω β)
    (hPair : KMSPairingWitness
      (n := n) (E := E) T σ u bridge K ω β) :
    CocycleGeneratorLift n T (CocycleEntropyPotential (H := E) σ u bridge) := by
  have hClosure : SinkhornKMSClosure (F := E) n T K ω β :=
    sinkhorn_step_kmsClosure_of_control
      (n := n) (T := T) (K := K) (ω := ω) (β := β) hControl
  exact cocycleGeneratorLift_of_sinkhornKMSClosure_pairingWitness
    (n := n) (E := E)
    (T := T) (σ := σ) (u := u) (bridge := bridge)
    (K := K) (ω := ω) (β := β)
    hClosure hPair

/--
Cocycle law + exact Sinkhorn-step KMS closure + pairing witness imply the
topological Bekenstein bound.
-/
theorem topologicalBekensteinBound_of_connesCocycle_and_sinkhornKMSClosure_pairingWitness
    (T : SinkhornTrajectory n)
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd E)
    (hCocycle : IsConnesCocycle σ u)
    (bridge : ScalarCocycleBridge (H := E) σ)
    (K : KMSSinkhornBridge.AlgebraEnd E)
    (ω : Nat → KMSSinkhornBridge.AlgebraEnd E →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure (F := E) n T K ω β)
    (hPair : KMSPairingWitness
      (n := n) (E := E) T σ u bridge K ω β) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_connesCocycle_generatorLift
    (n := n) (H := E)
    (σ := σ) (u := u) (T := T)
    (hCocycle := hCocycle) (hBridge := bridge)
    (hLift :=
      cocycleGeneratorLift_of_sinkhornKMSClosure_pairingWitness
        (n := n) (E := E)
        (T := T) (σ := σ) (u := u) (bridge := bridge)
        (K := K) (ω := ω) (β := β)
        hClosure hPair)

/--
Control-form Bekenstein endpoint:
Connes cocycle law plus Sinkhorn KMS control and the pairing witness imply the
topological Bekenstein bound.
-/
theorem topologicalBekensteinBound_of_connesCocycle_and_sinkhornKMSControl_pairingWitness
    (T : SinkhornTrajectory n)
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd E)
    (hCocycle : IsConnesCocycle σ u)
    (bridge : ScalarCocycleBridge (H := E) σ)
    (K : KMSSinkhornBridge.AlgebraEnd E)
    (ω : Nat → KMSSinkhornBridge.AlgebraEnd E →L[ℝ] ℝ)
    (β : ℝ)
    (hControl : SinkhornKMSControl n T K ω β)
    (hPair : KMSPairingWitness
      (n := n) (E := E) T σ u bridge K ω β) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_connesCocycle_generatorLift
    (n := n) (H := E)
    (σ := σ) (u := u) (T := T)
    (hCocycle := hCocycle) (hBridge := bridge)
    (hLift :=
      cocycleGeneratorLift_of_sinkhornKMSControl_pairingWitness
        (n := n) (E := E)
        (T := T) (σ := σ) (u := u) (bridge := bridge)
        (K := K) (ω := ω) (β := β)
        hControl hPair)

end Core

end InfoGeometry.Canonical.KMSCocycleBridge
