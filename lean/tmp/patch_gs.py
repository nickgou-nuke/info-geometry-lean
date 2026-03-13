import re

with open('lean/InfoGeometry/Canonical/GrandSynthesis.lean', 'r') as f:
    content = f.read()

# Replacement 1: sinkhornStepwise_kmsResidual_le_entropyBarrier
old_1 = """theorem sinkhornStepwise_kmsResidual_le_entropyBarrier
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k)) :
    ∀ k : Nat, ∀ A B : AlgebraEnd F,
      kmsResidual K ((ibInducedObservable (F := F) prob pTrajectory) (k + 1)) β A B
        ≤ trajectoryRNBarrier n T k := by
  have hControl :
      SinkhornKMSControl n T K (ibInducedObservable (F := F) prob pTrajectory) β :=
    sinkhorn_kmsControl_of_ibDynamics_concrete
      (n := n) (T := T) (K := K) (β := β)
      (prob := prob) (pTrajectory := pTrajectory) hStep
  exact sinkhorn_stepwise_kms_bound
    (n := n) (T := T) (K := K)
    (ω := ibInducedObservable (F := F) prob pTrajectory) (β := β) hControl"""

new_1 = """theorem sinkhornStepwise_kmsResidual_le_entropyBarrier
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (x0 : Xib) (t0 : Tib)
    (vac : ThermalVacuum (E := F) K)
    (hStruct : ExpectationSeedKMSHypotheses (F := F) K β vac.Omega) :
    ∀ k : Nat, ∀ A B : AlgebraEnd F,
      kmsResidual K ((ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) (k + 1)) β A B
        ≤ trajectoryRNBarrier n T k := by
  have hControl :
      SinkhornKMSControl n T K (ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β :=
    sinkhorn_kmsControl_of_ibDynamics_weighted_from_thermalVacuum
      (n := n) (T := T) (K := K) (β := β)
      (prob := prob) (pTrajectory := pTrajectory) hStep (x0 := x0) (t0 := t0) vac hStruct
  exact sinkhorn_stepwise_kms_bound
    (n := n) (T := T) (K := K)
    (ω := ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) (β := β) hControl"""

# Replacement 2: bochnerWeitzenboeckBridge_of_ibDynamics
old_2 = """theorem bochnerWeitzenboeckBridge_of_ibDynamics
    [FiniteDimensional ℝ V]
    (n : Nat)
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k)) :
    GeometricAlgebraicState n T flow D Γ →
      ThermodynamicKMSState n T K (ibInducedObservable (F := F) prob pTrajectory) β := by
  have hControl :
      SinkhornKMSControl n T.traj K (ibInducedObservable (F := F) prob pTrajectory) β :=
    sinkhorn_kmsControl_of_ibDynamics_concrete
      (n := n) (T := T.traj) (K := K) (β := β)
      (prob := prob) (pTrajectory := pTrajectory) hStep
  have hClosure :
      SinkhornKMSClosure n T.traj K (ibInducedObservable (F := F) prob pTrajectory) β :=
    sinkhorn_step_kmsClosure_of_control
      (n := n) (T := T.traj) (K := K)
      (ω := ibInducedObservable (F := F) prob pTrajectory) (β := β) hControl
  intro _hGeoAlg
  exact hClosure"""

new_2 = """theorem bochnerWeitzenboeckBridge_of_ibDynamics
    [FiniteDimensional ℝ V]
    (n : Nat)
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (x0 : Xib) (t0 : Tib)
    (vac : ThermalVacuum (E := F) K)
    (hStruct : ExpectationSeedKMSHypotheses (F := F) K β vac.Omega) :
    GeometricAlgebraicState n T flow D Γ →
      ThermodynamicKMSState n T K (ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β := by
  have hControl :
      SinkhornKMSControl n T.traj K (ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β :=
    sinkhorn_kmsControl_of_ibDynamics_weighted_from_thermalVacuum
      (n := n) (T := T.traj) (K := K) (β := β)
      (prob := prob) (pTrajectory := pTrajectory) hStep (x0 := x0) (t0 := t0) vac hStruct
  have hClosure :
      SinkhornKMSClosure n T.traj K (ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β :=
    sinkhorn_step_kmsClosure_of_control
      (n := n) (T := T.traj) (K := K)
      (ω := ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) (β := β) hControl
  intro _hGeoAlg
  exact hClosure"""

# Replacement 3: directionalBridges_of_ibDynamics_and_indexHypotheses
old_3 = """theorem directionalBridges_of_ibDynamics_and_indexHypotheses
    [FiniteDimensional ℝ V]
    (n : Nat)
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hD : indexInvariantAlong_of_chiralParts_eq (V := V) D Γ)
    (hΓ : ∀ s, (Γ s).comp (Γ s) = LinearMap.id) :
    (GeometricAlgebraicState n T flow D Γ →
      ThermodynamicKMSState n T K (ibInducedObservable (F := F) prob pTrajectory) β) ∧
    (ThermodynamicKMSState n T K (ibInducedObservable (F := F) prob pTrajectory) β →
      GeometricAlgebraicState n T flow D Γ) := by
  constructor
  · exact bochnerWeitzenboeckBridge_of_ibDynamics
      (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
      (K := K) (β := β) (prob := prob) (pTrajectory := pTrajectory) hStep
  · intro _hThermo
    exact calabiYauEntropyBridge_of_sinkhornRicciIndexHypotheses
      (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
      hNorm hFixed hD hΓ"""

new_3 = """theorem directionalBridges_of_ibDynamics_and_indexHypotheses
    [FiniteDimensional ℝ V]
    (n : Nat)
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (x0 : Xib) (t0 : Tib)
    (vac : ThermalVacuum (E := F) K)
    (hStruct : ExpectationSeedKMSHypotheses (F := F) K β vac.Omega)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hD : indexInvariantAlong_of_chiralParts_eq (V := V) D Γ)
    (hΓ : ∀ s, (Γ s).comp (Γ s) = LinearMap.id) :
    (GeometricAlgebraicState n T flow D Γ →
      ThermodynamicKMSState n T K (ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β) ∧
    (ThermodynamicKMSState n T K (ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β →
      GeometricAlgebraicState n T flow D Γ) := by
  constructor
  · exact bochnerWeitzenboeckBridge_of_ibDynamics
      (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
      (K := K) (β := β) (prob := prob) (pTrajectory := pTrajectory) hStep (x0 := x0) (t0 := t0) vac hStruct
  · intro _hThermo
    exact calabiYauEntropyBridge_of_sinkhornRicciIndexHypotheses
      (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
      hNorm hFixed hD hΓ"""

# Replacement 4: wheelerDeWittEquivalence_of_ibDynamics
old_4 = """theorem wheelerDeWittEquivalence_of_ibDynamics
    [FiniteDimensional ℝ V]
    (n : Nat)
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (hGeoAlg : GeometricAlgebraicState n T flow D Γ)
    :
    ThermodynamicKMSState n T K (ibInducedObservable (F := F) prob pTrajectory) β
      ↔ GeometricAlgebraicState n T flow D Γ := by
  have hControl :
      SinkhornKMSControl n T.traj K (ibInducedObservable (F := F) prob pTrajectory) β :=
    sinkhorn_kmsControl_of_ibDynamics_concrete
      (n := n) (T := T.traj) (K := K) (β := β)
      (prob := prob) (pTrajectory := pTrajectory) hStep
  have hClosure :
      SinkhornKMSClosure n T.traj K (ibInducedObservable (F := F) prob pTrajectory) β :=
    sinkhorn_step_kmsClosure_of_control
      (n := n) (T := T.traj) (K := K)
      (ω := ibInducedObservable (F := F) prob pTrajectory) (β := β) hControl
  constructor
  · intro _hThermo
    exact hGeoAlg
  · intro _hGeo
    exact hClosure"""

new_4 = """theorem wheelerDeWittEquivalence_of_ibDynamics
    [FiniteDimensional ℝ V]
    (n : Nat)
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (x0 : Xib) (t0 : Tib)
    (vac : ThermalVacuum (E := F) K)
    (hStruct : ExpectationSeedKMSHypotheses (F := F) K β vac.Omega)
    (hGeoAlg : GeometricAlgebraicState n T flow D Γ)
    :
    ThermodynamicKMSState n T K (ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β
      ↔ GeometricAlgebraicState n T flow D Γ := by
  have hControl :
      SinkhornKMSControl n T.traj K (ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β :=
    sinkhorn_kmsControl_of_ibDynamics_weighted_from_thermalVacuum
      (n := n) (T := T.traj) (K := K) (β := β)
      (prob := prob) (pTrajectory := pTrajectory) hStep (x0 := x0) (t0 := t0) vac hStruct
  have hClosure :
      SinkhornKMSClosure n T.traj K (ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) β :=
    sinkhorn_step_kmsClosure_of_control
      (n := n) (T := T.traj) (K := K)
      (ω := ibInducedObservableWeighted (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib) pTrajectory x0 t0 (omegaSeed (F := F) vac.Omega)) (β := β) hControl
  constructor
  · intro _hThermo
    exact hGeoAlg
  · intro _hGeo
    exact hClosure"""

content = content.replace(old_1, new_1)
content = content.replace(old_2, new_2)
content = content.replace(old_3, new_3)
content = content.replace(old_4, new_4)

with open('lean/InfoGeometry/Canonical/GrandSynthesis.lean', 'w') as f:
    f.write(content)
