import InfoGeometry.Inference.PoissonSinkhornLyapunov

open InfoGeometry.Canonical.MoE

namespace InfoGeometry.Inference

def lyapunovSmokeMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then 1 else 2
    else if j = 0 then 3 else 4

def lyapunovSmokeRowPositive : HasPositiveRowSums 2 lyapunovSmokeMatrix := by
  intro i
  fin_cases i <;> norm_num [HasPositiveRowSums, rowSum, lyapunovSmokeMatrix]

noncomputable def lyapunovSmokeRowNormalized : Matrix (Fin 2) (Fin 2) ℝ :=
  rowNormalize 2 lyapunovSmokeMatrix lyapunovSmokeRowPositive

example :
    poissonSinkhornStep SinkhornPhase.row
      lyapunovSmokeMatrix lyapunovSmokeRowNormalized :=
  ⟨lyapunovSmokeRowPositive, rfl⟩

example :
    phaseLyapunovAfter 2 SinkhornPhase.row lyapunovSmokeRowNormalized ≤
      phaseLyapunovBefore 2 SinkhornPhase.row lyapunovSmokeMatrix :=
  poissonSinkhornStep_lyapunov_nonincrease
    (M := lyapunovSmokeMatrix)
    (M' := lyapunovSmokeRowNormalized)
    ⟨lyapunovSmokeRowPositive, rfl⟩

example :
    phaseRNBarrierAfter 2 SinkhornPhase.row lyapunovSmokeRowNormalized ≤
      phaseRNBarrierBefore 2 SinkhornPhase.row lyapunovSmokeMatrix :=
  poissonSinkhornStep_rnBarrier_nonincrease
    (M := lyapunovSmokeMatrix)
    (M' := lyapunovSmokeRowNormalized)
    ⟨lyapunovSmokeRowPositive, rfl⟩

end InfoGeometry.Inference
