import InfoGeometry.Canonical.IBFrozenDescent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RelativePotentialScalarBridge

/-!
# InfoGeometry.Canonical.IBFrozenModularBridge

Frozen Information Bottleneck slice rewritten in canonical modular-potential
language.

The foundational quantity is the negative logarithmic Radon-Nikodym derivative
of the BA-updated slice relative to the frozen prior `qT`. The frozen partition
function appears only as the additive gauge-normalization term.
-/

open scoped BigOperators ENNReal NNReal

namespace InfoGeometry.Canonical.IB

open InfoGeometry.MaxEnt.Finite

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

section FrozenModular

variable [DecidableEq T]

private theorem ibBlahutArimotoStepFrozen_toReal_eq_frozenSliceGibbsProb
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (x : X) (t : T) :
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    let hZ : J.partition lam ≠ 0 :=
      frozenSliceJaynes_partition_one_ne_zero
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
    ((ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal
      = J.gibbsProb lam hZ t := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  let hZ : J.partition lam ≠ 0 :=
    frozenSliceJaynes_partition_one_ne_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hfun :
      ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT x
        =
      ibBlahutArimotoStepFrozenGibbs
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x := by
    simpa using congrArg (fun f => f x)
      (ibBlahutArimotoStepFrozen_eq_frozenGibbs
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq)
  calc
    ((ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal
        = ((ibBlahutArimotoStepFrozenGibbs
              (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x) t).toReal := by
            exact congrArg (fun p => (p t).toReal) hfun
    _ = J.gibbsProb lam hZ t := by
          simpa [ibBlahutArimotoStepFrozenGibbs, J, lam, hZ] using
            (J.gibbsDist_pointwise lam hZ t)

private theorem ibBlahutArimotoStepFrozen_ratio_pos
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (x : X) (t : T) :
    0 < (((ibBlahutArimotoStepFrozen
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal / (qT t).toReal) := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  let hZ : J.partition lam ≠ 0 :=
    frozenSliceJaynes_partition_one_ne_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hprior : J.FullSupportPrior :=
    frozenSliceJaynes_fullSupportPrior
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hstep :
      ((ibBlahutArimotoStepFrozen
          (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal =
        J.gibbsProb lam hZ t :=
    ibBlahutArimotoStepFrozen_toReal_eq_frozenSliceGibbsProb
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x t
  have hprior_eq : (J.prior t).toReal = (qT t).toReal := by
    simp [J, frozenSliceJaynes, FiniteJaynesProblem.ofLogLikelihood]
  have hratio :
      J.gibbsProb lam hZ t / (J.prior t).toReal
        = Real.exp (J.energy lam t - J.logPartition lam) := by
    rw [J.gibbsProb_eq_prior_mul_exp_tilt lam hZ t]
    field_simp [(hprior t).ne']
  rw [hstep, ← hprior_eq, hratio]
  exact Real.exp_pos _

/--
The logarithmic BA update ratio relative to the frozen prior is exactly the
Jaynes slice energy minus the partition gauge term.
-/
theorem ibBlahutArimotoStepFrozen_log_ratio_eq_neg_betaKL_sub_logPartitionFrozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (x : X) (t : T) :
    Real.log ((((ibBlahutArimotoStepFrozen
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal) / (qT t).toReal)
      = -prob.beta *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
        - logPartitionFrozen prob qT mY_givenT x := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  let hZ : J.partition lam ≠ 0 :=
    frozenSliceJaynes_partition_one_ne_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hprior : J.FullSupportPrior :=
    frozenSliceJaynes_fullSupportPrior
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hstep :
      ((ibBlahutArimotoStepFrozen
          (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal =
        J.gibbsProb lam hZ t :=
    ibBlahutArimotoStepFrozen_toReal_eq_frozenSliceGibbsProb
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x t
  have hprior_eq : (J.prior t).toReal = (qT t).toReal := by
    simp [J, frozenSliceJaynes, FiniteJaynesProblem.ofLogLikelihood]
  have hlog := J.log_gibbsRatio_eq_energy_sub_logPartition hprior lam hZ t
  have henergy :
      J.energy lam t =
        -prob.beta *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal := by
    simp [J, lam, frozenSliceJaynes, FiniteJaynesProblem.ofLogLikelihood_energy]
  have hpart : J.logPartition lam = logPartitionFrozen prob qT mY_givenT x := by
    simpa [J, lam] using
      (frozenSlice_logPartition_eq_logPartitionFrozen
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x)
  calc
    Real.log ((((ibBlahutArimotoStepFrozen
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal) / (qT t).toReal)
        = Real.log (J.gibbsProb lam hZ t / (J.prior t).toReal) := by
            rw [hstep, hprior_eq]
    _ = J.energy lam t - J.logPartition lam := hlog
    _ = -prob.beta *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
        - logPartitionFrozen prob qT mY_givenT x := by
          rw [henergy, hpart]

/--
The frozen BA step carries the canonical scalar modular potential relative to
its frozen prior. The partition function contributes only the additive gauge
normalization term `logPartitionFrozen`.
-/
theorem ibBlahutArimotoStepFrozen_scalarModularPotential_eq_betaKL_add_logPartitionFrozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (x : X) (t : T) :
    InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential
      ((((ibBlahutArimotoStepFrozen
          (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal) / (qT t).toReal)
      (ibBlahutArimotoStepFrozen_ratio_pos
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x t)
      = prob.beta *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
        + logPartitionFrozen prob qT mY_givenT x := by
  rw [InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log]
  have hlog :=
    ibBlahutArimotoStepFrozen_log_ratio_eq_neg_betaKL_sub_logPartitionFrozen
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x t
  linarith

/--
After removing the frozen partition term, the BA-updated local modular
potential is exactly the essential `β · KL` generator. This isolates
`logPartitionFrozen` as the local gauge-fixing normalization term.
-/
theorem ibBlahutArimotoStepFrozen_scalarModularPotential_sub_logPartitionFrozen_eq_betaKL
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (x : X) (t : T) :
    InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential
      ((((ibBlahutArimotoStepFrozen
          (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal) / (qT t).toReal)
      (ibBlahutArimotoStepFrozen_ratio_pos
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x t)
      - logPartitionFrozen prob qT mY_givenT x
      = prob.beta *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal := by
  have hmod :=
    ibBlahutArimotoStepFrozen_scalarModularPotential_eq_betaKL_add_logPartitionFrozen
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x t
  linarith

end FrozenModular

end InfoGeometry.Canonical.IB
