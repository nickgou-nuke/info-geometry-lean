import InfoGeometry.Canonical.IBBase

/-!
# InfoGeometry.Canonical.IBFrozenJaynes

Derived Jaynes / exponential-family representation of the frozen finite
Information Bottleneck slice.
-/

open scoped BigOperators ENNReal NNReal

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

section FrozenJaynes

variable [DecidableEq T]

/--
Finite Jaynes slice induced by the frozen IB target at fixed `x`.
-/
noncomputable def frozenSliceJaynes
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) : InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem T Unit :=
  InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.ofLogLikelihood
    qT
    (fun t =>
      -prob.beta * (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)

lemma frozenSliceJaynes_fullSupportPrior
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    (frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x).FullSupportPrior := by
  intro t
  simpa [frozenSliceJaynes] using hq t

lemma frozenSliceJaynes_partition_one_ne_zero
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    (frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x).partition
      (fun _ : Unit => (1 : ℝ)) ≠ 0 := by
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  have hprior : J.FullSupportPrior := by
    intro t
    simpa [J, frozenSliceJaynes] using hq t
  haveI : Nonempty T := by
    rcases qT.support_nonempty with ⟨t0, ht0⟩
    exact ⟨t0⟩
  exact J.partition_ne_zero_of_fullSupport hprior (fun _ : Unit => (1 : ℝ))

lemma frozenSlice_partition_eq_baScoreFrozen_tsum_toReal
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    J.partition lam = ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal) := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  calc
    J.partition lam
        = ∑ t : T, (qT t).toReal *
            Real.exp
              (-prob.beta *
                (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal) := by
            simp [J, lam, frozenSliceJaynes,
              InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.ofLogLikelihood,
              InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition,
              InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.energy]
    _ = ∑ t : T, (baScoreFrozen prob qT mY_givenT x t).toReal := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          unfold baScoreFrozen
          rw [ENNReal.toReal_mul]
          rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
    _ = ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal) := by
          rw [tsum_fintype, ENNReal.toReal_sum]
          intro t ht
          exact baScoreFrozen_ne_top prob qT mY_givenT x t

lemma frozenSlice_logPartition_eq_logPartitionFrozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    J.logPartition lam = logPartitionFrozen prob qT mY_givenT x := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  have hpart : J.partition lam = ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal) := by
    simpa [J, lam] using
      (frozenSlice_partition_eq_baScoreFrozen_tsum_toReal
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x)
  simpa [J, lam, hpart, InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.logPartition, logPartitionFrozen]

/--
Local frozen free-energy identity in Jaynes variational form (single slice `x`).
-/
lemma frozenSlice_local_free_energy_identity_sum
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (p_x : FinProb T)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    let hZ : J.partition lam ≠ 0 :=
      frozenSliceJaynes_partition_one_ne_zero
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
    (InfoGeometry.fin_kl_div p_x qT).toReal +
      prob.beta * ∑ t : T, (p_x t).toReal *
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
    =
      (∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t))
        - J.logPartition lam := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  let hZ : J.partition lam ≠ 0 :=
    frozenSliceJaynes_partition_one_ne_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hprior : J.FullSupportPrior := by
    intro t
    simpa [J, frozenSliceJaynes] using hq t
  have hvar := J.kl_gibbs_variational_identity hprior lam hZ p_x
  have hKLq :
      (InfoGeometry.fin_kl_div p_x qT).toReal
        = ∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / (J.prior t).toReal) := by
    simpa [J, frozenSliceJaynes] using
      (InfoGeometry.MaxEnt.IProjection.toReal_klDiv_eq_sum_log_ratio
        (P := p_x) (Q := qT) hq)
  have hMoment :
      (∑ i ∈ J.index, lam i * J.moment p_x (J.feature i))
        =
      -prob.beta * ∑ t : T, (p_x t).toReal *
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal := by
    calc
      (∑ i ∈ J.index, lam i * J.moment p_x (J.feature i))
          = ∑ i ∈ ({()} : Finset Unit), lam i * J.moment p_x (J.feature i) := by
              simp [J, frozenSliceJaynes,
                InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.ofLogLikelihood]
      _ = J.moment p_x (J.feature ()) := by
              simp [lam]
      _ =
          -prob.beta * ∑ t : T, (p_x t).toReal *
            (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal := by
              unfold InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.moment
              calc
                (∑ t : T, (p_x t).toReal * J.feature () t)
                    = ∑ t : T, (p_x t).toReal *
                        (-prob.beta *
                          (InfoGeometry.fin_kl_div (condYGivenX prob x)
                            (mY_givenT t)).toReal) := by
                          simp [J, frozenSliceJaynes,
                            InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.ofLogLikelihood]
                _ = ∑ t : T, -prob.beta * ((p_x t).toReal *
                      (InfoGeometry.fin_kl_div (condYGivenX prob x)
                        (mY_givenT t)).toReal) := by
                      refine Finset.sum_congr rfl ?_
                      intro t ht
                      ring
                _ =
                    -prob.beta * ∑ t : T, (p_x t).toReal *
                      (InfoGeometry.fin_kl_div (condYGivenX prob x)
                        (mY_givenT t)).toReal := by
                      simpa using (Finset.mul_sum (s := (Finset.univ : Finset T))
                        (f := fun t : T => (p_x t).toReal *
                          (InfoGeometry.fin_kl_div (condYGivenX prob x)
                            (mY_givenT t)).toReal)
                        (a := -prob.beta)).symm
  rw [← hKLq, hMoment] at hvar
  linarith

/--
Local frozen free-energy identity as KL-to-Gibbs minus log-partition.
-/
lemma local_free_energy_identity
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (p_x : FinProb T)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    let hZ : J.partition lam ≠ 0 :=
      frozenSliceJaynes_partition_one_ne_zero
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
    (InfoGeometry.fin_kl_div p_x qT).toReal +
      prob.beta * ∑ t : T, (p_x t).toReal *
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
    =
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
        - J.logPartition lam := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  let hZ : J.partition lam ≠ 0 :=
    frozenSliceJaynes_partition_one_ne_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hsum :
      (InfoGeometry.fin_kl_div p_x qT).toReal +
        prob.beta * ∑ t : T, (p_x t).toReal *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
      =
        (∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t))
          - J.logPartition lam := by
    simpa [J, lam, hZ] using
      (frozenSlice_local_free_energy_identity_sum
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x p_x hq)
  have hGibbsFull : ∀ t : T, 0 < ((J.gibbsDist lam hZ t).toReal) := by
    intro t
    rw [J.gibbsDist_pointwise]
    unfold InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsProb
    unfold InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsWeight
    have hZnonneg : 0 ≤ J.partition lam := J.partition_nonneg lam
    have hZpos : 0 < J.partition lam := lt_of_le_of_ne hZnonneg (Ne.symm hZ)
    exact div_pos (mul_pos (hq t) (Real.exp_pos _)) hZpos
  have hKLg :
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
        = ∑ t : T, (p_x t).toReal *
            Real.log ((p_x t).toReal / ((J.gibbsDist lam hZ) t).toReal) := by
    simpa using
      (InfoGeometry.MaxEnt.IProjection.toReal_klDiv_eq_sum_log_ratio
        (P := p_x) (Q := J.gibbsDist lam hZ) hGibbsFull)
  have hKLg' :
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
        = ∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t) := by
    calc
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
          = ∑ t : T, (p_x t).toReal *
              Real.log ((p_x t).toReal / ((J.gibbsDist lam hZ) t).toReal) := hKLg
      _ = ∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            simp [J.gibbsDist_pointwise]
  calc
    (InfoGeometry.fin_kl_div p_x qT).toReal +
        prob.beta * ∑ t : T, (p_x t).toReal *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
        =
      (∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t))
        - J.logPartition lam := hsum
    _ =
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
        - J.logPartition lam := by
          rw [hKLg']

end FrozenJaynes

end InfoGeometry.Canonical.IB
