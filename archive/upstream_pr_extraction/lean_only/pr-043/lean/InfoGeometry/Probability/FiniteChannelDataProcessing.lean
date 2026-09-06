import InfoGeometry.EntropicInference

noncomputable section

namespace InfoGeometry.Probability.FiniteChannelDataProcessing

open scoped BigOperators
open InfoGeometry
open InfoGeometry.EntropicInference

variable {X Y : Type*}
variable [Fintype X] [Fintype Y]
variable [MeasurableSpace X] [MeasurableSpace Y]

/-- Swap the two coordinates of a finite joint law. -/
def swapJoint (p : Joint X Y) : Joint Y X :=
  p.map Prod.swap

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Pointwise action of coordinate swap on a finite joint law. -/
theorem swapJoint_apply
    [DecidableEq X] [DecidableEq Y]
    (p : Joint X Y)
    (y : Y)
    (x : X) :
    swapJoint p (y, x) = p (x, y) := by
  unfold swapJoint
  rw [PMF.map_apply, tsum_fintype]
  classical
  simp only [Prod.swap]
  rw [Finset.sum_eq_single (x, y)]
  · simp
  · intro z _ hne
    simp only [ite_eq_right_iff]
    intro heq
    exact (hne (Prod.ext
      (congrArg Prod.snd heq).symm
      (congrArg Prod.fst heq).symm)).elim
  · simp

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The first marginal after coordinate swap is the original second marginal. -/
theorem marginal_x_swapJoint
    (p : Joint X Y) :
    marginal_x (swapJoint p) = marginal_theta p := by
  unfold marginal_x marginal_theta swapJoint
  rw [PMF.map_comp]
  simp [Function.comp_def]

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Strict positivity is preserved by coordinate swap. -/
theorem swapJoint_toReal_pos
    [DecidableEq X] [DecidableEq Y]
    (p : Joint X Y)
    (hp : ∀ x : X, ∀ y : Y, 0 < (p (x, y)).toReal) :
    ∀ y : Y, ∀ x : X, 0 < (swapJoint p (y, x)).toReal := by
  intro y x
  rw [swapJoint_apply]
  exact hp x y

/-- Finite `toReal` KL is invariant under coordinate swap. -/
theorem kl_swapJoint_toReal
    [DecidableEq X] [DecidableEq Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (p q : Joint X Y)
    (hq : ∀ x : X, ∀ y : Y, 0 < (q (x, y)).toReal) :
    (kl (swapJoint p) (swapJoint q)).toReal =
      (kl p q).toReal := by
  have hq_joint : ∀ z : X × Y, 0 < (q z).toReal := by
    intro z
    exact hq z.1 z.2
  have hq_swap : ∀ z : Y × X, 0 < (swapJoint q z).toReal := by
    intro z
    exact swapJoint_toReal_pos q hq z.1 z.2
  rw [show
      (kl (swapJoint p) (swapJoint q)).toReal =
        ∑ z : Y × X,
          (swapJoint p z).toReal *
            Real.log ((swapJoint p z).toReal / (swapJoint q z).toReal) by
      simpa [kl, InfoGeometry.KL.kl_div] using
        (InfoGeometry.MaxEnt.IProjection.toReal_klDiv_eq_sum_log_ratio
          (P := swapJoint p) (Q := swapJoint q) hq_swap)]
  rw [show
      (kl p q).toReal =
        ∑ z : X × Y,
          (p z).toReal * Real.log ((p z).toReal / (q z).toReal) by
      simpa [kl, InfoGeometry.KL.kl_div] using
        (InfoGeometry.MaxEnt.IProjection.toReal_klDiv_eq_sum_log_ratio
          (P := p) (Q := q) hq_joint)]
  simp_rw [Fintype.sum_prod_type, swapJoint_apply]
  rw [Finset.sum_comm]

/-- Data processing for the second-coordinate marginal of a positive joint. -/
theorem kl_marginal_theta_le_toReal_strict
    [DecidableEq X] [DecidableEq Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    [Nonempty X]
    (p q : Joint X Y)
    (hp : ∀ x : X, ∀ y : Y, 0 < (p (x, y)).toReal)
    (hq : ∀ x : X, ∀ y : Y, 0 < (q (x, y)).toReal) :
    (InfoGeometry.KL.kl_div
      (marginal_theta p).toMeasure
      (marginal_theta q).toMeasure).toReal
      ≤
    (kl p q).toReal := by
  have hswap :=
    kl_marginal_x_le_toReal_strict
      (p := swapJoint p)
      (q := swapJoint q)
      (hposp := swapJoint_toReal_pos p hp)
      (hposq := swapJoint_toReal_pos q hq)
  rw [marginal_x_swapJoint, marginal_x_swapJoint,
    kl_swapJoint_toReal p q hq] at hswap
  exact hswap

/-- Output law of a finite probability kernel. -/
def applyKernel
    (p : FinProb X)
    (K : X → FinProb Y) : FinProb Y :=
  marginal_theta (assemble p K)

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- A strictly positive input and kernel produce a strictly positive joint. -/
theorem assemble_toReal_pos
    (p : FinProb X)
    (K : X → FinProb Y)
    (hp : ∀ x : X, 0 < (p x).toReal)
    (hK : ∀ x : X, ∀ y : Y, 0 < (K x y).toReal) :
    ∀ x : X, ∀ y : Y, 0 < (assemble p K (x, y)).toReal := by
  intro x y
  rw [assemble_apply, ENNReal.toReal_mul]
  exact mul_pos (hp x) (hK x y)

/--
Applying one strictly positive finite kernel to two strictly positive laws
cannot increase `toReal` KL divergence.
-/
theorem kl_applyKernel_le_toReal_strict
    [DecidableEq X] [DecidableEq Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    [Nonempty X] [Nonempty Y]
    (p q : FinProb X)
    (K : X → FinProb Y)
    (hp : ∀ x : X, 0 < (p x).toReal)
    (hq : ∀ x : X, 0 < (q x).toReal)
    (hK : ∀ x : X, ∀ y : Y, 0 < (K x y).toReal) :
    (InfoGeometry.KL.kl_div
      (applyKernel p K).toMeasure
      (applyKernel q K).toMeasure).toReal
      ≤
    (InfoGeometry.KL.kl_div p.toMeasure q.toMeasure).toReal := by
  let jp : Joint X Y := assemble p K
  let jq : Joint X Y := assemble q K
  have hjp_pos : ∀ x : X, ∀ y : Y, 0 < (jp (x, y)).toReal :=
    assemble_toReal_pos p K hp hK
  have hjq_pos : ∀ x : X, ∀ y : Y, 0 < (jq (x, y)).toReal :=
    assemble_toReal_pos q K hq hK
  have houtput :
      (InfoGeometry.KL.kl_div
        (marginal_theta jp).toMeasure
        (marginal_theta jq).toMeasure).toReal
        ≤
      (kl jp jq).toReal :=
    kl_marginal_theta_le_toReal_strict jp jq hjp_pos hjq_pos
  have hjoint :
      (InfoGeometry.KL.kl_div
        (marginal_x jp).toMeasure
        (marginal_x jq).toMeasure).toReal =
      (kl jp jq).toReal := by
    apply
      (kl_marginal_x_eq_toReal_iff_exists_shared_recovery
        jp jq hjp_pos hjq_pos).2
    refine ⟨K, ?_, ?_⟩
    · simp [jp, marginal_x_assemble]
    · simp [jq, marginal_x_assemble]
  simpa [applyKernel, jp, jq, marginal_x_assemble] using
    houtput.trans_eq hjoint.symm

end InfoGeometry.Probability.FiniteChannelDataProcessing
