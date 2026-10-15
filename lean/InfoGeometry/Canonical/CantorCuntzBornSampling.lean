import Mathlib
import InfoGeometry.Canonical.CantorPoUSamplingBridge

/-!
# Cuntz cylinder sampling and the six-channel Born law

The depth-five diagonal Cuntz matrix units are orthogonal cylinder projections
on the actual Cantor `L²` carrier and resolve its identity.  The positive
`Gr(2,4)` state occupies only six cylinders.  This file identifies the
normalized projector expectations on those six cylinders with the existing
Born PMF and proves their finite cell-sum identity.  It does not identify the
six-cell probability sum with an amplituhedron canonical differential form.
-/

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.Canonical.CantorCuntzBornSampling

open InfoGeometry.Canonical.ParaKahlerCantorBridge32
open InfoGeometry.Canonical.PluckerCantorPlabicClusterBridge
open InfoGeometry.Canonical.CantorPoUSamplingBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.Projective.MatrixPluckerPositiveBridge

/-- Diagonal depth-five Cuntz matrix units, viewed as cylinder effects. -/
noncomputable def cylinderEffect (w : Word5) : BoundedL2Operator :=
  cylinderMatrixUnit5 w w

section LinearBornRule

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {W : Type*} [Fintype W]

/-- Born weight defined by evaluating a real-linear state on an outcome
operator. -/
def stateBornProbability (ω : A →ₗ[ℝ] ℝ) (P : W → A) (w : W) : ℝ :=
  ω (P w)

/-- A normalized linear state sends every finite operator partition of unity
to total Born probability one. -/
theorem stateBornProbability_sum_one
    (ω : A →ₗ[ℝ] ℝ) (P : W → A)
    (hP : ∑ w : W, P w = 1) (hω : ω 1 = 1) :
    ∑ w : W, stateBornProbability ω P w = 1 := by
  calc
    ∑ w : W, stateBornProbability ω P w = ω (∑ w : W, P w) := by
      unfold stateBornProbability
      symm
      exact map_sum ω P Finset.univ
    _ = 1 := by rw [hP, hω]

/-- Positivity of the state on the effects gives nonnegative Born weights. -/
theorem stateBornProbability_nonneg
    (ω : A →ₗ[ℝ] ℝ) (P : W → A)
    (hpos : ∀ w, 0 ≤ ω (P w)) (w : W) :
    0 ≤ stateBornProbability ω P w :=
  hpos w

/-- A nonnegative normalized finite Born family has no outcome probability
larger than one. -/
theorem stateBornProbability_le_one
    (ω : A →ₗ[ℝ] ℝ) (P : W → A)
    (hP : ∑ w : W, P w = 1) (hω : ω 1 = 1)
    (hpos : ∀ w, 0 ≤ ω (P w)) (w : W) :
    stateBornProbability ω P w ≤ 1 := by
  have hsum := stateBornProbability_sum_one ω P hP hω
  have hone : stateBornProbability ω P w ≤
      ∑ w' : W, stateBornProbability ω P w' := by
    apply Finset.single_le_sum
    · intro w' hw'
      exact hpos w'
    · exact Finset.mem_univ w
  rw [hsum] at hone
  exact hone

end LinearBornRule

/-- Integrating a finite density over a disjoint cell family is the sum of
its cell integrals. This is the finite additive statement used for the
partition-of-unity cell calculation; it does not assert canonical-form
triangulation or residue cancellation. -/
theorem finiteCellSum_biUnion
    {X Cell : Type*} [Fintype X] [DecidableEq X]
    [Fintype Cell] [DecidableEq Cell]
    (cell : Cell → Finset X) (density : X → ℝ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset Cell)) cell) :
    ∑ x ∈ (Finset.univ : Finset Cell).biUnion cell, density x =
      ∑ c : Cell, ∑ x ∈ cell c, density x := by
  simpa using (Finset.sum_biUnion (s := Finset.univ) (t := cell)
    (f := density) hdisj)

theorem finiteCellSum_eq_total
    {X Cell : Type*} [Fintype X] [DecidableEq X]
    [Fintype Cell] [DecidableEq Cell]
    (cell : Cell → Finset X) (density : X → ℝ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset Cell)) cell)
    (hcover : (Finset.univ : Finset X) =
      (Finset.univ : Finset Cell).biUnion cell) :
    ∑ c : Cell, ∑ x ∈ cell c, density x = ∑ x : X, density x := by
  rw [← finiteCellSum_biUnion cell density hdisj, hcover]

/-- The depth-five Cuntz cylinder effects resolve the identity on the actual
Bernoulli Cantor `L²` space. -/
theorem cylinderEffect_resolution :
    ∑ w : Word5, cylinderEffect w = ContinuousLinearMap.id ℂ L2Boundary := by
  exact cylinderMatrixUnit5_resolution

/-- Each depth-five effect is idempotent. -/
theorem cylinderEffect_idempotent (w : Word5) :
    (cylinderEffect w).comp (cylinderEffect w) = cylinderEffect w := by
  simpa [cylinderEffect] using cylinderMatrixUnit5_mul w w w w

/-- A depth-five cylinder effect selects its own normalized prefix vector and
annihilates every distinct equal-depth prefix vector. -/
theorem cylinderEffect_apply_basis (u v : Word5) :
    cylinderEffect u (cylinderVector5 v) =
      if u = v then cylinderVector5 v else 0 := by
  by_cases huv : u = v
  · subst v
    simp [cylinderEffect, cylinderMatrixUnit5_apply_basis]
  · rw [if_neg huv]
    change operatorWord (List.ofFn u)
      ((operatorWordDag (List.ofFn u))
        (operatorWord (List.ofFn v) vacuumL2)) = 0
    have hlen : (List.ofFn u).length = (List.ofFn v).length := by simp
    have hwords : List.ofFn u ≠ List.ofFn v := by
      intro h
      exact huv (List.ofFn_injective h)
    have hcomp := operatorWordDag_comp_operatorWord_of_length_eq hlen hwords
    have hcancel := congrArg (fun T => T vacuumL2) hcomp
    have hcancelVec :
        operatorWordDag (List.ofFn u) (operatorWord (List.ofFn v) vacuumL2) = 0 := by
      simpa using hcancel
    rw [hcancelVec]
    simp

@[simp] theorem cylinderMatrixUnit5_diag_apply_basis (u v : Word5) :
    cylinderMatrixUnit5 u u (cylinderVector5 v) =
      if u = v then cylinderVector5 v else 0 := by
  simpa [cylinderEffect] using cylinderEffect_apply_basis u v

/-- The effect for an active Plücker address extracts that channel from the
six-term Cantor state. -/
theorem cylinderEffect_apply_pluckerState (M : Matrix2x4) (i : Fin 6) :
    cylinderEffect (pluckerAddress i) (pluckerCantorState M) =
      (matrixPluckerCoords M i : ℂ) • cylinderVector5 (pluckerAddress i) := by
  classical
  unfold cylinderEffect pluckerCantorState
  simp only [map_sum]
  rw [Finset.sum_eq_single i]
  · simp only [map_smul, cylinderMatrixUnit5_apply_basis]
  · intro j _ hji
    have haddr : pluckerAddress i ≠ pluckerAddress j := fun h =>
      hji (pluckerAddress_injective h.symm)
    simp [cylinderMatrixUnit5_diag_apply_basis, haddr]
  · simp

/-- An address outside the six Plücker channels has zero projected state. -/
theorem cylinderEffect_apply_pluckerState_off_channel
    (M : Matrix2x4) (w : Word5)
    (hw : ∀ i : Fin 6, pluckerAddress i ≠ w) :
    cylinderEffect w (pluckerCantorState M) = 0 := by
  classical
  unfold cylinderEffect pluckerCantorState
  simp only [map_sum]
  have hne : ∀ i : Fin 6, w ≠ pluckerAddress i := fun i => Ne.symm (hw i)
  simp [cylinderMatrixUnit5_diag_apply_basis, hne]

/-- Unnormalized Born expectation of a Cuntz cylinder effect in the actual
Cantor `L²` Plücker state. -/
noncomputable def cylinderBornNumerator (M : Matrix2x4) (w : Word5) : ℝ :=
  (inner ℂ (pluckerCantorState M) (cylinderEffect w (pluckerCantorState M))).re

theorem cylinderBornNumerator_active (M : Matrix2x4) (i : Fin 6) :
    cylinderBornNumerator M (pluckerAddress i) = (matrixPluckerCoords M i) ^ 2 := by
  unfold cylinderBornNumerator
  rw [cylinderEffect_apply_pluckerState]
  have hread : inner ℂ (pluckerCantorState M)
      (cylinderVector5 (pluckerAddress i)) = (matrixPluckerCoords M i : ℂ) := by
    rw [← inner_conj_symm, pluckerCantorState_channel_coefficient]
    simp
  rw [inner_smul_right, hread]
  simp
  ring

theorem cylinderBornNumerator_off_channel
    (M : Matrix2x4) (w : Word5)
    (hw : ∀ i : Fin 6, pluckerAddress i ≠ w) :
    cylinderBornNumerator M w = 0 := by
  unfold cylinderBornNumerator
  rw [cylinderEffect_apply_pluckerState_off_channel M w hw]
  simp

/-- Ray-normalized probability of observing a depth-five Cuntz cylinder in
the positive Plücker state. -/
noncomputable def cylinderBornProbability (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (w : Word5) : ℝ :=
  cylinderBornNumerator M w / pluckerEnergy M

theorem cylinderBornProbability_active (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    cylinderBornProbability M hM (pluckerAddress i) = pluckerBornWeight M i := by
  simp [cylinderBornProbability, cylinderBornNumerator_active,
    pluckerBornWeight, cantorSectorReadout_eq]

theorem cylinderBornProbability_off_channel (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (w : Word5)
    (hw : ∀ i : Fin 6, pluckerAddress i ≠ w) :
    cylinderBornProbability M hM w = 0 := by
  simp [cylinderBornProbability, cylinderBornNumerator_off_channel M w hw]

/-- The six Plücker-cell Born weights form a finite partition of unity. -/
theorem pluckerCellBorn_sum_one (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∑ i : Fin 6, cylinderBornProbability M hM (pluckerAddress i) = 1 := by
  simp_rw [cylinderBornProbability_active]
  exact pluckerBornWeight_sum_one M hM

/-- The actual path PMF reads back as the Cuntz state-sampling probability on
active cells. -/
theorem cantorPathPMF_active_eq_cylinderBorn (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    (cantorPathPMF M hM (pluckerAddress i)).toReal =
      cylinderBornProbability M hM (pluckerAddress i) := by
  rw [cantorPathPMF_active_mass, ENNReal.toReal_ofReal]
  · exact (cylinderBornProbability_active M hM i).symm
  · exact le_of_lt (pluckerBornWeight_pos M hM i)

/-- At every depth-five address, the pushed-forward PMF agrees with the Born
expectation of the corresponding Cuntz cylinder effect. -/
theorem cantorPathPMF_toReal_eq_cylinderBorn (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (w : Word5) :
    (cantorPathPMF M hM w).toReal = cylinderBornProbability M hM w := by
  by_cases hactive : ∃ i : Fin 6, pluckerAddress i = w
  · obtain ⟨i, rfl⟩ := hactive
    exact cantorPathPMF_active_eq_cylinderBorn M hM i
  · have hw : ∀ i : Fin 6, pluckerAddress i ≠ w := by
      intro i hi
      exact hactive ⟨i, hi⟩
    rw [cantorPathPMF_off_channel M hM w hw,
      cylinderBornProbability_off_channel M hM w hw]
    simp

/-- The full 32-outcome path law is normalized as an ENNReal PMF. -/
theorem cantorPathPMF_tsum_one (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∑' w : Word5, cantorPathPMF M hM w = 1 :=
  (cantorPathPMF M hM).tsum_coe

/-- An observable on the six active channels, viewed on the Cantor address
space and set to zero away from those addresses. -/
def activePathObservable (f : Fin 6 → ℝ) : Word5 → ℝ := fun w =>
  ∑ i : Fin 6, if w = pluckerAddress i then f i else 0

/-- Sampling the pushed-forward Cantor PMF and evaluating an observable
supported on the six Plücker addresses has the same expectation as sampling
the six-channel Born PMF. -/
theorem cantorPathPMF_expectation_active (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (f : Fin 6 → ℝ) :
    ∫ w, activePathObservable f w ∂(cantorPathPMF M hM).toMeasure =
      ∑ i : Fin 6, pluckerBornWeight M i * f i := by
  rw [PMF.integral_eq_sum]
  calc
    (∑ w : Word5, (cantorPathPMF M hM w).toReal • activePathObservable f w) =
        ∑ w : Word5, ∑ i : Fin 6,
          (cantorPathPMF M hM w).toReal *
            (if w = pluckerAddress i then f i else 0) := by
          apply Finset.sum_congr rfl
          intro w hw
          simp only [activePathObservable, smul_eq_mul, Finset.mul_sum]
    _ = ∑ i : Fin 6, ∑ w : Word5,
          (cantorPathPMF M hM w).toReal *
            (if w = pluckerAddress i then f i else 0) := by
          exact Finset.sum_comm
    _ = ∑ i : Fin 6,
          (cantorPathPMF M hM (pluckerAddress i)).toReal * f i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_eq_single (pluckerAddress i)]
          · simp
          · intro w hw hne
            simp [hne]
          · simp
    _ = ∑ i : Fin 6, pluckerBornWeight M i * f i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [cantorPathPMF_active_eq_cylinderBorn]
          rw [cylinderBornProbability_active]

end InfoGeometry.Canonical.CantorCuntzBornSampling
