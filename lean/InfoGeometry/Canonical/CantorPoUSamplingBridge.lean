import Mathlib
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import InfoGeometry.Canonical.ParaKahlerCantorBridge32
import InfoGeometry.Canonical.PluckerCantorPlabicClusterBridge
import InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
import InfoGeometry.Canonical.FiniteFisherRaoSquareRoot

/-!
# Projective and Born sampling from the six positive Cantor--Plücker channels

The module distinguishes two normalized laws: linear projective Plücker
coordinates and squared-amplitude Born probabilities. Both live on the six
active channels and push forward to their actual depth-five Cantor addresses.
Neither law has full support on all 32 paths; the operator resolution of the
identity remains an owner theorem on the full Cantor `L²` space.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.CantorPoUSamplingBridge

open InfoGeometry.Canonical.ParaKahlerCantorBridge32
open InfoGeometry.Canonical.PluckerCantorPlabicClusterBridge
open InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.Canonical.FiniteFisherRaoSquareRoot

/-- Sum of squared readouts of the six active Cantor--Plücker channels. -/
noncomputable def pluckerEnergy (M : Matrix2x4) : ℝ :=
  ∑ i : Fin 6, (cantorSectorReadout M i) ^ 2

theorem pluckerEnergy_eq_l2_norm_sq (M : Matrix2x4) :
    pluckerEnergy M = ‖pluckerCantorState M‖ ^ 2 := by
  unfold pluckerEnergy
  simp_rw [cantorSectorReadout_eq]
  exact (pluckerCantorState_norm_sq M).symm

theorem pluckerEnergy_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    0 < pluckerEnergy M := by
  unfold pluckerEnergy
  apply Finset.sum_pos
  · intro i hi
    exact sq_pos_of_pos (cantorSectorReadout_pos M hM i)
  · exact Finset.univ_nonempty

/-- Sum of the six positive Plücker amplitudes, used for projective
normalization. This law is distinct from the squared-amplitude Born law below. -/
noncomputable def pluckerAmplitudeMass (M : Matrix2x4) : ℝ :=
  ∑ i : Fin 6, cantorSectorReadout M i

theorem pluckerAmplitudeMass_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    0 < pluckerAmplitudeMass M := by
  unfold pluckerAmplitudeMass
  apply Finset.sum_pos
  · intro i hi
    exact cantorSectorReadout_pos M hM i
  · exact Finset.univ_nonempty

/-- Projectively normalized (linear, not Born-squared) Plücker channel weight. -/
noncomputable def pluckerProjectiveWeight (M : Matrix2x4) (i : Fin 6) : ℝ :=
  cantorSectorReadout M i / pluckerAmplitudeMass M

theorem pluckerProjectiveWeight_nonneg (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    0 ≤ pluckerProjectiveWeight M i := by
  unfold pluckerProjectiveWeight
  exact div_nonneg (le_of_lt (cantorSectorReadout_pos M hM i))
    (le_of_lt (pluckerAmplitudeMass_pos M hM))

theorem pluckerProjectiveWeight_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    0 < pluckerProjectiveWeight M i := by
  unfold pluckerProjectiveWeight
  exact div_pos (cantorSectorReadout_pos M hM i)
    (pluckerAmplitudeMass_pos M hM)

theorem pluckerProjectiveWeight_sum_one (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∑ i : Fin 6, pluckerProjectiveWeight M i = 1 := by
  unfold pluckerProjectiveWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (pluckerAmplitudeMass_pos M hM))

theorem pluckerProjectiveWeight_eq_normalizedPluckerCoords
    (M : Matrix2x4) (i : Fin 6) :
    pluckerProjectiveWeight M i = normalizedPluckerCoords M i := by
  simp [pluckerProjectiveWeight, pluckerAmplitudeMass,
    normalizedPluckerCoords, pluckerNormalizationDenom,
    cantorSectorReadout_eq]

theorem pluckerProjectiveWeight_row_basis_invariant
    (A : Matrix (Fin 2) (Fin 2) ℝ) (M : Matrix2x4)
    (hA : 0 < Matrix.det A)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    pluckerProjectiveWeight (A * M) i = pluckerProjectiveWeight M i := by
  rw [pluckerProjectiveWeight_eq_normalizedPluckerCoords,
    pluckerProjectiveWeight_eq_normalizedPluckerCoords]
  exact congrFun (normalizedPluckerCoords_left_mul A M hA hM) i

/-- The linear projective channel law as a strictly positive point of the
six-outcome probability simplex. -/
noncomputable def pluckerProjectiveStrictProbability (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) : StrictProbability (Fin 6) where
  probability := pluckerProjectiveWeight M
  probability_pos := pluckerProjectiveWeight_pos M hM
  sum_probability := pluckerProjectiveWeight_sum_one M hM

/-- Fisher--Rao pairing on tangent directions of the finite projective
Plücker probability simplex. -/
noncomputable def pluckerProjectiveFisherPair (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (u v : Fin 6 → ℝ) : ℝ :=
  (pluckerProjectiveStrictProbability M hM).fisherPair u v

theorem pluckerProjectiveFisherPair_nonneg (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (v : Fin 6 → ℝ) :
    0 ≤ pluckerProjectiveFisherPair M hM v v :=
  (pluckerProjectiveStrictProbability M hM).fisherPair_self_nonnegative v

theorem pluckerProjectiveFisherPair_sqrt_isometry (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (u v : Fin 6 → ℝ) :
    (pluckerProjectiveStrictProbability M hM).euclideanPair
        ((pluckerProjectiveStrictProbability M hM).twoSqrtDifferential u)
        ((pluckerProjectiveStrictProbability M hM).twoSqrtDifferential v) =
      pluckerProjectiveFisherPair M hM u v :=
  (pluckerProjectiveStrictProbability M hM).euclideanPair_twoSqrtDifferential u v

/-- The six linear projective weights form a native finite PMF. -/
noncomputable def pluckerProjectivePMF (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) : PMF (Fin 6) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (pluckerProjectiveWeight M i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [pluckerProjectiveWeight_sum_one M hM, ENNReal.ofReal_one]
    · intro i hi
      exact pluckerProjectiveWeight_nonneg M hM i)

/-- Push the linear projective law to the six Cantor cylinder addresses. -/
noncomputable def pluckerProjectivePathPMF (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) : PMF Word5 :=
  (pluckerProjectivePMF M hM).map pluckerAddress

@[simp] theorem pluckerProjectivePMF_apply (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    pluckerProjectivePMF M hM i =
      ENNReal.ofReal (pluckerProjectiveWeight M i) := rfl

theorem pluckerProjectivePathPMF_active_mass (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    pluckerProjectivePathPMF M hM (pluckerAddress i) =
      ENNReal.ofReal (pluckerProjectiveWeight M i) := by
  classical
  rw [pluckerProjectivePathPMF, PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single i]
  · simp [pluckerProjectivePMF]
  · intro j hj hji
    have haddr : ¬(pluckerAddress i = pluckerAddress j) := by
      intro h
      exact hji (pluckerAddress_injective h.symm)
    simp [haddr]
  · simp

theorem pluckerProjectivePathPMF_off_channel (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (w : Word5)
    (hw : ∀ i : Fin 6, pluckerAddress i ≠ w) :
    pluckerProjectivePathPMF M hM w = 0 := by
  classical
  rw [pluckerProjectivePathPMF, PMF.map_apply, tsum_fintype]
  have hne : ∀ i : Fin 6, w ≠ pluckerAddress i := fun i => Ne.symm (hw i)
  simp [hne]

theorem pluckerProjectivePathPMF_active_mass_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    0 < pluckerProjectivePathPMF M hM (pluckerAddress i) := by
  rw [pluckerProjectivePathPMF_active_mass]
  exact ENNReal.ofReal_pos.mpr (pluckerProjectiveWeight_pos M hM i)

/-- Normalized Born weight of a Plücker channel. -/
noncomputable def pluckerBornWeight (M : Matrix2x4) (i : Fin 6) : ℝ :=
  (cantorSectorReadout M i) ^ 2 / pluckerEnergy M

theorem pluckerBornWeight_nonneg (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    0 ≤ pluckerBornWeight M i := by
  unfold pluckerBornWeight
  exact div_nonneg (sq_nonneg _) (le_of_lt (pluckerEnergy_pos M hM))

theorem pluckerBornWeight_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    0 < pluckerBornWeight M i := by
  unfold pluckerBornWeight
  exact div_pos (sq_pos_of_pos (cantorSectorReadout_pos M hM i))
    (pluckerEnergy_pos M hM)

theorem pluckerBornWeight_sum_one (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∑ i : Fin 6, pluckerBornWeight M i = 1 := by
  unfold pluckerBornWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (pluckerEnergy_pos M hM))

/-- The six normalized squared Cantor-channel readouts form a native finite
probability mass function. -/
noncomputable def pluckerChannelPMF (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) : PMF (Fin 6) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (pluckerBornWeight M i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [pluckerBornWeight_sum_one M hM, ENNReal.ofReal_one]
    · intro i hi
      exact pluckerBornWeight_nonneg M hM i)

@[simp] theorem pluckerChannelPMF_apply (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    pluckerChannelPMF M hM i = ENNReal.ofReal (pluckerBornWeight M i) := rfl

/-- Push the channel PMF to the actual five-bit cylinder address carrier. -/
noncomputable def cantorPathPMF (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) : PMF Word5 :=
  (pluckerChannelPMF M hM).map pluckerAddress

theorem cantorPathPMF_active_mass (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    cantorPathPMF M hM (pluckerAddress i) =
      ENNReal.ofReal (pluckerBornWeight M i) := by
  classical
  rw [cantorPathPMF, PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single i]
  · simp [pluckerChannelPMF]
  · intro j hj hji
    have haddr : ¬(pluckerAddress i = pluckerAddress j) := by
      intro h
      exact hji (pluckerAddress_injective h.symm)
    simp [haddr]
  · simp

theorem cantorPathPMF_off_channel (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (w : Word5)
    (hw : ∀ i : Fin 6, pluckerAddress i ≠ w) :
    cantorPathPMF M hM w = 0 := by
  classical
  rw [cantorPathPMF, PMF.map_apply, tsum_fintype]
  have hne : ∀ i : Fin 6, w ≠ pluckerAddress i := fun i => Ne.symm (hw i)
  simp [hne]

theorem cantorPathPMF_active_mass_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    0 < cantorPathPMF M hM (pluckerAddress i) := by
  rw [cantorPathPMF_active_mass]
  exact ENNReal.ofReal_pos.mpr (pluckerBornWeight_pos M hM i)

@[simp] theorem pluckerChannelPMF_toReal (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    (pluckerChannelPMF M hM i).toReal = pluckerBornWeight M i := by
  rw [pluckerChannelPMF_apply]
  exact ENNReal.toReal_ofReal (pluckerBornWeight_nonneg M hM i)

/-- The expected value of a finite observable under the six-channel Born law
is the Plücker-weighted sum of its channel values. -/
theorem pluckerChannelPMF_expectation (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (f : Fin 6 → ℝ) :
    ∫ i, f i ∂(pluckerChannelPMF M hM).toMeasure =
      ∑ i : Fin 6, pluckerBornWeight M i * f i := by
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pluckerChannelPMF_toReal]
  rw [smul_eq_mul]

/-- Partition-of-unity gluing for the six finite Plücker channels: a common
local value is recovered by summing it against the normalized Born weights.
This statement concerns the six channels, not a positroid-cell decomposition
or a canonical-form recursion. -/
theorem pluckerCellSum_gluing (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (f : Fin 6 → ℝ) (value : ℝ)
    (hf : ∀ i, f i = value) :
    ∑ i : Fin 6, pluckerBornWeight M i * f i = value := by
  calc
    ∑ i : Fin 6, pluckerBornWeight M i * f i =
        ∑ i : Fin 6, pluckerBornWeight M i * value := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hf i]
    _ = (∑ i : Fin 6, pluckerBornWeight M i) * value := by
          rw [Finset.sum_mul]
    _ = value := by rw [pluckerBornWeight_sum_one M hM, one_mul]

/-- The partition-of-unity identity is equivalently the expectation of a
constant observable under the native Mathlib PMF. -/
theorem pluckerChannelPMF_expectation_const (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (value : ℝ) :
    ∫ _i, value ∂(pluckerChannelPMF M hM).toMeasure = value := by
  rw [pluckerChannelPMF_expectation]
  exact pluckerCellSum_gluing M hM (fun _ => value) value (fun _ => rfl)

/-- Local contribution of a finite chart cell to an observable's Born
expectation. `cellWeight c i` is the partition-of-unity weight of cell `c`
at Plücker channel `i`. -/
noncomputable def pluckerCellContribution {ι : Type*} [Fintype ι]
    (M : Matrix2x4) (_hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (cellWeight : ι → Fin 6 → ℝ)
    (f : Fin 6 → ℝ) (c : ι) : ℝ :=
  ∑ i : Fin 6, pluckerBornWeight M i * cellWeight c i * f i

/-- Finite cell-sum identity: any finite partition of unity on the six
Plücker channels decomposes the global Born expectation into the sum of its
localized cell contributions. This is the finite chart-level analogue of a
cellwise amplituhedron sum; it does not assert positroid cells or canonical
differential forms. -/
theorem pluckerCellSum_partition_unity {ι : Type*} [Fintype ι]
    (M : Matrix2x4) (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (cellWeight : ι → Fin 6 → ℝ)
    (hpartition : ∀ i, ∑ c : ι, cellWeight c i = 1) (f : Fin 6 → ℝ) :
    ∑ c : ι, pluckerCellContribution M hM cellWeight f c =
      ∫ i, f i ∂(pluckerChannelPMF M hM).toMeasure := by
  rw [pluckerChannelPMF_expectation]
  unfold pluckerCellContribution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hfactor : (∑ c : ι,
      pluckerBornWeight M i * cellWeight c i * f i) =
      pluckerBornWeight M i * f i * (∑ c : ι, cellWeight c i) := by
    calc
      (∑ c : ι, pluckerBornWeight M i * cellWeight c i * f i) =
          ∑ c : ι, (pluckerBornWeight M i * f i) * cellWeight c i := by
            apply Finset.sum_congr rfl
            intro c hc
            ring
      _ = pluckerBornWeight M i * f i * (∑ c : ι, cellWeight c i) :=
          (Finset.mul_sum _ _ _).symm
  rw [hfactor, hpartition i, mul_one]

/-- The singleton partition of the six discrete Plücker channels recovers the
normalized Born sum, so the total cell mass is one. -/
theorem pluckerSingletonCellSum_one (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∑ i : Fin 6, pluckerCellContribution M hM
      (fun c j => if c = j then 1 else 0) (fun _ => 1) i = 1 := by
  rw [pluckerCellSum_partition_unity]
  · rw [pluckerChannelPMF_expectation_const]
  · intro j
    simp

end InfoGeometry.Canonical.CantorPoUSamplingBridge
