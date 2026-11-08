import Mathlib
import InfoGeometry.Canonical.PluckerCantorPlabicClusterBridge
import InfoGeometry.Canonical.ParaKahlerCantorBridge32
import InfoGeometry.Canonical.GrassmannianCartanInteroperability
import InfoGeometry.Projective.MatrixPluckerPositiveBridge
import InfoGeometry.Topology.PlabicCluster

/-!
# Cantor, plabic mutation, and momentum-twistor readback

This file is a bridge over the existing owners: the Cantor `L²` state and its
six Plücker channels, the `Gr(2,4)` matrix Plücker coordinates, and the
five-coordinate plabic square mutation.  The finite transfer calculation is
kept as a separate path-weight calculation; it is not presented as an
operator on the full Cantor `L²` space.
-/

namespace InfoGeometry.Canonical.CantorPlabicTwistorBridge

open InfoGeometry.Canonical.ParaKahlerCantorBridge32
open InfoGeometry.Canonical.AmplituhedronBCFW
open InfoGeometry.Canonical.GrassmannianCartanInteroperability
open InfoGeometry.Canonical.PluckerCantorPlabicClusterBridge
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.PlabicCluster

/-! ## The five-face square move read from the Cantor state -/

/-- Attach the actual Cantor-read Plücker face coordinate to a local square
seed, retaining its four neighboring coordinates. -/
noncomputable def cantorSquareSeed (M : Matrix2x4) (s : SquareFaceWeights ℝ) :
    SquareFaceWeights ℝ :=
  { s with yf := cantorPlabicFaceWeight M }

/-- The full five-coordinate monodromy identity is the owner square-move
identity specialized to the positive Cantor-read face weight. -/
theorem cantor_square_monodromy (M : Matrix2x4) (s : SquareFaceWeights ℝ)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    (mutateF (cantorSquareSeed M s)).yf *
      ((mutateF (cantorSquareSeed M s)).y1 * (mutateF (cantorSquareSeed M s)).y2) *
      ((mutateF (cantorSquareSeed M s)).y3 * (mutateF (cantorSquareSeed M s)).y4) =
      (cantorSquareSeed M s).yf *
        ((cantorSquareSeed M s).y1 * (cantorSquareSeed M s).y2) *
        ((cantorSquareSeed M s).y3 * (cantorSquareSeed M s).y4) := by
  apply total_cluster_face_weight_monodromy
  · exact ne_of_gt (cantorPlabicFaceWeight_pos M hM)
  · intro hzero
    change 1 + cantorPlabicFaceWeight M = 0 at hzero
    linarith [cantorPlabicFaceWeight_pos M hM]

/-- Reversing the quiver at the mutated face and mutating again recovers the
entire seed, including all four adjacent face coordinates. -/
theorem cantor_square_mutation_involutive (M : Matrix2x4)
    (s : SquareFaceWeights ℝ)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    mutateF_rev (mutateF (cantorSquareSeed M s)) = cantorSquareSeed M s := by
  apply cluster_mutation_involution
  · exact ne_of_gt (cantorPlabicFaceWeight_pos M hM)
  · intro hzero
    change 1 + cantorPlabicFaceWeight M = 0 at hzero
    linarith [cantorPlabicFaceWeight_pos M hM]

/-! ## Transfer weights on the six actual Cantor addresses -/

def stageWeight (u : ℝ) (b : Bool) : ℝ := if b then u - 1 else u + 1

def pathTransferWeight (u : ℝ) (w : Word5) : ℝ :=
  stageWeight u (w 0) * stageWeight u (w 1) * stageWeight u (w 2) *
    stageWeight u (w 3) * stageWeight u (w 4)

theorem plucker_paths_have_weight_two (i : Fin 6) :
    (Finset.univ.filter (fun k : Fin 5 => pluckerAddress i k)).card = 2 := by
  exact pluckerAddress_weight i

/-- Each actual Plücker address has the same product of its five stage
weights.  This is a finite diagonal-weight identity, not a claim of a
continuum transfer-matrix spectrum. -/
theorem plucker_paths_transfer_weight (u : ℝ) (i : Fin 6) :
    pathTransferWeight u (pluckerAddress i) = (u - 1) ^ 2 * (u + 1) ^ 3 := by
  fin_cases i <;>
    norm_num [pathTransferWeight, stageWeight, pluckerAddress] <;> ring

/-- The depth-five transfer operator is diagonal on the finite Cantor path
coordinate functions. -/
def transferOp (u : ℝ) (f : Word5 → ℝ) : Word5 → ℝ :=
  fun w => pathTransferWeight u w * f w

theorem transferOp_comm (u v : ℝ) (f : Word5 → ℝ) :
    transferOp u (transferOp v f) = transferOp v (transferOp u f) := by
  funext w
  simp [transferOp, mul_assoc, mul_left_comm, mul_comm]

/-- Functions supported on the six existing Grassmannian addresses are
eigenvectors for the finite transfer operator with the common weight-two
eigenvalue. -/
theorem transferOp_plucker_supported (u : ℝ) (f : Word5 → ℝ)
    (hsupp : ∀ w, f w ≠ 0 → ∃ i : Fin 6, w = pluckerAddress i) :
    transferOp u f = fun w => ((u - 1) ^ 2 * (u + 1) ^ 3) * f w := by
  funext w
  by_cases hw : f w = 0
  · simp [transferOp, hw]
  · obtain ⟨i, rfl⟩ := hsupp w hw
    simp [transferOp, plucker_paths_transfer_weight]

/-! ## Momentum-twistor Cauchy--Binet and row-basis covariance -/

abbrev MomentumTwistorMatrix := Matrix (Fin 4) (Fin 4) ℝ

def projectedTwistorPlane (C : Matrix2x4) (Z : MomentumTwistorMatrix) :
    Matrix2x4 := C * Z

def twistorBivector (Z : MomentumTwistorMatrix) (i j a b : Fin 4) : ℝ :=
  Z i a * Z j b - Z i b * Z j a

def projectedTwistorMinor (C : Matrix2x4) (Z : MomentumTwistorMatrix)
    (a b : Fin 4) : ℝ :=
  let Y := projectedTwistorPlane C Z
  Y 0 a * Y 1 b - Y 0 b * Y 1 a

/-- Cauchy--Binet in the repository's six-coordinate Plücker ordering. -/
theorem projectedTwistorMinor_cauchy_binet (C : Matrix2x4)
    (Z : MomentumTwistorMatrix) (a b : Fin 4) :
    projectedTwistorMinor C Z a b =
      matrixPluckerCoords C 0 * twistorBivector Z 0 1 a b +
      matrixPluckerCoords C 1 * twistorBivector Z 0 2 a b +
      matrixPluckerCoords C 2 * twistorBivector Z 0 3 a b +
      matrixPluckerCoords C 3 * twistorBivector Z 1 2 a b +
      matrixPluckerCoords C 4 * twistorBivector Z 1 3 a b +
      matrixPluckerCoords C 5 * twistorBivector Z 2 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [projectedTwistorMinor, projectedTwistorPlane, twistorBivector,
      matrixPluckerCoords_apply, Matrix.mul_apply, Fin.sum_univ_four] <;>
    all_goals ring

def detTwo (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  M.det

/-- Every Plücker channel scales by the determinant under an arbitrary
two-by-two change of row basis. -/
theorem cantorPluckerCoords_gl2_covariance
    (M : Matrix (Fin 2) (Fin 2) ℝ) (C : Matrix2x4) :
    matrixPluckerCoords (M * C) = fun i => detTwo M * matrixPluckerCoords C i := by
  funext i
  fin_cases i
  · simpa [matrixPluckerCoords_apply, pluckerMinor, detTwo] using
      (pluckerMinor_left_mul M C (0 : Fin 4) 1)
  · simpa [matrixPluckerCoords_apply, pluckerMinor, detTwo] using
      (pluckerMinor_left_mul M C (0 : Fin 4) 2)
  · simpa [matrixPluckerCoords_apply, pluckerMinor, detTwo] using
      (pluckerMinor_left_mul M C (0 : Fin 4) 3)
  · simpa [matrixPluckerCoords_apply, pluckerMinor, detTwo] using
      (pluckerMinor_left_mul M C (1 : Fin 4) 2)
  · simpa [matrixPluckerCoords_apply, pluckerMinor, detTwo] using
      (pluckerMinor_left_mul M C (1 : Fin 4) 3)
  · simpa [matrixPluckerCoords_apply, pluckerMinor, detTwo] using
      (pluckerMinor_left_mul M C (2 : Fin 4) 3)

/-- Consequently the central plabic ratio read from the Cantor channels is
invariant under every invertible row-basis change. -/
theorem cantorPlabicFaceWeight_row_basis_invariant
    (M : Matrix (Fin 2) (Fin 2) ℝ) (C : Matrix2x4)
    (hdet : detTwo M ≠ 0) :
    cantorPlabicFaceWeight (M * C) = cantorPlabicFaceWeight C := by
  rw [cantorPlabicFaceWeight_eq_pluckerRatio,
    cantorPlabicFaceWeight_eq_pluckerRatio]
  have hcov := cantorPluckerCoords_gl2_covariance M C
  have h0 := congrFun hcov 0
  have h2 := congrFun hcov 2
  have h3 := congrFun hcov 3
  have h5 := congrFun hcov 5
  rw [h0, h2, h3, h5]
  have hdet2 : detTwo M ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  calc
    (detTwo M * matrixPluckerCoords C 0 *
        (detTwo M * matrixPluckerCoords C 5)) *
        (detTwo M * matrixPluckerCoords C 2 *
          (detTwo M * matrixPluckerCoords C 3))⁻¹ =
      (detTwo M ^ 2) * (matrixPluckerCoords C 0 * matrixPluckerCoords C 5) *
        ((detTwo M ^ 2) *
          (matrixPluckerCoords C 2 * matrixPluckerCoords C 3))⁻¹ := by ring
    _ = (matrixPluckerCoords C 0 * matrixPluckerCoords C 5) *
        (matrixPluckerCoords C 2 * matrixPluckerCoords C 3)⁻¹ := by
      rw [mul_inv_rev]
      calc
        detTwo M ^ 2 * (matrixPluckerCoords C 0 * matrixPluckerCoords C 5) *
            ((matrixPluckerCoords C 2 * matrixPluckerCoords C 3)⁻¹ *
              (detTwo M ^ 2)⁻¹) =
            (detTwo M ^ 2 * (detTwo M ^ 2)⁻¹) *
              ((matrixPluckerCoords C 0 * matrixPluckerCoords C 5) *
                (matrixPluckerCoords C 2 * matrixPluckerCoords C 3)⁻¹) := by ring
        _ = 1 * ((matrixPluckerCoords C 0 * matrixPluckerCoords C 5) *
              (matrixPluckerCoords C 2 * matrixPluckerCoords C 3)⁻¹) := by
          rw [mul_inv_cancel₀ hdet2]
        _ = _ := by rw [one_mul]

/-! ## The finite Born weights on the six Plücker channels -/

/-- A real finite partition of unity.  The value type is `ℝ` so that the
normalization is an exact algebraic identity; this is not a measure on the
infinite Cantor space. -/
def IsFinitePartitionOfUnity {α : Type*} [Fintype α] (weight : α → ℝ) : Prop :=
  (∀ a, 0 ≤ weight a) ∧ ∑ a, weight a = 1

/-- Finite nonnegative weights with total mass one, packaged as a subtype so
the normalization proof is a property rather than mutable data. -/
def FinitePartitionOfUnity (α : Type*) [Fintype α] :=
  {weight : α → ℝ // IsFinitePartitionOfUnity weight}

namespace FinitePartitionOfUnity

def weight {α : Type*} [Fintype α] (p : FinitePartitionOfUnity α) : α → ℝ := p.1

theorem nonneg {α : Type*} [Fintype α] (p : FinitePartitionOfUnity α) (a : α) :
    0 ≤ p.weight a := p.2.1 a

theorem sum_one {α : Type*} [Fintype α] (p : FinitePartitionOfUnity α) :
    ∑ a, p.weight a = 1 := p.2.2

end FinitePartitionOfUnity

def pluckerSectorNormSq (M : Matrix2x4) : ℝ :=
  ∑ i : Fin 6, (matrixPluckerCoords M i) ^ 2

theorem pluckerSectorNormSq_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) : 0 < pluckerSectorNormSq M := by
  unfold pluckerSectorNormSq
  exact Finset.sum_pos
    (fun i _ => sq_pos_of_pos
      (positiveGrassmannianInterior_mem_matrixPluckerPositive M hM i))
    Finset.univ_nonempty

/-- The squared Plücker norm has homogeneous degree two under a row-basis
change, because every Plücker coordinate scales by the determinant. -/
theorem pluckerSectorNormSq_row_basis_covariant
    (A : Matrix (Fin 2) (Fin 2) ℝ) (M : Matrix2x4) :
    pluckerSectorNormSq (A * M) = detTwo A ^ 2 * pluckerSectorNormSq M := by
  unfold pluckerSectorNormSq
  rw [cantorPluckerCoords_gl2_covariance]
  calc
    (∑ i : Fin 6, (detTwo A * matrixPluckerCoords M i) ^ 2) =
        ∑ i : Fin 6, detTwo A ^ 2 * (matrixPluckerCoords M i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = detTwo A ^ 2 * ∑ i : Fin 6, (matrixPluckerCoords M i) ^ 2 := by
          rw [Finset.mul_sum]

/-- Born-rule weights obtained by normalizing the squared real Cantor
Plücker channel coefficients. -/
noncomputable def pluckerSectorProbability (M : Matrix2x4) (i : Fin 6) : ℝ :=
  (matrixPluckerCoords M i) ^ 2 / pluckerSectorNormSq M

/-- Gauge fixing by the squared Plücker norm removes the projective
`GL(2)` row-scale: normalized six-channel probabilities depend only on the
underlying two-plane. -/
theorem pluckerSectorProbability_row_basis_invariant
    (A : Matrix (Fin 2) (Fin 2) ℝ) (M : Matrix2x4)
    (hdet : detTwo A ≠ 0)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    pluckerSectorProbability (A * M) i = pluckerSectorProbability M i := by
  unfold pluckerSectorProbability
  rw [show matrixPluckerCoords (A * M) i =
      detTwo A * matrixPluckerCoords M i by
        exact congrFun (cantorPluckerCoords_gl2_covariance A M) i,
    pluckerSectorNormSq_row_basis_covariant]
  have hdet2 : detTwo A ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  field_simp [hdet2, ne_of_gt (pluckerSectorNormSq_pos M hM)]

/-- The normalized squared Plücker coefficients form a partition of unity
on the six active Grassmannian channels. -/
noncomputable def pluckerSector_pou (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    FinitePartitionOfUnity (Fin 6) := by
  refine ⟨pluckerSectorProbability M, ?_⟩
  constructor
  · intro i
    exact div_nonneg (sq_nonneg _) (le_of_lt (pluckerSectorNormSq_pos M hM))
  · unfold pluckerSectorProbability
    rw [← Finset.sum_div]
    change pluckerSectorNormSq M / pluckerSectorNormSq M = 1
    exact div_self (ne_of_gt (pluckerSectorNormSq_pos M hM))

/-- Finite amplituhedron chart cell-sum identity: the six normalized
Plücker-channel weights sum to one. This is the channel partition on the
positive `Gr(2,4)` chart, not a claim about a positroid-cell triangulation or
an integrated canonical form. -/
theorem amplituhedronChannel_partition_sum (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∑ i : Fin 6, pluckerSectorProbability M i = 1 :=
  (pluckerSector_pou M hM).2.2

theorem pluckerSectorProbability_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    0 < pluckerSectorProbability M i := by
  unfold pluckerSectorProbability
  exact div_pos (sq_pos_of_pos
    (positiveGrassmannianInterior_mem_matrixPluckerPositive M hM i))
    (pluckerSectorNormSq_pos M hM)

/-- A finite real partition of unity induces the corresponding Mathlib PMF by
the standard `ℝ → ℝ≥0∞` probability embedding. -/
noncomputable def FinitePartitionOfUnity.toPMF
    {α : Type*} [Fintype α] (p : FinitePartitionOfUnity α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p.weight a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ => p.nonneg a), p.sum_one]
    norm_num)

@[simp] theorem FinitePartitionOfUnity.toPMF_toReal
    {α : Type*} [Fintype α] (p : FinitePartitionOfUnity α) (a : α) :
    (p.toPMF a).toReal = p.weight a := by
  simp [FinitePartitionOfUnity.toPMF, PMF.ofFintype_apply, p.nonneg]

/-- Born's rule for a normalized finite complex state gives a finite
partition of unity through the squared coefficient magnitudes. -/
def finiteBornPoU {α : Type*} [Fintype α]
    (ψ : α → ℂ) (hnorm : ∑ a, Complex.normSq (ψ a) = 1) :
    FinitePartitionOfUnity α :=
  ⟨fun a => Complex.normSq (ψ a),
    ⟨fun a => Complex.normSq_nonneg (ψ a), hnorm⟩⟩

/-- The Born partition of a normalized finite vector as a Mathlib PMF. -/
noncomputable def finiteBornPMF {α : Type*} [Fintype α]
    (ψ : α → ℂ) (hnorm : ∑ a, Complex.normSq (ψ a) = 1) : PMF α :=
  (finiteBornPoU ψ hnorm).toPMF

@[simp] theorem finiteBornPMF_toReal {α : Type*} [Fintype α]
    (ψ : α → ℂ) (hnorm : ∑ a, Complex.normSq (ψ a) = 1) (i : α) :
    (finiteBornPMF ψ hnorm i).toReal = Complex.normSq (ψ i) := by
  exact ENNReal.toReal_ofReal (Complex.normSq_nonneg (ψ i))

/-- Probability law on the six active positive Grassmannian Plücker channels. -/
noncomputable def pluckerSectorPMF (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) : PMF (Fin 6) :=
  (pluckerSector_pou M hM).toPMF

@[simp] theorem pluckerSectorPMF_toReal (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    (pluckerSectorPMF M hM i).toReal = pluckerSectorProbability M i := by
  exact ENNReal.toReal_ofReal (le_of_lt (pluckerSectorProbability_pos M hM i))

/-- Normalized amplitude read from an actual Cantor `L²` cylinder.  This is
a finite-stage construction and does not assert a measure on the infinite
Cantor boundary. -/
noncomputable def pluckerCantorBornAmplitude (M : Matrix2x4) (i : Fin 6) : ℂ :=
  inner ℂ (cylinderVector5 (pluckerAddress i)) (pluckerCantorState M) /
    (‖pluckerCantorState M‖ : ℂ)

/-- A depth-five diagonal Cuntz matrix unit projects a cylinder basis vector
onto itself exactly when the addresses agree, and kills the other basis
vectors. -/
theorem cylinderProjector_apply_basis (u v : Word5) :
    cylinderMatrixUnit5 u u (cylinderVector5 v) =
      if u = v then cylinderVector5 v else 0 := by
  by_cases huv : u = v
  · subst v
    simpa using cylinderMatrixUnit5_apply_basis u u
  · rw [if_neg huv]
    change operatorWord (List.ofFn u)
      ((operatorWordDag (List.ofFn u))
        (operatorWord (List.ofFn v)
          vacuumL2)) = 0
    have hlen : (List.ofFn u).length = (List.ofFn v).length := by simp
    have hwords : List.ofFn u ≠ List.ofFn v := by
      intro h
      exact huv (List.ofFn_injective h)
    have hcomp := operatorWordDag_comp_operatorWord_of_length_eq hlen hwords
    have hcancel := congrArg
      (fun T => T vacuumL2)
      hcomp
    have hcancelVec :
        operatorWordDag (List.ofFn u)
          (operatorWord (List.ofFn v) vacuumL2) = 0 := by
      simpa using hcancel
    rw [hcancelVec]
    simp

/-- The level-five Cuntz cylinder projectors form a measurement partition:
their summed state expectation is the squared norm of the state. -/
theorem cylinderProjector_expectations_sum
    (ψ : InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport.L2Boundary) :
    (∑ w : Word5,
      inner ℂ ψ (cylinderMatrixUnit5 w w ψ)) = inner ℂ ψ ψ := by
  have hsum :
      (∑ w : Word5, cylinderMatrixUnit5 w w ψ) = ψ := by
    have h := congrArg (fun T => T ψ) cylinderMatrixUnit5_resolution
    simpa using h
  calc
    (∑ w : Word5, inner ℂ ψ (cylinderMatrixUnit5 w w ψ)) =
        inner ℂ ψ (∑ w : Word5, cylinderMatrixUnit5 w w ψ) := by
          symm
          rw [inner_sum]
    _ = inner ℂ ψ ψ := by rw [hsum]

/-- The actual Cuntz cylinder projector extracts exactly one Plücker
coefficient from the six-channel state. -/
theorem cylinderProjector_apply_pluckerState (M : Matrix2x4) (i : Fin 6) :
    cylinderMatrixUnit5 (pluckerAddress i) (pluckerAddress i)
        (pluckerCantorState M) =
      (matrixPluckerCoords M i : ℂ) • cylinderVector5 (pluckerAddress i) := by
  classical
  unfold pluckerCantorState
  simp only [map_sum]
  rw [Finset.sum_eq_single i]
  · simp only [map_smul, cylinderMatrixUnit5_apply_basis]
  · intro j _ hji
    have haddr : pluckerAddress i ≠ pluckerAddress j := fun h =>
      hji (pluckerAddress_injective h.symm)
    simp [cylinderProjector_apply_basis, haddr]
  · simp

/-- The normalized six-channel state in the actual Cantor `L²` carrier. -/
noncomputable def normalizedPluckerCantorState (M : Matrix2x4) :=
  ((‖pluckerCantorState M‖ : ℂ)⁻¹) • pluckerCantorState M

/-- The Cuntz cylinder projection extracts the normalized channel amplitude
as a rank-one output on the corresponding cylinder vector. -/
theorem cylinderProjector_apply_normalizedPluckerState
    (M : Matrix2x4) (i : Fin 6) :
    cylinderMatrixUnit5 (pluckerAddress i) (pluckerAddress i)
        (normalizedPluckerCantorState M) =
      pluckerCantorBornAmplitude M i • cylinderVector5 (pluckerAddress i) := by
  rw [normalizedPluckerCantorState, map_smul,
    cylinderProjector_apply_pluckerState, pluckerCantorBornAmplitude,
    pluckerCantorState_channel_coefficient]
  simp only [smul_smul, div_eq_mul_inv]
  congr 1
  ring

/-- A depth-five Cuntz projector outside the six Plücker channels kills the
Plücker state. -/
theorem cylinderProjector_apply_pluckerState_off_channel
    (M : Matrix2x4) (w : Word5)
    (hw : ∀ i : Fin 6, pluckerAddress i ≠ w) :
    cylinderMatrixUnit5 w w (pluckerCantorState M) = 0 := by
  classical
  unfold pluckerCantorState
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have haddr : w ≠ pluckerAddress i := Ne.symm (hw i)
  simp [cylinderProjector_apply_basis, haddr]

/-- The expectation of every inactive depth-five cylinder projector is zero. -/
theorem cylinderProjector_expectation_off_channel
    (M : Matrix2x4) (w : Word5)
    (hw : ∀ i : Fin 6, pluckerAddress i ≠ w) :
    inner ℂ (normalizedPluckerCantorState M)
      (cylinderMatrixUnit5 w w (normalizedPluckerCantorState M)) = 0 := by
  rw [normalizedPluckerCantorState, map_smul,
    cylinderProjector_apply_pluckerState_off_channel M w hw]
  simp

/-- A channel probability is the squared magnitude of its normalized
amplitude in the repository's Cantor `L²` Plücker state. -/
theorem pluckerSectorProbability_eq_cantorBorn (M : Matrix2x4) (i : Fin 6) :
    pluckerSectorProbability M i =
      Complex.normSq (pluckerCantorBornAmplitude M i) := by
  rw [pluckerSectorProbability, pluckerCantorBornAmplitude,
    pluckerCantorState_channel_coefficient]
  simp only [Complex.normSq_div, Complex.normSq_ofReal]
  unfold pluckerSectorNormSq
  rw [← pluckerCantorState_norm_sq]
  simp [pow_two]

/-- Born's rule as the actual expectation of the Cuntz cylinder projection
in the normalized Plücker state. -/
theorem cylinderProjector_expectation_eq_probability
    (M : Matrix2x4) (i : Fin 6) :
    inner ℂ (normalizedPluckerCantorState M)
        (cylinderMatrixUnit5 (pluckerAddress i) (pluckerAddress i)
          (normalizedPluckerCantorState M)) =
      (pluckerSectorProbability M i : ℂ) := by
  have hcoeff :
      inner ℂ (cylinderVector5 (pluckerAddress i))
          (normalizedPluckerCantorState M) = pluckerCantorBornAmplitude M i := by
    rw [normalizedPluckerCantorState, inner_smul_right,
      pluckerCantorBornAmplitude, pluckerCantorState_channel_coefficient]
    simp [div_eq_mul_inv, mul_comm]
  calc
    _ = pluckerCantorBornAmplitude M i *
        star (pluckerCantorBornAmplitude M i) := by
          rw [cylinderProjector_apply_normalizedPluckerState,
            inner_smul_right, ← inner_conj_symm, hcoeff]
          rfl
    _ = (Complex.normSq (pluckerCantorBornAmplitude M i) : ℂ) := by
          change inner ℂ (pluckerCantorBornAmplitude M i)
            (pluckerCantorBornAmplitude M i) = _
          rw [inner_self_eq_norm_sq_to_K]
          calc
            (‖pluckerCantorBornAmplitude M i‖ : ℂ) ^ 2 =
                ((‖pluckerCantorBornAmplitude M i‖ ^ 2 : ℝ) : ℂ) := by norm_num
            _ = (Complex.normSq (pluckerCantorBornAmplitude M i) : ℂ) :=
              congrArg (fun r : ℝ => (r : ℂ))
                (Complex.normSq_eq_norm_sq (pluckerCantorBornAmplitude M i)).symm
    _ = (pluckerSectorProbability M i : ℂ) := by
          rw [← pluckerSectorProbability_eq_cantorBorn]


/-- PMF readback as the Born probability of the normalized Cantor state. -/
@[simp] theorem pluckerSectorPMF_toReal_eq_cantorBorn (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    (pluckerSectorPMF M hM i).toReal =
      Complex.normSq (pluckerCantorBornAmplitude M i) := by
  calc
    (pluckerSectorPMF M hM i).toReal = pluckerSectorProbability M i :=
      pluckerSectorPMF_toReal M hM i
    _ = Complex.normSq (pluckerCantorBornAmplitude M i) :=
      pluckerSectorProbability_eq_cantorBorn M i

/-- Push the six-channel law to the actual five-bit cylinder addresses.  Its
support consists of the six Grassmannian channels, so this is not a full
support law on all 32 depth-five addresses. -/

noncomputable def pluckerAddressPMF (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) : PMF Word5 :=
  (pluckerSectorPMF M hM).map pluckerAddress

/-- The pushforward assigns each active cylinder exactly the probability of
its source Plücker channel. -/
theorem pluckerAddressPMF_apply (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    pluckerAddressPMF M hM (pluckerAddress i) = pluckerSectorPMF M hM i := by
  classical
  rw [pluckerAddressPMF, PMF.map_apply]
  rw [tsum_eq_single i]
  · simp
  · intro j hji
    have haddr : pluckerAddress i ≠ pluckerAddress j := fun h =>
      hji (pluckerAddress_injective h).symm
    simp [haddr]

/-- At each active address, the pushed-forward cylinder mass is the Born
probability of the normalized Cantor `L²` state. -/
theorem pluckerAddressPMF_toReal_eq_cantorBorn (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (i : Fin 6) :
    (pluckerAddressPMF M hM (pluckerAddress i)).toReal =
      Complex.normSq (pluckerCantorBornAmplitude M i) := by
  rw [pluckerAddressPMF_apply, pluckerSectorPMF_toReal_eq_cantorBorn]

theorem pluckerAddressPMF_support (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    (pluckerAddressPMF M hM).support = Set.range pluckerAddress := by
  rw [pluckerAddressPMF, PMF.support_map]
  ext w
  constructor
  · rintro ⟨i, hmem, heq⟩
    exact ⟨i, heq⟩
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_, rfl⟩
    rw [PMF.mem_support_iff]
    intro hzero
    have hpos : 0 < (pluckerSectorPMF M hM i).toReal := by
      rw [pluckerSectorPMF_toReal]
      exact pluckerSectorProbability_pos M hM i
    rw [hzero] at hpos
    norm_num at hpos

end InfoGeometry.Canonical.CantorPlabicTwistorBridge
