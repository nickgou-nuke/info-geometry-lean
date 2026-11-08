import InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinorVolumeOddTransport
import InfoGeometry.Clifford.Cl55ChiralSectorFlipContract

/-!
# Predicate readback for the matrix chiral sectors

The sector submodules and the native chirality predicates are two views of the
same projector equations.  This file records that readback without asserting
any octonionic model or a dimension statement.
-/

namespace InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge

open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge

theorem mem_chiralPlusSector_iff_chiralPlus (v : SpinorSpace 5) :
    v ∈ chiralPlusSector ↔ chiralPlus v := by
  exact (chiralPlus_iff_projector_fixed v).symm

theorem mem_chiralMinusSector_iff_chiralMinus (v : SpinorSpace 5) :
    v ∈ chiralMinusSector ↔ chiralMinus v := by
  exact (chiralMinus_iff_projector_fixed v).symm

theorem mem_chiralPlusSector_iff_volume_eigenvalue (v : SpinorSpace 5) :
    v ∈ chiralPlusSector ↔
      matrixApply chiralityMatrix v = v := by
  exact mem_chiralPlusSector_iff_chiralPlus v

theorem mem_chiralMinusSector_iff_volume_eigenvalue (v : SpinorSpace 5) :
    v ∈ chiralMinusSector ↔
      matrixApply chiralityMatrix v = -v := by
  exact mem_chiralMinusSector_iff_chiralMinus v

theorem odd_action_maps_plus_to_minus
    (M : SpinorMatrix 5)
    (hM : M * chiralityMatrix = -(chiralityMatrix * M))
    (v : SpinorSpace 5) (hv : chiralPlus v) :
    chiralMinus (matrixApply M v) := by
  have hM' : chiralityMatrix * M = -(M * chiralityMatrix) := by
    rw [hM]
    module
  change matrixApply chiralityMatrix (matrixApply M v) =
    -matrixApply M v
  rw [← matrixApply_mul, hM', matrixApply_neg, matrixApply_mul, hv]

theorem odd_action_maps_minus_to_plus
    (M : SpinorMatrix 5)
    (hM : M * chiralityMatrix = -(chiralityMatrix * M))
    (v : SpinorSpace 5) (hv : chiralMinus v) :
    chiralPlus (matrixApply M v) := by
  have hM' : chiralityMatrix * M = -(M * chiralityMatrix) := by
    rw [hM]
    module
  change matrixApply chiralityMatrix (matrixApply M v) =
    matrixApply M v
  rw [← matrixApply_mul, hM', matrixApply_neg, matrixApply_mul, hv]
  have hneg : matrixApply M (-v) = -matrixApply M v := by
    rw [matrixApply_eq_mulVec, matrixApply_eq_mulVec]
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [hneg]
  module

theorem cl55_odd_generator_maps_plus_to_minus
    (a : V55) (v : SpinorSpace 5) (hv : chiralPlus v) :
    chiralMinus
      (matrixApply (cl55SpinorAlgEquiv (ι55 a)) v) := by
  exact odd_action_maps_plus_to_minus
    (cl55SpinorAlgEquiv (ι55 a))
    (spinor_chirality_anticommutes_vector a) v hv

theorem cl55_odd_generator_maps_minus_to_plus
    (a : V55) (v : SpinorSpace 5) (hv : chiralMinus v) :
    chiralPlus
      (matrixApply (cl55SpinorAlgEquiv (ι55 a)) v) := by
  exact odd_action_maps_minus_to_plus
    (cl55SpinorAlgEquiv (ι55 a))
    (spinor_chirality_anticommutes_vector a) v hv

theorem cl55_odd_generator_maps_plusSector_to_minusSector
    (a : V55) (v : chiralPlusSector) :
    Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1 ∈
      chiralMinusSector := by
  rw [mem_chiralMinusSector_iff_chiralMinus]
  apply cl55_odd_generator_maps_plus_to_minus a v.1
  exact (mem_chiralPlusSector_iff_chiralPlus v.1).mp v.2

theorem cl55_odd_generator_maps_minusSector_to_plusSector
    (a : V55) (v : chiralMinusSector) :
    Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1 ∈
      chiralPlusSector := by
  rw [mem_chiralPlusSector_iff_chiralPlus]
  apply cl55_odd_generator_maps_minus_to_plus a v.1
  exact (mem_chiralMinusSector_iff_chiralMinus v.1).mp v.2

noncomputable def cl55OddGeneratorPlusToMinus (a : V55) :
    chiralPlusSector →ₗ[ℝ] chiralMinusSector where
  toFun v := ⟨Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1,
    cl55_odd_generator_maps_plusSector_to_minusSector a v⟩
  map_add' v w := by
    apply Subtype.ext
    change Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) (v.1 + w.1) =
      Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1 +
        Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) w.1
    rw [Matrix.mulVec_add]
  map_smul' c v := by
    apply Subtype.ext
    change Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) (c • v.1) =
      c • Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1
    rw [Matrix.mulVec_smul]

noncomputable def cl55OddGeneratorMinusToPlus (a : V55) :
    chiralMinusSector →ₗ[ℝ] chiralPlusSector where
  toFun v := ⟨Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1,
    cl55_odd_generator_maps_minusSector_to_plusSector a v⟩
  map_add' v w := by
    apply Subtype.ext
    change Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) (v.1 + w.1) =
      Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1 +
        Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) w.1
    rw [Matrix.mulVec_add]
  map_smul' c v := by
    apply Subtype.ext
    change Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) (c • v.1) =
      c • Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1
    rw [Matrix.mulVec_smul]

/-- The positive orthogonal generator `e₀` acts invertibly and exchanges the
two real chirality sectors. Its inverse is the same Clifford action because
the generator squares to `1`. -/
theorem cl55_positive_generator_sector_exchange_bijective :
    Function.Bijective
      (cl55OddGeneratorPlusToMinus (wittBasis (Sum.inl 0))) := by
  let a : V55 := wittBasis (Sum.inl 0)
  let A : SpinorMatrix 5 := cl55SpinorAlgEquiv (ι55 a)
  have ha : Q55 a = 1 := by
    change Q55 (wittBasis (Sum.inl 0)) = 1
    rw [wittBasis_left, Q55_e_pos]
  have hι : ι55 a * ι55 a = (Q55 a) • (1 : Cl55) := by
    rw [CliffordAlgebra.ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  have hA : A * A = 1 := by
    dsimp [A]
    calc
      cl55SpinorAlgEquiv (ι55 a) * cl55SpinorAlgEquiv (ι55 a) =
          cl55SpinorAlgEquiv (ι55 a * ι55 a) := (map_mul _ _ _).symm
      _ = cl55SpinorAlgEquiv ((Q55 a) • (1 : Cl55)) := by rw [hι]
      _ = 1 := by rw [map_smul, ha]; simp
  have hround (x : SpinorSpace 5) :
      Matrix.mulVec A (Matrix.mulVec A x) = x := by
    calc
      Matrix.mulVec A (Matrix.mulVec A x) = Matrix.mulVec (A * A) x :=
        Matrix.mulVec_mulVec x A A
      _ = Matrix.mulVec (1 : SpinorMatrix 5) x := by rw [hA]
      _ = x := by simp
  have hleft (x : chiralPlusSector) :
      cl55OddGeneratorMinusToPlus a
          (cl55OddGeneratorPlusToMinus a x) = x := by
    apply Subtype.ext
    exact hround x.1
  have hright (x : chiralMinusSector) :
      cl55OddGeneratorPlusToMinus a
          (cl55OddGeneratorMinusToPlus a x) = x := by
    apply Subtype.ext
    exact hround x.1
  constructor
  · intro x y hxy
    calc
      x = cl55OddGeneratorMinusToPlus a
            (cl55OddGeneratorPlusToMinus a x) := (hleft x).symm
      _ = cl55OddGeneratorMinusToPlus a
            (cl55OddGeneratorPlusToMinus a y) := congrArg
              (cl55OddGeneratorMinusToPlus a) hxy
      _ = y := hleft y
  · intro y
    exact ⟨cl55OddGeneratorMinusToPlus a y, hright y⟩

/-- The two real eigenspaces of the native `Cl(5,5)` volume on the 32-real
dimensional spinor carrier each have dimension sixteen. -/
theorem cl55_real_chiral_spinor_sectors_finrank :
    Module.finrank ℝ chiralPlusSector = 16 ∧
      Module.finrank ℝ chiralMinusSector = 16 := by
  exact chiralSector_finrank_each_eq_16_of_bijective
    (cl55OddGeneratorPlusToMinus (wittBasis (Sum.inl 0)))
    cl55_positive_generator_sector_exchange_bijective

end InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
