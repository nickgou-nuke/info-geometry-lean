/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.PolarFrameTraceDensity
import InfoGeometry.Canonical.BKMCommutatorDikin

/-!
# Polar normalization preserves BKM commutator geometry

The matrix logarithm is transported through the existing finite matrix/operator
realization.  Trace normalization adds a central operator, so its commutators,
their BKM energy, and their Dikin ellipsoid membership are unchanged at a fixed
faithful BKM density.  This connects the relative polar frame construction to
the native bounded-operator geometry without identifying different metrics.
-/

noncomputable section

namespace InfoGeometry.Canonical.PolarFrameBKMGeometry

open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
open InfoGeometry.Canonical.PolarFrameTraceDensity
open InfoGeometry.Canonical.BKMCommutatorDikin
open InfoGeometry.Canonical.DikinFiniteOrbitColimit
open InfoGeometry.Canonical.FiniteBogoliubovFrameDeformationEntropy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- Coordinate transport of subtraction on the full finite operator algebra. -/
theorem matrixOfOp_sub (A B : FiniteOperatorAlgebra n) :
    matrixOfOp (A - B) = matrixOfOp A - matrixOfOp B :=
  (LinearMap.toMatrix (ketBasis (Fin n)) (ketBasis (Fin n))).map_sub
    A.toLinearMap B.toLinearMap

/-- Coordinate transport of ordered multiplication. -/
theorem matrixOfOp_mul (A B : FiniteOperatorAlgebra n) :
    matrixOfOp (A * B) = matrixOfOp A * matrixOfOp B :=
  matrixOfOp_comp A B

/-- The negative CFC logarithm in the existing self-adjoint bounded-operator carrier. -/
def negativeLogOperator (P : Mat) : SelfAdjointOperator n :=
  ⟨matrixOp (-CFC.log P), matrixOp_isSelfAdjoint _ IsSelfAdjoint.log.neg⟩

@[simp] theorem negativeLogOperator_val (P : Mat) :
    (negativeLogOperator P).1 = matrixOp (-CFC.log P) := rfl

/-- The central normalization shift preserves every bounded-operator commutator. -/
theorem normalized_negativeLogOperator_commutator [NeZero n]
    (P : Mat) (X : FiniteOperatorAlgebra n) (hP : IsStrictlyPositive P) :
    (negativeLogOperator (normalizedDensity P)).1 * X -
        X * (negativeLogOperator (normalizedDensity P)).1 =
      (negativeLogOperator P).1 * X - X * (negativeLogOperator P).1 := by
  apply matrixOfOp_injective
  simp only [matrixOfOp_sub, matrixOfOp_mul, negativeLogOperator_val, matrixOfOp_matrixOp]
  exact neg_log_normalizedDensity_commutator P (matrixOfOp X) hP

/-- Rotating the commutator into the self-adjoint carrier also commutes with normalization. -/
theorem normalized_selfAdjointCommutator [NeZero n]
    (P : Mat) (X : SelfAdjointOperator n) (hP : IsStrictlyPositive P) :
    selfAdjointCommutator (negativeLogOperator (normalizedDensity P)) X =
      selfAdjointCommutator (negativeLogOperator P) X := by
  apply Subtype.ext
  simp only [selfAdjointCommutator_val]
  rw [normalized_negativeLogOperator_commutator P X.1 hP]

/-- At a fixed BKM density, normalization preserves the Dikin commutator energy. -/
theorem normalized_bkmDikinQuadratic [NeZero n]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (P : Mat) (X : SelfAdjointOperator n) (hP : IsStrictlyPositive P) :
    bkmDikinQuadratic D hpow
        (selfAdjointCommutator (negativeLogOperator (normalizedDensity P)) X) =
      bkmDikinQuadratic D hpow
        (selfAdjointCommutator (negativeLogOperator P) X) := by
  rw [normalized_selfAdjointCommutator P X hP]

/-- The corresponding ellipsoid constraint is preserved for every radius. -/
theorem normalized_mem_bkmDikinEllipsoid_iff [NeZero n]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (P : Mat) (X : SelfAdjointOperator n) (r : ℝ) (hP : IsStrictlyPositive P) :
    InBkmDikinEllipsoid D hpow
        (selfAdjointCommutator (negativeLogOperator (normalizedDensity P)) X) r ↔
      InBkmDikinEllipsoid D hpow
        (selfAdjointCommutator (negativeLogOperator P) X) r := by
  rw [normalized_selfAdjointCommutator P X hP]

/-- The pre-existing relative polar frame supplies the hypotheses of the BKM bridge. -/
theorem normalized_polar_frame_bkm_energy [NeZero n]
    (F : FramePair (n := Fin n)) (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (X : SelfAdjointOperator n) :
    bkmDikinQuadratic D hpow
        (selfAdjointCommutator
          (negativeLogOperator (normalizedDensity F.polarVolumeOperator)) X) =
      bkmDikinQuadratic D hpow
        (selfAdjointCommutator (negativeLogOperator F.polarVolumeOperator) X) :=
  normalized_bkmDikinQuadratic D hpow F.polarVolumeOperator X
    F.polarVolumeOperator_isStrictlyPositive

/-- Zero energy after normalization detects commutativity with the original frame surprisal. -/
theorem normalized_polar_frame_bkm_energy_eq_zero_iff [NeZero n]
    (F : FramePair (n := Fin n)) (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (X : SelfAdjointOperator n) :
    bkmDikinQuadratic D hpow
        (selfAdjointCommutator
          (negativeLogOperator (normalizedDensity F.polarVolumeOperator)) X) = 0 ↔
      Commute (matrixOp F.deformationSurprisalOperator) X.1 := by
  rw [normalized_polar_frame_bkm_energy F D hpow X]
  exact bkmDikinQuadratic_selfAdjointCommutator_eq_zero_iff D hpow
    (negativeLogOperator F.polarVolumeOperator) X

end InfoGeometry.Canonical.PolarFrameBKMGeometry
