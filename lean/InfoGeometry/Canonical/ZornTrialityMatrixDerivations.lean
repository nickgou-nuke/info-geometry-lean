/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornInfinitesimalTriality
import InfoGeometry.Algebra.Zorn.MatrixDerivation
import InfoGeometry.Algebra.ZornPinorReconstruction
import InfoGeometry.Lie.CanonicalZornDerivation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit diagonal triality and native matrix derivations

The source cross-product convention is transported by negating both spatial
slots. Its quaternion directions become `lower - upper`, and its hyperbolic
directions become `-(upper + lower)`. These expressions use the existing
canonical chiral basis; no second basis or multiplication is introduced.

The two vector-bivector combinations are identified with the existing
trace-zero matrix derivations. Their two spin actions coincide with the vector
action, giving the actual diagonal triality specialization. The square
readouts are on the indicated axis, not identities on the entire module.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornTrialityMatrixDerivations

open InfoGeometry.Canonical.ZornInfinitesimalTriality
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornDerivation

/-- The exact two traceless coefficient matrices used below do not commute.
The equalities identify the witnesses with those rotation and boost matrices. -/
theorem rotation_boost_matrices_noncommuting :
    ∃ D B : Matrix (Fin 3) (Fin 3) ℝ,
      D * B ≠ B * D ∧
        D = !![0, 1, 0; -1, 0, 0; 0, 0, 0] ∧
        B = !![0, -1, 0; -1, 0, 0; 0, 0, 0] := by
  refine ⟨!![0, 1, 0; -1, 0, 0; 0, 0, 0],
    !![0, -1, 0; -1, 0, 0; 0, 0, 0], ?_, rfl, rfl⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_three] at h00

local notation "q[" i "]" =>
  (ZornMatrix.chiralLowerBasis i - ZornMatrix.chiralUpperBasis i : ZornMatrix ℝ)
local notation "f[" i "]" =>
  (-(ZornMatrix.chiralUpperBasis i + ZornMatrix.chiralLowerBasis i) : ZornMatrix ℝ)

/-- The existing source-orientation transport gives exactly the quaternion
directions used in the triality combinations below. -/
theorem quaternionAxis_transport (i : Fin 3) :
    canonicalVectorEquiv.symm
        (InfoGeometry.Algebra.ZornPinorReconstruction.gamma
          (InfoGeometry.Algebra.ZornVec3.basis i)) = q[i] := by
  fin_cases i <;> ext j <;> (try fin_cases j) <;>
    simp [canonicalVectorEquiv, InfoGeometry.Algebra.ZornPinorReconstruction.gamma,
      InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal,
      InfoGeometry.Algebra.ZornVec3.basis,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis, Pi.single_apply]

/-- The transported hyperbolic directions use the same two native chiral slots. -/
theorem hyperbolicAxis_transport (i : Fin 3) :
    canonicalVectorEquiv.symm
        (InfoGeometry.Algebra.ZornPinorReconstruction.kappa
          (InfoGeometry.Algebra.ZornVec3.basis i)) = f[i] := by
  fin_cases i <;> ext j <;> (try fin_cases j) <;>
    simp [canonicalVectorEquiv, InfoGeometry.Algebra.ZornPinorReconstruction.kappa,
      InfoGeometry.Algebra.ZornVectorMatrix.offDiagonal,
      InfoGeometry.Algebra.ZornVec3.basis,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis, Pi.single_apply]

/-- The compact rotation as the stated difference of vector bivectors. -/
def rotationBivector : Module.End ℝ (ZornMatrix ℝ) :=
  vectorBivector q[0] q[1] - vectorBivector f[0] f[1]

/-- The noncompact boost with the source's corrected mixed-pair sign. -/
def boostBivector : Module.End ℝ (ZornMatrix ℝ) :=
  vectorBivector q[0] f[1] - vectorBivector f[0] q[1]

/-- Exact action on both spatial slots; both scalar coordinates vanish. -/
theorem rotationBivector_apply (z : ZornMatrix ℝ) :
    rotationBivector z =
      { a := 0, b := 0, x := ![z.x 1, -z.x 0, 0],
        y := ![z.y 1, -z.y 0, 0] } := by
  ext i <;> (try fin_cases i) <;>
    norm_num [rotationBivector, vectorBivector_apply, zornNorm_polarBilin_apply,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.dot, Pi.single_apply] <;> ring

/-- The boost acts by opposite transpose matrices on the two spatial slots. -/
theorem boostBivector_apply (z : ZornMatrix ℝ) :
    boostBivector z =
      { a := 0, b := 0, x := ![-z.x 1, -z.x 0, 0],
        y := ![z.y 1, z.y 0, 0] } := by
  ext i <;> (try fin_cases i) <;>
    norm_num [boostBivector, vectorBivector_apply, zornNorm_polarBilin_apply,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.dot, Pi.single_apply] <;> ring

/-- Identification with a constructed native derivation, not an assumed Leibniz law. -/
theorem rotationBivector_eq_matrixDerivation :
    rotationBivector =
      vectorToCanonicalEnd
        (InfoGeometry.Algebra.ZornVectorMatrix.matrixDerivation
          (!![0, 1, 0; -1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ)
          (by norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_three])) := by
  apply LinearMap.ext
  intro z
  rw [rotationBivector_apply]
  ext i <;> (try fin_cases i) <;>
    simp [vectorToCanonicalEnd, canonicalVectorEquiv,
      InfoGeometry.Algebra.ZornVectorMatrix.matrixDerivation,
      InfoGeometry.Algebra.ZornVectorMatrix.matrixAction,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The boost belongs to the same native traceless-matrix derivation family. -/
theorem boostBivector_eq_matrixDerivation :
    boostBivector =
      vectorToCanonicalEnd
        (InfoGeometry.Algebra.ZornVectorMatrix.matrixDerivation
          (!![0, -1, 0; -1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ)
          (by norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_three])) := by
  apply LinearMap.ext
  intro z
  rw [boostBivector_apply]
  ext i <;> (try fin_cases i) <;>
    simp [vectorToCanonicalEnd, canonicalVectorEquiv,
      InfoGeometry.Algebra.ZornVectorMatrix.matrixDerivation,
      InfoGeometry.Algebra.ZornVectorMatrix.matrixAction,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Native derivation membership follows from the existing matrix constructor. -/
theorem rotationBivector_isDerivation : IsDerivation rotationBivector := by
  rw [rotationBivector_eq_matrixDerivation]
  exact vectorToCanonicalEnd_isDerivation _

/-- In particular the boost satisfies Leibniz on arbitrary Zorn inputs. -/
theorem boostBivector_isDerivation : IsDerivation boostBivector := by
  rw [boostBivector_eq_matrixDerivation]
  exact vectorToCanonicalEnd_isDerivation _

/-- The positive chiral rotation equals the vector rotation on the full module. -/
theorem rotation_spinPlus_diagonal :
    spinPlusBivector q[0] q[1] - spinPlusBivector f[0] f[1] =
      rotationBivector := by
  apply LinearMap.ext
  intro z
  rw [rotationBivector_apply]
  ext i <;> (try fin_cases i) <;>
    norm_num [spinPlusBivector_apply, zornConj,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross, Pi.single_apply] <;> ring

/-- The negative chiral rotation has the same full-module action. -/
theorem rotation_spinMinus_diagonal :
    spinMinusBivector q[0] q[1] - spinMinusBivector f[0] f[1] =
      rotationBivector := by
  apply LinearMap.ext
  intro z
  rw [rotationBivector_apply]
  ext i <;> (try fin_cases i) <;>
    norm_num [spinMinusBivector_apply, zornConj,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross, Pi.single_apply] <;> ring

/-- The corrected mixed spin combination equals the native boost. -/
theorem boost_spinPlus_diagonal :
    spinPlusBivector q[0] f[1] - spinPlusBivector f[0] q[1] =
      boostBivector := by
  apply LinearMap.ext
  intro z
  rw [boostBivector_apply]
  ext i <;> (try fin_cases i) <;>
    norm_num [spinPlusBivector_apply, zornConj,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross, Pi.single_apply] <;> ring

/-- Both chiral boost actions coincide with the vector action. -/
theorem boost_spinMinus_diagonal :
    spinMinusBivector q[0] f[1] - spinMinusBivector f[0] q[1] =
      boostBivector := by
  apply LinearMap.ext
  intro z
  rw [boostBivector_apply]
  ext i <;> (try fin_cases i) <;>
    norm_num [spinMinusBivector_apply, zornConj,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross, Pi.single_apply] <;> ring

@[simp] theorem rotationBivector_one : rotationBivector 1 = 0 := by
  rw [rotationBivector_apply]
  ext i <;> (try fin_cases i) <;> simp

@[simp] theorem boostBivector_one : boostBivector 1 = 0 := by
  rw [boostBivector_apply]
  ext i <;> (try fin_cases i) <;> simp

/-- The rotation sends the first transported quaternion axis to minus the second. -/
theorem rotationBivector_quaternion_axis : rotationBivector q[0] = -q[1] := by
  rw [rotationBivector_apply]
  ext i <;> (try fin_cases i) <;>
    norm_num [ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis, Pi.single_apply]

/-- Compact square on the indicated quaternion axis. -/
theorem rotationBivector_square_axis : rotationBivector (rotationBivector q[0]) = -q[0] := by
  simp only [rotationBivector_apply]
  ext i <;> (try fin_cases i) <;>
    norm_num [ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis, Pi.single_apply]

/-- The boost exchanges the quaternion and hyperbolic axes with a minus sign. -/
theorem boostBivector_quaternion_axis : boostBivector q[0] = -f[1] := by
  rw [boostBivector_apply]
  ext i <;> (try fin_cases i) <;>
    norm_num [ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis, Pi.single_apply]

/-- Hyperbolic square on the indicated axis; the scalar poles remain in the kernel. -/
theorem boostBivector_square_axis : boostBivector (boostBivector q[0]) = q[0] := by
  simp only [boostBivector_apply]
  ext i <;> (try fin_cases i) <;>
    norm_num [ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis, Pi.single_apply]

/-- The rotation-boost commutator has an exact nonzero action on the first
transported quaternion axis, with the canonical hyperbolic-axis sign. -/
theorem rotation_boost_commutator_axis :
    (rotationBivector * boostBivector - boostBivector * rotationBivector) q[0] =
      (-2 : ℝ) • f[0] := by
  change rotationBivector (boostBivector q[0]) -
    boostBivector (rotationBivector q[0]) = (-2 : ℝ) • f[0]
  simp only [rotationBivector_apply, boostBivector_apply]
  ext i <;> (try fin_cases i) <;>
    norm_num [ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis, Pi.single_apply]

/-- The actual rotation and boost on the full native Zorn module do not commute. -/
theorem rotationBivector_boostBivector_ne :
    rotationBivector * boostBivector ≠ boostBivector * rotationBivector := by
  intro h
  have h0 := congrArg
    (fun T : Module.End ℝ (ZornMatrix ℝ) => (T q[0]).x 0) h
  change (rotationBivector (boostBivector q[0])).x 0 =
    (boostBivector (rotationBivector q[0])).x 0 at h0
  norm_num [rotationBivector_apply, boostBivector_apply,
    ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis, Pi.single_apply] at h0

end InfoGeometry.Canonical.ZornTrialityMatrixDerivations
