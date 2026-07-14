import Mathlib
import InfoGeometry.Projective.FiveGradedCentralizer
import InfoGeometry.Projective.FiveGradedTopologicalBridge
import InfoGeometry.Projective.AndreevHorizonUnitarity
import InfoGeometry.OperatorAlgebra.ConstructiveKasparovBoundary

open InfoGeometry.Projective.Closure
open InfoGeometry.Projective.Topology
open InfoGeometry.OperatorAlgebra.ConstructiveKasparovBoundary

namespace KasparovKreinDIIIBridge

abbrev Fin2Matrix := Matrix (Fin 2) (Fin 2) ℝ

/-- Finite 2×2 DIII time-reversal operator (the Möbius-parity convention in this repo). -/
def DIII_TimeReversal : Fin2Matrix := mobiusParity2

/-- Particle-hole/CPT involution in the finite model (`C² = 1`). -/
def DIII_ParticleHole : Fin2Matrix :=
  Matrix.diagonal fun i : Fin 2 => if i = (0 : Fin 2) then (1 : ℝ) else -1

/-- Chiral grading `S = T*C` in the finite DIII certificate. -/
def DIII_Chiral : Fin2Matrix :=
  DIII_TimeReversal * DIII_ParticleHole

/-- Finite Andreev boundary involution from `(e,h) ↦ (-h, e)` as a matrix. -/
def FiniteAndreevReflection : Fin2Matrix := -mobiusParity2

/-- Signed convention relation to the DIII time reversal in this model. -/
theorem finite_andreev_reflection_eq_neg_time_reversal :
    FiniteAndreevReflection = -DIII_TimeReversal := by
  rfl

/-- Class-DIII time reversal square: `T² = -I`. -/
theorem finite_diii_time_reversal_sq :
    DIII_TimeReversal * DIII_TimeReversal = -(1 : Fin2Matrix) := by
  simpa [DIII_TimeReversal] using mobiusParity2_sq

/-- Particle-hole square: `C² = I`. -/
theorem finite_diii_particle_hole_sq :
    DIII_ParticleHole * DIII_ParticleHole = (1 : Fin2Matrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [DIII_ParticleHole, Matrix.diagonal, Matrix.mul_apply]

/-- Finite DIII anti-commutation: `T*C = -C*T`. -/
theorem finite_diii_TC_anticomm :
    DIII_TimeReversal * DIII_ParticleHole = -(DIII_ParticleHole * DIII_TimeReversal) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [DIII_TimeReversal, DIII_ParticleHole,
      Matrix.mul_apply, mobiusParity2, Matrix.diagonal]

/-- Chiral in this finite model squares to `+I`. -/
theorem finite_diii_chiral_sq :
    DIII_Chiral * DIII_Chiral = (1 : Fin2Matrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [DIII_Chiral, DIII_TimeReversal, DIII_ParticleHole,
      Matrix.mul_apply, mobiusParity2, Matrix.diagonal]

/-- Finite Andreev reflection square: `A² = -I`. -/
theorem finite_andreev_sq :
    FiniteAndreevReflection * FiniteAndreevReflection = -(1 : Fin2Matrix) := by
  simpa [FiniteAndreevReflection, DIII_TimeReversal] using finite_diii_time_reversal_sq

/-- Finite Andreev reflection is the opposite convention of the topological Möbius parity. -/
theorem finite_andreev_compat_with_topological_closure :
    FiniteAndreevReflection = -mobiusParity2 := rfl

/-- Kasparov defect packet on the finite 2×2 Andreev/DIII operator. -/
def KasparovPacket2 : KasparovDefectDatum Fin2Matrix :=
  { F := FiniteAndreevReflection }

/-- `F* = Fᵀ` on this real matrix model. -/
theorem finite_andreev_star_eq_transpose :
    star FiniteAndreevReflection = Matrix.transpose FiniteAndreevReflection := by
  ext i j
  simp [FiniteAndreevReflection, Matrix.star_apply]

/-- Isometry law for the finite Andreev/DIII operator: `FᵀF = I`. -/
theorem finite_andreev_isometry :
    Matrix.transpose FiniteAndreevReflection * FiniteAndreevReflection = (1 : Fin2Matrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [FiniteAndreevReflection, mobiusParity2, Matrix.mul_apply, Matrix.transpose_apply]

/-- Left Kasparov defect vanishes for the finite Andreev/DIII operator. -/
theorem finite_andreev_left_kasparov_defect_zero :
    leftKasparovDefect FiniteAndreevReflection = (0 : Fin2Matrix) := by
  apply leftKasparovDefect_eq_zero_of_isometry
  calc
    star FiniteAndreevReflection * FiniteAndreevReflection
        = Matrix.transpose FiniteAndreevReflection * FiniteAndreevReflection := by
          simp [finite_andreev_star_eq_transpose]
    _ = (1 : Fin2Matrix) := finite_andreev_isometry

/-- Right Kasparov defect also vanishes for this concrete operator. -/
theorem finite_andreev_right_kasparov_defect_zero :
    rightKasparovDefect FiniteAndreevReflection = (0 : Fin2Matrix) := by
  apply rightKasparovDefect_eq_zero_of_coisometry
  have hco :
      FiniteAndreevReflection * star FiniteAndreevReflection = (1 : Fin2Matrix) := by
    calc
      FiniteAndreevReflection * star FiniteAndreevReflection
          = FiniteAndreevReflection * Matrix.transpose FiniteAndreevReflection := by
            simp [finite_andreev_star_eq_transpose]
      _ = (1 : Fin2Matrix) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [FiniteAndreevReflection, mobiusParity2,
            Matrix.mul_apply, Matrix.transpose_apply]
  exact hco

/-- The concrete topological socket and the DIII time-reversal operator coincide. -/
theorem concrete_topological_socket_matches_diii_time :
    concreteTopologicalSocket2.inv.closure.moebiusParity = DIII_TimeReversal := by
  rfl

/-- Concrete topological trace-zero and Kasparov isometry assumptions assemble into an
anomaly-preserving DIII-Andreev bridge. -/
theorem concrete_diii_andreev_bridge_packet :
    (concreteTopologicalSocket2.inv.closure.moebiusParity.transpose *
      concreteTopologicalSocket2.inv.closure.moebiusParity =
      concreteTopologicalSocket2.inv.closure.I) ∧
    (KasparovPacket2.leftDefect = 0) ∧ (KasparovPacket2.rightDefect = 0) := by
  constructor
  · have h_top :
        (mobiusParity2.transpose * mobiusParity2 : Fin2Matrix) =
          (1 : Fin2Matrix) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [mobiusParity2, Matrix.mul_apply, Matrix.transpose_apply]
    simpa [concreteTopologicalSocket2, concreteSpinTopologicalInvariants2,
      mobiusClosureFromConformalInversion2, mobiusClosure2,
      DIII_TimeReversal] using h_top
  constructor
  · simpa [KasparovPacket2, ConstructiveKasparovBoundary.KasparovDefectDatum.leftDefect] using
      finite_andreev_left_kasparov_defect_zero
  · simpa [KasparovPacket2, ConstructiveKasparovBoundary.KasparovDefectDatum.rightDefect] using
      finite_andreev_right_kasparov_defect_zero

end KasparovKreinDIIIBridge
