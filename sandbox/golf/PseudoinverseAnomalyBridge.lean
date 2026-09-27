import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Singular.Drazin
import InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita

namespace InfoGeometry.Golf.PseudoinverseAnomalyBridge

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.Drazin
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita

variable {R : Type*} [CommRing R] [StarRing R]

/-- The topological defect/anomaly is defined as the commutator between the 
    Moore-Penrose inverse and the Drazin inverse. -/
def pseudoinverseAnomaly (AMP AD : R) : R :=
  AMP * AD - AD * AMP

/-- The algebraic mismatch between the Moore-Penrose projection and Drazin projection. -/
def projectionMismatch (A AMP AD : R) : R :=
  (A * AMP) - (A * AD)

/-- The Scalar Triple Product using the Parity-Twisted Levi-Civita symbol. 
    This represents the chiral volume. -/
def chiralVolume (χ : R) (u v w : Fin 3 → R) : R :=
  ∑ k : Fin 3, u k * parityTwistedCross χ v w k

/-- Map the anomaly components into a topological defect volume.
    Given three anomaly vector fields derived from the pseudoinverse mismatch,
    we compute their chiral volume. -/
def anomalyChiralVolume (χ : R) (A AMP AD : Fin 3 → R) : R :=
  chiralVolume χ A AMP AD

/-- A simple bound/identity showing that if the Moore-Penrose and Drazin 
    inverses commute, the anomaly vanishes. -/
theorem pseudoinverseAnomaly_eq_zero_of_commute (AMP AD : R) (h : AMP * AD = AD * AMP) :
    pseudoinverseAnomaly AMP AD = 0 := by
  unfold pseudoinverseAnomaly
  rw [h, sub_self]

/-- If Moore-Penrose and Drazin projections match, the mismatch is zero. -/
theorem projectionMismatch_eq_zero (A AMP AD : R) (h : A * AMP = A * AD) :
    projectionMismatch A AMP AD = 0 := by
  unfold projectionMismatch
  rw [h, sub_self]

end InfoGeometry.Golf.PseudoinverseAnomalyBridge
