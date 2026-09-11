import InfoGeometry.Exceptional.STUJordanTripleSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.FreudenthalKantorTripleSystem

/-!
# The coordinatewise STU Freudenthal--Kantor triple system

The coordinatewise commutative algebra on the STU carrier supplies a genuine
finite Freudenthal--Kantor triple-system instance.  This is a concrete
prerequisite for later TKK constructions; it is not the exceptional split
Albert/Freudenthal model and does not assert an `E₇` identification.
-/

noncomputable section

namespace InfoGeometry.Exceptional.STUDatum

open InfoGeometry.Algebra

def stuTripleProductLinear :
    STUCarrier →ₗ[ℝ] STUCarrier →ₗ[ℝ] STUCarrier →ₗ[ℝ] STUCarrier where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => stuTripleProduct x y z
          map_add' := by
            intro z w
            ext i
            simp [stuTripleProduct]
            ring
          map_smul' := by
            intro r z
            ext i
            simp [stuTripleProduct]
            ring }
      map_add' := by
        intro y z
        ext i
        simp [stuTripleProduct]
        ring
      map_smul' := by
        intro r y
        ext i
        simp [stuTripleProduct]
        ring }
  map_add' := by
    intro x y
    ext z i
    simp [stuTripleProduct]
    ring
  map_smul' := by
    intro r x
    ext y z i
    simp [stuTripleProduct]
    ring

def stuFreudenthalKantorSystem :
    FreudenthalKantorTripleSystem (R := ℝ) (U := STUCarrier) where
  epsilon := -1
  delta := 1
  triple := stuTripleProductLinear
  left_identity := by
    intro x y u v w
    ext i
    simp [stuTripleProductLinear, stuTripleProduct]
    ring
  k_identity := by
    intro x y u v w
    ext i
    simp [fktsK, stuTripleProductLinear, stuTripleProduct]
    ring

@[simp] theorem stuFreudenthalKantorSystem_epsilon :
    stuFreudenthalKantorSystem.epsilon = (-1 : ℝ) := rfl

@[simp] theorem stuFreudenthalKantorSystem_delta :
    stuFreudenthalKantorSystem.delta = (1 : ℝ) := rfl

end InfoGeometry.Exceptional.STUDatum
