import InfoGeometry.Clifford.ChevalleySpinorBlueprint
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford

noncomputable section

abbrev ChevalleyL5 := InfoGeometry.Algebra.FiniteSpin.Vec5R
abbrev ChevalleySpinor5 := SpinorSpace ChevalleyL5

def chevalleyBasisVector (i : Fin 5) : ChevalleyL5 :=
  Pi.single i 1

def chevalleyCoordinateCovector (i : Fin 5) : Dual ChevalleyL5 where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem chevalleyCoordinateCovector_apply_basis
    (i j : Fin 5) :
    chevalleyCoordinateCovector i (chevalleyBasisVector j) =
      if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [chevalleyCoordinateCovector, chevalleyBasisVector]
  · simp [chevalleyCoordinateCovector, chevalleyBasisVector, h]

theorem chevalley_coordinate_CAR
    (i j : Fin 5) (w : ChevalleySpinor5) :
    extAction (chevalleyBasisVector i)
        (intAction (chevalleyCoordinateCovector j) w) +
      intAction (chevalleyCoordinateCovector j)
        (extAction (chevalleyBasisVector i) w) =
      (if i = j then w else 0) := by
  have h := ext_int_anticommutator
    (chevalleyBasisVector i) (chevalleyCoordinateCovector j) w
  rw [chevalleyCoordinateCovector_apply_basis] at h
  simpa [Algebra.smul_def, eq_comm] using h

end

end InfoGeometry.Clifford
