import proofs.RealPin55OrthogonalCover
import proofs.RealPin55OrthogonalAction
import proofs.RealPin55MatrixRepresentation
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.OperatorAlgebra.FiveGradeActionPreservation

/-!
# The real `Pin(5,5)` action transports the native Clifford five-grading

The causal order here is: the signature-correct Pin action on `V55`, its
quadratic isometry, the induced Clifford algebra equivalence, and finally the
transport of the CAR number-operator grades.  The action transports the
grading element along with the grading; it is not claimed to fix each grade.

The independent 45-dimensional quadratic core and 55-dimensional five-lane
Lie closure remain distinct.  This bridge makes no D₅/B₅ identification.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open RealPin55Core
open RealPin55TwistedAction
open RealPin55OrthogonalAction
open RealPin55MatrixRepresentation
open V55Fin10Coordinates
open InfoGeometry.OperatorAlgebra

/-- The isometry of the split quadratic space induced by the real Pin action. -/
def fullPin55Isometry (g : FullPin55) : Q55.IsometryEquiv Q55 where
  __ := twistedVectorEquiv g
  map_app' := fullPin55_preserves_Q g

/-- The canonical Clifford-algebra lift of the real Pin action. -/
def fullPin55CliffordAlgEquiv (g : FullPin55) : Cl55 ≃ₐ[ℝ] Cl55 :=
  CliffordAlgebra.equivOfIsometry (fullPin55Isometry g)

/-- On Clifford generators, the lifted action is exactly the existing
twisted-adjoint vector action used by the `O(5,5)` representation. -/
@[simp] theorem fullPin55CliffordAlgEquiv_ι (g : FullPin55) (v : V55) :
    fullPin55CliffordAlgEquiv g (ι55 v) = ι55 (twistedVector g v) := by
  simp [fullPin55CliffordAlgEquiv, fullPin55Isometry]

/-- The algebra lift and the matrix orthogonal representation have the same
action on the ten-dimensional vector carrier. -/
theorem fullPin55_matrix_vector_readback (g : FullPin55) (v : V55) :
    ((fullPinToO55 g : O55) : M10ˣ).val.mulVec (v55Fin10Equiv v) =
      v55Fin10Equiv (twistedVector g v) := by
  simpa [fullPinToO55_coe] using fullPinMatrix_mulVec g v

/-- The CAR number operator transported by a real Pin element. -/
def fullPin55TransportedNumberOperator (g : FullPin55) : Cl55 :=
  fullPin55CliffordAlgEquiv g numberOperator55

/-- Every integer grade is carried to the corresponding grade for the
transported number operator. -/
theorem fullPin55_grade_transport (g : FullPin55) (k : ℤ) :
    Submodule.map (fullPin55CliffordAlgEquiv g).toLinearMap
        (gradeSubmodule numberOperator55 k) =
      gradeSubmodule (fullPin55TransportedNumberOperator g) k := by
  exact algEquiv_map_gradeSubmodule_transport
    (fullPin55CliffordAlgEquiv g) numberOperator55 k

/-- The positive CAR generators remain in grade `+1` for the transported
grading. -/
theorem fullPin55_creation_mem_transported_grade_one
    (g : FullPin55) (i : Fin 5) :
    fullPin55CliffordAlgEquiv g (creation55 i) ∈
      gradeSubmodule (fullPin55TransportedNumberOperator g) 1 := by
  rw [← fullPin55_grade_transport g 1]
  exact ⟨creation55 i, creation55_mem_grade_one i, rfl⟩

/-- The negative CAR generators remain in grade `-1` for the transported
grading. -/
theorem fullPin55_annihilation_mem_transported_grade_neg_one
    (g : FullPin55) (i : Fin 5) :
    fullPin55CliffordAlgEquiv g (annihilation55 i) ∈
      gradeSubmodule (fullPin55TransportedNumberOperator g) (-1) := by
  rw [← fullPin55_grade_transport g (-1)]
  exact ⟨annihilation55 i, annihilation55_mem_grade_neg_one i, rfl⟩

/-- The five homogeneous CAR lanes are preserved as a family when both the
operators and the grading element are transported by the same Pin symmetry. -/
theorem fullPin55_transports_five_grade_lanes
    (g : FullPin55) :
    (∀ i : Fin 5,
      fullPin55CliffordAlgEquiv g (creation55 i) ∈
        gradeSubmodule (fullPin55TransportedNumberOperator g) 1) ∧
    (∀ i : Fin 5,
      fullPin55CliffordAlgEquiv g (annihilation55 i) ∈
        gradeSubmodule (fullPin55TransportedNumberOperator g) (-1)) ∧
    (∀ i j : Fin 5,
      fullPin55CliffordAlgEquiv g (creation55 i * creation55 j) ∈
        gradeSubmodule (fullPin55TransportedNumberOperator g) 2) ∧
    (∀ i j : Fin 5,
      fullPin55CliffordAlgEquiv g (creation55 i * annihilation55 j) ∈
        gradeSubmodule (fullPin55TransportedNumberOperator g) 0) ∧
    (∀ i j : Fin 5,
      fullPin55CliffordAlgEquiv g (annihilation55 i * annihilation55 j) ∈
        gradeSubmodule (fullPin55TransportedNumberOperator g) (-2)) := by
  refine ⟨fullPin55_creation_mem_transported_grade_one g,
    fullPin55_annihilation_mem_transported_grade_neg_one g, ?_, ?_, ?_⟩
  · intro i j
    rw [← fullPin55_grade_transport g 2]
    exact ⟨creation55 i * creation55 j,
      creation55_mul_creation55_mem_grade_two i j,
      (fullPin55CliffordAlgEquiv g).map_mul _ _⟩
  · intro i j
    rw [← fullPin55_grade_transport g 0]
    exact ⟨creation55 i * annihilation55 j,
      creation55_mul_annihilation55_mem_grade_zero i j,
      (fullPin55CliffordAlgEquiv g).map_mul _ _⟩
  · intro i j
    rw [← fullPin55_grade_transport g (-2)]
    exact ⟨annihilation55 i * annihilation55 j,
      annihilation55_mul_annihilation55_mem_grade_neg_two i j,
      (fullPin55CliffordAlgEquiv g).map_mul _ _⟩

end InfoGeometry.Clifford.Clifford55

end noncomputable section
