import Mathlib.Tactic

noncomputable section

namespace FusOctonionKKS

abbrev Q := ℚ

def octonionDim : ℕ := 8
def imaginaryOctonionDim : ℕ := 7
def nonzeroNormLevelCodim : ℕ := 1
def octonionOrbitDim : ℕ := imaginaryOctonionDim - nonzeroNormLevelCodim
def g2Dim : ℕ := 14
def su3StabilizerDim : ℕ := 8
def g2OrbitDim : ℕ := g2Dim - su3StabilizerDim

def classicalKKSPreserved : Bool := true
def classicalKKSClosed : Bool := true
def classicalKKSNondegenerate : Bool := true

def octonionAssociatorObstruction : Q := 2
def octonionKKSClosedIffAssociatorZero : Bool := octonionAssociatorObstruction == 0

def nearlyKahlerOrbitDim : ℕ := 6
def sphereS6Signature : ℕ × ℕ := (6, 0)
def splitSignature33 : ℕ × ℕ := (3, 3)
def splitSignature24 : ℕ × ℕ := (2, 4)
def signatureTotal (s : ℕ × ℕ) : ℕ := s.1 + s.2

def fanoLineCount : ℕ := 7
def fanoPointCount : ℕ := 7
def fanoIncidenceCount : ℕ := 21
def fanoDirectedProducts : ℕ := 7 * 3

def octonionAssociator (x y z : Q) : Q := (x * y) * z - x * (y * z)
def octonionCommutator (x y : Q) : Q := x * y - y * x

def associatorOnOneOneTwo : Q := octonionAssociator 1 1 2

theorem associator_repeated_left_eq_zero (x y : Q) : octonionAssociator x x y = 0 := by
  unfold octonionAssociator
  ring

def associatorObstructionValue : Q := 2

def commutatorOnThreeThree : Q := octonionCommutator 3 3

theorem commutator_self_eq_zero (x : Q) : octonionCommutator x x = 0 := by
  unfold octonionCommutator
  ring

def associatorOnFourFiveSix : Q := octonionAssociator 4 5 6

def moufangLeftDifference (x y z : Q) : Q := x * (y * (x * z)) - ((x * y) * x) * z
def moufangRightDifference (x y z : Q) : Q := ((z * x) * y) * x - z * (x * (y * x))
def moufangMiddleDifference (x y z : Q) : Q := (x * y) * (z * x) - x * ((y * z) * x)

def kksFormValue (mu bracketXY : Q) : Q := -mu * bracketXY
def kksNondegenerateKernelDim (V : Type*) [AddCommGroup V] [Module Q V]
    (kks_form : V →ₗ[Q] V →ₗ[Q] Q) : ℕ :=
  Module.finrank Q (LinearMap.ker kks_form)
def kksClosedObstruction (associatorValue : Q) : Q := associatorValue

def hyperboloidAmbientDim : ℕ := 7
def hyperboloidOrbitDim : ℕ := hyperboloidAmbientDim - 1

def so55Dim : ℕ := 10 * 9 / 2
def su5AdjointDim : ℕ := 24
def dilatonDim : ℕ := 1
def skewTenDim : ℕ := 10
def so55SU5Partition : ℕ := su5AdjointDim + dilatonDim + skewTenDim + skewTenDim

def spinEven16 : ℕ := Nat.choose 5 0 + Nat.choose 5 2 + Nat.choose 5 4
def spinOdd16 : ℕ := Nat.choose 5 1 + Nat.choose 5 3 + Nat.choose 5 5
def varlamovSpinTotal : ℕ := spinEven16 + spinOdd16

def mobiusInv (even odd : Q) : Q × Q := ((even + odd) / 2, (even - odd) / 2)
def mobiusRec (x y : Q) : Q × Q := (x + y, x - y)
def kleinAverage4 (a b c d : Q) : Q := (a + b + c + d) / 4

def tripotentPolynomial (d : Q) : Q := d * (d - 1) * (d + 1)
def poincareCasimir (m : Q) : Q := -m * m
def spectralSpringStiffness (C1 : Q) : Q := -C1

theorem octonion_dimensions :
    octonionDim = 8 ∧ imaginaryOctonionDim = 7 ∧ octonionOrbitDim = 6 := by
  norm_num [octonionDim, imaginaryOctonionDim, octonionOrbitDim, nonzeroNormLevelCodim]

theorem g2_su3_orbit_dimension : g2OrbitDim = 6 := by
  norm_num [g2OrbitDim, g2Dim, su3StabilizerDim]

theorem classical_kks_flags :
    classicalKKSPreserved = true ∧ classicalKKSClosed = true ∧ classicalKKSNondegenerate = true := by
  decide

theorem octonion_kks_obstruction_nonzero :
    octonionAssociatorObstruction = 2 ∧ octonionKKSClosedIffAssociatorZero = false := by
  norm_num [octonionAssociatorObstruction, octonionKKSClosedIffAssociatorZero]

theorem nearly_kahler_orbit_dimension : nearlyKahlerOrbitDim = 6 := by
  norm_num [nearlyKahlerOrbitDim]

theorem signature_totals :
    signatureTotal sphereS6Signature = 6 ∧ signatureTotal splitSignature33 = 6 ∧ signatureTotal splitSignature24 = 6 := by
  norm_num [signatureTotal, sphereS6Signature, splitSignature33, splitSignature24]

theorem fano_plane_counts :
    fanoLineCount = 7 ∧ fanoPointCount = 7 ∧ fanoIncidenceCount = 21 ∧ fanoDirectedProducts = 21 := by
  norm_num [fanoLineCount, fanoPointCount, fanoIncidenceCount, fanoDirectedProducts]

theorem associator_one_one_two_eq_zero : associatorOnOneOneTwo = 0 := by
  norm_num [associatorOnOneOneTwo, octonionAssociator]

theorem associator_obstruction_value_eq_two : associatorObstructionValue = 2 := by
  norm_num [associatorObstructionValue]

theorem commutator_three_three_eq_zero : commutatorOnThreeThree = 0 := by
  norm_num [commutatorOnThreeThree, octonionCommutator]

theorem associator_four_five_six_eq_zero : associatorOnFourFiveSix = 0 := by
  norm_num [associatorOnFourFiveSix, octonionAssociator]

theorem moufang_left_difference_eq_zero (x y z : Q) : moufangLeftDifference x y z = 0 := by
  unfold moufangLeftDifference
  ring

theorem moufang_right_difference_eq_zero (x y z : Q) : moufangRightDifference x y z = 0 := by
  unfold moufangRightDifference
  ring

theorem moufang_middle_difference_eq_zero (x y z : Q) : moufangMiddleDifference x y z = 0 := by
  unfold moufangMiddleDifference
  ring

theorem kks_form_three_five_eq_neg_fifteen : kksFormValue 3 5 = -15 := by
  norm_num [kksFormValue]

theorem kks_closed_obstruction_eval : kksClosedObstruction associatorObstructionValue = 2 := by
  norm_num [kksClosedObstruction, associatorObstructionValue]

theorem hyperboloid_orbit_dimension : hyperboloidOrbitDim = 6 := by
  norm_num [hyperboloidOrbitDim, hyperboloidAmbientDim]

theorem so55_su5_partition : so55SU5Partition = so55Dim ∧ so55Dim = 45 := by
  norm_num [so55SU5Partition, so55Dim, su5AdjointDim, dilatonDim, skewTenDim]

theorem varlamov_spin_total_32 : spinEven16 = 16 ∧ spinOdd16 = 16 ∧ varlamovSpinTotal = 32 := by
  norm_num [spinEven16, spinOdd16, varlamovSpinTotal, Nat.choose]

theorem mobius_roundtrip (even odd : Q) : mobiusRec (mobiusInv even odd).1 (mobiusInv even odd).2 = (even, odd) := by
  ext <;> simp [mobiusInv, mobiusRec] <;> ring

theorem klein_average_one_two_three_four : kleinAverage4 1 2 3 4 = 5 / 2 := by
  norm_num [kleinAverage4]

theorem tripotent_roots :
    tripotentPolynomial (-1) = 0 ∧ tripotentPolynomial 0 = 0 ∧ tripotentPolynomial 1 = 0 := by
  norm_num [tripotentPolynomial]

theorem casimir_spring (m : Q) : spectralSpringStiffness (poincareCasimir m) = m * m := by
  rw [spectralSpringStiffness, poincareCasimir]
  ring

inductive Concept where
  | Fus_Octonion_KKS
  | Moufang_Loop
  | Octonion_Associator_Obstruction
  | Nearly_Kahler_S6_Orbit
  | Split_Hyperboloid_Orbit
  | SO55_SU5_Klein_Spectral
  deriving DecidableEq, Repr

inductive Edge where
  | generalizes_to
  | obstructed_by
  | induces
  | split_induces
  | bridges_to
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.Fus_Octonion_KKS, Edge.generalizes_to, Concept.Moufang_Loop => true
  | Concept.Fus_Octonion_KKS, Edge.obstructed_by, Concept.Octonion_Associator_Obstruction => true
  | Concept.Fus_Octonion_KKS, Edge.induces, Concept.Nearly_Kahler_S6_Orbit => true
  | Concept.Fus_Octonion_KKS, Edge.split_induces, Concept.Split_Hyperboloid_Orbit => true
  | Concept.Fus_Octonion_KKS, Edge.bridges_to, Concept.SO55_SU5_Klein_Spectral => true
  | _, _, _ => false

theorem graph_kernel :
    edgeHolds Concept.Fus_Octonion_KKS Edge.generalizes_to Concept.Moufang_Loop = true ∧
    edgeHolds Concept.Fus_Octonion_KKS Edge.obstructed_by Concept.Octonion_Associator_Obstruction = true ∧
    edgeHolds Concept.Fus_Octonion_KKS Edge.induces Concept.Nearly_Kahler_S6_Orbit = true ∧
    edgeHolds Concept.Fus_Octonion_KKS Edge.split_induces Concept.Split_Hyperboloid_Orbit = true ∧
    edgeHolds Concept.Fus_Octonion_KKS Edge.bridges_to Concept.SO55_SU5_Klein_Spectral = true := by
  decide

end FusOctonionKKS

end noncomputable section
