import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.SolderingIsomorphism
import InfoGeometry.Clifford.SolderingGNSCARBridge
import InfoGeometry.Physics.NoncommutativeZornBdGDerivations
import InfoGeometry.Algebra.ZornGaugeEmergence

/-!
# Soldering roots as the native `Cl(1,1)` matrix representation

The split-soldering root matrices are the images of explicit elements of
Mathlib's `CliffordAlgebra q11` under the existing algebra equivalence
`cl11EquivMat`.  This records an actual algebraic intertwiner between the
spacetime/matrix root packet and the Clifford carrier.
-/

noncomputable section

namespace InfoGeometry.Clifford.SolderingCl11MatrixBridge

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Soldering
open InfoGeometry.Clifford.SolderingIsomorphism
open InfoGeometry.Clifford.SolderingGNSCARBridge
open InfoGeometry.Projective.SplitQuaternionRankOneProjective
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.Physics.NoncommutativeZornBdGDerivations
open InfoGeometry.Algebra.ZornGaugeEmergence
open scoped Matrix

/-- Clifford element represented by the raising soldering root. -/
def rootPlusCl11 : CliffordAlgebra q11 :=
  (1 / 2 : ℝ) •
    ((CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1)) +
      CliffordAlgebra.ι q11 (0, 1))

/-- Clifford element represented by the lowering soldering root. -/
def rootMinusCl11 : CliffordAlgebra q11 :=
  (1 / 2 : ℝ) •
    ((CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1)) -
      CliffordAlgebra.ι q11 (0, 1))

/-- The Clifford representative of the raising root is exactly its soldering
matrix under the native Pauli algebra equivalence. -/
theorem cl11EquivMat_rootPlusCl11 :
    cl11EquivMat rootPlusCl11 = rootPlus := by
  calc
    cl11EquivMat rootPlusCl11 =
        (1 / 2 : ℝ) • (J1 + Eminus) := by
          simp [rootPlusCl11, map_smul, map_add, map_mul]
          rw [Eplus_mul_Eminus]
    _ = rootPlus := by
          rw [rootPlus_eq_matrix]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [J1, Eminus, Matrix.add_apply, Matrix.smul_apply]

/-- The Clifford representative of the lowering root is exactly its soldering
matrix under the native Pauli algebra equivalence. -/
theorem cl11EquivMat_rootMinusCl11 :
    cl11EquivMat rootMinusCl11 = rootMinus := by
  calc
    cl11EquivMat rootMinusCl11 =
        (1 / 2 : ℝ) • (J1 - Eminus) := by
          simp [rootMinusCl11, map_smul, map_sub, map_mul]
          rw [Eplus_mul_Eminus]
    _ = rootMinus := by
          rw [rootMinus_eq_matrix]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [J1, Eminus, Matrix.sub_apply, Matrix.smul_apply]

/-- Soldering the spacetime null root agrees with the matrix represented by
the corresponding native Clifford element. -/
theorem soldering_vecRootPlus_eq_clifford :
    soldering vecRootPlus = cl11EquivMat rootPlusCl11 := by
  change soldering (solderingInv rootPlus) = cl11EquivMat rootPlusCl11
  rw [soldering_solderingInv, cl11EquivMat_rootPlusCl11]

/-- Soldering the opposite spacetime null root agrees with the matrix
represented by the corresponding native Clifford element. -/
theorem soldering_vecRootMinus_eq_clifford :
    soldering vecRootMinus = cl11EquivMat rootMinusCl11 := by
  change soldering (solderingInv rootMinus) = cl11EquivMat rootMinusCl11
  rw [soldering_solderingInv, cl11EquivMat_rootMinusCl11]

/-- The inverse-soldered vector of the Clifford raising root is the existing
spacetime root vector. -/
theorem rootPlusCl11_solderedVector_eq :
    solderingInv (cl11EquivMat rootPlusCl11) = vecRootPlus := by
  rw [cl11EquivMat_rootPlusCl11]
  rfl

/-- The inverse-soldered vector of the Clifford lowering root is the existing
spacetime root vector. -/
theorem rootMinusCl11_solderedVector_eq :
    solderingInv (cl11EquivMat rootMinusCl11) = vecRootMinus := by
  rw [cl11EquivMat_rootMinusCl11]
  rfl

/-- The Clifford raising root determines a null spacetime vector under the
existing soldering equivalence. -/
theorem rootPlusCl11_solderedVector_null :
    q22 (solderingInv (cl11EquivMat rootPlusCl11)) = 0 := by
  rw [rootPlusCl11_solderedVector_eq]
  exact rootPlus_null

/-- The Clifford lowering root determines a null spacetime vector under the
existing soldering equivalence. -/
theorem rootMinusCl11_solderedVector_null :
    q22 (solderingInv (cl11EquivMat rootMinusCl11)) = 0 := by
  rw [rootMinusCl11_solderedVector_eq]
  exact rootMinus_null

/-- The twistor incidence witness for the raising spacetime root is also the
incidence witness for the vector obtained directly from the Clifford element. -/
theorem rootPlusCl11_incident_twistor :
    InfoGeometry.Twistor.Incidence.Incident (0, spinorPlus)
      (solderingInv (cl11EquivMat rootPlusCl11)) := by
  rw [rootPlusCl11_solderedVector_eq]
  exact vecRootPlus_incident_twistor

/-- The twistor incidence witness for the lowering spacetime root is also the
incidence witness for the vector obtained directly from the Clifford element. -/
theorem rootMinusCl11_incident_twistor :
    InfoGeometry.Twistor.Incidence.Incident (0, spinorMinus)
      (solderingInv (cl11EquivMat rootMinusCl11)) := by
  rw [rootMinusCl11_solderedVector_eq]
  exact vecRootMinus_incident_twistor

/-- The determinant nullity of the Clifford representative is the spacetime
nullity of the soldered raising root. -/
theorem rootPlusCl11_determinant_eq_q22 :
    (cl11EquivMat rootPlusCl11).det = q22 vecRootPlus := by
  rw [← soldering_vecRootPlus_eq_clifford]
  exact det_soldering_eq_q22 vecRootPlus

/-- The determinant nullity of the Clifford representative is the spacetime
nullity of the soldered lowering root. -/
theorem rootMinusCl11_determinant_eq_q22 :
    (cl11EquivMat rootMinusCl11).det = q22 vecRootMinus := by
  rw [← soldering_vecRootMinus_eq_clifford]
  exact det_soldering_eq_q22 vecRootMinus

/-- The raising Clifford element is square-zero, transported through the
injective native algebra equivalence from the soldering CAR root. -/
theorem rootPlusCl11_sq_zero : rootPlusCl11 * rootPlusCl11 = 0 := by
  apply cl11EquivMat.injective
  simp [map_mul, cl11EquivMat_rootPlusCl11, rootPlus_sq_zero]

/-- The lowering Clifford element is square-zero, transported through the
injective native algebra equivalence from the soldering CAR root. -/
theorem rootMinusCl11_sq_zero : rootMinusCl11 * rootMinusCl11 = 0 := by
  apply cl11EquivMat.injective
  simp [map_mul, cl11EquivMat_rootMinusCl11, rootMinus_sq_zero]

/-- The Clifford representatives satisfy the same CAR anticommutator as the
soldering roots, by transport through the injective algebra equivalence. -/
theorem rootCl11_anticommutator :
    rootPlusCl11 * rootMinusCl11 + rootMinusCl11 * rootPlusCl11 = 1 := by
  apply cl11EquivMat.injective
  simp only [map_add, map_mul, map_one,
    cl11EquivMat_rootPlusCl11, cl11EquivMat_rootMinusCl11]
  exact root_anticommutator

/-! ## Clifford roots inside the associative single-color Zorn slice

The full Zorn multiplication is not asserted associative.  The existing
`embedMat2` theorem identifies an associative matrix subcarrier inside it.
Composing that map with the native Clifford algebra equivalence gives a
concrete bridge from `Cl(1,1)` into this subcarrier.
-/

/-- The Clifford algebra map into the single-color matrix slice of the
noncommutative Zorn carrier. -/
def cl11ToZorn (x : CliffordAlgebra q11) : NCZorn ℝ :=
  embedMat2 (cl11EquivMat x)

/-- The Clifford-to-Zorn map preserves multiplication. -/
theorem cl11ToZorn_mul (x y : CliffordAlgebra q11) :
    cl11ToZorn (x * y) = cl11ToZorn x * cl11ToZorn y := by
  change embedMat2 (cl11EquivMat (x * y)) = _
  rw [map_mul]
  exact embedMat2_mul (cl11EquivMat x) (cl11EquivMat y)

/-- The matrix slice embedding preserves addition, using the componentwise
additive structure of `NCZorn`. -/
theorem embedMat2_add (M N : Mat2) :
    embedMat2 (M + N) = embedMat2 M + embedMat2 N := by
  apply NCZorn.ext
  · rfl
  · ext i
    change singleColor0 (M 0 1 + N 0 1) i =
      singleColor0 (M 0 1) i + singleColor0 (N 0 1) i
    fin_cases i <;> simp [singleColor0]
  · ext i
    change singleColor0 (M 1 0 + N 1 0) i =
      singleColor0 (M 1 0) i + singleColor0 (N 1 0) i
    fin_cases i <;> simp [singleColor0]
  · rfl

/-- The single-color matrix embedding sends the zero matrix to Zorn zero. -/
theorem embedMat2_zero : embedMat2 (0 : Mat2) = (0 : NCZorn ℝ) := by
  apply NCZorn.ext
  · rfl
  · ext i
    change singleColor0 (0 : ℝ) i = 0
    fin_cases i <;> simp [singleColor0]
  · ext i
    change singleColor0 (0 : ℝ) i = 0
    fin_cases i <;> simp [singleColor0]
  · rfl

/-- The single-color matrix embedding sends the identity matrix to Zorn one. -/
theorem embedMat2_one : embedMat2 (1 : Mat2) = (1 : NCZorn ℝ) := by
  apply NCZorn.ext
  · rfl
  · ext i
    change singleColor0 0 i = (fun _ : Fin 3 => 0) i
    fin_cases i <;> simp [singleColor0]
  · ext i
    change singleColor0 0 i = (fun _ : Fin 3 => 0) i
    fin_cases i <;> simp [singleColor0]
  · rfl

/-- The Clifford-to-Zorn map preserves addition. -/
theorem cl11ToZorn_add (x y : CliffordAlgebra q11) :
    cl11ToZorn (x + y) = cl11ToZorn x + cl11ToZorn y := by
  change embedMat2 (cl11EquivMat (x + y)) =
    embedMat2 (cl11EquivMat x) + embedMat2 (cl11EquivMat y)
  rw [map_add, embedMat2_add]

/-- The Clifford-to-Zorn map preserves the multiplicative identity. -/
theorem cl11ToZorn_one : cl11ToZorn (1 : CliffordAlgebra q11) = 1 := by
  change embedMat2 (cl11EquivMat 1) = 1
  rw [map_one]
  exact embedMat2_one

/-- Associativity holds for products of Clifford images in Zorn because these
images lie in the single-color matrix subcarrier. -/
theorem cl11ToZorn_mul_assoc (x y z : CliffordAlgebra q11) :
    (cl11ToZorn x * cl11ToZorn y) * cl11ToZorn z =
      cl11ToZorn x * (cl11ToZorn y * cl11ToZorn z) := by
  exact embedMat2_mul_assoc (cl11EquivMat x) (cl11EquivMat y)
    (cl11EquivMat z)

/-- The Clifford-to-Zorn map is injective: no Clifford elements are lost in
the single-color Zorn realization. -/
theorem cl11ToZorn_injective : Function.Injective cl11ToZorn := by
  intro x y h
  apply cl11EquivMat.injective
  exact embedMat2_injective h

/-- The raising CAR root has the expected single-color Zorn image. -/
theorem cl11ToZorn_rootPlus :
    cl11ToZorn rootPlusCl11 = embedMat2 rootPlus := by
  exact congrArg embedMat2 cl11EquivMat_rootPlusCl11

/-- The lowering CAR root has the expected single-color Zorn image. -/
theorem cl11ToZorn_rootMinus :
    cl11ToZorn rootMinusCl11 = embedMat2 rootMinus := by
  exact congrArg embedMat2 cl11EquivMat_rootMinusCl11

/-- The raising-then-lowering Clifford product maps to the first Zorn Peirce
idempotent. This follows from the concrete root matrices and the existing
single-color matrix embedding. -/
theorem cl11ToZorn_rootPlus_rootMinus_eq_vacuumP1 :
    cl11ToZorn (rootPlusCl11 * rootMinusCl11) =
      (vacuumP1 : NCZorn ℝ) := by
  rw [cl11ToZorn_mul, cl11ToZorn_rootPlus, cl11ToZorn_rootMinus,
    ← embedMat2_mul]
  have hroot : rootPlus * rootMinus = !![(1 : ℝ), 0; 0, 0] := by
    rw [rootPlus_eq_matrix, rootMinus_eq_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hroot]
  apply NCZorn.ext
  · rfl
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl
  · rfl

/-- The lowering-then-raising Clifford product maps to the second Zorn Peirce
idempotent. -/
theorem cl11ToZorn_rootMinus_rootPlus_eq_vacuumP2 :
    cl11ToZorn (rootMinusCl11 * rootPlusCl11) =
      (vacuumP2 : NCZorn ℝ) := by
  rw [cl11ToZorn_mul, cl11ToZorn_rootPlus, cl11ToZorn_rootMinus,
    ← embedMat2_mul]
  have hroot : rootMinus * rootPlus = !![(0 : ℝ), 0; 0, 1] := by
    rw [rootPlus_eq_matrix, rootMinus_eq_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hroot]
  apply NCZorn.ext
  · rfl
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl
  · rfl

/-- A derivation stabilizing the Zorn vacuum annihilates the Clifford Peirce
idempotent represented by the raising-lowering product. -/
theorem stabilizing_derivation_kills_cl11_peirceP1
    (D : ZornDerivation ℝ) (hD : StabilizesVacuum D) :
    D.toFun (cl11ToZorn (rootPlusCl11 * rootMinusCl11)) = ncZornZero := by
  rw [cl11ToZorn_rootPlus_rootMinus_eq_vacuumP1]
  exact hD

/-- A vacuum-stabilizing derivation also annihilates the complementary
Clifford Peirce idempotent, by the existing Zorn stabilizer equivalence. -/
theorem stabilizing_derivation_kills_cl11_peirceP2
    (D : ZornDerivation ℝ) (hD : StabilizesVacuum D) :
    D.toFun (cl11ToZorn (rootMinusCl11 * rootPlusCl11)) = ncZornZero := by
  rw [cl11ToZorn_rootMinus_rootPlus_eq_vacuumP2]
  exact (stabilizes_vacuum_iff_P2 D).mp hD

/-- The two Clifford roots remain square-zero after their Zorn embedding. -/
theorem cl11ToZorn_roots_square_zero :
    cl11ToZorn rootPlusCl11 * cl11ToZorn rootPlusCl11 = 0 ∧
    cl11ToZorn rootMinusCl11 * cl11ToZorn rootMinusCl11 = 0 := by
  constructor
  · calc
      cl11ToZorn rootPlusCl11 * cl11ToZorn rootPlusCl11 =
          cl11ToZorn (rootPlusCl11 * rootPlusCl11) :=
            (cl11ToZorn_mul _ _).symm
      _ = 0 := by
        rw [rootPlusCl11_sq_zero]
        change embedMat2 (cl11EquivMat (0 : CliffordAlgebra q11)) = 0
        rw [map_zero]
        exact embedMat2_zero
  · calc
      cl11ToZorn rootMinusCl11 * cl11ToZorn rootMinusCl11 =
          cl11ToZorn (rootMinusCl11 * rootMinusCl11) :=
            (cl11ToZorn_mul _ _).symm
      _ = 0 := by
        rw [rootMinusCl11_sq_zero]
        change embedMat2 (cl11EquivMat (0 : CliffordAlgebra q11)) = 0
        rw [map_zero]
        exact embedMat2_zero

/-- The Clifford CAR anticommutator is preserved in the Zorn subcarrier. -/
theorem cl11ToZorn_root_anticommutator :
    cl11ToZorn rootPlusCl11 * cl11ToZorn rootMinusCl11 +
      cl11ToZorn rootMinusCl11 * cl11ToZorn rootPlusCl11 =
        embedMat2 (1 : Mat2) := by
  calc
    cl11ToZorn rootPlusCl11 * cl11ToZorn rootMinusCl11 +
        cl11ToZorn rootMinusCl11 * cl11ToZorn rootPlusCl11
      = embedMat2 (cl11EquivMat rootPlusCl11 * cl11EquivMat rootMinusCl11) +
          embedMat2 (cl11EquivMat rootMinusCl11 * cl11EquivMat rootPlusCl11) := by
          rw [cl11ToZorn_rootPlus, cl11ToZorn_rootMinus,
            cl11EquivMat_rootPlusCl11, cl11EquivMat_rootMinusCl11,
            embedMat2_mul, embedMat2_mul]
    _ = embedMat2
          (cl11EquivMat rootPlusCl11 * cl11EquivMat rootMinusCl11 +
            cl11EquivMat rootMinusCl11 * cl11EquivMat rootPlusCl11) := by
          rw [← embedMat2_add]
    _ = embedMat2 (cl11EquivMat 1) := by
          rw [← map_mul, ← map_mul, ← map_add, rootCl11_anticommutator]
    _ = embedMat2 (1 : Mat2) := by rw [map_one]

/-! ## Reconciliation with the finite-stage GNS representation

The coordinate readout below is only a retraction on the single-color image;
it is not asserted to preserve multiplication on all of `NCZorn ℝ`.
Composing the restricted readout with the existing coefficient extension and
GNS representation identifies the same root operators.
-/

/-- Read the scalar and color-zero coordinates of a Zorn element as a `2 × 2`
matrix. -/
def zornSliceMatrix (X : NCZorn ℝ) : Mat2 :=
  !![X.a, X.u 0; X.v 0, X.b]

/-- The matrix readout is a left inverse of the single-color Zorn embedding. -/
theorem zornSliceMatrix_embedMat2 (M : Mat2) :
    zornSliceMatrix (embedMat2 M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zornSliceMatrix, embedMat2, singleColor0]

/-- Apply the existing complex coefficient extension and first-stage matrix
representation to the matrix readout of a Zorn element. -/
def zornSliceGaugeStage (X : NCZorn ℝ) : gaugeStage 1 :=
  CStarMatrix.ofMatrixStarAlgEquiv
    (realMatrixToComplex (zornSliceMatrix X))

/-- On the single-color matrix image, the Zorn readout followed by coefficient
extension is exactly the existing matrix-stage map. -/
theorem zornSliceGaugeStage_embedMat2 (M : Mat2) :
    zornSliceGaugeStage (embedMat2 M) =
      CStarMatrix.ofMatrixStarAlgEquiv (realMatrixToComplex M) := by
  change CStarMatrix.ofMatrixStarAlgEquiv
      (realMatrixToComplex (zornSliceMatrix (embedMat2 M))) = _
  rw [zornSliceMatrix_embedMat2]

/-- The Clifford raising root reaches the same gauge-stage element through its
Zorn single-color image. -/
theorem zornSliceGaugeStage_cl11_rootPlus :
    zornSliceGaugeStage (cl11ToZorn rootPlusCl11) =
      rootPlusGaugeStage := by
  change CStarMatrix.ofMatrixStarAlgEquiv
      (realMatrixToComplex
        (zornSliceMatrix (cl11ToZorn rootPlusCl11))) = _
  rw [cl11ToZorn_rootPlus, zornSliceMatrix_embedMat2]
  rfl

/-- The Clifford lowering root reaches the same gauge-stage element through
its Zorn single-color image. -/
theorem zornSliceGaugeStage_cl11_rootMinus :
    zornSliceGaugeStage (cl11ToZorn rootMinusCl11) =
      rootMinusGaugeStage := by
  change CStarMatrix.ofMatrixStarAlgEquiv
      (realMatrixToComplex
        (zornSliceMatrix (cl11ToZorn rootMinusCl11))) = _
  rw [cl11ToZorn_rootMinus, zornSliceMatrix_embedMat2]
  rfl

/-- The first Clifford Peirce idempotent reaches the product of the two root
operators in the existing finite gauge stage. -/
theorem zornSliceGaugeStage_cl11_peirceP1 :
    zornSliceGaugeStage (cl11ToZorn (rootPlusCl11 * rootMinusCl11)) =
      rootPlusGaugeStage * rootMinusGaugeStage := by
  rw [cl11ToZorn_mul, cl11ToZorn_rootPlus, cl11ToZorn_rootMinus,
    ← embedMat2_mul, zornSliceGaugeStage_embedMat2]
  change CStarMatrix.ofMatrixStarAlgEquiv
      (realMatrixToComplex (rootPlus * rootMinus)) =
    CStarMatrix.ofMatrixStarAlgEquiv (realMatrixToComplex rootPlus) *
      CStarMatrix.ofMatrixStarAlgEquiv (realMatrixToComplex rootMinus)
  rw [map_mul]
  exact (CStarMatrix.ofMatrixStarAlgEquiv).map_mul _ _

/-- The complementary Clifford Peirce idempotent reaches the reversed root
product in the finite gauge stage. -/
theorem zornSliceGaugeStage_cl11_peirceP2 :
    zornSliceGaugeStage (cl11ToZorn (rootMinusCl11 * rootPlusCl11)) =
      rootMinusGaugeStage * rootPlusGaugeStage := by
  rw [cl11ToZorn_mul, cl11ToZorn_rootPlus, cl11ToZorn_rootMinus,
    ← embedMat2_mul, zornSliceGaugeStage_embedMat2]
  change CStarMatrix.ofMatrixStarAlgEquiv
      (realMatrixToComplex (rootMinus * rootPlus)) =
    CStarMatrix.ofMatrixStarAlgEquiv (realMatrixToComplex rootMinus) *
      CStarMatrix.ofMatrixStarAlgEquiv (realMatrixToComplex rootPlus)
  rw [map_mul]
  exact (CStarMatrix.ofMatrixStarAlgEquiv).map_mul _ _

/-- The Clifford/Zorn first Peirce projector, represented at the finite gauge
stage, is exactly the first Peirce projector on the GNS Hilbert space. -/
theorem cl11Zorn_peirceP1_gns_transport :
    gaugeStageGNSRepresentation
        (zornSliceGaugeStage
          (cl11ToZorn (rootPlusCl11 * rootMinusCl11))) =
      rootPlusGNSPeirceProjector := by
  rw [zornSliceGaugeStage_cl11_peirceP1]
  exact rootPlusGNSPeirceProjector_eq_gns_image.symm

/-- The complementary Clifford/Zorn projector is transported to the
complementary represented GNS Peirce projector. -/
theorem cl11Zorn_peirceP2_gns_transport :
    gaugeStageGNSRepresentation
        (zornSliceGaugeStage
          (cl11ToZorn (rootMinusCl11 * rootPlusCl11))) =
      rootMinusGNSPeirceProjector := by
  rw [zornSliceGaugeStage_cl11_peirceP2]
  exact rootMinusGNSPeirceProjector_eq_gns_image.symm

/-- End-to-end Peirce synthesis across the Clifford roots, the Zorn vacuum
idempotents, the finite gauge stage, and the represented GNS operators. The
two explicit transport equations identify the carrier maps; the remaining
fields give the idempotence, orthogonality, and resolution laws in GNS. -/
theorem cl11Zorn_gns_peirce_synthesis :
    gaugeStageGNSRepresentation
        (zornSliceGaugeStage
          (cl11ToZorn (rootPlusCl11 * rootMinusCl11))) =
      rootPlusGNSPeirceProjector ∧
    gaugeStageGNSRepresentation
        (zornSliceGaugeStage
          (cl11ToZorn (rootMinusCl11 * rootPlusCl11))) =
      rootMinusGNSPeirceProjector ∧
    rootPlusGNSPeirceProjector * rootPlusGNSPeirceProjector =
      rootPlusGNSPeirceProjector ∧
    rootMinusGNSPeirceProjector * rootMinusGNSPeirceProjector =
      rootMinusGNSPeirceProjector ∧
    rootPlusGNSPeirceProjector * rootMinusGNSPeirceProjector = 0 ∧
    rootMinusGNSPeirceProjector * rootPlusGNSPeirceProjector = 0 ∧
    rootPlusGNSPeirceProjector + rootMinusGNSPeirceProjector = 1 := by
  exact ⟨cl11Zorn_peirceP1_gns_transport,
    cl11Zorn_peirceP2_gns_transport,
    rootPlusGNSPeirceProjector_idempotent,
    rootMinusGNSPeirceProjector_idempotent,
    rootGNSPeirceProjectors_orthogonal.1,
    rootGNSPeirceProjectors_orthogonal.2,
    rootGNSPeirceProjectors_resolve_identity⟩

/-- The Clifford roots and their Zorn single-color readouts agree at the
existing finite gauge stage, whose GNS representation is governed by the
separate kernel-checked root CAR theorems. -/
theorem zorn_gauge_gns_root_compatibility :
    zornSliceGaugeStage (cl11ToZorn rootPlusCl11) = rootPlusGaugeStage ∧
    zornSliceGaugeStage (cl11ToZorn rootMinusCl11) = rootMinusGaugeStage ∧
    rootPlusGNSOperator * rootPlusGNSOperator = 0 ∧
    rootMinusGNSOperator * rootMinusGNSOperator = 0 ∧
    rootPlusGNSOperator * rootMinusGNSOperator +
      rootMinusGNSOperator * rootPlusGNSOperator = 1 := by
  exact ⟨zornSliceGaugeStage_cl11_rootPlus,
    zornSliceGaugeStage_cl11_rootMinus,
    rootPlusGNSOperator_sq, rootMinusGNSOperator_sq,
    rootGNSOperator_anticommutator⟩

/-- The raising `Cl(1,1)` element transported through the native matrix
equivalence and coefficient extension into the first gauge matrix stage. -/
def rootPlusCl11GaugeStage : gaugeStage 1 :=
  CStarMatrix.ofMatrixStarAlgEquiv
    (realMatrixToComplex (cl11EquivMat rootPlusCl11))

/-- The lowering `Cl(1,1)` element transported through the native matrix
equivalence and coefficient extension into the first gauge matrix stage. -/
def rootMinusCl11GaugeStage : gaugeStage 1 :=
  CStarMatrix.ofMatrixStarAlgEquiv
    (realMatrixToComplex (cl11EquivMat rootMinusCl11))

/-- The Clifford and soldering constructions give the same raising operator
in the first complex matrix stage. -/
theorem rootPlusCl11GaugeStage_eq :
    rootPlusCl11GaugeStage = rootPlusGaugeStage := by
  change CStarMatrix.ofMatrixStarAlgEquiv
      (realMatrixToComplex (cl11EquivMat rootPlusCl11)) =
    CStarMatrix.ofMatrixStarAlgEquiv (realMatrixToComplex rootPlus)
  rw [cl11EquivMat_rootPlusCl11]

/-- The Clifford and soldering constructions give the same lowering operator
in the first complex matrix stage. -/
theorem rootMinusCl11GaugeStage_eq :
    rootMinusCl11GaugeStage = rootMinusGaugeStage := by
  change CStarMatrix.ofMatrixStarAlgEquiv
      (realMatrixToComplex (cl11EquivMat rootMinusCl11)) =
    CStarMatrix.ofMatrixStarAlgEquiv (realMatrixToComplex rootMinus)
  rw [cl11EquivMat_rootMinusCl11]

/-! ## Shared root facts across the Clifford, spacetime, twistor, and GNS lanes -/

/-- A single raising-root compatibility packet: the native Clifford root is
square-zero; its soldered vector is null and twistor-incident; its matrix-stage
image is the established gauge root; and the corresponding first-stage GNS
operator remains square-zero.  These are linked by the explicit Clifford to
matrix and soldering equalities above.  The conjunction asserts no equivalence
between the twistor and GNS carriers. -/
theorem rootPlusCl11_cross_lane_compatibility :
    rootPlusCl11 * rootPlusCl11 = 0 ∧
    q22 (solderingInv (cl11EquivMat rootPlusCl11)) = 0 ∧
    InfoGeometry.Twistor.Incidence.Incident (0, spinorPlus)
      (solderingInv (cl11EquivMat rootPlusCl11)) ∧
    rootPlusCl11GaugeStage = rootPlusGaugeStage ∧
    rootPlusGNSOperator * rootPlusGNSOperator = 0 := by
  exact ⟨rootPlusCl11_sq_zero,
    rootPlusCl11_solderedVector_null,
    rootPlusCl11_incident_twistor,
    rootPlusCl11GaugeStage_eq,
    rootPlusGNSOperator_sq⟩

/-- The lowering-root counterpart of
`rootPlusCl11_cross_lane_compatibility`. -/
theorem rootMinusCl11_cross_lane_compatibility :
    rootMinusCl11 * rootMinusCl11 = 0 ∧
    q22 (solderingInv (cl11EquivMat rootMinusCl11)) = 0 ∧
    InfoGeometry.Twistor.Incidence.Incident (0, spinorMinus)
      (solderingInv (cl11EquivMat rootMinusCl11)) ∧
    rootMinusCl11GaugeStage = rootMinusGaugeStage ∧
    rootMinusGNSOperator * rootMinusGNSOperator = 0 := by
  exact ⟨rootMinusCl11_sq_zero,
    rootMinusCl11_solderedVector_null,
    rootMinusCl11_incident_twistor,
    rootMinusCl11GaugeStage_eq,
    rootMinusGNSOperator_sq⟩

/-- The same raising/lowering pair satisfies CAR in the Clifford and GNS
operator carriers, with the gauge-stage equalities recording the explicit
transport between those realizations. -/
theorem rootCl11_GNS_CAR_synthesis :
    rootPlusCl11 * rootMinusCl11 + rootMinusCl11 * rootPlusCl11 = 1 ∧
    rootPlusCl11GaugeStage = rootPlusGaugeStage ∧
    rootMinusCl11GaugeStage = rootMinusGaugeStage ∧
    rootPlusGNSOperator * rootMinusGNSOperator +
      rootMinusGNSOperator * rootPlusGNSOperator = 1 := by
  exact ⟨rootCl11_anticommutator,
    rootPlusCl11GaugeStage_eq,
    rootMinusCl11GaugeStage_eq,
    rootGNSOperator_anticommutator⟩

end InfoGeometry.Clifford.SolderingCl11MatrixBridge

end
