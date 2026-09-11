import InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Algebra.SupermatrixKoszul
import InfoGeometry.Clifford.KoszulFoundation

noncomputable section

/-!
# Op-square triad bridge

This file packages the exact pivot requested in the current lane:

* the square-class trichotomy `{-1, 0, 1}`;
* the concrete hypercomplex triad `(I, N, E)`;
* the `1|1` supermatrix odd-odd Koszul sign;
* the Clifford anticommutation / volume-element parity readout.

No additional classification theorem is claimed here.
-/

namespace InfoGeometry.Clifford.OpSquareTriadBridge

open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Clifford.KoszulFoundation
open InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents

/-- The basic trichotomy of square classes. -/
inductive OpSquareClass
  | elliptic
  | parabolic
  | hyperbolic
deriving DecidableEq, Repr

/-- Classify a real number into its sign class. -/
def classifySquareValue (x : ℝ) : Option OpSquareClass :=
  if x = -1 then some .elliptic
  else if x = 0 then some .parabolic
  else if x = 1 then some .hyperbolic
  else none

@[simp] theorem classifySquareValue_neg_one : classifySquareValue (-1) = some .elliptic := by
  dsimp [classifySquareValue]
  simp
@[simp] theorem classifySquareValue_zero : classifySquareValue 0 = some .parabolic := by
  dsimp [classifySquareValue]
  -- We have to prove `if 0 = -1 then ...`
  have h : (0 : ℝ) ≠ -1 := by norm_num
  simp [h]
@[simp] theorem classifySquareValue_one : classifySquareValue 1 = some .hyperbolic := by
  dsimp [classifySquareValue]
  have h1 : (1 : ℝ) ≠ -1 := by norm_num
  have h2 : (1 : ℝ) ≠ 0 := by norm_num
  simp [h1, h2]

/-- The three scalar values `-1, 0, 1` attached to the local square classes. -/
def opSquareScalar : OpSquareClass → ℝ
  | .elliptic => -1
  | .parabolic => 0
  | .hyperbolic => 1

/-- The canonical `2 × 2` matrix model attached to each square class. -/
def opSquareMatrix : OpSquareClass → Mat2
  | .elliptic => I
  | .parabolic => N
  | .hyperbolic => E

@[simp] theorem opSquareMatrix_elliptic_sq :
    opSquareMatrix OpSquareClass.elliptic * opSquareMatrix OpSquareClass.elliptic =
      (opSquareScalar OpSquareClass.elliptic) • (1 : Mat2) := by
  simp [opSquareMatrix, opSquareScalar, I_sq]

@[simp] theorem opSquareMatrix_parabolic_sq :
    opSquareMatrix OpSquareClass.parabolic * opSquareMatrix OpSquareClass.parabolic =
      (opSquareScalar OpSquareClass.parabolic) • (1 : Mat2) := by
  simp [opSquareMatrix, opSquareScalar, N_sq]

@[simp] theorem opSquareMatrix_hyperbolic_sq :
    opSquareMatrix OpSquareClass.hyperbolic * opSquareMatrix OpSquareClass.hyperbolic =
      (opSquareScalar OpSquareClass.hyperbolic) • (1 : Mat2) := by
  simp [opSquareMatrix, opSquareScalar, E_sq]

/-- Unified square law for the canonical triad model. -/
theorem opSquareMatrix_sq (c : OpSquareClass) :
    opSquareMatrix c * opSquareMatrix c = (opSquareScalar c) • (1 : Mat2) := by
  cases c <;> simp [opSquareMatrix, opSquareScalar, I_sq, N_sq, E_sq]

/-- The supermatrix odd-odd channel is the even block product. -/
@[simp] theorem oddBlock_mul_oddBlock_bridge
    (b c e f : ℝ) :
    InfoGeometry.Algebra.SupermatrixKoszul.oddBlock b c *
        InfoGeometry.Algebra.SupermatrixKoszul.oddBlock e f =
      InfoGeometry.Algebra.SupermatrixKoszul.evenBlock (b * f) (c * e) := by
  simpa using
    (InfoGeometry.Algebra.SupermatrixKoszul.oddBlock_mul_oddBlock (R := ℝ) b c e f)

/-- The odd-odd Koszul sign is the parabolic square-zero pivot. -/
@[simp] theorem oddOdd_koszul_neg_square_bridge (x : ℝ) :
    -((-x) * x) = x * x := by
  simpa using
    (InfoGeometry.Algebra.SupermatrixKoszul.oddOdd_koszul_neg_square (R := ℝ) x)

/-- The three square classes are exactly the `-1, 0, 1` trichotomy. -/
theorem opSquareTriad_pivot :
    classifySquareValue (-1) = some OpSquareClass.elliptic ∧
      classifySquareValue 0 = some OpSquareClass.parabolic ∧
      classifySquareValue 1 = some OpSquareClass.hyperbolic := by
  exact ⟨classifySquareValue_neg_one, ⟨classifySquareValue_zero, classifySquareValue_one⟩⟩

/-- Clifford orthogonality gives the ABS-style anticommutation law. -/
theorem cliffordOrthogonal_anticommute
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (v w : M) (h : Q.IsOrtho v w) :
    CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w =
      -(CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v) := by
  exact clifford_orthogonal_anticommute (Q := Q) v w h

/-- The finite Clifford volume element picks up the expected parity sign. -/
theorem cliffordVolumeElement_involute
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (vectors : List M) :
    CliffordAlgebra.involute (cliffordVolumeElement Q vectors) =
      (-1 : R) ^ vectors.length • cliffordVolumeElement Q vectors := by
  simpa using (clifford_involute_volumeElement (Q := Q) vectors)

end InfoGeometry.Clifford.OpSquareTriadBridge
