import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.Concrete

noncomputable section

namespace InfoGeometry.Quantum.CircularPauliCausalCone

open Matrix
open InfoGeometry.Quantum.PauliSoldering

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2C

structure Rail where
  scalar : ℂ
  spatial : Fin 3 → ℂ

def sR (r : Rail) : ℂ := r.spatial 0 - Complex.I * r.spatial 1
def sL (r : Rail) : ℂ := r.spatial 0 + Complex.I * r.spatial 1

def railMatrix (r : Rail) : Mat2 :=
  !![r.scalar + r.spatial 2, sR r;
     sL r, r.scalar - r.spatial 2]

def uPlus : Mat2 := !![1, 0; 0, 0]
def uMinus : Mat2 := !![0, 0; 0, 1]
def sigmaPlus : Mat2 := !![0, 1; 0, 0]
def sigmaMinus : Mat2 := !![0, 0; 1, 0]

@[simp] theorem uPlus_sq : uPlus * uPlus = uPlus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uPlus, Matrix.mul_apply]

@[simp] theorem uMinus_sq : uMinus * uMinus = uMinus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uMinus, Matrix.mul_apply]

@[simp] theorem uPlus_mul_uMinus : uPlus * uMinus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uPlus, uMinus, Matrix.mul_apply]

@[simp] theorem uMinus_mul_uPlus : uMinus * uPlus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uPlus, uMinus, Matrix.mul_apply]

@[simp] theorem sigmaPlus_sq : sigmaPlus * sigmaPlus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaPlus, Matrix.mul_apply]

@[simp] theorem sigmaMinus_sq : sigmaMinus * sigmaMinus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaMinus, Matrix.mul_apply]

@[simp] theorem sigmaPlus_mul_sigmaMinus :
    sigmaPlus * sigmaMinus = uPlus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaMinus, uPlus, Matrix.mul_apply]

@[simp] theorem sigmaMinus_mul_sigmaPlus :
    sigmaMinus * sigmaPlus = uMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaMinus, uMinus, Matrix.mul_apply]

@[simp] theorem circular_basis_from_pauli :
    uPlus = ((1 / 2 : ℂ) • (σ0 + σ3)) ∧
      uMinus = ((1 / 2 : ℂ) • (σ0 - σ3)) ∧
      sigmaPlus = σPlus ∧ sigmaMinus = σMinus := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [uPlus, uMinus, sigmaPlus, sigmaMinus, σ0, σ1, σ2, σ3,
        InfoGeometry.Quantum.PauliSoldering.σPlus,
        InfoGeometry.Quantum.PauliSoldering.σMinus] <;>
      norm_num

def causalMatrix (xPlus xMinus z zbar : ℂ) : Mat2 :=
  !![xPlus, zbar; z, xMinus]

@[simp] theorem causalMatrix_det (xPlus xMinus z zbar : ℂ) :
    (causalMatrix xPlus xMinus z zbar).det = xPlus * xMinus - zbar * z := by
  simp [causalMatrix, Matrix.det_fin_two]

theorem causalMatrix_circular_expansion
    (xPlus xMinus z zbar : ℂ) :
    causalMatrix xPlus xMinus z zbar =
      xPlus • uPlus + xMinus • uMinus + zbar • sigmaPlus + z • sigmaMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [causalMatrix, uPlus, uMinus, sigmaPlus, sigmaMinus]

@[simp] theorem railMatrix_det (r : Rail) :
    (railMatrix r).det =
      r.scalar ^ 2 - (r.spatial 0) ^ 2 -
        (r.spatial 1) ^ 2 - (r.spatial 2) ^ 2 := by
    simp [railMatrix, sR, sL, Matrix.det_fin_two, pow_two,
      Complex.I_mul_I]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring

theorem railMatrix_cayley_hamilton (r : Rail) :
    railMatrix r * railMatrix r =
      (2 * r.scalar) • railMatrix r -
        (railMatrix r).det • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [railMatrix, sR, sL, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_two, Complex.I_sq, sub_eq_add_neg]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring

theorem railMatrix_square_eq_zero_of_trace_zero_and_null (r : Rail)
    (hr : r.scalar ^ 2 - (r.spatial 0) ^ 2 -
      (r.spatial 1) ^ 2 - (r.spatial 2) ^ 2 = 0)
    (htrace : r.scalar = 0) :
    railMatrix r * railMatrix r = 0 := by
  rw [railMatrix_cayley_hamilton, htrace, railMatrix_det, hr]
  simp

theorem railMatrix_circular_expansion (r : Rail) :
    railMatrix r =
      (r.scalar + r.spatial 2) • uPlus +
      (r.scalar - r.spatial 2) • uMinus +
      sR r • sigmaPlus + sL r • sigmaMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [railMatrix, sR, sL, uPlus, uMinus, sigmaPlus, sigmaMinus]

theorem rail_circular_coordinates (r : Rail) :
    sR r = r.spatial 0 - Complex.I * r.spatial 1 ∧
      sL r = r.spatial 0 + Complex.I * r.spatial 1 :=
  ⟨rfl, rfl⟩

/-! ## Three-component Pauli operator sheets -/

abbrev Vector3 := InfoGeometry.Algebra.FiniteSpin.Vec3C

def orderedDot (x y : Vector3) : ℂ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def orderedCross (x y : Vector3) : Vector3
  | 0 => x 1 * y 2 - x 2 * y 1
  | 1 => x 2 * y 0 - x 0 * y 2
  | 2 => x 0 * y 1 - x 1 * y 0

def pauliVector (x : Vector3) : Mat2 :=
  !![x 2, x 0 - Complex.I * x 1;
     x 0 + Complex.I * x 1, -x 2]

def eR : Mat2 := sigmaPlus
def eL : Mat2 := sigmaMinus

@[simp] theorem eR_eq_sigmaPlus : eR = sigmaPlus := rfl
@[simp] theorem eL_eq_sigmaMinus : eL = sigmaMinus := rfl

structure ChiralRailCoords (𝕜 : Type*) where
  u : 𝕜
  s : Fin 3 → 𝕜

structure TwoRailCoords (𝕜 : Type*) where
  plus : ChiralRailCoords 𝕜
  minus : ChiralRailCoords 𝕜

def railSolder (r : ChiralRailCoords ℂ) : Mat2 :=
  r.u • σ0 + pauliVector r.s

def zornShell (z : TwoRailCoords ℂ) : Matrix (Fin 2) (Fin 2) Mat2 :=
  !![z.plus.u • σ0, pauliVector z.plus.s;
     pauliVector z.minus.s, z.minus.u • σ0]

@[simp] theorem railSolder_apply (r : ChiralRailCoords ℂ) :
    railSolder r =
      !![r.u + r.s 2, r.s 0 - Complex.I * r.s 1;
         r.s 0 + Complex.I * r.s 1, r.u - r.s 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [railSolder, pauliVector, σ0, σ1, σ2, σ3,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

@[simp] theorem zornShell_entries (z : TwoRailCoords ℂ) :
    zornShell z 0 0 = z.plus.u • σ0 ∧
      zornShell z 0 1 = pauliVector z.plus.s ∧
      zornShell z 1 0 = pauliVector z.minus.s ∧
      zornShell z 1 1 = z.minus.u • σ0 := by
  simp [zornShell]

@[simp] theorem pauliVector_apply (x : Vector3) :
    pauliVector x = x 0 • σ1 + x 1 • σ2 + x 2 • σ3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, σ1, σ2, σ3, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

theorem pauliVector_mul (x y : Vector3) :
    pauliVector x * pauliVector y =
      !![orderedDot x y + Complex.I * orderedCross x y 2,
         orderedCross x y 1 + Complex.I * orderedCross x y 0;
         -orderedCross x y 1 + Complex.I * orderedCross x y 0,
         orderedDot x y - Complex.I * orderedCross x y 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, orderedDot, orderedCross, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_sq, sub_eq_add_neg]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring

theorem pauliVector_square (x : Vector3) :
    pauliVector x * pauliVector x =
      !![orderedDot x x, 0; 0, orderedDot x x] := by
  rw [pauliVector_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orderedDot, orderedCross, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    <;> ring

theorem pauliVector_square_eq_zero {x : Vector3}
    (hx : orderedDot x x = 0) :
    pauliVector x * pauliVector x = 0 := by
  rw [pauliVector_square, hx]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def scalarReadout (M : Mat2) : ℂ :=
  (M 0 0 + M 1 1) / 2

def vectorReadout (M : Mat2) : Vector3
  | 0 => (M 1 0 + M 0 1) / 2
  | 1 => (M 1 0 - M 0 1) / (2 * Complex.I)
  | 2 => (M 0 0 - M 1 1) / 2

@[simp] theorem scalarReadout_pauliVector_mul (x y : Vector3) :
    scalarReadout (pauliVector x * pauliVector y) = orderedDot x y := by
  rw [pauliVector_mul]
  simp [scalarReadout, orderedDot, orderedCross]

@[simp] theorem vectorReadout_pauliVector_mul (x y : Vector3) :
    vectorReadout (pauliVector x * pauliVector y) =
      fun k => Complex.I * orderedCross x y k := by
  funext k
  fin_cases k <;>
    rw [pauliVector_mul] <;>
    simp [vectorReadout, orderedCross, Complex.I_sq] <;>
    field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def pauliScalarCorrelation (x y : Vector3) : ℂ :=
  scalarReadout (pauliVector x * pauliVector y)

def pauliVectorCorrelation (x y : Vector3) : Vector3 :=
  vectorReadout (pauliVector x * pauliVector y)

@[simp] theorem pauliScalarCorrelation_eq_orderedDot
    (x y : Vector3) :
    pauliScalarCorrelation x y = orderedDot x y := by
  exact scalarReadout_pauliVector_mul x y

@[simp] theorem pauliVectorCorrelation_eq_i_orderedCross
    (x y : Vector3) :
    pauliVectorCorrelation x y = fun k => Complex.I * orderedCross x y k := by
  exact vectorReadout_pauliVector_mul x y

/-! The two correlation channels carry the expected symmetric/antisymmetric
parts independently of any supergrading: the scalar channel is symmetric,
while the oriented vector channel is antisymmetric. -/

theorem pauliScalarCorrelation_comm (x y : Vector3) :
    pauliScalarCorrelation x y = pauliScalarCorrelation y x := by
  rw [pauliScalarCorrelation_eq_orderedDot,
    pauliScalarCorrelation_eq_orderedDot]
  simp [orderedDot, mul_comm, add_comm, add_left_comm, add_assoc]

theorem pauliVectorCorrelation_anticomm (x y : Vector3) :
    pauliVectorCorrelation x y = -pauliVectorCorrelation y x := by
  rw [pauliVectorCorrelation_eq_i_orderedCross,
    pauliVectorCorrelation_eq_i_orderedCross]
  funext k
  fin_cases k <;> simp [orderedCross] <;> ring

def zornX (X : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) : Vector3
  | 0 => X.x1
  | 1 => X.x2
  | 2 => X.x3

def zornY (X : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) : Vector3
  | 0 => X.y1
  | 1 => X.y2
  | 2 => X.y3

@[simp] theorem orderedDot_zornX_zornY
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    orderedDot (zornX X) (zornY Y) =
      X.x1 * Y.y1 + X.x2 * Y.y2 + X.x3 * Y.y3 := by
  simp [orderedDot, zornX, zornY]

@[simp] theorem orderedDot_zornY_zornX
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    orderedDot (zornY X) (zornX Y) =
      X.y1 * Y.x1 + X.y2 * Y.x2 + X.y3 * Y.x3 := by
  simp [orderedDot, zornX, zornY]

theorem zornCell_ext {X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ}
    (hr : X.r = Y.r) (hs : X.s = Y.s)
    (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2) (hx3 : X.x3 = Y.x3)
    (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) (hy3 : X.y3 = Y.y3) :
    X = Y := by
  cases X
  cases Y
  simp_all

def pauliCorrelationReadout
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ where
  r := X.r * Y.r + pauliScalarCorrelation (zornX X) (zornY Y)
  s := pauliScalarCorrelation (zornY X) (zornX Y) + X.s * Y.s
  x1 := X.r * Y.x1 + Y.s * X.x1 +
    Complex.I * pauliVectorCorrelation (zornY X) (zornY Y) 0
  x2 := X.r * Y.x2 + Y.s * X.x2 +
    Complex.I * pauliVectorCorrelation (zornY X) (zornY Y) 1
  x3 := X.r * Y.x3 + Y.s * X.x3 +
    Complex.I * pauliVectorCorrelation (zornY X) (zornY Y) 2
  y1 := Y.r * X.y1 + X.s * Y.y1 -
    Complex.I * pauliVectorCorrelation (zornX X) (zornX Y) 0
  y2 := Y.r * X.y2 + X.s * Y.y2 -
    Complex.I * pauliVectorCorrelation (zornX X) (zornX Y) 1
  y3 := Y.r * X.y3 + X.s * Y.y3 -
    Complex.I * pauliVectorCorrelation (zornX X) (zornX Y) 2

theorem zornMul_eq_pauliCorrelationReadout
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ X Y =
      pauliCorrelationReadout X Y := by
  cases X
  cases Y
  apply zornCell_ext <;>
    simp [pauliCorrelationReadout, zornX, zornY,
      pauliScalarCorrelation_eq_orderedDot,
      pauliVectorCorrelation_eq_i_orderedCross,
      InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ,
      orderedDot, orderedCross, pow_two, Complex.I_sq] <;>
    ring_nf <;> try rw [Complex.I_sq] <;> ring

def zornCorrelationReadout
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ :=
  pauliCorrelationReadout X Y

theorem zornCorrelationReadout_eq_zornMul
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    zornCorrelationReadout X Y =
      InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ X Y := by
  symm
  exact zornMul_eq_pauliCorrelationReadout X Y

theorem zornCorrelationReadout_r
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    (zornCorrelationReadout X Y).r =
      X.r * Y.r + pauliScalarCorrelation (zornX X) (zornY Y) := rfl

theorem zornCorrelationReadout_s
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    (zornCorrelationReadout X Y).s =
      pauliScalarCorrelation (zornY X) (zornX Y) + X.s * Y.s := rfl

theorem zornCorrelationReadout_x1
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    (zornCorrelationReadout X Y).x1 =
      X.r * Y.x1 + Y.s * X.x1 +
        Complex.I * pauliVectorCorrelation (zornY X) (zornY Y) 0 := rfl

theorem zornCorrelationReadout_y1
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    (zornCorrelationReadout X Y).y1 =
      Y.r * X.y1 + X.s * Y.y1 -
        Complex.I * pauliVectorCorrelation (zornX X) (zornX Y) 0 := rfl

theorem zornCorrelationReadout_x2
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    (zornCorrelationReadout X Y).x2 =
      X.r * Y.x2 + Y.s * X.x2 +
        Complex.I * pauliVectorCorrelation (zornY X) (zornY Y) 1 := rfl

theorem zornCorrelationReadout_x3
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    (zornCorrelationReadout X Y).x3 =
      X.r * Y.x3 + Y.s * X.x3 +
        Complex.I * pauliVectorCorrelation (zornY X) (zornY Y) 2 := rfl

theorem zornCorrelationReadout_y2
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    (zornCorrelationReadout X Y).y2 =
      Y.r * X.y2 + X.s * Y.y2 -
        Complex.I * pauliVectorCorrelation (zornX X) (zornX Y) 1 := rfl

theorem zornCorrelationReadout_y3
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    (zornCorrelationReadout X Y).y3 =
      Y.r * X.y3 + X.s * Y.y3 -
        Complex.I * pauliVectorCorrelation (zornX X) (zornX Y) 2 := rfl

theorem zornCorrelationReadout_eq_mul
    (X Y : InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ) :
    zornCorrelationReadout X Y = X * Y := by
  simpa [InfoGeometry.Algebra.Zorn.Concrete.ZornCell.instMulZornCell] using
    zornCorrelationReadout_eq_zornMul X Y

structure OperatorSheet where
  scalar : ℂ
  spatial : Vector3

def sheetMatrix (S : OperatorSheet) : Mat2 :=
  S.scalar • σ0 + pauliVector S.spatial

def crossSheet (S T : OperatorSheet) : Mat2 :=
  sheetMatrix S * sheetMatrix T

theorem crossSheet_pauli_decomposition (S T : OperatorSheet) :
    crossSheet S T =
      (S.scalar * T.scalar + orderedDot S.spatial T.spatial) • σ0 +
      (S.scalar • T.spatial + T.scalar • S.spatial +
        fun k => Complex.I * orderedCross S.spatial T.spatial k) 0 • σ1 +
      (S.scalar • T.spatial + T.scalar • S.spatial +
        fun k => Complex.I * orderedCross S.spatial T.spatial k) 1 • σ2 +
      (S.scalar • T.spatial + T.scalar • S.spatial +
        fun k => Complex.I * orderedCross S.spatial T.spatial k) 2 • σ3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossSheet, sheetMatrix, pauliVector, orderedDot, orderedCross,
      Matrix.mul_apply, Fin.sum_univ_two, σ0, σ1, σ2, σ3,
      sub_eq_add_neg, Complex.I_sq, pow_two]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring

/-! ## Zorn multiplication readout from Pauli correlations -/

/-- The two full Pauli-soldered rails are the two vector slots of a concrete
Zorn cell.  The rails remain separate: this is a coordinate readout, not an
algebra homomorphism from Zorn multiplication into matrix multiplication. -/
def twoRailZornCell (z : TwoRailCoords ℂ) :
    InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ where
  r := z.plus.u
  s := z.minus.u
  x1 := z.plus.s 0
  x2 := z.plus.s 1
  x3 := z.plus.s 2
  y1 := z.minus.s 0
  y2 := z.minus.s 1
  y3 := z.minus.s 2

/-- The upper-left Zorn product coordinate is the scalar Pauli correlation of
the upper rail of the first cell with the lower rail of the second cell. -/
theorem twoRailZornCell_mul_r_eq_pauliScalarCorrelation
    (z w : TwoRailCoords ℂ) :
    (InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (twoRailZornCell z) (twoRailZornCell w)).r =
      z.plus.u * w.plus.u +
        scalarReadout (pauliVector z.plus.s * pauliVector w.minus.s) := by
  rw [scalarReadout_pauliVector_mul]
  simp [twoRailZornCell,
    InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ,
    orderedDot]

/-- The lower-right Zorn product coordinate is the scalar Pauli correlation of
the lower rail of the first cell with the upper rail of the second cell. -/
theorem twoRailZornCell_mul_s_eq_pauliScalarCorrelation
    (z w : TwoRailCoords ℂ) :
    (InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (twoRailZornCell z) (twoRailZornCell w)).s =
      scalarReadout (pauliVector z.minus.s * pauliVector w.plus.s) +
        z.minus.u * w.minus.u := by
  rw [scalarReadout_pauliVector_mul]
  simp [twoRailZornCell,
    InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ,
    orderedDot]

/-- Pauli vector readout for the upper-right Zorn slot. -/
def twoRailZornXReadout (z w : TwoRailCoords ℂ) : Vector3 :=
  fun k => z.plus.u * w.plus.s k + w.minus.u * z.plus.s k +
    Complex.I * vectorReadout
      (pauliVector z.minus.s * pauliVector w.minus.s) k

/-- Pauli vector readout for the lower-left Zorn slot. -/
def twoRailZornYReadout (z w : TwoRailCoords ℂ) : Vector3 :=
  fun k => w.plus.u * z.minus.s k + z.minus.u * w.minus.s k -
    Complex.I * vectorReadout
      (pauliVector z.plus.s * pauliVector w.plus.s) k

/-- The three upper-right Zorn coordinates are recovered from the opposite
Pauli vector correlation with the positive chiral orientation. -/
theorem twoRailZornCell_mul_x_eq_pauliVectorCorrelation
    (z w : TwoRailCoords ℂ) :
    (InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (twoRailZornCell z) (twoRailZornCell w)).x1 =
        twoRailZornXReadout z w 0 ∧
      (InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (twoRailZornCell z) (twoRailZornCell w)).x2 =
        twoRailZornXReadout z w 1 ∧
      (InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (twoRailZornCell z) (twoRailZornCell w)).x3 =
        twoRailZornXReadout z w 2 := by
  constructor
  · dsimp [twoRailZornXReadout]
    rw [vectorReadout_pauliVector_mul]
    simp [twoRailZornXReadout, twoRailZornCell,
      InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ,
      orderedCross, pow_two] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring
  · constructor <;> dsimp [twoRailZornXReadout] <;>
      rw [vectorReadout_pauliVector_mul] <;>
      simp [twoRailZornXReadout, twoRailZornCell,
        InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ,
        orderedCross, pow_two] <;>
      ring_nf <;> rw [Complex.I_sq] <;> ring

/-- The three lower-left Zorn coordinates are recovered from the opposite
Pauli vector correlation with the negative chiral orientation. -/
theorem twoRailZornCell_mul_y_eq_pauliVectorCorrelation
    (z w : TwoRailCoords ℂ) :
    (InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (twoRailZornCell z) (twoRailZornCell w)).y1 =
        twoRailZornYReadout z w 0 ∧
      (InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (twoRailZornCell z) (twoRailZornCell w)).y2 =
        twoRailZornYReadout z w 1 ∧
      (InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (twoRailZornCell z) (twoRailZornCell w)).y3 =
        twoRailZornYReadout z w 2 := by
  constructor
  · dsimp [twoRailZornYReadout]
    rw [vectorReadout_pauliVector_mul]
    simp [twoRailZornYReadout, twoRailZornCell,
      InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ,
      orderedCross, pow_two] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring
  · constructor <;> dsimp [twoRailZornYReadout] <;>
      rw [vectorReadout_pauliVector_mul] <;>
      simp [twoRailZornYReadout, twoRailZornCell,
        InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ,
        orderedCross, pow_two] <;>
      ring_nf <;> rw [Complex.I_sq] <;> ring

/-- Complete reconstruction of the genuine Zorn product from the four Pauli
correlation channels. -/
def twoRailPauliCorrelationProduct (z w : TwoRailCoords ℂ) :
    InfoGeometry.Algebra.Zorn.Concrete.ZornCell ℂ where
  r := z.plus.u * w.plus.u +
    scalarReadout (pauliVector z.plus.s * pauliVector w.minus.s)
  s := scalarReadout (pauliVector z.minus.s * pauliVector w.plus.s) +
    z.minus.u * w.minus.u
  x1 := twoRailZornXReadout z w 0
  x2 := twoRailZornXReadout z w 1
  x3 := twoRailZornXReadout z w 2
  y1 := twoRailZornYReadout z w 0
  y2 := twoRailZornYReadout z w 1
  y3 := twoRailZornYReadout z w 2

theorem twoRailZornCell_mul_eq_pauliCorrelationProduct
    (z w : TwoRailCoords ℂ) :
    InfoGeometry.Algebra.Zorn.Concrete.ZornCell.mulZ
        (twoRailZornCell z) (twoRailZornCell w) =
      twoRailPauliCorrelationProduct z w := by
  have hr := twoRailZornCell_mul_r_eq_pauliScalarCorrelation z w
  have hs := twoRailZornCell_mul_s_eq_pauliScalarCorrelation z w
  have hx := twoRailZornCell_mul_x_eq_pauliVectorCorrelation z w
  have hy := twoRailZornCell_mul_y_eq_pauliVectorCorrelation z w
  rcases hx with ⟨hx1, hx2, hx3⟩
  rcases hy with ⟨hy1, hy2, hy3⟩
  apply zornCell_ext
  · simpa [twoRailPauliCorrelationProduct] using hr
  · simpa [twoRailPauliCorrelationProduct] using hs
  · simpa [twoRailPauliCorrelationProduct] using hx1
  · simpa [twoRailPauliCorrelationProduct] using hx2
  · simpa [twoRailPauliCorrelationProduct] using hx3
  · simpa [twoRailPauliCorrelationProduct] using hy1
  · simpa [twoRailPauliCorrelationProduct] using hy2
  · simpa [twoRailPauliCorrelationProduct] using hy3

def nambuSheet (S T : OperatorSheet) : Matrix (Fin 2) (Fin 2) Mat2 :=
  !![0, sheetMatrix S; sheetMatrix T, 0]

theorem nambuSheet_square (S T : OperatorSheet) :
    nambuSheet S T * nambuSheet S T =
      !![crossSheet S T, 0; 0, crossSheet T S] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nambuSheet, crossSheet, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Quantum.CircularPauliCausalCone
