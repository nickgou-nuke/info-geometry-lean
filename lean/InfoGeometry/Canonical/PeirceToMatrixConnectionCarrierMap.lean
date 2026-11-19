/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixConnectionCurvatureTransport
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations
import InfoGeometry.Canonical.ZornMaxwellFormsDegreeBridge
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Peirce expressions under ring homomorphisms

Proves naturality of Peirce corner expressions under ring endomorphisms of the
same matrix ring `Mat`. This file does not construct a map from an arbitrary
Peirce carrier to a matrix carrier. Differential transport belongs to
`MatrixConnectionCurvatureTransport`, where compatibility assumptions are
stated explicitly.
-/

noncomputable section

namespace InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap

open ExteriorAlgebra
open InfoGeometry.Canonical.MatrixConnectionCurvatureTransport
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)

/-- An `R`-linear exterior differential that kills the unit also kills every
coefficient coming from the scalar ring `R`. This is the precise obstruction
to treating the affine coordinate `X` itself as a coefficient when one sets
`R = Polynomial ℝ`: the existing `Module.End R` differential cannot also send
that scalar coefficient to `dX`. A polynomial-valued de Rham carrier must
therefore use a differential that is only linear over the constants (or an
explicit coefficient-extension construction). -/
theorem linear_exterior_differential_kills_base_scalar
    (d : Module.End R (ExteriorAlgebra R V)) (hd : d 1 = 0) (r : R) :
    d (algebraMap R (ExteriorAlgebra R V) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hd, smul_zero]

/-- A chain map from polynomial differentiation into an exterior differential
cannot send the polynomial coordinate to a target scalar. This isolates the
carrier obstruction: a grading-preserving map into the degree-zero part of an
ordinary exterior algebra cannot preserve `dX = 1`. -/
theorem no_scalar_polynomial_coordinate_chain_map
    [Nontrivial R] (φ : Polynomial R →+* ExteriorAlgebra R V)
    (d : Module.End R (ExteriorAlgebra R V)) (hd : d 1 = 0)
    (hchain : ∀ p : Polynomial R, d (φ p) = φ (Polynomial.derivative p))
    (hX : ∃ c : R, φ Polynomial.X = algebraMap R (ExteriorAlgebra R V) c) :
    False := by
  obtain ⟨c, hc⟩ := hX
  have hscalar := linear_exterior_differential_kills_base_scalar d hd c
  rw [← hc] at hscalar
  have hcoord := hchain Polynomial.X
  rw [Polynomial.derivative_X, map_one] at hcoord
  rw [hscalar] at hcoord
  exact zero_ne_one hcoord

/-- `f` intertwines `conePlus`: `f (conePlus P A) = conePlus (f P) (f A)`. -/
theorem intertwines_conePlus (f : Mat →+* Mat) (P A : Mat) :
    f (conePlus P A) = conePlus (f P) (f A) := by
  calc
    f (conePlus P A) = f (P * A * (1 - P)) := rfl
    _ = f P * f A * f (1 - P) := by
      rw [map_mul, map_mul]
    _ = f P * f A * (1 - f P) := by
      have h : f (1 - P) = 1 - f P := by
        calc
          f (1 - P) = f 1 - f P := by rw [map_sub]
          _ = 1 - f P := by rw [map_one]
      rw [h]
    _ = conePlus (f P) (f A) := rfl

/-- `f` intertwines `coneMinus`: `f (coneMinus P C) = coneMinus (f P) (f C)`. -/
theorem intertwines_coneMinus (f : Mat →+* Mat) (P C : Mat) :
    f (coneMinus P C) = coneMinus (f P) (f C) := by
  calc
    f (coneMinus P C) = f ((1 - P) * C * P) := rfl
    _ = f (1 - P) * f C * f P := by
      rw [map_mul, map_mul]
    _ = (1 - f P) * f C * f P := by
      have h : f (1 - P) = 1 - f P := by
        calc
          f (1 - P) = f 1 - f P := by rw [map_sub]
          _ = 1 - f P := by rw [map_one]
      rw [h]
    _ = coneMinus (f P) (f C) := rfl

/-- `f` intertwines `genPhi`: `f (genPhi P A C) = genPhi (f P) (f A) (f C)`. -/
theorem intertwines_genPhi (f : Mat →+* Mat) (P A C : Mat) :
    f (genPhi P A C) = genPhi (f P) (f A) (f C) := by
  calc
    f (genPhi P A C) = f (conePlus P A + coneMinus P C) := rfl
    _ = f (conePlus P A) + f (coneMinus P C) := by rw [map_add]
    _ = conePlus (f P) (f A) + coneMinus (f P) (f C) := by
      rw [intertwines_conePlus f P A, intertwines_coneMinus f P C]
    _ = genPhi (f P) (f A) (f C) := rfl

/-- `f` intertwines `genV`: `f (genV P A C) = genV (f P) (f A) (f C)`. -/
theorem intertwines_genV (f : Mat →+* Mat) (P A C : Mat) :
    f (genV P A C) = genV (f P) (f A) (f C) := by
  calc
    f (genV P A C) = f (anticomm (conePlus P A) (coneMinus P C)) := rfl
    _ = f (conePlus P A * coneMinus P C + coneMinus P C * conePlus P A) := rfl
    _ = f (conePlus P A * coneMinus P C) + f (coneMinus P C * conePlus P A) := by
      rw [map_add]
    _ = f (conePlus P A) * f (coneMinus P C) + f (coneMinus P C) * f (conePlus P A) := by
      rw [map_mul, map_mul]
    _ = conePlus (f P) (f A) * coneMinus (f P) (f C) +
        coneMinus (f P) (f C) * conePlus (f P) (f A) := by
      rw [intertwines_conePlus f P A, intertwines_coneMinus f P C]
    _ = genV (f P) (f A) (f C) := by simp [genV, anticomm]

/-- `f` intertwines `peirceGradingDeriv`: `f (peirceGradingDeriv P X) = peirceGradingDeriv (f P) (f X)`. -/
theorem intertwines_peirceGradingDeriv (f : Mat →+* Mat) (P X : Mat) :
    f (peirceGradingDeriv P X) = peirceGradingDeriv (f P) (f X) := by
  calc
    f (peirceGradingDeriv P X) = f (comm P X) := rfl
    _ = f (P * X - X * P) := rfl
    _ = f P * f X - f X * f P := by
      rw [map_sub, map_mul, map_mul]
    _ = comm (f P) (f X) := rfl
    _ = peirceGradingDeriv (f P) (f X) := rfl

/-- `f` intertwines `peirceCovariantDeriv`:
`f (peirceCovariantDeriv P A C X) = peirceCovariantDeriv (f P) (f A) (f C) (f X)`. -/
theorem intertwines_peirceCovariantDeriv (f : Mat →+* Mat) (P A C X : Mat) :
    f (peirceCovariantDeriv P A C X) = peirceCovariantDeriv (f P) (f A) (f C) (f X) := by
  calc
    f (peirceCovariantDeriv P A C X) = f (peirceGradingDeriv P X + comm (genPhi P A C) X) := rfl
    _ = f (peirceGradingDeriv P X) + f (comm (genPhi P A C) X) := by rw [map_add]
    _ = peirceGradingDeriv (f P) (f X) + f (genPhi P A C * X - X * genPhi P A C) := by
      rw [intertwines_peirceGradingDeriv f P X]
      rfl
    _ = peirceGradingDeriv (f P) (f X) + (f (genPhi P A C) * f X - f X * f (genPhi P A C)) := by
      rw [map_sub, map_mul, map_mul]
    _ = peirceGradingDeriv (f P) (f X) + (genPhi (f P) (f A) (f C) * f X - f X * genPhi (f P) (f A) (f C)) := by
      rw [intertwines_genPhi f P A C]
    _ = peirceGradingDeriv (f P) (f X) + InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi (f P) (f A) (f C)) (f X) := by
      simp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    _ = peirceCovariantDeriv (f P) (f A) (f C) (f X) := rfl

/-- `f` intertwines `peirceMaurerCartanCurvature`:
`f (peirceMaurerCartanCurvature P A C) = peirceMaurerCartanCurvature (f P) (f A) (f C)`. -/
theorem intertwines_peirceMaurerCartanCurvature (f : Mat →+* Mat) (P A C : Mat) :
    f (peirceMaurerCartanCurvature P A C) = peirceMaurerCartanCurvature (f P) (f A) (f C) := by
  calc
    f (peirceMaurerCartanCurvature P A C) =
      f (peirceGradingDeriv P (genPhi P A C) + genPhi P A C * genPhi P A C) := rfl
    _ = f (peirceGradingDeriv P (genPhi P A C)) + f (genPhi P A C * genPhi P A C) := by
      rw [map_add]
    _ = peirceGradingDeriv (f P) (f (genPhi P A C)) + f (genPhi P A C) * f (genPhi P A C) := by
      rw [intertwines_peirceGradingDeriv f P (genPhi P A C)]
      rw [map_mul]
    _ = peirceGradingDeriv (f P) (genPhi (f P) (f A) (f C)) +
        genPhi (f P) (f A) (f C) * genPhi (f P) (f A) (f C) := by
      rw [intertwines_genPhi f P A C]
    _ = peirceMaurerCartanCurvature (f P) (f A) (f C) := rfl

/-- The `2 × 2` upper-left matrix unit used in the obstruction below. -/
def peirceExteriorE00 {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] :
    Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V) :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- The `2 × 2` upper-right matrix unit used in the obstruction below. -/
def peirceExteriorE01 {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] :
    Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V) :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- A universal equality between componentwise exterior differentiation and the Peirce
commutator is impossible, even in the smallest noncommutative matrix carrier.  The
matrix unit `E₀₁` is killed entrywise by any linear map with `d 1 = 0`, while its
commutator with `E₀₀` has `(0,1)` entry `1`.  Thus the compatibility required by a
Peirce-to-exterior substitution theorem must be supplied for selected data; it cannot
be inferred from the carrier types or from a generic exterior derivative. -/
theorem no_universal_peirceExteriorDerivative_compatibility
    {R V : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup V] [Module R V]
    (d : Module.End R (ExteriorAlgebra R V)) (hd : d 1 = 0) :
    ¬ (∀ M : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V),
      matrixExteriorDerivative d M = peirceGradingDeriv (peirceExteriorE00 (R := R) (V := V)) M) := by
  intro h
  have hDM := h (peirceExteriorE01 (R := R) (V := V))
  have hentry := congrFun (congrFun hDM (0 : Fin 2)) (1 : Fin 2)
  have hOne : (0 : ExteriorAlgebra R V) = 1 := by
    simpa [matrixExteriorDerivative, peirceExteriorE01, peirceExteriorE00,
      Matrix.mul_apply,
      Fin.sum_univ_two, hd, peirceGradingDeriv,
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using hentry
  exact one_ne_zero hOne.symm

/-- For the canonical inclusion of the `2 × 2` matrix/exterior carrier, even
the correctly typed degree-zero-to-degree-one compatibility fails on the
Peirce cut itself unless the connection generator vanishes.  The exterior
differential is entrywise and kills the constant cut `E₀₀`; the Peirce
superderivation sends that cut to the difference of the two off-diagonal
connection corners.  Those corners have disjoint matrix support, so their
vanishing forces `genPhi = 0`.

This is a no-go theorem for the identity representation, not for a different
representation or a total differential that mixes the two gradings. -/
theorem identity_representation_cut_compatibility_forces_genPhi_zero
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (d : Module.End R (ExteriorAlgebra R V)) (hd : d 1 = 0)
    (A C : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V))
    (hcompat : matrixExteriorDerivative d
        (peirceExteriorE00 (R := R) (V := V)) =
      superDerivPhi (peirceExteriorE00 (R := R) (V := V)) A C
        (peirceExteriorE00 (R := R) (V := V))) :
    genPhi (peirceExteriorE00 (R := R) (V := V)) A C = 0 := by
  have h_ext_cut : matrixExteriorDerivative d
      (peirceExteriorE00 (R := R) (V := V)) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixExteriorDerivative, peirceExteriorE00, hd]
  rw [h_ext_cut] at hcompat
  have h_phi : superDerivPhi (peirceExteriorE00 (R := R) (V := V)) A C
      (peirceExteriorE00 (R := R) (V := V)) = 0 := hcompat.symm
  have h01 := congrFun (congrFun h_phi (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun h_phi (1 : Fin 2)) (0 : Fin 2)
  simp [superDerivPhi, superDerivPlus, superDerivMinus, parityConj,
    invS, conePlus, coneMinus, peirceExteriorE00,
    Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [genPhi, conePlus, coneMinus, peirceExteriorE00,
      Matrix.mul_apply, Fin.sum_univ_two, h01, h10]

/-! ### A moving two-sheet representation over the affine line

The constant-cut obstruction above is specific to the canonical inclusion.
The following model changes both the cut and the coefficient carrier: the
two-sheet algebra is represented in matrices over `ℝ[X]`, and its ordinary
polynomial derivative is compared with a connection commutator. -/

section MovingTwoSheetRepresentation

abbrev MovingSheetMat := Matrix (Fin 2) (Fin 2) (Polynomial ℝ)

/-- The unipotent conjugate of the diagonal two-sheet algebra. -/
def movingSheetRep (a b : ℝ) : MovingSheetMat :=
  ![![Polynomial.C a, (Polynomial.C b - Polynomial.C a) * Polynomial.X],
    ![0, Polynomial.C b]]

/-- The connection form `U' U⁻¹` for `U = [[1,X],[0,1]]`. -/
def movingSheetConnection : MovingSheetMat := ![![0, 1], ![0, 0]]

/-- Entrywise formal differentiation in the affine coordinate `X`. -/
def movingSheetDerivative (M : MovingSheetMat) : MovingSheetMat :=
  fun i j => Polynomial.derivative (M i j)

lemma movingSheet_ext {M N : MovingSheetMat}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  funext i
  fin_cases i
  · funext j
    fin_cases j
    · exact h00
    · exact h01
  · funext j
    fin_cases j
    · exact h10
    · exact h11

lemma movingSheet_mul00 (M N : MovingSheetMat) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

lemma movingSheet_mul01 (M N : MovingSheetMat) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

lemma movingSheet_mul10 (M N : MovingSheetMat) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

lemma movingSheet_mul11 (M N : MovingSheetMat) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

private lemma poly_deriv_sum2 (u₁ v₁ u₂ v₂ : Polynomial ℝ) :
    (Polynomial.derivative u₁ * v₁ + u₁ * Polynomial.derivative v₁) +
      (Polynomial.derivative u₂ * v₂ + u₂ * Polynomial.derivative v₂) =
    (Polynomial.derivative u₁ * v₁ + Polynomial.derivative u₂ * v₂) +
      (u₁ * Polynomial.derivative v₁ + u₂ * Polynomial.derivative v₂) := by
  ring

private lemma movingSheetRep_offdiag_add (a₁ b₁ a₂ b₂ : ℝ) :
    (Polynomial.C b₁ - Polynomial.C a₁) * Polynomial.X +
      (Polynomial.C b₂ - Polynomial.C a₂) * Polynomial.X =
    (Polynomial.C (b₁ + b₂) - Polynomial.C (a₁ + a₂)) * Polynomial.X := by
  simp only [Polynomial.C_add]
  ring

/-- Entrywise polynomial differentiation is a derivation of the matrix
coefficient algebra. -/
theorem movingSheetDerivative_mul (M N : MovingSheetMat) :
    movingSheetDerivative (M * N) =
      movingSheetDerivative M * N + M * movingSheetDerivative N := by
  apply movingSheet_ext
  · change Polynomial.derivative ((M * N) 0 0) = _
    rw [movingSheet_mul00, Matrix.add_apply, movingSheet_mul00, movingSheet_mul00]
    simp only [movingSheetDerivative, Polynomial.derivative_add,
      Polynomial.derivative_mul]
    exact poly_deriv_sum2 _ _ _ _
  · change Polynomial.derivative ((M * N) 0 1) = _
    rw [movingSheet_mul01, Matrix.add_apply, movingSheet_mul01, movingSheet_mul01]
    simp only [movingSheetDerivative, Polynomial.derivative_add,
      Polynomial.derivative_mul]
    exact poly_deriv_sum2 _ _ _ _
  · change Polynomial.derivative ((M * N) 1 0) = _
    rw [movingSheet_mul10, Matrix.add_apply, movingSheet_mul10, movingSheet_mul10]
    simp only [movingSheetDerivative, Polynomial.derivative_add,
      Polynomial.derivative_mul]
    exact poly_deriv_sum2 _ _ _ _
  · change Polynomial.derivative ((M * N) 1 1) = _
    rw [movingSheet_mul11, Matrix.add_apply, movingSheet_mul11, movingSheet_mul11]
    simp only [movingSheetDerivative, Polynomial.derivative_add,
      Polynomial.derivative_mul]
    exact poly_deriv_sum2 _ _ _ _

theorem movingSheetRep_mul (a b c d : ℝ) :
    movingSheetRep a b * movingSheetRep c d = movingSheetRep (a * c) (b * d) := by
  apply movingSheet_ext
  · rw [movingSheet_mul00]; simp [movingSheetRep]
  · rw [movingSheet_mul01]; simp [movingSheetRep]; ring
  · rw [movingSheet_mul10]; simp [movingSheetRep]
  · rw [movingSheet_mul11]; simp [movingSheetRep]

/-- A genuine unital ring representation of the two-sheet algebra in the
polynomial matrix carrier. -/
def movingSheetRepHom : (ℝ × ℝ) →+* MovingSheetMat where
  toFun p := movingSheetRep p.1 p.2
  map_one' := by
    apply movingSheet_ext <;> simp [movingSheetRep]
  map_mul' p q := (movingSheetRep_mul p.1 p.2 q.1 q.2).symm
  map_zero' := by
    apply movingSheet_ext <;> simp [movingSheetRep]
  map_add' p q := by
    apply movingSheet_ext
    · rw [Matrix.add_apply]; simp [movingSheetRep]
    · rw [Matrix.add_apply]
      simp [movingSheetRep]
      <;> simp [movingSheetRep]
    · rw [Matrix.add_apply]; simp [movingSheetRep]
    · rw [Matrix.add_apply]; simp [movingSheetRep]

/-- The cut is the image of the first primitive idempotent of the two-sheet
algebra. -/
theorem movingSheetRep_first_idempotent :
    movingSheetRep 1 0 * movingSheetRep 1 0 = movingSheetRep 1 0 := by
  rw [movingSheetRep_mul]
  simp

/-- The represented cut is genuinely moving: its off-diagonal coefficient
has nonzero formal derivative. -/
theorem movingSheetRep_first_idempotent_moves :
    movingSheetDerivative (movingSheetRep 1 0) ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [movingSheetDerivative, movingSheetRep, Polynomial.derivative_C,
    Polynomial.derivative_mul, Polynomial.derivative_X] at h01

/-- On the represented two-sheet subalgebra, the affine derivative is exactly
the inner derivation implemented by the connection matrix. -/
theorem movingSheetRep_derivative_eq_connection_commutator (a b : ℝ) :
    movingSheetDerivative (movingSheetRep a b) =
      movingSheetConnection * movingSheetRep a b -
        movingSheetRep a b * movingSheetConnection := by
  apply movingSheet_ext
  · rw [Matrix.sub_apply, movingSheet_mul00, movingSheet_mul00]
    simp [movingSheetDerivative, movingSheetRep, movingSheetConnection,
      Polynomial.derivative_C]
  · rw [Matrix.sub_apply, movingSheet_mul01, movingSheet_mul01]
    simp [movingSheetDerivative, movingSheetRep, movingSheetConnection,
      Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_X]
  · rw [Matrix.sub_apply, movingSheet_mul10, movingSheet_mul10]
    simp [movingSheetDerivative, movingSheetRep, movingSheetConnection]
  · rw [Matrix.sub_apply, movingSheet_mul11, movingSheet_mul11]
    simp [movingSheetDerivative, movingSheetRep, movingSheetConnection,
      Polynomial.derivative_C]

/-- The connection commutator on the represented algebra is exactly the
repository's Peirce superderivation for the moving idempotent cut. -/
theorem movingSheetRep_derivative_eq_peirce_superderivation (a b : ℝ) :
    movingSheetDerivative (movingSheetRep a b) =
      superDerivPhi (movingSheetRep 1 0) movingSheetConnection 0
        (movingSheetRep a b) := by
  let P : MovingSheetMat := movingSheetRep 1 0
  let A : MovingSheetMat := movingSheetConnection
  let X : MovingSheetMat := movingSheetRep a b
  have hP : P * P = P := by dsimp [P]; exact movingSheetRep_first_idempotent
  have hPA : P * A = A := by
    dsimp [P, A]
    apply movingSheet_ext
    · rw [movingSheet_mul00]; simp [movingSheetRep, movingSheetConnection]
    · rw [movingSheet_mul01]; simp [movingSheetRep, movingSheetConnection]
    · rw [movingSheet_mul10]; simp [movingSheetRep, movingSheetConnection]
    · rw [movingSheet_mul11]; simp [movingSheetRep, movingSheetConnection]
  have hAP : A * P = 0 := by
    dsimp [P, A]
    apply movingSheet_ext
    · rw [movingSheet_mul00]; simp [movingSheetRep, movingSheetConnection]
    · rw [movingSheet_mul01]; simp [movingSheetRep, movingSheetConnection]
    · rw [movingSheet_mul10]; simp [movingSheetRep, movingSheetConnection]
    · rw [movingSheet_mul11]; simp [movingSheetRep, movingSheetConnection]
  have hPX : P * X = X * P := by
    dsimp [P, X]
    apply movingSheet_ext
    · rw [movingSheet_mul00, movingSheet_mul00]; simp [movingSheetRep]
    · rw [movingSheet_mul01, movingSheet_mul01]; simp [movingSheetRep]; ring
    · rw [movingSheet_mul10, movingSheet_mul10]; simp [movingSheetRep]
    · rw [movingSheet_mul11, movingSheet_mul11]; simp [movingSheetRep]
  have hParity : parityConj P X = X := by
    apply (parityConj_fixed_iff_commutes_with_grading hP X).2
    dsimp [invS]
    noncomm_ring [hPX]
  have hCorner : conePlus P A = A := by
    dsimp [conePlus]
    rw [hPA]
    calc A * (1 - P) = A - A * P := by noncomm_ring
      _ = A := by rw [hAP, sub_zero]
  rw [movingSheetRep_derivative_eq_connection_commutator]
  change A * X - X * A = superDerivPhi P A 0 X
  rw [superDerivPhi, superDerivPlus, superDerivMinus, hCorner, hParity]
  simp [coneMinus]

/-- The 0- and 1-form coefficient pair on the affine line. The first
component is the coefficient of `1`, and the second the coefficient of `dX`;
products of two `dX` terms vanish in dimension one. -/
structure AffineLineMatrixForm where
  degreeZero : MovingSheetMat
  degreeOne : MovingSheetMat

@[ext] theorem affineLineMatrixForm_ext (u v : AffineLineMatrixForm)
    (h0 : u.degreeZero = v.degreeZero) (h1 : u.degreeOne = v.degreeOne) : u = v := by
  cases u
  cases v
  cases h0
  cases h1
  rfl

/-- Embed a matrix coefficient as a 0-form. -/
def affineZeroForm (M : MovingSheetMat) : AffineLineMatrixForm :=
  ⟨M, 0⟩

/-- Embed a matrix coefficient as the coefficient of `dX`. -/
def affineOneForm (M : MovingSheetMat) : AffineLineMatrixForm :=
  ⟨0, M⟩

/-- Wedge product in the truncated affine-line form carrier. -/
def affineLineFormMul (u v : AffineLineMatrixForm) : AffineLineMatrixForm :=
  ⟨u.degreeZero * v.degreeZero,
    u.degreeZero * v.degreeOne + u.degreeOne * v.degreeZero⟩

/-- Componentwise addition of affine-line forms. -/
def affineLineFormAdd (u v : AffineLineMatrixForm) : AffineLineMatrixForm :=
  ⟨u.degreeZero + v.degreeZero, u.degreeOne + v.degreeOne⟩

def affineLineFormNeg (u : AffineLineMatrixForm) : AffineLineMatrixForm :=
  ⟨-u.degreeZero, -u.degreeOne⟩

/-- Unit in the truncated affine-line matrix-form algebra. -/
def affineLineFormOne : AffineLineMatrixForm := ⟨1, 0⟩

/-- Zero in the truncated affine-line matrix-form algebra. -/
def affineLineFormZero : AffineLineMatrixForm := ⟨0, 0⟩

theorem affineLineFormMul_assoc (u v w : AffineLineMatrixForm) :
    affineLineFormMul (affineLineFormMul u v) w =
      affineLineFormMul u (affineLineFormMul v w) := by
  cases u with
  | mk u0 u1 =>
    cases v with
    | mk v0 v1 =>
      cases w with
      | mk w0 w1 =>
        apply affineLineMatrixForm_ext
        · simp [affineLineFormMul, mul_assoc]
        · simp only [affineLineFormMul]
          noncomm_ring

theorem affineLineFormMul_one (u : AffineLineMatrixForm) :
    affineLineFormMul u affineLineFormOne = u ∧
      affineLineFormMul affineLineFormOne u = u := by
  cases u with
  | mk u0 u1 =>
    constructor <;> apply affineLineMatrixForm_ext <;>
      simp [affineLineFormMul, affineLineFormOne]

theorem affineLineFormMul_add_left (u v w : AffineLineMatrixForm) :
    affineLineFormMul (affineLineFormAdd u v) w =
      affineLineFormAdd (affineLineFormMul u w) (affineLineFormMul v w) := by
  cases u with
  | mk u0 u1 => cases v with
    | mk v0 v1 => cases w with
      | mk w0 w1 =>
        apply affineLineMatrixForm_ext <;>
          simp [affineLineFormMul, affineLineFormAdd, Matrix.add_mul,
            add_mul, mul_add] <;> abel

theorem affineLineFormMul_add_right (u v w : AffineLineMatrixForm) :
    affineLineFormMul u (affineLineFormAdd v w) =
      affineLineFormAdd (affineLineFormMul u v) (affineLineFormMul u w) := by
  cases u with
  | mk u0 u1 => cases v with
    | mk v0 v1 => cases w with
      | mk w0 w1 =>
        apply affineLineMatrixForm_ext <;>
          simp [affineLineFormMul, affineLineFormAdd, Matrix.mul_add,
            add_mul, mul_add] <;> abel

theorem affineLineFormAdd_assoc (u v w : AffineLineMatrixForm) :
    affineLineFormAdd (affineLineFormAdd u v) w =
      affineLineFormAdd u (affineLineFormAdd v w) := by
  cases u with
  | mk u0 u1 => cases v with
    | mk v0 v1 => cases w with
      | mk w0 w1 =>
        apply affineLineMatrixForm_ext <;>
          simp [affineLineFormAdd, add_assoc]

theorem affineLineFormAdd_comm (u v : AffineLineMatrixForm) :
    affineLineFormAdd u v = affineLineFormAdd v u := by
  cases u with
  | mk u0 u1 => cases v with
    | mk v0 v1 =>
      apply affineLineMatrixForm_ext <;> simp [affineLineFormAdd, add_comm]

theorem affineLineFormAdd_zero (u : AffineLineMatrixForm) :
    affineLineFormAdd u affineLineFormZero = u ∧
      affineLineFormAdd affineLineFormZero u = u := by
  cases u with
  | mk u0 u1 =>
    constructor <;> apply affineLineMatrixForm_ext <;>
      simp [affineLineFormAdd, affineLineFormZero]

theorem affineLineFormAdd_neg (u : AffineLineMatrixForm) :
    affineLineFormAdd u (affineLineFormNeg u) = affineLineFormZero := by
  cases u with
  | mk u0 u1 =>
    apply affineLineMatrixForm_ext <;> simp [affineLineFormAdd, affineLineFormNeg,
      affineLineFormZero]

/-- De Rham differential on the affine-line form pair. -/
def affineLineFormD (u : AffineLineMatrixForm) : AffineLineMatrixForm :=
  affineOneForm (movingSheetDerivative u.degreeZero)

/-- The grading involution is positive on 0-forms and negative on 1-forms. -/
def affineLineFormParity (u : AffineLineMatrixForm) : AffineLineMatrixForm :=
  ⟨u.degreeZero, -u.degreeOne⟩

theorem affineLineFormD_sq_zero (u : AffineLineMatrixForm) :
    (affineLineFormD (affineLineFormD u)).degreeZero = 0 ∧
      (affineLineFormD (affineLineFormD u)).degreeOne = 0 := by
  exact ⟨rfl, rfl⟩

/-- The truncated affine-line carrier satisfies the graded Leibniz rule for
its matrix-coefficient product and grading involution. -/
theorem affineLineFormD_graded_leibniz (u v : AffineLineMatrixForm) :
    affineLineFormD (affineLineFormMul u v) =
      affineLineFormAdd (affineLineFormMul (affineLineFormD u) v)
        (affineLineFormMul (affineLineFormParity u) (affineLineFormD v)) := by
  cases u with
  | mk u0 u1 =>
    cases v with
    | mk v0 v1 =>
      apply affineLineMatrixForm_ext
      · simp only [affineLineFormD, affineLineFormMul, affineLineFormParity,
          affineLineFormAdd, affineOneForm]
        simp
      · simp only [affineLineFormD, affineLineFormMul, affineLineFormParity,
          affineLineFormAdd, affineOneForm, zero_mul, mul_zero, add_zero,
          zero_add]
        exact movingSheetDerivative_mul u0 v0

/-- The represented two-sheet algebra multiplies in degree zero. -/
theorem affineZeroForm_movingSheetRep_mul (a b c d : ℝ) :
    affineLineFormMul (affineZeroForm (movingSheetRep a b))
        (affineZeroForm (movingSheetRep c d)) =
      affineZeroForm (movingSheetRep (a * c) (b * d)) := by
  simp only [affineLineFormMul, affineZeroForm, zero_mul, mul_zero, add_zero]
  rw [movingSheetRep_mul]

/-- The Peirce differential is a degree-zero-to-degree-one soldering map on
the represented algebra. -/
theorem affineLineFormD_movingSheetRep (a b : ℝ) :
    affineLineFormD (affineZeroForm (movingSheetRep a b)) =
      affineOneForm
        (superDerivPhi (movingSheetRep 1 0) movingSheetConnection 0
          (movingSheetRep a b)) := by
  change affineOneForm (movingSheetDerivative (movingSheetRep a b)) = _
  exact congrArg affineOneForm
    (movingSheetRep_derivative_eq_peirce_superderivation a b)

/-- Left and right multiplication by represented 0-forms give the expected
bimodule actions on affine-line 1-form coefficients. -/
theorem affineLineForm_zero_one_actions (a b : ℝ) (M : MovingSheetMat) :
    affineLineFormMul (affineZeroForm (movingSheetRep a b)) (affineOneForm M) =
        affineOneForm (movingSheetRep a b * M) ∧
      affineLineFormMul (affineOneForm M) (affineZeroForm (movingSheetRep a b)) =
        affineOneForm (M * movingSheetRep a b) := by
  constructor <;> simp [affineLineFormMul, affineZeroForm, affineOneForm]

/-- On the represented algebra, the soldered differential satisfies the
ordinary Leibniz rule with the induced left and right 0-form actions. -/
theorem affineLineFormD_movingSheetRep_leibniz (a b c d : ℝ) :
    affineLineFormD
        (affineLineFormMul (affineZeroForm (movingSheetRep a b))
          (affineZeroForm (movingSheetRep c d))) =
      affineOneForm
        (movingSheetDerivative (movingSheetRep a b) * movingSheetRep c d +
          movingSheetRep a b * movingSheetDerivative (movingSheetRep c d)) := by
  simp only [affineLineFormD, affineLineFormMul, affineZeroForm, affineOneForm,
    zero_mul, mul_zero, add_zero]
  rw [movingSheetRep_mul a b c d]
  change affineOneForm (movingSheetDerivative (movingSheetRep (a * c) (b * d))) = _
  apply congrArg affineOneForm
  rw [movingSheetRep_derivative_eq_connection_commutator (a * c) (b * d),
    movingSheetRep_derivative_eq_connection_commutator a b,
    movingSheetRep_derivative_eq_connection_commutator c d,
    ← movingSheetRep_mul a b c d]
  noncomm_ring

end MovingTwoSheetRepresentation

/-- The componentwise lift of an exterior-algebra endomorphism to matrices,
viewed as an additive map so that the square-zero Leibniz obstruction applies. -/
def matrixExteriorDerivativeHom
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (d : Module.End R (ExteriorAlgebra R V)) :
    Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) →+
      Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) where
  toFun := matrixExteriorDerivative d
  map_zero' := by
    ext i j
    simp [matrixExteriorDerivative]
  map_add' M N := by
    ext i j
    simp [matrixExteriorDerivative]

/-- Homogeneous exterior components of distinct degrees intersect trivially.
This follows from the direct-sum grading of the exterior algebra, not from a
dimension or finite-basis argument. -/
theorem eq_zero_of_homogeneous_exterior_degrees_ne
    {k l : ℕ} {x : ExteriorAlgebra R V} (hkl : k ≠ l)
    (hk : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.IsHomogeneousExteriorDegree k x)
    (hl : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.IsHomogeneousExteriorDegree l x) :
    x = 0 := by
  have hrange (m : ℕ) :
      Set.range (fun v : Fin m → V => (List.ofFn fun i => ι R (v i)).prod) =
        Set.range (ExteriorAlgebra.ιMulti R m) := by
    ext y
    simp only [Set.mem_range]
    constructor <;> rintro ⟨v, rfl⟩ <;> exact ⟨v, (ExteriorAlgebra.ιMulti_apply v).symm⟩
  have hk' : x ∈ ⋀[R]^k V := by
    have hspan : Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R k)) = ⋀[R]^k V :=
      ExteriorAlgebra.ιMulti_span_fixedDegree R k
    rw [← hspan]
    change x ∈ Submodule.span R
      (Set.range (fun v : Fin k → V => (List.ofFn fun i => ι R (v i)).prod))
    rw [hrange k]
    exact hk
  have hl' : x ∈ ⋀[R]^l V := by
    have hspan : Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R l)) = ⋀[R]^l V :=
      ExteriorAlgebra.ιMulti_span_fixedDegree R l
    rw [← hspan]
    change x ∈ Submodule.span R
      (Set.range (fun v : Fin l → V => (List.ofFn fun i => ι R (v i)).prod))
    rw [hrange l]
    exact hl
  by_contra hx
  have hdeg := DirectSum.degree_eq_of_mem_mem
    (fun i : ℕ => ⋀[R]^i V) hk' hl' hx
  exact hkl hdeg

/-- Identify the repository's homogeneous-span predicate with the native
fixed-degree exterior submodule, without requiring a field of coefficients. -/
theorem homogeneous_iff_fixedDegree (k : ℕ) (x : ExteriorAlgebra R V) :
    InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.IsHomogeneousExteriorDegree k x ↔
      x ∈ ⋀[R]^k V := by
  unfold InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.IsHomogeneousExteriorDegree
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
  have hfun : (fun v : Fin k → V => (List.ofFn fun i => ι R (v i)).prod) =
      (ExteriorAlgebra.ιMulti R k : (Fin k → V) → ExteriorAlgebra R V) := by
    funext v
    exact (ExteriorAlgebra.ιMulti_apply v).symm
  rw [hfun]

/-- An element that is Peirce-odd on both sides and commutes with its
idempotent cut must vanish. -/
theorem peirce_odd_eq_zero_of_commutator_eq_zero
    {P X : Mat} (hP : P * P = P)
    (h11 : P * X * P = 0) (h00 : (1 - P) * X * (1 - P) = 0)
    (hcomm : P * X - X * P = 0) : X = 0 := by
  have h_expand : X - P * X - X * P + P * X * P = 0 := by
    calc
      X - P * X - X * P + P * X * P = (1 - P) * X * (1 - P) := by noncomm_ring
      _ = 0 := h00
  rw [h11] at h_expand
  have h_linear : X - P * X - X * P = 0 := by simpa using h_expand
  have h_decomp : X = P * X + X * P := by
    calc X = (X - P * X - X * P) + P * X + X * P := by abel
      _ = P * X + X * P := by rw [h_linear]; abel
  have hpx : P * X = 0 := by
    calc P * X = (P * P) * X := by rw [hP]
      _ = P * (P * X) := by rw [mul_assoc]
      _ = P * (X * P) := by rw [sub_eq_zero.mp hcomm]
      _ = P * X * P := by noncomm_ring
      _ = 0 := h11
  have hxp : X * P = 0 := by
    calc X * P = P * X := sub_eq_zero.mp hcomm |>.symm
      _ = 0 := hpx
  rw [hpx, hxp] at h_decomp
  simpa using h_decomp

/-- The corner terms defining `genPhi` have zero diagonal Peirce corners for
an idempotent cut. -/
theorem genPhi_has_zero_diagonal_corners
    {P A C : Mat} (hP : P * P = P) :
    P * genPhi P A C * P = 0 ∧
      (1 - P) * genPhi P A C * (1 - P) = 0 := by
  have hpq : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hqp : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hqq : (1 - P) * (1 - P) = 1 - P := by
    calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  constructor
  · dsimp [genPhi, conePlus, coneMinus]
    rw [mul_add, add_mul]
    have h₁ : P * (P * A * (1 - P)) * P = 0 := by
      calc P * (P * A * (1 - P)) * P = P * P * A * (1 - P) * P := by noncomm_ring
        _ = 0 := by rw [hP]; rw [mul_assoc, hqp, mul_zero]
    have h₂ : P * ((1 - P) * C * P) * P = 0 := by
      calc P * ((1 - P) * C * P) * P = P * (1 - P) * C * P * P := by noncomm_ring
        _ = 0 := by rw [hpq]; noncomm_ring
    rw [h₁, h₂, add_zero]
  · dsimp [genPhi, conePlus, coneMinus]
    rw [mul_add, add_mul]
    have h₁ : (1 - P) * (P * A * (1 - P)) * (1 - P) = 0 := by
      calc (1 - P) * (P * A * (1 - P)) * (1 - P) = (1 - P) * P * A * (1 - P) * (1 - P) := by noncomm_ring
        _ = 0 := by rw [hqp]; noncomm_ring
    have h₂ : (1 - P) * ((1 - P) * C * P) * (1 - P) = 0 := by
      calc (1 - P) * ((1 - P) * C * P) * (1 - P) = (1 - P) * (1 - P) * C * P * (1 - P) := by noncomm_ring
        _ = 0 := by rw [hqq]; rw [mul_assoc, hpq, mul_zero]
    rw [h₁, h₂, add_zero]

/-- A degree-two exterior derivative cannot equal a degree-one Peirce
commutator unless both vanish.  The hypotheses state the two actual graded
carrier memberships; `ExteriorDifferentialData` alone does not include the
degree-raising law needed to discharge `hDdeg`. -/
theorem degree_shift_peirce_compatibility_forces_both_sides_zero
    {P A C : Mat}
    (D : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.ExteriorDifferentialData R V)
    (hDdeg : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 2
      (matrixExteriorDerivative D.d (genPhi P A C)))
    (hPeirceDeg : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1
      (peirceGradingDeriv P (genPhi P A C)))
    (hcompat : matrixExteriorDerivative D.d (genPhi P A C) =
      peirceGradingDeriv P (genPhi P A C)) :
    matrixExteriorDerivative D.d (genPhi P A C) = 0 ∧
      peirceGradingDeriv P (genPhi P A C) = 0 := by
  have hzero : matrixExteriorDerivative D.d (genPhi P A C) = 0 := by
    ext i j
    apply eq_zero_of_homogeneous_exterior_degrees_ne (k := 2) (l := 1) (by decide)
      (hDdeg i j) (by rw [hcompat]; exact hPeirceDeg i j)
  exact ⟨hzero, by rw [← hcompat, hzero]⟩

/-- A selected typed Maxwell operator discharges both degree-membership
premises in the preceding obstruction: its `d₁` type raises one-forms to
two-forms, while multiplication by a degree-zero cut preserves the degree of
the one-form in the Peirce commutator. Thus this is an unconditional
nonexistence result for nonzero compatibility on that typed carrier, even if
the cut is not closed. -/
theorem typed_maxwell_peirce_compatibility_is_zero
    (D₀ : InfoGeometry.Canonical.ZornDifferentialFormsLaplacianBridge.FormDifferentialLaplacianData
      (R := R) (V := V))
    (O : InfoGeometry.Canonical.ZornMaxwellFormsDegreeBridge.TypedMaxwellOperators D₀)
    {P A C : Mat}
    (hP : P * P = P)
    (hPdeg : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 0 P)
    (hXdeg : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1
      (genPhi P A C))
    (hcompat : matrixExteriorDerivative D₀.differential (genPhi P A C) =
      peirceGradingDeriv P (genPhi P A C)) :
    genPhi P A C = 0 := by
  have hDdeg : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 2
      (matrixExteriorDerivative D₀.differential (genPhi P A C)) := by
    intro i j
    change InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.IsHomogeneousExteriorDegree
      2 (D₀.differential ((genPhi P A C) i j))
    exact InfoGeometry.Canonical.ZornMaxwellFormsDegreeBridge.typed_differential_raises_degree_one
      D₀ O (hXdeg i j)
  have hmul {k l : ℕ} {x y : ExteriorAlgebra R V}
      (hx : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.IsHomogeneousExteriorDegree k x)
      (hy : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.IsHomogeneousExteriorDegree l y) :
      InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.IsHomogeneousExteriorDegree (k + l) (x * y) := by
    have hx' : x ∈ ⋀[R]^k V := by
      exact (homogeneous_iff_fixedDegree k x).mp hx
    have hy' : y ∈ ⋀[R]^l V := by
      exact (homogeneous_iff_fixedDegree l y).mp hy
    exact (homogeneous_iff_fixedDegree (k + l) (x * y)).mpr
      (SetLike.GradedMonoid.toGradedMul.mul_mem hx' hy')
  have hmulMat {k l : ℕ} {M N : Mat}
      (hM : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous k M)
      (hN : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous l N) :
      InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous (k + l) (M * N) := by
    intro i j
    apply (homogeneous_iff_fixedDegree (k + l) _).mpr
    rw [Matrix.mul_apply]
    apply Submodule.sum_mem
    intro q hq
    exact (homogeneous_iff_fixedDegree (k + l) _).mp
      (hmul (hM i q) (hN q j))
  have hPX : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1
      (P * genPhi P A C) := by
    have h := hmulMat hPdeg hXdeg
    simpa using h
  have hXP : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1
      (genPhi P A C * P) := by
    have h := hmulMat hXdeg hPdeg
    simpa [Nat.add_comm] using h
  have hPcomm : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1
      (peirceGradingDeriv P (genPhi P A C)) := by
    intro i j
    change InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.IsHomogeneousExteriorDegree 1
      ((P * genPhi P A C - genPhi P A C * P) i j)
    rw [Matrix.sub_apply]
    apply Submodule.sub_mem
    · exact hPX i j
    · exact hXP i j
  have hzero := degree_shift_peirce_compatibility_forces_both_sides_zero
    (InfoGeometry.Canonical.ZornMaxwellFormsDegreeBridge.typedMaxwellExteriorDifferentialData D₀ O)
    hDdeg hPcomm hcompat
  rcases genPhi_has_zero_diagonal_corners hP with ⟨h11, h00⟩
  apply peirce_odd_eq_zero_of_commutator_eq_zero hP h11 h00
  simpa [peirceGradingDeriv, InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using hzero.2

/-- The componentwise lift of a graded exterior differential obeys the ordinary
left product rule when the left matrix is homogeneous of degree zero. -/
theorem matrixExteriorDerivative_mul_zero_form_left
    (D : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.ExteriorDifferentialData R V)
    (P X : Mat)
    (hP : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 0 P) :
    matrixExteriorDerivative D.d (P * X) =
      matrixExteriorDerivative D.d P * X + P * matrixExteriorDerivative D.d X := by
  ext i j
  change D.d (∑ k : Fin n, P i k * X k j) =
    (∑ k : Fin n, D.d (P i k) * X k j) +
      ∑ k : Fin n, P i k * D.d (X k j)
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have h := D.gradedLeibniz 0 (P i k) (X k j) (hP i k)
  simpa using h

/-- The componentwise lift of a graded exterior differential obeys the odd
right product rule on a one-form matrix. -/
theorem matrixExteriorDerivative_mul_one_form_right
    (D : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.ExteriorDifferentialData R V)
    (X P : Mat)
    (hX : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 X) :
    matrixExteriorDerivative D.d (X * P) =
      matrixExteriorDerivative D.d X * P - X * matrixExteriorDerivative D.d P := by
  ext i j
  change D.d (∑ k : Fin n, X i k * P k j) =
    (∑ k : Fin n, D.d (X i k) * P k j) -
      ∑ k : Fin n, X i k * D.d (P k j)
  rw [map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have h := D.gradedLeibniz 1 (X i k) (P k j) (hX i k)
  simpa only [pow_one, neg_one_smul, sub_eq_add_neg] using h

/-- A closed idempotent cut cannot support a nonzero Peirce-odd connection
whose componentwise matrix differential equals the Peirce commutator.  This
specializes the square-zero obstruction to the actual matrix/exterior carrier:
if the lifted differential is a square-zero Leibniz differential and it kills
`P`, compatibility on `genPhi P A C` forces that connection generator to vanish.
Thus a nontrivial soldering on this carrier must transport a non-closed cut or
change the differential structure. -/
theorem closed_cut_compatibility_forces_genPhi_zero
    {P A C : Mat}
    (d : Module.End R (ExteriorAlgebra R V))
    (hP : P * P = P)
    (hd : InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.IsSquareZeroRingDifferential
      (matrixExteriorDerivativeHom (n := n) d))
    (hdP : matrixExteriorDerivative d P = 0)
    (hcompat : matrixExteriorDerivative d (genPhi P A C) =
      peirceGradingDeriv P (genPhi P A C)) :
    genPhi P A C = 0 := by
  have hcorner₁₁ : P * genPhi P A C * P = 0 := by
    have hpq : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
    have hqp : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
    dsimp [genPhi, conePlus, coneMinus]
    rw [mul_add, add_mul]
    have h₁ : P * (P * A * (1 - P)) * P = 0 := by
      calc P * (P * A * (1 - P)) * P = P * P * A * (1 - P) * P := by noncomm_ring
      _ = 0 := by
        rw [hP]
        calc P * A * (1 - P) * P = P * A * ((1 - P) * P) := by noncomm_ring
          _ = 0 := by rw [hqp, mul_zero]
    have h₂ : P * ((1 - P) * C * P) * P = 0 := by
      calc P * ((1 - P) * C * P) * P = P * (1 - P) * C * P * P := by noncomm_ring
        _ = 0 := by rw [hpq]; noncomm_ring
    rw [h₁, h₂, add_zero]
  have hcorner₀₀ : (1 - P) * genPhi P A C * (1 - P) = 0 := by
    dsimp [genPhi, conePlus, coneMinus]
    have hpq : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
    have hqp : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
    have hqq : (1 - P) * (1 - P) = 1 - P := by
      calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
    rw [mul_add, add_mul]
    have h₁ : (1 - P) * (P * A * (1 - P)) * (1 - P) = 0 := by
      calc (1 - P) * (P * A * (1 - P)) * (1 - P) = (1 - P) * P * A * (1 - P) * (1 - P) := by noncomm_ring
        _ = 0 := by rw [hqp]; noncomm_ring
    have h₂ : (1 - P) * ((1 - P) * C * P) * (1 - P) = 0 := by
      calc (1 - P) * ((1 - P) * C * P) * (1 - P) = (1 - P) * (1 - P) * C * P * (1 - P) := by noncomm_ring
        _ = 0 := by
          rw [hqq]
          calc (1 - P) * C * P * (1 - P) = (1 - P) * C * (P * (1 - P)) := by noncomm_ring
            _ = 0 := by rw [hpq, mul_zero]
    rw [h₁, h₂, add_zero]
  apply InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.squareZero_differential_not_Peirce_commutator_on_nonzero_odd
    hd hP (by simpa [matrixExteriorDerivativeHom] using hdP) hcorner₁₁ hcorner₀₀
  simpa [matrixExteriorDerivativeHom, peirceGradingDeriv,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using hcompat

/-- The matrix/exterior specialization of the local-rule obstruction. Unlike
`closed_cut_compatibility_forces_genPhi_zero`, this does not require the
componentwise differential to be an ordinary derivation on every matrix
product. It records only its square-zero law and the two product rules for the
even cut and the selected connection generator; these are the obligations a
graded exterior differential must discharge for this particular pair. -/
theorem graded_closed_cut_local_compatibility_forces_genPhi_zero
    {P A C : Mat}
    (d : Module.End R (ExteriorAlgebra R V))
    (hP : P * P = P)
    (hSq : ∀ X : Mat, matrixExteriorDerivative d
      (matrixExteriorDerivative d X) = 0)
    (hdP : matrixExteriorDerivative d P = 0)
    (hPX : matrixExteriorDerivative d (P * genPhi P A C) =
      matrixExteriorDerivative d P * genPhi P A C +
        P * matrixExteriorDerivative d (genPhi P A C))
    (hXP : matrixExteriorDerivative d (genPhi P A C * P) =
      matrixExteriorDerivative d (genPhi P A C) * P +
        genPhi P A C * matrixExteriorDerivative d P)
    (hcompat : matrixExteriorDerivative d (genPhi P A C) =
      peirceGradingDeriv P (genPhi P A C)) :
    genPhi P A C = 0 := by
  have hcorner₁₁ : P * genPhi P A C * P = 0 := by
    have hpq : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
    have hqp : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
    dsimp [genPhi, conePlus, coneMinus]
    rw [mul_add, add_mul]
    have h₁ : P * (P * A * (1 - P)) * P = 0 := by
      calc P * (P * A * (1 - P)) * P = P * P * A * (1 - P) * P := by noncomm_ring
        _ = 0 := by
          rw [hP]
          calc P * A * (1 - P) * P = P * A * ((1 - P) * P) := by noncomm_ring
            _ = 0 := by rw [hqp, mul_zero]
    have h₂ : P * ((1 - P) * C * P) * P = 0 := by
      calc P * ((1 - P) * C * P) * P = P * (1 - P) * C * P * P := by noncomm_ring
        _ = 0 := by rw [hpq]; noncomm_ring
    rw [h₁, h₂, add_zero]
  have hcorner₀₀ : (1 - P) * genPhi P A C * (1 - P) = 0 := by
    have hpq : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
    have hqp : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
    have hqq : (1 - P) * (1 - P) = 1 - P := by
      calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        _ = 1 - P := by rw [hP]; noncomm_ring
    dsimp [genPhi, conePlus, coneMinus]
    rw [mul_add, add_mul]
    have h₁ : (1 - P) * (P * A * (1 - P)) * (1 - P) = 0 := by
      calc (1 - P) * (P * A * (1 - P)) * (1 - P) = (1 - P) * P * A * (1 - P) * (1 - P) := by noncomm_ring
        _ = 0 := by rw [hqp]; noncomm_ring
    have h₂ : (1 - P) * ((1 - P) * C * P) * (1 - P) = 0 := by
      calc (1 - P) * ((1 - P) * C * P) * (1 - P) = (1 - P) * (1 - P) * C * P * (1 - P) := by noncomm_ring
        _ = 0 := by
          rw [hqq]
          calc (1 - P) * C * P * (1 - P) = (1 - P) * C * (P * (1 - P)) := by noncomm_ring
            _ = 0 := by rw [hpq, mul_zero]
    rw [h₁, h₂, add_zero]
  let D : Mat →+ Mat := matrixExteriorDerivativeHom (n := n) d
  apply InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.squareZero_local_differential_not_Peirce_commutator_on_nonzero_odd
      (d := D) (P := P) (X := genPhi P A C)
      (fun X => by simpa [D, matrixExteriorDerivativeHom] using hSq X)
      hP (by simpa [D, matrixExteriorDerivativeHom] using hdP)
      hcorner₁₁ hcorner₀₀
      (by simpa [D, matrixExteriorDerivativeHom] using hPX)
      (by simpa [D, matrixExteriorDerivativeHom] using hXP)
      (by simpa [D, matrixExteriorDerivativeHom, peirceGradingDeriv,
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using hcompat)

/-- Closed-cut obstruction for the actual graded exterior differential. The
local matrix product rules are derived from homogeneous degree zero of the cut,
degree one of `genPhi`, and the graded Leibniz law. Thus this result does not
assume ordinary Leibniz on all exterior-form matrices. -/
theorem graded_exterior_closed_cut_compatibility_forces_genPhi_zero
    {P A C : Mat}
    (D : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.ExteriorDifferentialData R V)
    (hPdeg : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 0 P)
    (hXdeg : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1
      (genPhi P A C))
    (hP : P * P = P)
    (hdP : matrixExteriorDerivative D.d P = 0)
    (hcompat : matrixExteriorDerivative D.d (genPhi P A C) =
      peirceGradingDeriv P (genPhi P A C)) :
    genPhi P A C = 0 := by
  apply graded_closed_cut_local_compatibility_forces_genPhi_zero
    D.d hP
    (by
      intro X
      ext i j
      simp only [matrixExteriorDerivative]
      exact InfoGeometry.Canonical.ExteriorGradedDerivationBridge.differential_sq_zero D (X i j))
    hdP
    (matrixExteriorDerivative_mul_zero_form_left D P (genPhi P A C) hPdeg)
    (by
      rw [matrixExteriorDerivative_mul_one_form_right D (genPhi P A C) P hXdeg, hdP]
      simp)
    hcompat

/-! ### Polynomial coefficients tensored with a genuine exterior generator

The existing exterior differential is linear over its scalar ring, so it
cannot differentiate a polynomial coordinate used as that scalar ring. The
following carrier keeps polynomial coefficients over the constant field and
places the one-form generator in a separate exterior-algebra factor. -/

section AffineExteriorCoefficientExtension

open scoped TensorProduct

/-- Formal partial derivatives in distinct polynomial coordinates commute.
This is the coefficient-side identity required for nilpotence of the
two-direction polynomial-form differential. -/
theorem affinePlane_partial_derivatives_commute
    {σ : Type*} [DecidableEq σ] (i j : σ) (p : MvPolynomial σ ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  let C : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ) :=
    ⁅(MvPolynomial.pderiv i : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)),
      (MvPolynomial.pderiv j : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))⁆
  have hC : C = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    by_cases hik : i = k
    · subst k
      by_cases hij : i = j
      · subst j
        simp [C, Derivation.commutator_apply]
      · simp [C, Derivation.commutator_apply, hij]
    · by_cases hjk : j = k
      · subst k
        have hij : i ≠ j := fun h => hik h
        simp [C, Derivation.commutator_apply, hij]
      · simp [C, Derivation.commutator_apply, hik, hjk]
  have hzero :
      MvPolynomial.pderiv i (MvPolynomial.pderiv j p) -
        MvPolynomial.pderiv j (MvPolynomial.pderiv i p) = 0 := by
    have h := Derivation.congr_fun hC p
    simpa [C, Derivation.commutator_apply] using h
  exact sub_eq_zero.mp hzero

/-- The off-diagonal two-direction connection matrix squares to the two
ordered products of its one-form coefficients. -/
def affinePlaneConnectionMatrix {B : Type*} [Ring B] (dx dy : B) :
    Matrix (Fin 2) (Fin 2) B := ![![0, dx], ![dy, 0]]

theorem affinePlaneConnectionMatrix_sq {B : Type*} [Ring B] (dx dy : B) :
    affinePlaneConnectionMatrix dx dy * affinePlaneConnectionMatrix dx dy =
      ![![dx * dy, 0], ![0, dy * dx]] := by
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [affinePlaneConnectionMatrix]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [affinePlaneConnectionMatrix]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [affinePlaneConnectionMatrix]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [affinePlaneConnectionMatrix]
    noncomm_ring

/-- If the ordered wedge coefficient is nonzero, the two-direction connection
has nonzero quadratic curvature. -/
theorem affinePlaneConnectionMatrix_sq_ne_zero {B : Type*} [Ring B]
    {dx dy : B} (hxy : dx * dy ≠ 0) :
    affinePlaneConnectionMatrix dx dy * affinePlaneConnectionMatrix dx dy ≠ 0 := by
  intro hzero
  have h00 := congrFun (congrFun hzero 0) 0
  rw [affinePlaneConnectionMatrix_sq] at h00
  simp at h00
  exact hxy h00

/-- The affine-line exterior coefficient carrier: polynomial functions tensored
over constants with the exterior algebra on one generator. -/
abbrev AffineExteriorCoeff := (Polynomial ℝ ⊗[ℝ] ExteriorAlgebra ℝ ℝ)

/-- The degree-one generator representing `dX`. -/
def affineExteriorDX : ExteriorAlgebra ℝ ℝ :=
  ExteriorAlgebra.ι ℝ (1 : ℝ)

/-- Send a 0-form coefficient `p` and a 1-form coefficient `q dX` to the
polynomial/exterior tensor carrier. -/
def affinePairToExteriorCoeff (p q : Polynomial ℝ) : AffineExteriorCoeff :=
  (p ⊗ₜ[ℝ] (1 : ExteriorAlgebra ℝ ℝ)) +
    (q ⊗ₜ[ℝ] affineExteriorDX)

/-- The coefficient map respects the affine-line wedge product. -/
theorem affinePairToExteriorCoeff_mul (p q r s : Polynomial ℝ) :
    affinePairToExteriorCoeff p q * affinePairToExteriorCoeff r s =
      affinePairToExteriorCoeff (p * r) (p * s + q * r) := by
  simp [affinePairToExteriorCoeff, affineExteriorDX, add_mul, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_sq_zero]
  rw [TensorProduct.add_tmul]
  abel

/-- The affine-line differential on coefficient pairs. -/
def affinePairD (p q : Polynomial ℝ) : Polynomial ℝ × Polynomial ℝ :=
  (0, Polynomial.derivative p)

/-- Differentiate the polynomial factor and wedge with the exterior generator.
This is `ℝ`-linear, but not linear over `Polynomial ℝ`. -/
def affineExteriorCoeffD : Module.End ℝ AffineExteriorCoeff :=
  TensorProduct.map Polynomial.derivative
    (Algebra.lmul ℝ (ExteriorAlgebra ℝ ℝ) affineExteriorDX)

/-- The polynomial/exterior tensor differential is square-zero on the whole
coefficient carrier, not merely on tensors in the affine-line image. -/
theorem affineExteriorCoeffD_sq_zero (x : AffineExteriorCoeff) :
    affineExteriorCoeffD (affineExteriorCoeffD x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, add_zero]
  | tmul p a =>
      have hdx : affineExteriorDX * affineExteriorDX = 0 := by
        simp [affineExteriorDX]
      change Polynomial.derivative (Polynomial.derivative p) ⊗ₜ[ℝ]
        (affineExteriorDX * (affineExteriorDX * a)) = 0
      rw [← mul_assoc, hdx, zero_mul, TensorProduct.tmul_zero]

/-- The affine-pair map intertwines the source differential with the tensor
coefficient differential on every 0-form/1-form pair. -/
theorem affinePairToExteriorCoeff_differential (p q : Polynomial ℝ) :
    affineExteriorCoeffD (affinePairToExteriorCoeff p q) =
      affinePairToExteriorCoeff 0 (Polynomial.derivative p) := by
  simp [affineExteriorCoeffD, affinePairToExteriorCoeff, affineExteriorDX,
    TensorProduct.map_tmul, Algebra.coe_lmul_eq_mul, ExteriorAlgebra.ι_sq_zero]

/-- Addition of affine-line coefficient pairs is preserved by the tensor map. -/
theorem affinePairToExteriorCoeff_add (p q r s : Polynomial ℝ) :
    affinePairToExteriorCoeff (p + r) (q + s) =
      affinePairToExteriorCoeff p q + affinePairToExteriorCoeff r s := by
  simp [affinePairToExteriorCoeff, TensorProduct.add_tmul]
  abel

/-- Zero is preserved by the affine-line coefficient map. -/
@[simp] theorem affinePairToExteriorCoeff_zero :
    affinePairToExteriorCoeff 0 0 = 0 := by
  simp [affinePairToExteriorCoeff]

/-- The affine-pair coefficient map commutes with finite sums. -/
theorem affinePairToExteriorCoeff_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (p q : α → Polynomial ℝ) :
    affinePairToExteriorCoeff (∑ i ∈ s, p i) (∑ i ∈ s, q i) =
      ∑ i ∈ s, affinePairToExteriorCoeff (p i) (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [affinePairToExteriorCoeff]
  | @insert a s has ih =>
      simp only [Finset.sum_insert has]
      rw [affinePairToExteriorCoeff_add, ih]

/-- Entrywise extension from matrix-valued affine-line forms to the tensor
exterior coefficient carrier. -/
def affineLineMatrixToExteriorCoeff (u : AffineLineMatrixForm) :
    Matrix (Fin 2) (Fin 2) AffineExteriorCoeff :=
  fun i j => affinePairToExteriorCoeff (u.degreeZero i j) (u.degreeOne i j)

/-- The entrywise soldering map preserves matrix-valued wedge multiplication. -/
theorem affineLineMatrixToExteriorCoeff_mul (u v : AffineLineMatrixForm) :
    affineLineMatrixToExteriorCoeff (affineLineFormMul u v) =
      affineLineMatrixToExteriorCoeff u * affineLineMatrixToExteriorCoeff v := by
  ext i j
  simp only [affineLineMatrixToExteriorCoeff, affineLineFormMul, Matrix.mul_apply]
  let q : Fin 2 → Polynomial ℝ := fun k =>
    u.degreeZero i k * v.degreeOne k j + u.degreeOne i k * v.degreeZero k j
  have hdegreeOne : (u.degreeZero * v.degreeOne + u.degreeOne * v.degreeZero) i j =
      ∑ k : Fin 2, q k := by
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    change (∑ k : Fin 2, u.degreeZero i k * v.degreeOne k j) +
      (∑ k : Fin 2, u.degreeOne i k * v.degreeZero k j) = ∑ k, q k
    rw [← Finset.sum_add_distrib]
  rw [hdegreeOne]
  let p : Fin 2 → Polynomial ℝ := fun k => u.degreeZero i k * v.degreeZero k j
  change affinePairToExteriorCoeff (∑ k, p k) (∑ k, q k) =
    ∑ k, affinePairToExteriorCoeff (u.degreeZero i k) (u.degreeOne i k) *
      affinePairToExteriorCoeff (v.degreeZero k j) (v.degreeOne k j)
  rw [affinePairToExteriorCoeff_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simpa [p, q] using
    (affinePairToExteriorCoeff_mul (u.degreeZero i k) (u.degreeOne i k)
      (v.degreeZero k j) (v.degreeOne k j)).symm

/-- Componentwise differential on matrices over the polynomial/exterior tensor
coefficient carrier. -/
def affineExteriorMatrixD
    (M : Matrix (Fin 2) (Fin 2) AffineExteriorCoeff) :
    Matrix (Fin 2) (Fin 2) AffineExteriorCoeff :=
  fun i j => affineExteriorCoeffD (M i j)

/-- Componentwise matrix differentiation inherits square-zero on every matrix
over the tensor coefficient carrier. -/
theorem affineExteriorMatrixD_sq_zero
    (M : Matrix (Fin 2) (Fin 2) AffineExteriorCoeff) :
    affineExteriorMatrixD (affineExteriorMatrixD M) = 0 := by
  ext i j
  exact affineExteriorCoeffD_sq_zero (M i j)

/-- The matrix soldering map also intertwines the source and target
differentials on every affine-line matrix form. -/
theorem affineLineMatrixToExteriorCoeff_differential (u : AffineLineMatrixForm) :
    affineExteriorMatrixD (affineLineMatrixToExteriorCoeff u) =
      affineLineMatrixToExteriorCoeff (affineLineFormD u) := by
  ext i j
  exact affinePairToExteriorCoeff_differential (u.degreeZero i j) (u.degreeOne i j)

/-- The moving two-sheet representation's nonzero differential remains the
Peirce connection commutator after soldering into the polynomial/exterior
tensor coefficient carrier. This is the concrete representation-level bridge
from the moving-cut model to the matrix-valued target, not merely transport of
an abstract curvature expression. -/
theorem movingSheetRep_tensor_differential_eq_connection_commutator (a b : ℝ) :
    affineExteriorMatrixD
        (affineLineMatrixToExteriorCoeff
          (affineZeroForm (movingSheetRep a b))) =
      affineLineMatrixToExteriorCoeff
        (affineOneForm
          (movingSheetConnection * movingSheetRep a b -
            movingSheetRep a b * movingSheetConnection)) := by
  rw [affineLineMatrixToExteriorCoeff_differential]
  simp only [affineLineFormD, affineZeroForm, affineOneForm]
  rw [movingSheetRep_derivative_eq_connection_commutator]

/-- The matrix soldering map preserves addition. -/
theorem affineLineMatrixToExteriorCoeff_add (u v : AffineLineMatrixForm) :
    affineLineMatrixToExteriorCoeff (affineLineFormAdd u v) =
      affineLineMatrixToExteriorCoeff u + affineLineMatrixToExteriorCoeff v := by
  ext i j
  exact affinePairToExteriorCoeff_add (u.degreeZero i j) (u.degreeOne i j)
    (v.degreeZero i j) (v.degreeOne i j)

/-- The affine-line matrix soldering preserves the unit, completing its
additive, multiplicative, and unital algebra-map laws on the pair carrier. -/
theorem affineLineMatrixToExteriorCoeff_one :
    affineLineMatrixToExteriorCoeff affineLineFormOne =
      (1 : Matrix (Fin 2) (Fin 2) AffineExteriorCoeff) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [affineLineMatrixToExteriorCoeff, affineLineFormOne,
      affinePairToExteriorCoeff, affineExteriorDX, Matrix.one_apply_eq,
      Matrix.zero_apply]
    change (1 : Polynomial ℝ) ⊗ₜ[ℝ] (1 : ExteriorAlgebra ℝ ℝ) +
      (0 : Polynomial ℝ) ⊗ₜ[ℝ] (affineExteriorDX) = (1 : AffineExteriorCoeff)
    rw [TensorProduct.zero_tmul, add_zero]
    exact Algebra.TensorProduct.one_def.symm
  · simp [affineLineMatrixToExteriorCoeff, affineLineFormOne,
      affinePairToExteriorCoeff, h]

/-- The entrywise soldering map preserves zero. -/
theorem affineLineMatrixToExteriorCoeff_zero :
    affineLineMatrixToExteriorCoeff affineLineFormZero = 0 := by
  ext i j
  simp [affineLineMatrixToExteriorCoeff, affineLineFormZero,
    affinePairToExteriorCoeff]

/-- Negation is preserved by the affine-line matrix soldering map. -/
theorem affineLineMatrixToExteriorCoeff_neg (u : AffineLineMatrixForm) :
    affineLineMatrixToExteriorCoeff (affineLineFormNeg u) =
      -affineLineMatrixToExteriorCoeff u := by
  have h := congrArg affineLineMatrixToExteriorCoeff (affineLineFormAdd_neg u)
  rw [affineLineMatrixToExteriorCoeff_add,
    affineLineMatrixToExteriorCoeff_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Subtraction, defined by the pair carrier's additive inverse, is preserved
by its tensor coefficient map. -/
theorem affineLineMatrixToExteriorCoeff_sub (u v : AffineLineMatrixForm) :
    affineLineMatrixToExteriorCoeff (affineLineFormAdd u (affineLineFormNeg v)) =
      affineLineMatrixToExteriorCoeff u - affineLineMatrixToExteriorCoeff v := by
  rw [affineLineMatrixToExteriorCoeff_add,
    affineLineMatrixToExteriorCoeff_neg]
  rfl

/-- The tensor soldering map carries the moving-sheet derivative to the
connection's left-minus-right bimodule action on the one-form image. -/
theorem movingSheetRep_tensor_differential_eq_target_bimodule_commutator (a b : ℝ) :
    affineExteriorMatrixD
        (affineLineMatrixToExteriorCoeff
          (affineZeroForm (movingSheetRep a b))) =
      affineLineMatrixToExteriorCoeff
          (affineZeroForm movingSheetConnection) *
        affineLineMatrixToExteriorCoeff
          (affineOneForm (movingSheetRep a b)) -
        affineLineMatrixToExteriorCoeff
          (affineOneForm (movingSheetRep a b)) *
        affineLineMatrixToExteriorCoeff
          (affineZeroForm movingSheetConnection) := by
  rw [movingSheetRep_tensor_differential_eq_connection_commutator]
  have hsource :
      affineOneForm
          (movingSheetConnection * movingSheetRep a b -
            movingSheetRep a b * movingSheetConnection) =
        affineLineFormAdd
          (affineOneForm (movingSheetConnection * movingSheetRep a b))
          (affineLineFormNeg
            (affineOneForm (movingSheetRep a b * movingSheetConnection))) := by
    apply affineLineMatrixForm_ext <;>
      simp [affineOneForm, affineLineFormAdd, affineLineFormNeg,
        sub_eq_add_neg]
  have hmul₁ : affineOneForm (movingSheetConnection * movingSheetRep a b) =
      affineLineFormMul (affineZeroForm movingSheetConnection)
        (affineOneForm (movingSheetRep a b)) := by
    apply affineLineMatrixForm_ext <;>
      simp [affineOneForm, affineZeroForm, affineLineFormMul]
  have hmul₂ : affineOneForm (movingSheetRep a b * movingSheetConnection) =
      affineLineFormMul (affineOneForm (movingSheetRep a b))
        (affineZeroForm movingSheetConnection) := by
    apply affineLineMatrixForm_ext <;>
      simp [affineOneForm, affineZeroForm, affineLineFormMul]
  rw [hsource, affineLineMatrixToExteriorCoeff_sub]
  rw [hmul₁, hmul₂]
  rw [← affineLineMatrixToExteriorCoeff_mul,
    ← affineLineMatrixToExteriorCoeff_mul]

/-- Curvature expressions on the affine-line source and its polynomial/exterior
coefficient target. -/
def affineLineMatrixCurvature (A : AffineLineMatrixForm) : AffineLineMatrixForm :=
  affineLineFormAdd (affineLineFormD A) (affineLineFormMul A A)

def affineExteriorMatrixCurvature
    (A : Matrix (Fin 2) (Fin 2) AffineExteriorCoeff) :
    Matrix (Fin 2) (Fin 2) AffineExteriorCoeff :=
  affineExteriorMatrixD A + A * A

/-- Curvature is transported by the constructed affine-line matrix map. This is
the connection-level bridge on the polynomial/exterior tensor carrier; the
existing exterior-only Bianchi owner still needs to be generalized or supplied
with a carrier equivalence before it can consume this result. -/
theorem affineLineMatrixToExteriorCoeff_curvature (A : AffineLineMatrixForm) :
    affineLineMatrixToExteriorCoeff (affineLineMatrixCurvature A) =
      affineExteriorMatrixCurvature (affineLineMatrixToExteriorCoeff A) := by
  rw [affineLineMatrixCurvature, affineExteriorMatrixCurvature,
    affineLineMatrixToExteriorCoeff_add,
    affineLineMatrixToExteriorCoeff_differential,
    affineLineMatrixToExteriorCoeff_mul]

/-- The one-generator affine-line carrier has no nonzero curvature for a
genuine one-form connection: its differential vanishes on degree one and the
wedge product of two degree-one forms vanishes. Thus nontrivial Yang--Mills
curvature requires a carrier with at least two independent form directions. -/
theorem affineLineConnection_one_form_curvature_vanishes (A : MovingSheetMat) :
    affineLineMatrixCurvature (affineOneForm A) = affineLineFormZero := by
  have hD0 : movingSheetDerivative (0 : MovingSheetMat) = 0 := by
    apply movingSheet_ext <;> simp [movingSheetDerivative]
  change affineLineFormAdd (affineOneForm (movingSheetDerivative (0 : MovingSheetMat)))
    (affineLineFormMul (affineOneForm A) (affineOneForm A)) = affineLineFormZero
  rw [hD0]
  apply affineLineMatrixForm_ext <;>
    simp [affineLineFormAdd, affineLineFormMul, affineOneForm, affineLineFormZero]

end AffineExteriorCoefficientExtension

end InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap

namespace InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMapWitnesses

open scoped TensorProduct

theorem movingSheet_mat2_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) (Polynomial ℝ), A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem peirceExterior_mat2_noncomm {R V : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup V] [Module R V] :
    ∃ A B : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V), A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem affineExteriorCoeff_mat2_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) (Polynomial ℝ ⊗[ℝ] ExteriorAlgebra ℝ ℝ),
      A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  exact absurd h00 (by norm_num)

end InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMapWitnesses

end noncomputable section
