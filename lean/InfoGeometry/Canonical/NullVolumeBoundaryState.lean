/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
import InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge
import InfoGeometry.Clifford.ExteriorZornCARIntertwiner
import InfoGeometry.Canonical.CantorSplitNullBridge
import InfoGeometry.Canonical.SplitCliffordCantorFock
import InfoGeometry.Canonical.OperatorCl11WittBasis
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.UHFDiracSpectralTripleColimit
import InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit
import InfoGeometry.Canonical.AlgebraicSolderingTransport

/-!
# Null Volume Operator Represented State (Jaynesian Inductive Colimit Synthesis)

Unifies the null-volume operator and its represented boundary state strictly within
the repository's **Jaynesian inductive colimit** architecture (`UHFAlg` and
`RealBlockColimit m`), with **no** `UniformSpace.Completion`, **no** `H_lp` / `ℓ²`
Hilbert completion, and **no** postulated non-inductive continuum:

1. **Zorn Algebraic Soldering & `Cl(5,5) → Exterior3 → ZornMatrix ℝ` Intertwiner**:
   Explicit bijection `zornCellMatrixEquiv : ZornCell ℝ ≃ ZornMatrix ℝ` preserving
   addition and Zorn multiplication, intertwining `zornTopRightNull` / `zornBottomLeftNull`
   with `chiralUpperBasis 0` / `chiralLowerBasis 0`, composing with
   `cl55VacuumIdealSpinorEquiv` and `fockToZorn` to intertwine the first three `Cl(5,5)`
   modes with the Zorn regular CAR operators, and inducing the represented Zorn-Fock
   vacuum state `zornVacuumState`.
2. **Cantor Bit → Four-Carrier Null-Volume Soldering**:
   Connects finite Cantor words `BitWord n` / `FiniteBinaryWord` simultaneously to
   `ZornCell ℝ`, `ZornMatrix ℝ`, `Cl55` (`infinityClifford55` / `originClifford55`,
   with null-volume projector `infinityProjector55 = ι(∞)ι(0)` reading `affineGaugeCoord`),
   and `M₂(ℝ)` ladder modes (`a_op`, `aDag_op`).
3. **Jaynesian Inductive-Colimit Sewn `Cl(1,1)` & Anomaly Cancellation**:
   Replaces completed `H_lp` sewing with the finite-stage `Cl(1,1)` pair
   `(localSwapJ, localChiralEps)` lifted into `RealBlockColimit 2`, instantiating
   `OperatorCl11` (recovering `a_op = wittPlus`, `aDag_op = wittMinus`, and
   `localNullVolProj = a_op * aDag_op`) and proving sewn boundary chiral anomaly
   cancellation `colimitHSInner ψ (colimitSewnEps * (B * ψ)) = 0` for `colimitSewnJ`-fixed
   states and sewn elements `B` in `RealBlockColimit 2`.
4. **Cantor-Cylinder MASA Intertwiner & Represented Null-Volume State on `UHFAlg`**:
   Builds the exact stagewise isomorphism `bitWordEquivFin n : BitWord n ≃ Fin (2 ^ n)`
   and diagonal embedding `diagToUHFStage n : DiagAlg n → UHFStage n`, proving
   `diagToUHFStage (n + 1) (diagEmbedSucc n f) = uhfStep n (diagToUHFStage n f)` and
   `stageProj0 n = diagToUHFStage (n + 1) (fun w => if w 0 then 0 else 1)`. Defines the
   positive unital state `nullVolumeUHFState x = 2 * uhfColimitTrace (uhfNullVolProj * x * uhfNullVolProj)`
   on `UHFAlg` and its compatible pullback `nullVolumeCylinderState` on `DiagAlg (n + 1)`.
5. **`Pin(5,5)` Bisognano–Wichmann Wedge Causality in `RealBlockColimit 10`**:
   Binds the Krein-isometric boost group and Unruh wedge KMS identity from
   `JaynesianTomitaBisognanoColimit` together with the four layers above into
   `jaynesian_null_volume_boundary_state_synthesis`.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NullVolumeBoundaryState

open Matrix
open InfoGeometry.Clifford.Clifford55
open ProjectiveAffineConformalClosure55
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
open InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge
open InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.ExteriorZornCARIntertwiner
open InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open InfoGeometry.Canonical.SplitZornNullBoundary
open InfoGeometry.Canonical.CantorSplitNullBridge
open InfoGeometry.Canonical.TypeIIIModularCantorSystem
open InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord
open InfoGeometry.Canonical.SplitCliffordCantorFock
open InfoGeometry.Canonical.OperatorCl11WittBasis
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.UHFColimitCStarCompletion
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.UHFTracialStateCore
open InfoGeometry.Canonical.UHFDiracSpectralTripleColimit
open InfoGeometry.Canonical.BisognanoPeirceProjectionCore
open InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit
open InfoGeometry.Canonical.Pin55BisognanoWichmannBoost

/-!
## 1. Explicit Zorn Soldering & `Cl(5,5) → Exterior3 → ZornMatrix ℝ` Intertwiner
-/

/-- Explicit coordinate isomorphism from `ZornCell ℝ` (`SplitZornNullBoundary` /
`CantorSplitNullBridge`) to `InfoGeometry.Canonical.ZornMatrix ℝ`. -/
def zornCellToMatrix (X : ZornCell ℝ) : InfoGeometry.Canonical.ZornMatrix ℝ where
  a := X.r
  b := X.s
  x := ![X.x1, X.x2, X.x3]
  y := ![X.y1, X.y2, X.y3]

/-- Inverse coordinate map from `InfoGeometry.Canonical.ZornMatrix ℝ` to `ZornCell ℝ`. -/
def zornMatrixToCell (Z : InfoGeometry.Canonical.ZornMatrix ℝ) : ZornCell ℝ where
  r := Z.a
  s := Z.b
  x1 := Z.x 0
  x2 := Z.x 1
  x3 := Z.x 2
  y1 := Z.y 0
  y2 := Z.y 1
  y3 := Z.y 2

/-- Bundled equivalence `ZornCell ℝ ≃ InfoGeometry.Canonical.ZornMatrix ℝ`. -/
def zornCellMatrixEquiv : ZornCell ℝ ≃ InfoGeometry.Canonical.ZornMatrix ℝ where
  toFun := zornCellToMatrix
  invFun := zornMatrixToCell
  left_inv X := by
    cases X
    rfl
  right_inv Z := by
    cases Z with
    | mk a b x y =>
      apply InfoGeometry.Canonical.ZornMatrix.ext
      · rfl
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl

/-- `zornCellToMatrix` preserves Zorn addition. -/
theorem zornCellToMatrix_add (X Y : ZornCell ℝ) :
    zornCellToMatrix (addZ X Y) = zornCellToMatrix X + zornCellToMatrix Y := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- Exact algebraic soldering: `zornCellToMatrix` preserves nonassociative Zorn multiplication. -/
theorem zornCellToMatrix_mul (X Y : ZornCell ℝ) :
    zornCellToMatrix (X * Y) = zornCellToMatrix X * zornCellToMatrix Y := by
  change zornCellToMatrix (mulZ X Y) = zornCellToMatrix X * zornCellToMatrix Y
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [zornCellToMatrix, mulZ, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot]
  · simp [zornCellToMatrix, mulZ, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot]
    ring
  · funext i
    fin_cases i <;>
    · simp [zornCellToMatrix, mulZ, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.cross]
  · funext i
    fin_cases i <;>
    · simp [zornCellToMatrix, mulZ, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.cross]
      try ring

@[simp] theorem zornCellToMatrix_topRight :
    zornCellToMatrix zornTopRightNull =
      InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0 := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [zornCellToMatrix, zornTopRightNull,
      InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis]
  · funext i; fin_cases i <;> simp [zornCellToMatrix, zornTopRightNull,
      InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis]

@[simp] theorem zornCellToMatrix_bottomLeft :
    zornCellToMatrix zornBottomLeftNull =
      InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis (R := ℝ) 0 := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [zornCellToMatrix, zornBottomLeftNull,
      InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis]
  · funext i; fin_cases i <;> simp [zornCellToMatrix, zornBottomLeftNull,
      InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis]

/-- Transported hyperbolic pair satisfies the exact mixed CAR anticommutator `= 1`
in `ZornMatrix ℝ`. -/
theorem zornCellToMatrix_nullPair_car :
    zornCellToMatrix zornTopRightNull * zornCellToMatrix zornBottomLeftNull +
      zornCellToMatrix zornBottomLeftNull * zornCellToMatrix zornTopRightNull =
      (1 : InfoGeometry.Canonical.ZornMatrix ℝ) := by
  rw [zornCellToMatrix_topRight, zornCellToMatrix_bottomLeft]
  simpa using raw_mixed_CAR 0 0

/-- Exterior retraction onto the first three color coordinates (defined locally without
pulling in concurrently dirty bridge modules). -/
def projectColorExterior :
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.Spinor →ₐ[ℝ] Exterior3 :=
  ExteriorAlgebra.map fiveVectorToColor

theorem projectColorExterior_includeColorExterior (ψ : Exterior3) :
    projectColorExterior (includeColorExterior ψ) = ψ := by
  change ((ExteriorAlgebra.map fiveVectorToColor).comp
    (ExteriorAlgebra.map colorVectorToFive)) ψ = ψ
  rw [ExteriorAlgebra.map_comp_map, fiveVectorToColor_colorVectorToFive,
    ExteriorAlgebra.map_id]
  rfl

/-- `Cl(5,5)` vacuum-ideal creation generators intertwine across `Exterior3` with the
Zorn regular creation operators. -/
theorem cl55_color_creation_intertwines_zorn (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (annihilation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ)))) =
      InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i (fockToZorn ψ) := by
  rw [cl55_annihilation55_restricts_to_color_creation,
    projectColorExterior_includeColorExterior, fockToZorn_wedge]
  have hbasis : basisVector3 i = Pi.single i (1 : ℝ) := by
    funext j
    by_cases h : j = i <;> simp [basisVector3, h]
  rw [hbasis, creationMap_basis]

/-- `Cl(5,5)` vacuum-ideal annihilation generators intertwine across `Exterior3` with the
Zorn regular annihilation operators. -/
theorem cl55_color_annihilation_intertwines_zorn (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (creation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ)))) =
      InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i (fockToZorn ψ) := by
  rw [cl55_creation55_restricts_to_color_annihilation,
    projectColorExterior_includeColorExterior, fockToZorn_contract]

/-- Represented Fock vacuum expectation functional on the associative endomorphism algebra
of `ZornMatrix ℝ`, reading the lower-pole `zornMinus` vacuum coefficient. -/
def zornVacuumState (T : Module.End ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)) : ℝ :=
  (T (InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ))).b

theorem vacuumProjector_eq_zornVacuumState_smul
    (T : Module.End ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)) :
    vacuumProjector (T (InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ))) =
      zornVacuumState T • InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ) :=
  vacuumProjector_apply (T (InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ)))

theorem zornVacuumState_one :
    zornVacuumState (1 : Module.End ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)) = 1 := rfl

theorem zornVacuumState_add
    (S T : Module.End ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)) :
    zornVacuumState (S + T) = zornVacuumState S + zornVacuumState T := by
  simp [zornVacuumState]

theorem zornVacuumState_smul (c : ℝ)
    (T : Module.End ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)) :
    zornVacuumState (c • T) = c * zornVacuumState T := by
  simp [zornVacuumState, InfoGeometry.Canonical.ZornMatrix.smul_b]

theorem zornVacuumState_create_annihilate_zero (i : Fin 3) :
    zornVacuumState
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) = 0 := by
  unfold zornVacuumState
  rw [Module.End.mul_apply, (regular_vacuum i).1, map_zero]
  rfl

theorem zornVacuumState_annihilate_create_one (i : Fin 3) :
    zornVacuumState
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) = 1 := by
  have hcar := congrArg (fun T : Module.End ℝ (InfoGeometry.Canonical.ZornMatrix ℝ) =>
    zornVacuumState T) (regular_mixed_CAR i i)
  simp only [ite_true, zornVacuumState_add] at hcar
  rw [zornVacuumState_create_annihilate_zero i, zero_add] at hcar
  exact hcar

theorem zornVacuumState_vacuumProjector :
    zornVacuumState vacuumProjector = 1 := by
  unfold zornVacuumState
  rw [vacuumProjector_apply]
  simp [InfoGeometry.Canonical.ZornMatrix.zornMinus]

/-!
## 2. Cantor Bit → Four-Carrier Null-Volume Soldering
-/

/-- Embed a fixed-length `BitWord n` into `FiniteBinaryWord := List Bool`. -/
def bitWordToBinaryWord {n : ℕ} (w : BitWord n) : FiniteBinaryWord :=
  List.ofFn w

theorem bitWordToBinaryWord_extendSucc (n : ℕ) (w : BitWord n) (b : Bool) :
    bitWordToBinaryWord (extendSucc n w b) = child (bitWordToBinaryWord w) b := by
  unfold bitWordToBinaryWord child
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [List.getElem_ofFn, List.getElem_append]
    by_cases hlt : i < n
    · have hc : i < (List.ofFn w).length := by simpa using hlt
      rw [dif_pos hc]
      simp [List.getElem_ofFn, extendSucc, hlt]
    · have hc : ¬ (i < (List.ofFn w).length) := by simpa using hlt
      have hieq : i = n := by
        have hi : i < n + 1 := by simpa using hi₁
        omega
      rw [dif_neg hc]
      simp [extendSucc, hieq]

theorem addressNullGenerator_extendSucc (n : ℕ) (w : BitWord n) (b : Bool) :
    addressNullGenerator (bitWordToBinaryWord (extendSucc n w b)) = bitNullGenerator b := by
  rw [bitWordToBinaryWord_extendSucc, addressNullGenerator_child]

/-- Bit selector transported into `InfoGeometry.Canonical.ZornMatrix ℝ`. -/
def bitZornMatrixNull (b : Bool) : InfoGeometry.Canonical.ZornMatrix ℝ :=
  zornCellToMatrix (bitNullGenerator b)

/-- Bit selector into the `Cl(5,5)` Witt infinity/origin pair `(ι(∞), ι(0))`. -/
def bitCl55Null : Bool → Cl55
  | false => infinityClifford55
  | true => originClifford55

/-- Bit selector into the `M₂(ℝ)` Cantor Fock ladder `(a, a†)`. -/
def bitFockLadder : Bool → M2R
  | false => a_op
  | true => aDag_op

theorem bitCl55Null_sq_zero (b : Bool) :
    bitCl55Null b * bitCl55Null b = 0 := by
  cases b
  · exact infinityClifford55_sq_zero
  · exact originClifford55_sq_zero

theorem bitCl55Null_car :
    bitCl55Null false * bitCl55Null true + bitCl55Null true * bitCl55Null false = 1 :=
  infinity_origin_CAR_clifford

theorem bitCl55Null_nullVolumeProjector :
    bitCl55Null false * bitCl55Null true = infinityProjector55 := rfl

theorem bitFockLadder_sq_zero (b : Bool) :
    bitFockLadder b * bitFockLadder b = 0 := by
  cases b
  · exact a_op_sq_zero
  · exact aDag_op_sq_zero

theorem bitFockLadder_car :
    bitFockLadder false * bitFockLadder true + bitFockLadder true * bitFockLadder false = 1 :=
  local_car_identity

theorem bitFockLadder_nullVolumeProjector :
    bitFockLadder false * bitFockLadder true = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bitFockLadder, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem bitCl55Null_affineGauge_readout (X : PACSplit55) :
    bitCl55Null false * ι55 (pacSplit55ToV55 X) +
        ι55 (pacSplit55ToV55 X) * bitCl55Null false =
      algebraMap ℝ Cl55 (affineGaugeCoord X) :=
  infinity_reads_affineGauge X

/-!
## 3. Jaynesian Inductive-Colimit Sewn `Cl(1,1)` & Anomaly Cancellation
-/

/-- Finite-stage modular swap involution `J₂ = a + a† = !![0, 1; 1, 0]` on `RealBlockStage 2 0`. -/
def localSwapJ : RealBlockStage 2 0 := a_op + aDag_op

/-- Finite-stage chiral grading `ε₂ = a a† - a† a = !![1, 0; 0, -1]` on `RealBlockStage 2 0`. -/
def localChiralEps : RealBlockStage 2 0 := a_op * aDag_op - aDag_op * a_op

/-- Finite-stage null-volume projector `P₀ = a a† = !![1, 0; 0, 0]` on `RealBlockStage 2 0`. -/
def localNullVolProj : RealBlockStage 2 0 := a_op * aDag_op

theorem localSwapJ_sq : localSwapJ * localSwapJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localSwapJ, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem localChiralEps_sq : localChiralEps * localChiralEps = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localChiralEps, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem localSwapJ_transpose : localSwapJᵀ = localSwapJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [localSwapJ, a_op, aDag_op]

theorem localChiralEps_transpose : localChiralEpsᵀ = localChiralEps := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [localChiralEps, a_op, aDag_op]

theorem localSwapJ_anticomm_eps :
    localSwapJ * localChiralEps = -(localChiralEps * localSwapJ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localSwapJ, localChiralEps, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem localNullVolProj_sq : localNullVolProj * localNullVolProj = localNullVolProj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localNullVolProj, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem localNullVolProj_eq_half_add_eps :
    localNullVolProj = (1 / 2 : ℝ) • (1 + localChiralEps) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localNullVolProj, localChiralEps, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

/-- Instantiates `OperatorCl11` with `Γ := localSwapJ` and `J := localChiralEps`. -/
instance instOperatorCl11Local : OperatorCl11 localSwapJ localChiralEps where
  gamma_sq := localSwapJ_sq
  exchange_sq := localChiralEps_sq
  exchange_gamma_anticomm := by
    rw [← neg_eq_iff_eq_neg]
    exact localSwapJ_anticomm_eps.symm

theorem wittPlus_local_eq_a_op : wittPlus localSwapJ localChiralEps = a_op := by
  unfold wittPlus OperatorCl11WittBasis.phase OperatorCl11WittBasis.half
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [localSwapJ, localChiralEps, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two,
      Algebra.algebraMap_eq_smul_one, Rat.smul_def]; try norm_num)

theorem wittMinus_local_eq_aDag_op : wittMinus localSwapJ localChiralEps = aDag_op := by
  unfold wittMinus OperatorCl11WittBasis.phase OperatorCl11WittBasis.half
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [localSwapJ, localChiralEps, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two,
      Algebra.algebraMap_eq_smul_one, Rat.smul_def]; try norm_num)

theorem wittPlus_mul_wittMinus_eq_localNullVolProj :
    wittPlus localSwapJ localChiralEps * wittMinus localSwapJ localChiralEps =
      localNullVolProj := by
  rw [wittPlus_local_eq_a_op, wittMinus_local_eq_aDag_op]
  rfl

/-- Jaynesian inductive-colimit sewn swap involution in `RealBlockColimit 2`. -/
def colimitSewnJ : RealBlockColimit 2 := toBlockColimit 0 localSwapJ

/-- Jaynesian inductive-colimit chiral grading in `RealBlockColimit 2`. -/
def colimitSewnEps : RealBlockColimit 2 := toBlockColimit 0 localChiralEps

/-- Jaynesian inductive-colimit null-volume projector in `RealBlockColimit 2`. -/
def colimitNullVolProj : RealBlockColimit 2 := toBlockColimit 0 localNullVolProj

theorem colimitSewnJ_sq : colimitSewnJ * colimitSewnJ = 1 := by
  unfold colimitSewnJ
  rw [mul_toBlockColimit, localSwapJ_sq, toBlockColimit_one]

theorem colimitSewnEps_sq : colimitSewnEps * colimitSewnEps = 1 := by
  unfold colimitSewnEps
  rw [mul_toBlockColimit, localChiralEps_sq, toBlockColimit_one]

theorem colimitSewnJ_star : star colimitSewnJ = colimitSewnJ := by
  unfold colimitSewnJ
  rw [star_toBlockColimit_transpose, localSwapJ_transpose]

theorem colimitSewnEps_star : star colimitSewnEps = colimitSewnEps := by
  unfold colimitSewnEps
  rw [star_toBlockColimit_transpose, localChiralEps_transpose]

theorem colimitSewnJ_anticomm_eps :
    colimitSewnJ * colimitSewnEps = -(colimitSewnEps * colimitSewnJ) := by
  unfold colimitSewnJ colimitSewnEps
  rw [mul_toBlockColimit, mul_toBlockColimit, neg_toBlockColimit, localSwapJ_anticomm_eps]

theorem colimitNullVolProj_idempotent :
    colimitNullVolProj * colimitNullVolProj = colimitNullVolProj := by
  unfold colimitNullVolProj
  rw [mul_toBlockColimit, localNullVolProj_sq]

theorem colimitNullVolProj_eq_half_add_eps :
    colimitNullVolProj = (1 / 2 : ℝ) • (1 + colimitSewnEps) := by
  unfold colimitNullVolProj colimitSewnEps
  rw [← toBlockColimit_one 0, add_toBlockColimit, smul_toBlockColimit,
    ← localNullVolProj_eq_half_add_eps]

theorem colimitSewnJ_eps_noncomm :
    colimitSewnJ * colimitSewnEps ≠ colimitSewnEps * colimitSewnJ := by
  intro h
  unfold colimitSewnJ colimitSewnEps at h
  rw [mul_toBlockColimit, mul_toBlockColimit] at h
  have hmat := toBlockColimit_injective 0 h
  have h01 := congrArg (fun M : RealBlockStage 2 0 => M 0 1) hmat
  norm_num [localSwapJ, localChiralEps, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Left multiplication by any self-adjoint colimit element is symmetric with respect to
`colimitHSInner` in `RealBlockColimit m`. -/
theorem colimitHSInner_mul_left_selfAdjoint {m : ℕ} (a x y : RealBlockColimit m)
    (ha : star a = a) :
    colimitHSInner (a * x) y = colimitHSInner x (a * y) := by
  rcases toBlockColimit_lift_three a x y with ⟨k, A, X, Y, rfl, rfl, rfl⟩
  have hstar : toBlockColimit k (star A) = toBlockColimit k A := by
    simpa [star_toBlockColimit] using ha
  have hA_star : star A = A := toBlockColimit_injective k hstar
  have hA_tr : Aᵀ = A := by
    ext i j
    simpa [Matrix.star_apply] using congrArg (fun M : RealBlockStage m k => M i j) hA_star
  rw [mul_toBlockColimit, mul_toBlockColimit, colimitHSInner_toBlockColimit,
    colimitHSInner_toBlockColimit]
  unfold normHSInner FiniteMatrixTomitaPolar.hsInner
  rw [Matrix.transpose_mul, hA_tr, Matrix.mul_assoc]

theorem colimitHSInner_neg_right {m : ℕ} (x y : RealBlockColimit m) :
    colimitHSInner x (-y) = -colimitHSInner x y := by
  have hneg : (-y : RealBlockColimit m) = (-1 : ℝ) • y := (neg_one_smul ℝ y).symm
  rw [hneg, colimitHSInner_smul_right]
  ring

/-- **Jaynesian Sewn Boundary Anomaly Cancellation (Paired Summand)**:
replaces the `H_lp` `ℓ²` cancellation law purely inside `RealBlockColimit 2`. -/
theorem jaynesian_paired_chiral_summand_zero (B : RealBlockColimit 2)
    (hB : colimitSewnJ * B * colimitSewnJ = B) (ψ : RealBlockColimit 2) :
    colimitHSInner ψ (colimitSewnEps * (B * ψ)) +
      colimitHSInner (colimitSewnJ * ψ) (colimitSewnEps * (B * (colimitSewnJ * ψ))) = 0 := by
  have h_second :
      colimitHSInner (colimitSewnJ * ψ) (colimitSewnEps * (B * (colimitSewnJ * ψ))) =
        -colimitHSInner ψ (colimitSewnEps * (B * ψ)) := by
    calc
      colimitHSInner (colimitSewnJ * ψ) (colimitSewnEps * (B * (colimitSewnJ * ψ)))
          = colimitHSInner ψ (colimitSewnJ * (colimitSewnEps * (B * (colimitSewnJ * ψ)))) :=
            colimitHSInner_mul_left_selfAdjoint colimitSewnJ ψ _ colimitSewnJ_star
      _ = colimitHSInner ψ ((colimitSewnJ * colimitSewnEps) * (B * (colimitSewnJ * ψ))) := by
            simp only [mul_assoc]
      _ = colimitHSInner ψ (-(colimitSewnEps * colimitSewnJ) * (B * (colimitSewnJ * ψ))) := by
            rw [colimitSewnJ_anticomm_eps]
      _ = colimitHSInner ψ (-(colimitSewnEps * ((colimitSewnJ * B * colimitSewnJ) * ψ))) := by
            simp only [neg_mul, mul_assoc]
      _ = colimitHSInner ψ (-(colimitSewnEps * (B * ψ))) := by rw [hB]
      _ = -colimitHSInner ψ (colimitSewnEps * (B * ψ)) := colimitHSInner_neg_right _ _
  linarith

/-- **Jaynesian Sewn Boundary Anomaly Cancellation (Fixed State)**:
every `colimitSewnJ`-fixed state has zero chiral expectation for every sewn operator `B`. -/
theorem jaynesian_sewn_chiral_expectation_zero (B : RealBlockColimit 2)
    (hB : colimitSewnJ * B * colimitSewnJ = B) (ψ : RealBlockColimit 2)
    (hψ : colimitSewnJ * ψ = ψ) :
    colimitHSInner ψ (colimitSewnEps * (B * ψ)) = 0 := by
  have hpair := jaynesian_paired_chiral_summand_zero B hB ψ
  rw [hψ] at hpair
  linarith

/-- Concrete nonzero `colimitSewnJ`-fixed vacuum element in `RealBlockColimit 2`. -/
def colimitSewnVacuum : RealBlockColimit 2 :=
  toBlockColimit 0 !![(1 : ℝ), 1; 1, 1]

theorem colimitSewnVacuum_ne_zero : colimitSewnVacuum ≠ 0 := by
  intro h
  unfold colimitSewnVacuum at h
  rw [← toBlockColimit_zero 0] at h
  have hmat := toBlockColimit_injective 0 h
  have h00 := congrArg (fun M : RealBlockStage 2 0 => M 0 0) hmat
  norm_num at h00

theorem colimitSewnVacuum_fixed : colimitSewnJ * colimitSewnVacuum = colimitSewnVacuum := by
  unfold colimitSewnJ colimitSewnVacuum
  rw [mul_toBlockColimit]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localSwapJ, a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem colimitSewnVacuum_chiral_zero (B : RealBlockColimit 2)
    (hB : colimitSewnJ * B * colimitSewnJ = B) :
    colimitHSInner colimitSewnVacuum (colimitSewnEps * (B * colimitSewnVacuum)) = 0 :=
  jaynesian_sewn_chiral_expectation_zero B hB colimitSewnVacuum colimitSewnVacuum_fixed

/-!
## 4. Cantor-Cylinder MASA Intertwiner & Represented Null-Volume State on `UHFAlg`
-/

/-- Split an `(n + 1)`-bit Cantor word by its last bit into two `n`-bit halves. -/
def bitWordSplitEquiv (n : ℕ) : BitWord (n + 1) ≃ BitWord n ⊕ BitWord n where
  toFun w := if w ⟨n, Nat.lt_succ_self n⟩ then Sum.inr (prefixSucc n w)
             else Sum.inl (prefixSucc n w)
  invFun
    | Sum.inl w => extendSucc n w false
    | Sum.inr w => extendSucc n w true
  left_inv w := by
    by_cases hlast : w ⟨n, Nat.lt_succ_self n⟩ = true
    · simp only [hlast, ↓reduceIte]
      ext i
      have hi_lt : i.1 < n + 1 := i.isLt
      by_cases hi : i.1 < n
      · simp [extendSucc, prefixSucc, hi]
      · have hi_val : i.1 = n := by omega
        have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi_val
        simp [extendSucc, hieq, hlast]
    · have hfalse : w ⟨n, Nat.lt_succ_self n⟩ = false := Bool.eq_false_iff.mpr hlast
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      ext i
      have hi_lt : i.1 < n + 1 := i.isLt
      by_cases hi : i.1 < n
      · simp [extendSucc, prefixSucc, hi]
      · have hi_val : i.1 = n := by omega
        have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi_val
        simp [extendSucc, hieq, hfalse]
  right_inv s := by
    cases s with
    | inl w =>
      have hlast : extendSucc n w false ⟨n, Nat.lt_succ_self n⟩ = false := by
        simp [extendSucc]
      simp [hlast, prefixSucc_extendSucc]
    | inr w =>
      have hlast : extendSucc n w true ⟨n, Nat.lt_succ_self n⟩ = true := by
        simp [extendSucc]
      simp [hlast, prefixSucc_extendSucc]

/-- Recursive equivalence `BitWord n ≃ Fin (2 ^ n)` compatible with `finSumTwoPow`. -/
def bitWordEquivFin : (n : ℕ) → BitWord n ≃ Fin (2 ^ n)
  | 0 =>
    { toFun := fun _ => 0
      invFun := fun _ i => Fin.elim0 i
      left_inv := fun w => by ext i; exact Fin.elim0 i
      right_inv := fun j => by
        have hj : j.1 < 2 ^ 0 := j.2
        ext; omega }
  | n + 1 =>
    (bitWordSplitEquiv n).trans
      ((Equiv.sumCongr (bitWordEquivFin n) (bitWordEquivFin n)).trans (finSumTwoPow n))

@[simp] theorem bitWordEquivFin_symm_finSumTwoPow_inl (n : ℕ) (i : Fin (2 ^ n)) :
    (bitWordEquivFin (n + 1)).symm (finSumTwoPow n (Sum.inl i)) =
      extendSucc n ((bitWordEquivFin n).symm i) false := by
  change (bitWordSplitEquiv n).symm ((Equiv.sumCongr (bitWordEquivFin n) (bitWordEquivFin n)).symm
    ((finSumTwoPow n).symm (finSumTwoPow n (Sum.inl i)))) = _
  simp [bitWordSplitEquiv]

@[simp] theorem bitWordEquivFin_symm_finSumTwoPow_inr (n : ℕ) (i : Fin (2 ^ n)) :
    (bitWordEquivFin (n + 1)).symm (finSumTwoPow n (Sum.inr i)) =
      extendSucc n ((bitWordEquivFin n).symm i) true := by
  change (bitWordSplitEquiv n).symm ((Equiv.sumCongr (bitWordEquivFin n) (bitWordEquivFin n)).symm
    ((finSumTwoPow n).symm (finSumTwoPow n (Sum.inr i)))) = _
  simp [bitWordSplitEquiv]

/-- Embed the diagonal Cantor-cylinder algebra `DiagAlg n` into `UHFStage n = M_{2^n}(ℂ)`. -/
def diagToUHFStage (n : ℕ) (f : DiagAlg n) : UHFStage n :=
  Matrix.diagonal (fun i => f ((bitWordEquivFin n).symm i))

theorem diagToUHFStage_one (n : ℕ) :
    diagToUHFStage n 1 = (1 : UHFStage n) := by
  ext i j
  by_cases h : i = j <;> simp [diagToUHFStage, Matrix.one_apply, h]

theorem diagToUHFStage_add (n : ℕ) (f g : DiagAlg n) :
    diagToUHFStage n (f + g) = diagToUHFStage n f + diagToUHFStage n g := by
  ext i j
  by_cases h : i = j <;> simp [diagToUHFStage, h]

theorem diagToUHFStage_mul (n : ℕ) (f g : DiagAlg n) :
    diagToUHFStage n (f * g) = diagToUHFStage n f * diagToUHFStage n g := by
  unfold diagToUHFStage
  rw [Matrix.diagonal_mul_diagonal]
  rfl

theorem diagToUHFStage_injective (n : ℕ) :
    Function.Injective (diagToUHFStage n) := by
  intro f g hfg
  ext w
  have hii := congrArg (fun M : UHFStage n => M (bitWordEquivFin n w) (bitWordEquivFin n w)) hfg
  simpa [diagToUHFStage, Matrix.diagonal_apply] using hii

/-- Exact algebraic soldering of block reindexing at UHF stage `n + 1` via `AlgebraicSoldering`. -/
def uhfBlockMatrixSoldering (n : ℕ) :
    InfoGeometry.Canonical.AlgebraicSoldering ℂ
      (Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℂ)
      (UHFStage (n + 1)) where
  equiv := (Matrix.reindexAlgEquiv ℂ ℂ (finSumTwoPow n)).toLinearEquiv
  sourceMul := (· * ·)
  targetMul := (· * ·)
  map_mul := fun A B => (Matrix.reindexAlgEquiv ℂ ℂ (finSumTwoPow n)).map_mul A B

/-- **Exact Diagonal MASA Intertwiner**: `diagToUHFStage` intertwines the Cantor cylinder
embedding `diagEmbedSucc n` with the UHF block-doubling step `uhfStep n`. -/
theorem diagToUHFStage_intertwines_step (n : ℕ) (f : DiagAlg n) :
    diagToUHFStage (n + 1) (diagEmbedSucc n f) = uhfStep n (diagToUHFStage n f) := by
  apply (Matrix.reindexAlgEquiv ℂ ℂ (finSumTwoPow n)).symm.injective
  rw [uhfStep, (Matrix.reindexAlgEquiv ℂ ℂ (finSumTwoPow n)).symm_apply_apply]
  ext s₁ s₂
  rcases s₁ with i | i <;> rcases s₂ with j | j
  · change Matrix.diagonal (fun k => diagEmbedSucc n f ((bitWordEquivFin (n + 1)).symm k))
        (finSumTwoPow n (Sum.inl i)) (finSumTwoPow n (Sum.inl j)) =
      (fromBlocks (diagToUHFStage n f) 0 0 (diagToUHFStage n f)) (Sum.inl i) (Sum.inl j)
    have heq : (finSumTwoPow n (Sum.inl i) = finSumTwoPow n (Sum.inl j)) ↔ i = j := by
      constructor
      · intro h
        have hs := (finSumTwoPow n).injective h
        exact Sum.inl.inj hs
      · intro h; rw [h]
    by_cases hij : i = j
    · subst hij
      simp [diagToUHFStage, diagEmbedSucc, prefixSucc_extendSucc]
    · simp [diagToUHFStage, heq, hij]
  · change Matrix.diagonal (fun k => diagEmbedSucc n f ((bitWordEquivFin (n + 1)).symm k))
        (finSumTwoPow n (Sum.inl i)) (finSumTwoPow n (Sum.inr j)) =
      (fromBlocks (diagToUHFStage n f) 0 0 (diagToUHFStage n f)) (Sum.inl i) (Sum.inr j)
    have hne : finSumTwoPow n (Sum.inl i) ≠ finSumTwoPow n (Sum.inr j) := by
      intro h
      have hs := (finSumTwoPow n).injective h
      cases hs
    simp [hne]
  · change Matrix.diagonal (fun k => diagEmbedSucc n f ((bitWordEquivFin (n + 1)).symm k))
        (finSumTwoPow n (Sum.inr i)) (finSumTwoPow n (Sum.inl j)) =
      (fromBlocks (diagToUHFStage n f) 0 0 (diagToUHFStage n f)) (Sum.inr i) (Sum.inl j)
    have hne : finSumTwoPow n (Sum.inr i) ≠ finSumTwoPow n (Sum.inl j) := by
      intro h
      have hs := (finSumTwoPow n).injective h
      cases hs
    simp [hne]
  · change Matrix.diagonal (fun k => diagEmbedSucc n f ((bitWordEquivFin (n + 1)).symm k))
        (finSumTwoPow n (Sum.inr i)) (finSumTwoPow n (Sum.inr j)) =
      (fromBlocks (diagToUHFStage n f) 0 0 (diagToUHFStage n f)) (Sum.inr i) (Sum.inr j)
    have heq : (finSumTwoPow n (Sum.inr i) = finSumTwoPow n (Sum.inr j)) ↔ i = j := by
      constructor
      · intro h
        have hs := (finSumTwoPow n).injective h
        exact Sum.inr.inj hs
      · intro h; rw [h]
    by_cases hij : i = j
    · subst hij
      simp [diagToUHFStage, diagEmbedSucc, prefixSucc_extendSucc]
    · simp [diagToUHFStage, heq, hij]

theorem toUHF_diagToUHFStage_compat (n : ℕ) (f : DiagAlg n) :
    toUHF (n + 1) (diagToUHFStage (n + 1) (diagEmbedSucc n f)) =
      toUHF n (diagToUHFStage n f) := by
  rw [diagToUHFStage_intertwines_step, toUHF_uhfStep]

theorem uhfTracialState_diagToUHFStage (n : ℕ) (f : DiagAlg n) :
    uhfTracialState n (diagToUHFStage n f) =
      (1 / (2 : ℂ) ^ n) * ∑ w : BitWord n, f w := by
  unfold uhfTracialState diagToUHFStage
  rw [matrixTraceState_apply, Matrix.trace_diagonal]
  congr 1
  exact Equiv.sum_comp (bitWordEquivFin n).symm f

/-- Canonical null-volume projector inside `UHFAlg`, lifting `stageOneProj0 = diag(1, 0)`. -/
def uhfNullVolProj : UHFAlg := toUHF 1 stageOneProj0

private lemma fin2Pow1_cases (i : Fin (2 ^ 1)) : i = 0 ∨ i = 1 := by
  rcases i with ⟨k, hk⟩
  have hk2 : k < 2 := by simpa using hk
  rcases k with _ | _ | k
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

private lemma bitWord1_zero : (bitWordEquivFin 1).symm 0 0 = false := by
  have hz : (0 : Fin (2 ^ 1)) = finSumTwoPow 0 (Sum.inl 0) := by decide
  rw [hz, bitWordEquivFin_symm_finSumTwoPow_inl]
  simp [extendSucc]

private lemma bitWord1_one : (bitWordEquivFin 1).symm 1 0 = true := by
  have ho : (1 : Fin (2 ^ 1)) = finSumTwoPow 0 (Sum.inr 0) := by decide
  rw [ho, bitWordEquivFin_symm_finSumTwoPow_inr]
  simp [extendSucc]

/-- Every finite-stage diagonal projection `stageProj0 n` equals the embedded Cantor
first-bit indicator `w ↦ if w 0 then 0 else 1`. -/
theorem stageProj0_eq_diagToUHFStage (n : ℕ) :
    stageProj0 n = diagToUHFStage (n + 1) (fun w : BitWord (n + 1) => if w 0 then 0 else 1) := by
  induction n with
  | zero =>
    change stageOneProj0 =
      Matrix.diagonal (fun i : Fin (2 ^ 1) =>
        if (bitWordEquivFin 1).symm i 0 then (0 : ℂ) else 1)
    ext i j
    rcases fin2Pow1_cases i with rfl | rfl <;> rcases fin2Pow1_cases j with rfl | rfl
    · simp only [stageOneProj0, Matrix.diagonal_apply, ite_true, Matrix.of_apply,
        Matrix.cons_val_zero]
      rw [bitWord1_zero]
      simp
    · simp [stageOneProj0]
    · simp [stageOneProj0]
    · simp only [stageOneProj0, Matrix.diagonal_apply, ite_true, Matrix.of_apply,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [bitWord1_one]
      simp
  | succ n ih =>
    change uhfStep (n + 1) (stageProj0 n) = _
    rw [ih, ← diagToUHFStage_intertwines_step]
    rfl

theorem toUHF_stageProj0 (n : ℕ) :
    toUHF (n + 1) (stageProj0 n) = uhfNullVolProj := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change toUHF (n + 2) (uhfStep (n + 1) (stageProj0 n)) = uhfNullVolProj
    rw [toUHF_uhfStep, ih]

theorem uhfNullVolProj_idempotent :
    uhfNullVolProj * uhfNullVolProj = uhfNullVolProj := by
  unfold uhfNullVolProj
  rw [mul_toUHF]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stageOneProj0, Matrix.mul_apply, Fin.sum_univ_two]

theorem uhfNullVolProj_star : star uhfNullVolProj = uhfNullVolProj := by
  unfold uhfNullVolProj
  rw [star_toUHF]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stageOneProj0, Matrix.star_apply]

theorem uhfNullVolProj_trace : uhfColimitTrace uhfNullVolProj = 1 / 2 := by
  unfold uhfNullVolProj
  rw [uhfColimitTrace_toUHF, uhfTracialState, matrixTraceState_apply]
  have htr : Matrix.trace stageOneProj0 = 1 := by
    simp [stageOneProj0, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  rw [htr]
  norm_num

/-- **Represented Null-Volume State on the Jaynesian UHF Inductive Colimit**:
compresses the faithful normalized colimit trace `uhfColimitTrace` by the null-volume
Witt/Cantor projector `uhfNullVolProj`. -/
def nullVolumeUHFState (x : UHFAlg) : ℂ :=
  2 * uhfColimitTrace (uhfNullVolProj * x * uhfNullVolProj)

theorem nullVolumeUHFState_one : nullVolumeUHFState (1 : UHFAlg) = 1 := by
  unfold nullVolumeUHFState
  rw [mul_one, uhfNullVolProj_idempotent, uhfNullVolProj_trace]
  norm_num

theorem nullVolumeUHFState_add (x y : UHFAlg) :
    nullVolumeUHFState (x + y) = nullVolumeUHFState x + nullVolumeUHFState y := by
  unfold nullVolumeUHFState
  rw [mul_add, add_mul, uhfColimitTrace_add, mul_add]

theorem nullVolumeUHFState_nonneg (x : UHFAlg) :
    0 ≤ (nullVolumeUHFState (star x * x)).re := by
  unfold nullVolumeUHFState
  have hfactor :
      uhfNullVolProj * (star x * x) * uhfNullVolProj =
        star (x * uhfNullVolProj) * (x * uhfNullVolProj) := by
    rw [star_mul, uhfNullVolProj_star]
    simp only [mul_assoc]
  rw [hfactor]
  have htwo : ((2 : ℂ) * uhfColimitTrace (star (x * uhfNullVolProj) * (x * uhfNullVolProj))).re =
      2 * (uhfColimitTrace (star (x * uhfNullVolProj) * (x * uhfNullVolProj))).re := by
    simp [Complex.mul_re]
  rw [htwo]
  exact mul_nonneg (by norm_num) (uhfColimitTrace_nonneg (x * uhfNullVolProj))

theorem nullVolumeUHFState_proj : nullVolumeUHFState uhfNullVolProj = 1 := by
  unfold nullVolumeUHFState
  rw [uhfNullVolProj_idempotent, uhfNullVolProj_idempotent, uhfNullVolProj_trace]
  norm_num

theorem nullVolumeUHFState_compl_proj : nullVolumeUHFState (1 - uhfNullVolProj) = 0 := by
  unfold nullVolumeUHFState
  have hzero : uhfNullVolProj * (1 - uhfNullVolProj) * uhfNullVolProj = 0 := by
    rw [mul_sub, mul_one, uhfNullVolProj_idempotent, sub_self, zero_mul]
  rw [hzero]
  change (2 : ℂ) * uhfColimitTrace (toUHF 0 0) = 0
  rw [uhfColimitTrace_toUHF]
  unfold uhfTracialState
  rw [matrixTraceState_apply, Matrix.trace_zero]
  simp

theorem nullVolumeUHFState_dirac_zero : nullVolumeUHFState uhfColimitDirac = 0 := by
  unfold nullVolumeUHFState uhfNullVolProj uhfColimitDirac
  rw [mul_toUHF, mul_toUHF, uhfColimitTrace_toUHF]
  have hzero : stageOneProj0 * InfoGeometry.Canonical.Cl11DiracGeneratorCore.diracGenerator *
      stageOneProj0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stageOneProj0, InfoGeometry.Canonical.Cl11DiracGeneratorCore.diracGenerator,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [hzero]
  unfold uhfTracialState
  rw [matrixTraceState_apply, Matrix.trace_zero]
  simp

/-- Pullback of `nullVolumeUHFState` along `diagToUHFStage` to finite Cantor cylinder
observables `DiagAlg (n + 1)`. -/
def nullVolumeCylinderState (n : ℕ) (f : DiagAlg (n + 1)) : ℂ :=
  nullVolumeUHFState (toUHF (n + 1) (diagToUHFStage (n + 1) f))

/-- Cylinder observables yield a compatible state family across `diagEmbedSucc`. -/
theorem nullVolumeCylinderState_compat (n : ℕ) (f : DiagAlg (n + 1)) :
    nullVolumeCylinderState (n + 1) (diagEmbedSucc (n + 1) f) = nullVolumeCylinderState n f := by
  unfold nullVolumeCylinderState
  rw [toUHF_diagToUHFStage_compat]

theorem nullVolumeCylinderState_one (n : ℕ) :
    nullVolumeCylinderState n 1 = 1 := by
  unfold nullVolumeCylinderState
  rw [diagToUHFStage_one, toUHF_one, nullVolumeUHFState_one]

theorem nullVolumeCylinderState_stageOne (f : DiagAlg 1) :
    nullVolumeCylinderState 0 f = f (fun _ => false) := by
  unfold nullVolumeCylinderState nullVolumeUHFState uhfNullVolProj
  rw [mul_toUHF, mul_toUHF, uhfColimitTrace_toUHF, uhfTracialState, matrixTraceState_apply]
  have hmat :
      stageOneProj0 * diagToUHFStage 1 f * stageOneProj0 =
        !![f ((bitWordEquivFin 1).symm 0), 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stageOneProj0, diagToUHFStage, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hw0 : (bitWordEquivFin 1).symm 0 = (fun _ : Fin 1 => false) := by
    have hz : (0 : Fin (2 ^ 1)) = finSumTwoPow 0 (Sum.inl 0) := by decide
    rw [hz, bitWordEquivFin_symm_finSumTwoPow_inl]
    ext i
    have hi0 : i = 0 := by
      have hilt : i.1 < 1 := i.isLt
      exact Fin.ext (by omega)
    subst hi0
    simp [extendSucc]
  rw [hmat, hw0]
  have htr : Matrix.trace !![f (fun _ => false), (0 : ℂ); 0, 0] = f (fun _ => false) := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  rw [htr]
  norm_num
  ring

theorem nullVolumeCylinderState_false_indicator (n : ℕ) :
    nullVolumeCylinderState n (fun w : BitWord (n + 1) => if w 0 then 0 else 1) = 1 := by
  unfold nullVolumeCylinderState
  rw [← stageProj0_eq_diagToUHFStage, toUHF_stageProj0, nullVolumeUHFState_proj]

theorem nullVolumeCylinderState_true_indicator (n : ℕ) :
    nullVolumeCylinderState n (fun w : BitWord (n + 1) => if w 0 then 1 else 0) = 0 := by
  have hcomp :
      (fun w : BitWord (n + 1) => if w 0 then (1 : ℂ) else 0) =
        1 - (fun w : BitWord (n + 1) => if w 0 then 0 else 1) := by
    ext w
    cases hw : w 0 <;> simp [hw]
  unfold nullVolumeCylinderState
  rw [hcomp]
  have hsub :
      diagToUHFStage (n + 1) (1 - fun w : BitWord (n + 1) => if w 0 then 0 else 1) =
        1 - diagToUHFStage (n + 1) (fun w : BitWord (n + 1) => if w 0 then 0 else 1) := by
    ext i j
    by_cases h : i = j <;> simp [diagToUHFStage, h]
  rw [hsub]
  have htoSub :
      toUHF (n + 1) (1 - diagToUHFStage (n + 1) (fun w : BitWord (n + 1) => if w 0 then 0 else 1)) =
        (1 : UHFAlg) - uhfNullVolProj := by
    rw [sub_eq_add_neg, ← add_toUHF, toUHF_one, ← neg_toUHF, ← stageProj0_eq_diagToUHFStage,
      toUHF_stageProj0, sub_eq_add_neg]
  rw [htoSub, nullVolumeUHFState_compl_proj]

/-!
## 5. Master Jaynesian Null-Volume Boundary State Synthesis
-/

/-- **Master Jaynesian Synthesis**: connects by explicit maps, algebraic soldering, and
operator intertwiners (with zero `H_lp` / Cauchy completion):
1. `Cl(5,5)` Witt null-volume projector `ι(∞)ι(0) = infinityProjector55` & affine gauge `u + v` readout;
2. Zorn soldering (`zornCellMatrixEquiv` multiplication & null-pair CAR), `Cl(5,5) → Exterior3 → Zorn`
   CAR intertwiners, and Zorn vacuum state;
3. Cantor bit-word soldering into `ZornCell ℝ` and the UHF diagonal MASA (`diagToUHFStage`, `stageProj0`);
4. Jaynesian `RealBlockColimit 2` sewn `Cl(1,1)` algebra, non-commutativity, and anomaly cancellation;
5. Positive unital null-volume represented state on `UHFAlg` & compatible cylinder pullback;
6. `Pin(5,5)` Bisognano–Wichmann Krein isometry & Unruh wedge KMS law in `RealBlockColimit 10`. -/
theorem jaynesian_null_volume_boundary_state_synthesis :
    (bitCl55Null false * bitCl55Null true = infinityProjector55 ∧
      ∀ X : PACSplit55,
        bitCl55Null false * ι55 (pacSplit55ToV55 X) +
          ι55 (pacSplit55ToV55 X) * bitCl55Null false = algebraMap ℝ Cl55 (affineGaugeCoord X)) ∧
    ((∀ X Y : ZornCell ℝ, zornCellToMatrix (X * Y) = zornCellToMatrix X * zornCellToMatrix Y) ∧
      (∀ (i : Fin 3) (ψ : Exterior3),
        fockToZorn (projectColorExterior
          (cl55VacuumIdealSpinorEquiv
            (cl55VacuumIdealLeftAction
              (annihilation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ)))) =
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i (fockToZorn ψ)) ∧
      zornVacuumState vacuumProjector = 1) ∧
    ((∀ (n : ℕ) (w : BitWord n) (b : Bool),
        addressNullGenerator (bitWordToBinaryWord (extendSucc n w b)) = bitNullGenerator b) ∧
      (∀ (n : ℕ) (f : DiagAlg n),
        diagToUHFStage (n + 1) (diagEmbedSucc n f) = uhfStep n (diagToUHFStage n f)) ∧
      (∀ n : ℕ, toUHF (n + 1) (stageProj0 n) = uhfNullVolProj)) ∧
    (colimitSewnJ * colimitSewnEps ≠ colimitSewnEps * colimitSewnJ ∧
      colimitSewnVacuum ≠ 0 ∧
      ∀ B : RealBlockColimit 2, colimitSewnJ * B * colimitSewnJ = B →
        colimitHSInner colimitSewnVacuum (colimitSewnEps * (B * colimitSewnVacuum)) = 0) ∧
    (nullVolumeUHFState 1 = 1 ∧
      (∀ x : UHFAlg, 0 ≤ (nullVolumeUHFState (star x * x)).re) ∧
      nullVolumeUHFState uhfColimitDirac = 0 ∧
      (∀ (n : ℕ) (f : DiagAlg (n + 1)),
        nullVolumeCylinderState (n + 1) (diagEmbedSucc (n + 1) f) = nullVolumeCylinderState n f) ∧
      (∀ f : DiagAlg 1, nullVolumeCylinderState 0 f = f (fun _ => false))) ∧
    ((∀ η : ℝ, star (colimitPin55Boost η) * colimitJ55 * colimitPin55Boost η = colimitJ55) ∧
      (∀ (a : ℝ), a > 0 → ∀ (x y : RealBlockColimit 10),
        colimitState (rindlerThermalDensity (1 / unruhTemperature a))
            (x * colimitWedgeBoostFlow (1 / a) y) =
          colimitState (rindlerThermalDensity (1 / unruhTemperature a)) (y * x))) := by
  refine ⟨⟨bitCl55Null_nullVolumeProjector, bitCl55Null_affineGauge_readout⟩,
    ⟨zornCellToMatrix_mul, cl55_color_creation_intertwines_zorn, zornVacuumState_vacuumProjector⟩,
    ⟨addressNullGenerator_extendSucc, diagToUHFStage_intertwines_step, toUHF_stageProj0⟩,
    ⟨colimitSewnJ_eps_noncomm, colimitSewnVacuum_ne_zero, colimitSewnVacuum_chiral_zero⟩,
    ⟨nullVolumeUHFState_one, nullVolumeUHFState_nonneg, nullVolumeUHFState_dirac_zero,
      nullVolumeCylinderState_compat, nullVolumeCylinderState_stageOne⟩,
    ⟨colimitPin55Boost_krein_isometry, colimit_wedge_kms_condition⟩⟩

end InfoGeometry.Canonical.NullVolumeBoundaryState

end
