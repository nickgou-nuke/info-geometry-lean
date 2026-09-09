import InfoGeometry.Physics.CircularOperatorFourPotentialRotorReadout
import InfoGeometry.Physics.OperatorFourVectorZornReadout
import InfoGeometry.Physics.NuclearOperatorZornSuperSolovievBridge
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition
import InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.NoetherModularFlow
import InfoGeometry.Algebra.ChiralDoubledRealBlock
import InfoGeometry.Canonical.SolovievCircularInformationMetriplecticBridge
import InfoGeometry.Optics.OperatorLiftCarrier

/-!
# Operator four-potentials and the five-grade operator lane

This file is a bridge only.  The four-potential, the transported operator-Zorn
matrix algebra, the Clifford parity, the Peirce five-grade projectors, and the
canonical Zorn derivation lane remain owned by their respective modules.

The bridge records the compatible statements which can be proved without
adding a bosonisation, a Killing hypothesis, or a non-associative commutator
claim.  In particular, `OperatorZornMatrix` is the associative transported
operator carrier; the genuine split-octonion derivations act on it through the
existing adjoint derivation lane.
-/

namespace InfoGeometry.Canonical.OperatorFourPotentialFiveGradeBridge

open InfoGeometry.Physics
open InfoGeometry.Physics.CircularOperatorFourPotentialRotorReadout
open InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
open InfoGeometry.Physics.CircularChiralFockScalarPoleBridge
open InfoGeometry.Physics.OperatorFourVectorZornReadout
open InfoGeometry.Physics.OperatorZornMatrix
open InfoGeometry.Physics.NuclearOperatorZornSuperSolovievBridge
open InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms
open InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
open InfoGeometry.OperatorAlgebra.DerivationVectorCalculus
open InfoGeometry.Physics.Algebra
open InfoGeometry.Canonical.SolovievCircularInformationMetriplecticBridge

noncomputable section

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5
abbrev OperatorZornPotential := OperatorZornMatrix FockOp

abbrev ApolloniusParameterSpace := Fin 2 → ℝ

def nuclearOperatorMatrix (M : OperatorZornPotential) :
    InfoGeometry.Optics.OperatorLiftCarrier.OperatorMatrix
      (R := ℝ) (W := FockOp) :=
  fun i j => Algebra.lmul ℝ FockOp (toMatrix M i j)

@[simp] theorem lmul_comp_lmul (a b : FockOp) :
    (Algebra.lmul ℝ FockOp a).comp
        (Algebra.lmul ℝ FockOp b) =
      Algebra.lmul ℝ FockOp (a * b) := by
  apply LinearMap.ext
  intro x
  simp [Algebra.lmul, mul_assoc]

def nuclearSoldering (M : OperatorZornPotential) :
    Module.End ℝ (Fin 2 → FockOp) :=
  InfoGeometry.Optics.OperatorLiftCarrier.matrixActionAlgEquiv
    (nuclearOperatorMatrix M)

@[simp] theorem nuclearSoldering_apply
    (M : OperatorZornPotential) (ψ : Fin 2 → FockOp) (i : Fin 2) :
    nuclearSoldering M ψ i =
      toMatrix M i 0 * ψ 0 + toMatrix M i 1 * ψ 1 := by
  simp [nuclearSoldering, nuclearOperatorMatrix,
    InfoGeometry.Optics.OperatorLiftCarrier.matrixAction_apply,
    Fin.sum_univ_two, Algebra.lmul]

theorem nuclearSoldering_add
    (M N : OperatorZornPotential) (ψ : Fin 2 → FockOp) (i : Fin 2) :
    nuclearSoldering (M + N) ψ i =
      nuclearSoldering M ψ i + nuclearSoldering N ψ i := by
  rw [nuclearSoldering_apply, nuclearSoldering_apply, nuclearSoldering_apply]
  rw [toMatrix_add]
  simp only [Matrix.add_apply]
  noncomm_ring

@[simp] theorem nuclearSoldering_zero
    (ψ : Fin 2 → FockOp) (i : Fin 2) :
    nuclearSoldering 0 ψ i = 0 := by
  rw [nuclearSoldering_apply]
  simp

theorem nuclearSoldering_state_add
    (M : OperatorZornPotential) (ψ φ : Fin 2 → FockOp) (i : Fin 2) :
    nuclearSoldering M (ψ + φ) i =
      nuclearSoldering M ψ i + nuclearSoldering M φ i := by
  rw [nuclearSoldering_apply, nuclearSoldering_apply, nuclearSoldering_apply]
  simp only [Pi.add_apply, mul_add]
  abel

/-! ## Soloviev coordinate injection into the existing operator-Zorn carrier -/

def solovievCausalOperatorFourVector
    (eQ eP coupling : ℝ) (K : FockOp) : Fin 4 → FockOp :=
  fun i =>
    (solovievCausalParameters eQ eP coupling i) • K

@[simp] theorem solovievCausalOperatorFourVector_apply
    (eQ eP coupling : ℝ) (K : FockOp) (i : Fin 4) :
    solovievCausalOperatorFourVector eQ eP coupling K i =
      (solovievCausalParameters eQ eP coupling i) • K :=
  rfl

def solovievCausalZornPotential
    (eQ eP coupling : ℝ) (K : FockOp) : OperatorZornPotential :=
  fromCoordinates (solovievCausalOperatorFourVector eQ eP coupling K)

/-! ## Hestenes--Krein/Nambu carrier interface

The doubled real carrier is the existing Nambu--Gorkov realization.  The
following equivalence is the canonical mathlib identification of a two-slot
Nambu spinor with a product carrier; it introduces no new algebraic
identification with the QGT or matrix-stage carriers.
-/

def nambuCoordinateEquiv {H : Type*} [AddCommMonoid H] [Module ℝ H] :
    (Fin 2 → H) ≃ₗ[ℝ] InfoGeometry.Algebra.DoubledRealCarrier H :=
  LinearEquiv.finTwoArrow ℝ H

@[simp] theorem nambuCoordinateEquiv_apply
    {H : Type*} [AddCommMonoid H] [Module ℝ H]
    (x : Fin 2 → H) :
    nambuCoordinateEquiv x = (x 0, x 1) :=
  rfl

@[simp] theorem nambuCoordinateEquiv_symm_apply
    {H : Type*} [AddCommMonoid H] [Module ℝ H]
    (x : InfoGeometry.Algebra.DoubledRealCarrier H) :
    (nambuCoordinateEquiv (H := H)).symm x = ![x.1, x.2] :=
  by
    funext i
    fin_cases i <;> rfl

/-! ## Equivariant transport interface -/

def transportOperatorFourVector
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : FockOp ≃ₗ[ℝ] W) (v : Fin 4 → FockOp) : Fin 4 → W :=
  fun i => e (v i)

@[simp] theorem transportOperatorFourVector_apply
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : FockOp ≃ₗ[ℝ] W) (v : Fin 4 → FockOp) (i : Fin 4) :
    transportOperatorFourVector e v i = e (v i) :=
  rfl

theorem transportOperatorFourVector_add
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : FockOp ≃ₗ[ℝ] W) (v w : Fin 4 → FockOp) :
    transportOperatorFourVector e (v + w) =
      transportOperatorFourVector e v + transportOperatorFourVector e w := by
  funext i
  simp [transportOperatorFourVector]

/-! ## Four-vector soldering -/

def operatorFourPotential (i : Fin 3) : RealOperatorFourPotential :=
  circularCompressedFourPotential i

def operatorZornFourPotential (i : Fin 3) : OperatorZornPotential :=
  fromCoordinates (operatorFourPotential i)

/-! ## Explicit Apollonius-to-operator encoding

The repository does not determine a unique physical encoding of the two
Apollonius coordinates into four operator components.  This definition makes
the chosen finite encoding explicit: the two coordinates act by left scalar
multiplication on `K`, and the remaining components are zero. -/

def apolloniusOperatorFourVector
    (u : ApolloniusParameterSpace) (K : FockOp) : Fin 4 → FockOp :=
  ![(u 0) • K, (u 1) • K, 0, 0]

@[simp] theorem apolloniusOperatorFourVector_zero
    (u : ApolloniusParameterSpace) (K : FockOp) :
    apolloniusOperatorFourVector u K 0 = (u 0) • K :=
  rfl

@[simp] theorem apolloniusOperatorFourVector_one
    (u : ApolloniusParameterSpace) (K : FockOp) :
    apolloniusOperatorFourVector u K 1 = (u 1) • K :=
  rfl

@[simp] theorem apolloniusOperatorFourVector_two
    (u : ApolloniusParameterSpace) (K : FockOp) :
    apolloniusOperatorFourVector u K 2 = 0 :=
  rfl

@[simp] theorem apolloniusOperatorFourVector_three
    (u : ApolloniusParameterSpace) (K : FockOp) :
    apolloniusOperatorFourVector u K 3 = 0 :=
  rfl

def apolloniusZornOperatorPotential
    (u : ApolloniusParameterSpace) (K : FockOp) : OperatorZornPotential :=
  fromCoordinates (apolloniusOperatorFourVector u K)

theorem apolloniusZornOperatorPotential_toMatrix
    (u : ApolloniusParameterSpace) (K : FockOp) :
    toMatrix (apolloniusZornOperatorPotential u K) =
      !![(u 0) • K, (u 1) • K;
         (u 1) • K, (u 0) • K] := by
  rw [apolloniusZornOperatorPotential, fromCoordinates_toMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [apolloniusOperatorFourVector]

/-! The parameter lift is bundled at the algebraic level.  This is the
canonical interface for later analytic differentiation: the lift is a
linear map before any choice of topology or normed structure is made. -/

def apolloniusOperatorFourVectorLinear (K : FockOp) :
    ApolloniusParameterSpace →ₗ[ℝ] (Fin 4 → FockOp) where
  toFun u := apolloniusOperatorFourVector u K
  map_add' u v := by
    funext i
    fin_cases i <;>
      simp [apolloniusOperatorFourVector, add_smul]
  map_smul' c u := by
    funext i
    fin_cases i <;>
      simp [apolloniusOperatorFourVector, mul_smul]

@[simp] theorem apolloniusOperatorFourVectorLinear_apply
    (K : FockOp) (u : ApolloniusParameterSpace) :
    apolloniusOperatorFourVectorLinear K u =
      apolloniusOperatorFourVector u K :=
  rfl

theorem apolloniusOperatorFourVector_add
    (u v : ApolloniusParameterSpace) (K : FockOp) :
    apolloniusOperatorFourVector (u + v) K =
      apolloniusOperatorFourVector u K +
        apolloniusOperatorFourVector v K := by
  exact (apolloniusOperatorFourVectorLinear K).map_add u v

theorem apolloniusOperatorFourVector_smul
    (c : ℝ) (u : ApolloniusParameterSpace) (K : FockOp) :
    apolloniusOperatorFourVector (c • u) K =
      c • apolloniusOperatorFourVector u K := by
  exact (apolloniusOperatorFourVectorLinear K).map_smul c u

/-! The nuclear operator readout is the same soldered Apollonius packet. -/

theorem nuclearSoldering_apollonius
    (u : ApolloniusParameterSpace) (K : FockOp)
    (ψ : Fin 2 → FockOp) :
    nuclearSoldering (apolloniusZornOperatorPotential u K) ψ 0 =
      (u 0 • K) * ψ 0 + (u 1 • K) * ψ 1 := by
  rw [nuclearSoldering_apply]
  rw [apolloniusZornOperatorPotential_toMatrix]
  simp

theorem nuclearSoldering_apollonius_dual_row
    (u : ApolloniusParameterSpace) (K : FockOp)
    (ψ : Fin 2 → FockOp) :
    nuclearSoldering (apolloniusZornOperatorPotential u K) ψ 1 =
      (u 1 • K) * ψ 0 + (u 0 • K) * ψ 1 := by
  rw [nuclearSoldering_apply]
  rw [apolloniusZornOperatorPotential_toMatrix]
  simp

theorem nuclearSoldering_apollonius_rows
    (u : ApolloniusParameterSpace) (K : FockOp)
    (ψ : Fin 2 → FockOp) :
    nuclearSoldering (apolloniusZornOperatorPotential u K) ψ =
      ![(u 0 • K) * ψ 0 + (u 1 • K) * ψ 1,
        (u 1 • K) * ψ 0 + (u 0 • K) * ψ 1] := by
  funext i
  fin_cases i
  · exact nuclearSoldering_apollonius u K ψ
  · exact nuclearSoldering_apollonius_dual_row u K ψ

theorem operatorZornFourPotential_eq_soldered (i : Fin 3) :
    operatorZornFourPotential i = circularColourOperatorZorn i := by
  apply (equivMatrix (A := FockOp)).injective
  change toMatrix (fromCoordinates (operatorFourPotential i)) =
    toMatrix (circularColourOperatorZorn i)
  rw [fromCoordinates_toMatrix]
  change realSplitFourSoldering (operatorFourPotential i) =
    toMatrix (circularColourOperatorZorn i)
  exact realSplitFourSoldering_eq_circularOperatorZorn i

/-! ## Even/odd operator decomposition -/

def operatorPotentialEven (M : OperatorZornPotential) : OperatorZornPotential :=
  ⟨M.n_plus_op, M.n_minus_op, 0, 0⟩

def operatorPotentialOdd (M : OperatorZornPotential) : OperatorZornPotential :=
  ⟨0, 0, M.sigma_plus_op, M.sigma_minus_op⟩

theorem operatorPotential_even_add_odd (M : OperatorZornPotential) :
    operatorPotentialEven M + operatorPotentialOdd M = M := by
  apply (equivMatrix (A := FockOp)).injective
  change toMatrix (operatorPotentialEven M + operatorPotentialOdd M) = toMatrix M
  rw [Equiv.add_def]
  simp [operatorPotentialEven, operatorPotentialOdd, toMatrix, ofMatrix]

theorem operatorZornFourPotential_even_odd_packet (i : Fin 3) :
    operatorPotentialEven (operatorZornFourPotential i) +
        operatorPotentialOdd (operatorZornFourPotential i) =
      operatorZornFourPotential i :=
  operatorPotential_even_add_odd _

theorem operatorPotentialEven_idempotent (M : OperatorZornPotential) :
    operatorPotentialEven (operatorPotentialEven M) = operatorPotentialEven M := by
  cases M
  rfl

theorem operatorPotentialOdd_idempotent (M : OperatorZornPotential) :
    operatorPotentialOdd (operatorPotentialOdd M) = operatorPotentialOdd M := by
  cases M
  rfl

theorem operatorPotential_even_odd_orthogonal (M : OperatorZornPotential) :
    operatorPotentialEven (operatorPotentialOdd M) = 0 ∧
      operatorPotentialOdd (operatorPotentialEven M) = 0 := by
  constructor <;> rfl

/-! ## Linear soldering of derivation actions

The four-potential is assembled componentwise from one seed operator.  The
following map is the canonical linear transport on that carrier; it does not
claim that an arbitrary linear map is a derivation of the operator algebra.
-/

def zornDerivationAction (D : FockOp →ₗ[ℝ] FockOp)
    (M : OperatorZornPotential) : OperatorZornPotential :=
  ⟨D M.n_plus_op, D M.n_minus_op, D M.sigma_plus_op, D M.sigma_minus_op⟩

theorem zornDerivationAction_apollonius
    (D : FockOp →ₗ[ℝ] FockOp) (u : ApolloniusParameterSpace) (K : FockOp) :
    zornDerivationAction D (apolloniusZornOperatorPotential u K) =
      apolloniusZornOperatorPotential u (D K) := by
  apply (equivMatrix (A := FockOp)).injective
  change toMatrix (zornDerivationAction D
      (apolloniusZornOperatorPotential u K)) =
    toMatrix (apolloniusZornOperatorPotential u (D K))
  simp [zornDerivationAction, apolloniusZornOperatorPotential,
    apolloniusOperatorFourVector, fromCoordinates, toMatrix, map_smul]

theorem operatorPotential_dirac_square_even (Delta : FockOp) :
    (operatorZornParity (A := FockOp)).IsEven
      (InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.diracOperator Delta) :=
  dirac_square_internal_even Delta

theorem operatorPotential_dirac_odd (Delta : FockOp) :
    (operatorZornParity (A := FockOp)).IsOdd
      (InfoGeometry.Physics.NCG.diracOperator Delta) :=
  dirac_internal_odd Delta

/-! ## Five-grade projection -/

theorem fiveGrade_recompose_operator (e x : FockOp) :
    fiveGradeRecomposeLinear e (fiveGradeDecomposeLinear e x) = x := by
  exact fiveGrade_recompose_decompose e x

/-! The owner API uses the nested product
`FiveGradeCoordinates e`, rather than a finite function of grades.  The Zorn
lift therefore keeps four independent coordinate decompositions. -/

abbrev ZornFiveGradeCoordinates (e : FockOp) :=
  FiveGradeCoordinates e × FiveGradeCoordinates e ×
    FiveGradeCoordinates e × FiveGradeCoordinates e

def fiveGradeDecomposeZorn (e : FockOp) (M : OperatorZornPotential) :
    ZornFiveGradeCoordinates e :=
  (fiveGradeDecomposeLinear e M.n_plus_op,
    fiveGradeDecomposeLinear e M.n_minus_op,
    fiveGradeDecomposeLinear e M.sigma_plus_op,
    fiveGradeDecomposeLinear e M.sigma_minus_op)

def fiveGradeRecomposeZorn (e : FockOp)
    (C : ZornFiveGradeCoordinates e) : OperatorZornPotential :=
  ⟨fiveGradeRecomposeLinear e C.1,
    fiveGradeRecomposeLinear e C.2.1,
    fiveGradeRecomposeLinear e C.2.2.1,
    fiveGradeRecomposeLinear e C.2.2.2⟩

theorem fiveGrade_recompose_zorn (e : FockOp) (M : OperatorZornPotential) :
    fiveGradeRecomposeZorn e (fiveGradeDecomposeZorn e M) = M := by
  cases M
  simp [fiveGradeRecomposeZorn, fiveGradeDecomposeZorn]

/-! ## Frechet differential of the operator carrier -/

theorem operatorCarrier_identity_frechet (X : FockOp) :
    HasFDerivAt (fun Y : FockOp => Y)
      (1 : FockOp →L[ℝ] FockOp) X :=
  hasFDerivAt_id X

end
end InfoGeometry.Canonical.OperatorFourPotentialFiveGradeBridge
