/-
InfoGeometry/Canonical/FirstQuantizedChiralConeBridge.lean

Finite first-quantized bridge for the Pauli/chiral layer.

This file deliberately separates the finite matrix block from the unbounded
`xp` operator.  A complex 2 x 2 matrix is only a Pauli representation block;
the primary Weyl/Jordan quantization layer is real-algebraic.  Elliptic
bivectors give rotations and square-positive bivectors give hyperbolic
boosts.  An unbounded self-adjoint realization requires a separate domain
owner.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.PosDef
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.OperatorAlgebra.OperatorChiralLightcone
import InfoGeometry.OperatorAlgebra.ChiralRealBivectorRotor
import InfoGeometry.OperatorAlgebra.CuntzTomitaQuadraticReadout

noncomputable section

namespace InfoGeometry.Canonical.FirstQuantizedChiralConeBridge

open Matrix
open scoped ComplexOrder
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.OperatorAlgebra

abbrev PauliBlock := Matrix (Fin 2) (Fin 2) ℂ

/-! ## 0. Soldering coordinates -/

/-- The soldering map into the Hermitian Pauli block. -/
def solderingMap (P : PauliParavector) : PauliBlock := P.pauliMatrix

@[simp] theorem solderingMap_det (P : PauliParavector) :
    Matrix.det (solderingMap P) = (P.minkowskiNormSq : ℂ) :=
  PauliParavector.det_pauliMatrix_eq_minkowskiNormSq P

@[simp] theorem solderingMap_trace (P : PauliParavector) :
    Matrix.trace (solderingMap P) = ((2 * P.energy : ℝ) : ℂ) :=
  PauliParavector.trace_pauliMatrix_eq_two_energy P

theorem solderingMap_isHermitian (P : PauliParavector) :
    (solderingMap P).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [solderingMap, PauliParavector.pauliMatrix, Matrix.conjTranspose,
      Complex.conj_I] <;> ring

/-! ## 1. Finite density matrices -/

/-- The unnormalized Gram matrix of a finite spinor block. -/
def gram (A : PauliBlock) : PauliBlock := Aᴴ * A

@[simp] theorem gram_isHermitian (A : PauliBlock) :
    (gram A).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_self A

theorem gram_posSemidef (A : PauliBlock) :
    (gram A).PosSemidef := by
  simpa [gram] using
    (Matrix.posSemidef_self_mul_conjTranspose Aᴴ)

theorem gram_eq_tomitaQuadratic_conjTranspose (A : PauliBlock) :
    gram A = InfoGeometry.OperatorAlgebra.tomitaQuadratic 0 Aᴴ := by
  rw [InfoGeometry.OperatorAlgebra.tomitaQuadratic_eq_observable_mul_conjTranspose]
  simp [gram]

theorem gram_trace_ne_zero_of_ne_zero
    {A : PauliBlock} (hA : A ≠ 0) :
    Matrix.trace (gram A) ≠ 0 := by
  intro htrace
  have hre := congrArg Complex.re htrace
  simp [gram, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two] at hre
  have hzero (z : ℂ) (hz :
      z.re * z.re + z.im * z.im = 0) : z = 0 := by
    apply Complex.ext <;> norm_num at * <;>
      nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]
  have h00 : A 0 0 = 0 := by
    apply hzero
    nlinarith [mul_self_nonneg (A 1 0).re, mul_self_nonneg (A 1 0).im,
      mul_self_nonneg (A 0 1).re, mul_self_nonneg (A 0 1).im,
      mul_self_nonneg (A 1 1).re, mul_self_nonneg (A 1 1).im]
  have h10 : A 1 0 = 0 := by
    apply hzero
    nlinarith [mul_self_nonneg (A 0 0).re, mul_self_nonneg (A 0 0).im,
      mul_self_nonneg (A 0 1).re, mul_self_nonneg (A 0 1).im,
      mul_self_nonneg (A 1 1).re, mul_self_nonneg (A 1 1).im]
  have h01 : A 0 1 = 0 := by
    apply hzero
    nlinarith [mul_self_nonneg (A 0 0).re, mul_self_nonneg (A 0 0).im,
      mul_self_nonneg (A 1 0).re, mul_self_nonneg (A 1 0).im,
      mul_self_nonneg (A 1 1).re, mul_self_nonneg (A 1 1).im]
  have h11 : A 1 1 = 0 := by
    apply hzero
    nlinarith [mul_self_nonneg (A 0 0).re, mul_self_nonneg (A 0 0).im,
      mul_self_nonneg (A 1 0).re, mul_self_nonneg (A 1 0).im,
      mul_self_nonneg (A 0 1).re, mul_self_nonneg (A 0 1).im]
  apply hA
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h01, h11]

/-- Trace normalization on a certified nonzero-trace domain. -/
def densityMatrix (A : PauliBlock) (hTrace : Matrix.trace (gram A) ≠ 0) : PauliBlock :=
  (Matrix.trace (gram A))⁻¹ • gram A

/-- Density constructor whose only input side condition is `A ≠ 0`. -/
def densityMatrixFromNonzero (A : PauliBlock) (hA : A ≠ 0) : PauliBlock :=
  densityMatrix A (gram_trace_ne_zero_of_ne_zero hA)

theorem densityMatrix_eq_normalizedTomitaQuadratic_conjTranspose
    (A : PauliBlock)
    (hTrace : Matrix.trace (gram A) ≠ 0) :
    densityMatrix A hTrace =
      InfoGeometry.OperatorAlgebra.normalizedTomitaQuadratic 0 Aᴴ
        (by
          simpa [gram_eq_tomitaQuadratic_conjTranspose A] using hTrace) := by
  change (Matrix.trace (gram A))⁻¹ • gram A =
    (Matrix.trace (InfoGeometry.OperatorAlgebra.tomitaQuadratic 0 Aᴴ))⁻¹ •
      InfoGeometry.OperatorAlgebra.tomitaQuadratic 0 Aᴴ
  rw [gram_eq_tomitaQuadratic_conjTranspose A]

theorem densityMatrix_posSemidef
    (A : PauliBlock)
    (hTrace : Matrix.trace (gram A) ≠ 0) :
    (densityMatrix A hTrace).PosSemidef := by
  rw [densityMatrix_eq_normalizedTomitaQuadratic_conjTranspose A hTrace]
  exact InfoGeometry.OperatorAlgebra.normalizedTomitaQuadratic_posSemidef_of_trace_ne_zero
    0 Aᴴ (by
      simpa [gram_eq_tomitaQuadratic_conjTranspose A] using hTrace)

/-- The right-Gram convention `A Aᴴ` used for density operators. -/
def rightGram (A : PauliBlock) : PauliBlock := A * Aᴴ

theorem gram_trace_eq_rightGram_trace (A : PauliBlock) :
    Matrix.trace (gram A) = Matrix.trace (rightGram A) := by
  unfold gram rightGram
  exact Matrix.trace_mul_comm _ _

theorem gram_trace_ne_zero_iff_rightGram_trace_ne_zero (A : PauliBlock) :
    Matrix.trace (gram A) ≠ 0 ↔ Matrix.trace (rightGram A) ≠ 0 := by
  rw [gram_trace_eq_rightGram_trace]

/-- Trace-normalized quadratic density operator in the `A Aᴴ` convention. -/
def densityMatrixOfOp
    (A : PauliBlock)
    (hTrace : Matrix.trace (rightGram A) ≠ 0) : PauliBlock :=
  (Matrix.trace (rightGram A))⁻¹ • rightGram A

theorem rightGram_trace_ne_zero_of_ne_zero
    {A : PauliBlock} (hA : A ≠ 0) :
    Matrix.trace (rightGram A) ≠ 0 := by
  intro hTrace
  apply gram_trace_ne_zero_of_ne_zero hA
  calc
    Matrix.trace (gram A) = Matrix.trace (Aᴴ * A) := rfl
    _ = Matrix.trace (A * Aᴴ) := Matrix.trace_mul_comm _ _
    _ = 0 := hTrace

/-- Right-Gram density constructor with the natural nonzero-block input. -/
def densityMatrixOfOpFromNonzero
    (A : PauliBlock) (hA : A ≠ 0) : PauliBlock :=
  densityMatrixOfOp A (rightGram_trace_ne_zero_of_ne_zero hA)

theorem rightGram_isHermitian (A : PauliBlock) :
    (rightGram A).IsHermitian := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    Matrix.isHermitian_conjTranspose_mul_self Aᴴ

theorem rightGram_posSemidef (A : PauliBlock) :
    (rightGram A).PosSemidef := by
  simpa [rightGram] using
    (Matrix.posSemidef_self_mul_conjTranspose A)

theorem rightGram_eq_tomitaQuadratic (A : PauliBlock) :
    rightGram A = InfoGeometry.OperatorAlgebra.tomitaQuadratic 0 A := by
  rw [InfoGeometry.OperatorAlgebra.tomitaQuadratic_eq_observable_mul_conjTranspose]
  rfl

theorem densityMatrixOfOp_eq_normalizedTomitaQuadratic
    (A : PauliBlock)
    (hTrace : Matrix.trace (rightGram A) ≠ 0) :
    densityMatrixOfOp A hTrace =
      InfoGeometry.OperatorAlgebra.normalizedTomitaQuadratic 0 A
        (by
          simpa [rightGram_eq_tomitaQuadratic A] using hTrace) := by
  change (Matrix.trace (rightGram A))⁻¹ • rightGram A =
    (Matrix.trace (InfoGeometry.OperatorAlgebra.tomitaQuadratic 0 A))⁻¹ •
      InfoGeometry.OperatorAlgebra.tomitaQuadratic 0 A
  rw [rightGram_eq_tomitaQuadratic A]

theorem densityMatrixOfOp_posSemidef
    (A : PauliBlock)
    (hTrace : Matrix.trace (rightGram A) ≠ 0) :
    (densityMatrixOfOp A hTrace).PosSemidef := by
  rw [densityMatrixOfOp_eq_normalizedTomitaQuadratic A hTrace]
  exact InfoGeometry.OperatorAlgebra.normalizedTomitaQuadratic_posSemidef_of_trace_ne_zero
    0 A (by
      simpa [rightGram_eq_tomitaQuadratic A] using hTrace)

theorem densityMatrixOfOp_isHermitian
    (A : PauliBlock)
    (hTrace : Matrix.trace (rightGram A) ≠ 0) :
    (densityMatrixOfOp A hTrace).IsHermitian := by
  unfold densityMatrixOfOp
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  rw [rightGram_isHermitian A]
  have hstar : star (Matrix.trace (rightGram A)) = Matrix.trace (rightGram A) := by
    calc
      star (Matrix.trace (rightGram A)) = Matrix.trace (rightGram A)ᴴ :=
        (Matrix.trace_conjTranspose (rightGram A)).symm
      _ = Matrix.trace (rightGram A) := by rw [rightGram_isHermitian A]
  simp [hstar]

theorem densityMatrixOfOp_trace
    (A : PauliBlock)
    (hTrace : Matrix.trace (rightGram A) ≠ 0) :
    Matrix.trace (densityMatrixOfOp A hTrace) = 1 := by
  unfold densityMatrixOfOp
  rw [Matrix.trace_smul]
  exact inv_mul_cancel₀ hTrace

theorem densityMatrixOfOpFromNonzero_trace
    (A : PauliBlock) (hA : A ≠ 0) :
    Matrix.trace (densityMatrixOfOpFromNonzero A hA) = 1 := by
  exact densityMatrixOfOp_trace A (rightGram_trace_ne_zero_of_ne_zero hA)

theorem densityMatrixOfOpFromNonzero_posSemidef
    (A : PauliBlock) (hA : A ≠ 0) :
    (densityMatrixOfOpFromNonzero A hA).PosSemidef := by
  exact densityMatrixOfOp_posSemidef A (rightGram_trace_ne_zero_of_ne_zero hA)

@[simp] theorem densityMatrix_isHermitian
    (A : PauliBlock) (hTrace : Matrix.trace (gram A) ≠ 0) :
    (densityMatrix A hTrace).IsHermitian := by
  unfold densityMatrix
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  rw [gram_isHermitian A]
  have hstar : star (Matrix.trace (gram A)) = Matrix.trace (gram A) := by
    calc
      star (Matrix.trace (gram A)) = Matrix.trace (gram A)ᴴ :=
        (Matrix.trace_conjTranspose (gram A)).symm
      _ = Matrix.trace (gram A) := by rw [gram_isHermitian A]
  simp [hstar]

@[simp] theorem densityMatrix_trace
    (A : PauliBlock) (hTrace : Matrix.trace (gram A) ≠ 0) :
    Matrix.trace (densityMatrix A hTrace) = 1 := by
  unfold densityMatrix
  rw [Matrix.trace_smul]
  exact inv_mul_cancel₀ hTrace

theorem densityMatrixFromNonzero_trace
    (A : PauliBlock) (hA : A ≠ 0) :
    Matrix.trace (densityMatrixFromNonzero A hA) = 1 := by
  exact densityMatrix_trace A (gram_trace_ne_zero_of_ne_zero hA)

theorem densityMatrixFromNonzero_isHermitian
    (A : PauliBlock) (hA : A ≠ 0) :
    (densityMatrixFromNonzero A hA).IsHermitian := by
  exact densityMatrix_isHermitian A (gram_trace_ne_zero_of_ne_zero hA)

theorem densityMatrixFromNonzero_posSemidef
    (A : PauliBlock) (hA : A ≠ 0) :
    (densityMatrixFromNonzero A hA).PosSemidef := by
  exact densityMatrix_posSemidef A (gram_trace_ne_zero_of_ne_zero hA)

/-- The Gram block is positive in the complex quadratic-form sense. -/
def ComplexPositive (M : PauliBlock) : Prop :=
  ∀ x : Fin 2 → ℂ, 0 ≤ (star x ⬝ᵥ (M *ᵥ x)).re

theorem gram_complexPositive (A : PauliBlock) : ComplexPositive (gram A) := by
  intro x
  change 0 ≤ (star x ⬝ᵥ ((Aᴴ * A) *ᵥ x)).re
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]
  calc
    0 ≤ ∑ i : Fin 2, ‖(A *ᵥ x) i‖ ^ 2 := by positivity
    _ = (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)).re := by
      simp only [Fin.sum_univ_two, dotProduct]
      rw [Complex.sq_norm, Complex.sq_norm]
      simp [Complex.normSq_apply]

/-! ## 2. Pauli/Bloch finite cone coordinates -/

/-- A real Bloch vector with its closed-unit-ball certificate. -/
structure BlochVector where
  r1 : ℝ
  r2 : ℝ
  r3 : ℝ
  norm_le_one : r1 ^ 2 + r2 ^ 2 + r3 ^ 2 ≤ 1

/-- The Pauli reconstruction of a Bloch vector. -/
def blochMatrix (b : BlochVector) : PauliBlock :=
  (1 / 2 : ℂ) • !![
    ((1 + b.r3 : ℝ) : ℂ), (b.r1 : ℂ) - Complex.I * (b.r2 : ℂ);
    (b.r1 : ℂ) + Complex.I * (b.r2 : ℂ), ((1 - b.r3 : ℝ) : ℂ)]

@[simp] theorem blochMatrix_trace (b : BlochVector) :
    Matrix.trace (blochMatrix b) = 1 := by
  simp [blochMatrix, Matrix.trace, Fin.sum_univ_two]
  ring

theorem blochMatrix_det (b : BlochVector) :
    Matrix.det (blochMatrix b) =
      ((1 - (b.r1 ^ 2 + b.r2 ^ 2 + b.r3 ^ 2)) / 4 : ℝ) := by
  simp [blochMatrix, Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem blochMatrix_det_nonneg (b : BlochVector) :
    0 ≤ Matrix.det (blochMatrix b) := by
  rw [blochMatrix_det]
  have hnonneg : 0 ≤ (1 - (b.r1 ^ 2 + b.r2 ^ 2 + b.r3 ^ 2)) / 4 := by
    nlinarith [b.norm_le_one]
  exact_mod_cast hnonneg

theorem blochMatrix_det_eq_zero_iff (b : BlochVector) :
    Matrix.det (blochMatrix b) = 0 ↔
      b.r1 ^ 2 + b.r2 ^ 2 + b.r3 ^ 2 = 1 := by
  rw [blochMatrix_det]
  constructor <;> intro h
  · have hr : (1 - (b.r1 ^ 2 + b.r2 ^ 2 + b.r3 ^ 2)) / 4 = 0 := by
      exact_mod_cast h
    nlinarith [hr]
  · rw [h]
    norm_num

theorem blochMatrix_isHermitian (b : BlochVector) :
    (blochMatrix b).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [blochMatrix, Matrix.conjTranspose, Complex.conj_I] <;> ring

/-! ## 2. Pauli cone and chiral-lightcone interface -/

theorem null_pauli_block_is_singular
    (P : PauliParavector)
    (hnull : P.minkowskiNormSq = 0) :
    Matrix.det P.pauliMatrix = 0 := by
  rw [PauliParavector.det_pauliMatrix_eq_minkowskiNormSq, hnull]
  simp

theorem pauli_block_readout_is_native
    (P : PauliParavector) (a : Fin 4) :
    PauliParavector.pauliCoefficientReadout a P.pauliMatrix =
      match a with
      | 0 => (P.energy : ℂ)
      | 1 => (P.px : ℂ)
      | 2 => (P.py : ℂ)
      | 3 => (P.pz : ℂ) :=
  PauliParavector.pauliCoefficientReadout_pauliMatrix P a

/-- A calibrated null spinor readout lands in the existing chiral cone owner.

The calibration is explicit: nullness alone does not choose a carrier-side
realization. -/
theorem calibrated_null_spinor_has_chiral_readout
    {Spinor Rotor Bivector Carrier Side : Type*}
    {LC : ChiralLightconeReadoutDatum Carrier Side}
    {D : HestenesSpinorRotorDatum Spinor Rotor Bivector}
    (B : PauliHestenesChiralLightconeBridge
      Spinor Rotor Bivector Carrier Side LC D)
    {ψ : Spinor}
    (hψ : (D.momentumReadout ψ).IsNull) :
    ∃ side : Side, B.carrierReadout ψ ∈ LC.Lightcone side :=
  PauliHestenesChiralLightconeBridge.chiral_lightcone_readout_of_null_momentum B hψ

/-! ## 3. Finite symmetric/antisymmetric operator lift -/

/-- Hermitian (symmetric) part of a finite matrix operator. -/
def hermitianPart (A : PauliBlock) : PauliBlock :=
  (2 : ℂ)⁻¹ • (A + Aᴴ)

/-- Skew-Hermitian (antisymmetric) part of a finite matrix operator. -/
def skewHermitianPart (A : PauliBlock) : PauliBlock :=
  (2 : ℂ)⁻¹ • (A - Aᴴ)

theorem hermitian_skewHermitian_decomposition (A : PauliBlock) :
    hermitianPart A + skewHermitianPart A = A := by
  unfold hermitianPart skewHermitianPart
  module

theorem hermitianPart_isHermitian (A : PauliBlock) :
    (hermitianPart A).IsHermitian := by
  unfold hermitianPart
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  norm_num
  module

theorem skewHermitianPart_conjTranspose (A : PauliBlock) :
    (skewHermitianPart A)ᴴ = -skewHermitianPart A := by
  unfold skewHermitianPart
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  norm_num
  module

/-- Finite matrix realization of the Weyl-ordered classical `xp` symbol. -/
def finiteXPGenerator (X P : PauliBlock) : PauliBlock :=
  (2 : ℂ)⁻¹ • (X * P + P * X)

/-- The ordered Lie/commutator channel complementary to `finiteXPGenerator`. -/
def finiteXPLiePart (X P : PauliBlock) : PauliBlock :=
  (2 : ℂ)⁻¹ • (X * P - P * X)

theorem finiteXP_product_split (X P : PauliBlock) :
    X * P = finiteXPGenerator X P + finiteXPLiePart X P := by
  unfold finiteXPGenerator finiteXPLiePart
  module

/-! ## 4. Spin transport as finite matrix conjugation -/

/-- Conjugation by a matrix unit is the finite spin transport. -/
def spinTransport (U : PauliBlockˣ) (A : PauliBlock) : PauliBlock :=
  (U : PauliBlock) * A * ((↑(U⁻¹) : PauliBlock))

theorem spinTransport_trace
    (U : PauliBlockˣ) (A : PauliBlock) :
    Matrix.trace (spinTransport U A) = Matrix.trace A := by
  unfold spinTransport
  exact Matrix.trace_units_conj U A

/-! ## 6. Real Weyl/Jordan quantization and Hestenes rotor lanes -/

namespace WeylOrderedXP

variable {A M : Type*}
variable [Field A] [CharZero A]
variable [AddCommGroup M] [Module A M]

/-- Algebraic canonical pair.  No boundedness or complex scalar is assumed. -/
structure CanonicalPair where
  X : Module.End A M
  P : Module.End A M
  center : A
  commutation :
    X * P - P * X = center • (LinearMap.id : Module.End A M)

namespace CanonicalPair

variable (C : CanonicalPair (A := A) (M := M))

/-- Jordan/Weyl channel of `XP`. -/
def symmetricPart (C : CanonicalPair (A := A) (M := M)) : Module.End A M :=
  (2 : A)⁻¹ • (C.X * C.P + C.P * C.X)

/-- Lie/commutator channel of `XP`. -/
def antisymmetricPart (C : CanonicalPair (A := A) (M := M)) : Module.End A M :=
  (2 : A)⁻¹ • (C.X * C.P - C.P * C.X)

theorem xp_eq_symmetric_add_antisymmetric :
    C.X * C.P = C.symmetricPart + C.antisymmetricPart := by
  unfold symmetricPart antisymmetricPart
  module

theorem antisymmetricPart_eq_central :
    C.antisymmetricPart =
      ((2 : A)⁻¹ * C.center) •
        (LinearMap.id : Module.End A M) := by
  unfold antisymmetricPart
  rw [C.commutation]
  module

theorem symmetricPart_eq_xp_sub_central :
    C.symmetricPart = C.X * C.P -
      ((2 : A)⁻¹ * C.center) •
        (LinearMap.id : Module.End A M) := by
  have h := C.xp_eq_symmetric_add_antisymmetric
  rw [C.antisymmetricPart_eq_central] at h
  exact eq_sub_of_add_eq' (by simpa [add_comm] using h.symm)

end CanonicalPair

/-! Real algebraic Hestenes planes and normalized rotor packets. -/

structure EllipticPlane (R : Type*) [Ring R] where
  B : R
  sq : B * B = -1

structure HyperbolicPlane (R : Type*) [Ring R] where
  K : R
  sq : K * K = 1

structure EllipticRotor (R : Type*) [Ring R] [Algebra ℝ R] where
  plane : EllipticPlane R
  c : ℝ
  s : ℝ
  normalization : c * c + s * s = 1
  rotor : R
  reverse : R
  rotor_eq : rotor = (c : ℝ) • (1 : R) + (s : ℝ) • plane.B
  reverse_eq : reverse = (c : ℝ) • (1 : R) - (s : ℝ) • plane.B

structure HyperbolicRotor (R : Type*) [Ring R] [Algebra ℝ R] where
  plane : HyperbolicPlane R
  a : ℝ
  b : ℝ
  normalization : a * a - b * b = 1
  rotor : R
  reverse : R
  rotor_eq : rotor = (a : ℝ) • (1 : R) + (b : ℝ) • plane.K
  reverse_eq : reverse = (a : ℝ) • (1 : R) - (b : ℝ) • plane.K

theorem ellipticRotor_mul_reverse
    {R : Type*} [Ring R] [Algebra ℝ R]
    (Q : EllipticRotor R) :
    Q.rotor * Q.reverse = 1 := by
  rw [Q.rotor_eq, Q.reverse_eq]
  simp only [Algebra.smul_def]
  have hB_c : Q.plane.B * algebraMap ℝ R Q.c =
      algebraMap ℝ R Q.c * Q.plane.B :=
    (Algebra.commutes Q.c Q.plane.B).symm
  have hB_s : Q.plane.B * algebraMap ℝ R Q.s =
      algebraMap ℝ R Q.s * Q.plane.B :=
    (Algebra.commutes Q.s Q.plane.B).symm
  have hsc : algebraMap ℝ R Q.s * algebraMap ℝ R Q.c =
      algebraMap ℝ R Q.c * algebraMap ℝ R Q.s :=
    by
      rw [← map_mul, ← map_mul, mul_comm]
  calc
    ((algebraMap ℝ R Q.c) * 1 + (algebraMap ℝ R Q.s) * Q.plane.B) *
        ((algebraMap ℝ R Q.c) * 1 - (algebraMap ℝ R Q.s) * Q.plane.B) =
      ((algebraMap ℝ R Q.c) * 1) * ((algebraMap ℝ R Q.c) * 1) +
        ((algebraMap ℝ R Q.s) * Q.plane.B) *
            ((algebraMap ℝ R Q.c) * 1) -
        (((algebraMap ℝ R Q.c) * 1) *
            ((algebraMap ℝ R Q.s) * Q.plane.B) +
          ((algebraMap ℝ R Q.s) * Q.plane.B) *
            ((algebraMap ℝ R Q.s) * Q.plane.B)) := by
            noncomm_ring
    _ = algebraMap ℝ R Q.c * algebraMap ℝ R Q.c -
        (algebraMap ℝ R Q.s * algebraMap ℝ R Q.s) *
          (Q.plane.B * Q.plane.B) := by
            simp only [one_mul, mul_one]
            have hcross :
                ((algebraMap ℝ R Q.s) * Q.plane.B) *
                    (algebraMap ℝ R Q.c) =
                  (algebraMap ℝ R Q.c) *
                    ((algebraMap ℝ R Q.s) * Q.plane.B) := by
              calc
                ((algebraMap ℝ R Q.s) * Q.plane.B) *
                    (algebraMap ℝ R Q.c) =
                  ((algebraMap ℝ R Q.s) *
                    (algebraMap ℝ R Q.c)) * Q.plane.B := by
                      calc
                        ((algebraMap ℝ R Q.s) * Q.plane.B) *
                            (algebraMap ℝ R Q.c) =
                          (algebraMap ℝ R Q.s) *
                            (Q.plane.B * algebraMap ℝ R Q.c) := by
                              simp only [mul_assoc]
                        _ = (algebraMap ℝ R Q.s) *
                            ((algebraMap ℝ R Q.c) * Q.plane.B) := by
                              rw [hB_c]
                        _ = ((algebraMap ℝ R Q.s) *
                            (algebraMap ℝ R Q.c)) * Q.plane.B := by
                              simp only [mul_assoc]
                _ = ((algebraMap ℝ R Q.c) *
                    (algebraMap ℝ R Q.s)) * Q.plane.B := by
                      rw [hsc]
                _ = (algebraMap ℝ R Q.c) *
                    ((algebraMap ℝ R Q.s) * Q.plane.B) := by
                      rw [← mul_assoc]
            have hquad :
                ((algebraMap ℝ R Q.s) * Q.plane.B) *
                    ((algebraMap ℝ R Q.s) * Q.plane.B) =
                  ((algebraMap ℝ R Q.s) * algebraMap ℝ R Q.s) *
                    (Q.plane.B * Q.plane.B) := by
              calc
                ((algebraMap ℝ R Q.s) * Q.plane.B) *
                    ((algebraMap ℝ R Q.s) * Q.plane.B) =
                  (algebraMap ℝ R Q.s) *
                    (Q.plane.B * algebraMap ℝ R Q.s) * Q.plane.B := by
                      noncomm_ring
                _ = (algebraMap ℝ R Q.s) *
                    ((algebraMap ℝ R Q.s) * Q.plane.B) * Q.plane.B := by
                      rw [hB_s]
                _ = ((algebraMap ℝ R Q.s) * algebraMap ℝ R Q.s) *
                    (Q.plane.B * Q.plane.B) := by
                      simp only [mul_assoc]
            rw [hcross, hquad]
            noncomm_ring
    _ = algebraMap ℝ R Q.c * algebraMap ℝ R Q.c +
        algebraMap ℝ R Q.s * algebraMap ℝ R Q.s := by
          rw [Q.plane.sq]
          simp
    _ = algebraMap ℝ R (Q.c * Q.c + Q.s * Q.s) := by
          simp [map_add, map_mul]
    _ = 1 := by
          rw [Q.normalization]
          simp

theorem hyperbolicRotor_mul_reverse
    {R : Type*} [Ring R] [Algebra ℝ R]
    (Q : HyperbolicRotor R) :
    Q.rotor * Q.reverse = 1 := by
  rw [Q.rotor_eq, Q.reverse_eq]
  simp only [Algebra.smul_def]
  have hK_a : Q.plane.K * algebraMap ℝ R Q.a =
      algebraMap ℝ R Q.a * Q.plane.K :=
    (Algebra.commutes Q.a Q.plane.K).symm
  have hK_b : Q.plane.K * algebraMap ℝ R Q.b =
      algebraMap ℝ R Q.b * Q.plane.K :=
    (Algebra.commutes Q.b Q.plane.K).symm
  have hba : algebraMap ℝ R Q.b * algebraMap ℝ R Q.a =
      algebraMap ℝ R Q.a * algebraMap ℝ R Q.b :=
    by
      rw [← map_mul, ← map_mul, mul_comm]
  calc
    ((algebraMap ℝ R Q.a) * 1 + (algebraMap ℝ R Q.b) * Q.plane.K) *
        ((algebraMap ℝ R Q.a) * 1 - (algebraMap ℝ R Q.b) * Q.plane.K) =
      ((algebraMap ℝ R Q.a) * 1) * ((algebraMap ℝ R Q.a) * 1) +
        ((algebraMap ℝ R Q.b) * Q.plane.K) *
            ((algebraMap ℝ R Q.a) * 1) -
        (((algebraMap ℝ R Q.a) * 1) *
            ((algebraMap ℝ R Q.b) * Q.plane.K) +
          ((algebraMap ℝ R Q.b) * Q.plane.K) *
            ((algebraMap ℝ R Q.b) * Q.plane.K)) := by
            noncomm_ring
    _ = algebraMap ℝ R Q.a * algebraMap ℝ R Q.a -
        (algebraMap ℝ R Q.b * algebraMap ℝ R Q.b) *
          (Q.plane.K * Q.plane.K) := by
            simp only [one_mul, mul_one]
            have hcross :
                ((algebraMap ℝ R Q.b) * Q.plane.K) *
                    (algebraMap ℝ R Q.a) =
                  (algebraMap ℝ R Q.a) *
                    ((algebraMap ℝ R Q.b) * Q.plane.K) := by
              calc
                ((algebraMap ℝ R Q.b) * Q.plane.K) *
                    (algebraMap ℝ R Q.a) =
                  ((algebraMap ℝ R Q.b) *
                    (algebraMap ℝ R Q.a)) * Q.plane.K := by
                      calc
                        ((algebraMap ℝ R Q.b) * Q.plane.K) *
                            (algebraMap ℝ R Q.a) =
                          (algebraMap ℝ R Q.b) *
                            (Q.plane.K * algebraMap ℝ R Q.a) := by
                              simp only [mul_assoc]
                        _ = (algebraMap ℝ R Q.b) *
                            ((algebraMap ℝ R Q.a) * Q.plane.K) := by
                              rw [hK_a]
                        _ = ((algebraMap ℝ R Q.b) *
                            (algebraMap ℝ R Q.a)) * Q.plane.K := by
                              simp only [mul_assoc]
                _ = ((algebraMap ℝ R Q.a) *
                    (algebraMap ℝ R Q.b)) * Q.plane.K := by
                      rw [hba]
                _ = (algebraMap ℝ R Q.a) *
                    ((algebraMap ℝ R Q.b) * Q.plane.K) := by
                      rw [← mul_assoc]
            have hquad :
                ((algebraMap ℝ R Q.b) * Q.plane.K) *
                    ((algebraMap ℝ R Q.b) * Q.plane.K) =
                  ((algebraMap ℝ R Q.b) * algebraMap ℝ R Q.b) *
                    (Q.plane.K * Q.plane.K) := by
              calc
                ((algebraMap ℝ R Q.b) * Q.plane.K) *
                    ((algebraMap ℝ R Q.b) * Q.plane.K) =
                  (algebraMap ℝ R Q.b) *
                    (Q.plane.K * algebraMap ℝ R Q.b) * Q.plane.K := by
                      noncomm_ring
                _ = (algebraMap ℝ R Q.b) *
                    ((algebraMap ℝ R Q.b) * Q.plane.K) * Q.plane.K := by
                      rw [hK_b]
                _ = ((algebraMap ℝ R Q.b) * algebraMap ℝ R Q.b) *
                    (Q.plane.K * Q.plane.K) := by
                      simp only [mul_assoc]
            rw [hcross, hquad]
            noncomm_ring
    _ = algebraMap ℝ R Q.a * algebraMap ℝ R Q.a -
        algebraMap ℝ R Q.b * algebraMap ℝ R Q.b := by
          rw [Q.plane.sq]
          simp
    _ = algebraMap ℝ R (Q.a * Q.a - Q.b * Q.b) := by
          simp [map_sub, map_mul]
    _ = 1 := by
          rw [Q.normalization]
          simp

/-! The finite Hestenes CCR uses the elliptic bivector itself as center. -/

structure HestenesCanonicalPair (R : Type*) [Ring R] [Algebra ℝ R] where
  X : R
  P : R
  phasePlane : EllipticPlane R
  hbar : ℝ
  commutation : X * P - P * X = hbar • phasePlane.B

def jordanPart {R : Type*} [Ring R] [Algebra ℝ R]
    (C : HestenesCanonicalPair R) : R :=
  (1 / 2 : ℝ) • (C.X * C.P + C.P * C.X)

def liePart {R : Type*} [Ring R] [Algebra ℝ R]
    (C : HestenesCanonicalPair R) : R :=
  (1 / 2 : ℝ) • (C.X * C.P - C.P * C.X)

theorem xp_eq_jordan_add_lie
    {R : Type*} [Ring R] [Algebra ℝ R]
    (C : HestenesCanonicalPair R) :
    C.X * C.P = jordanPart C + liePart C := by
  unfold jordanPart liePart
  module

theorem liePart_eq_hestenes_center
    {R : Type*} [Ring R] [Algebra ℝ R]
    (C : HestenesCanonicalPair R) :
    liePart C = (C.hbar / 2 : ℝ) • C.phasePlane.B := by
  unfold liePart
  rw [C.commutation]
  module

theorem jordanPart_eq_xp_sub_hestenes_center
    {R : Type*} [Ring R] [Algebra ℝ R]
    (C : HestenesCanonicalPair R) :
    jordanPart C = C.X * C.P -
      (C.hbar / 2 : ℝ) • C.phasePlane.B := by
  have h := xp_eq_jordan_add_lie C
  rw [liePart_eq_hestenes_center C] at h
  exact eq_sub_of_add_eq' (by simpa [add_comm] using h.symm)

end WeylOrderedXP

end InfoGeometry.Canonical.FirstQuantizedChiralConeBridge

end noncomputable section
