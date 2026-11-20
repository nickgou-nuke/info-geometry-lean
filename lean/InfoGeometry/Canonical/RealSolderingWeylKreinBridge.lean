/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealDoubledChiralKreinFrame
import InfoGeometry.Clifford.SolderingLinearEquiv
import InfoGeometry.Clifford.Cl11GradedTensorMorita
import InfoGeometry.Canonical.GradedTensorWeylBridge
import InfoGeometry.Canonical.SplitCliffordTowerUnification
import InfoGeometry.Krein.MajoranaBdGSheetBridge
import InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge
import InfoGeometry.Projective.MobiusDiagonalFlowClassification
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Real soldering ↔ Krein/Weyl bridge (no complex base field)

Connects the geometric lane (`RealDoubledChiralKreinFrame.FourSpace`, real
doubled Hestenes–Krein carrier with `J² = -1` as a real endomorphism) to the
real charge lane (`Clifford.Soldering.solderingEquiv : Vec22 ≃ₗ[ℝ] M₂(ℝ)`,
real Pauli basis `sigma0, sigma1, sigma3, epsilon`).

1. `fourSpaceEquivVec22`, `fourSpaceEquivMat2Real`: real linear identifications.
2. `realGradedMatrixTensorEquiv`: the native Koszul-graded product of the real
   `Cl(1,1) ≃ M₂(ℝ)` factor and a parity-graded `M₂(ℝ)` factor, represented on
   `M₂(M₂(ℝ))`. Its factor-interchange theorem records the graded sign.
3. `realGradedTensorOnFourSpace`: the Koszul-graded tensor of the real
   two-by-two Clifford/Pauli factor and the real two-by-two chiral factor,
   explicitly flattened to `End ℝ FourSpace`.
4. Real boost/rotation soldering: determinant `1`, trace `2 cosh η` / `2 cos θ`,
   matching the real hyperbolic/elliptic Möbius classes.

No `ℂ` scalar is used; the complex structure remains a real endomorphism.
The matrix flattening uses product indices before reindexing to `Fin 4`, and
the final map uses the established orthonormal basis of `FourSpace` to identify
`M₄(ℝ)` with its real endomorphism algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealSolderingWeylKreinBridge

open InfoGeometry.Clifford.Soldering
open InfoGeometry.Clifford.SolderingIsomorphism
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame
open InfoGeometry.Projective.MobiusDiagonalFlowClassification
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita
open InfoGeometry.Canonical.GradedTensorWeylBridge
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Krein
open Matrix
open scoped TensorProduct GradedTensorProduct

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

/-- Real identification of the geometric FourSpace with coordinate `ℝ⁴`. -/
def fourSpaceEquivVec22 : FourSpace ≃ₗ[ℝ] Vec22 :=
  (WithLp.linearEquiv (2 : ENNReal) ℝ (Fin 4 → ℝ)).trans
    { toFun := fun f => (f 0, f 1, f 2, f 3)
      invFun := fun v i => match i with
        | 0 => v.1
        | 1 => v.2.1
        | 2 => v.2.2.1
        | 3 => v.2.2.2
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl
      left_inv := by
        intro f
        ext i
        fin_cases i <;> rfl
      right_inv := by
        rintro ⟨t, z, x, y⟩
        rfl }

/-- The geometric FourSpace identified with the real charge matrix carrier. -/
def fourSpaceEquivMat2Real : FourSpace ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  fourSpaceEquivVec22.trans solderingEquiv

/-- Real momentum matrix of a geometric FourSpace point (real soldering). -/
def realMomentum (p : FourSpace) : Matrix (Fin 2) (Fin 2) ℝ :=
  soldering (fourSpaceEquivVec22 p)

/-- The real momentum determinant is the (2,2) quadratic form. -/
theorem realMomentum_det (p : FourSpace) :
    (realMomentum p).det = q22 (fourSpaceEquivVec22 p) :=
  det_soldering_eq_q22 _

/-- The real soldering trace is twice the time coordinate. -/
theorem soldering_trace (t z x y : ℝ) :
    (soldering (t, z, x, y)).trace = 2 * t := by
  simp [soldering, sigma0, sigma1, sigma3, epsilon, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two]
  ring

/-! ### The real graded tensor product of the two matrix factors

The Weyl carrier is not an ungraded repeated diagonal copy of `M₂(ℝ)`.  The
first factor is the real `Cl(1,1) ≃ M₂(ℝ)` Pauli representation with its
native even/odd grading.  The second `M₂(ℝ)` factor carries the parity
automorphism implemented by `diag(1,-1)`.  The native graded tensor product
then acts on the nested matrix carrier `M₂(M₂(ℝ))`; the parity twist in the
tail is precisely the Koszul sign. -/

private theorem realM2Parity_even {a : M2R} (ha : a ∈ matrixGrading 0) :
    matrixParity a = a :=
  involutionGrading_even matrixParity matrixParity_involutive ha

private theorem realM2Parity_odd {a : M2R} (ha : a ∈ matrixGrading 1) :
    matrixParity a = -a :=
  involutionGrading_odd matrixParity matrixParity_involutive ha

/-- The genuine graded tensor representation
`Cl(1,1) ᵍ⊗ M₂(ℝ) ≃ M₂(M₂(ℝ))`.  Via `cl11StandardEquiv_grade`, the first
factor is exactly the standard graded `M₂(ℝ)` factor. -/
def realGradedMatrixTensorEquiv :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] matrixGrading) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) M2R :=
  tensorMatrixEquiv matrixGrading matrixParity realM2Parity_even realM2Parity_odd

/-- Flatten the nested real block algebra by retaining both matrix indices.
For an outer block `(i,j)` and an inner entry `(a,b)`, the resulting row and
column are `(i,a)` and `(j,b)`. The multiplication proof uses the inner and
outer matrix sums in precisely that order. -/
def realNestedMatrixFlatten :
    Matrix (Fin 2) (Fin 2) M2R ≃ₐ[ℝ]
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ where
  toFun A := fun x y => A x.1 y.1 x.2 y.2
  invFun A := fun i j => fun a b => A (i, a) (j, b)
  left_inv A := by
    ext i j a b
    rfl
  right_inv A := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rfl
  map_mul' A B := by
    ext ⟨i, a⟩ ⟨k, c⟩
    change (∑ j : Fin 2, ∑ b : Fin 2, A i j a b * B j k b c) =
      ∑ x : Fin 2 × Fin 2, A i x.1 a x.2 * B x.1 k x.2 c
    rw [Fintype.sum_prod_type]
  map_add' A B := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rfl
  commutes' r := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
    · simp [Algebra.algebraMap_eq_smul_one, hij]

/-- The nested block algebra is the full real `4 × 4` matrix algebra under
the product-index ordering. This is the concrete representation-space map
for the Koszul-graded tensor equivalence above. -/
def realNestedMatrixToFin4 :
    Matrix (Fin 2) (Fin 2) M2R ≃ₐ[ℝ]
      Matrix (Fin 4) (Fin 4) ℝ :=
  realNestedMatrixFlatten.trans
    (Matrix.reindexAlgEquiv ℝ ℝ
      (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4))

/-- The genuine graded tensor product of the two real matrix factors acts on
the four-dimensional real Hestenes spinor carrier. The action is obtained by
composing the native graded Morita equivalence with the proved nested-matrix
flattening and the basis representation of endomorphisms of `FourSpace`. -/
def realGradedTensorOnFourSpace :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] matrixGrading) ≃ₐ[ℝ]
      Module.End ℝ FourSpace :=
  (realGradedMatrixTensorEquiv.trans realNestedMatrixToFin4).trans
    (LinearMap.toMatrixAlgEquiv (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).symm

/-- The literal supertensor of the two repository-owned checkerboard-graded
`M₂(ℝ)` factors acts faithfully on the real four-coordinate spinor carrier.
The factor change is the proved graded equivalence in
`SplitCliffordTowerUnification`; the final two maps are the existing nested
matrix flattening and `FourSpace` basis representation. -/
noncomputable def realTwoMatrixGradedTensorOnFourSpace :
    twoMatrixGradedTensor ≃ₐ[ℝ] Module.End ℝ FourSpace :=
  (twoMatrixGradedTensorMoritaEquiv.trans realNestedMatrixToFin4).trans
    (LinearMap.toMatrixAlgEquiv (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).symm

/-! ### Doubling the graded spinor action to the real Krein carrier

The graded matrix algebra acts first on the four-real-dimensional spinor
`FourSpace`.  This diagonal lift gives an action on the existing
eight-dimensional doubled carrier.  Both sheets carry the same operator, so
the Hestenes complex structure, which rotates the two sheets, commutes with
the lifted action. -/

/-- Apply one real endomorphism to both sheets of the doubled chiral carrier. -/
def doubleEnd (T : Module.End ℝ FourSpace) : Module.End ℝ KreinFrame4 where
  toFun u := to_doubled (T (WithLp.fst u)) (T (WithLp.snd u))
  map_add' u v := by
    apply DoubledSpace.ext <;> simp [WithLp.add_fst, WithLp.add_snd, map_add]
  map_smul' c u := by
    apply DoubledSpace.ext <;> simp [WithLp.smul_fst, WithLp.smul_snd, map_smul]

theorem doubleEnd_add (S T : Module.End ℝ FourSpace) :
    doubleEnd (S + T) = doubleEnd S + doubleEnd T := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [doubleEnd]

@[simp] theorem doubleEnd_zero : doubleEnd (0 : Module.End ℝ FourSpace) = 0 := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [doubleEnd]

/-- The diagonal lift preserves composition of real spinor endomorphisms. -/
theorem doubleEnd_mul (S T : Module.End ℝ FourSpace) :
    doubleEnd (S * T) = doubleEnd S * doubleEnd T := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [doubleEnd, Module.End.mul_apply]

/-- The diagonal lift sends the identity spinor operator to the identity on
the real doubled carrier. -/
@[simp] theorem doubleEnd_one :
    doubleEnd (1 : Module.End ℝ FourSpace) = (1 : Module.End ℝ KreinFrame4) := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [doubleEnd]

/-- The diagonal action on the two Krein sheets is a real algebra homomorphism.
It is the representation map that embeds the four-dimensional spinor
operators into endomorphisms of the eight-dimensional doubled carrier. -/
def doubleEndAlgHom : Module.End ℝ FourSpace →ₐ[ℝ]
    Module.End ℝ KreinFrame4 where
  toFun := doubleEnd
  map_one' := doubleEnd_one
  map_mul' := doubleEnd_mul
  map_zero' := doubleEnd_zero
  map_add' := doubleEnd_add
  commutes' r := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [doubleEnd, WithLp.smul_fst, WithLp.smul_snd]

/-- The diagonal two-sheet action is faithful. Restricting to the positive
sheet recovers the original four-dimensional endomorphism. -/
theorem doubleEnd_injective : Function.Injective doubleEnd := by
  intro S T h
  apply LinearMap.ext
  intro x
  have h' := congrArg (fun A : Module.End ℝ KreinFrame4 => A (to_doubled x 0)) h
  have hfst := congrArg (WithLp.fst : KreinFrame4 → FourSpace) h'
  simpa [doubleEnd] using hfst

/-- Every operator acting equally on the two sheets commutes with the real
Hestenes complex structure on `KreinFrame4`. -/
theorem doubleEnd_commutes_with_hestenesJ (T : Module.End ℝ FourSpace) :
    doubleEnd T ∘ₗ doubledComplexStructure.toLinearMap =
      doubledComplexStructure.toLinearMap ∘ₗ doubleEnd T := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [doubleEnd, doubledComplexStructure,
      InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.chiralComplexStructure,
      InfoGeometry.Krein.complex_i, InfoGeometry.Krein.modular_j,
      InfoGeometry.Krein.spectral_epsilon, map_neg]

/-- The two odd annihilation factors remain anticommuting after their actual
real four-dimensional operator representation. -/
theorem realTwoMatrixGradedTensor_annihilations_anticommute :
    realTwoMatrixGradedTensorOnFourSpace annihilation₀ *
        realTwoMatrixGradedTensorOnFourSpace annihilation₁ +
      realTwoMatrixGradedTensorOnFourSpace annihilation₁ *
        realTwoMatrixGradedTensorOnFourSpace annihilation₀ = 0 := by
  have h := congrArg realTwoMatrixGradedTensorOnFourSpace
    gradedTensor_odd_anticommute
  simpa only [map_add, map_mul, map_zero, annihilation₀, annihilation₁] using h

/-- The two real annihilation modes still anticommute after acting on the
eight-dimensional doubled Hestenes–Krein carrier. -/
theorem realTwoMatrixGradedTensor_doubled_annihilations_anticommute :
    doubleEnd (realTwoMatrixGradedTensorOnFourSpace annihilation₀) *
        doubleEnd (realTwoMatrixGradedTensorOnFourSpace annihilation₁) +
      doubleEnd (realTwoMatrixGradedTensorOnFourSpace annihilation₁) *
        doubleEnd (realTwoMatrixGradedTensorOnFourSpace annihilation₀) = 0 := by
  calc
    _ = doubleEnd
        (realTwoMatrixGradedTensorOnFourSpace annihilation₀ *
          realTwoMatrixGradedTensorOnFourSpace annihilation₁ +
        realTwoMatrixGradedTensorOnFourSpace annihilation₁ *
          realTwoMatrixGradedTensorOnFourSpace annihilation₀) := by
      rw [doubleEnd_add, doubleEnd_mul, doubleEnd_mul]
    _ = 0 := by rw [realTwoMatrixGradedTensor_annihilations_anticommute, doubleEnd_zero]

@[simp] theorem realGradedTensorOnFourSpace_apply
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] matrixGrading) :
    realGradedTensorOnFourSpace z =
      (LinearMap.toMatrixAlgEquiv (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).symm
        (realNestedMatrixToFin4 (realGradedMatrixTensorEquiv z)) := rfl

/-- Homogeneous elements of the two real matrix factors obey the Koszul
commutation law. This is the sign that an ordinary tensor product would lose. -/
theorem realMatrixFactors_koszul
    {i j : ZMod 2} (x : CliffordAlgebra.evenOdd q11 i)
    (A : matrixGrading j) :
    head (A := M2R) x * tail matrixParity (A : M2R) =
      (-1 : ℤˣ) ^ (j * i) •
        (tail matrixParity (A : M2R) * head (A := M2R) x) := by
  exact head_tail_supercommute matrixGrading matrixParity
    realM2Parity_even realM2Parity_odd x A

/-- The coefficient factor is represented by the parity-twisted lower block;
this is the right-factor tensor inclusion under the graded Morita map. -/
theorem realGradedMatrixTensorEquiv_right (A : M2R) :
    realGradedMatrixTensorEquiv ((1 : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] A) =
      !![A, 0; 0, matrixParity A] := by
  exact tensorMatrixEquiv_tail matrixGrading matrixParity
    realM2Parity_even realM2Parity_odd A

/-- The Clifford factor is the real Pauli matrix factor, with its grading
preserved by `cl11StandardEquiv_grade`. -/
theorem realGradedMatrixTensorEquiv_left (x : CliffordAlgebra q11) :
    realGradedMatrixTensorEquiv (x ᵍ⊗ₜ[ℝ] (1 : M2R)) =
      (fun i j => algebraMap ℝ M2R (cl11StandardEquiv x i j)) := by
  rw [realGradedMatrixTensorEquiv, tensorMatrixEquiv_head]
  rfl

/-- The real Weyl/tail lift is the right graded tensor inclusion.  Its lower
sheet is twisted by the parity automorphism, retaining the Koszul sign. -/
def realWeylBlock (A : M2R) : Matrix (Fin 2) (Fin 2) M2R :=
  tail matrixParity A

@[simp] theorem realWeylBlock_apply (A : M2R) :
    realWeylBlock A = !![A, 0; 0, matrixParity A] := rfl

theorem realWeylBlock_add (A B : M2R) :
    realWeylBlock (A + B) = realWeylBlock A + realWeylBlock B := by
  exact (tail matrixParity).map_add A B

theorem realWeylBlock_mul (A B : M2R) :
    realWeylBlock (A * B) = realWeylBlock A * realWeylBlock B := by
  exact (tail matrixParity).map_mul A B

theorem realWeylBlock_smul (c : ℝ) (A : M2R) :
    realWeylBlock (c • A) = c • realWeylBlock A := by
  exact (tail matrixParity).toLinearMap.map_smul c A

/-- Real boost soldering: determinant `1`, trace `2 cosh η` (hyperbolic class). -/
theorem realBoost_soldering_det_trace (η : ℝ) :
    (soldering (Real.cosh η, Real.sinh η, 0, 0)).det = 1 ∧
      (soldering (Real.cosh η, Real.sinh η, 0, 0)).trace = 2 * Real.cosh η := by
  constructor
  · rw [det_soldering_eq_q22, q22_apply]
    ring_nf
    exact Real.cosh_sq_sub_sinh_sq η
  · exact soldering_trace _ _ _ _

/-- Real rotation soldering: determinant `1`, trace `2 cos θ` (elliptic class). -/
theorem realRotation_soldering_det_trace (θ : ℝ) :
    (soldering (Real.cos θ, 0, 0, Real.sin θ)).det = 1 ∧
      (soldering (Real.cos θ, 0, 0, Real.sin θ)).trace = 2 * Real.cos θ := by
  constructor
  · rw [det_soldering_eq_q22, q22_apply]
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · rw [soldering_trace]

/-- The real boost/rotation parameters realize the hyperbolic/elliptic classes. -/
theorem realBoost_hyperbolic_class {η : ℝ} (hη : η ≠ 0) :
    diagonalMobiusClass η 0 = DiagonalMobiusClass.hyperbolic :=
  diagonalMobiusClass_hyperbolic hη

theorem realRotation_elliptic_class {θ : ℝ} (hθ : θ ≠ 0) :
    diagonalMobiusClass 0 θ = DiagonalMobiusClass.elliptic :=
  diagonalMobiusClass_elliptic hθ

/-! ### Three real matrix factors on the doubled carrier

The four-coordinate soldering above accounts for two local fermion modes.
The circular Zorn/CAR owner has three modes and acts on an eight-dimensional
real carrier.  The third factor is therefore added as a *graded* tensor
factor.  Its grading is the product grading transported through the proved
two-factor Morita equivalence; applying `matrixGrade` to the outer block
matrix implements the Koszul parity of the two existing factors. -/

open InfoGeometry.Krein.MajoranaBdGSheetBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
open InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge

abbrev RealExterior3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3

/-- Product parity on the two-factor real matrix superalgebra, transported
from its nested block-matrix Morita model. -/
def twoMatrixParityRingEquiv : twoMatrixGradedTensor ≃+* twoMatrixGradedTensor :=
  (twoMatrixGradedTensorMoritaEquiv.toRingEquiv.trans
    (InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade
      matrixParity.toRingEquiv)).trans
    twoMatrixGradedTensorMoritaEquiv.symm.toRingEquiv

/-- The product parity as a real-algebra automorphism. -/
def twoMatrixParity : twoMatrixGradedTensor ≃ₐ[ℝ] twoMatrixGradedTensor :=
  AlgEquiv.ofRingEquiv (f := twoMatrixParityRingEquiv) (by
    intro r
    apply twoMatrixGradedTensorMoritaEquiv.injective
    change twoMatrixGradedTensorMoritaEquiv.toRingEquiv
      ((twoMatrixGradedTensorMoritaEquiv.symm : _ ≃+* _)
        (InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade
          matrixParity.toRingEquiv
          (twoMatrixGradedTensorMoritaEquiv (algebraMap ℝ twoMatrixGradedTensor r)))) = _
    rw [AlgEquiv.symm_toRingEquiv, RingEquiv.apply_symm_apply, AlgEquiv.commutes]
    have hscalar :
        algebraMap ℝ (Matrix (Fin 2) (Fin 2) M2R) r =
          Matrix.scalar (Fin 2) (algebraMap ℝ M2R r) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Algebra.algebraMap_eq_smul_one, Matrix.scalar]
    rw [hscalar, InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade_scalar]
    change Matrix.scalar (Fin 2) (matrixParity (algebraMap ℝ M2R r)) = _
    rw [matrixParity.commutes])

theorem twoMatrixParity_apply (a : twoMatrixGradedTensor) :
    twoMatrixGradedTensorMoritaEquiv (twoMatrixParity a) =
      InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade
        matrixParity.toRingEquiv (twoMatrixGradedTensorMoritaEquiv a) := by
  change twoMatrixGradedTensorMoritaEquiv.toRingEquiv
    ((twoMatrixGradedTensorMoritaEquiv.symm : _ ≃+* _)
      (InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade
        matrixParity.toRingEquiv (twoMatrixGradedTensorMoritaEquiv a))) = _
  rw [AlgEquiv.symm_toRingEquiv, RingEquiv.apply_symm_apply]

theorem twoMatrixParity_involutive : Function.Involutive twoMatrixParity := by
  intro a
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [twoMatrixParity_apply, twoMatrixParity_apply]
  exact InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade_involutive
    matrixParity.toRingEquiv matrixParity_involutive _

/-- Native grading on the product of the first two real `M₂` factors. -/
abbrev twoMatrixProductGrading : ZMod 2 → Submodule ℝ twoMatrixGradedTensor :=
  involutionGrading twoMatrixParity twoMatrixParity_involutive

instance twoMatrixProductGradedAlgebra : GradedAlgebra twoMatrixProductGrading :=
  instGradedAlgebraInvolutionGrading twoMatrixParity twoMatrixParity_involutive

/-- Three local real `M₂` factors, grouped as the first Clifford/Pauli mode
graded-tensored with the native product of the other two matrix factors. -/
abbrev realThreeMatrixGradedTensor :=
  CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] twoMatrixProductGrading

/-- The three-factor graded Morita representation on `M₂(M₂(M₂(ℝ)))`.
The coefficient parity is the product parity above, so the final mode carries
the two preceding Jordan--Wigner signs. -/
noncomputable def realThreeMatrixTensorMorita :
    realThreeMatrixGradedTensor ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) twoMatrixGradedTensor :=
  tensorMatrixEquiv twoMatrixProductGrading twoMatrixParity
    (fun {_} h => involutionGrading_even twoMatrixParity twoMatrixParity_involutive h)
    (fun {_} h => involutionGrading_odd twoMatrixParity twoMatrixParity_involutive h)

/-- The last two real matrix factors enter the first-factor Morita model as
the parity-twisted diagonal block. This formula is the explicit Koszul sign
for the third local mode. -/
theorem realThreeMatrixTensorMorita_tail (a : twoMatrixGradedTensor) :
    realThreeMatrixTensorMorita ((1 : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] a) =
      !![a, 0; 0, twoMatrixParity a] :=
  tensorMatrixEquiv_tail twoMatrixProductGrading twoMatrixParity
    (fun {_} h => involutionGrading_even twoMatrixParity twoMatrixParity_involutive h)
    (fun {_} h => involutionGrading_odd twoMatrixParity twoMatrixParity_involutive h) a

/-- The first mode annihilator is the odd upper matrix unit in the first real
`M₂` factor, tensored with units in the other factors. This is a canonical
factor generator, not a transported preimage of a Zorn operator. -/
def realThreeAnnihilationHead : realThreeMatrixGradedTensor :=
  (headUnit 0 1) ᵍ⊗ₜ[ℝ] (1 : twoMatrixGradedTensor)

/-- The first mode creator is the lower matrix unit in the first real factor. -/
def realThreeCreationHead : realThreeMatrixGradedTensor :=
  (headUnit 1 0) ᵍ⊗ₜ[ℝ] (1 : twoMatrixGradedTensor)

theorem realThreeMatrixTensorMorita_annihilationHead :
    realThreeMatrixTensorMorita realThreeAnnihilationHead =
      Matrix.single 0 1 (1 : twoMatrixGradedTensor) := by
  rw [realThreeAnnihilationHead, realThreeMatrixTensorMorita,
    tensorMatrixEquiv_head twoMatrixProductGrading twoMatrixParity
      (fun {_} h => involutionGrading_even twoMatrixParity twoMatrixParity_involutive h)
      (fun {_} h => involutionGrading_odd twoMatrixParity twoMatrixParity_involutive h)]
  ext i j
  rw [head_apply, headUnit, cl11StandardEquiv.apply_symm_apply]
  simp [Matrix.single]

theorem realThreeMatrixTensorMorita_creationHead :
    realThreeMatrixTensorMorita realThreeCreationHead =
      Matrix.single 1 0 (1 : twoMatrixGradedTensor) := by
  rw [realThreeCreationHead, realThreeMatrixTensorMorita,
    tensorMatrixEquiv_head twoMatrixProductGrading twoMatrixParity
      (fun {_} h => involutionGrading_even twoMatrixParity twoMatrixParity_involutive h)
      (fun {_} h => involutionGrading_odd twoMatrixParity twoMatrixParity_involutive h)]
  ext i j
  rw [head_apply, headUnit, cl11StandardEquiv.apply_symm_apply]
  simp [Matrix.single]

/-- The first local matrix mode satisfies the CAR inside the native three-
factor graded tensor algebra. -/
theorem realThreeMatrixTensor_head_CAR :
    realThreeAnnihilationHead * realThreeCreationHead +
      realThreeCreationHead * realThreeAnnihilationHead = 1 := by
  apply realThreeMatrixTensorMorita.injective
  rw [map_add, map_mul, map_mul, map_one,
    realThreeMatrixTensorMorita_annihilationHead,
    realThreeMatrixTensorMorita_creationHead]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, Matrix.mul_apply]

/-! The remaining two sites are the two genuine matrix modes already owned
by `GradedTensorWeylBridge`. They enter through the native graded tensor
product; the Morita map records their Koszul parity as its lower-block twist. -/

/-- Second-site annihilation operator in the three-factor real graded
matrix algebra. -/
def realThreeAnnihilationMiddle : realThreeMatrixGradedTensor :=
  (1 : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] annihilation₀

/-- Second-site creation operator in the three-factor real graded matrix
algebra. -/
def realThreeCreationMiddle : realThreeMatrixGradedTensor :=
  (1 : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] creation₀

/-- Third-site annihilation operator in the three-factor real graded matrix
algebra. -/
def realThreeAnnihilationTail : realThreeMatrixGradedTensor :=
  (1 : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] annihilation₁

/-- Third-site creation operator in the three-factor real graded matrix
algebra. -/
def realThreeCreationTail : realThreeMatrixGradedTensor :=
  (1 : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] creation₁

/-- The second-site CAR is retained in the represented three-factor algebra.
The proof inspects both diagonal blocks of the graded Morita image. -/
theorem realThreeMatrixTensor_middle_CAR :
    realThreeAnnihilationMiddle * realThreeCreationMiddle +
      realThreeCreationMiddle * realThreeAnnihilationMiddle = 1 := by
  apply realThreeMatrixTensorMorita.injective
  simp only [realThreeAnnihilationMiddle, realThreeCreationMiddle]
  rw [map_add, map_mul, map_mul, map_one,
    realThreeMatrixTensorMorita_tail, realThreeMatrixTensorMorita_tail]
  have hlocal := annihilation₀_creation₀_CAR
  have hparity := congrArg twoMatrixParity hlocal
  have hparity' : twoMatrixParity annihilation₀ * twoMatrixParity creation₀ +
      twoMatrixParity creation₀ * twoMatrixParity annihilation₀ = 1 := by
    simpa only [map_add, map_mul, map_one] using hparity
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply] using hlocal
  · simp
  · simp
  · simpa [Matrix.mul_apply] using hparity'

/-- The third-site CAR is retained in the represented three-factor algebra,
including the product parity of the preceding two real matrix factors. -/
theorem realThreeMatrixTensor_tail_CAR :
    realThreeAnnihilationTail * realThreeCreationTail +
      realThreeCreationTail * realThreeAnnihilationTail = 1 := by
  apply realThreeMatrixTensorMorita.injective
  simp only [realThreeAnnihilationTail, realThreeCreationTail]
  rw [map_add, map_mul, map_mul, map_one,
    realThreeMatrixTensorMorita_tail, realThreeMatrixTensorMorita_tail]
  have hlocal := annihilation₁_creation₁_CAR
  have hparity := congrArg twoMatrixParity hlocal
  have hparity' : twoMatrixParity annihilation₁ * twoMatrixParity creation₁ +
      twoMatrixParity creation₁ * twoMatrixParity annihilation₁ = 1 := by
    simpa only [map_add, map_mul, map_one] using hparity
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply] using hlocal
  · simp
  · simp
  · simpa [Matrix.mul_apply] using hparity'

/-- The Koszul sign between the second and third annihilation modes is the
cross-factor CAR already proved in the two-matrix owner. -/
theorem realThreeMatrixTensor_middle_tail_anticommute :
    realThreeAnnihilationMiddle * realThreeAnnihilationTail +
      realThreeAnnihilationTail * realThreeAnnihilationMiddle = 0 := by
  apply realThreeMatrixTensorMorita.injective
  simp only [realThreeAnnihilationMiddle, realThreeAnnihilationTail]
  rw [map_add, map_mul, map_mul, map_zero,
    realThreeMatrixTensorMorita_tail, realThreeMatrixTensorMorita_tail]
  have hlocal := annihilation₀_annihilation₁_anticommute
  have hparity := congrArg twoMatrixParity hlocal
  have hparity' : twoMatrixParity annihilation₀ * twoMatrixParity annihilation₁ +
      twoMatrixParity annihilation₁ * twoMatrixParity annihilation₀ = 0 := by
    simpa only [map_add, map_mul, map_zero] using hparity
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply] using hlocal
  · simp
  · simp
  · simpa [Matrix.mul_apply] using hparity'

/-- Flatten one real two-by-two block index and one four-by-four block index.
The product index retains the order of the two tensor factors. -/
def realTwoByFourFlatten :
    Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) ℝ) ≃ₐ[ℝ]
      Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ where
  toFun A := fun x y => A x.1 y.1 x.2 y.2
  invFun A := fun i j => fun a b => A (i, a) (j, b)
  left_inv A := by ext i j a b; rfl
  right_inv A := by ext ⟨i,a⟩ ⟨j,b⟩; rfl
  map_mul' A B := by
    ext ⟨i,a⟩ ⟨k,c⟩
    change (∑ j : Fin 2, ∑ b : Fin 4, A i j a b * B j k b c) =
      ∑ x : Fin 2 × Fin 4, A i x.1 a x.2 * B x.1 k x.2 c
    rw [Fintype.sum_prod_type]
  map_add' A B := by ext ⟨i,a⟩ ⟨j,b⟩; rfl
  commutes' r := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hij : i = j
    · subst j
      by_cases hab : a = b
      · subst b
        simp [Algebra.algebraMap_eq_smul_one]
      · simp [Algebra.algebraMap_eq_smul_one, hab]
    · simp [Algebra.algebraMap_eq_smul_one, hij]

@[simp] theorem realTwoByFourFlatten_apply
    (A : Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) ℝ))
    (i j : Fin 2) (a b : Fin 4) :
    realTwoByFourFlatten A (i, a) (j, b) = A i j a b := rfl

/-- Reindex the binary occupation order of the three tensor factors to the
repository's circular Peirce order `(∅, {0}, {1}, {2}, {012}, {12}, {02},
{01})`. The input order is the matrix product order: head, middle, tail. -/
def realThreePeirceIndex : Fin 8 ≃ Fin 8 where
  toFun := ![0, 3, 2, 5, 1, 6, 7, 4]
  invFun := ![0, 4, 2, 1, 7, 3, 5, 6]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem realThreePeirceIndex_apply (i : Fin 8) :
    realThreePeirceIndex i = ![0, 3, 2, 5, 1, 6, 7, 4] i := rfl

/-- Decode a circular Peirce coordinate into the product index used by the
flattened first-factor/two-factor graded matrix representation. -/
private def realThreePeircePairIndex (i : Fin 8) : Fin 2 × Fin 4 :=
  (finProdFinEquiv (m := 2) (n := 4)).symm (realThreePeirceIndex.symm i)

@[simp] private theorem realThreePeircePairIndex_apply (i : Fin 8) :
    realThreePeircePairIndex i =
      ![(0, 0), (1, 0), (0, 2), (0, 1), (1, 3), (0, 3), (1, 1), (1, 2)] i := by
  fin_cases i <;> simp only [realThreePeircePairIndex, realThreePeirceIndex,
    finProdFinEquiv_symm_apply]
  all_goals
    apply Prod.ext <;> apply Fin.ext <;> norm_num [Fin.divNat, Fin.modNat]

/-- Three graded real `M₂` factors give the full real eight-by-eight matrix
algebra.  This uses the proved two-factor graded Morita owner at the
coefficient level, followed by genuine matrix-index flattening. -/
noncomputable def realThreeMatrixTensorToFin8 :
    realThreeMatrixGradedTensor ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  (((realThreeMatrixTensorMorita.trans
    twoMatrixGradedTensorMoritaEquiv.mapMatrix).trans
      realNestedMatrixToFin4.mapMatrix).trans realTwoByFourFlatten).trans
    (Matrix.reindexAlgEquiv ℝ ℝ
      ((finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8).trans realThreePeirceIndex))

set_option maxHeartbeats 800000
/-- In the circular Peirce coordinate ordering, the first tensor creation
mode has four unit transitions. The sign of the exterior ordered two-form is
supplied by the signed Fock basis below, rather than inserted into this
occupation-coordinate matrix. -/
theorem realThreeMatrixTensorToFin8_creationHead :
    realThreeMatrixTensorToFin8 realThreeCreationHead =
      Matrix.single 1 0 (1 : ℝ) + Matrix.single 6 3 1 +
        Matrix.single 7 2 1 + Matrix.single 4 5 1 := by
  rw [realThreeMatrixTensorToFin8, AlgEquiv.trans_apply,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    realThreeMatrixTensorMorita_creationHead]
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  ext i j
  change realTwoByFourFlatten
      ((Matrix.single 1 0 (1 : twoMatrixGradedTensor)).map
        (realNestedMatrixToFin4 ∘ twoMatrixGradedTensorMoritaEquiv))
      (realThreePeircePairIndex i) (realThreePeircePairIndex j) = _
  fin_cases i <;> fin_cases j <;>
    simp [realThreePeircePairIndex, realThreePeirceIndex,
      realTwoByFourFlatten_apply, realNestedMatrixToFin4,
      realNestedMatrixFlatten, Matrix.single, finProdFinEquiv,
      Fin.divNat, Fin.modNat] <;> rfl

/-- Conjugating the unsigned occupation matrix by the owner-specified Fock
coordinate signs supplies the ordered-wedge sign at transition `2 → 7`.
This is the concrete sign correction used in the real exterior action. -/
theorem realThreeMatrixTensorToFin8_creationHead_signed :
    Matrix.diagonal bdgSign *
        realThreeMatrixTensorToFin8 realThreeCreationHead *
          Matrix.diagonal bdgSign =
      Matrix.single 1 0 (1 : ℝ) + Matrix.single 6 3 1 -
        Matrix.single 7 2 1 + Matrix.single 4 5 1 := by
  rw [realThreeMatrixTensorToFin8_creationHead]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, bdgSign, Matrix.single]

/-- The exterior carrier basis selected by the existing Fock-to-circular-Zorn
equivalence. This is the signed Peirce basis owned by the Fock construction,
not the unsigned subset-order exterior basis. -/
noncomputable def realFockPeirceBasis : Module.Basis (Fin 8) ℝ RealExterior3 :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.map
    InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockBdGEquiv.symm

@[simp] theorem realFockPeirceBasis_apply (i : Fin 8) :
    realFockPeirceBasis i =
      InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockPreimageBasis i := by
  change InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockBdGEquiv.symm
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i) =
    InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockPreimageBasis i
  apply InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockBdGEquiv.injective
  rw [InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockBdGEquiv.apply_symm_apply]
  change InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i =
    InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockToZorn
      (InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockPreimageBasis i)
  rw [InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockToZorn_preimageBasis]

@[simp] theorem realFockPeirceBasis_repr_fockPreimage (i : Fin 8) :
    realFockPeirceBasis.repr
        (InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.fockPreimageBasis i) =
      Finsupp.single i 1 := by
  rw [← realFockPeirceBasis_apply, realFockPeirceBasis.repr_self]

@[simp] theorem realFockPeirceBasis_equivFun_basis (i : Fin 8) :
    realFockPeirceBasis.equivFun (realFockPeirceBasis i) = Pi.single i 1 := by
  funext j
  by_cases h : i = j
  · subst j
    rw [Module.Basis.equivFun_self]
    simp
  · have h' : j ≠ i := by
      intro hji
      exact h hji.symm
    rw [Module.Basis.equivFun_self]
    simp [h, h']

/-- The occupation-coordinate matrix representation acts on the literal
three-mode exterior carrier through its established Peirce basis. -/
noncomputable def realThreeMatrixTensorOnExterior :
    realThreeMatrixGradedTensor ≃ₐ[ℝ] Module.End ℝ RealExterior3 :=
  ((realThreeMatrixTensorToFin8.trans
    (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))).symm).trans
      (bdgCoordinateSignEquiv.conjAlgEquiv ℝ)).trans
      ((realFockPeirceBasis.equivFun.symm).conjAlgEquiv ℝ)

@[simp] theorem realFin8MatrixUnit_action (r c : Fin 8)
    (v : Fin 8 → ℝ) :
    ((LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))).symm
      (Matrix.single r c (1 : ℝ))) v = v c • Pi.single r 1 := by
  change Matrix.toLinAlgEquiv (Pi.basisFun ℝ (Fin 8))
      (Matrix.single r c (1 : ℝ)) v = _
  rw [Matrix.toLinAlgEquiv_apply, Matrix.single_mulVec_eq]
  ext k
  rw [Finset.sum_eq_single r]
  · simp [Pi.single_apply]
  · intro a ha har
    simp [har]
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

@[simp] theorem realThreeMatrixTensorOnExterior_apply
    (a : realThreeMatrixGradedTensor) (ψ : RealExterior3) :
    realThreeMatrixTensorOnExterior a ψ =
      realFockPeirceBasis.equivFun.symm
        (bdgCoordinateSignEquiv
          (((LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))).symm
              (realThreeMatrixTensorToFin8 a))
            (bdgCoordinateSignEquiv (realFockPeirceBasis.equivFun ψ)))) := by
  simp [realThreeMatrixTensorOnExterior, LinearEquiv.conjAlgEquiv_apply,
    bdgCoordinateSignEquiv]

/-- The genuine exterior-Fock equivalence followed by the existing Zorn to
doubled-Krein equivalence. Its signed Peirce basis is inherited from the Fock
owner rather than guessed from unsigned Nambu coordinates. -/
noncomputable def realThreeExteriorToH4 : RealExterior3 ≃ₗ[ℝ]
    InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4 :=
  fockBdGEquiv.trans zornToDoubleKrein

/-- The real graded matrix algebra acts on the common doubled Krein carrier
by transport of its exterior-Fock representation along the owner equivalence. -/
noncomputable def realThreeMatrixTensorOnH4 :
    realThreeMatrixGradedTensor ≃ₐ[ℝ]
      Module.End ℝ InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4 :=
  realThreeMatrixTensorOnExterior.trans (realThreeExteriorToH4.conjAlgEquiv ℝ)

/-- Every two-factor real Koszul-graded matrix operator embeds into the
three-factor real CAR algebra by its diagonal action on the two Krein sheets.
The source and target carriers stay distinct: this is an algebra embedding
whose represented action agrees exactly on `KreinFrame4`. -/
noncomputable def twoModeIntoThreeMode : twoMatrixGradedTensor →ₐ[ℝ]
    realThreeMatrixGradedTensor :=
  (realThreeMatrixTensorOnH4.symm.toAlgHom).comp
    (doubleEndAlgHom.comp realTwoMatrixGradedTensorOnFourSpace.toAlgHom)

/-- The embedding above is characterized by its action on the actual doubled
Krein carrier. -/
theorem realThreeMatrixTensorOnH4_twoModeIntoThreeMode (a : twoMatrixGradedTensor) :
    realThreeMatrixTensorOnH4 (twoModeIntoThreeMode a) =
      doubleEnd (realTwoMatrixGradedTensorOnFourSpace a) := by
  simp [twoModeIntoThreeMode, doubleEndAlgHom]

/-- The diagonal two-mode inclusion into the three-mode algebra is injective. -/
theorem twoModeIntoThreeMode_injective : Function.Injective twoModeIntoThreeMode := by
  intro a b h
  apply realTwoMatrixGradedTensorOnFourSpace.injective
  apply doubleEnd_injective
  have h' := congrArg realThreeMatrixTensorOnH4 h
  simpa only [realThreeMatrixTensorOnH4_twoModeIntoThreeMode] using h'

/-- Intertwining law for the actual exterior and doubled-Krein actions. -/
theorem realThreeMatrixTensorOnH4_intertwines_exterior
    (a : realThreeMatrixGradedTensor) (ψ : RealExterior3) :
    realThreeMatrixTensorOnH4 a (realThreeExteriorToH4 ψ) =
      realThreeExteriorToH4 (realThreeMatrixTensorOnExterior a ψ) := by
  simp [realThreeMatrixTensorOnH4, LinearEquiv.conjAlgEquiv_apply]

/-- The canonical first-mode CAR survives the real eight-dimensional
representation and the Nambu-to-doubled-Krein transport.  This is an
operator identity on `End ℝ KreinFrame4`, not a complex-matrix proxy. -/
theorem realThreeMatrixTensorOnH4_head_CAR :
    realThreeMatrixTensorOnH4 realThreeAnnihilationHead *
        realThreeMatrixTensorOnH4 realThreeCreationHead +
      realThreeMatrixTensorOnH4 realThreeCreationHead *
        realThreeMatrixTensorOnH4 realThreeAnnihilationHead = 1 := by
  have h := congrArg realThreeMatrixTensorOnH4 realThreeMatrixTensor_head_CAR
  simpa only [map_add, map_mul, map_one] using h

/-- The middle-site CAR survives the genuine graded-tensor representation on
the real doubled Krein carrier. -/
theorem realThreeMatrixTensorOnH4_middle_CAR :
    realThreeMatrixTensorOnH4 realThreeAnnihilationMiddle *
        realThreeMatrixTensorOnH4 realThreeCreationMiddle +
      realThreeMatrixTensorOnH4 realThreeCreationMiddle *
        realThreeMatrixTensorOnH4 realThreeAnnihilationMiddle = 1 := by
  simpa only [map_add, map_mul, map_one] using
    congrArg realThreeMatrixTensorOnH4 realThreeMatrixTensor_middle_CAR

/-- The tail-site CAR survives the genuine graded-tensor representation on
the real doubled Krein carrier. -/
theorem realThreeMatrixTensorOnH4_tail_CAR :
    realThreeMatrixTensorOnH4 realThreeAnnihilationTail *
        realThreeMatrixTensorOnH4 realThreeCreationTail +
      realThreeMatrixTensorOnH4 realThreeCreationTail *
        realThreeMatrixTensorOnH4 realThreeAnnihilationTail = 1 := by
  simpa only [map_add, map_mul, map_one] using
    congrArg realThreeMatrixTensorOnH4 realThreeMatrixTensor_tail_CAR

/-- The second and third modes remain mutually odd after transport to the
same real Krein endomorphism algebra. -/
theorem realThreeMatrixTensorOnH4_middle_tail_anticommute :
    realThreeMatrixTensorOnH4 realThreeAnnihilationMiddle *
        realThreeMatrixTensorOnH4 realThreeAnnihilationTail +
      realThreeMatrixTensorOnH4 realThreeAnnihilationTail *
        realThreeMatrixTensorOnH4 realThreeAnnihilationMiddle = 0 := by
  simpa only [map_add, map_mul, map_zero] using
    congrArg realThreeMatrixTensorOnH4
      realThreeMatrixTensor_middle_tail_anticommute

end InfoGeometry.Canonical.RealSolderingWeylKreinBridge
