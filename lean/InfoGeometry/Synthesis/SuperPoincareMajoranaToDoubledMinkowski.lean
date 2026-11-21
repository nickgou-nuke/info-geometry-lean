/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import InfoGeometry.Physics.CuntzDeformedSuperPoincare
import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Twistor.WeylZornMajoranaZeroMode
import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
import InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
import InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
import InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
import InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge
import InfoGeometry.Canonical.ZornBdGPhaseFlowBridge
import InfoGeometry.Clifford.Soldering
import InfoGeometry.Clifford.SolderingIsomorphism
import InfoGeometry.Clifford.SplitCl44CausalEnvelope
import InfoGeometry.Lie.SplitOctonionNonmultiplicativity
import InfoGeometry.Algebra.Zorn.SplitQuaternionCore
import InfoGeometry.Algebra.SplitQuaternionMatrices
import InfoGeometry.Projective.SplitQuaternionRankOneProjective
import InfoGeometry.Physics.LorentzBoostMinkowski
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11GradedMorita
import InfoGeometry.Clifford.Cl11GradedTensorUntwist
import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal

/-!
# Bridge: Real Super-Poincaré / Majorana-CAR → Doubled Minkowski Chiral Yang–Mills

**Real-linear Hestenes-Krein formulation with graded tensor product.**

- Carrier: `CanonicalZorn` (real split-octonions), `FourSpace := EuclideanSpace ℝ (Fin 4)`
- Operators: `Matrix (Fin 4) (Fin 4) ℝ` (real endomorphisms on real Krein space)
- Complex structure `J = sqI`: real operator with `J² = -1`
- Soldering: `Vec22 ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ` (real Pauli: σ₀=1, σ₁, σ₃, ε; ε² = -1)
- Majorana/CAR: `rootPlus`, `rootMinus` as real nilpotent 2×2 matrices (from `SplitQuaternionRankOneProjective`)
- Super-Poincaré: real `{Q,Q̄}=2P` on `Matrix (Fin 2) (Fin 2) ℝ` (split quaternions)

The key structure: **graded tensor product** of two `Cl(1,1) ≅ M2R` factors with
Z₂-grading, concretely realized as 2×2 blocks of 2×2 matrices (the chiral block
algebra) and, via the Kronecker/reindex chain, as `Mat4R`.
  - Even (degree 0): bosonic sector (translations, Lorentz)
  - Odd (degree 1): fermionic sector (supercharges)

All constructions reuse existing native theorems; zero `sorry`/`admit`/`axiom`.
-/

noncomputable section

namespace InfoGeometry.Synthesis.SuperPoincareMajoranaToDoubledMinkowski

open Matrix
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Physics.CuntzDeformedSuperPoincare
open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Twistor.WeylZornMajoranaZeroMode
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
open InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
open InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge
open InfoGeometry.Canonical.ZornBdGPhaseFlowBridge
open InfoGeometry.Clifford.Soldering
open InfoGeometry.Clifford.SolderingIsomorphism
open InfoGeometry.Clifford.SplitCl44CausalEnvelope
open InfoGeometry.Lie.SplitOctonionNonmultiplicativity
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.SplitQuaternionMatrices
open InfoGeometry.Projective.SplitQuaternionRankOneProjective
open InfoGeometry.Physics.LorentzBoostMinkowski
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorUntwist
open scoped TensorProduct

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat4R := Matrix (Fin 4) (Fin 4) ℝ
abbrev Coordinate := InfoGeometry.Algebra.FiniteSpin.Vec8R
abbrev FourSpace := EuclideanSpace ℝ (Fin 4)
abbrev FourVector := InfoGeometry.Physics.LorentzBoostMinkowski.FourVector
abbrev Vec22 := InfoGeometry.Clifford.Soldering.Vec22

/-! ## 1. Real Supercharge Embedding: M2R → Mat4R via Real Chiral Blocks -/

/-- Embed an `M2R` matrix as the upper Weyl block of a `Mat4R` (upper-right in `chiralOffBlock4`). -/
def embedUpperWeyl (U : M2R) : Mat4R :=
  chiralOffBlock4 U (0 : M2R)

/-- Embed an `M2R` matrix as the lower Weyl block of a `Mat4R` (lower-left in `chiralOffBlock4`). -/
def embedLowerWeyl (L : M2R) : Mat4R :=
  chiralOffBlock4 (0 : M2R) L

/-- Embed an `M2R` pair as the diagonal blocks of a `Mat4R` (via `chiralDiagBlock4`). -/
def embedDiagWeyl (U L : M2R) : Mat4R :=
  chiralDiagBlock4 U L

/-- The upper-right 2×2 block of `chiralOffBlock4 U L` is `U`. -/
theorem chiralOffBlock4_extractsUpper (U L : M2R) :
    (chiralOffBlock4 U L) 0 2 = U 0 0 ∧
    (chiralOffBlock4 U L) 0 3 = U 0 1 ∧
    (chiralOffBlock4 U L) 1 2 = U 1 0 ∧
    (chiralOffBlock4 U L) 1 3 = U 1 1 := by
  constructor <;> constructor <;> constructor <;>
    simp [chiralOffBlock4]
  <;>
  rfl

/-- The lower-left 2×2 block of `chiralOffBlock4 U L` is `L`. -/
theorem chiralOffBlock4_extractsLower (U L : M2R) :
    (chiralOffBlock4 U L) 2 0 = L 0 0 ∧
    (chiralOffBlock4 U L) 2 1 = L 0 1 ∧
    (chiralOffBlock4 U L) 3 0 = L 1 0 ∧
    (chiralOffBlock4 U L) 3 1 = L 1 1 := by
  constructor <;> constructor <;> constructor <;>
    simp [chiralOffBlock4]
  <;>
  rfl

/-- Off-diagonal multiplication: upper Weyl × lower Weyl = diagonal. -/
theorem embedUpperWeyl_mul_embedLowerWeyl (U V : M2R) :
    embedUpperWeyl U * embedLowerWeyl V = embedDiagWeyl (U * V) (0 : M2R) := by
  rw [embedUpperWeyl, embedLowerWeyl, embedDiagWeyl]
  rw [chiralOffBlock4_mul]
  <;>
  simp [chiralDiagBlock4, Matrix.mul_apply, Fin.sum_univ_two]
  <;>
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  <;>
  aesop

/-- Lower Weyl × upper Weyl = diagonal (other order). -/
theorem embedLowerWeyl_mul_embedUpperWeyl (L U : M2R) :
    embedLowerWeyl L * embedUpperWeyl U = embedDiagWeyl (0 : M2R) (L * U) := by
  rw [embedLowerWeyl, embedUpperWeyl, embedDiagWeyl]
  rw [chiralOffBlock4_mul]
  <;>
  simp [chiralDiagBlock4, Matrix.mul_apply, Fin.sum_univ_two]
  <;>
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  <;>
  aesop

/-! ## 2. Majorana/CAR ↔ Chiral Channels (Real, from SplitQuaternionRankOneProjective) -/

/-- The real CAR creation operator `rootPlus = [[0,1],[0,0]]` as upper Weyl block. -/
def CAR_creation_to_realWeylUpper : M2R :=
  rootPlus

/-- The real CAR annihilation operator `rootMinus = [[0,0],[1,0]]` as lower Weyl block. -/
def CAR_annihilation_to_realWeylLower : M2R :=
  rootMinus

/-- The full real circular connection for the single CAR mode. -/
def rootPair_realConnection : Mat4R :=
  chiralOffBlock4 CAR_creation_to_realWeylUpper CAR_annihilation_to_realWeylLower

/-- `rootPlus` and `rootMinus` are nilpotent real 2×2 matrices. -/
theorem rootPlus_sq_zero_real : rootPlus * rootPlus = (0 : M2R) := by
  rw [rootPlus_eq_matrix]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem rootMinus_sq_zero_real : rootMinus * rootMinus = (0 : M2R) := by
  rw [rootMinus_eq_matrix]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The CAR anticommutator gives the real super-Poincaré momentum. -/
theorem CAR_anticomm_to_momentum :
    rootPlus * rootMinus + rootMinus * rootPlus = (1 : M2R) := by
  have h₁ := rootPlus_rootMinus_products
  have h₂ := rootMinus_rootPlus_products
  rw [h₁, h₂]
  simp [axis_eq_diagonal]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Pi.smul_apply]
  <;>
  aesop

/-! ## 3. Real Split-Quaternion Super-Poincaré on M2R -/

/-- Real split-quaternion basis for M2R: 1, σ₁, σ₃, ε (ε = sqI, ε² = -1 is the complex structure J). -/
def realSuperPoincareBasis : Fin 4 → M2R :=
  ![ (1 : M2R), sigma1, sigma3, sqI ]

/-- Real super-Poincaré presentation: `{Q,Q̄} = 2P` on M2R with J = sqI. -/
structure RealChiralOperatorPresentation where
  antiQQbar : M2R
  Pspinor   : M2R
  super_poincare : antiQQbar = (2 : ℝ) • Pspinor
  J_complex_structure : (sqI : M2R) * (sqI : M2R) = -(1 : M2R) := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [sqI, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The CAR channels give a real super-Poincaré presentation. -/
def realChiralPresentation_from_CAR : RealChiralOperatorPresentation :=
  { antiQQbar := (2 : ℝ) • (CAR_creation_to_realWeylUpper * CAR_annihilation_to_realWeylLower)
  , Pspinor   := CAR_creation_to_realWeylUpper * CAR_annihilation_to_realWeylLower
  , super_poincare := by
      simp [RealChiralOperatorPresentation]
      <;> abel }

/-- The complex structure J = sqI acts on M2R by left multiplication. -/
def J_action (X : M2R) : M2R :=
  (sqI : M2R) * X

/-- J² = -1 on M2R. -/
theorem J_sq_neg_one (X : M2R) :
    J_action (J_action X) = -X := by
  simp only [J_action]
  calc
    (sqI : M2R) * ((sqI : M2R) * X) = ((sqI : M2R) * (sqI : M2R)) * X := by
      rw [Matrix.mul_assoc]
    _ = (-(1 : M2R)) * X := by
      rw [sqI_sq]
    _ = -X := by
      simp [Matrix.one_mul]
      <;>
      ext i j <;>
      simp [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
      <;>
      ring_nf
      <;>
      simp_all [Matrix.one_apply]
      <;>
      aesop

/-! ## 4. Translation Emergence: Real Pspinor → FourSpace -/

/-- Recover the real four-vector from the real Pauli-soldered `Pspinor : M2R`.
Components match the Soldering form: P = t*1 + z*sigma3 + x*sigma1 + y*sqI
where P = [[P00, P01], [P10, P11]].
Then: t = (P00 + P11)/2, z = (P00 - P11)/2, x = (P01 + P10)/2, y = (P01 - P10)/2. -/
def psinorToFourVector (P : M2R) : FourVector :=
  ⟨(P 0 0 + P 1 1) / 2, (P 0 1 + P 1 0) / 2, (P 0 1 - P 1 0) / 2, (P 0 0 - P 1 1) / 2⟩

/-- The determinant of the soldered matrix equals the (2,2) quadratic form.
This matches the Soldering form: det(P) = t² - z² - x² + y². -/
theorem psinorToFourVector_minkowskiSq (P : M2R) :
    (psinorToFourVector P).t ^ 2 - (psinorToFourVector P).z ^ 2 - (psinorToFourVector P).x ^ 2 + (psinorToFourVector P).y ^ 2 = P.det := by
  simp only [psinorToFourVector, Matrix.det_fin_two]
  <;>
  ring_nf
  <;>
  norm_num
  <;>
  linarith

/-- From `RealChiralOperatorPresentation`, extract the translation four-vector. -/
def realSuperPoincareTranslation (S : RealChiralOperatorPresentation) : FourVector :=
  psinorToFourVector S.Pspinor

/-- Map the real four-vector translation to `FourSpace = EuclideanSpace ℝ (Fin 4)`. -/
def fourVectorToFourSpace (v : FourVector) : FourSpace :=
  !₂[v.t, v.x, v.y, v.z]

/-- The composed translation from real supercharges to lattice base space. -/
def realSuperchargeTranslation (S : RealChiralOperatorPresentation) : FourSpace :=
  fourVectorToFourSpace (realSuperPoincareTranslation S)

/-! ## 5. Real Circular Connection from CAR -/

/-- The real circular connection matrix from CAR channels. -/
def realCircularConnection : Mat4R :=
  rootPair_realConnection

/-- The real off-diagonal composition gives diagonal curvature blocks. -/
theorem realChiralOffBlock_mul (U L U' L' : M2R) :
    chiralOffBlock4 U L * chiralOffBlock4 U' L' =
      chiralDiagBlock4 (U * L') (L * U') := by
  rw [chiralOffBlock4_mul]

/-- Real circular curvature matrix (coefficients restricted to ℝ). -/
def circularCurvatureMat4_real (x : Coordinate) : Mat4R :=
  (circularCurvatureMat4 x).map (fun (c : ℂ) => c.re)

/-! ## 6. Graded tensor product of the 2×2 matrix algebra

The `2×2` real matrix algebra `M2R` is the split Clifford algebra `Cl(1,1)`.
Its Mathlib `ZMod 2` grading is `CliffordAlgebra.evenOdd Q11`. The graded
tensor product of two such factors is the algebraic backbone of the doubled
(chiral) Minkowski operator algebra: `Cl(2,2) ≃ (evenOdd Q11) ᵍ⊗ (evenOdd Q11)`.

The Koszul sign `(-1)^(deg·deg)` in this product is exactly the fermionic
anticommutation of the Majorana/CAR supercharges, so this section connects the
super-Poincaré (fermionic) lane to the doubled-Minkowski (bosonic/graded) lane.

The final equivalence `splitGT2_to_blockMat2` realizes the graded tensor
product concretely as 2×2 blocks of 2×2 real matrices — exactly the chiral
block algebra used in section 1 — via the native Koszul untwisting.
-/

/-- The Z₂ grading of the `Cl(1,1) ≅ M2R` factor. -/
abbrev SplitClGrading := CliffordAlgebra.evenOdd InfoGeometry.Clifford.Cl11Matrix.q11

/-- The graded tensor product of two `Cl(1,1) ≅ M2R` factors. -/
abbrev SplitClGT2 := SplitClGrading ᵍ⊗[ℝ] SplitClGrading

/-- `Cl(1,1 ⊕ 1,1)` is the graded tensor product of two `Cl(1,1) (≅ M2R)` factors. -/
def cl11prod_as_gradedTensor :
    CliffordAlgebra (InfoGeometry.Clifford.Cl11Matrix.q11.prod
      InfoGeometry.Clifford.Cl11Matrix.q11) ≃ₐ[ℝ] SplitClGT2 :=
  CliffordAlgebra.prodEquiv _ _

/-- The graded tensor product is concretely the algebra of 2×2 blocks of 2×2
    real matrices (the chiral block algebra of section 1). -/
def splitGT2_to_blockMat2 : SplitClGT2 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) M2R :=
  (untwistEquiv InfoGeometry.Clifford.Cl11Matrix.q11).trans
    (AlgEquiv.mapMatrix cl11StandardEquiv)

/-- The graded tensor product is algebra-equivalent to `Mat4R`, assembled only
    from existing equivalences: block algebra, `matrixEquivTensor`, the
    Kronecker product, and the `Fin 4 ≃ Fin 2 × Fin 2` reindexing. -/
def splitGT2_to_mat4 : SplitClGT2 ≃ₐ[ℝ] Mat4R :=
  splitGT2_to_blockMat2 |>.trans
    (matrixEquivTensor (Fin 2) ℝ M2R) |>.trans
    (Matrix.kroneckerAlgEquiv (Fin 2) (Fin 2) ℝ) |>.trans
    (Matrix.reindexAlgEquiv ℝ ℝ finProdFinEquiv)

/-- The odd (grade-1) split Clifford generator — the fermionic unit. -/
def splitOddGen : SplitClGrading 1 :=
  ⟨CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0),
    CliffordAlgebra.ι_mem_evenOdd_one InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)⟩

/-- Fermionic anticommutation in the graded tensor product: the two odd pure
    tensors `(odd ⊗ 1)` and `(1 ⊗ odd)` anticommute by the Koszul sign. -/
theorem gradedTensor_odd_pure_anticommute :
    (((splitOddGen : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) ᵍ⊗ₜ[ℝ]
        (1 : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11)) : SplitClGT2) *
        ((1 : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) ᵍ⊗ₜ[ℝ]
          (splitOddGen : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11)) =
      -((((1 : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) ᵍ⊗ₜ[ℝ]
          (splitOddGen : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11)) : SplitClGT2) *
        ((splitOddGen : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) ᵍ⊗ₜ[ℝ]
          (1 : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11))) := by
  rw [GradedTensorProduct.tmul_one_mul_one_tmul]
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul]
  simp [splitOddGen]

end InfoGeometry.Synthesis.SuperPoincareMajoranaToDoubledMinkowski