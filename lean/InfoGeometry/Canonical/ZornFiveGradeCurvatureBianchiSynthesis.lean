/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionFiveGradeOperatorBridge
import InfoGeometry.Algebra.ZornLeftMultiplicationDefect
import InfoGeometry.Canonical.OperatorZornFourPotentialGauge

/-!
# Nonassociative Zorn Operator Closure, Five-Graded Endomorphism Algebra, and Curvature/Bianchi Defects

This module packages and bridges the three kernel-checked algebraic pillars connecting
nonassociative Zorn multiplication defects, five-graded operator closure, and
noncommutative-coefficient gauge curvature:

1. **Five-Grading on the Full Zorn Endomorphism Algebra (`SplitOctonionFiveGradeOperatorBridge`)**:
   On the canonical real Zorn carrier `Carrier = ZornMatrix ℝ`, the normalized left/right
   multiplication difference `t = (1 / 2) • (L_ℓ - R_ℓ)` satisfies `t³ = t`, decomposes
   `CarrierEnd = Module.End ℝ Carrier` into the five adjoint eigenspaces `{-2, -1, 0, +1, +2}`
   with exact reconstruction, satisfies `E_i · E_j ⊆ E_{i+j}` and `[E_i, E_j] ⊆ E_{i+j}`,
   and obeys `(ad_t)⁵ - 5 (ad_t)³ + 4 ad_t = 0`.
2. **Explicit Carrier Isomorphism & Strict Lie-Span Enlargement on `CarrierEnd`**:
   Via `canonicalVectorLinearEquiv : Carrier ≃ₗ[ℝ] Z` and the induced algebra isomorphism
   `carrierEndAlgEquiv : Module.End ℝ Z ≃ₐ[ℝ] CarrierEnd`, the left-multiplication operator
   and associator defect `multiplicationDefect X Y` on `Z` transport identically to
   `canonicalLeftMultiplicationMap` and `canonicalMultiplicationDefect` on `CarrierEnd`.
   In particular, on the five-graded endomorphism algebra `CarrierEnd` itself:
   - `canonicalMultiplicationDefect (chiralUpperBasis 0) (chiralUpperBasis 1) ≠ 0`,
   - its 5-grade coordinate tuple `fiveGradeDecomposeLinear peirceDefectOperator (...)` is nonzero,
   - and `LinearMap.range canonicalLeftMultiplicationMap < (LieSubalgebra.lieSpan ℝ CarrierEnd (Set.range canonicalLeftMultiplicationMap)).toSubmodule`.
3. **Full Noncommutative-Coefficient Zorn Curvature & Six-Term Bianchi Identity (`OperatorZornFourPotentialGauge`)**:
   Over an arbitrary associative coefficient ring `A`, the covariant derivative
   `∇_μ X = δ_{p_μ} X + Φ_μ X` has curvature retaining the background commutator
   derivation and both ordered associators (`curvatureAction_eq`), and cyclic
   Bianchi sum retaining the full six-term Akivis associator alternation (`bianchi_eq`).
-/

namespace InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis

open InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge
open InfoGeometry.Lie.SplitOctonionFiveGradeOperatorBridge
open InfoGeometry.Physics.Algebra
open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.ZornPinorReconstruction
open InfoGeometry.Algebra.ZornLeftCAR
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

/-! ### 1. Explicit Linear and Endomorphism-Algebra Isomorphism (`Carrier ≃ₗ[ℝ] Z`) -/

/-- `canonicalVectorEquiv` promoted to an `ℝ`-linear equivalence between
`Carrier = ZornMatrix ℝ` and `Z = ZornVectorMatrix ℝ`. -/
def canonicalVectorLinearEquiv : Carrier ≃ₗ[ℝ] Z where
  toEquiv := canonicalVectorEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem canonicalVectorLinearEquiv_apply (X : Carrier) :
    canonicalVectorLinearEquiv X = canonicalVectorEquiv X := rfl

@[simp] theorem canonicalVectorLinearEquiv_symm_apply (X : Z) :
    canonicalVectorLinearEquiv.symm X = canonicalVectorEquiv.symm X := rfl

/-- Conjugation by `canonicalVectorLinearEquiv` induces an `ℝ`-algebra isomorphism
between `Module.End ℝ Z` and the five-graded endomorphism algebra `CarrierEnd = Module.End ℝ Carrier`. -/
def carrierEndAlgEquiv : Module.End ℝ Z ≃ₐ[ℝ] CarrierEnd :=
  AlgEquiv.ofLinearEquiv
    (canonicalVectorLinearEquiv.symm.conj)
    (by
      apply LinearMap.ext
      intro X
      simp [LinearEquiv.conj_apply])
    (fun S T => by
      apply LinearMap.ext
      intro X
      simp [LinearEquiv.conj_apply, Module.End.mul_apply])

@[simp] theorem carrierEndAlgEquiv_apply (T : Module.End ℝ Z) (X : Carrier) :
    carrierEndAlgEquiv T X =
      canonicalVectorEquiv.symm (T (canonicalVectorEquiv X)) := rfl

/-- Canonical left multiplication on `Carrier = ZornMatrix ℝ` bundled as an `ℝ`-linear map
`Carrier →ₗ[ℝ] CarrierEnd`. -/
def canonicalLeftMultiplicationMap : Carrier →ₗ[ℝ] CarrierEnd where
  toFun := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.leftMultiplication
  map_add' X Y := by
    apply LinearMap.ext
    intro W
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul X Y W
  map_smul' r X := by
    apply LinearMap.ext
    intro W
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul r X W

@[simp] theorem canonicalLeftMultiplicationMap_apply (X W : Carrier) :
    canonicalLeftMultiplicationMap X W = X * W := rfl

/-- Associator multiplication defect `L_{X * Y} - L_X * L_Y` defined directly on
the five-graded endomorphism algebra `CarrierEnd = Module.End ℝ Carrier`. -/
def canonicalMultiplicationDefect (X Y : Carrier) : CarrierEnd :=
  canonicalLeftMultiplicationMap (X * Y) -
    canonicalLeftMultiplicationMap X * canonicalLeftMultiplicationMap Y

/-- `carrierEndAlgEquiv` intertwines `ZornLeftCAR.leftMultiplication` on `Z` with
`canonicalLeftMultiplicationMap` on `Carrier`. -/
theorem carrierEndAlgEquiv_leftMultiplication (X : Carrier) :
    carrierEndAlgEquiv (leftMultiplication (canonicalVectorEquiv X)) =
      canonicalLeftMultiplicationMap X := by
  apply LinearMap.ext
  intro W
  change canonicalVectorEquiv.symm
      (ZornVectorMatrix.mul (canonicalVectorEquiv X) (canonicalVectorEquiv W)) = X * W
  rw [← canonicalVectorEquiv_mul, Equiv.symm_apply_apply]

/-- `carrierEndAlgEquiv` transports `multiplicationDefect` on `Z` identically to
`canonicalMultiplicationDefect` on `CarrierEnd`. -/
theorem carrierEndAlgEquiv_multiplicationDefect (X Y : Carrier) :
    carrierEndAlgEquiv
      (multiplicationDefect (canonicalVectorEquiv X) (canonicalVectorEquiv Y)) =
      canonicalMultiplicationDefect X Y := by
  unfold multiplicationDefect canonicalMultiplicationDefect
  rw [map_sub, map_mul, ← canonicalVectorEquiv_mul,
    carrierEndAlgEquiv_leftMultiplication,
    carrierEndAlgEquiv_leftMultiplication,
    carrierEndAlgEquiv_leftMultiplication]

/-- The canonical associator defect for `chiralUpperBasis 0` and `chiralUpperBasis 1`
is strictly nonzero in `CarrierEnd`. -/
theorem canonicalMultiplicationDefect_chiralUpper01_ne_zero :
    canonicalMultiplicationDefect
      (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
      (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) ≠ 0 := by
  intro hZero
  apply multiplicationDefect_U01_ne_zero
  apply carrierEndAlgEquiv.injective
  rw [map_zero, ← canonicalUpperBasis_map 0, ← canonicalUpperBasis_map 1,
    carrierEndAlgEquiv_multiplicationDefect]
  exact hZero

/-- Every canonical associator defect `canonicalMultiplicationDefect X Y` decomposes into
its five adjoint grade components on `CarrierEnd`, and for `chiralUpperBasis 0, 1`
the 5-grade coordinate tuple is strictly nonzero. -/
theorem canonicalMultiplicationDefect_fiveGradeCoordinates_ne_zero :
    fiveGradeDecomposeLinear peirceDefectOperator
      (canonicalMultiplicationDefect
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1)) ≠ 0 := by
  intro hCoordZero
  apply canonicalMultiplicationDefect_chiralUpper01_ne_zero
  calc
    canonicalMultiplicationDefect
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) =
      fiveGradeRecomposeLinear peirceDefectOperator
        (fiveGradeDecomposeLinear peirceDefectOperator
          (canonicalMultiplicationDefect
            (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
            (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1))) :=
      (zornFiveGrade_recompose_decompose _).symm
    _ = 0 := by rw [hCoordZero, map_zero]

/-- On `CarrierEnd`, the associator defect `canonicalMultiplicationDefect (chiralUpperBasis 0) (chiralUpperBasis 1)`
does not belong to `LinearMap.range canonicalLeftMultiplicationMap`. -/
theorem canonicalMultiplicationDefect_chiralUpper01_not_mem_left_range :
    canonicalMultiplicationDefect
      (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
      (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1) ∉
      LinearMap.range canonicalLeftMultiplicationMap := by
  rintro ⟨W, hW⟩
  apply nonzero_multiplicationDefect_not_mem_left_range
    (ZornVectorMatrix.U 0) (ZornVectorMatrix.U 1)
    multiplicationDefect_U01_ne_zero
  refine ⟨canonicalVectorEquiv W, ?_⟩
  apply carrierEndAlgEquiv.injective
  rw [carrierEndAlgEquiv_leftMultiplication,
    ← canonicalUpperBasis_map 0, ← canonicalUpperBasis_map 1,
    carrierEndAlgEquiv_multiplicationDefect]
  exact hW

/-- Every canonical associator defect belongs to the Lie subalgebra of `CarrierEnd`
generated by `Set.range canonicalLeftMultiplicationMap`. -/
theorem canonicalMultiplicationDefect_mem_lieSpan (X Y : Carrier) :
    canonicalMultiplicationDefect X Y ∈
      LieSubalgebra.lieSpan ℝ CarrierEnd (Set.range canonicalLeftMultiplicationMap) := by
  have hComm :
      canonicalMultiplicationDefect X Y =
        (1 / 2 : ℝ) •
          (canonicalLeftMultiplicationMap (X * Y - Y * X) -
            ⁅canonicalLeftMultiplicationMap X, canonicalLeftMultiplicationMap Y⁆) := by
    have hZ := multiplicationDefect_eq_half_commutator_correction
      (canonicalVectorEquiv X) (canonicalVectorEquiv Y)
    have hMap := congrArg carrierEndAlgEquiv hZ
    rw [carrierEndAlgEquiv_multiplicationDefect, map_smul, map_sub] at hMap
    have hSub :
        ZornVectorMatrix.commutator (canonicalVectorEquiv X) (canonicalVectorEquiv Y) =
          canonicalVectorEquiv (X * Y - Y * X) := by
      change ZornVectorMatrix.sub
          (ZornVectorMatrix.mul (canonicalVectorEquiv X) (canonicalVectorEquiv Y))
          (ZornVectorMatrix.mul (canonicalVectorEquiv Y) (canonicalVectorEquiv X)) =
        canonicalVectorEquiv (X * Y - Y * X)
      rw [← canonicalVectorEquiv_mul, ← canonicalVectorEquiv_mul, ← canonicalVectorEquiv_sub]
    have hLie :
        carrierEndAlgEquiv
          ⁅leftMultiplication (canonicalVectorEquiv X),
            leftMultiplication (canonicalVectorEquiv Y)⁆ =
          ⁅canonicalLeftMultiplicationMap X, canonicalLeftMultiplicationMap Y⁆ := by
      change carrierEndAlgEquiv
          (leftMultiplication (canonicalVectorEquiv X) *
            leftMultiplication (canonicalVectorEquiv Y) -
           leftMultiplication (canonicalVectorEquiv Y) *
            leftMultiplication (canonicalVectorEquiv X)) =
        canonicalLeftMultiplicationMap X * canonicalLeftMultiplicationMap Y -
          canonicalLeftMultiplicationMap Y * canonicalLeftMultiplicationMap X
      rw [map_sub, map_mul, map_mul,
        carrierEndAlgEquiv_leftMultiplication,
        carrierEndAlgEquiv_leftMultiplication]
    rw [hSub, carrierEndAlgEquiv_leftMultiplication, hLie] at hMap
    exact hMap
  rw [hComm]
  exact (LieSubalgebra.lieSpan ℝ CarrierEnd (Set.range canonicalLeftMultiplicationMap)).smul_mem
    (1 / 2 : ℝ)
    ((LieSubalgebra.lieSpan ℝ CarrierEnd (Set.range canonicalLeftMultiplicationMap)).sub_mem
      (LieSubalgebra.subset_lieSpan ⟨X * Y - Y * X, rfl⟩)
      ((LieSubalgebra.lieSpan ℝ CarrierEnd (Set.range canonicalLeftMultiplicationMap)).lie_mem
        (LieSubalgebra.subset_lieSpan ⟨X, rfl⟩)
        (LieSubalgebra.subset_lieSpan ⟨Y, rfl⟩)))

/-- Strict Lie-span enlargement directly on the five-graded endomorphism algebra `CarrierEnd`:
`LinearMap.range canonicalLeftMultiplicationMap < (LieSubalgebra.lieSpan ℝ CarrierEnd (Set.range canonicalLeftMultiplicationMap)).toSubmodule`. -/
theorem canonical_left_action_range_lt_lieSpan :
    LinearMap.range canonicalLeftMultiplicationMap <
      (LieSubalgebra.lieSpan ℝ CarrierEnd
        (Set.range canonicalLeftMultiplicationMap)).toSubmodule := by
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · intro T hT
    exact LieSubalgebra.subset_lieSpan hT
  · intro hBack
    exact canonicalMultiplicationDefect_chiralUpper01_not_mem_left_range
      (hBack (canonicalMultiplicationDefect_mem_lieSpan
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
        (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1)))

/-! ### 2. Unified Three-Pillar Synthesis Theorem -/

/-- **Three-Pillar Synthesis of Zorn Five-Grade Closure, Associator Lie Enlargement
on `CarrierEnd`, and Noncommutative-Coefficient Curvature/Bianchi Defects**: -/
theorem zorn_five_grade_associator_enlargement_and_curvature_bianchi
    {A : Type*} [Ring A]
    (T : CarrierEnd) (k : FiveGrade)
    (X Y : Z) (Xc Yc : Carrier)
    (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu rho : Fin 4) (Ψ : OperatorZornMatrix A) :
    -- Pillar 1: Zorn left/right tripotent and 5-graded endomorphism decomposition on CarrierEnd
    (peirceDefectOperator =
       (1 / 2 : ℝ) •
         (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.leftMultiplication
           InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit -
          InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.rightMultiplication
           InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) ∧
     peirceDefectOperator * peirceDefectOperator * peirceDefectOperator =
       peirceDefectOperator ∧
     fiveGradeRecomposeLinear peirceDefectOperator
       (fiveGradeDecomposeLinear peirceDefectOperator T) = T ∧
     fiveGradeRange peirceDefectOperator k =
       (LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator).eigenspace
         (fiveGradeValue k : ℝ) ∧
     LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator ^ 5 -
       (5 : ℝ) • LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator ^ 3 +
       (4 : ℝ) • LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator = 0) ∧
    -- Pillar 2: Associator multiplication defect, carrier bridge, and strict Lie-span enlargement on both Z and CarrierEnd
    (leftMultiplication X * leftMultiplication Y -
       leftMultiplication Y * leftMultiplication X =
       leftMultiplication (ZornVectorMatrix.commutator X Y) -
         2 • multiplicationDefect X Y ∧
     carrierEndAlgEquiv
       (multiplicationDefect (canonicalVectorEquiv Xc) (canonicalVectorEquiv Yc)) =
       canonicalMultiplicationDefect Xc Yc ∧
     fiveGradeDecomposeLinear peirceDefectOperator
       (canonicalMultiplicationDefect
         (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
         (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1)) ≠ 0 ∧
     LinearMap.range canonicalLeftMultiplicationMap <
       (LieSubalgebra.lieSpan ℝ CarrierEnd
         (Set.range canonicalLeftMultiplicationMap)).toSubmodule) ∧
    -- Pillar 3: Noncommutative-coefficient Zorn curvature and 6-term Akivis Bianchi identity
    (curvatureAction p Phi mu nu Ψ =
       coefficientDeriv (coefficientBracket (p mu) (p nu)) Ψ +
         fieldStrength p Phi mu nu * Ψ -
           associator (Phi mu) (Phi nu) Ψ + associator (Phi nu) (Phi mu) Ψ ∧
     bianchi p Phi mu nu rho =
       coefficientDeriv (coefficientBracket (p mu) (p nu)) (Phi rho) +
         coefficientDeriv (coefficientBracket (p nu) (p rho)) (Phi mu) +
           coefficientDeriv (coefficientBracket (p rho) (p mu)) (Phi nu) -
             associatorAlternation (Phi mu) (Phi nu) (Phi rho)) := by
  rcases zorn_tripotent_five_grade_operator_synthesis T k with
    ⟨hT1, hT2, _, _, hT5, hT6, hT7⟩
  exact ⟨⟨hT1, hT2, hT5, hT6, hT7⟩,
    ⟨leftMultiplication_commutator_defect X Y,
     carrierEndAlgEquiv_multiplicationDefect Xc Yc,
     canonicalMultiplicationDefect_fiveGradeCoordinates_ne_zero,
     canonical_left_action_range_lt_lieSpan⟩,
    ⟨curvatureAction_eq p Phi mu nu Ψ,
     bianchi_eq p Phi mu nu rho⟩⟩

end
end InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis
