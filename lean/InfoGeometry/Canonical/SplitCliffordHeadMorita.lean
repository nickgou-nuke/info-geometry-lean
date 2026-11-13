/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11GradedTensorMorita
import InfoGeometry.Canonical.SplitCliffordHeadTailParity

/-!
# Graded cancellation of the actual split-Clifford tower head

The canonical one-head factorization of the existing algebraic direct limit
is identified with two-by-two matrices over its full algebraic tail. The
canonical limit involution is proved to be the factorwise Clifford/tail parity,
so the resulting module-category equivalence uses the existing grading.

The finite matrix presentations commute with the actual fixed-head bonding
maps. All constructions concern the algebraic direct limit and its full
noncommutative coefficient algebra; no analytic completion is introduced.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct Matrix Matrix.Module

namespace InfoGeometry.Canonical.SplitCliffordHeadMorita

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordFiniteHeadTail
open InfoGeometry.Canonical.SplitCliffordHeadTailTower

/-- Removing the unique zero-dimensional last factor identifies the actual
first tower quadratic space with the matrix-side split form. -/
def splitOneIsometry : (Qsplit 1).IsometryEquiv q11 where
  toLinearEquiv := LinearEquiv.prodUnique
    (R := ℝ) (M := ℝ × ℝ) (M₂ := SplitSpace 0)
  map_app' x := by
    change q11 x.1 = Q11 x.1 + 0
    simp only [q11_eq_splitQ11, add_zero]

/-- The native Clifford algebra identification induced by that isometry. -/
def splitOneClifford : SplitClNNAlg 1 ≃ₐ[ℝ] CliffordAlgebra q11 :=
  CliffordAlgebra.equivOfIsometry splitOneIsometry

@[simp] theorem splitOneClifford_ι (x : SplitSpace 1) :
    splitOneClifford (CliffordAlgebra.ι (Qsplit 1) x) =
      CliffordAlgebra.ι q11 x.1 :=
  CliffordAlgebra.map_apply_ι _ _

private theorem cliffordMap_involute
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (f : Q →qᵢ Q') (x : CliffordAlgebra Q) :
    CliffordAlgebra.involute (CliffordAlgebra.map f x) =
      CliffordAlgebra.map f (CliffordAlgebra.involute x) := by
  have h : (CliffordAlgebra.involute (Q := Q')).comp (CliffordAlgebra.map f) =
      (CliffordAlgebra.map f).comp (CliffordAlgebra.involute (Q := Q)) := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    simp only [AlgHom.comp_apply, LinearMap.comp_apply,
      CliffordAlgebra.map_apply_ι, CliffordAlgebra.involute_ι, map_neg]
  exact AlgHom.congr_fun h x

theorem splitOneClifford_involute (x : SplitClNNAlg 1) :
    splitOneClifford (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (splitOneClifford x) :=
  (cliffordMap_involute splitOneIsometry.toIsometry x).symm

theorem splitOneClifford_mem_grade {i : ZMod 2} {x : SplitClNNAlg 1}
    (hx : x ∈ CliffordAlgebra.evenOdd (Qsplit 1) i) :
    splitOneClifford x ∈ CliffordAlgebra.evenOdd q11 i := by
  fin_cases i
  · apply (clifford_involute_eq_self_iff_mem_even q11 _).mp
    rw [← splitOneClifford_involute, CliffordAlgebra.involute_eq_of_mem_even hx]
  · apply (clifford_involute_eq_neg_iff_mem_odd q11 _).mp
    rw [← splitOneClifford_involute, CliffordAlgebra.involute_eq_of_mem_odd hx, map_neg]

section Coefficients

universe u
variable {A : Type u} [Ring A] [Algebra ℝ A]
variable (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
variable (θ : A ≃ₐ[ℝ] A)
variable (hEven : ∀ {a : A}, a ∈ 𝒜 0 → θ a = a)
variable (hOdd : ∀ {a : A}, a ∈ 𝒜 1 → θ a = -a)

/-- The one-head matrix map uses the actual tower head carrier. -/
def splitHeadMatrix :
    (CliffordAlgebra.evenOdd (Qsplit 1) ᵍ⊗[ℝ] 𝒜) →ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) A :=
  GradedTensorProduct.lift _ _
    ((head (A := A)).comp splitOneClifford.toAlgHom) (tail θ) (by
      intro i j x a
      exact head_tail_supercommute 𝒜 θ hEven hOdd
        ⟨splitOneClifford x, splitOneClifford_mem_grade x.property⟩ a)

private def headChangeLinear :
    (CliffordAlgebra.evenOdd (Qsplit 1) ᵍ⊗[ℝ] 𝒜) ≃ₗ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :=
  (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit 1)) 𝒜).symm.trans
    ((TensorProduct.congr splitOneClifford.toLinearEquiv
      (LinearEquiv.refl ℝ A)).trans
        (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜))

private theorem splitHeadMatrix_eq_linear :
    (splitHeadMatrix 𝒜 θ hEven hOdd).toLinearMap =
      ((headChangeLinear 𝒜).trans
        (tensorMatrixEquiv 𝒜 θ hEven hOdd).toLinearEquiv).toLinearMap := by
  apply GradedTensorProduct.hom_ext
  apply TensorProduct.ext'
  intro x a
  rfl

/-- Bijectivity is inherited from the proved four-unit inverse, after the
native isometric change of head carrier. -/
def splitHeadMatrixEquiv :
    (CliffordAlgebra.evenOdd (Qsplit 1) ᵍ⊗[ℝ] 𝒜) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) A :=
  AlgEquiv.ofBijective (splitHeadMatrix 𝒜 θ hEven hOdd) (by
    change Function.Bijective (splitHeadMatrix 𝒜 θ hEven hOdd).toLinearMap
    rw [splitHeadMatrix_eq_linear]
    exact ((headChangeLinear 𝒜).trans
      (tensorMatrixEquiv 𝒜 θ hEven hOdd).toLinearEquiv).bijective)

@[simp] theorem splitHeadMatrixEquiv_tmul (x : SplitClNNAlg 1) (a : A) :
    splitHeadMatrixEquiv 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a) =
      tensorMatrixEquiv 𝒜 θ hEven hOdd (splitOneClifford x ᵍ⊗ₜ a) := rfl

theorem splitHeadMatrixEquiv_tmul_entries (x : SplitClNNAlg 1) (a : A) :
    splitHeadMatrixEquiv 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a) =
      !![cl11StandardEquiv (splitOneClifford x) 0 0 • a,
         cl11StandardEquiv (splitOneClifford x) 0 1 • θ a;
         cl11StandardEquiv (splitOneClifford x) 1 0 • a,
         cl11StandardEquiv (splitOneClifford x) 1 1 • θ a] :=
  tensorToMatrix_tmul_matrix 𝒜 θ hEven hOdd _ _

/-- The native head-carrier change intertwines canonical factorwise parity. -/
theorem splitHeadMatrixEquiv_involute_tmul (x : SplitClNNAlg 1) (a : A) :
    splitHeadMatrixEquiv 𝒜 θ hEven hOdd
        (CliffordAlgebra.involute x ᵍ⊗ₜ θ a) =
      matrixGrade θ.toRingEquiv (splitHeadMatrixEquiv 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a)) := by
  rw [splitHeadMatrixEquiv_tmul, splitOneClifford_involute,
    splitHeadMatrixEquiv_tmul]
  exact tensorParity_compatible 𝒜 θ hEven hOdd (splitOneClifford x ᵍ⊗ₜ a)

end Coefficients

/-- The existing real-linear tail involution is an actual algebra automorphism. -/
def tailParity (k : ℕ) : SplitCliffordTailInfinity k ≃ₐ[ℝ] SplitCliffordTailInfinity k where
  __ := splitCliffordTailInfinityInvolute k
  toFun := splitCliffordTailInfinityInvolute k
  invFun := splitCliffordTailInfinityInvolute k
  left_inv := splitCliffordTailInfinityInvolute_involutive k
  right_inv := splitCliffordTailInfinityInvolute_involutive k
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, splitCliffordTailInfinityInvolute_smul,
      map_one]

@[simp] theorem tailParity_apply (k : ℕ) (a : SplitCliffordTailInfinity k) :
    tailParity k a = splitCliffordTailInfinityInvolute k a := rfl

theorem tailParity_even (k : ℕ) {a : SplitCliffordTailInfinity k}
    (ha : a ∈ splitCliffordTailGrade k 0) : tailParity k a = a := by
  exact ha

theorem tailParity_odd (k : ℕ) {a : SplitCliffordTailInfinity k}
    (ha : a ∈ splitCliffordTailGrade k 1) : tailParity k a = -a := by
  exact ha

/-- The canonical original-limit grade involution, bundled as an automorphism. -/
def infinityParity : SplitCliffordInfinity ≃ₐ[ℝ] SplitCliffordInfinity :=
  AlgEquiv.ofBijective splitCliffordInfinityInvolute
    (Function.Involutive.bijective splitCliffordInfinityInvolute_involutive)

@[simp] theorem infinityParity_apply (x : SplitCliffordInfinity) :
    infinityParity x = splitCliffordInfinityInvolute x := rfl

/-- Transported finite-stage parity equals the independently specified
factorwise Clifford parity. -/
theorem finiteHeadTailInvolute_tmul (k n : ℕ)
    (a : SplitClNNAlg k) (b : SplitClNNAlg n) :
    splitCliffordHeadTailStageInvolute k n (a ᵍ⊗ₜ b) =
      (CliffordAlgebra.involute a ᵍ⊗ₜ CliffordAlgebra.involute b) := by
  apply (splitCliffordFiniteHeadTailEquiv k n).symm.injective
  change (splitCliffordFiniteHeadTailEquiv k n).symm
      (splitCliffordFiniteHeadTailEquiv k n
        (CliffordAlgebra.involute
          ((splitCliffordFiniteHeadTailEquiv k n).symm (a ᵍ⊗ₜ b)))) = _
  rw [AlgEquiv.symm_apply_apply]
  change CliffordAlgebra.involute
      (CliffordAlgebra.map (splitSpaceAppendIsometry k n).symm.toIsometry
        (CliffordAlgebra.map (QuadraticMap.Isometry.inl (Qsplit k) (Qsplit n)) a *
          CliffordAlgebra.map (QuadraticMap.Isometry.inr (Qsplit k) (Qsplit n)) b)) =
    CliffordAlgebra.map (splitSpaceAppendIsometry k n).symm.toIsometry
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl (Qsplit k) (Qsplit n))
          (CliffordAlgebra.involute a) *
        CliffordAlgebra.map (QuadraticMap.Isometry.inr (Qsplit k) (Qsplit n))
          (CliffordAlgebra.involute b))
  rw [cliffordMap_involute, map_mul, cliffordMap_involute, cliffordMap_involute]

private theorem headTailLift_tmul_stage (k n : ℕ)
    (a : SplitClNNAlg k) (b : SplitClNNAlg n) :
    splitCliffordHeadTailGradedTensorLift k (a ᵍ⊗ₜ splitCliffordTailOf 0 n b) =
      splitCliffordHeadTailOf k n (a ᵍ⊗ₜ b) := by
  rw [splitCliffordHeadTailGradedTensorLift_eq_moduleEquiv_ofStage]
  exact splitCliffordHeadTailModuleEquiv_tmul_ofStage k n a b

private theorem headTailLift_involute_tmul (k : ℕ)
    (a : SplitClNNAlg k) (b : SplitCliffordTailInfinity 0) :
    splitCliffordHeadTailInfinityInvolute k
        (splitCliffordHeadTailGradedTensorLift k (a ᵍ⊗ₜ b)) =
      splitCliffordHeadTailGradedTensorLift k
        (CliffordAlgebra.involute a ᵍ⊗ₜ tailParity 0 b) := by
  induction b using DirectLimit.induction with
  | _ n b =>
      change splitCliffordHeadTailInfinityInvolute k
          (splitCliffordHeadTailGradedTensorLift k
            (a ᵍ⊗ₜ splitCliffordTailOf 0 n b)) =
        splitCliffordHeadTailGradedTensorLift k
          (CliffordAlgebra.involute a ᵍ⊗ₜ
            splitCliffordTailInfinityInvolute 0 (splitCliffordTailOf 0 n b))
      rw [splitCliffordTailInfinityInvolute_ofStage, headTailLift_tmul_stage,
        headTailLift_tmul_stage, splitCliffordHeadTailInfinityInvolute_ofStage,
        finiteHeadTailInvolute_tmul]

/-- The existing head--tail equivalence intertwines the canonical original
limit involution with factorwise Clifford/tail parity. -/
theorem headTailEquiv_involute_tmul (k : ℕ)
    (a : SplitClNNAlg k) (b : SplitCliffordTailInfinity 0) :
    infinityParity (splitCliffordInfinity_headTailGradedTensorAlgEquiv k (a ᵍ⊗ₜ b)) =
      splitCliffordInfinity_headTailGradedTensorAlgEquiv k
        (CliffordAlgebra.involute a ᵍ⊗ₜ tailParity 0 b) := by
  change splitCliffordInfinityInvolute
      (splitCliffordHeadTailInfinity_ringEquiv k
        (splitCliffordHeadTailGradedTensorLift k (a ᵍ⊗ₜ b))) =
    splitCliffordHeadTailInfinity_ringEquiv k
      (splitCliffordHeadTailGradedTensorLift k
        (CliffordAlgebra.involute a ᵍ⊗ₜ tailParity 0 b))
  have h := RingHom.congr_fun
    (splitCliffordHeadTailInfinity_ringEquiv_grade_involution k)
      (splitCliffordHeadTailGradedTensorLift k (a ᵍ⊗ₜ b))
  change splitCliffordInfinityInvolute
      (splitCliffordHeadTailInfinity_ringEquiv k
        (splitCliffordHeadTailGradedTensorLift k (a ᵍ⊗ₜ b))) =
    splitCliffordHeadTailInfinity_ringEquiv k
      (splitCliffordHeadTailInfinityInvolute k
        (splitCliffordHeadTailGradedTensorLift k (a ᵍ⊗ₜ b))) at h
  rw [h, headTailLift_involute_tmul]

/-- The actual algebraic Clifford direct limit is a matrix algebra over its
entire algebraic tail, with the existing one-head factorization reused. -/
def splitInfinityMatrixEquiv :
    SplitCliffordInfinity ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (SplitCliffordTailInfinity 0) :=
  (splitCliffordInfinity_headTailGradedTensorAlgEquiv 1).symm.trans
    (splitHeadMatrixEquiv (splitCliffordTailGrade 0) (tailParity 0)
      (tailParity_even 0) (tailParity_odd 0))

@[simp] theorem splitInfinityMatrixEquiv_headTail
    (z : CliffordAlgebra.evenOdd (Qsplit 1) ᵍ⊗[ℝ] splitCliffordTailGrade 0) :
    splitInfinityMatrixEquiv (splitCliffordInfinity_headTailGradedTensorAlgEquiv 1 z) =
      splitHeadMatrixEquiv (splitCliffordTailGrade 0) (tailParity 0)
        (tailParity_even 0) (tailParity_odd 0) z :=
  congrArg _ ((splitCliffordInfinity_headTailGradedTensorAlgEquiv 1).symm_apply_apply z)

/-- The matrix presentation preserves the canonical grading of the actual
algebraic colimit, not merely a newly transported grading. -/
theorem splitInfinityMatrixEquiv_grade (x : SplitCliffordInfinity) :
    splitInfinityMatrixEquiv (infinityParity x) =
      matrixGrade (tailParity 0).toRingEquiv (splitInfinityMatrixEquiv x) := by
  obtain ⟨z, rfl⟩ := (splitCliffordInfinity_headTailGradedTensorAlgEquiv 1).surjective x
  obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ
    (CliffordAlgebra.evenOdd (Qsplit 1)) (splitCliffordTailGrade 0)).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      change splitInfinityMatrixEquiv
          (infinityParity
            (splitCliffordInfinity_headTailGradedTensorAlgEquiv 1 (a ᵍ⊗ₜ b))) = _
      rw [headTailEquiv_involute_tmul, splitInfinityMatrixEquiv_headTail,
        splitInfinityMatrixEquiv_headTail]
      exact splitHeadMatrixEquiv_involute_tmul
        (splitCliffordTailGrade 0) (tailParity 0)
        (tailParity_even 0) (tailParity_odd 0) a b
  | add a b ha hb => simpa only [map_add, ha, hb]

/-- The actual canonical graded module category of the algebraic direct
limit reduces to modules over its full graded tail. -/
def splitInfinityGradedCancellation :
    GradedModuleCat infinityParity.toRingEquiv ≌
      GradedModuleCat (tailParity 0).toRingEquiv :=
  (ofRingEquiv infinityParity.toRingEquiv (matrixGrade (tailParity 0).toRingEquiv)
    splitInfinityMatrixEquiv.toRingEquiv splitInfinityMatrixEquiv_grade).trans
      (matrixEquivalence (tailParity 0).toRingEquiv).symm

section FiniteBonds

private def finiteParity (n : ℕ) : SplitClNNAlg n ≃ₐ[ℝ] SplitClNNAlg n :=
  CliffordAlgebra.involuteEquiv (Q := Qsplit n)

private theorem finiteParity_even (n : ℕ) {a : SplitClNNAlg n}
    (ha : a ∈ CliffordAlgebra.evenOdd (Qsplit n) 0) : finiteParity n a = a :=
  CliffordAlgebra.involute_eq_of_mem_even ha

private theorem finiteParity_odd (n : ℕ) {a : SplitClNNAlg n}
    (ha : a ∈ CliffordAlgebra.evenOdd (Qsplit n) 1) : finiteParity n a = -a :=
  CliffordAlgebra.involute_eq_of_mem_odd ha

/-- The same one-head matrix presentation at every actual finite tail stage. -/
def finiteHeadMatrixEquiv (n : ℕ) :
    SplitCliffordHeadTailStage 1 n ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (SplitClNNAlg n) :=
  splitHeadMatrixEquiv (CliffordAlgebra.evenOdd (Qsplit n)) (finiteParity n)
    (finiteParity_even n) (finiteParity_odd n)

/-- The finite matrix presentations intertwine the actual fixed-head
bonding maps with coefficientwise native matrix maps. -/
theorem finiteHeadMatrixEquiv_bond (m n : ℕ) (h : m ≤ n) :
    (finiteHeadMatrixEquiv n).toAlgHom.comp (splitCliffordHeadTailMap 1 m n h) =
      (splitCliffordMap m n h).mapMatrix.comp (finiteHeadMatrixEquiv m).toAlgHom := by
  apply AlgHom.toLinearMap_injective
  apply GradedTensorProduct.hom_ext
  apply TensorProduct.ext'
  intro a b
  have hb := LinearMap.congr_fun (splitCliffordHeadTailMap_toLinearMap 1 m n h)
    (a ᵍ⊗ₜ b)
  change splitCliffordHeadTailMap 1 m n h (a ᵍ⊗ₜ b) =
    (a ᵍ⊗ₜ splitCliffordMap m n h b) at hb
  change finiteHeadMatrixEquiv n (splitCliffordHeadTailMap 1 m n h (a ᵍ⊗ₜ b)) =
    (splitCliffordMap m n h).mapMatrix (finiteHeadMatrixEquiv m (a ᵍ⊗ₜ b))
  rw [hb]
  simp only [finiteHeadMatrixEquiv, splitHeadMatrixEquiv_tmul_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AlgHom.mapMatrix_apply, finiteParity, splitCliffordMap_involute]

end FiniteBonds

end InfoGeometry.Canonical.SplitCliffordHeadMorita
