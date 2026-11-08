/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitCliffordHeadTailTower
import InfoGeometry.Canonical.SplitCliffordTailParity

/-!
# Parity grading on the fixed-head split-Clifford colimit

The grade involutions on finite fixed-head stages induce an internal
`ZMod 2`-grading on their algebraic direct limit. This makes the colimit a
graded algebra, rather than merely a ring equipped with an involution.
-/

noncomputable section

open scoped TensorProduct

namespace InfoGeometry.Canonical.SplitCliffordHeadTailTower

open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordFiniteHeadTail
open InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower

/-- The finite Clifford head embedded at stage zero of the fixed-head limit. -/
noncomputable def splitCliffordHeadTailHeadInclusion (k : ℕ) :
    CliffordAlgebra (Qsplit k) →ₐ[ℝ] SplitCliffordHeadTailInfinity k :=
  (DirectLimit.Algebra.of (SplitCliffordHeadTailStage k)
    (fun m n h => splitCliffordHeadTailMap k m n h) 0).comp
      (GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd (Qsplit k))
        (CliffordAlgebra.evenOdd (Qsplit 0)))

/-- The head inclusion may be represented at any later fixed-head stage by
transporting its left graded-tensor inclusion along the directed-system bond. -/
theorem splitCliffordHeadTailHeadInclusion_stage (k n : ℕ)
    (a : CliffordAlgebra (Qsplit k)) :
    splitCliffordHeadTailHeadInclusion k a =
      splitCliffordHeadTailOf k n
        (splitCliffordHeadTailMap k 0 n (Nat.zero_le n)
          (GradedTensorProduct.includeLeft
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit 0)) a)) := by
  change DirectLimit.Algebra.of (SplitCliffordHeadTailStage k)
      (fun m l h => splitCliffordHeadTailMap k m l h) 0
      (GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd (Qsplit k))
        (CliffordAlgebra.evenOdd (Qsplit 0)) a) = _
  exact (DirectLimit.Ring.of_f
    (G := SplitCliffordHeadTailStage k)
    (f := fun i j hij => splitCliffordHeadTailMap k i j hij)
    (hij := Nat.zero_le n)
    (x := GradedTensorProduct.includeLeft
      (CliffordAlgebra.evenOdd (Qsplit k))
      (CliffordAlgebra.evenOdd (Qsplit 0)) a)).symm

/-- The transported bond leaves the head inclusion unchanged. -/
@[simp] theorem splitCliffordHeadTailMap_includeLeft (k n : ℕ)
    (a : CliffordAlgebra (Qsplit k)) :
    splitCliffordHeadTailMap k 0 n (Nat.zero_le n)
        (GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit 0)) a) =
      GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd (Qsplit k))
        (CliffordAlgebra.evenOdd (Qsplit n)) a := by
  have hlinear := splitCliffordHeadTailMap_toLinearMap k 0 n (Nat.zero_le n)
  have hmap := congrArg (fun f : SplitCliffordHeadTailStage k 0 →ₗ[ℝ]
      SplitCliffordHeadTailStage k n => f
        (GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit 0)) a)) hlinear
  change splitCliffordHeadTailMap k 0 n (Nat.zero_le n)
      (a ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 0))) = _ at hmap
  change splitCliffordHeadTailMap k 0 n (Nat.zero_le n)
      (a ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 0))) =
    (LinearMap.lTensor (CliffordAlgebra (Qsplit k))
      (splitCliffordMap 0 n (Nat.zero_le n)).toLinearMap)
      (a ⊗ₜ[ℝ] (1 : CliffordAlgebra (Qsplit 0))) at hmap
  rw [LinearMap.lTensor_tmul] at hmap
  have hOne :
      (splitCliffordMap 0 n (Nat.zero_le n)).toLinearMap 1 =
        (1 : SplitClNNAlg n) := (splitCliffordMap 0 n (Nat.zero_le n)).map_one
  rw [hOne] at hmap
  change splitCliffordHeadTailMap k 0 n (Nat.zero_le n)
      (a ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 0))) =
    a ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) at hmap
  exact hmap

/-- At a finite fixed-head stage, elements from the head and tail factors
supercommute with the sign prescribed by their `ZMod 2` degrees. -/
theorem splitCliffordHeadTailStage_inclusions_supercommute (k n : ℕ)
    {i j : ZMod 2} (a : CliffordAlgebra.evenOdd (Qsplit k) i)
    (b : CliffordAlgebra.evenOdd (Qsplit (n + 0)) j) :
    GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd (Qsplit k))
        (CliffordAlgebra.evenOdd (Qsplit (n + 0))) a *
      GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd (Qsplit k))
        (CliffordAlgebra.evenOdd (Qsplit (n + 0))) b =
      (-1 : ℤˣ) ^ (j * i) •
        (GradedTensorProduct.includeRight
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit (n + 0))) b *
          GradedTensorProduct.includeLeft
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit (n + 0))) a) := by
  let uHead : CliffordAlgebra.evenOdd (Qsplit k) 0 := 1
  let uTail : CliffordAlgebra.evenOdd (Qsplit (n + 0)) 0 := 1
  change ((a : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ
        ((uTail : CliffordAlgebra.evenOdd (Qsplit (n + 0)) 0) : CliffordAlgebra (Qsplit (n + 0)))) *
      (((uHead : CliffordAlgebra.evenOdd (Qsplit k) 0) : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ
        (b : CliffordAlgebra (Qsplit (n + 0)))) =
    (-1 : ℤˣ) ^ (j * i) •
      ((((uHead : CliffordAlgebra.evenOdd (Qsplit k) 0) : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ
          (b : CliffordAlgebra (Qsplit (n + 0)))) *
        ((a : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ
          ((uTail : CliffordAlgebra.evenOdd (Qsplit (n + 0)) 0) : CliffordAlgebra (Qsplit (n + 0)))))
  rw [GradedTensorProduct.tmul_zero_coe_mul_coe_tmul,
    GradedTensorProduct.tmul_coe_mul_coe_tmul]
  simp [uHead, uTail, smul_smul, Int.units_mul_self]

/-- Stage maps for the infinite tail factor, represented in fixed-head
coordinates by the right graded-tensor inclusion. -/
private noncomputable def splitCliffordHeadTailTailStageMap (k n : ℕ) :
    SplitClNNAlg (n + 0) →ₐ[ℝ] SplitCliffordHeadTailInfinity k :=
  (DirectLimit.Algebra.of (SplitCliffordHeadTailStage k)
    (fun m l h => splitCliffordHeadTailMap k m l h) n).comp
      (GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd (Qsplit k))
        (CliffordAlgebra.evenOdd (Qsplit (n + 0))))

/-- The tail-stage maps commute with the respective Clifford tower bonds. -/
private theorem splitCliffordHeadTailTailStageMap_natural (k m n : ℕ)
    (h : m ≤ n) (x : SplitClNNAlg (m + 0)) :
    splitCliffordHeadTailTailStageMap k n
        (splitCliffordMap (m + 0) (n + 0)
          (Nat.add_le_add_right h 0) x) =
      splitCliffordHeadTailTailStageMap k m x := by
  have hlinear := splitCliffordHeadTailMap_toLinearMap k m n h
  have hstage :
      splitCliffordHeadTailMap k m n h
          (GradedTensorProduct.includeRight
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit m)) x) =
        GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit n))
          (splitCliffordMap m n h x) := by
    have hmap := congrArg (fun f : SplitCliffordHeadTailStage k m →ₗ[ℝ]
        SplitCliffordHeadTailStage k n => f
          (GradedTensorProduct.includeRight
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit m)) x)) hlinear
    change splitCliffordHeadTailMap k m n h
        ((1 : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ x) =
      (LinearMap.lTensor (CliffordAlgebra (Qsplit k))
        (splitCliffordMap m n h).toLinearMap)
        ((1 : CliffordAlgebra (Qsplit k)) ⊗ₜ[ℝ] x) at hmap
    rw [LinearMap.lTensor_tmul] at hmap
    exact hmap
  change splitCliffordHeadTailOf k n
      (GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd (Qsplit k))
        (CliffordAlgebra.evenOdd (Qsplit n))
        (splitCliffordMap m n h x)) =
    splitCliffordHeadTailOf k m
      (GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd (Qsplit k))
        (CliffordAlgebra.evenOdd (Qsplit m)) x)
  calc
    _ = splitCliffordHeadTailOf k n
        (splitCliffordHeadTailMap k m n h
          (GradedTensorProduct.includeRight
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit m)) x)) := by
          exact congrArg (splitCliffordHeadTailOf k n) hstage.symm
    _ = _ := DirectLimit.Ring.of_f
      (G := SplitCliffordHeadTailStage k)
      (f := fun i j hij => splitCliffordHeadTailMap k i j hij)
      (hij := h) _

/-- The canonical algebra map from the infinite tail into the fixed-head
colimit. -/
noncomputable def splitCliffordHeadTailTailInclusion (k : ℕ) :
    SplitCliffordTailInfinity 0 →ₐ[ℝ] SplitCliffordHeadTailInfinity k :=
  DirectLimit.Algebra.lift (fun n : ℕ => SplitClNNAlg (n + 0))
    (fun m n h => splitCliffordMap (m + 0) (n + 0)
      (Nat.add_le_add_right h 0))
    (SplitCliffordHeadTailInfinity k)
    (splitCliffordHeadTailTailStageMap k)
    (splitCliffordHeadTailTailStageMap_natural k)

/-- The tail inclusion on a finite representative is the right graded-tensor
inclusion at the corresponding fixed-head stage. -/
@[simp] theorem splitCliffordHeadTailTailInclusion_ofStage (k n : ℕ)
    (x : SplitClNNAlg (n + 0)) :
    splitCliffordHeadTailTailInclusion k
        (splitCliffordTailOf 0 n x) =
      splitCliffordHeadTailOf k n
        (GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit (n + 0))) x) := by
  change DirectLimit.Algebra.lift _ _ _
      (splitCliffordHeadTailTailStageMap k)
      (splitCliffordHeadTailTailStageMap_natural k)
      (DirectLimit.Algebra.of _ _ n x) = _
  rw [DirectLimit.Algebra.lift_of]
  rfl

/-- The two canonical factor maps supercommute according to their grades. -/
theorem splitCliffordHeadTailInclusions_supercommute (k : ℕ)
    {i j : ZMod 2} (a : CliffordAlgebra.evenOdd (Qsplit k) i)
    (b : splitCliffordTailGrade 0 j) :
    splitCliffordHeadTailHeadInclusion k a *
        splitCliffordHeadTailTailInclusion k b =
      (-1 : ℤˣ) ^ (j * i) •
        (splitCliffordHeadTailTailInclusion k b *
          splitCliffordHeadTailHeadInclusion k a) := by
  fin_cases j
  · obtain ⟨n, x, hx, hgrade⟩ :=
      (splitCliffordTailInfinity_fixed_iff_exists_even_stage 0 b).mp b.property
    let bStage : CliffordAlgebra.evenOdd (Qsplit (n + 0)) 0 := ⟨x, hgrade⟩
    have hfinite := splitCliffordHeadTailStage_inclusions_supercommute
      k n a bStage
    have hhead : splitCliffordHeadTailHeadInclusion k a =
        splitCliffordHeadTailOf k n
          (GradedTensorProduct.includeLeft
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit (n + 0))) a) := by
      rw [splitCliffordHeadTailHeadInclusion_stage,
        splitCliffordHeadTailMap_includeLeft]
      rfl
    have htail := splitCliffordHeadTailTailInclusion_ofStage k n x
    rw [hx] at htail
    have hstage := congrArg (splitCliffordHeadTailOf k n) hfinite
    simp only [map_mul, Units.smul_def, map_zsmul] at hstage
    calc
      splitCliffordHeadTailHeadInclusion k a *
          splitCliffordHeadTailTailInclusion k b =
        splitCliffordHeadTailOf k n
          (GradedTensorProduct.includeLeft
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit (n + 0))) a) *
          splitCliffordHeadTailOf k n
            (GradedTensorProduct.includeRight
              (CliffordAlgebra.evenOdd (Qsplit k))
              (CliffordAlgebra.evenOdd (Qsplit (n + 0))) bStage) := by
              rw [hhead, htail]
      _ = (-1 : ℤˣ) ^ ((0 : ZMod 2) * i) •
            (splitCliffordHeadTailTailInclusion k b *
              splitCliffordHeadTailHeadInclusion k a) := by
            rw [hhead, htail]
            simpa [bStage, Units.smul_def] using hstage
      _ = (-1 : ℤˣ) ^ ((0 : ZMod 2) * i) •
            (splitCliffordHeadTailTailInclusion k b *
              splitCliffordHeadTailHeadInclusion k a) := rfl
  · obtain ⟨n, x, hx, hgrade⟩ :=
      (splitCliffordTailInfinity_negated_iff_exists_odd_stage 0 b).mp b.property
    let bStage : CliffordAlgebra.evenOdd (Qsplit (n + 0)) 1 := ⟨x, hgrade⟩
    have hfinite := splitCliffordHeadTailStage_inclusions_supercommute
      k n a bStage
    have hhead : splitCliffordHeadTailHeadInclusion k a =
        splitCliffordHeadTailOf k n
          (GradedTensorProduct.includeLeft
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit (n + 0))) a) := by
      rw [splitCliffordHeadTailHeadInclusion_stage,
        splitCliffordHeadTailMap_includeLeft]
      rfl
    have htail := splitCliffordHeadTailTailInclusion_ofStage k n x
    rw [hx] at htail
    have hstage := congrArg (splitCliffordHeadTailOf k n) hfinite
    simp only [map_mul, Units.smul_def, map_zsmul] at hstage
    calc
      splitCliffordHeadTailHeadInclusion k a *
          splitCliffordHeadTailTailInclusion k b =
        splitCliffordHeadTailOf k n
          (GradedTensorProduct.includeLeft
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit (n + 0))) a) *
          splitCliffordHeadTailOf k n
            (GradedTensorProduct.includeRight
              (CliffordAlgebra.evenOdd (Qsplit k))
              (CliffordAlgebra.evenOdd (Qsplit (n + 0))) bStage) := by
              rw [hhead, htail]
      _ = (-1 : ℤˣ) ^ ((1 : ZMod 2) * i) •
            (splitCliffordHeadTailTailInclusion k b *
              splitCliffordHeadTailHeadInclusion k a) := by
            rw [hhead, htail]
            simpa [bStage, Units.smul_def] using hstage
      _ = (-1 : ℤˣ) ^ ((1 : ZMod 2) * i) •
            (splitCliffordHeadTailTailInclusion k b *
              splitCliffordHeadTailHeadInclusion k a) := rfl

/-- The fixed-head colimit receives the canonical algebra map from the
graded tensor product of the finite head and infinite cofinal tail. -/
noncomputable def splitCliffordHeadTailGradedTensorLift (k : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit k) ᵍ⊗[ℝ]
      splitCliffordTailGrade 0) →ₐ[ℝ] SplitCliffordHeadTailInfinity k :=
  GradedTensorProduct.lift _ _
    (splitCliffordHeadTailHeadInclusion k)
    (splitCliffordHeadTailTailInclusion k)
    (by
      intro i j a b
      exact splitCliffordHeadTailInclusions_supercommute k a b)

/-- The existing head--tail colimit module equivalence, expressed on the
underlying module of the graded tensor product. -/
noncomputable def splitCliffordHeadTailGradedTensorModuleEquiv (k : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit k) ᵍ⊗[ℝ]
      splitCliffordTailGrade 0) ≃ₗ[ℝ] SplitCliffordHeadTailInfinity k := by
  let tailToBase : SplitCliffordTailInfinity 0 ≃ₗ[ℝ] SplitCliffordInfinity :=
    LinearEquiv.refl ℝ _
  exact (GradedTensorProduct.of ℝ
      (CliffordAlgebra.evenOdd (Qsplit k)) (splitCliffordTailGrade 0)).symm.trans
    ((TensorProduct.congr (LinearEquiv.refl ℝ (CliffordAlgebra (Qsplit k)))
      tailToBase).trans (splitCliffordHeadTailModuleEquiv k))

/-- On a pure tensor, the graded tensor lift multiplies the canonical head
and tail images in that order. -/
@[simp] theorem splitCliffordHeadTailGradedTensorLift_tmul (k : ℕ)
    (a : CliffordAlgebra (Qsplit k)) (b : SplitCliffordTailInfinity 0) :
    splitCliffordHeadTailGradedTensorLift k (a ᵍ⊗ₜ b) =
      splitCliffordHeadTailHeadInclusion k a *
        splitCliffordHeadTailTailInclusion k b := by
  simp [splitCliffordHeadTailGradedTensorLift,
    GradedTensorProduct.lift_tmul]

/-- On every finite tail representative, the graded algebra lift agrees with
the canonical head--tail module equivalence. -/
theorem splitCliffordHeadTailGradedTensorLift_eq_moduleEquiv_ofStage
    (k n : ℕ) (a : CliffordAlgebra (Qsplit k)) (x : SplitClNNAlg n) :
    splitCliffordHeadTailGradedTensorLift k
        (a ᵍ⊗ₜ splitCliffordTailOf 0 n x) =
      splitCliffordHeadTailGradedTensorModuleEquiv k
        (a ᵍ⊗ₜ splitCliffordTailOf 0 n x) := by
  have hHead : splitCliffordHeadTailHeadInclusion k a =
      splitCliffordHeadTailOf k n
        (GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit n)) a) := by
    rw [splitCliffordHeadTailHeadInclusion_stage,
      splitCliffordHeadTailMap_includeLeft]
  have hTail := splitCliffordHeadTailTailInclusion_ofStage k n x
  have hTail' : splitCliffordHeadTailTailInclusion k
      (splitCliffordTailOf 0 n x) =
      splitCliffordHeadTailOf k n
        (GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit n)) x) := by
    simpa using hTail
  calc
    splitCliffordHeadTailGradedTensorLift k
        (a ᵍ⊗ₜ splitCliffordTailOf 0 n x) =
      splitCliffordHeadTailHeadInclusion k a *
        splitCliffordHeadTailTailInclusion k (splitCliffordTailOf 0 n x) := by
          rw [splitCliffordHeadTailGradedTensorLift_tmul]
    _ = splitCliffordHeadTailOf k n
          (GradedTensorProduct.includeLeft
              (CliffordAlgebra.evenOdd (Qsplit k))
              (CliffordAlgebra.evenOdd (Qsplit n)) a *
            GradedTensorProduct.includeRight
              (CliffordAlgebra.evenOdd (Qsplit k))
              (CliffordAlgebra.evenOdd (Qsplit n)) x) := by
          rw [hHead, hTail', map_mul]
    _ = splitCliffordHeadTailOf k n (a ᵍ⊗ₜ x) := by
          congr 1
          change (a ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n))) *
              ((1 : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ x) = a ᵍ⊗ₜ x
          exact GradedTensorProduct.tmul_one_mul_one_tmul
            (CliffordAlgebra.evenOdd (Qsplit k))
            (CliffordAlgebra.evenOdd (Qsplit n)) a x
    _ = splitCliffordHeadTailGradedTensorModuleEquiv k
          (a ᵍ⊗ₜ splitCliffordTailOf 0 n x) := by
          symm
          exact splitCliffordHeadTailModuleEquiv_tmul_ofStage k n a x

/-- The graded algebra lift is the canonical module equivalence on the whole
graded tensor product, since the two maps agree on every finite tail stage. -/
theorem splitCliffordHeadTailGradedTensorLift_eq_moduleEquiv (k : ℕ) :
    (splitCliffordHeadTailGradedTensorLift k).toLinearMap =
      (splitCliffordHeadTailGradedTensorModuleEquiv k).toLinearMap := by
  apply GradedTensorProduct.hom_ext
  apply TensorProduct.ext'
  intro a b
  induction b using DirectLimit.induction with
  | _ n x =>
      change splitCliffordHeadTailGradedTensorLift k
          (a ᵍ⊗ₜ splitCliffordTailOf 0 n x) =
        splitCliffordHeadTailGradedTensorModuleEquiv k
          (a ᵍ⊗ₜ splitCliffordTailOf 0 n x)
      exact splitCliffordHeadTailGradedTensorLift_eq_moduleEquiv_ofStage
        k n a x

/-- The graded algebra lift is bijective because it is the canonical module
equivalence on the underlying real vector spaces. -/
theorem splitCliffordHeadTailGradedTensorLift_bijective (k : ℕ) :
    Function.Bijective (splitCliffordHeadTailGradedTensorLift k) := by
  change Function.Bijective
    (splitCliffordHeadTailGradedTensorLift k).toLinearMap
  rw [splitCliffordHeadTailGradedTensorLift_eq_moduleEquiv]
  exact (splitCliffordHeadTailGradedTensorModuleEquiv k).bijective

/-- The fixed-head split-Clifford limit is the graded tensor product of its
finite head and cofinal infinite tail, as an `ℝ`-algebra. -/
noncomputable def splitCliffordHeadTailGradedTensorAlgEquiv (k : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit k) ᵍ⊗[ℝ]
      splitCliffordTailGrade 0) ≃ₐ[ℝ] SplitCliffordHeadTailInfinity k :=
  AlgEquiv.ofBijective (splitCliffordHeadTailGradedTensorLift k)
    (splitCliffordHeadTailGradedTensorLift_bijective k)

/-- The original split-Clifford algebraic direct limit is the graded tensor
algebra of a finite head and the offset-zero infinite Clifford tail. -/
noncomputable def splitCliffordInfinity_headTailGradedTensorAlgEquiv (k : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit k) ᵍ⊗[ℝ]
      splitCliffordTailGrade 0) ≃ₐ[ℝ] SplitCliffordInfinity :=
  (splitCliffordHeadTailGradedTensorAlgEquiv k).trans
    (splitCliffordHeadTailInfinity_algEquiv k)

/-- Reindexing a cofinal tail is a real-algebra equivalence, obtained by
passing through the original split-Clifford direct limit. -/
noncomputable def splitCliffordTailInfinityAlgEquiv (k l : ℕ) :
    SplitCliffordTailInfinity k ≃ₐ[ℝ] SplitCliffordTailInfinity l :=
  (splitCliffordInfinity_alg_shift_equiv k).symm.trans
    (splitCliffordInfinity_alg_shift_equiv l)

/-- The cofinal-tail algebra equivalence intertwines the induced Clifford
grade involutions. -/
theorem splitCliffordTailInfinityAlgEquiv_grade (k l : ℕ)
    (x : SplitCliffordTailInfinity k) :
    splitCliffordTailInfinityInvolute l
        (splitCliffordTailInfinityAlgEquiv k l x) =
      splitCliffordTailInfinityAlgEquiv k l
        (splitCliffordTailInfinityInvolute k x) := by
  have h := splitCliffordTailInfinity_ring_shift_equiv_grade_involution k l
  exact RingHom.congr_fun h x

/-- Reversing the two cofinal-tail shifts gives the inverse algebra
equivalence. -/
theorem splitCliffordTailInfinityAlgEquiv_symm (k l : ℕ) :
    splitCliffordTailInfinityAlgEquiv l k =
      (splitCliffordTailInfinityAlgEquiv k l).symm := by
  ext x
  simp [splitCliffordTailInfinityAlgEquiv, AlgEquiv.trans_apply]

/-- The cofinal-tail algebra equivalence preserves each even/odd sector. -/
theorem splitCliffordTailInfinityAlgEquiv_mem_grade (k l : ℕ)
    (p : ZMod 2) {x : SplitCliffordTailInfinity k}
    (hx : x ∈ splitCliffordTailGrade k p) :
    splitCliffordTailInfinityAlgEquiv k l x ∈ splitCliffordTailGrade l p := by
  fin_cases p
  · change splitCliffordTailInfinityInvolute k x = x at hx
    change splitCliffordTailInfinityInvolute l
        (splitCliffordTailInfinityAlgEquiv k l x) =
      splitCliffordTailInfinityAlgEquiv k l x
    rw [splitCliffordTailInfinityAlgEquiv_grade, hx]
  · change splitCliffordTailInfinityInvolute k x = -x at hx
    change splitCliffordTailInfinityInvolute l
        (splitCliffordTailInfinityAlgEquiv k l x) =
      -splitCliffordTailInfinityAlgEquiv k l x
    rw [splitCliffordTailInfinityAlgEquiv_grade, hx, map_neg]

/-- The canonical factor inclusions into a graded tensor product
supercommute according to the two homogeneous degrees. -/
theorem splitCliffordGradedTensorInclusions_supercommute
    (h l : ℕ) {i j : ZMod 2}
    (a : CliffordAlgebra.evenOdd (Qsplit h) i)
    (b : splitCliffordTailGrade l j) :
    GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) a *
        GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) b =
      (-1 : ℤˣ) ^ (j * i) •
        (GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) b *
          GradedTensorProduct.includeLeft
            (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) a) := by
  change ((a : CliffordAlgebra (Qsplit h)) ᵍ⊗ₜ
      (1 : SplitCliffordTailInfinity l)) *
    ((1 : CliffordAlgebra (Qsplit h)) ᵍ⊗ₜ
      (b : SplitCliffordTailInfinity l)) =
    (-1 : ℤˣ) ^ (j * i) •
      (((1 : CliffordAlgebra (Qsplit h)) ᵍ⊗ₜ
          (b : SplitCliffordTailInfinity l)) *
        ((a : CliffordAlgebra (Qsplit h)) ᵍ⊗ₜ
          (1 : SplitCliffordTailInfinity l)))
  rw [GradedTensorProduct.tmul_one_mul_one_tmul,
    GradedTensorProduct.tmul_coe_mul_coe_tmul]
  simp only [one_mul, mul_one]
  rw [smul_smul, ← uzpow_add]
  have hExp : (j * i) + (j * i) = 0 := by
    fin_cases i <;> fin_cases j <;> rfl
  rw [hExp, uzpow_zero, one_smul]

/-- The grading-preserving tail equivalence transports the supercommutation
law between the fixed head and tail factors. -/
theorem splitCliffordHeadTailTailTransport_anticommutes
    (h k l : ℕ) {i j : ZMod 2}
    (a : CliffordAlgebra.evenOdd (Qsplit h) i)
    (b : splitCliffordTailGrade k j) :
    GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) a *
        ((GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l)).comp
            (splitCliffordTailInfinityAlgEquiv k l).toAlgHom) b =
      (-1 : ℤˣ) ^ (j * i) •
        (((GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l)).comp
            (splitCliffordTailInfinityAlgEquiv k l).toAlgHom) b *
          GradedTensorProduct.includeLeft
            (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) a) := by
  change GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) a *
      GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l)
        (splitCliffordTailInfinityAlgEquiv k l b) =
    (-1 : ℤˣ) ^ (j * i) •
      (GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l)
        (splitCliffordTailInfinityAlgEquiv k l b) *
        GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) a)
  exact splitCliffordGradedTensorInclusions_supercommute h l a
    ⟨splitCliffordTailInfinityAlgEquiv k l b,
      splitCliffordTailInfinityAlgEquiv_mem_grade k l j b.property⟩

/-- The cofinal-tail algebra equivalence induces a homomorphism between
graded tensor products while leaving the finite head fixed. -/
noncomputable def splitCliffordHeadTailTailTransport (h k l : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
      splitCliffordTailGrade k) →ₐ[ℝ]
        (CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
          splitCliffordTailGrade l) :=
  GradedTensorProduct.lift _ _
    (GradedTensorProduct.includeLeft
      (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l))
    ((GradedTensorProduct.includeRight
      (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l)).comp
        (splitCliffordTailInfinityAlgEquiv k l).toAlgHom)
    (fun {i j} a b => splitCliffordHeadTailTailTransport_anticommutes
      h k l (i := i) (j := j) a b)

@[simp] theorem splitCliffordHeadTailTailTransport_includeLeft
    (h k l : ℕ) (a : CliffordAlgebra (Qsplit h)) :
    splitCliffordHeadTailTailTransport h k l
        (GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade k) a) =
      GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) a := by
  change GradedTensorProduct.lift _ _ _ _
      (fun {i j} a b => splitCliffordHeadTailTailTransport_anticommutes
        h k l (i := i) (j := j) a b)
      (a ᵍ⊗ₜ (1 : SplitCliffordTailInfinity k)) = _
  rw [GradedTensorProduct.lift_tmul]
  simp [GradedTensorProduct.tmul_one_mul_one_tmul]

@[simp] theorem splitCliffordHeadTailTailTransport_includeRight
    (h k l : ℕ) (b : SplitCliffordTailInfinity k) :
    splitCliffordHeadTailTailTransport h k l
        (GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade k) b) =
      GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l)
        (splitCliffordTailInfinityAlgEquiv k l b) := by
  change GradedTensorProduct.lift _ _ _ _
      (fun {i j} a b => splitCliffordHeadTailTailTransport_anticommutes
        h k l (i := i) (j := j) a b)
      ((1 : CliffordAlgebra (Qsplit h)) ᵍ⊗ₜ b) = _
  rw [GradedTensorProduct.lift_tmul]
  simp [GradedTensorProduct.tmul_one_mul_one_tmul]

@[simp] theorem splitCliffordHeadTailTailTransport_tmul
    (h k l : ℕ) (a : CliffordAlgebra (Qsplit h))
    (b : SplitCliffordTailInfinity k) :
    splitCliffordHeadTailTailTransport h k l (a ᵍ⊗ₜ b) =
      (GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l) a) *
      (GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd (Qsplit h)) (splitCliffordTailGrade l)
        (splitCliffordTailInfinityAlgEquiv k l b)) := by
  simp [splitCliffordHeadTailTailTransport,
    GradedTensorProduct.lift_tmul]

theorem splitCliffordHeadTailTailTransport_left_inverse (h k l : ℕ) :
    (splitCliffordHeadTailTailTransport h l k).toLinearMap.comp
        (splitCliffordHeadTailTailTransport h k l).toLinearMap =
      LinearMap.id := by
  apply GradedTensorProduct.hom_ext
  apply TensorProduct.ext'
  intro a b
  induction b using DirectLimit.induction with
  | _ n y =>
      change splitCliffordHeadTailTailTransport h l k
          (splitCliffordHeadTailTailTransport h k l
            (a ᵍ⊗ₜ splitCliffordTailOf k n y)) =
        a ᵍ⊗ₜ splitCliffordTailOf k n y
      simp [splitCliffordHeadTailTailTransport_tmul,
        GradedTensorProduct.tmul_one_mul_one_tmul,
        splitCliffordTailInfinityAlgEquiv]

theorem splitCliffordHeadTailTailTransport_bijective (h k l : ℕ) :
    Function.Bijective (splitCliffordHeadTailTailTransport h k l) := by
  constructor
  · intro x y hxy
    have hx := congrArg
      (fun f : CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
          splitCliffordTailGrade k →ₗ[ℝ]
          CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
            splitCliffordTailGrade k => f x)
      (splitCliffordHeadTailTailTransport_left_inverse h k l)
    have hy := congrArg (splitCliffordHeadTailTailTransport h l k) hxy
    have hx' : splitCliffordHeadTailTailTransport h l k
        (splitCliffordHeadTailTailTransport h k l x) = x := by
      simpa [LinearMap.comp_apply] using hx
    have hy' : splitCliffordHeadTailTailTransport h l k
        (splitCliffordHeadTailTailTransport h k l y) = y := by
      have hyEq := congrArg
        (fun f : CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
            splitCliffordTailGrade k →ₗ[ℝ]
            CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
              splitCliffordTailGrade k => f y)
        (splitCliffordHeadTailTailTransport_left_inverse h k l)
      simpa [LinearMap.comp_apply] using hyEq
    exact hx'.symm.trans (hy.trans hy')
  · intro y
    refine ⟨splitCliffordHeadTailTailTransport h l k y, ?_⟩
    have hright := congrArg
      (fun f : CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
          splitCliffordTailGrade l →ₗ[ℝ]
          CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
            splitCliffordTailGrade l => f y)
      (splitCliffordHeadTailTailTransport_left_inverse h l k)
    simpa [LinearMap.comp_apply] using hright

/-- Reindexing a cofinal tail induces an algebra equivalence on the graded
tensor product while leaving the finite Clifford head fixed. -/
noncomputable def splitCliffordHeadTailTailAlgEquiv (h k l : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
      splitCliffordTailGrade k) ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd (Qsplit h) ᵍ⊗[ℝ]
          splitCliffordTailGrade l) :=
  AlgEquiv.ofBijective (splitCliffordHeadTailTailTransport h k l)
    (splitCliffordHeadTailTailTransport_bijective h k l)

theorem splitCliffordHeadTailInfinityInvolute_smul (k : ℕ) (r : ℝ)
    (x : SplitCliffordHeadTailInfinity k) :
    splitCliffordHeadTailInfinityInvolute k (r • x) =
      r • splitCliffordHeadTailInfinityInvolute k x := by
  induction x using DirectLimit.induction with
  | _ n a =>
      change splitCliffordHeadTailInfinityInvolute k
          (splitCliffordHeadTailOf k n (r • a)) =
        r • splitCliffordHeadTailInfinityInvolute k
          (splitCliffordHeadTailOf k n a)
      rw [splitCliffordHeadTailInfinityInvolute_ofStage,
        splitCliffordHeadTailInfinityInvolute_ofStage]
      change DirectLimit.Module.of ℝ ℕ (SplitCliffordHeadTailStage k)
          (fun i j h => (splitCliffordHeadTailMap k i j h).toLinearMap) n
          (splitCliffordFiniteHeadTailEquiv k n
            (CliffordAlgebra.involute
              ((splitCliffordFiniteHeadTailEquiv k n).symm (r • a)))) =
        r • DirectLimit.Module.of ℝ ℕ (SplitCliffordHeadTailStage k)
          (fun i j h => (splitCliffordHeadTailMap k i j h).toLinearMap) n
          (splitCliffordFiniteHeadTailEquiv k n
            (CliffordAlgebra.involute
              ((splitCliffordFiniteHeadTailEquiv k n).symm a)))
      have hstage :
          splitCliffordFiniteHeadTailEquiv k n
              (CliffordAlgebra.involute
                ((splitCliffordFiniteHeadTailEquiv k n).symm (r • a))) =
            r • splitCliffordFiniteHeadTailEquiv k n
              (CliffordAlgebra.involute
                ((splitCliffordFiniteHeadTailEquiv k n).symm a)) := by
        simp only [map_smul]
      rw [hstage]
      exact (DirectLimit.Module.of ℝ ℕ (SplitCliffordHeadTailStage k)
        (fun i j h => (splitCliffordHeadTailMap k i j h).toLinearMap) n).map_smul r _

/-- Even elements fixed by the induced Clifford grade involution. -/
def splitCliffordHeadTailEven (k : ℕ) :
    Submodule ℝ (SplitCliffordHeadTailInfinity k) where
  carrier := {x | splitCliffordHeadTailInfinityInvolute k x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change splitCliffordHeadTailInfinityInvolute k (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change splitCliffordHeadTailInfinityInvolute k (r • x) = r • x
    rw [splitCliffordHeadTailInfinityInvolute_smul, hx]

/-- Odd elements negated by the induced Clifford grade involution. -/
def splitCliffordHeadTailOdd (k : ℕ) :
    Submodule ℝ (SplitCliffordHeadTailInfinity k) where
  carrier := {x | splitCliffordHeadTailInfinityInvolute k x = -x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change splitCliffordHeadTailInfinityInvolute k (x + y) = -(x + y)
    rw [map_add, hx, hy, neg_add]
  smul_mem' := by
    intro r x hx
    change splitCliffordHeadTailInfinityInvolute k (r • x) = -(r • x)
    rw [splitCliffordHeadTailInfinityInvolute_smul, hx, smul_neg]

/-- Even projection associated with the fixed-head grade involution. -/
def splitCliffordHeadTailEvenPart (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k) : SplitCliffordHeadTailInfinity k :=
  (2 : ℝ)⁻¹ • (x + splitCliffordHeadTailInfinityInvolute k x)

/-- Odd projection associated with the fixed-head grade involution. -/
def splitCliffordHeadTailOddPart (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k) : SplitCliffordHeadTailInfinity k :=
  (2 : ℝ)⁻¹ • (x - splitCliffordHeadTailInfinityInvolute k x)

theorem splitCliffordHeadTailEvenPart_mem (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k) :
    splitCliffordHeadTailEvenPart k x ∈ splitCliffordHeadTailEven k := by
  change splitCliffordHeadTailInfinityInvolute k
      (splitCliffordHeadTailEvenPart k x) = splitCliffordHeadTailEvenPart k x
  unfold splitCliffordHeadTailEvenPart
  rw [splitCliffordHeadTailInfinityInvolute_smul, map_add,
    splitCliffordHeadTailInfinityInvolute_involutive]
  module

theorem splitCliffordHeadTailOddPart_mem (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k) :
    splitCliffordHeadTailOddPart k x ∈ splitCliffordHeadTailOdd k := by
  change splitCliffordHeadTailInfinityInvolute k
      (splitCliffordHeadTailOddPart k x) = -splitCliffordHeadTailOddPart k x
  unfold splitCliffordHeadTailOddPart
  rw [splitCliffordHeadTailInfinityInvolute_smul, map_sub,
    splitCliffordHeadTailInfinityInvolute_involutive]
  module

theorem splitCliffordHeadTailEvenPart_add_oddPart (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k) :
    splitCliffordHeadTailEvenPart k x + splitCliffordHeadTailOddPart k x = x := by
  unfold splitCliffordHeadTailEvenPart splitCliffordHeadTailOddPart
  module

theorem splitCliffordHeadTailEvenPart_of_mem (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k)
    (hx : x ∈ splitCliffordHeadTailEven k) :
    splitCliffordHeadTailEvenPart k x = x := by
  change splitCliffordHeadTailInfinityInvolute k x = x at hx
  unfold splitCliffordHeadTailEvenPart
  rw [hx]
  module

theorem splitCliffordHeadTailEvenPart_of_odd (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k)
    (hx : x ∈ splitCliffordHeadTailOdd k) :
    splitCliffordHeadTailEvenPart k x = 0 := by
  change splitCliffordHeadTailInfinityInvolute k x = -x at hx
  unfold splitCliffordHeadTailEvenPart
  rw [hx]
  module

theorem splitCliffordHeadTailOddPart_of_mem (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k)
    (hx : x ∈ splitCliffordHeadTailOdd k) :
    splitCliffordHeadTailOddPart k x = x := by
  change splitCliffordHeadTailInfinityInvolute k x = -x at hx
  unfold splitCliffordHeadTailOddPart
  rw [hx]
  module

theorem splitCliffordHeadTailOddPart_of_even (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k)
    (hx : x ∈ splitCliffordHeadTailEven k) :
    splitCliffordHeadTailOddPart k x = 0 := by
  change splitCliffordHeadTailInfinityInvolute k x = x at hx
  unfold splitCliffordHeadTailOddPart
  rw [hx]
  module

theorem splitCliffordHeadTailEvenPart_add (k : ℕ)
    (x y : SplitCliffordHeadTailInfinity k) :
    splitCliffordHeadTailEvenPart k (x + y) =
      splitCliffordHeadTailEvenPart k x + splitCliffordHeadTailEvenPart k y := by
  unfold splitCliffordHeadTailEvenPart
  rw [map_add]
  module

theorem splitCliffordHeadTailOddPart_add (k : ℕ)
    (x y : SplitCliffordHeadTailInfinity k) :
    splitCliffordHeadTailOddPart k (x + y) =
      splitCliffordHeadTailOddPart k x + splitCliffordHeadTailOddPart k y := by
  unfold splitCliffordHeadTailOddPart
  rw [map_add]
  module

theorem splitCliffordHeadTailEvenOdd_isCompl (k : ℕ) :
    IsCompl (splitCliffordHeadTailEven k) (splitCliffordHeadTailOdd k) := by
  constructor
  · rw [disjoint_iff_inf_le]
    intro x hx
    rcases hx with ⟨he, ho⟩
    have hfix := splitCliffordHeadTailEvenPart_of_mem k x he
    have hzero := splitCliffordHeadTailEvenPart_of_odd k x ho
    rw [hfix] at hzero
    exact hzero
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [Submodule.mem_sup]
    exact ⟨splitCliffordHeadTailEvenPart k x,
      splitCliffordHeadTailEvenPart_mem k x,
      splitCliffordHeadTailOddPart k x,
      splitCliffordHeadTailOddPart_mem k x,
      splitCliffordHeadTailEvenPart_add_oddPart k x⟩

/-- The fixed/anti-fixed eigenspaces form the two components of the
`ZMod 2`-graded fixed-head colimit. -/
def splitCliffordHeadTailGrade (k : ℕ) :
    ZMod 2 → Submodule ℝ (SplitCliffordHeadTailInfinity k) :=
  fun i => if i = 0 then splitCliffordHeadTailEven k else splitCliffordHeadTailOdd k

theorem splitCliffordHeadTailGrade_isInternal (k : ℕ) :
    DirectSum.IsInternal (splitCliffordHeadTailGrade k) := by
  have hcover : (Set.univ : Set (ZMod 2)) = {0, 1} := by
    ext i
    fin_cases i
    · constructor
      · intro _
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      · intro _
        trivial
    · constructor
      · intro _
        exact Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mpr rfl))
      · intro _
        trivial
  exact (DirectSum.isInternal_submodule_iff_isCompl
    (splitCliffordHeadTailGrade k) (by decide : (0 : ZMod 2) ≠ 1) hcover).2
    (splitCliffordHeadTailEvenOdd_isCompl k)

noncomputable instance splitCliffordHeadTailGrade_decomposition (k : ℕ) :
    DirectSum.Decomposition (splitCliffordHeadTailGrade k) :=
  DirectSum.IsInternal.chooseDecomposition (splitCliffordHeadTailGrade k)
    (splitCliffordHeadTailGrade_isInternal k)

theorem splitCliffordHeadTailEven_mul_even (k : ℕ)
    {x y : SplitCliffordHeadTailInfinity k}
    (hx : x ∈ splitCliffordHeadTailEven k)
    (hy : y ∈ splitCliffordHeadTailEven k) :
    x * y ∈ splitCliffordHeadTailEven k := by
  change splitCliffordHeadTailInfinityInvolute k x = x at hx
  change splitCliffordHeadTailInfinityInvolute k y = y at hy
  change splitCliffordHeadTailInfinityInvolute k (x * y) = x * y
  rw [map_mul, hx, hy]

theorem splitCliffordHeadTailEven_mul_odd (k : ℕ)
    {x y : SplitCliffordHeadTailInfinity k}
    (hx : x ∈ splitCliffordHeadTailEven k)
    (hy : y ∈ splitCliffordHeadTailOdd k) :
    x * y ∈ splitCliffordHeadTailOdd k := by
  change splitCliffordHeadTailInfinityInvolute k x = x at hx
  change splitCliffordHeadTailInfinityInvolute k y = -y at hy
  change splitCliffordHeadTailInfinityInvolute k (x * y) = -(x * y)
  rw [map_mul, hx, hy]
  simp

theorem splitCliffordHeadTailOdd_mul_even (k : ℕ)
    {x y : SplitCliffordHeadTailInfinity k}
    (hx : x ∈ splitCliffordHeadTailOdd k)
    (hy : y ∈ splitCliffordHeadTailEven k) :
    x * y ∈ splitCliffordHeadTailOdd k := by
  change splitCliffordHeadTailInfinityInvolute k x = -x at hx
  change splitCliffordHeadTailInfinityInvolute k y = y at hy
  change splitCliffordHeadTailInfinityInvolute k (x * y) = -(x * y)
  rw [map_mul, hx, hy]
  simp

theorem splitCliffordHeadTailOdd_mul_odd (k : ℕ)
    {x y : SplitCliffordHeadTailInfinity k}
    (hx : x ∈ splitCliffordHeadTailOdd k)
    (hy : y ∈ splitCliffordHeadTailOdd k) :
    x * y ∈ splitCliffordHeadTailEven k := by
  change splitCliffordHeadTailInfinityInvolute k x = -x at hx
  change splitCliffordHeadTailInfinityInvolute k y = -y at hy
  change splitCliffordHeadTailInfinityInvolute k (x * y) = x * y
  rw [map_mul, hx, hy]
  simp

/-- The even submodule at a finite fixed-head stage. -/
def splitCliffordHeadTailStageEven (k n : ℕ) :
    Submodule ℝ (SplitCliffordHeadTailStage k n) where
  carrier := {x | splitCliffordHeadTailStageInvolute k n x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change splitCliffordHeadTailStageInvolute k n (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change splitCliffordHeadTailStageInvolute k n (r • x) = r • x
    rw [splitCliffordHeadTailStageInvolute_smul, hx]

/-- The odd submodule at a finite fixed-head stage. -/
def splitCliffordHeadTailStageOdd (k n : ℕ) :
    Submodule ℝ (SplitCliffordHeadTailStage k n) where
  carrier := {x | splitCliffordHeadTailStageInvolute k n x = -x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change splitCliffordHeadTailStageInvolute k n (x + y) = -(x + y)
    rw [map_add, hx, hy, neg_add]
  smul_mem' := by
    intro r x hx
    change splitCliffordHeadTailStageInvolute k n (r • x) = -(r • x)
    rw [splitCliffordHeadTailStageInvolute_smul, hx, smul_neg]

/-- The stagewise eigensubmodules are preserved by every tower bond. -/
theorem splitCliffordHeadTailMap_preserves_parity (k m n : ℕ)
    (h : m ≤ n) (p : ZMod 2) (x : SplitCliffordHeadTailStage k m)
    (hx : x ∈ if p = 0 then splitCliffordHeadTailStageEven k m
      else splitCliffordHeadTailStageOdd k m) :
    splitCliffordHeadTailMap k m n h x ∈
      if p = 0 then splitCliffordHeadTailStageEven k n
      else splitCliffordHeadTailStageOdd k n := by
  fin_cases p
  · change splitCliffordHeadTailStageInvolute k m x = x at hx
    change splitCliffordHeadTailStageInvolute k n
      (splitCliffordHeadTailMap k m n h x) =
        splitCliffordHeadTailMap k m n h x
    have hcomm := AlgHom.congr_fun
      (splitCliffordHeadTailMap_involute k m n h) x
    change splitCliffordHeadTailMap k m n h
        (splitCliffordHeadTailStageInvolute k m x) =
      splitCliffordHeadTailStageInvolute k n
        (splitCliffordHeadTailMap k m n h x) at hcomm
    rw [← hcomm, hx]
  · change splitCliffordHeadTailStageInvolute k m x = -x at hx
    change splitCliffordHeadTailStageInvolute k n
      (splitCliffordHeadTailMap k m n h x) =
        -(splitCliffordHeadTailMap k m n h x)
    have hcomm := AlgHom.congr_fun
      (splitCliffordHeadTailMap_involute k m n h) x
    change splitCliffordHeadTailMap k m n h
        (splitCliffordHeadTailStageInvolute k m x) =
      splitCliffordHeadTailStageInvolute k n
        (splitCliffordHeadTailMap k m n h x) at hcomm
    rw [← hcomm, hx, map_neg]

/-- The canonical map from a finite fixed-head stage into the colimit
preserves its even and odd sectors. -/
theorem splitCliffordHeadTailOf_preserves_parity (k n : ℕ)
    (p : ZMod 2) (x : SplitCliffordHeadTailStage k n)
    (hx : x ∈ if p = 0 then splitCliffordHeadTailStageEven k n
      else splitCliffordHeadTailStageOdd k n) :
    splitCliffordHeadTailOf k n x ∈
      if p = 0 then splitCliffordHeadTailEven k
      else splitCliffordHeadTailOdd k := by
  fin_cases p
  · change splitCliffordHeadTailStageInvolute k n x = x at hx
    change splitCliffordHeadTailInfinityInvolute k
      (splitCliffordHeadTailOf k n x) = splitCliffordHeadTailOf k n x
    rw [splitCliffordHeadTailInfinityInvolute_ofStage]
    exact congrArg (splitCliffordHeadTailOf k n) hx
  · change splitCliffordHeadTailStageInvolute k n x = -x at hx
    change splitCliffordHeadTailInfinityInvolute k
      (splitCliffordHeadTailOf k n x) = -(splitCliffordHeadTailOf k n x)
    rw [splitCliffordHeadTailInfinityInvolute_ofStage, hx, map_neg]

instance splitCliffordHeadTailGrade_gradedMonoid (k : ℕ) :
    SetLike.GradedMonoid (splitCliffordHeadTailGrade k) where
  one_mem := by
    change splitCliffordHeadTailInfinityInvolute k
      (1 : SplitCliffordHeadTailInfinity k) = 1
    exact map_one _
  mul_mem := by
    intro i j x y hx hy
    fin_cases i <;> fin_cases j
    · change x ∈ splitCliffordHeadTailEven k at hx
      change y ∈ splitCliffordHeadTailEven k at hy
      change x * y ∈ splitCliffordHeadTailEven k
      exact splitCliffordHeadTailEven_mul_even k hx hy
    · change x ∈ splitCliffordHeadTailEven k at hx
      change y ∈ splitCliffordHeadTailOdd k at hy
      change x * y ∈ splitCliffordHeadTailOdd k
      exact splitCliffordHeadTailEven_mul_odd k hx hy
    · change x ∈ splitCliffordHeadTailOdd k at hx
      change y ∈ splitCliffordHeadTailEven k at hy
      change x * y ∈ splitCliffordHeadTailOdd k
      exact splitCliffordHeadTailOdd_mul_even k hx hy
    · change x ∈ splitCliffordHeadTailOdd k at hx
      change y ∈ splitCliffordHeadTailOdd k at hy
      change x * y ∈ splitCliffordHeadTailEven k
      exact splitCliffordHeadTailOdd_mul_odd k hx hy

/-- The fixed-head algebraic colimit is internally graded by its induced
Clifford parity involution. -/
noncomputable instance splitCliffordHeadTailGrade_gradedAlgebra (k : ℕ) :
    GradedAlgebra (splitCliffordHeadTailGrade k) := {}

end InfoGeometry.Canonical.SplitCliffordHeadTailTower

end
