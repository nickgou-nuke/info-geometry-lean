/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift

/-!
# Even and odd sectors of a cofinal Clifford tail

The cofinal tail carries the direct-limit grade involution and its real-linear
structure. This owner defines the actual positive and negative eigensubmodules.
-/

namespace InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.CliffordTower

/-- A tail element fixed by the grade involution has a finite even-stage
representative. -/
theorem splitCliffordTailInfinity_fixed_iff_exists_even_stage
    (k : ℕ) (x : SplitCliffordTailInfinity k) :
    splitCliffordTailInfinityInvolute k x = x ↔
      ∃ n, ∃ a : SplitClNNAlg (n + k),
        splitCliffordTailOf k n a = x ∧
        a ∈ CliffordAlgebra.evenOdd (Qsplit (n + k)) 0 := by
  constructor
  · intro hx
    induction x using DirectLimit.induction with
    | _ n a =>
        refine ⟨n, a, rfl, ?_⟩
        apply (clifford_involute_eq_self_iff_mem_even (Qsplit (n + k)) a).mp
        apply splitCliffordTailInfinity_stage_injective k n
        change splitCliffordTailOf k n
            (CliffordAlgebra.involute (Q := Qsplit (n + k)) a) =
          splitCliffordTailOf k n a
        rw [← splitCliffordTailInfinityInvolute_ofStage]
        exact hx
  · rintro ⟨n, a, rfl, ha⟩
    exact splitCliffordTailInfinity_of_even_fixed k n ha

/-- A tail element negated by the grade involution has a finite odd-stage
representative. -/
theorem splitCliffordTailInfinity_negated_iff_exists_odd_stage
    (k : ℕ) (x : SplitCliffordTailInfinity k) :
    splitCliffordTailInfinityInvolute k x = -x ↔
      ∃ n, ∃ a : SplitClNNAlg (n + k),
        splitCliffordTailOf k n a = x ∧
        a ∈ CliffordAlgebra.evenOdd (Qsplit (n + k)) 1 := by
  constructor
  · intro hx
    induction x using DirectLimit.induction with
    | _ n a =>
        refine ⟨n, a, rfl, ?_⟩
        apply (clifford_involute_eq_neg_iff_mem_odd (Qsplit (n + k)) a).mp
        apply splitCliffordTailInfinity_stage_injective k n
        change splitCliffordTailOf k n
            (CliffordAlgebra.involute (Q := Qsplit (n + k)) a) =
          splitCliffordTailOf k n (-a)
        rw [← splitCliffordTailInfinityInvolute_ofStage, map_neg]
        exact hx
  · rintro ⟨n, a, rfl, ha⟩
    exact splitCliffordTailInfinity_of_odd_negated k n ha

def splitCliffordTailEven (k : ℕ) :
    Submodule ℝ (SplitCliffordTailInfinity k) where
  carrier := {x | splitCliffordTailInfinityInvolute k x = x}
  zero_mem' := by
    change splitCliffordTailInfinityInvolute k (0 : SplitCliffordTailInfinity k) = 0
    exact map_zero _
  add_mem' := by
    intro x y hx hy
    change splitCliffordTailInfinityInvolute k (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change splitCliffordTailInfinityInvolute k (r • x) = r • x
    rw [splitCliffordTailInfinityInvolute_smul, hx]

def splitCliffordTailOdd (k : ℕ) :
    Submodule ℝ (SplitCliffordTailInfinity k) where
  carrier := {x | splitCliffordTailInfinityInvolute k x = -x}
  zero_mem' := by
    change splitCliffordTailInfinityInvolute k (0 : SplitCliffordTailInfinity k) = -0
    simp only [map_zero, neg_zero]
  add_mem' := by
    intro x y hx hy
    change splitCliffordTailInfinityInvolute k (x + y) = -(x + y)
    rw [map_add, hx, hy, neg_add]
  smul_mem' := by
    intro r x hx
    change splitCliffordTailInfinityInvolute k (r • x) = -(r • x)
    rw [splitCliffordTailInfinityInvolute_smul, hx, smul_neg]

/-- The even projection associated with the tail grade involution. -/
noncomputable def splitCliffordTailEvenPart (k : ℕ)
    (x : SplitCliffordTailInfinity k) : SplitCliffordTailInfinity k :=
  (2 : ℝ)⁻¹ • (x + splitCliffordTailInfinityInvolute k x)

/-- The odd projection associated with the tail grade involution. -/
noncomputable def splitCliffordTailOddPart (k : ℕ)
    (x : SplitCliffordTailInfinity k) : SplitCliffordTailInfinity k :=
  (2 : ℝ)⁻¹ • (x - splitCliffordTailInfinityInvolute k x)

/-- Every tail element's even projection is fixed by the grade involution. -/
theorem splitCliffordTailEvenPart_mem (k : ℕ)
    (x : SplitCliffordTailInfinity k) :
    splitCliffordTailEvenPart k x ∈ splitCliffordTailEven k := by
  change splitCliffordTailInfinityInvolute k
      (splitCliffordTailEvenPart k x) = splitCliffordTailEvenPart k x
  unfold splitCliffordTailEvenPart
  rw [splitCliffordTailInfinityInvolute_smul, map_add,
    splitCliffordTailInfinityInvolute_involutive]
  module

/-- Every tail element's odd projection is negated by the grade involution. -/
theorem splitCliffordTailOddPart_mem (k : ℕ)
    (x : SplitCliffordTailInfinity k) :
    splitCliffordTailOddPart k x ∈ splitCliffordTailOdd k := by
  change splitCliffordTailInfinityInvolute k
      (splitCliffordTailOddPart k x) = -splitCliffordTailOddPart k x
  unfold splitCliffordTailOddPart
  rw [splitCliffordTailInfinityInvolute_smul, map_sub,
    splitCliffordTailInfinityInvolute_involutive]
  module

/-- The even and odd projections reconstruct every element of the tail. -/
theorem splitCliffordTailEvenPart_add_oddPart (k : ℕ)
    (x : SplitCliffordTailInfinity k) :
    splitCliffordTailEvenPart k x + splitCliffordTailOddPart k x = x := by
  unfold splitCliffordTailEvenPart splitCliffordTailOddPart
  module

/-- The even projection fixes every element of the even eigensubmodule. -/
theorem splitCliffordTailEvenPart_of_mem (k : ℕ)
    (x : SplitCliffordTailInfinity k)
    (hx : x ∈ splitCliffordTailEven k) :
    splitCliffordTailEvenPart k x = x := by
  change splitCliffordTailInfinityInvolute k x = x at hx
  unfold splitCliffordTailEvenPart
  rw [hx]
  module

/-- The even projection vanishes on the odd eigensubmodule. -/
theorem splitCliffordTailEvenPart_of_odd (k : ℕ)
    (x : SplitCliffordTailInfinity k)
    (hx : x ∈ splitCliffordTailOdd k) :
    splitCliffordTailEvenPart k x = 0 := by
  change splitCliffordTailInfinityInvolute k x = -x at hx
  unfold splitCliffordTailEvenPart
  rw [hx]
  module

/-- The odd projection fixes every element of the odd eigensubmodule. -/
theorem splitCliffordTailOddPart_of_mem (k : ℕ)
    (x : SplitCliffordTailInfinity k)
    (hx : x ∈ splitCliffordTailOdd k) :
    splitCliffordTailOddPart k x = x := by
  change splitCliffordTailInfinityInvolute k x = -x at hx
  unfold splitCliffordTailOddPart
  rw [hx]
  module

/-- The odd projection vanishes on the even eigensubmodule. -/
theorem splitCliffordTailOddPart_of_even (k : ℕ)
    (x : SplitCliffordTailInfinity k)
    (hx : x ∈ splitCliffordTailEven k) :
    splitCliffordTailOddPart k x = 0 := by
  change splitCliffordTailInfinityInvolute k x = x at hx
  unfold splitCliffordTailOddPart
  rw [hx]
  module

/-- The even projection is additive. -/
theorem splitCliffordTailEvenPart_add (k : ℕ)
    (x y : SplitCliffordTailInfinity k) :
    splitCliffordTailEvenPart k (x + y) =
      splitCliffordTailEvenPart k x + splitCliffordTailEvenPart k y := by
  unfold splitCliffordTailEvenPart
  rw [map_add]
  module

/-- The odd projection is additive. -/
theorem splitCliffordTailOddPart_add (k : ℕ)
    (x y : SplitCliffordTailInfinity k) :
    splitCliffordTailOddPart k (x + y) =
      splitCliffordTailOddPart k x + splitCliffordTailOddPart k y := by
  unfold splitCliffordTailOddPart
  rw [map_add]
  module

/-- The even and odd terms in a decomposition are uniquely determined by the
grade involution projections. -/
theorem splitCliffordTailEvenOdd_decomposition_unique (k : ℕ)
    (e₁ e₂ o₁ o₂ : SplitCliffordTailInfinity k)
    (he₁ : e₁ ∈ splitCliffordTailEven k)
    (he₂ : e₂ ∈ splitCliffordTailEven k)
    (ho₁ : o₁ ∈ splitCliffordTailOdd k)
    (ho₂ : o₂ ∈ splitCliffordTailOdd k)
    (h : e₁ + o₁ = e₂ + o₂) : e₁ = e₂ ∧ o₁ = o₂ := by
  have he := congrArg (splitCliffordTailEvenPart k) h
  have ho := congrArg (splitCliffordTailOddPart k) h
  rw [splitCliffordTailEvenPart_add, splitCliffordTailEvenPart_add] at he
  rw [splitCliffordTailOddPart_add, splitCliffordTailOddPart_add] at ho
  rw [splitCliffordTailEvenPart_of_mem k e₁ he₁,
    splitCliffordTailEvenPart_of_odd k o₁ ho₁,
    splitCliffordTailEvenPart_of_mem k e₂ he₂,
    splitCliffordTailEvenPart_of_odd k o₂ ho₂] at he
  rw [splitCliffordTailOddPart_of_mem k o₁ ho₁,
    splitCliffordTailOddPart_of_even k e₁ he₁,
    splitCliffordTailOddPart_of_mem k o₂ ho₂,
    splitCliffordTailOddPart_of_even k e₂ he₂] at ho
  simpa only [add_zero, zero_add] using And.intro he ho

/-- The fixed and anti-fixed eigensubmodules form a direct complement in each
cofinal Clifford tail. -/
theorem splitCliffordTailEvenOdd_isCompl (k : ℕ) :
    IsCompl (splitCliffordTailEven k) (splitCliffordTailOdd k) := by
  constructor
  · rw [disjoint_iff_inf_le]
    intro x hx
    rcases hx with ⟨he, ho⟩
    have hfix := splitCliffordTailEvenPart_of_mem k x he
    have hzero := splitCliffordTailEvenPart_of_odd k x ho
    rw [hfix] at hzero
    exact hzero
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [Submodule.mem_sup]
    exact ⟨splitCliffordTailEvenPart k x,
      splitCliffordTailEvenPart_mem k x,
      splitCliffordTailOddPart k x,
      splitCliffordTailOddPart_mem k x,
      splitCliffordTailEvenPart_add_oddPart k x⟩

/-- The `ZMod 2`-indexed family determined by the tail grade involution. -/
def splitCliffordTailGrade (k : ℕ) :
    ZMod 2 → Submodule ℝ (SplitCliffordTailInfinity k) :=
  fun i => if i = 0 then splitCliffordTailEven k else splitCliffordTailOdd k

/-- Multiplication of two fixed elements remains fixed. -/
theorem splitCliffordTailEven_mul_even (k : ℕ)
    {x y : SplitCliffordTailInfinity k}
    (hx : x ∈ splitCliffordTailEven k)
    (hy : y ∈ splitCliffordTailEven k) :
    x * y ∈ splitCliffordTailEven k := by
  change splitCliffordTailInfinityInvolute k x = x at hx
  change splitCliffordTailInfinityInvolute k y = y at hy
  change splitCliffordTailInfinityInvolute k (x * y) = x * y
  rw [map_mul, hx, hy]

/-- Multiplication of a fixed element and an anti-fixed element is
anti-fixed, in the same order. -/
theorem splitCliffordTailEven_mul_odd (k : ℕ)
    {x y : SplitCliffordTailInfinity k}
    (hx : x ∈ splitCliffordTailEven k)
    (hy : y ∈ splitCliffordTailOdd k) :
    x * y ∈ splitCliffordTailOdd k := by
  change splitCliffordTailInfinityInvolute k x = x at hx
  change splitCliffordTailInfinityInvolute k y = -y at hy
  change splitCliffordTailInfinityInvolute k (x * y) = -(x * y)
  rw [map_mul, hx, hy]
  simp

/-- Multiplication of an anti-fixed element and a fixed element is
anti-fixed, in the same order. -/
theorem splitCliffordTailOdd_mul_even (k : ℕ)
    {x y : SplitCliffordTailInfinity k}
    (hx : x ∈ splitCliffordTailOdd k)
    (hy : y ∈ splitCliffordTailEven k) :
    x * y ∈ splitCliffordTailOdd k := by
  change splitCliffordTailInfinityInvolute k x = -x at hx
  change splitCliffordTailInfinityInvolute k y = y at hy
  change splitCliffordTailInfinityInvolute k (x * y) = -(x * y)
  rw [map_mul, hx, hy]
  simp

/-- Multiplication of two anti-fixed elements is fixed. -/
theorem splitCliffordTailOdd_mul_odd (k : ℕ)
    {x y : SplitCliffordTailInfinity k}
    (hx : x ∈ splitCliffordTailOdd k)
    (hy : y ∈ splitCliffordTailOdd k) :
    x * y ∈ splitCliffordTailEven k := by
  change splitCliffordTailInfinityInvolute k x = -x at hx
  change splitCliffordTailInfinityInvolute k y = -y at hy
  change splitCliffordTailInfinityInvolute k (x * y) = x * y
  rw [map_mul, hx, hy]
  simp

/-- The fixed/anti-fixed splitting is multiplicative with `ZMod 2` degree. -/
instance splitCliffordTailGrade_gradedMonoid (k : ℕ) :
    SetLike.GradedMonoid (splitCliffordTailGrade k) where
  one_mem := by
    change splitCliffordTailInfinityInvolute k (1 : SplitCliffordTailInfinity k) = 1
    exact map_one _
  mul_mem := by
    intro i j x y hx hy
    fin_cases i <;> fin_cases j
    · change x ∈ splitCliffordTailEven k at hx
      change y ∈ splitCliffordTailEven k at hy
      change x * y ∈ splitCliffordTailEven k
      exact splitCliffordTailEven_mul_even k hx hy
    · change x ∈ splitCliffordTailEven k at hx
      change y ∈ splitCliffordTailOdd k at hy
      change x * y ∈ splitCliffordTailOdd k
      exact splitCliffordTailEven_mul_odd k hx hy
    · change x ∈ splitCliffordTailOdd k at hx
      change y ∈ splitCliffordTailEven k at hy
      change x * y ∈ splitCliffordTailOdd k
      exact splitCliffordTailOdd_mul_even k hx hy
    · change x ∈ splitCliffordTailOdd k at hx
      change y ∈ splitCliffordTailOdd k at hy
      change x * y ∈ splitCliffordTailEven k
      exact splitCliffordTailOdd_mul_odd k hx hy

/-- The complementary parity sectors give an internal direct-sum
decomposition of the tail as a real module. -/
theorem splitCliffordTailGrade_isInternal (k : ℕ) :
    DirectSum.IsInternal (splitCliffordTailGrade k) := by
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
    (splitCliffordTailGrade k) (by decide : (0 : ZMod 2) ≠ 1) hcover).2
    (splitCliffordTailEvenOdd_isCompl k)

/-- The tail's even/odd decomposition, obtained from its proved internal
direct-sum property. -/
noncomputable instance splitCliffordTailGrade_decomposition (k : ℕ) :
    DirectSum.Decomposition (splitCliffordTailGrade k) :=
  DirectSum.IsInternal.chooseDecomposition (splitCliffordTailGrade k)
    (splitCliffordTailGrade_isInternal k)

/-- The cofinal tail is an internally `ZMod 2`-graded real algebra, with its
grading induced by the canonical Clifford grade involution. -/
noncomputable instance splitCliffordTailGrade_gradedAlgebra (k : ℕ) :
    GradedAlgebra (splitCliffordTailGrade k) := {}

/-- Every canonical finite-stage map into the cofinal tail preserves the
Clifford `ZMod 2` grade. -/
theorem splitCliffordTailOf_preserves_grade (k n : ℕ)
    (p : ZMod 2) (x : SplitClNNAlg (n + k))
    (hx : x ∈ CliffordAlgebra.evenOdd (Qsplit (n + k)) p) :
    splitCliffordTailOf k n x ∈ splitCliffordTailGrade k p := by
  fin_cases p
  · change x ∈ CliffordAlgebra.evenOdd (Qsplit (n + k)) 0 at hx
    change splitCliffordTailOf k n x ∈ splitCliffordTailEven k
    exact splitCliffordTailInfinity_of_even_fixed k n hx
  · change x ∈ CliffordAlgebra.evenOdd (Qsplit (n + k)) 1 at hx
    change splitCliffordTailOf k n x ∈ splitCliffordTailOdd k
    exact splitCliffordTailInfinity_of_odd_negated k n hx

end InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift
