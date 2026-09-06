import InfoGeometry.Algebra.SplitCayleyF2DeltaNativeRelations

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-! The elementary families named in Lopatin--Zubkov, arXiv:2208.08122v3,
    §1.3.  The paper uses `δ₁(t uᵢ)` and `δ₂(t vᵢ)` for field parameters
    `t`; over `F₂` the parameter is a `Bool`.  This file records the native
    generators as data.  It deliberately does not assert that they generate
    the full automorphism group. -/

def standardVec3 (i : Fin 3) : Vec3 :=
  fun j => if i = j then 1 else 0

theorem standardVec3_same (i : Fin 3) : standardVec3 i i = 1 := by
  simp [standardVec3]

theorem standardVec3_ne {i j : Fin 3} (h : i ≠ j) : standardVec3 i j = 0 := by
  simp [standardVec3, h]

theorem standardVec3_injective : Function.Injective standardVec3 := by
  intro i j hij
  by_contra h
  have hji : standardVec3 j i = 0 := standardVec3_ne (Ne.symm h)
  have hii : standardVec3 i i = 1 := standardVec3_same i
  have : (1 : Scalar) = 0 := by
    rw [← hii, hij, hji]
  exact one_ne_zero this

noncomputable def elementaryDeltaNativeGenerator (kind : Bool) (t : Bool) (i : Fin 3) :
    SplitOctF2Aut :=
  if kind then
    delta2NativeAutomorphism (fun j => if t then standardVec3 i j else 0)
  else
    delta1NativeAutomorphism (fun j => if t then standardVec3 i j else 0)

def elementaryDeltaNativeGeneratorSet : Set SplitOctF2Aut :=
  Set.range (fun q : Bool × Bool × Fin 3 =>
    elementaryDeltaNativeGenerator q.1 q.2.1 q.2.2)

def elementaryDeltaNativeSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure elementaryDeltaNativeGeneratorSet

theorem elementaryDeltaNativeGenerator_mem_subgroup
    (kind t : Bool) (i : Fin 3) :
    elementaryDeltaNativeGenerator kind t i ∈ elementaryDeltaNativeSubgroup := by
  apply Subgroup.subset_closure
  exact ⟨(kind, t, i), rfl⟩

theorem elementaryDeltaNativeGenerator_map_add
    (kind t : Bool) (i : Fin 3) (x y : SplitOctF2) :
    (elementaryDeltaNativeGenerator kind t i).1
        (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
        ((elementaryDeltaNativeGenerator kind t i).1 x)
        ((elementaryDeltaNativeGenerator kind t i).1 y) := by
  by_cases hk : kind
  · simp [elementaryDeltaNativeGenerator, hk, delta2Native_map_add]
  · simp [elementaryDeltaNativeGenerator, hk, delta1Native_map_add]

theorem elementaryDeltaNativeGenerator_map_mul
    (kind t : Bool) (i : Fin 3) (x y : SplitOctF2) :
    (elementaryDeltaNativeGenerator kind t i).1
        (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        ((elementaryDeltaNativeGenerator kind t i).1 x)
        ((elementaryDeltaNativeGenerator kind t i).1 y) := by
  by_cases hk : kind
  · simp [elementaryDeltaNativeGenerator, hk, delta2Native_map_mul]
  · simp [elementaryDeltaNativeGenerator, hk, delta1Native_map_mul]

theorem elementaryDeltaNativeGenerator_map_one
    (kind t : Bool) (i : Fin 3) :
    (elementaryDeltaNativeGenerator kind t i).1
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one := by
  by_cases hk : kind
  · simp [elementaryDeltaNativeGenerator, hk, delta2Native_map_one]
  · simp [elementaryDeltaNativeGenerator, hk, delta1Native_map_one]

theorem elementaryDeltaNativeGenerator_false (kind : Bool) (i : Fin 3) :
    elementaryDeltaNativeGenerator kind false i =
      (1 : SplitOctF2Aut) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  dsimp [elementaryDeltaNativeGenerator]
  split_ifs with hk
  · exact delta2NativeAutomorphism_zero_parameter x
  · exact delta1NativeAutomorphism_zero_parameter x

theorem elementaryDeltaNativeGenerator_true_square (kind : Bool) (i : Fin 3) :
    elementaryDeltaNativeGenerator kind true i *
        elementaryDeltaNativeGenerator kind true i =
      (1 : SplitOctF2Aut) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hk : kind
  · simpa [elementaryDeltaNativeGenerator, hk] using
      (delta2NativeAutomorphism_square (standardVec3 i) x)
  · simpa [elementaryDeltaNativeGenerator, hk] using
      (delta1NativeAutomorphism_square (standardVec3 i) x)

end InfoGeometry.Algebra.SplitCayleyF2
