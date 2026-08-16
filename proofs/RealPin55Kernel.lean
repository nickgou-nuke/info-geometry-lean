import proofs.RealPin55MatrixRepresentation

/-! # Central signs in the real Pin representation kernel -/

noncomputable section
namespace RealPin55Kernel

open Clifford55
open RealPin55Core
open RealPin55TwistedAction
open RealPin55MatrixRepresentation
open V55Fin10Coordinates

theorem negOne_mem_fullPin55 : (-1 : Cl55ˣ) ∈ FullPin55 := by
  exact RealPin55Core.neg_one_mem_fullPin55

def pinNegOne : FullPin55 := ⟨-1, negOne_mem_fullPin55⟩

@[simp] theorem pinNegOne_coe : (pinNegOne : Cl55ˣ) = -1 := rfl

@[simp] theorem pinNegOne_sq : pinNegOne * pinNegOne = 1 := by
  apply Subtype.ext
  simp [pinNegOne]

theorem pinNegOne_ne_one : pinNegOne ≠ 1 := by
  intro h
  have hc := congrArg (fun g : FullPin55 ↦ ((g : Cl55ˣ) : Cl55)) h
  have hc' : (-1 : Cl55) = 1 := by simpa [pinNegOne] using hc
  have hm : algebraMap ℝ Cl55 (-1) = algebraMap ℝ Cl55 1 := by
    simpa using hc'
  have hr : (-1 : ℝ) = 1 := FaithfulSMul.algebraMap_injective ℝ Cl55 hm
  norm_num at hr

@[simp] theorem twistedVector_pinNegOne (v : V55) :
    twistedVector pinNegOne v = v := by
  apply iota55_injective
  rw [iota_twistedVector]
  simp [pinNegOne]

theorem pinNegOne_mem_kernel :
    pinNegOne ∈ MonoidHom.ker fullPinToO55 := by
  change fullPinToO55 pinNegOne = 1
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hmul := fullPinMatrix_mulVec pinNegOne
    (v55Fin10Equiv.symm (Pi.single j 1))
  have hij := congrFun hmul i
  simpa [Pi.single_apply, Matrix.one_apply] using hij

/-- The literal two-element central sign subgroup inside the full Pin group. -/
def centralSignSubgroup : Subgroup FullPin55 :=
  Subgroup.closure {pinNegOne}

def literalCentralSigns : Subgroup FullPin55 where
  carrier := {g | g = 1 ∨ g = pinNegOne}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl
    · exact Or.inl (inv_one)
    · exact Or.inr (by
        apply mul_left_cancel (a := pinNegOne)
        simp)

theorem centralSignSubgroup_eq_literal :
    centralSignSubgroup = literalCentralSigns := by
  apply le_antisymm
  · rw [centralSignSubgroup, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_singleton_iff] at hg
    subst g
    exact Or.inr rfl
  · intro g hg
    rcases hg with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_singleton pinNegOne)

theorem mem_centralSignSubgroup_iff (g : FullPin55) :
    g ∈ centralSignSubgroup ↔ g = 1 ∨ g = pinNegOne := by
  rw [centralSignSubgroup_eq_literal]
  rfl

theorem centralSignSubgroup_le_kernel :
    centralSignSubgroup ≤ MonoidHom.ker fullPinToO55 := by
  rw [centralSignSubgroup, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_singleton_iff] at hg
  subst g
  simpa using pinNegOne_mem_kernel

end RealPin55Kernel
end noncomputable section
