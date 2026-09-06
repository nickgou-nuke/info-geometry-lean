import Mathlib.GroupTheory.QuotientGroup.Defs
import proofs.RealPin55MatrixRepresentation

/-! # Central signs in the real Pin representation kernel -/

noncomputable section
namespace RealPin55Kernel

open Clifford55
open RealPin55Core
open RealPin55TwistedAction
open RealPin55MatrixRepresentation
open V55Fin10Coordinates

def pinNegOne : FullPin55 :=
  ⟨-1, RealPin55Core.neg_one_mem_fullPin55⟩

@[simp] theorem pinNegOne_coe : (pinNegOne : Cl55ˣ) = -1 := rfl

@[simp] theorem pinNegOne_coe_clifford :
    (((pinNegOne : FullPin55) : Cl55ˣ) : Cl55) = -1 := rfl

@[simp] theorem pinNegOne_sq : pinNegOne * pinNegOne = 1 := by
  apply Subtype.ext
  simp [pinNegOne]

@[simp] theorem pinNegOne_inv : pinNegOne⁻¹ = pinNegOne := by
  apply mul_left_cancel (a := pinNegOne)
  simp

theorem pinNegOne_ne_one : pinNegOne ≠ 1 := by
  intro h
  have hc := congrArg (fun g : FullPin55 ↦ ((g : Cl55ˣ) : Cl55)) h
  have hc' : (-1 : Cl55) = 1 := by simpa [pinNegOne] using hc
  have hm : algebraMap ℝ Cl55 (-1) = algebraMap ℝ Cl55 1 := by
    simpa using hc'
  have hr : (-1 : ℝ) = 1 := FaithfulSMul.algebraMap_injective ℝ Cl55 hm
  norm_num at hr

theorem pinNegOne_commutes (g : FullPin55) :
    pinNegOne * g = g * pinNegOne := by
  apply Subtype.ext
  apply Units.ext
  simp [pinNegOne]

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

@[simp] theorem fullPinToO55_pinNegOne :
    fullPinToO55 pinNegOne = 1 :=
  pinNegOne_mem_kernel

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

@[simp] theorem mem_centralSignSubgroup_iff (g : FullPin55) :
    g ∈ centralSignSubgroup ↔ g = 1 ∨ g = pinNegOne := by
  rw [centralSignSubgroup_eq_literal]
  rfl

theorem centralSignSubgroup_commutes
    {z : FullPin55}
    (hz : z ∈ centralSignSubgroup)
    (g : FullPin55) :
    z * g = g * z := by
  rcases (mem_centralSignSubgroup_iff z).1 hz with rfl | rfl
  · simp
  · exact pinNegOne_commutes g

theorem centralSignSubgroup_le_kernel :
    centralSignSubgroup ≤ MonoidHom.ker fullPinToO55 := by
  intro g hg
  rcases (mem_centralSignSubgroup_iff g).1 hg with rfl | rfl
  · exact Subgroup.one_mem _
  · exact pinNegOne_mem_kernel

theorem coe_centralSignSubgroup :
    (centralSignSubgroup : Set FullPin55) = {1, pinNegOne} := by
  ext g
  simp [mem_centralSignSubgroup_iff]

theorem centralSignSubgroup_ne_bot :
    centralSignSubgroup ≠ (⊥ : Subgroup FullPin55) := by
  intro hbot
  have hmem : pinNegOne ∈ (⊥ : Subgroup FullPin55) := by
    rw [← hbot]
    exact (mem_centralSignSubgroup_iff pinNegOne).2 (Or.inr rfl)
  exact pinNegOne_ne_one (Subgroup.mem_bot.mp hmem)

theorem sq_eq_one_of_mem_centralSignSubgroup
    {z : FullPin55} (hz : z ∈ centralSignSubgroup) :
    z * z = 1 := by
  rcases (mem_centralSignSubgroup_iff z).1 hz with rfl | rfl
  · simp
  · exact pinNegOne_sq

theorem centralSignSubgroup_commutes
    (z : FullPin55) (hz : z ∈ centralSignSubgroup) (g : FullPin55) :
    z * g = g * z := by
  rcases (mem_centralSignSubgroup_iff z).1 hz with rfl | rfl
  · simp
  · exact pinNegOne_commutes g

instance centralSignSubgroup_normal : centralSignSubgroup.Normal := by
  refine ⟨?_⟩
  intro z hz g
  have hconj : g * z * g⁻¹ = z := by
    calc
      g * z * g⁻¹ = z * g * g⁻¹ := by
        rw [(centralSignSubgroup_commutes z hz g).symm]
      _ = z := by simp [mul_assoc]
  rw [hconj]
  exact hz

theorem fullPinToO55_eq_one_of_mem_centralSignSubgroup
    {z : FullPin55} (hz : z ∈ centralSignSubgroup) :
    fullPinToO55 z = 1 :=
  centralSignSubgroup_le_kernel hz

theorem fullPinToO55_sign_mul
    (z : FullPin55) (hz : z ∈ centralSignSubgroup) (g : FullPin55) :
    fullPinToO55 (z * g) = fullPinToO55 g := by
  rw [map_mul, fullPinToO55_eq_one_of_mem_centralSignSubgroup hz, one_mul]

theorem fullPinToO55_mul_sign
    (g z : FullPin55) (hz : z ∈ centralSignSubgroup) :
    fullPinToO55 (g * z) = fullPinToO55 g := by
  rw [map_mul, fullPinToO55_eq_one_of_mem_centralSignSubgroup hz, mul_one]

@[simp] theorem fullPinToO55_pinNegOne_mul (g : FullPin55) :
    fullPinToO55 (pinNegOne * g) = fullPinToO55 g := by
  exact fullPinToO55_sign_mul pinNegOne
    ((mem_centralSignSubgroup_iff pinNegOne).2 (Or.inr rfl)) g

@[simp] theorem fullPinToO55_mul_pinNegOne (g : FullPin55) :
    fullPinToO55 (g * pinNegOne) = fullPinToO55 g := by
  exact fullPinToO55_mul_sign g pinNegOne
    ((mem_centralSignSubgroup_iff pinNegOne).2 (Or.inr rfl))

abbrev ProjectiveFullPin55 : Type :=
  FullPin55 ⧸ centralSignSubgroup

def fullPinToO55ModuloCentralSigns :
    ProjectiveFullPin55 →* RealPin55MatrixRepresentation.O55 :=
  QuotientGroup.lift centralSignSubgroup fullPinToO55
    centralSignSubgroup_le_kernel

@[simp] theorem fullPinToO55ModuloCentralSigns_mk (g : FullPin55) :
    fullPinToO55ModuloCentralSigns (QuotientGroup.mk' centralSignSubgroup g) =
      fullPinToO55 g := rfl

theorem fullPinToO55_factor_through_centralSigns :
    fullPinToO55ModuloCentralSigns.comp
        (QuotientGroup.mk' centralSignSubgroup) = fullPinToO55 := rfl

@[simp] theorem projective_pinNegOne_eq_one :
    QuotientGroup.mk' centralSignSubgroup pinNegOne = 1 := by
  apply (QuotientGroup.eq_one_iff pinNegOne).2
  exact (mem_centralSignSubgroup_iff pinNegOne).2 (Or.inr rfl)

@[simp] theorem projective_pinNegOne_mul (g : FullPin55) :
    QuotientGroup.mk' centralSignSubgroup (pinNegOne * g) =
      QuotientGroup.mk' centralSignSubgroup g := by
  rw [map_mul, projective_pinNegOne_eq_one, one_mul]

@[simp] theorem projective_mul_pinNegOne (g : FullPin55) :
    QuotientGroup.mk' centralSignSubgroup (g * pinNegOne) =
      QuotientGroup.mk' centralSignSubgroup g := by
  rw [map_mul, projective_pinNegOne_eq_one, mul_one]

end RealPin55Kernel
end noncomputable section
