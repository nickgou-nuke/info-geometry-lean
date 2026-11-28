/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Orthogonal.O55ContactGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.ZMod.Basic

/-! Native source/target block multigrading for the contact carrier. -/

noncomputable section
namespace InfoGeometry.Orthogonal.O55Contact

inductive Weight3 | minus | zero | plus
  deriving DecidableEq, Repr

instance : Fintype Weight3 where
  elems := {.minus, .zero, .plus}
  complete weight := by cases weight <;> decide

namespace Weight3
def value : Weight3 → ℤ
  | minus => -1 | zero => 0 | plus => 1
def valueR (w : Weight3) : ℝ := (w.value : ℝ)
def opposite : Weight3 → Weight3
  | minus => plus | zero => zero | plus => minus
@[simp] theorem opposite_opposite (w : Weight3) : w.opposite.opposite = w := by cases w <;> rfl
@[simp] theorem value_opposite (w : Weight3) : w.opposite.value = -w.value := by cases w <;> rfl
@[simp] theorem valueR_opposite (w : Weight3) :
    w.opposite.valueR = -w.valueR := by
  cases w <;> simp [valueR, value, opposite] <;> norm_num
end Weight3

def weightOfIndex : Fin 10 → Weight3 :=
  ![Weight3.minus, Weight3.minus, Weight3.zero, Weight3.zero, Weight3.zero,
    Weight3.zero, Weight3.zero, Weight3.zero, Weight3.plus, Weight3.plus]

@[simp] theorem weightOfIndex_dual (i : Fin 10) :
    weightOfIndex (dualIndex i) = (weightOfIndex i).opposite := by
  fin_cases i <;> rfl

@[simp] theorem contactWeight_eq_weightValue (i : Fin 10) :
    contactWeight i = (weightOfIndex i).value := by
  fin_cases i <;> rfl

@[simp] theorem contactWeightR_eq_weightValueR (i : Fin 10) :
    contactWeightR i = (weightOfIndex i).valueR := by
  simp [contactWeightR, Weight3.valueR]

def weightProjector (w : Weight3) : End55 where
  toFun x i := if weightOfIndex i = w then x i else 0
  map_add' x y := by
    ext i
    by_cases h : weightOfIndex i = w <;> simp [h]
  map_smul' c x := by
    ext i
    by_cases h : weightOfIndex i = w <;> simp [h]

@[simp] theorem weightProjector_apply (w : Weight3) (x : Vector55) (i : Fin 10) :
    weightProjector w x i = if weightOfIndex i = w then x i else 0 := rfl

theorem weightProjector_sq (w : Weight3) :
    weightProjector w * weightProjector w = weightProjector w := by
  apply LinearMap.ext; intro x; funext i
  by_cases h : weightOfIndex i = w <;>
    simp [Module.End.mul_apply, weightProjector_apply, h]

theorem weightProjector_mul_of_ne {u v : Weight3} (h : u ≠ v) :
    weightProjector u * weightProjector v = 0 := by
  apply LinearMap.ext; intro x; funext i
  by_cases hi : weightOfIndex i = u
  · have hiv : weightOfIndex i ≠ v := by
      intro hiv; exact h (hi.symm.trans hiv)
    simp [Module.End.mul_apply, weightProjector_apply, hi, hiv, h]
  · simp [Module.End.mul_apply, weightProjector_apply, hi]

theorem weightProjector_resolution :
    weightProjector Weight3.minus + weightProjector Weight3.zero +
      weightProjector Weight3.plus = (1 : End55) := by
  apply LinearMap.ext; intro x; funext i
  fin_cases i <;> simp [weightProjector_apply, weightOfIndex]

theorem euler_mul_weightProjector (w : Weight3) :
    contactEulerEnd * weightProjector w = w.valueR • weightProjector w := by
  apply LinearMap.ext; intro x; funext i
  by_cases h : weightOfIndex i = w
  · have hw : contactWeightR i = w.valueR := by
      simp [contactWeightR, contactWeight_eq_weightValue, h, Weight3.valueR]
    simp [Module.End.mul_apply, weightProjector_apply, h,
      contactEulerEnd_apply, hw, Weight3.valueR]
  · simp [Module.End.mul_apply, weightProjector_apply, h,
      contactEulerEnd_apply]

theorem weightProjector_mul_euler (w : Weight3) :
    weightProjector w * contactEulerEnd = w.valueR • weightProjector w := by
  apply LinearMap.ext; intro x; funext i
  by_cases h : weightOfIndex i = w
  · have hw : contactWeightR i = w.valueR := by
      simp [contactWeightR, contactWeight_eq_weightValue, h, Weight3.valueR]
    simp [Module.End.mul_apply, weightProjector_apply, h,
      contactEulerEnd_apply, hw, Weight3.valueR]
  · simp [Module.End.mul_apply, weightProjector_apply, h]

structure BlockDegree where
  target : Weight3
  source : Weight3
  deriving DecidableEq, Repr

instance : Inhabited BlockDegree := ⟨⟨Weight3.zero, Weight3.zero⟩⟩

instance : Fintype BlockDegree :=
  Fintype.ofEquiv (Weight3 × Weight3) {
    toFun := fun p => ⟨p.1, p.2⟩
    invFun := fun d => (d.target, d.source)
    left_inv := by intro p; cases p; rfl
    right_inv := by intro d; cases d; rfl
  }

namespace BlockDegree
def contact (d : BlockDegree) : ℤ := d.target.value - d.source.value
def parity (d : BlockDegree) : ZMod 2 := (d.contact : ZMod 2)
def opposite (d : BlockDegree) : BlockDegree :=
  ⟨d.target.opposite, d.source.opposite⟩
def adjointPartner (d : BlockDegree) : BlockDegree :=
  ⟨d.source.opposite, d.target.opposite⟩
@[simp] theorem contact_opposite (d : BlockDegree) :
    d.opposite.contact = -d.contact := by
  rcases d with ⟨target, source⟩
  cases target <;> cases source <;> rfl
@[simp] theorem opposite_opposite (d : BlockDegree) :
    d.opposite.opposite = d := by
  cases d
  simp [opposite]
@[simp] theorem parity_opposite (d : BlockDegree) :
    d.opposite.parity = d.parity := by
  simp only [parity, contact_opposite, Int.cast_neg]
  have htwo : (2 : ZMod 2) = 0 := rfl
  calc
    -(d.contact : ZMod 2) = (d.contact : ZMod 2) - (2 : ZMod 2) * (d.contact : ZMod 2) := by ring
    _ = (d.contact : ZMod 2) := by rw [htwo]; ring
@[simp] theorem adjointPartner_adjointPartner (d : BlockDegree) :
    d.adjointPartner.adjointPartner = d := by
  cases d
  simp [adjointPartner]
@[simp] theorem contact_adjointPartner (d : BlockDegree) :
    d.adjointPartner.contact = d.contact := by
  cases d
  simp [adjointPartner, contact]
  ring
end BlockDegree

def blockComponent (d : BlockDegree) (A : End55) : End55 :=
  weightProjector d.target * A * weightProjector d.source

theorem weightProjector_pairing_move
    (w : Weight3) (x y : Vector55) :
    splitPairing (weightProjector w x) y =
      splitPairing x (weightProjector w.opposite y) := by
  cases w <;>
    simp [splitPairing, weightProjector, weightOfIndex, Weight3.opposite]
    <;> ring

theorem blockComponent_pairing
    {A : End55} (hA : IsSplitSkew A)
    (d : BlockDegree) (x y : Vector55) :
    splitPairing (blockComponent d A x) y =
      -splitPairing x (blockComponent d.adjointPartner A y) := by
  have hskew := hA (weightProjector d.source x)
    (weightProjector d.target.opposite y)
  calc
    splitPairing (blockComponent d A x) y =
        splitPairing (A (weightProjector d.source x))
          (weightProjector d.target.opposite y) := by
            simp [blockComponent, Module.End.mul_apply,
              weightProjector_pairing_move]
    _ = -splitPairing (weightProjector d.source x)
          (A (weightProjector d.target.opposite y)) := by
            linarith
    _ = -splitPairing x
          (weightProjector d.source.opposite
            (A (weightProjector d.target.opposite y))) := by
            rw [weightProjector_pairing_move]
    _ = -splitPairing x (blockComponent d.adjointPartner A y) := by
            simp [blockComponent, BlockDegree.adjointPartner, Module.End.mul_apply]

theorem blockComponent_grade (d : BlockDegree) (A : End55) :
    endCommutator contactEulerEnd (blockComponent d A) =
      (d.contact : ℝ) • blockComponent d A := by
  unfold blockComponent BlockDegree.contact endCommutator
  calc
    contactEulerEnd * (weightProjector d.target * A * weightProjector d.source) -
        (weightProjector d.target * A * weightProjector d.source) * contactEulerEnd =
      (contactEulerEnd * weightProjector d.target) * A * weightProjector d.source -
        weightProjector d.target * A * (weightProjector d.source * contactEulerEnd) := by
          noncomm_ring
    _ = (d.target.valueR • weightProjector d.target) * A * weightProjector d.source -
        weightProjector d.target * A * (d.source.valueR • weightProjector d.source) := by
          rw [euler_mul_weightProjector, weightProjector_mul_euler]
    _ = (d.contact : ℝ) •
        (weightProjector d.target * A * weightProjector d.source) := by
          simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
            Weight3.valueR]
          rw [← sub_smul]
          congr 1
          simp [BlockDegree.contact]

theorem blockComponent_add (d : BlockDegree) (A B : End55) :
    blockComponent d (A + B) = blockComponent d A + blockComponent d B := by
  unfold blockComponent
  noncomm_ring

theorem blockComponent_smul (d : BlockDegree) (c : ℝ) (A : End55) :
    blockComponent d (c • A) = c • blockComponent d A := by
  unfold blockComponent
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

theorem matching_block_degree_add (target middle source : Weight3) :
    (BlockDegree.mk target middle).contact +
        (BlockDegree.mk middle source).contact =
      (BlockDegree.mk target source).contact := by
  simp [BlockDegree.contact]

theorem blockComponent_mul_of_mismatch
    (d e : BlockDegree) (A B : End55)
    (h : d.source ≠ e.target) :
    blockComponent d A * blockComponent e B = 0 := by
  unfold blockComponent
  calc
    (weightProjector d.target * A * weightProjector d.source) *
        (weightProjector e.target * B * weightProjector e.source) =
      weightProjector d.target * A *
        (weightProjector d.source * weightProjector e.target) * B *
          weightProjector e.source := by noncomm_ring
    _ = 0 := by rw [weightProjector_mul_of_ne h]; simp

theorem matching_block_parity_add
    (target middle source : Weight3) :
    (BlockDegree.mk target middle).parity +
        (BlockDegree.mk middle source).parity =
      (BlockDegree.mk target source).parity := by
  unfold BlockDegree.parity
  rw [← Int.cast_add, matching_block_degree_add]

theorem full_block_decomposition (A : End55) :
    A =
      blockComponent ⟨Weight3.minus, Weight3.minus⟩ A +
      blockComponent ⟨Weight3.minus, Weight3.zero⟩ A +
      blockComponent ⟨Weight3.minus, Weight3.plus⟩ A +
      blockComponent ⟨Weight3.zero, Weight3.minus⟩ A +
      blockComponent ⟨Weight3.zero, Weight3.zero⟩ A +
      blockComponent ⟨Weight3.zero, Weight3.plus⟩ A +
      blockComponent ⟨Weight3.plus, Weight3.minus⟩ A +
      blockComponent ⟨Weight3.plus, Weight3.zero⟩ A +
      blockComponent ⟨Weight3.plus, Weight3.plus⟩ A := by
  have hres := weightProjector_resolution
  calc
    A = (1 : End55) * A * 1 := by simp
    _ = (weightProjector Weight3.minus +
          weightProjector Weight3.zero + weightProjector Weight3.plus) * A *
        (weightProjector Weight3.minus +
          weightProjector Weight3.zero + weightProjector Weight3.plus) := by
          rw [hres]
    _ = _ := by
      unfold blockComponent
      noncomm_ring

theorem crosscap_weightProjector (w : Weight3) :
    crosscapEnd * weightProjector w * crosscapEnd =
      weightProjector w.opposite := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases hi : weightOfIndex i = w.opposite
  · have hopp : (weightOfIndex i).opposite = w := by
      rw [hi, Weight3.opposite_opposite]
    simp [Module.End.mul_apply, weightProjector_apply, hi, hopp]
  · have hopp : (weightOfIndex i).opposite ≠ w := by
      intro h
      apply hi
      rw [← Weight3.opposite_opposite (weightOfIndex i), h]
    simp [Module.End.mul_apply, weightProjector_apply, hi, hopp]

theorem crosscap_blockComponent (d : BlockDegree) (A : End55) :
    crosscapEnd * blockComponent d A * crosscapEnd =
      blockComponent d.opposite
        (crosscapEnd * A * crosscapEnd) := by
  unfold blockComponent BlockDegree.opposite
  rw [← crosscap_weightProjector, ← crosscap_weightProjector]
  calc
    crosscapEnd * (weightProjector d.target * A * weightProjector d.source) * crosscapEnd =
      crosscapEnd * (weightProjector d.target * (1 * A * 1) * weightProjector d.source) * crosscapEnd := by
        simp
    _ = crosscapEnd * (weightProjector d.target * ((crosscapEnd * crosscapEnd) * A * (crosscapEnd * crosscapEnd)) * weightProjector d.source) * crosscapEnd := by
        rw [crosscapEnd_sq]
    _ = (crosscapEnd * weightProjector d.target * crosscapEnd) * (crosscapEnd * A * crosscapEnd) * (crosscapEnd * weightProjector d.source * crosscapEnd) := by
        noncomm_ring


/-- The combined contact-degree and parity label. -/
structure MultiDegree where
  contact : ℤ
  parity : ZMod 2
  parity_eq : parity = (contact : ZMod 2)

def canonicalMultiDegree (k : ℤ) : MultiDegree :=
  ⟨k, (k : ZMod 2), rfl⟩

instance : Inhabited MultiDegree := ⟨canonicalMultiDegree 0⟩

def MultiDegree.add (d e : MultiDegree) : MultiDegree where
  contact := d.contact + e.contact
  parity := d.parity + e.parity
  parity_eq := by
    rw [d.parity_eq, e.parity_eq]
    simp

def MultiDegree.opposite (d : MultiDegree) : MultiDegree where
  contact := -d.contact
  parity := d.parity
  parity_eq := by
    simpa [d.parity_eq] using
      (show (d.contact : ZMod 2) = -((d.contact : ZMod 2)) by ring)

@[simp] theorem canonicalMultiDegree_add (k l : ℤ) :
    (canonicalMultiDegree k).add (canonicalMultiDegree l) =
      canonicalMultiDegree (k + l) := by
  simp [canonicalMultiDegree, MultiDegree.add]

@[simp] theorem canonicalMultiDegree_opposite (k : ℤ) :
    (canonicalMultiDegree k).opposite = canonicalMultiDegree (-k) := by
  simp [canonicalMultiDegree, MultiDegree.opposite]

theorem multigraded_bracket
    {k l : ℤ} {A B : O55Lie}
    (hA : A ∈ realContactGradeSpace k)
    (hB : B ∈ realContactGradeSpace l) :
    ⁅A, B⁆ ∈ realContactGradeSpace (k + l) ∧
      canonicalMultiDegree (k + l) =
        (canonicalMultiDegree k).add (canonicalMultiDegree l) := by
  exact ⟨contactGrade_bracket hA hB, by simp⟩

theorem multigraded_crosscap
    {k : ℤ} {A : O55Lie}
    (hA : A ∈ realContactGradeSpace k) :
    crosscapConjugation A ∈ realContactGradeSpace (-k) ∧
      canonicalMultiDegree (-k) =
        (canonicalMultiDegree k).opposite := by
  exact ⟨crosscap_reverses_grade hA, by simp⟩

end InfoGeometry.Orthogonal.O55Contact
