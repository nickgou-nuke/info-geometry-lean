import InfoGeometry.Orthogonal.O55ContactGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.ZMod.Basic

/-! Native source/target block multigrading for the contact carrier. -/

noncomputable section
namespace InfoGeometry.Orthogonal.O55Contact

inductive Weight3 | minus | zero | plus
  deriving DecidableEq, Fintype, Repr

namespace Weight3
def value : Weight3 → ℤ
  | minus => -1 | zero => 0 | plus => 1
def valueR (w : Weight3) : ℝ := (w.value : ℝ)
def opposite : Weight3 → Weight3
  | minus => plus | zero => zero | plus => minus
@[simp] theorem opposite_opposite (w : Weight3) : w.opposite.opposite = w := by cases w <;> rfl
@[simp] theorem value_opposite (w : Weight3) : w.opposite.value = -w.value := by cases w <;> rfl
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
  deriving DecidableEq, Fintype, Repr

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

end InfoGeometry.Orthogonal.O55Contact
