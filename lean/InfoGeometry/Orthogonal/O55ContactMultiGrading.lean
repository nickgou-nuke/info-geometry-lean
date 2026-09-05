import InfoGeometry.Orthogonal.O55ContactFiveGrading
import Mathlib.Data.ZMod.Basic

/-!
# Multiple gradings on the `(5,5)` contact carrier

The vector carrier has three Euler weights.  Endomorphisms therefore carry a
`3 × 3` source/target block bigrading.  Its difference is the contact
five-degree, and reduction modulo two is the induced parity.  These gradings
are kept distinct and connected by explicit maps.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

inductive Weight3
  | minus
  | zero
  | plus
  deriving DecidableEq, Fintype, Repr

namespace Weight3

def value : Weight3 → ℤ
  | minus => -1
  | zero => 0
  | plus => 1

def valueR (w : Weight3) : ℝ := (w.value : ℝ)

def opposite : Weight3 → Weight3
  | minus => plus
  | zero => zero
  | plus => minus

@[simp] theorem opposite_opposite (w : Weight3) :
    w.opposite.opposite = w := by cases w <;> rfl

@[simp] theorem value_opposite (w : Weight3) :
    w.opposite.value = -w.value := by cases w <;> rfl

@[simp] theorem valueR_opposite (w : Weight3) :
    w.opposite.valueR = -w.valueR := by
  cases w <;> norm_num [valueR, value]
end Weight3

def weightOfIndex : Fin 10 → Weight3 :=
  ![Weight3.minus, Weight3.minus,
    Weight3.zero, Weight3.zero, Weight3.zero,
    Weight3.zero, Weight3.zero, Weight3.zero,
    Weight3.plus, Weight3.plus]

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
    by_cases hi : weightOfIndex i = w <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : weightOfIndex i = w <;> simp [hi]

@[simp] theorem weightProjector_apply (w : Weight3)
    (x : Vector55) (i : Fin 10) :
    weightProjector w x i = if weightOfIndex i = w then x i else 0 := rfl

theorem weightProjector_sq (w : Weight3) :
    weightProjector w * weightProjector w = weightProjector w := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases hi : weightOfIndex i = w <;>
    simp [Module.End.mul_apply, weightProjector_apply, hi]

theorem weightProjector_mul_of_ne {u v : Weight3} (h : u ≠ v) :
    weightProjector u * weightProjector v = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases hi : weightOfIndex i = u
  · have hiv : weightOfIndex i ≠ v := by
      intro hiv
      exact h (hi.symm.trans hiv)
    simp [Module.End.mul_apply, weightProjector_apply, hi, hiv]
  · simp [Module.End.mul_apply, weightProjector_apply, hi]

theorem weightProjector_resolution :
    weightProjector Weight3.minus +
        weightProjector Weight3.zero +
      weightProjector Weight3.plus = (1 : End55) := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;> simp [weightProjector_apply, weightOfIndex]

theorem euler_mul_weightProjector (w : Weight3) :
    contactEulerEnd * weightProjector w =
      w.valueR • weightProjector w := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases hi : weightOfIndex i = w
  · have hw : contactWeightR i = w.valueR := by
      rw [contactWeightR_eq_weightValueR, hi]
    simp [Module.End.mul_apply, weightProjector_apply, hi,
      contactEulerEnd_apply, hw]
  · simp [Module.End.mul_apply, weightProjector_apply, hi,
      contactEulerEnd_apply]

theorem weightProjector_mul_euler (w : Weight3) :
    weightProjector w * contactEulerEnd =
      w.valueR • weightProjector w := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases hi : weightOfIndex i = w
  · have hw : contactWeightR i = w.valueR := by
      rw [contactWeightR_eq_weightValueR, hi]
    simp [Module.End.mul_apply, weightProjector_apply, hi,
      contactEulerEnd_apply, hw]
  · simp [Module.End.mul_apply, weightProjector_apply, hi]

structure BlockDegree where
  target : Weight3
  source : Weight3
  deriving DecidableEq, Fintype, Repr

namespace BlockDegree

def contact (d : BlockDegree) : ℤ :=
  d.target.value - d.source.value

def parity (d : BlockDegree) : ZMod 2 :=
  (d.contact : ZMod 2)

def opposite (d : BlockDegree) : BlockDegree :=
  ⟨d.target.opposite, d.source.opposite⟩

@[simp] theorem opposite_opposite (d : BlockDegree) :
    d.opposite.opposite = d := by
  cases d
  simp [opposite]

@[simp] theorem contact_opposite (d : BlockDegree) :
    d.opposite.contact = -d.contact := by
  cases d
  simp [opposite, contact]
  ring

@[simp] theorem parity_opposite (d : BlockDegree) :
    d.opposite.parity = d.parity := by
  unfold parity
  rw [contact_opposite]
  change -((d.contact : ZMod 2)) = (d.contact : ZMod 2)
  ring
end BlockDegree

def blockComponent (d : BlockDegree) (A : End55) : End55 :=
  weightProjector d.target * A * weightProjector d.source

theorem blockComponent_grade (d : BlockDegree) (A : End55) :
    endCommutator contactEulerEnd (blockComponent d A) =
      (d.contact : ℝ) • blockComponent d A := by
  unfold blockComponent BlockDegree.contact endCommutator
  calc
    contactEulerEnd *
          (weightProjector d.target * A * weightProjector d.source) -
        (weightProjector d.target * A * weightProjector d.source) *
          contactEulerEnd =
      (contactEulerEnd * weightProjector d.target) * A *
          weightProjector d.source -
        weightProjector d.target * A *
          (weightProjector d.source * contactEulerEnd) := by
            noncomm_ring
    _ = (d.target.valueR • weightProjector d.target) * A *
          weightProjector d.source -
        weightProjector d.target * A *
          (d.source.valueR • weightProjector d.source) := by
            rw [euler_mul_weightProjector, weightProjector_mul_euler]
    _ = (d.contact : ℝ) •
        (weightProjector d.target * A * weightProjector d.source) := by
          simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
            Weight3.valueR, Int.cast_sub]
          module

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

theorem matching_block_degree_add
    (target middle source : Weight3) :
    (BlockDegree.mk target middle).contact +
        (BlockDegree.mk middle source).contact =
      (BlockDegree.mk target source).contact := by
  simp [BlockDegree.contact]
  ring

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
  · have hdual : weightOfIndex (dualIndex i) = w := by
      rw [weightOfIndex_dual, hi]
      simp
    simp [Module.End.mul_apply, weightProjector_apply, hi, hdual]
  · have hdual : weightOfIndex (dualIndex i) ≠ w := by
      intro h
      apply hi
      rw [weightOfIndex_dual, h]
      simp
    simp [Module.End.mul_apply, weightProjector_apply, hi, hdual]

theorem crosscap_blockComponent (d : BlockDegree) (A : End55) :
    crosscapEnd * blockComponent d A * crosscapEnd =
      blockComponent d.opposite
        (crosscapEnd * A * crosscapEnd) := by
  unfold blockComponent BlockDegree.opposite
  calc
    crosscapEnd *
        (weightProjector d.target * A * weightProjector d.source) *
        crosscapEnd =
      (crosscapEnd * weightProjector d.target * crosscapEnd) *
        (crosscapEnd * A * crosscapEnd) *
        (crosscapEnd * weightProjector d.source * crosscapEnd) := by
          noncomm_ring [crosscapEnd_sq]
    _ = _ := by
      rw [crosscap_weightProjector, crosscap_weightProjector]

structure MultiDegree where
  contact : ℤ
  parity : ZMod 2
  parity_eq : parity = (contact : ZMod 2)

def canonicalMultiDegree (k : ℤ) : MultiDegree :=
  ⟨k, (k : ZMod 2), rfl⟩

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
    rw [d.parity_eq]
    change (d.contact : ZMod 2) = -((d.contact : ZMod 2))
    ring

@[simp] theorem canonicalMultiDegree_add (k l : ℤ) :
    (canonicalMultiDegree k).add (canonicalMultiDegree l) =
      canonicalMultiDegree (k + l) := by
  apply MultiDegree.ext <;> rfl

@[simp] theorem canonicalMultiDegree_opposite (k : ℤ) :
    (canonicalMultiDegree k).opposite = canonicalMultiDegree (-k) := by
  apply MultiDegree.ext
  · rfl
  · change (k : ZMod 2) = ((-k : ℤ) : ZMod 2)
    ring

theorem multigraded_bracket
    {k l : ℤ} {A B : O55Lie}
    (hA : A ∈ contactGradeSpace k)
    (hB : B ∈ contactGradeSpace l) :
    ⁅A, B⁆ ∈ contactGradeSpace (k + l) ∧
      canonicalMultiDegree (k + l) =
        (canonicalMultiDegree k).add (canonicalMultiDegree l) := by
  exact ⟨contactGrade_bracket hA hB, by simp⟩

theorem multigraded_crosscap
    {k : ℤ} {A : O55Lie}
    (hA : A ∈ contactGradeSpace k) :
    crosscapConjugation A ∈ contactGradeSpace (-k) ∧
      canonicalMultiDegree (-k) =
        (canonicalMultiDegree k).opposite := by
  exact ⟨crosscap_reverses_grade hA, by simp⟩

end InfoGeometry.Orthogonal.O55Contact
