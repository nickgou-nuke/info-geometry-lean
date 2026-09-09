import Mathlib
import InfoGeometry.SignedNetwork.ExactCancellation

/-! Finite marked-event laws.  The `none` mark is an absorbing outcome when
the supplied total rate is zero; no continuous-time process is asserted here.
-/
namespace InfoGeometry.SignedNetwork.BranchingEventLaw

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]

abbrev Event (C : Type*) := C × C

def rate (r : C → C → ℝ) (e : Event C) : ℝ := r e.1 e.2

def totalRate (r : C → C → ℝ) : ℝ := ∑ x, ∑ y, r x y

def probability (r : C → C → ℝ) : Option (Event C) → ℝ
  | none => if totalRate r = 0 then 1 else 0
  | some e => if totalRate r = 0 then 0 else rate r e / totalRate r

theorem probability_nonneg (r : C → C → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (e : Option (Event C)) : 0 ≤ probability r e := by
  cases e with
  | none => simp [probability]; split_ifs <;> norm_num
  | some e =>
      unfold probability
      split_ifs
      · exact le_rfl
      · exact div_nonneg (hr _ _) (Finset.sum_nonneg fun x _ =>
          Finset.sum_nonneg fun y _ => hr _ _)

theorem totalRate_nonneg (r : C → C → ℝ) (hr : ∀ x y, 0 ≤ r x y) :
    0 ≤ totalRate r :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hr _ _

theorem sum_probability (r : C → C → ℝ) (hr : ∀ x y, 0 ≤ r x y) :
    (∑ e, probability r e) = 1 := by
  classical
  by_cases h : totalRate r = 0
  · simp [Fintype.sum_option, probability, h]
  · simp only [Fintype.sum_option, probability, h, if_false, zero_add, add_zero]
    rw [← Finset.sum_div]
    convert div_self h using 1 <;>
      simp [Fintype.sum_prod_type, rate, totalRate]

def eventPMF (r : C → C → ℝ) (hr : ∀ x y, 0 ≤ r x y) :
    PMF (Option (Event C)) :=
  PMF.ofFintype (fun e => ENNReal.ofReal (probability r e)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun e _ => probability_nonneg r hr e), sum_probability r hr]
    simp)

@[simp] theorem eventPMF_toReal (r : C → C → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (e : Option (Event C)) : (eventPMF r hr e).toReal = probability r e := by
  exact ENNReal.toReal_ofReal (probability_nonneg r hr e)

def applyEvent (p : InfoGeometry.SignedNetwork.ExactCancellation.Counts C)
    (e : Event C) : InfoGeometry.SignedNetwork.ExactCancellation.Counts C :=
  { positive := fun x => p.positive x + if x = e.2 then 1 else 0
    negative := fun x => p.negative x + if x = e.1 then 1 else 0 }

theorem applyEvent_signed (p : InfoGeometry.SignedNetwork.ExactCancellation.Counts C)
    (e : Event C) (x : C) :
    (InfoGeometry.SignedNetwork.ExactCancellation.signed (applyEvent p e)) x =
      InfoGeometry.SignedNetwork.ExactCancellation.signed p x +
        (if x = e.2 then 1 else 0) - (if x = e.1 then 1 else 0) := by
  simp [applyEvent, InfoGeometry.SignedNetwork.ExactCancellation.signed]
  ring

end
end InfoGeometry.SignedNetwork.BranchingEventLaw
