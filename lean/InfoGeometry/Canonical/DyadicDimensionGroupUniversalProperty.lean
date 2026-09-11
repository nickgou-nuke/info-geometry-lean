import InfoGeometry.Canonical.DyadicDimensionGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical

/-!
# Universal property of the dyadic direct-limit carrier

The bonding maps are `ℤ → ℤ`, `z ↦ 2z`. A cocone is therefore a family of
additive maps whose next-stage value on `2z` agrees with the current-stage
value on `z`. The resulting lift is constructed on the existing
`DyadicRational` carrier and transported through its canonical equivalence
with `DyadicDirectLimit`.
-/

structure DyadicCocone (G : Type*) [AddCommGroup G] where
  leg : ℕ → ℤ →+ G
  compatible : ∀ n z, leg (n + 1) (2 * z) = leg n z

namespace DyadicCocone

variable {G : Type*} [AddCommGroup G]

lemma leg_iterate (C : DyadicCocone G) (n k : ℕ) (z : ℤ) :
    C.leg (n + k) ((2 : ℤ) ^ k * z) = C.leg n z := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        C.leg (n + (k + 1)) ((2 : ℤ) ^ (k + 1) * z) =
            C.leg ((n + k) + 1) (2 * ((2 : ℤ) ^ k * z)) := by
              congr 1 <;> ring
        _ = C.leg (n + k) ((2 : ℤ) ^ k * z) := by
              simpa using C.compatible (n + k) ((2 : ℤ) ^ k * z)
        _ = C.leg n z := ih

lemma leg_eq_of_fraction_eq
    (C : DyadicCocone G) {z w : ℤ} {n m : ℕ}
    (h : (z : ℚ) / (2 : ℚ) ^ n = (w : ℚ) / (2 : ℚ) ^ m) :
    C.leg n z = C.leg m w := by
  have hcross :=
    (dyadicRepresentative_rel_iff_cross
      (⟨z, n⟩ : DyadicRepresentative)
      (⟨w, m⟩ : DyadicRepresentative)).mp h
  calc
    C.leg n z = C.leg (n + m) ((2 : ℤ) ^ m * z) :=
      (C.leg_iterate n m z).symm
    _ = C.leg (n + m) ((2 : ℤ) ^ n * w) := congrArg (C.leg (n + m)) hcross
    _ = C.leg (m + n) ((2 : ℤ) ^ n * w) := by rw [Nat.add_comm]
    _ = C.leg m w := C.leg_iterate m n w

noncomputable def representative (q : DyadicRational) : DyadicRepresentative :=
  let z := Classical.choose q.property
  let hz := Classical.choose_spec q.property
  let n := Classical.choose hz
  ⟨z, n⟩

lemma representative_spec (q : DyadicRational) :
    (q : ℚ) =
      (representative q).numerator /
        (2 : ℚ) ^ (representative q).level := by
  dsimp [representative]
  exact Classical.choose_spec (Classical.choose_spec q.property)

noncomputable def value (C : DyadicCocone G) (q : DyadicRational) : G :=
  C.leg (representative q).level (representative q).numerator

lemma value_eq_leg_of_representation
    (C : DyadicCocone G) (q : DyadicRational)
    {z : ℤ} {n : ℕ}
    (hq : (q : ℚ) = (z : ℚ) / (2 : ℚ) ^ n) :
    C.value q = C.leg n z := by
  apply C.leg_eq_of_fraction_eq
  calc
    (representative q).numerator / (2 : ℚ) ^ (representative q).level =
        (q : ℚ) := (representative_spec q).symm
    _ = (z : ℚ) / (2 : ℚ) ^ n := hq

noncomputable def lift (C : DyadicCocone G) : DyadicRational →+ G where
  toFun := C.value
  map_zero' := by
    rw [C.value_eq_leg_of_representation (0 : DyadicRational) (z := 0) (n := 0)]
    · simp
    · norm_num
  map_add' := by
    intro q r
    rcases q.property with ⟨z, n, hq⟩
    rcases r.property with ⟨w, m, hr⟩
    let t : ℤ := z * (2 : ℤ) ^ m + w * (2 : ℤ) ^ n
    have hsum : (q + r : ℚ) = (t : ℚ) / (2 : ℚ) ^ (n + m) := by
      rw [show (q : ℚ) = (z : ℚ) / (2 : ℚ) ^ n from hq,
        show (r : ℚ) = (w : ℚ) / (2 : ℚ) ^ m from hr]
      dsimp [t]
      have hn : (2 : ℚ) ^ n ≠ 0 := by positivity
      have hm : (2 : ℚ) ^ m ≠ 0 := by positivity
      field_simp [hn, hm]
      push_cast
      ring
    calc
      C.value (q + r) = C.leg (n + m) t :=
        C.value_eq_leg_of_representation (q + r) (z := t) (n := n + m) hsum
      _ = C.leg (n + m) ((2 : ℤ) ^ m * z) +
          C.leg (n + m) ((2 : ℤ) ^ n * w) := by
            rw [show t = (2 : ℤ) ^ m * z + (2 : ℤ) ^ n * w by
              dsimp [t]; ring, map_add]
      _ = C.leg n z + C.leg m w := by
            rw [C.leg_iterate n m z]
            simpa [Nat.add_comm] using congrArg id (C.leg_iterate m n w)
      _ = C.value q + C.value r := by
            rw [C.value_eq_leg_of_representation q (z := z) (n := n) hq,
              C.value_eq_leg_of_representation r (z := w) (n := m) hr]

noncomputable def liftToDirectLimit (C : DyadicCocone G) :
    DyadicDirectLimit →+ G :=
  (C.lift).comp dyadicDirectLimitAddEquiv

theorem lift_stage (C : DyadicCocone G) (n : ℕ) (z : ℤ) :
    C.lift (dyadicStageMap n z) = C.leg n z := by
  apply C.value_eq_leg_of_representation (dyadicStageMap n z) (z := z) (n := n)
  rfl

theorem liftToDirectLimit_stage (C : DyadicCocone G) (n : ℕ) (z : ℤ) :
    C.liftToDirectLimit (Quotient.mk _ ⟨z, n⟩) = C.leg n z := by
  rw [liftToDirectLimit, AddMonoidHom.comp_apply]
  change C.lift (dyadicStageMap n z) = _
  exact C.lift_stage n z

theorem liftToDirectLimit_unique
    (C : DyadicCocone G) (f : DyadicDirectLimit →+ G)
    (hf : ∀ n z, f (Quotient.mk _ ⟨z, n⟩) = C.leg n z) :
    f = C.liftToDirectLimit := by
  ext x
  induction x using Quotient.inductionOn with
  | _ rep =>
      rcases rep with ⟨z, n⟩
      rw [hf, C.liftToDirectLimit_stage]

end DyadicCocone

end InfoGeometry.Canonical
