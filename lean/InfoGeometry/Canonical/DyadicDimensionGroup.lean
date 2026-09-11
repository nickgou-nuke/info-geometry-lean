import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The concrete dyadic direct-limit group

This owner models the additive colimit of
`ℤ --×2--> ℤ --×2--> ...` by quotienting stage representatives.  Its
canonical additive equivalence with the subgroup of dyadic rationals is
proved explicitly.  No `K₀`, `KO₀`, C*-completion, or state-space theorem is
claimed here.
-/

namespace InfoGeometry.Canonical

noncomputable section

structure DyadicRepresentative where
  numerator : ℤ
  level : ℕ

def dyadicRepresentativeValue (x : DyadicRepresentative) : ℚ :=
  (x.numerator : ℚ) / (2 : ℚ) ^ x.level

def dyadicRepresentativeRel (x y : DyadicRepresentative) : Prop :=
  dyadicRepresentativeValue x = dyadicRepresentativeValue y

instance : Setoid DyadicRepresentative where
  r := dyadicRepresentativeRel
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

theorem dyadicRepresentativeRel_iff_value_eq
    (x y : DyadicRepresentative) :
    x ≈ y ↔ dyadicRepresentativeValue x =
      dyadicRepresentativeValue y := Iff.rfl

theorem dyadicRepresentative_rel_iff_cross
    (x y : DyadicRepresentative) :
    x ≈ y ↔
      (2 : ℤ) ^ y.level * x.numerator =
        (2 : ℤ) ^ x.level * y.numerator := by
  change ((x.numerator : ℚ) / (2 : ℚ) ^ x.level =
    (y.numerator : ℚ) / (2 : ℚ) ^ y.level) ↔ _
  constructor
  · intro h
    have hx : (2 : ℚ) ^ x.level ≠ 0 := by positivity
    have hy : (2 : ℚ) ^ y.level ≠ 0 := by positivity
    field_simp [hx, hy] at h
    have h' : (x.numerator : ℚ) * (2 : ℚ) ^ y.level =
        (2 : ℚ) ^ x.level * y.numerator := by
      simpa [mul_comm] using h
    norm_cast at h'
    simpa [mul_comm] using h'
  · intro h
    have hx : (2 : ℚ) ^ x.level ≠ 0 := by positivity
    have hy : (2 : ℚ) ^ y.level ≠ 0 := by positivity
    field_simp [hx, hy]
    have h' : (2 : ℤ) ^ y.level * x.numerator =
        y.numerator * (2 : ℤ) ^ x.level := by
      simpa [mul_comm] using h
    have h'' : x.numerator * (2 : ℤ) ^ y.level =
        (2 : ℤ) ^ x.level * y.numerator := by
      calc
        x.numerator * (2 : ℤ) ^ y.level =
            (2 : ℤ) ^ y.level * x.numerator := by ring
        _ = y.numerator * (2 : ℤ) ^ x.level := h'
        _ = (2 : ℤ) ^ x.level * y.numerator := by ring
    exact_mod_cast h''

theorem dyadicRepresentativeRel_iff_cross
    (x y : DyadicRepresentative) :
    x ≈ y ↔
      (2 : ℤ) ^ y.level * x.numerator =
        (2 : ℤ) ^ x.level * y.numerator :=
  dyadicRepresentative_rel_iff_cross x y

def dyadicRepresentativeAdd (x y : DyadicRepresentative) :
    DyadicRepresentative :=
  ⟨x.numerator * (2 : ℤ) ^ y.level +
      y.numerator * (2 : ℤ) ^ x.level, x.level + y.level⟩

def dyadicRepresentativeNeg (x : DyadicRepresentative) :
    DyadicRepresentative :=
  ⟨-x.numerator, x.level⟩

def dyadicRepresentativeZero : DyadicRepresentative := ⟨0, 0⟩

theorem dyadicRepresentativeValue_add (x y : DyadicRepresentative) :
    dyadicRepresentativeValue (dyadicRepresentativeAdd x y) =
      dyadicRepresentativeValue x + dyadicRepresentativeValue y := by
  dsimp [dyadicRepresentativeValue, dyadicRepresentativeAdd]
  push_cast
  field_simp [pow_ne_zero]
  ring

theorem dyadicRepresentativeValue_neg (x : DyadicRepresentative) :
    dyadicRepresentativeValue (dyadicRepresentativeNeg x) =
      -dyadicRepresentativeValue x := by
  dsimp [dyadicRepresentativeValue, dyadicRepresentativeNeg]
  ring

theorem dyadicRepresentativeValue_zero :
    dyadicRepresentativeValue dyadicRepresentativeZero = 0 := by
  simp [dyadicRepresentativeValue, dyadicRepresentativeZero]

/-! The explicit quotient carrier. -/

abbrev DyadicDirectLimit :=
  Quotient (inferInstance : Setoid DyadicRepresentative)

noncomputable def dyadicDirectLimitAdd :
    DyadicDirectLimit → DyadicDirectLimit → DyadicDirectLimit :=
  fun x y => Quotient.liftOn₂ x y
    (fun x y => Quotient.mk' (dyadicRepresentativeAdd x y))
    (by
      intro x y x' y' hxx' hyy'
      apply Quotient.sound
      change dyadicRepresentativeValue x =
          dyadicRepresentativeValue x' at hxx'
      change dyadicRepresentativeValue y =
          dyadicRepresentativeValue y' at hyy'
      change dyadicRepresentativeValue
          (dyadicRepresentativeAdd x y) =
        dyadicRepresentativeValue
          (dyadicRepresentativeAdd x' y')
      have hx := hxx'
      have hy := hyy'
      rw [dyadicRepresentativeValue_add, dyadicRepresentativeValue_add,
        hx, hy])

noncomputable def dyadicDirectLimitNeg : DyadicDirectLimit → DyadicDirectLimit :=
  fun x => Quotient.liftOn x
    (fun x => Quotient.mk' (dyadicRepresentativeNeg x))
    (by
      intro x y hxy
      apply Quotient.sound
      change dyadicRepresentativeValue x =
          dyadicRepresentativeValue y at hxy
      change dyadicRepresentativeValue
          (dyadicRepresentativeNeg x) =
        dyadicRepresentativeValue (dyadicRepresentativeNeg y)
      rw [dyadicRepresentativeValue_neg, dyadicRepresentativeValue_neg,
        hxy])

noncomputable instance : Add DyadicDirectLimit := ⟨dyadicDirectLimitAdd⟩
noncomputable instance : Neg DyadicDirectLimit := ⟨dyadicDirectLimitNeg⟩
noncomputable instance : Zero DyadicDirectLimit :=
  ⟨Quotient.mk' dyadicRepresentativeZero⟩

noncomputable instance : AddCommGroup DyadicDirectLimit where
  add_assoc x y z := by
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    change Quotient.mk' (dyadicRepresentativeAdd
      (dyadicRepresentativeAdd a b) c) =
      Quotient.mk' (dyadicRepresentativeAdd
        a (dyadicRepresentativeAdd b c))
    apply Quotient.sound
    change dyadicRepresentativeValue
        (dyadicRepresentativeAdd
          (dyadicRepresentativeAdd a b) c) =
      dyadicRepresentativeValue
        (dyadicRepresentativeAdd
          a (dyadicRepresentativeAdd b c))
    simp only [dyadicRepresentativeValue_add]
    abel
  zero_add x := by
    refine Quotient.inductionOn x ?_
    intro a
    change Quotient.mk' (dyadicRepresentativeAdd
      dyadicRepresentativeZero a) = Quotient.mk' a
    apply Quotient.sound
    change dyadicRepresentativeValue
        (dyadicRepresentativeAdd dyadicRepresentativeZero a) =
      dyadicRepresentativeValue a
    simp only [dyadicRepresentativeValue_add,
      dyadicRepresentativeValue_zero]
    abel
  add_zero x := by
    refine Quotient.inductionOn x ?_
    intro a
    change Quotient.mk' (dyadicRepresentativeAdd
      a dyadicRepresentativeZero) = Quotient.mk' a
    apply Quotient.sound
    change dyadicRepresentativeValue
        (dyadicRepresentativeAdd a dyadicRepresentativeZero) =
      dyadicRepresentativeValue a
    simp only [dyadicRepresentativeValue_add,
      dyadicRepresentativeValue_zero]
    abel
  add_comm x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change Quotient.mk' (dyadicRepresentativeAdd a b) =
      Quotient.mk' (dyadicRepresentativeAdd b a)
    apply Quotient.sound
    change dyadicRepresentativeValue
        (dyadicRepresentativeAdd a b) =
      dyadicRepresentativeValue (dyadicRepresentativeAdd b a)
    simp only [dyadicRepresentativeValue_add]
    abel
  neg_add_cancel x := by
    refine Quotient.inductionOn x ?_
    intro a
    change Quotient.mk' (dyadicRepresentativeAdd
      (dyadicRepresentativeNeg a) a) =
      Quotient.mk' dyadicRepresentativeZero
    apply Quotient.sound
    change dyadicRepresentativeValue
        (dyadicRepresentativeAdd (dyadicRepresentativeNeg a) a) =
      dyadicRepresentativeValue dyadicRepresentativeZero
    simp only [dyadicRepresentativeValue_add,
      dyadicRepresentativeValue_neg,
      dyadicRepresentativeValue_zero]
    abel
  nsmul := nsmulRec
  zsmul := zsmulRec

def dyadicBond (n : ℕ) : ℤ →+ ℤ where
  toFun z := 2 * z
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

def dyadicStage (n : ℕ) (z : ℤ) : DyadicDirectLimit :=
  Quotient.mk' ⟨z, n⟩

def dyadicRational : AddSubgroup ℚ where
  carrier := {q | ∃ z : ℤ, ∃ n : ℕ, q = (z : ℚ) / (2 : ℚ) ^ n}
  zero_mem' := by exact ⟨0, 0, by norm_num⟩
  add_mem' := by
    rintro x y ⟨z, n, rfl⟩ ⟨w, m, rfl⟩
    refine ⟨z * (2 : ℤ) ^ m + w * (2 : ℤ) ^ n, n + m, ?_⟩
    push_cast
    field_simp [pow_ne_zero]
    ring
  neg_mem' := by
    rintro x ⟨z, n, rfl⟩
    refine ⟨-z, n, ?_⟩
    change -(↑z / (2 : ℚ) ^ n) = (-↑z : ℚ) / (2 : ℚ) ^ n
    ring

abbrev DyadicRational := ↥dyadicRational

def dyadicStageMap (n : ℕ) : ℤ →+ DyadicRational where
  toFun z := ⟨(z : ℚ) / (2 : ℚ) ^ n, z, n, rfl⟩
  map_zero' := by ext; simp
  map_add' x y := by
    ext
    push_cast
    ring

theorem dyadicStageMap_succ (n : ℕ) (z : ℤ) :
    dyadicStageMap (n + 1) (dyadicBond n z) = dyadicStageMap n z := by
  ext
  dsimp [dyadicStageMap, dyadicBond]
  rw [pow_succ]
  field_simp [pow_ne_zero]
  norm_cast

theorem dyadicStageMap_bond (n : ℕ) (z : ℤ) :
    dyadicStageMap (n + 1) (dyadicBond n z) = dyadicStageMap n z :=
  dyadicStageMap_succ n z

theorem dyadicStage_add (n : ℕ) (x y : ℤ) :
    dyadicStage n x + dyadicStage n y = dyadicStage n (x + y) := by
  change Quotient.mk' (dyadicRepresentativeAdd
    ⟨x, n⟩ ⟨y, n⟩) = Quotient.mk' ⟨x + y, n⟩
  apply Quotient.sound
  change dyadicRepresentativeValue
      (dyadicRepresentativeAdd ⟨x, n⟩ ⟨y, n⟩) =
    dyadicRepresentativeValue ⟨x + y, n⟩
  dsimp [dyadicRepresentativeValue, dyadicRepresentativeAdd]
  have hn : (2 : ℚ) ^ n ≠ 0 := by positivity
  field_simp [hn]
  rw [pow_add]
  push_cast
  ring

theorem dyadicStage_neg (n : ℕ) (x : ℤ) :
    -dyadicStage n x = dyadicStage n (-x) := by
  change Quotient.mk' (dyadicRepresentativeNeg ⟨x, n⟩) =
    Quotient.mk' ⟨-x, n⟩
  apply Quotient.sound
  change dyadicRepresentativeValue
      (dyadicRepresentativeNeg ⟨x, n⟩) =
    dyadicRepresentativeValue ⟨-x, n⟩
  simp [dyadicRepresentativeValue, dyadicRepresentativeNeg]

theorem dyadicStage_bond (n : ℕ) (z : ℤ) :
    dyadicStage (n + 1) (dyadicBond n z) = dyadicStage n z := by
  apply Quotient.sound
  change dyadicRepresentativeValue
      ⟨2 * z, n + 1⟩ = dyadicRepresentativeValue ⟨z, n⟩
  simp [dyadicRepresentativeValue, dyadicBond, pow_succ]
  ring

theorem dyadicDirectLimit_representation (x : DyadicDirectLimit) :
    ∃ n : ℕ, ∃ z : ℤ, dyadicStage n z = x := by
  induction x using Quotient.inductionOn with
  | _ rep => exact ⟨rep.level, rep.numerator, rfl⟩

noncomputable def dyadicDirectLimitReadout :
    DyadicDirectLimit →+ DyadicRational where
  toFun := Quotient.lift
    (fun x => ⟨dyadicRepresentativeValue x,
      ⟨x.numerator, x.level, rfl⟩⟩)
    (by
      intro x y hxy
      apply Subtype.ext
      exact hxy)
  map_zero' := by
    change (⟨dyadicRepresentativeValue dyadicRepresentativeZero,
      _⟩ : DyadicRational) = 0
    apply Subtype.ext
    exact dyadicRepresentativeValue_zero
  map_add' := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro x y
    change (⟨dyadicRepresentativeValue
        (dyadicRepresentativeAdd x y), _⟩ : DyadicRational) = _
    apply Subtype.ext
    exact dyadicRepresentativeValue_add x y

noncomputable def dyadicDirectLimitInverse :
    DyadicRational → DyadicDirectLimit := fun q =>
  let z := Classical.choose q.property
  let hz := Classical.choose_spec q.property
  let n := Classical.choose hz
  dyadicStage n z

theorem dyadicDirectLimitInverse_readout (q : DyadicRational) :
    dyadicDirectLimitReadout (dyadicDirectLimitInverse q) = q := by
  apply Subtype.ext
  dsimp [dyadicDirectLimitInverse, dyadicDirectLimitReadout,
    dyadicStage]
  exact (Classical.choose_spec (Classical.choose_spec q.property)).symm

theorem dyadicDirectLimitReadout_inverse (x : DyadicDirectLimit) :
    dyadicDirectLimitInverse (dyadicDirectLimitReadout x) = x := by
  induction x using Quotient.inductionOn with
  | _ rep =>
      apply Quotient.sound
      dsimp [dyadicDirectLimitInverse, dyadicDirectLimitReadout]
      change dyadicRepresentativeValue
          ⟨Classical.choose _, Classical.choose _⟩ =
        dyadicRepresentativeValue rep
      exact (Classical.choose_spec (Classical.choose_spec
        (show dyadicRepresentativeValue rep ∈ dyadicRational from
          ⟨rep.numerator, rep.level, rfl⟩))).symm

noncomputable def dyadicDirectLimitEquiv :
    DyadicDirectLimit ≃+ DyadicRational :=
  { toEquiv :=
      { toFun := dyadicDirectLimitReadout
        invFun := dyadicDirectLimitInverse
        left_inv := dyadicDirectLimitReadout_inverse
        right_inv := dyadicDirectLimitInverse_readout }
    map_add' := dyadicDirectLimitReadout.map_add }

noncomputable abbrev dyadicDirectLimitAddEquiv :
    DyadicDirectLimit ≃+ DyadicRational := dyadicDirectLimitEquiv

@[simp] theorem dyadicDirectLimitEquiv_apply (q : DyadicDirectLimit) :
    dyadicDirectLimitEquiv q = dyadicDirectLimitReadout q := rfl

@[simp] theorem dyadicDirectLimitEquiv_stage (n : ℕ) (z : ℤ) :
    dyadicDirectLimitEquiv (dyadicStage n z) = dyadicStageMap n z := by
  apply Subtype.ext
  rfl

theorem dyadicDirectLimit_stage_compatible (n : ℕ) (z : ℤ) :
    dyadicStageMap (n + 1) (dyadicBond n z) = dyadicStageMap n z :=
  dyadicStageMap_succ n z

end
end InfoGeometry.Canonical
