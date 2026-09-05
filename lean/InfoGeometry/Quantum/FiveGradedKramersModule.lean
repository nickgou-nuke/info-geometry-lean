import InfoGeometry.Quantum.ComplexKramersAntiunitary

/-!
# A five-graded complex Kramers module

This is the finite representation-theoretic carrier behind the statement that
a square-minus-one antiunitary reverses contact degree.  The five weights are
`-2,-1,0,1,2`; the Kramers operator combines the canonical antiunitary on
`ℂ²` with reversal of the weight index.

The resulting operator has square `-1`, anticommutes with the Euler grading
operator, and maps every homogeneous component of weight `k` to the component
of weight `-k` while preserving the derived parity modulo two.
-/

noncomputable section

namespace InfoGeometry.Quantum.FiveGradedKramersModule

open InfoGeometry.Quantum.ComplexKramersAntiunitary

/-- The five contact weights. -/
inductive Weight where
  | minus2
  | minus1
  | zero
  | plus1
  | plus2
  deriving DecidableEq, Fintype, Repr

/-- Integer value of a contact weight. -/
def Weight.value : Weight → ℤ
  | .minus2 => -2
  | .minus1 => -1
  | .zero => 0
  | .plus1 => 1
  | .plus2 => 2

/-- Opposition of the contact grading. -/
def Weight.opposite : Weight → Weight
  | .minus2 => .plus2
  | .minus1 => .plus1
  | .zero => .zero
  | .plus1 => .minus1
  | .plus2 => .minus2

@[simp] theorem Weight.opposite_opposite (w : Weight) :
    w.opposite.opposite = w := by
  cases w <;> rfl

@[simp] theorem Weight.value_opposite (w : Weight) :
    w.opposite.value = -w.value := by
  cases w <;> rfl

/-- Derived fermion parity of the integer contact weight. -/
def Weight.parity (w : Weight) : ZMod 2 :=
  (w.value : ZMod 2)

@[simp] theorem Weight.parity_opposite (w : Weight) :
    w.opposite.parity = w.parity := by
  unfold Weight.parity
  rw [Weight.value_opposite, Int.cast_neg]
  exact ZMod.neg_eq_self_mod_two _

/-- Five graded copies of the canonical two-component Kramers carrier. -/
abbrev Carrier := Weight → H2

/-- Euler/degree operator. -/
def euler : Module.End ℂ Carrier where
  toFun ψ w := (w.value : ℂ) • ψ w
  map_add' ψ φ := by
    funext w
    simp [smul_add]
  map_smul' c ψ := by
    funext w
    simp only [Pi.smul_apply, smul_smul]
    ring

@[simp] theorem euler_apply (ψ : Carrier) (w : Weight) :
    euler ψ w = (w.value : ℂ) • ψ w := rfl

/-- Kramers operator: reverse the grade and apply the canonical antiunitary. -/
def kramers : Carrier ≃ₗ⋆[ℂ] Carrier where
  toFun ψ w := timeReversal (ψ w.opposite)
  invFun ψ w := -timeReversal (ψ w.opposite)
  left_inv ψ := by
    funext w
    simp [Weight.opposite_opposite]
  right_inv ψ := by
    funext w
    simp [Weight.opposite_opposite]
  map_add' ψ φ := by
    funext w
    simp
  map_smul' c ψ := by
    funext w
    simp

@[simp] theorem kramers_apply (ψ : Carrier) (w : Weight) :
    kramers ψ w = timeReversal (ψ w.opposite) := rfl

/-- Global Kramers square on the five-graded carrier. -/
@[simp] theorem kramers_sq (ψ : Carrier) :
    kramers (kramers ψ) = -ψ := by
  funext w
  simp [Weight.opposite_opposite]

@[simp] theorem kramers_fourth (ψ : Carrier) :
    kramers (kramers (kramers (kramers ψ))) = ψ := by
  simp

/-- The Kramers operator reverses the Euler grading. -/
theorem euler_kramers_anticommute (ψ : Carrier) :
    euler (kramers ψ) = -kramers (euler ψ) := by
  funext w
  cases w <;> simp [euler, kramers, Weight.value, Weight.opposite]

/-- Homogeneous-vector predicate for the Euler action. -/
def HasGrade (k : ℤ) (ψ : Carrier) : Prop :=
  euler ψ = (k : ℂ) • ψ

/-- Grade reversal for arbitrary homogeneous vectors. -/
theorem kramers_hasGrade_neg {k : ℤ} {ψ : Carrier}
    (hψ : HasGrade k ψ) :
    HasGrade (-k) (kramers ψ) := by
  unfold HasGrade at hψ ⊢
  rw [euler_kramers_anticommute, hψ]
  simp

/-- Inclusion of one homogeneous fibre. -/
def include (w : Weight) : H2 →ₗ[ℂ] Carrier where
  toFun v q := if q = w then v else 0
  map_add' u v := by
    funext q
    by_cases hq : q = w <;> simp [hq]
  map_smul' c v := by
    funext q
    by_cases hq : q = w <;> simp [hq]

@[simp] theorem include_same (w : Weight) (v : H2) :
    include w v w = v := by
  simp [include]

@[simp] theorem include_ne {w q : Weight} (hqw : q ≠ w) (v : H2) :
    include w v q = 0 := by
  simp [include, hqw]

/-- Every included fibre vector has its declared integer grade. -/
theorem include_hasGrade (w : Weight) (v : H2) :
    HasGrade w.value (include w v) := by
  unfold HasGrade
  funext q
  by_cases hq : q = w
  · subst q
    simp [euler, include]
  · simp [euler, include, hq]

/-- Kramers transport exchanges opposite homogeneous fibres. -/
theorem kramers_include (w : Weight) (v : H2) :
    kramers (include w v) = include w.opposite (timeReversal v) := by
  funext q
  cases q <;> cases w <;> simp [kramers, include, Weight.opposite]

/-- The five-grade and Kramers-parity packet. -/
theorem five_graded_kramers_packet (w : Weight) (v : H2) :
    HasGrade w.value (include w v) ∧
      HasGrade (-w.value) (kramers (include w v)) ∧
      w.opposite.parity = w.parity ∧
      kramers (kramers (include w v)) = -include w v := by
  exact ⟨include_hasGrade w v,
    kramers_hasGrade_neg (include_hasGrade w v),
    Weight.parity_opposite w,
    kramers_sq (include w v)⟩

end InfoGeometry.Quantum.FiveGradedKramersModule
