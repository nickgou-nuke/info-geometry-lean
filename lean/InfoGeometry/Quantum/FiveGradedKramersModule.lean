import InfoGeometry.Quantum.ComplexKramersAntiunitary
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Five contact grades carrying the native complex Kramers antiunitary. -/
noncomputable section
namespace InfoGeometry.Quantum.FiveGradedKramersModule

open InfoGeometry.Quantum.ComplexKramersAntiunitary

inductive Weight where
  | minus2 | minus1 | zero | plus1 | plus2
  deriving DecidableEq, Fintype, Repr

def Weight.value : Weight → ℤ
  | .minus2 => -2 | .minus1 => -1 | .zero => 0 | .plus1 => 1 | .plus2 => 2

def Weight.opposite : Weight → Weight
  | .minus2 => .plus2 | .minus1 => .plus1 | .zero => .zero
  | .plus1 => .minus1 | .plus2 => .minus2

@[simp] theorem Weight.opposite_opposite (w : Weight) :
    w.opposite.opposite = w := by cases w <;> rfl

@[simp] theorem Weight.value_opposite (w : Weight) :
    w.opposite.value = -w.value := by cases w <;> rfl

def Weight.parity (w : Weight) : ZMod 2 := (w.value : ZMod 2)

@[simp] theorem Weight.parity_opposite (w : Weight) :
    w.opposite.parity = w.parity := by
  unfold Weight.parity
  rw [Weight.value_opposite, Int.cast_neg]
  exact ZMod.neg_eq_self_mod_two _

abbrev Carrier := Weight → H2

def euler : Module.End ℂ Carrier where
  toFun ψ w := (w.value : ℂ) • ψ w
  map_add' ψ φ := by funext w; simp [smul_add]
  map_smul' c ψ := by
    funext w
    simp only [Pi.smul_apply, smul_smul]
    simp only [RingHom.id_apply]
    ring_nf

@[simp] theorem euler_apply (ψ : Carrier) (w : Weight) :
    euler ψ w = (w.value : ℂ) • ψ w := rfl

def kramers : Carrier ≃ₗ⋆[ℂ] Carrier where
  toFun ψ w := timeReversal (ψ w.opposite)
  invFun ψ w := -timeReversal (ψ w.opposite)
  left_inv ψ := by funext w; simp [Weight.opposite_opposite]
  right_inv ψ := by funext w; simp [Weight.opposite_opposite]
  map_add' ψ φ := by funext w; simp
  map_smul' c ψ := by funext w; simp

@[simp] theorem kramers_apply (ψ : Carrier) (w : Weight) :
    kramers ψ w = timeReversal (ψ w.opposite) := rfl

@[simp] theorem kramers_sq (ψ : Carrier) : kramers (kramers ψ) = -ψ := by
  funext w
  simp [Weight.opposite_opposite]

@[simp] theorem kramers_fourth (ψ : Carrier) :
    kramers (kramers (kramers (kramers ψ))) = ψ := by simp

theorem euler_kramers_anticommute (ψ : Carrier) :
    euler (kramers ψ) = -kramers (euler ψ) := by
  funext w
  cases w <;> simp [euler, kramers, Weight.value, Weight.opposite]

def HasGrade (k : ℤ) (ψ : Carrier) : Prop := euler ψ = (k : ℂ) • ψ

theorem kramers_hasGrade_neg {k : ℤ} {ψ : Carrier}
    (hψ : HasGrade k ψ) : HasGrade (-k) (kramers ψ) := by
  unfold HasGrade at hψ ⊢
  rw [euler_kramers_anticommute, hψ]
  rw [map_smulₛₗ]
  norm_num

def fibreInclude (w : Weight) : H2 →ₗ[ℂ] Carrier where
  toFun v q := if q = w then v else 0
  map_add' u v := by funext q; by_cases hq : q = w <;> simp [hq]
  map_smul' c v := by funext q; by_cases hq : q = w <;> simp [hq]

@[simp] theorem include_same (w : Weight) (v : H2) : fibreInclude w v w = v := by
  simp [fibreInclude]

@[simp] theorem include_ne {w q : Weight} (hqw : q ≠ w) (v : H2) :
    fibreInclude w v q = 0 := by simp [fibreInclude, hqw]

theorem include_hasGrade (w : Weight) (v : H2) :
    HasGrade w.value (fibreInclude w v) := by
  unfold HasGrade
  funext q
  by_cases hq : q = w
  · subst q; simp [euler, fibreInclude]
  · simp [euler, fibreInclude, hq]

theorem kramers_include (w : Weight) (v : H2) :
    kramers (fibreInclude w v) = fibreInclude w.opposite (timeReversal v) := by
  funext q
  cases q <;> cases w <;> simp [kramers, fibreInclude, Weight.opposite]

theorem five_graded_kramers_packet (w : Weight) (v : H2) :
    HasGrade w.value (fibreInclude w v) ∧
      HasGrade (-w.value) (kramers (fibreInclude w v)) ∧
      w.opposite.parity = w.parity ∧
      kramers (kramers (fibreInclude w v)) = -fibreInclude w v := by
  exact ⟨include_hasGrade w v,
    kramers_hasGrade_neg (include_hasGrade w v),
    Weight.parity_opposite w,
    kramers_sq (fibreInclude w v)⟩

end InfoGeometry.Quantum.FiveGradedKramersModule
end noncomputable section
