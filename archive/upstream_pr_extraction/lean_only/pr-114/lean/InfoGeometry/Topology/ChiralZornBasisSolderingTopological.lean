import Mathlib
import InfoGeometry.Algebra.ChiralZornBasisSoldering

/-!
# Topological chiral/soldered coordinate change

The algebraic Zorn owner supplies the eight symbolic coordinate slots.  This
file equips the coefficient carrier `Fin 8 → ℂ` with the product topology and
proves that the change from the chiral order

`(u+, σ+₁, σ+₂, σ+₃, u-, σ-₁, σ-₂, σ-₃)`

to the soldered order

`(1, ℓ, σ+₁, σ-₁, σ+₂, σ-₂, σ+₃, σ-₃)`

is a genuine homeomorphism.  This is a coordinate theorem, not a claim that
the non-associative Zorn carrier is itself a topological algebra.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra

noncomputable section

abbrev ChiralCoefficientSpace := Fin 8 → ℂ

def chiralToSoldered : ChiralCoefficientSpace ≃ₜ ChiralCoefficientSpace where
  toFun c := ![
    c 0 + c 4,
    c 0 - c 4,
    c 1,
    c 5,
    c 2,
    c 6,
    c 3,
    c 7]
  invFun d := ![
    (d 0 + d 1) / 2,
    d 2,
    d 4,
    d 6,
    (d 0 - d 1) / 2,
    d 3,
    d 5,
    d 7]
  left_inv := by
    intro c
    funext i
    fin_cases i <;> simp <;> ring
  right_inv := by
    intro d
    funext i
    fin_cases i <;> simp <;> ring
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun c : ChiralCoefficientSpace => c 0 + c 4)
      fun_prop
    · change Continuous (fun c : ChiralCoefficientSpace => c 0 - c 4)
      fun_prop
    · change Continuous (fun c : ChiralCoefficientSpace => c 1)
      fun_prop
    · change Continuous (fun c : ChiralCoefficientSpace => c 5)
      fun_prop
    · change Continuous (fun c : ChiralCoefficientSpace => c 2)
      fun_prop
    · change Continuous (fun c : ChiralCoefficientSpace => c 6)
      fun_prop
    · change Continuous (fun c : ChiralCoefficientSpace => c 3)
      fun_prop
    · change Continuous (fun c : ChiralCoefficientSpace => c 7)
      fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun d : ChiralCoefficientSpace => (d 0 + d 1) / 2)
      fun_prop
    · change Continuous (fun d : ChiralCoefficientSpace => d 2)
      fun_prop
    · change Continuous (fun d : ChiralCoefficientSpace => d 4)
      fun_prop
    · change Continuous (fun d : ChiralCoefficientSpace => d 6)
      fun_prop
    · change Continuous (fun d : ChiralCoefficientSpace => (d 0 - d 1) / 2)
      fun_prop
    · change Continuous (fun d : ChiralCoefficientSpace => d 3)
      fun_prop
    · change Continuous (fun d : ChiralCoefficientSpace => d 5)
      fun_prop
    · change Continuous (fun d : ChiralCoefficientSpace => d 7)
      fun_prop

@[simp] theorem chiralToSoldered_apply_zero (c : ChiralCoefficientSpace) :
    chiralToSoldered c 0 = c 0 + c 4 := rfl

@[simp] theorem chiralToSoldered_apply_one (c : ChiralCoefficientSpace) :
    chiralToSoldered c 1 = c 0 - c 4 := rfl

@[simp] theorem chiralToSoldered_apply_two (c : ChiralCoefficientSpace) :
    chiralToSoldered c 2 = c 1 := rfl

@[simp] theorem chiralToSoldered_apply_three (c : ChiralCoefficientSpace) :
    chiralToSoldered c 3 = c 5 := rfl

@[simp] theorem chiralToSoldered_apply_four (c : ChiralCoefficientSpace) :
    chiralToSoldered c 4 = c 2 := rfl

@[simp] theorem chiralToSoldered_apply_five (c : ChiralCoefficientSpace) :
    chiralToSoldered c 5 = c 6 := rfl

@[simp] theorem chiralToSoldered_apply_six (c : ChiralCoefficientSpace) :
    chiralToSoldered c 6 = c 3 := rfl

@[simp] theorem chiralToSoldered_apply_seven (c : ChiralCoefficientSpace) :
    chiralToSoldered c 7 = c 7 := rfl

theorem chiralToSoldered_diagonal_inverse (c : ChiralCoefficientSpace) :
    (chiralToSoldered c 0 + chiralToSoldered c 1) / 2 = c 0 ∧
      (chiralToSoldered c 0 - chiralToSoldered c 1) / 2 = c 4 := by
  constructor <;> simp <;> ring

theorem continuous_chiralToSoldered :
    Continuous (chiralToSoldered : ChiralCoefficientSpace → ChiralCoefficientSpace) :=
  chiralToSoldered.continuous_toFun

theorem continuous_solderedToChiral :
    Continuous (chiralToSoldered.symm : ChiralCoefficientSpace → ChiralCoefficientSpace) :=
  chiralToSoldered.symm.continuous_toFun

end
end InfoGeometry.Topology
