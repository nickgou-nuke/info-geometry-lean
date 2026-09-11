import InfoGeometry.OperatorAlgebra.SplitOctonionG2TypeGenerators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.KleinFourTag

namespace InfoGeometry.Canonical.SplitOctonionKleinFourAutomorphism

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.CyclicAutomorphism
open InfoGeometry.OperatorAlgebra.SplitOctonions.G2TypeGenerators

abbrev V4 := InfoGeometry.Geometry.KleinFourTag.Tag
abbrev SplitOct := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct

local instance : Mul SplitOct := ⟨mulZ⟩

/-- The second diagonal sign flip, obtained by conjugating `tau` by `rho`. -/
def tau₂ (X : SplitOct) : SplitOct := rho (tau (rho (rho X)))

theorem tau₂_order_two (X : SplitOct) : tau₂ (tau₂ X) = X := by
  cases X
  simp [tau₂, rho, tau]

theorem tau₂_mulZ (X Y : SplitOct) :
    tau₂ (mulZ X Y) = mulZ (tau₂ X) (tau₂ Y) := by
  unfold tau₂
  simp only [rho_mulZ, tau_mulZ]

theorem tau_tau₂_comm (X : SplitOct) : tau (tau₂ X) = tau₂ (tau X) := by
  cases X
  simp [tau₂, rho, tau]

def tau12 (X : SplitOct) : SplitOct := tau (tau₂ X)

theorem tau12_order_two (X : SplitOct) : tau12 (tau12 X) = X := by
  simp [tau12, tau_tau₂_comm, tau_order_two, tau₂_order_two]

theorem tau12_mulZ (X Y : SplitOct) :
    tau12 (mulZ X Y) = mulZ (tau12 X) (tau12 Y) := by
  simp [tau12, tau_mulZ, tau₂_mulZ]

def involutiveMulEquiv (f : SplitOct → SplitOct)
    (hf : ∀ X, f (f X) = X)
    (hprod : ∀ X Y, f (mulZ X Y) = mulZ (f X) (f Y)) :
    SplitOct ≃* SplitOct where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf
  map_mul' := hprod

def tauAut : SplitOct ≃* SplitOct :=
  involutiveMulEquiv tau tau_order_two tau_mulZ

def tau₂Aut : SplitOct ≃* SplitOct :=
  involutiveMulEquiv tau₂ tau₂_order_two tau₂_mulZ

def tau12Aut : SplitOct ≃* SplitOct :=
  involutiveMulEquiv tau12 tau12_order_two tau12_mulZ

@[simp] theorem tauAut_apply (X : SplitOct) : tauAut X = tau X := rfl
@[simp] theorem tau₂Aut_apply (X : SplitOct) : tau₂Aut X = tau₂ X := rfl
@[simp] theorem tau12Aut_apply (X : SplitOct) : tau12Aut X = tau12 X := rfl

def axisAction : V4 → SplitOct ≃* SplitOct
  | (0, 0) => 1
  | (1, 0) => tauAut
  | (0, 1) => tau₂Aut
  | (1, 1) => tau12Aut

theorem axisAction_apply (g : V4) (X : SplitOct) :
    axisAction g X =
      match g with
      | (0, 0) => X
      | (1, 0) => tau X
      | (0, 1) => tau₂ X
      | (1, 1) => tau12 X := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> rfl

theorem axisAction_mul_apply (g h : V4) (X : SplitOct) :
    axisAction (g + h) X = axisAction g (axisAction h X) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases g with ⟨a, b⟩
  rcases h with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [h11, axisAction, tau12, tau_tau₂_comm, tau_order_two,
      tau₂_order_two, tau12_order_two]

end InfoGeometry.Canonical.SplitOctonionKleinFourAutomorphism
