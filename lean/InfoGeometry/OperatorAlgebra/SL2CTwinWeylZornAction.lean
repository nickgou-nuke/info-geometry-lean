import InfoGeometry.OperatorAlgebra.TwinLightconeWeylOperatorZorn
import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.Canonical.HestenesSpinAction

/-! Concrete two-sided spin action on the existing associative twin block. -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SL2CTwinWeylZornAction

open InfoGeometry.Canonical.HestenesSpinAction
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev TwinWeylBlock := ZornBlock Mat2C
abbrev ChiralLorentzPair := SL2C × SL2C

def act (g : ChiralLorentzPair) (Z : TwinWeylBlock) : TwinWeylBlock :=
  ⟨spinAction g.1 Z.n_plus_op,
    spinAction g.2 Z.n_minus_op,
    (g.1 : Mat2C) * Z.sigma_plus_op * star (g.2 : Mat2C),
    (g.2 : Mat2C) * Z.sigma_minus_op * star (g.1 : Mat2C)⟩

@[simp] theorem act_n_plus (g : ChiralLorentzPair) (Z : TwinWeylBlock) :
    (act g Z).n_plus_op = spinAction g.1 Z.n_plus_op := rfl

@[simp] theorem act_n_minus (g : ChiralLorentzPair) (Z : TwinWeylBlock) :
    (act g Z).n_minus_op = spinAction g.2 Z.n_minus_op := rfl

@[simp] theorem act_sigma_plus (g : ChiralLorentzPair) (Z : TwinWeylBlock) :
    (act g Z).sigma_plus_op =
      (g.1 : Mat2C) * Z.sigma_plus_op * star (g.2 : Mat2C) := rfl

@[simp] theorem act_sigma_minus (g : ChiralLorentzPair) (Z : TwinWeylBlock) :
    (act g Z).sigma_minus_op =
      (g.2 : Mat2C) * Z.sigma_minus_op * star (g.1 : Mat2C) := rfl

theorem act_one (Z : TwinWeylBlock) : act (1, 1) Z = Z := by
  apply zornBlock_ext <;> simp [act, spinAction]

theorem act_mul (g h : ChiralLorentzPair) (Z : TwinWeylBlock) :
    act (g.1 * h.1, g.2 * h.2) Z = act g (act h Z) := by
  apply zornBlock_ext <;>
    simp [act, spinAction, Matrix.star_mul, mul_assoc]

theorem sheetExchange_act (g : ChiralLorentzPair) (Z : TwinWeylBlock) :
    sheetExchange * act g Z * sheetExchange =
      act (g.2, g.1) (sheetExchange * Z * sheetExchange) := by
  rw [sheetExchange_conjugates, sheetExchange_conjugates]
  rfl

theorem act_preserves_diagonal_determinants (g : ChiralLorentzPair) (Z : TwinWeylBlock) :
    Matrix.det (act g Z).n_plus_op = Matrix.det Z.n_plus_op ∧
      Matrix.det (act g Z).n_minus_op = Matrix.det Z.n_minus_op := by
  exact ⟨spinAction_preserves_det g.1 Z.n_plus_op,
    spinAction_preserves_det g.2 Z.n_minus_op⟩

theorem sl2c_twin_weyl_packet (g h : ChiralLorentzPair) (Z : TwinWeylBlock) :
    act (1, 1) Z = Z ∧
      act (g.1 * h.1, g.2 * h.2) Z = act g (act h Z) ∧
      Matrix.det (act g Z).n_plus_op = Matrix.det Z.n_plus_op ∧
      Matrix.det (act g Z).n_minus_op = Matrix.det Z.n_minus_op := by
  exact ⟨act_one Z, act_mul g h Z,
    (act_preserves_diagonal_determinants g Z).1,
    (act_preserves_diagonal_determinants g Z).2⟩

end InfoGeometry.OperatorAlgebra.SL2CTwinWeylZornAction
