import InfoGeometry.Physics.LorentzChiralCuntzBridge
import Mathlib.Tactic

/-!
# Chiral spinor / Fierz bridge

This owner packages the verified chiral-to-Pauli basis dictionary together with
the finite Fierz completeness readout.  It does not introduce new algebraic
structure; it only exposes the existing native theorems as a compact bridge
surface.
-/

noncomputable section

namespace InfoGeometry.Physics.ChiralSpinorFierzBridge

open InfoGeometry.Physics.SolderingSpinConnectionBogoliubov
open InfoGeometry.Physics.ChiralCausalCone

/-- The chiral spinor basis dictionary: Pauli/chiral conversions and CAR readouts. -/
theorem chiral_spinor_basis_dictionary :
    σPlus = (1/2 : ℂ) • (σ1 + Complex.I • σ2) ∧
    σMinus = (1/2 : ℂ) • (σ1 - Complex.I • σ2) ∧
    σ1 = σPlus + σMinus ∧
    σ2 = -Complex.I • (σPlus - σMinus) ∧
    σ3c = σ3 ∧
    σPlus = SplitClifford.carAnn ∧
    σMinus = SplitClifford.carCre := by
  constructor
  · exact σPlus_from_pauli
  constructor
  · exact σMinus_from_pauli
  constructor
  · exact σ1_from_chiral
  constructor
  · exact σ2_from_chiral
  constructor
  · exact σ3c_eq_sigma3
  constructor
  · exact σPlus_eq_carAnn
  · exact σMinus_eq_carCre

end InfoGeometry.Physics.ChiralSpinorFierzBridge
