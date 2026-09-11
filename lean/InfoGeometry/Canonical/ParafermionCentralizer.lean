import InfoGeometry.Canonical.HorizonZeroModeFierz
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.CliffordTower

noncomputable section

namespace InfoGeometry.Canonical.ParafermionCentralizer

open InfoGeometry.Canonical.DrazinModularPersistence
open InfoGeometry.Canonical.DrazinCentralizerErlangen
open InfoGeometry.Canonical.HorizonZeroModeFierz
open InfoGeometry.Clifford.CliffordTower
open InfoGeometry.OperatorAlgebra.Thermodynamics

/--
A Drazin-compressed centralizer element is fixed by the modular flow.
This is the explicit commutation/fixed-point content carried by
`InDrazinCompressedCentralizer`.
-/
@[rep_depth operator]
theorem compressed_centralizer_commutes_with_modular_flow
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (x : Obs)
    (hx : InDrazinCompressedCentralizer flow D x) :
    ∀ t : ℝ, flow.flow t x = x :=
  hx.2

/--
A horizon zero mode in the canonical sanctuary is fixed by the modular flow.
-/
@[rep_depth operator]
theorem horizon_zero_mode_commutes_with_modular_flow
    {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]
    (S : DrazinCentralizerSanctuary Obs)
    (x : Obs)
    (hx : IsHorizonZeroMode S x) :
    ∀ t : ℝ, S.flow.flow t x = x := by
  exact compressed_centralizer_commutes_with_modular_flow S.flow S.horizon x hx

/--
The distinguished parafermion centralizer dimension readout used by the
Clifford-tower hierarchy.
-/
@[simp] theorem parafermion_centralizer_dimension :
    parafermion_centralizer_dim = 137 := by
  rfl

/--
The same readout expressed as the Bastin-Kilmister-Noyes hierarchy sum.
-/
theorem parafermion_centralizer_dimension_equals_hierarchy :
    parafermion_centralizer_dim =
      InfoGeometry.Clifford.CliffordTower.mersenne 2 +
      InfoGeometry.Clifford.CliffordTower.mersenne 3 +
      InfoGeometry.Clifford.CliffordTower.mersenne 7 := by
  exact parafermion_centralizer_equals_hierarchy

/--
Real-valued inverse fine-structure readout induced by the combinatorial
parafermion centralizer dimension.
-/
theorem parafermion_alpha_inverse_readout :
    alpha_inv_combinatorial = (137 : ℝ) := by
  exact alpha_inv_is_137

/--
Real-valued fine-structure readout induced by the same combinatorial dimension.
-/
theorem parafermion_alpha_readout :
    alpha_combinatorial = 1 / (137 : ℝ) := by
  exact alpha_combinatorial_value

end InfoGeometry.Canonical.ParafermionCentralizer
