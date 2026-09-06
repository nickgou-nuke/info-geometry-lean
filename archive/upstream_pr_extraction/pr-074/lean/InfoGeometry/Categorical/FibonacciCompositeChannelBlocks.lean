import InfoGeometry.Categorical.FibonacciPentagonPathCarrier
import InfoGeometry.Categorical.FibonacciFusionTreeAssociator

/-!
# Explicit composite-channel indexing for Fibonacci fusion trees

The object `τ ⊗ τ` is the formal sum `𝟙 ⊕ τ`.  This owner exposes the
canonical finite-index decompositions needed to write the remaining
four-anyon associators as block matrices.  It does not choose an
associator matrix; it fixes only the domain/codomain block order.
-/

namespace InfoGeometry.Categorical.FibonacciCompositeChannelBlocks

open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciFusionTreeAssociator

noncomputable def compositeTau : FibCat :=
  fibTensorObj tauObject tauObject

theorem compositeTau_unit : compositeTau FibSimple.unit = 1 := by
  simp [compositeTau, tauObject, fibTensorObj, Finsupp.single_apply]

theorem compositeTau_tau : compositeTau FibSimple.tau = 1 := by
  simp [compositeTau, tauObject, fibTensorObj, Finsupp.single_apply]

theorem outerComposite_unit_count :
    fibTensorObj compositeTau compositeTau FibSimple.unit = 2 := by
  rw [fibTensorObj_apply_unit, compositeTau_unit, compositeTau_tau]

theorem outerComposite_tau_count :
    fibTensorObj compositeTau compositeTau FibSimple.tau = 3 := by
  rw [fibTensorObj_apply_tau, compositeTau_unit, compositeTau_tau]

theorem outerComposite_unit_block_shape :
    fibTensorObj compositeTau compositeTau FibSimple.unit =
      compositeTau FibSimple.unit + compositeTau FibSimple.unit := by
  rw [outerComposite_unit_count, compositeTau_unit]

theorem outerComposite_tau_block_shape :
    fibTensorObj compositeTau compositeTau FibSimple.tau =
      compositeTau FibSimple.unit + compositeTau FibSimple.tau +
        compositeTau FibSimple.tau := by
  rw [outerComposite_tau_count, compositeTau_unit, compositeTau_tau]

noncomputable def outerCompositeUnitBlockEquiv :
    Fin (fibTensorObj compositeTau compositeTau FibSimple.unit) ≃
      Sum (Fin (compositeTau FibSimple.unit))
        (Fin (compositeTau FibSimple.unit)) :=
  (Equiv.cast (by
    rw [outerComposite_unit_block_shape])).trans finSumFinEquiv.symm

noncomputable def outerCompositeTauBlockEquiv :
    Fin (fibTensorObj compositeTau compositeTau FibSimple.tau) ≃
      Sum (Fin (compositeTau FibSimple.unit + compositeTau FibSimple.tau))
        (Fin (compositeTau FibSimple.tau)) :=
  (Equiv.cast (by
    rw [outerComposite_tau_block_shape])).trans finSumFinEquiv.symm

theorem outerCompositeUnitBlockEquiv_source_card :
    Fintype.card (Fin (fibTensorObj compositeTau compositeTau FibSimple.unit)) =
      Fintype.card (Sum (Fin (compositeTau FibSimple.unit))
        (Fin (compositeTau FibSimple.unit))) := by
  rw [outerComposite_unit_count, compositeTau_unit]
  simp

theorem outerCompositeTauBlockEquiv_source_card :
    Fintype.card (Fin (fibTensorObj compositeTau compositeTau FibSimple.tau)) =
      Fintype.card (Sum (Fin (compositeTau FibSimple.unit + compositeTau FibSimple.tau))
        (Fin (compositeTau FibSimple.tau))) := by
  rw [outerComposite_tau_count, compositeTau_unit, compositeTau_tau]
  simp

end InfoGeometry.Categorical.FibonacciCompositeChannelBlocks
