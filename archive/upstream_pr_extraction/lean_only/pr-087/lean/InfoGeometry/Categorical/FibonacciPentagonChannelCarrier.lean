import InfoGeometry.Categorical.FibonacciPentagonPathCarrier

/-!
# Channel-function carriers for the Fibonacci pentagon

The pentagon path owner supplies a cardinality transport from the formal
channel count to `Basis6`.  This file packages that transport as a genuine
linear equivalence of function spaces.  It is deliberately a carrier-level
statement: the equivalence is not promoted to a fusion-tree basis
identification.
-/

namespace InfoGeometry.Categorical.FibonacciPentagonChannelCarrier

open InfoGeometry.Categorical.FibonacciPentagonPathCarrier
open InfoGeometry.Categorical.FibonacciFusionCategoryData

abbrev ChannelIndex (v : PentagonVertex) : Type :=
  Fin (parenthesizedObject v FibSimple.unit +
    parenthesizedObject v FibSimple.tau)

abbrev ChannelFunctions (v : PentagonVertex) : Type :=
  ChannelIndex v → ℂ

abbrev FormalChannelIndex (v : PentagonVertex) : Type :=
  Sum (Fin (parenthesizedObject v FibSimple.unit))
    (Fin (parenthesizedObject v FibSimple.tau))

/-! This is the explicit unit/tau block indexing of the formal multiplicity
object.  It is a basis-index equivalence, not a claim about a preferred
physical fusion-tree ordering. -/

noncomputable def formalChannelBasisEquiv (v : PentagonVertex) :
    FormalChannelIndex v ≃
      InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices.Basis6 :=
  finSumFinEquiv.trans (parenthesizedChannelEquiv v)

theorem formalChannelIndex_card (v : PentagonVertex) :
    Fintype.card (FormalChannelIndex v) = 5 := by
  rw [Fintype.card_sum]
  simpa using congrArg id (parenthesizedObject_total_channel_count v)

theorem formalChannelIndex_unit_card (v : PentagonVertex) :
    Fintype.card (Fin (parenthesizedObject v FibSimple.unit)) = 2 := by
  simpa using (parenthesizedObject_counts v).1

theorem formalChannelIndex_tau_card (v : PentagonVertex) :
    Fintype.card (Fin (parenthesizedObject v FibSimple.tau)) = 3 := by
  simpa using (parenthesizedObject_counts v).2

abbrev FormalChannelFunctions (v : PentagonVertex) : Type :=
  FormalChannelIndex v → ℂ

noncomputable def formalChannelCarrierEquiv (v : PentagonVertex) :
    FormalChannelFunctions v ≃ₗ[ℂ] PathCarrier :=
  { toFun := fun x i => x ((formalChannelBasisEquiv v).symm i)
    invFun := fun y j => y (formalChannelBasisEquiv v j)
    map_add' := by
      intro x y
      funext i
      rfl
    map_smul' := by
      intro c x
      funext i
      rfl
    left_inv := by
      intro x
      funext j
      change x ((formalChannelBasisEquiv v).symm
        (formalChannelBasisEquiv v j)) = x j
      rw [Equiv.symm_apply_apply]
    right_inv := by
      intro y
      funext i
      change y (formalChannelBasisEquiv v
        ((formalChannelBasisEquiv v).symm i)) = y i
      rw [Equiv.apply_symm_apply] }

@[simp]
theorem formalChannelCarrierEquiv_apply
    (v : PentagonVertex) (x : FormalChannelFunctions v)
    (i : InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices.Basis6) :
    formalChannelCarrierEquiv v x i =
      x ((formalChannelBasisEquiv v).symm i) :=
  rfl

@[simp]
theorem formalChannelCarrierEquiv_symm_apply
    (v : PentagonVertex) (y : PathCarrier)
    (j : FormalChannelIndex v) :
    (formalChannelCarrierEquiv v).symm y j =
      y (formalChannelBasisEquiv v j) :=
  rfl

noncomputable def parenthesizedChannelCarrierEquiv (v : PentagonVertex) :
    ChannelFunctions v ≃ₗ[ℂ] PathCarrier :=
  { toFun := fun x i => x ((parenthesizedChannelEquiv v).symm i)
    invFun := fun y j => y (parenthesizedChannelEquiv v j)
    map_add' := by
      intro x y
      funext i
      rfl
    map_smul' := by
      intro c x
      funext i
      rfl
    left_inv := by
      intro x
      funext j
      simp
    right_inv := by
      intro y
      funext i
      simp }

@[simp]
theorem parenthesizedChannelCarrierEquiv_apply
    (v : PentagonVertex) (x : ChannelFunctions v)
    (i : InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices.Basis6) :
    parenthesizedChannelCarrierEquiv v x i =
      x ((parenthesizedChannelEquiv v).symm i) :=
  rfl

@[simp]
theorem parenthesizedChannelCarrierEquiv_symm_apply
    (v : PentagonVertex) (y : PathCarrier) (j : ChannelIndex v) :
    (parenthesizedChannelCarrierEquiv v).symm y j =
      y (parenthesizedChannelEquiv v j) :=
  rfl

end InfoGeometry.Categorical.FibonacciPentagonChannelCarrier
