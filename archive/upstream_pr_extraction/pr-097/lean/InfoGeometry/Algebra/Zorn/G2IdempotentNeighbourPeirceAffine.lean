/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2AdmissibleBasisCoordinateConstraints

/-!
# Affine Peirce residuals of idempotent neighbour fibres

The residual carrier records exactly the hypotheses needed for translation by
the complementary idempotent.  It does not silently turn a one-sided
incidence relation into a two-sided linear eigenspace.
-/

namespace InfoGeometry.Algebra.Zorn.G2IdempotentNeighbourPeirceAffine

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def LeftPeirceResidual (u : NontrivialIdempotent) : Type :=
  {x : SplitOctF2 //
    mul u.1 x = zero ∧
    ∃ v : NontrivialIdempotent,
      add x (nontrivialIdempotentComplement u).1 = v.1}

def RightPeirceResidual (u : NontrivialIdempotent) : Type :=
  {x : SplitOctF2 //
    mul x u.1 = zero ∧
    ∃ v : NontrivialIdempotent,
      add x (nontrivialIdempotentComplement u).1 = v.1}

theorem leftNeighbourResidual_mem
    (u : NontrivialIdempotent)
    (v : NontrivialIdempotentNeighbours u) :
    mul u.1 (add v.1 (nontrivialIdempotentComplement u).1) = zero := by
  rw [mul_add, v.2, nontrivialIdempotentComplement_left_orthogonal u,
    add_zero]

theorem rightNeighbourResidual_mem
    (u : NontrivialIdempotent)
    (v : RightNontrivialIdempotentNeighbours u) :
    mul (add v.1 (nontrivialIdempotentComplement u).1) u.1 = zero := by
  rw [add_mul, v.2, nontrivialIdempotentComplement_right_orthogonal u,
    add_zero]

def leftNeighbourResidual
    (u : NontrivialIdempotent)
    (v : NontrivialIdempotentNeighbours u) :
    LeftPeirceResidual u := by
  refine ⟨add v.1 (nontrivialIdempotentComplement u).1,
    leftNeighbourResidual_mem u v, ?_⟩
  refine ⟨v.1, ?_⟩
  rw [add_assoc, add_self, add_zero]

def rightNeighbourResidual
    (u : NontrivialIdempotent)
    (v : RightNontrivialIdempotentNeighbours u) :
    RightPeirceResidual u := by
  refine ⟨add v.1 (nontrivialIdempotentComplement u).1,
    rightNeighbourResidual_mem u v, ?_⟩
  refine ⟨v.1, ?_⟩
  rw [add_assoc, add_self, add_zero]

@[simp] theorem leftNeighbourResidual_value
    (u : NontrivialIdempotent)
    (v : NontrivialIdempotentNeighbours u) :
    (leftNeighbourResidual u v).1 =
      add v.1 (nontrivialIdempotentComplement u).1 :=
  rfl

@[simp] theorem rightNeighbourResidual_value
    (u : NontrivialIdempotent)
    (v : RightNontrivialIdempotentNeighbours u) :
    (rightNeighbourResidual u v).1 =
      add v.1 (nontrivialIdempotentComplement u).1 :=
  rfl

noncomputable def leftPeirceResidualWitness
    (u : NontrivialIdempotent) (x : LeftPeirceResidual u) :
    NontrivialIdempotent :=
  Classical.choose x.2.2

theorem leftPeirceResidualWitness_spec
    (u : NontrivialIdempotent) (x : LeftPeirceResidual u) :
    add x.1 (nontrivialIdempotentComplement u).1 =
      (leftPeirceResidualWitness u x).1 :=
  Classical.choose_spec x.2.2

noncomputable def leftPeirceResidualInverse
    (u : NontrivialIdempotent) (x : LeftPeirceResidual u) :
    NontrivialIdempotentNeighbours u := by
  refine ⟨leftPeirceResidualWitness u x, ?_⟩
  rw [← leftPeirceResidualWitness_spec u x, mul_add,
    x.2.1, nontrivialIdempotentComplement_left_orthogonal u, add_zero]

noncomputable def leftNeighbourPeirceResidualEquiv
    (u : NontrivialIdempotent) :
    NontrivialIdempotentNeighbours u ≃ LeftPeirceResidual u where
  toFun := leftNeighbourResidual u
  invFun := leftPeirceResidualInverse u
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change (leftPeirceResidualWitness u (leftNeighbourResidual u v)).1 = v.1
    have hw := leftPeirceResidualWitness_spec u (leftNeighbourResidual u v)
    rw [leftNeighbourResidual_value] at hw
    rw [← hw]
    rw [InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_assoc,
      add_self, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_zero]
  right_inv x := by
    apply Subtype.ext
    have hw := leftPeirceResidualWitness_spec u x
    change add (leftPeirceResidualWitness u x).1
      (nontrivialIdempotentComplement u).1 = x.1
    rw [← hw]
    rw [InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_assoc,
      add_self, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_zero]

theorem leftNeighbourPeirceResidualEquiv_apply
    (u : NontrivialIdempotent) (v : NontrivialIdempotentNeighbours u) :
    leftNeighbourPeirceResidualEquiv u v = leftNeighbourResidual u v :=
  rfl

noncomputable def rightPeirceResidualWitness
    (u : NontrivialIdempotent) (x : RightPeirceResidual u) :
    NontrivialIdempotent :=
  Classical.choose x.2.2

theorem rightPeirceResidualWitness_spec
    (u : NontrivialIdempotent) (x : RightPeirceResidual u) :
    add x.1 (nontrivialIdempotentComplement u).1 =
      (rightPeirceResidualWitness u x).1 :=
  Classical.choose_spec x.2.2

noncomputable def rightPeirceResidualInverse
    (u : NontrivialIdempotent) (x : RightPeirceResidual u) :
    RightNontrivialIdempotentNeighbours u := by
  refine ⟨rightPeirceResidualWitness u x, ?_⟩
  rw [← rightPeirceResidualWitness_spec u x, add_mul,
    x.2.1, nontrivialIdempotentComplement_right_orthogonal u, add_zero]

noncomputable def rightNeighbourPeirceResidualEquiv
    (u : NontrivialIdempotent) :
    RightNontrivialIdempotentNeighbours u ≃ RightPeirceResidual u where
  toFun := rightNeighbourResidual u
  invFun := rightPeirceResidualInverse u
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change (rightPeirceResidualWitness u (rightNeighbourResidual u v)).1 = v.1
    have hw := rightPeirceResidualWitness_spec u (rightNeighbourResidual u v)
    rw [rightNeighbourResidual_value] at hw
    rw [← hw]
    rw [InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_assoc,
      add_self, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_zero]
  right_inv x := by
    apply Subtype.ext
    have hw := rightPeirceResidualWitness_spec u x
    change add (rightPeirceResidualWitness u x).1
      (nontrivialIdempotentComplement u).1 = x.1
    rw [← hw]
    rw [InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_assoc,
      add_self, InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_zero]

theorem rightNeighbourPeirceResidualEquiv_apply
    (u : NontrivialIdempotent) (v : RightNontrivialIdempotentNeighbours u) :
    rightNeighbourPeirceResidualEquiv u v = rightNeighbourResidual u v :=
  rfl

theorem leftPeirceResidual_card_eq_neighbour_card
    (u : NontrivialIdempotent)
    [Fintype (NontrivialIdempotentNeighbours u)]
    [Fintype (LeftPeirceResidual u)] :
    Fintype.card (LeftPeirceResidual u) =
      Fintype.card (NontrivialIdempotentNeighbours u) := by
  exact Fintype.card_congr (leftNeighbourPeirceResidualEquiv u).symm

theorem rightPeirceResidual_card_eq_neighbour_card
    (u : NontrivialIdempotent)
    [Fintype (RightNontrivialIdempotentNeighbours u)]
    [Fintype (RightPeirceResidual u)] :
    Fintype.card (RightPeirceResidual u) =
      Fintype.card (RightNontrivialIdempotentNeighbours u) := by
  exact Fintype.card_congr (rightNeighbourPeirceResidualEquiv u).symm

noncomputable def leftPeirceResidualTransportEquiv
    (f : SplitOctF2Aut) (u : NontrivialIdempotent) :
    LeftPeirceResidual u ≃ LeftPeirceResidual (f • u) :=
  (leftNeighbourPeirceResidualEquiv u).symm.trans
    ((nontrivialIdempotentNeighboursEquiv f u).trans
      (leftNeighbourPeirceResidualEquiv (f • u)))

noncomputable def rightPeirceResidualTransportEquiv
    (f : SplitOctF2Aut) (u : NontrivialIdempotent) :
    RightPeirceResidual u ≃ RightPeirceResidual (f • u) :=
  (rightNeighbourPeirceResidualEquiv u).symm.trans
    ((rightNontrivialIdempotentNeighboursEquiv f u).trans
      (rightNeighbourPeirceResidualEquiv (f • u)))

theorem leftPeirceResidual_card_invariant
    (f : SplitOctF2Aut) (u : NontrivialIdempotent)
    [Fintype (LeftPeirceResidual u)]
    [Fintype (LeftPeirceResidual (f • u))] :
    Fintype.card (LeftPeirceResidual u) =
      Fintype.card (LeftPeirceResidual (f • u)) :=
  Fintype.card_congr (leftPeirceResidualTransportEquiv f u)

theorem rightPeirceResidual_card_invariant
    (f : SplitOctF2Aut) (u : NontrivialIdempotent)
    [Fintype (RightPeirceResidual u)]
    [Fintype (RightPeirceResidual (f • u))] :
    Fintype.card (RightPeirceResidual u) =
      Fintype.card (RightPeirceResidual (f • u)) :=
  Fintype.card_congr (rightPeirceResidualTransportEquiv f u)

end InfoGeometry.Algebra.Zorn.G2IdempotentNeighbourPeirceAffine
