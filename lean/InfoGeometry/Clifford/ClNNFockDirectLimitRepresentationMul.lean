/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationScalarLeftWave19

/-!
# Lie action law on the symmetric split Clifford Fock colimit

BUCKET 1 — The multiplication law for the descended Chevalley action is owned
by `ClNNFockDirectLimitRepresentation`.
BUCKET 2 — Subtraction preservation follows from the already proved additive
and real-linear action laws.
BUCKET 3 — The commutator identity is proved for arbitrary elements of the
algebraic `Cl(n,n)` direct limit acting on the algebraic Fock direct limit.
No finite-dimensional bound or analytic completion is imposed on either
colimit carrier.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.ClNN

/-! The product law is owned by
`ClNNFockDirectLimitRepresentation.splitCliffordFockAction_mul`. This module
adds its Lie-bracket consequence on arbitrary elements of the algebraic
direct limit. -/

/-- The descended action carries subtraction in the Clifford algebra
colimit to subtraction of the induced spinor operators. -/
theorem splitCliffordFockAction_sub_left
    (aInf bInf : SplitCliffordInfinity) (ψInf : FockInfinity) :
    splitCliffordFockAction (aInf - bInf) ψInf =
      splitCliffordFockAction aInf ψInf - splitCliffordFockAction bInf ψInf := by
  rw [sub_eq_add_neg, splitCliffordFockAction_add_left]
  have hneg : splitCliffordFockAction (-bInf) ψInf =
      -splitCliffordFockAction bInf ψInf := by
    calc
      splitCliffordFockAction (-bInf) ψInf =
          splitCliffordFockAction ((-1 : ℝ) • bInf) ψInf := by
            congr 1
      _ = (-1 : ℝ) • splitCliffordFockAction bInf ψInf :=
        splitCliffordFockAction_smul_left (-1) bInf ψInf
      _ = -splitCliffordFockAction bInf ψInf := by simp
  rw [hneg]
  exact (sub_eq_add_neg _ _).symm

/-- The Chevalley action of a commutator in the Clifford algebra colimit is
the commutator of the two induced operators on the algebraic Fock colimit.
This is the Lie-representation law for the unbounded `Cl(n,n)` tower. -/
theorem splitCliffordFockAction_commutator
    (aInf bInf : SplitCliffordInfinity) (ψInf : FockInfinity) :
    splitCliffordFockAction (aInf * bInf - bInf * aInf) ψInf =
      splitCliffordFockAction aInf (splitCliffordFockAction bInf ψInf) -
        splitCliffordFockAction bInf (splitCliffordFockAction aInf ψInf) := by
  rw [splitCliffordFockAction_sub_left,
    splitCliffordFockAction_mul, splitCliffordFockAction_mul]

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
