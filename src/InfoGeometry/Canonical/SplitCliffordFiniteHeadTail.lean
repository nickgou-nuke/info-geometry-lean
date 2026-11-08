/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.Prod
import InfoGeometry.Clifford.Tower
import InfoGeometry.Canonical.SplitCliffordTensorBridge

open scoped TensorProduct

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordFiniteHeadTail

open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- Regroup the recursively ordered split space into a fixed finite head and
a remaining finite tail. -/
def splitSpaceAppendEquiv (k : ℕ) : (n : ℕ) →
    SplitSpace (k + n) ≃ₗ[ℝ] SplitSpace k × SplitSpace n
  | 0 =>
      (LinearEquiv.prodUnique (R := ℝ) (M := SplitSpace k)
        (M₂ := SplitSpace 0)).symm
  | n + 1 =>
      (LinearEquiv.prodCongr (LinearEquiv.refl ℝ (ℝ × ℝ))
        (splitSpaceAppendEquiv k n)).trans
        ((LinearEquiv.prodAssoc ℝ (ℝ × ℝ) (SplitSpace k)
          (SplitSpace n)).symm.trans
          ((LinearEquiv.prodCongr
            (LinearEquiv.prodComm ℝ (ℝ × ℝ) (SplitSpace k))
            (LinearEquiv.refl ℝ (SplitSpace n))).trans
            (LinearEquiv.prodAssoc ℝ (SplitSpace k) (ℝ × ℝ)
              (SplitSpace n))))

/-- Appending one recursive split coordinate acts only on the tail under the
head--tail regrouping. This is the quadratic-space compatibility underlying a
fixed-head comparison of the Clifford tower transitions. -/
theorem splitSpaceAppendEquiv_inr (k n : ℕ) (x : SplitSpace (k + n)) :
    splitSpaceAppendEquiv k (n + 1) (0, x) =
      ((splitSpaceAppendEquiv k n x).1,
        (0, (splitSpaceAppendEquiv k n x).2)) := by
  simp [splitSpaceAppendEquiv, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.prodComm_apply,
    LinearEquiv.prodAssoc, Equiv.prodAssoc]

/-- The recursive quadratic form on `SplitSpace (k+n)` is the orthogonal sum
of the forms on the selected head and tail coordinates. -/
theorem splitSpaceAppend_quadratic (k n : ℕ) (x : SplitSpace (k + n)) :
    Qsplit (k + n) x =
      (Qsplit k).prod (Qsplit n) (splitSpaceAppendEquiv k n x) := by
  induction n with
  | zero =>
      simp [splitSpaceAppendEquiv, Qsplit]
  | succ n ih =>
      rcases x with ⟨v, xs⟩
      let p := splitSpaceAppendEquiv k n xs
      have hmap : splitSpaceAppendEquiv k (n + 1) (v, xs) = (p.1, (v, p.2)) := by
        simp [splitSpaceAppendEquiv, p, LinearEquiv.trans_apply,
          LinearEquiv.prodCongr_apply,
          LinearEquiv.prodComm_apply, LinearEquiv.prodAssoc,
          Equiv.prodAssoc]
      have hleft : Qsplit (k + (n + 1)) (v, xs) =
          InfoGeometry.CliffordTower.Q11 v + Qsplit (k + n) xs := by
        convert Qsplit_succ_apply (k + n) v xs using 1
      calc
        Qsplit (k + (n + 1)) (v, xs) =
            InfoGeometry.CliffordTower.Q11 v + Qsplit (k + n) xs := hleft
        _ = InfoGeometry.CliffordTower.Q11 v +
            (Qsplit k p.1 + Qsplit n p.2) := by
              rw [ih xs]
              simp [p, QuadraticMap.prod_apply]
        _ = Qsplit k p.1 +
            (InfoGeometry.CliffordTower.Q11 v + Qsplit n p.2) := by abel
        _ = (Qsplit k).prod (Qsplit (n + 1))
            (splitSpaceAppendEquiv k (n + 1) (v, xs)) := by
              rw [hmap]
              simp only [QuadraticMap.prod_apply]
              rw [Qsplit_succ_apply]

def splitSpaceAppendIsometry (k n : ℕ) :
    (Qsplit (k + n)).IsometryEquiv ((Qsplit k).prod (Qsplit n)) :=
  ⟨splitSpaceAppendEquiv k n, fun x => (splitSpaceAppend_quadratic k n x).symm⟩

/-- Finite split Clifford head--tail factorization. It is an algebra
equivalence to Mathlib's graded tensor product, with the first `k` split
coordinates as head and the remaining `n` coordinates as tail. -/
def splitCliffordFiniteHeadTailEquiv (k n : ℕ) :
    SplitClNNAlg (k + n) ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit k) ᵍ⊗[ℝ]
        CliffordAlgebra.evenOdd (Qsplit n)) :=
  (CliffordAlgebra.equivOfIsometry (splitSpaceAppendIsometry k n)).trans
    (CliffordAlgebra.prodEquiv (Qsplit k) (Qsplit n))

/-- The finite head--tail equivalence sends each Clifford generator to the
sum of its head and tail generators in the graded tensor product. -/
@[simp]
theorem splitCliffordFiniteHeadTailEquiv_ι (k n : ℕ)
    (x : SplitSpace (k + n)) :
    splitCliffordFiniteHeadTailEquiv k n
        (CliffordAlgebra.ι (Qsplit (k + n)) x) =
      (CliffordAlgebra.ι (Qsplit k) (splitSpaceAppendEquiv k n x).1)
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) +
        (1 : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ
          CliffordAlgebra.ι (Qsplit n) (splitSpaceAppendEquiv k n x).2 := by
  have hpair : splitSpaceAppendEquiv k n x =
      ((splitSpaceAppendEquiv k n x).1, (splitSpaceAppendEquiv k n x).2) := by
    cases splitSpaceAppendEquiv k n x
    rfl
  simp [splitCliffordFiniteHeadTailEquiv, splitSpaceAppendIsometry]
  rw [hpair, CliffordAlgebra.ofProd_ι_mk]
  rfl

/-- Under the finite head--tail factorization, the tower's recursive
one-coordinate inclusion changes only the tail coordinate. -/
theorem splitCliffordFiniteHeadTailEquiv_inr (k n : ℕ)
    (x : SplitSpace (k + n)) :
    splitCliffordFiniteHeadTailEquiv k (n + 1)
        (CliffordAlgebra.ι (Qsplit (k + (n + 1))) (0, x)) =
      (CliffordAlgebra.ι (Qsplit k) (splitSpaceAppendEquiv k n x).1)
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit (n + 1))) +
        (1 : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ
          CliffordAlgebra.ι (Qsplit (n + 1))
            (0, (splitSpaceAppendEquiv k n x).2) := by
  rw [splitCliffordFiniteHeadTailEquiv_ι, splitSpaceAppendEquiv_inr]

end InfoGeometry.Canonical.SplitCliffordFiniteHeadTail

end
