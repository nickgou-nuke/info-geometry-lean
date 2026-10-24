/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Order.Fin.Basic

/-!
# Ordered exterior basis transport on the native real Fock carrier

Batch-1 candidate; repaired explicit successor-embedding transport. The new head is unoccupied: each old occupied
index is shifted by Fin.succ. No inner product or scalar extension is installed.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

/-- Zero insertion shifts the actual coordinate basis by one. -/
theorem vectorHeadZero_basisFun (n : ℕ) (i : Fin n) :
    vectorHeadZero n ((Pi.basisFun ℝ (Fin n)) i) =
      (Pi.basisFun ℝ (Fin (n + 1))) i.succ := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, Pi.single_apply]

/-- Increasing enumeration commutes with an order-preserving index inclusion. -/
theorem orderEmbOfFin_map_orderEmbedding
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ↪o β) (S : Finset α) (j : Fin S.card) :
    (S.map e.toEmbedding).orderEmbOfFin (Finset.card_map e.toEmbedding) j =
      e (S.orderEmbOfFin rfl j) := by
  have h := Finset.orderEmbOfFin_unique
    (s := S.map e.toEmbedding) (Finset.card_map e.toEmbedding)
    (f := fun k => e (S.orderEmbOfFin rfl k))
    (fun k => Finset.mem_map.mpr
      ⟨S.orderEmbOfFin rfl k, Finset.orderEmbOfFin_mem S rfl k, rfl⟩)
    (e.strictMono.comp (S.orderEmbOfFin rfl).strictMono)
  exact (congrFun h j).symm

/-- Native Fock transport respects ordered exterior products. -/
theorem fockTailMap_ιMulti (n m : ℕ) (v : Fin m → Vector n) :
    fockTailMap n (ExteriorAlgebra.ιMulti ℝ m v) =
      ExteriorAlgebra.ιMulti ℝ m (vectorHeadZero n ∘ v) := by
  exact ExteriorAlgebra.map_apply_ιMulti (vectorHeadZero n) v

/-- The actual exterior basis is transported by the increasing successor map,
with no permutation sign. The carrier is the existing real SpinorSpace. -/
theorem fockTailMap_exteriorBasis (n : ℕ) (S : Finset (Fin n)) :
    fockTailMap n ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S) =
      (Pi.basisFun ℝ (Fin (n + 1))).ExteriorAlgebra (S.map (Fin.succEmb n)) := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (rfl : S.card = S.card),
    ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_map (Fin.succEmb n))]
  change fockTailMap n (ExteriorAlgebra.ιMulti ℝ S.card
      (fun j => (Pi.basisFun ℝ (Fin n)) (S.orderEmbOfFin rfl j))) =
    ExteriorAlgebra.ιMulti ℝ S.card
      (fun j => (Pi.basisFun ℝ (Fin (n + 1)))
        ((S.map (Fin.succEmb n)).orderEmbOfFin
          (Finset.card_map (Fin.succEmb n)) j))
  rw [fockTailMap_ιMulti]
  congr 1
  funext j
  dsimp only [Function.comp_apply]
  rw [vectorHeadZero_basisFun]
  have hindex :
      ((S.map (Fin.succEmb n)).orderEmbOfFin
        (Finset.card_map (Fin.succEmb n)) j) =
      (S.orderEmbOfFin rfl j).succ := by
    simpa only [Fin.succOrderEmb_toEmbedding, Fin.coe_succOrderEmb] using
      orderEmbOfFin_map_orderEmbedding (Fin.succOrderEmb n) S j
  rw [hindex]

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
