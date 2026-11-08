/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FockTailExteriorBasis

/-!
# Signed coordinate actions on the native finite exterior basis

Signs are Mathlib's exact sorting-permutation
signs in ℤˣ. No metric, new operator carrier, or assumed action formula.
-/
noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford

/-- The singleton exterior basis vector is the native Clifford generator. -/
theorem fockExteriorBasis_singleton (n : ℕ) (i : Fin n) :
    (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra {i} =
      CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) ((Pi.basisFun ℝ (Fin n)) i) := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton i)]
  change ExteriorAlgebra.ιMulti ℝ 1
    (fun j => (Pi.basisFun ℝ (Fin n))
      (({i} : Finset (Fin n)).orderEmbOfFin (Finset.card_singleton i) j)) = _
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  have hi := Finset.orderEmbOfFin_mem ({i} : Finset (Fin n))
    (Finset.card_singleton i) (0 : Fin 1)
  have he := Finset.mem_singleton.mp hi
  rw [he]

/-- Contraction vanishes on a wedge word when the covector kills every letter. -/
theorem contractLeft_ιMulti_of_zero (n m : ℕ) (φ : Module.Dual ℝ (Vector n))
    (v : Fin m → Vector n) (hv : ∀ j, φ (v j) = 0) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Vector n))) φ
      (ExteriorAlgebra.ιMulti ℝ m v) = 0 := by
  induction m with
  | zero => simp only [ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one]
  | succ m ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul,
        hv 0, ih (Matrix.vecTail v) (fun j => hv j.succ)]
      simp only [zero_smul, mul_zero, sub_zero]

/-- An unoccupied coordinate contracts to zero on the actual exterior basis. -/
theorem fock_intAction_basis_of_not_mem (n : ℕ) (i : Fin n)
    (S : Finset (Fin n)) (hi : i ∉ S) :
    intAction (LinearMap.proj i : Module.Dual ℝ (Vector n))
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S) = 0 := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (rfl : S.card = S.card)]
  apply contractLeft_ιMulti_of_zero
  intro j
  have hj := Finset.orderEmbOfFin_mem S rfl j
  have hne : i ≠ S.orderEmbOfFin rfl j := by
    intro h
    exact hi (h.symm ▸ hj)
  change (Pi.basisFun ℝ (Fin n) (S.orderEmbOfFin rfl j)) i = 0
  simp [Pi.basisFun_apply, hne]

/-- Sign of sorting a fresh singleton followed by an increasing occupied set. -/
def fockInsertSign (n : ℕ) (i : Fin n) (S : Finset (Fin n)) (hi : i ∉ S) : ℤˣ :=
  (Set.powersetCard.permOfDisjoint
    (s := Set.powersetCard.ofCard (Finset.card_singleton i))
    (t := Set.powersetCard.ofCard (rfl : S.card = S.card))
    (Finset.disjoint_singleton_left.mpr hi)).sign

/-- Left creation inserts the fresh index with the exact native sorting sign. -/
theorem fock_extAction_basis_insert (n : ℕ) (i : Fin n)
    (S : Finset (Fin n)) (hi : i ∉ S) :
    extAction ((Pi.basisFun ℝ (Fin n)) i)
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S) =
    fockInsertSign n i S hi •
      (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra (insert i S) := by
  change CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n))
      ((Pi.basisFun ℝ (Fin n)) i) *
      (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S = _
  let s := Set.powersetCard.ofCard (Finset.card_singleton i)
  let t := Set.powersetCard.ofCard (rfl : S.card = S.card)
  have hd : Disjoint s.val t.val := Finset.disjoint_singleton_left.mpr hi
  have hu : (Set.powersetCard.disjUnion hd : Finset (Fin n)) = insert i S := by
    change ({i} : Finset (Fin n)).disjUnion S
      (Finset.disjoint_singleton_left.mpr hi) = insert i S
    rw [Finset.disjUnion_eq_union, Finset.singleton_union]
  have h := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun ℝ (Fin n)) s t hd
  change (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra {i} *
      (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S =
    fockInsertSign n i S hi • (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra
      (Set.powersetCard.disjUnion hd : Finset (Fin n)) at h
  rw [fockExteriorBasis_singleton, hu] at h
  exact h

/-- Creation at an already occupied coordinate is zero. -/
theorem fock_extAction_basis_of_mem (n : ℕ) (i : Fin n)
    (S : Finset (Fin n)) (hi : i ∈ S) :
    extAction ((Pi.basisFun ℝ (Fin n)) i)
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S) = 0 := by
  change CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n))
      ((Pi.basisFun ℝ (Fin n)) i) *
      (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S = 0
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun ℝ (Fin n))
    (Set.powersetCard.ofCard (Finset.card_singleton i))
    (Set.powersetCard.ofCard (rfl : S.card = S.card))
    (by simpa only [Set.powersetCard.val_ofCard, Finset.disjoint_singleton_left,
      not_not] using hi)
  simpa only [Set.powersetCard.val_ofCard, fockExteriorBasis_singleton] using h

/-- Contraction deletes a freshly inserted index with the same sorting sign. -/
theorem fock_intAction_basis_insert (n : ℕ) (i : Fin n)
    (S : Finset (Fin n)) (hi : i ∉ S) :
    intAction (LinearMap.proj i : Module.Dual ℝ (Vector n))
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra (insert i S)) =
    fockInsertSign n i S hi • (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S := by
  have h := ext_int_anticommutator ((Pi.basisFun ℝ (Fin n)) i)
    (LinearMap.proj i : Module.Dual ℝ (Vector n))
    ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S)
  rw [fock_intAction_basis_of_not_mem n i S hi, map_zero, zero_add,
    fock_extAction_basis_insert n i S hi, map_zsmul_unit] at h
  have heval : (LinearMap.proj i : Module.Dual ℝ (Vector n))
      ((Pi.basisFun ℝ (Fin n)) i) = 1 := by simp
  rw [heval, map_one, one_mul] at h
  calc
    _ = (fockInsertSign n i S hi)⁻¹ •
        (fockInsertSign n i S hi •
          intAction (LinearMap.proj i : Module.Dual ℝ (Vector n))
            ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra (insert i S))) :=
      (inv_smul_smul _ _).symm
    _ = (fockInsertSign n i S hi)⁻¹ •
        (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S := congrArg _ h
    _ = _ := by rw [Int.units_inv_eq_self]

/-- Occupied-coordinate deletion, with sign computed on the remaining set. -/
theorem fock_intAction_basis_erase (n : ℕ) (i : Fin n)
    (S : Finset (Fin n)) (hi : i ∈ S) :
    intAction (LinearMap.proj i : Module.Dual ℝ (Vector n))
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S) =
    fockInsertSign n i (S.erase i) (Finset.notMem_erase i S) •
      (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra (S.erase i) := by
  simpa only [Finset.insert_erase hi] using
    fock_intAction_basis_insert n i (S.erase i) (Finset.notMem_erase i S)

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
