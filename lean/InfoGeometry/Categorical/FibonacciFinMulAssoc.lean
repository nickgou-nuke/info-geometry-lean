import Mathlib

/-!
# Named finite-index associativity transport

The matrix Fibonacci owners use `Fin (m * n)` as a concrete encoding of a
product index.  This owner names the associativity transport between the two
parenthesizations and records the value-preservation facts needed when
comparing reindexed Kronecker matrices.
-/

namespace InfoGeometry.Categorical.FibonacciFinMulAssoc

private theorem fin_cast_congrArg_val {n m : ℕ} (h : n = m) (i : Fin n) :
    (Equiv.cast (congrArg Fin h) i).val = i.val := by
  cases h
  rfl

noncomputable def finMulAssocEquiv (m n p : ℕ) :
    Fin ((m * n) * p) ≃ Fin (m * (n * p)) :=
  Equiv.cast (congrArg Fin (Nat.mul_assoc m n p))

theorem finMulAssocEquiv_apply_val (m n p : ℕ) (i : Fin ((m * n) * p)) :
    (finMulAssocEquiv m n p i).val = i.val := by
  unfold finMulAssocEquiv
  exact fin_cast_congrArg_val (Nat.mul_assoc m n p) i

theorem finMulAssocEquiv_symm_apply_val (m n p : ℕ)
    (i : Fin (m * (n * p))) :
    ((finMulAssocEquiv m n p).symm i).val = i.val := by
  unfold finMulAssocEquiv
  exact fin_cast_congrArg_val (Nat.mul_assoc m n p).symm i

noncomputable def leftAssocIndexEquiv (m n p : ℕ) :
    (Fin m × Fin n) × Fin p ≃ Fin (m * (n * p)) :=
  ((Equiv.prodCongr (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))
      (Equiv.refl (Fin p))).trans
    (finProdFinEquiv : Fin (m * n) × Fin p ≃ Fin ((m * n) * p))).trans
    (finMulAssocEquiv m n p)

noncomputable def rightAssocIndexEquiv (m n p : ℕ) :
    Fin m × (Fin n × Fin p) ≃ Fin (m * (n * p)) :=
  (Equiv.prodCongr (Equiv.refl (Fin m))
      (finProdFinEquiv : Fin n × Fin p ≃ Fin (n * p))).trans
    (finProdFinEquiv : Fin m × Fin (n * p) ≃ Fin (m * (n * p)))

theorem leftAssocIndexEquiv_eq_prodAssoc_trans_rightAssoc
    (m n p : ℕ) :
    leftAssocIndexEquiv m n p =
      (Equiv.prodAssoc (Fin m) (Fin n) (Fin p)).trans
        (rightAssocIndexEquiv m n p) := by
  ext x
  rcases x with ⟨⟨i, j⟩, k⟩
  dsimp [leftAssocIndexEquiv, rightAssocIndexEquiv]
  have hcast := finMulAssocEquiv_apply_val m n p
    (finProdFinEquiv (⟨finProdFinEquiv (i, j), k⟩))
  rw [hcast]
  simp [finProdFinEquiv]
  simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ac_rfl

end InfoGeometry.Categorical.FibonacciFinMulAssoc
