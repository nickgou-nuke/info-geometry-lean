import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

/-! Native finite-index distribution used by the nested `blockDiag` channel
readouts.  This is only an equivalence of existing `Fin`/product/sum indices;
it introduces no fusion-tree carrier. -/

noncomputable def finSumProdFinEquiv (a b c : ℕ) :
    (Fin a × Fin c) ⊕ (Fin b × Fin c) ≃ Fin ((a + b) * c) :=
  ((Equiv.sumProdDistrib (Fin a) (Fin b) (Fin c)).symm.trans
      (Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin c)))).trans
    finProdFinEquiv

@[simp] theorem finSumProdFinEquiv_apply_left
    (a b c : ℕ) (i : Fin a) (k : Fin c) :
    finSumProdFinEquiv a b c (Sum.inl (i, k)) =
      finProdFinEquiv (finSumFinEquiv (Sum.inl i), k) := by
  simp [finSumProdFinEquiv]

@[simp] theorem finSumProdFinEquiv_apply_right
    (a b c : ℕ) (j : Fin b) (k : Fin c) :
    finSumProdFinEquiv a b c (Sum.inr (j, k)) =
      finProdFinEquiv (finSumFinEquiv (Sum.inr j), k) := by
  simp [finSumProdFinEquiv]

/-! The two branch embeddings underlying `finSumProdFinEquiv`. -/

noncomputable def finProdSumLeftEmbed (a b c : ℕ) :
    Fin (a * c) → Fin ((a + b) * c) := fun i =>
  finProdFinEquiv
    (finSumFinEquiv (Sum.inl ((finProdFinEquiv.symm i).1)),
      (finProdFinEquiv.symm i).2)

noncomputable def finProdSumRightEmbed (a b c : ℕ) :
    Fin (b * c) → Fin ((a + b) * c) := fun i =>
  finProdFinEquiv
    (finSumFinEquiv (Sum.inr ((finProdFinEquiv.symm i).1)),
      (finProdFinEquiv.symm i).2)

noncomputable def finSumLeftEmbed (a b : ℕ) :
    Fin a → Fin (a + b) := fun i => finSumFinEquiv (Sum.inl i)

noncomputable def finSumRightEmbed (a b : ℕ) :
    Fin b → Fin (a + b) := fun i => finSumFinEquiv (Sum.inr i)

theorem finSumLeftEmbed_injective (a b : ℕ) :
    Function.Injective (finSumLeftEmbed a b) := by
  intro i j h
  exact Sum.inl.inj (finSumFinEquiv.injective h)

theorem finSumRightEmbed_injective (a b : ℕ) :
    Function.Injective (finSumRightEmbed a b) := by
  intro i j h
  exact Sum.inr.inj (finSumFinEquiv.injective h)

theorem finSumLeftEmbed_ne_rightEmbed
    (a b : ℕ) (i : Fin a) (j : Fin b) :
    finSumLeftEmbed a b i ≠ finSumRightEmbed a b j := by
  intro h
  exact Sum.inl_ne_inr (finSumFinEquiv.injective h)

/-! The three native branches of the left-associated `blockDiag3` index. -/

noncomputable def finSum3FirstEmbed (a b c : ℕ) :
    Fin a → Fin ((a + b) + c) := fun i =>
  finSumLeftEmbed (a + b) c (finSumLeftEmbed a b i)

noncomputable def finSum3SecondEmbed (a b c : ℕ) :
    Fin b → Fin ((a + b) + c) := fun i =>
  finSumLeftEmbed (a + b) c (finSumRightEmbed a b i)

noncomputable def finSum3ThirdEmbed (a b c : ℕ) :
    Fin c → Fin ((a + b) + c) := fun i =>
  finSumRightEmbed (a + b) c i

theorem finSum3FirstEmbed_injective (a b c : ℕ) :
    Function.Injective (finSum3FirstEmbed a b c) := by
  exact (finSumLeftEmbed_injective (a + b) c).comp
    (finSumLeftEmbed_injective a b)

theorem finSum3SecondEmbed_injective (a b c : ℕ) :
    Function.Injective (finSum3SecondEmbed a b c) := by
  exact (finSumLeftEmbed_injective (a + b) c).comp
    (finSumRightEmbed_injective a b)

theorem finSum3ThirdEmbed_injective (a b c : ℕ) :
    Function.Injective (finSum3ThirdEmbed a b c) := by
  exact finSumRightEmbed_injective (a + b) c

theorem finSum3FirstEmbed_ne_secondEmbed
    (a b c : ℕ) (i : Fin a) (j : Fin b) :
    finSum3FirstEmbed a b c i ≠ finSum3SecondEmbed a b c j := by
  intro h
  apply finSumLeftEmbed_ne_rightEmbed a b
  exact (finSumLeftEmbed_injective (a + b) c) h

theorem finSum3FirstEmbed_ne_thirdEmbed
    (a b c : ℕ) (i : Fin a) (k : Fin c) :
    finSum3FirstEmbed a b c i ≠ finSum3ThirdEmbed a b c k := by
  intro h
  exact finSumLeftEmbed_ne_rightEmbed (a + b) c _ _ h

theorem finSum3SecondEmbed_ne_thirdEmbed
    (a b c : ℕ) (j : Fin b) (k : Fin c) :
    finSum3SecondEmbed a b c j ≠ finSum3ThirdEmbed a b c k := by
  intro h
  exact finSumLeftEmbed_ne_rightEmbed (a + b) c _ _ h

noncomputable def finSum3Equiv (a b c : ℕ) :
    Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin ((a + b) + c) :=
  ((Equiv.sumAssoc (Fin a) (Fin b) (Fin c)).symm.trans
      (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin c)))).trans
    finSumFinEquiv

@[simp] theorem finSum3Equiv_apply_inl
    (a b c : ℕ) (i : Fin a) :
    finSum3Equiv a b c (Sum.inl i) = finSum3FirstEmbed a b c i := by
  simp [finSum3Equiv, finSum3FirstEmbed, finSumLeftEmbed]

@[simp] theorem finSum3Equiv_apply_inr_inl
    (a b c : ℕ) (j : Fin b) :
    finSum3Equiv a b c (Sum.inr (Sum.inl j)) =
      finSum3SecondEmbed a b c j := by
  simp [finSum3Equiv, finSum3SecondEmbed, finSumLeftEmbed,
    finSumRightEmbed]

@[simp] theorem finSum3Equiv_apply_inr_inr
    (a b c : ℕ) (k : Fin c) :
    finSum3Equiv a b c (Sum.inr (Sum.inr k)) =
      finSum3ThirdEmbed a b c k := by
  simp [finSum3Equiv, finSum3ThirdEmbed, finSumRightEmbed]

theorem finProdSumLeftEmbed_injective (a b c : ℕ) :
    Function.Injective (finProdSumLeftEmbed a b c) := by
  intro i j h
  apply finProdFinEquiv.symm.injective
  simpa [finProdSumLeftEmbed] using congrArg finProdFinEquiv.symm h

theorem finProdSumRightEmbed_injective (a b c : ℕ) :
    Function.Injective (finProdSumRightEmbed a b c) := by
  intro i j h
  apply finProdFinEquiv.symm.injective
  simpa [finProdSumRightEmbed] using congrArg finProdFinEquiv.symm h

theorem finProdSumLeftEmbed_ne_rightEmbed
    (a b c : ℕ)
    (i : Fin (a * c)) (j : Fin (b * c)) :
    finProdSumLeftEmbed a b c i ≠ finProdSumRightEmbed a b c j := by
  intro h
  have hp := congrArg finProdFinEquiv.symm h
  have hs :
      finSumFinEquiv (Sum.inl ((finProdFinEquiv.symm i).1)) =
        finSumFinEquiv (Sum.inr ((finProdFinEquiv.symm j).1)) := by
    simpa only [finProdSumLeftEmbed, finProdSumRightEmbed,
      Equiv.symm_apply_apply] using congrArg Prod.fst hp
  exact Sum.inl_ne_inr (finSumFinEquiv.injective hs)

@[simp] theorem finSumProdFinEquiv_inl_as_leftEmbed
    (a b c : ℕ) (i : Fin a) (k : Fin c) :
    finSumProdFinEquiv a b c (Sum.inl (i, k)) =
      finProdSumLeftEmbed a b c (finProdFinEquiv (i, k)) := by
  simp [finSumProdFinEquiv, finProdSumLeftEmbed]

@[simp] theorem finSumProdFinEquiv_inr_as_rightEmbed
    (a b c : ℕ) (j : Fin b) (k : Fin c) :
    finSumProdFinEquiv a b c (Sum.inr (j, k)) =
      finProdSumRightEmbed a b c (finProdFinEquiv (j, k)) := by
  simp [finSumProdFinEquiv, finProdSumRightEmbed]

/-! Distribution of a three-way sum over a common finite product factor. -/

noncomputable def finSum3ProdFinEquiv (a b c d : ℕ) :
    (Fin (a * d) ⊕ (Fin (b * d) ⊕ Fin (c * d))) ≃
      Fin (((a + b) + c) * d) :=
  let e₁ :=
    (Equiv.sumAssoc (Fin (a * d)) (Fin (b * d)) (Fin (c * d))).symm
  let e₂ :=
    Equiv.sumCongr
      (Equiv.sumCongr
        (finProdFinEquiv (m := a) (n := d)).symm
        (finProdFinEquiv (m := b) (n := d)).symm)
      (Equiv.refl (Fin (c * d)))
  let e₃ :=
    Equiv.sumCongr (finSumProdFinEquiv a b d)
      (Equiv.refl (Fin (c * d)))
  let e₄ :=
    Equiv.sumCongr
      (finProdFinEquiv (m := a + b) (n := d)).symm
      (finProdFinEquiv (m := c) (n := d)).symm
  let e₅ := finSumProdFinEquiv (a + b) c d
  (((e₁.trans e₂).trans e₃).trans e₄).trans e₅

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
  simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  ac_rfl

end InfoGeometry.Categorical.FibonacciFinMulAssoc
