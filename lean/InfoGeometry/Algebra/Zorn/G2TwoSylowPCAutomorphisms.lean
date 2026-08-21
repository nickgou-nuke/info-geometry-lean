import InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity

namespace InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

theorem pc1_add (X Y : SplitOctF2) :
    pc1Fun (add X Y) = add (pc1Fun X) (pc1Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc1Fun, add, add2, bitToF2_xor] <;>
    ring

theorem pc2_add (X Y : SplitOctF2) :
    pc2Fun (add X Y) = add (pc2Fun X) (pc2Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc2Fun, add, add2, bitToF2_xor] <;>
    ring

theorem pc3_add (X Y : SplitOctF2) :
    pc3Fun (add X Y) = add (pc3Fun X) (pc3Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc3Fun, add, add2, bitToF2_xor] <;>
    ring

theorem pc4_add (X Y : SplitOctF2) :
    pc4Fun (add X Y) = add (pc4Fun X) (pc4Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc4Fun, add, add2, bitToF2_xor] <;>
    ring

theorem pc5_add (X Y : SplitOctF2) :
    pc5Fun (add X Y) = add (pc5Fun X) (pc5Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc5Fun, add, add2, bitToF2_xor] <;>
    ring

theorem pc6_add (X Y : SplitOctF2) :
    pc6Fun (add X Y) = add (pc6Fun X) (pc6Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc6Fun, add, add2, bitToF2_xor] <;>
    ring

theorem pc1_one : pc1Fun one = one := by rfl
theorem pc2_one : pc2Fun one = one := by rfl
theorem pc3_one : pc3Fun one = one := by rfl
theorem pc4_one : pc4Fun one = one := by rfl
theorem pc5_one : pc5Fun one = one := by rfl
theorem pc6_one : pc6Fun one = one := by rfl

theorem pc2_pc6 (X : SplitOctF2) :
    pc2Fun (pc6Fun X) = pc6Fun (pc2Fun X) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc2Fun, pc6Fun, bitToF2_xor] <;>
    ring

theorem pc2_inverse_left (X : SplitOctF2) :
    pc6Fun (pc2Fun (pc2Fun X)) = X := by
  rw [pc2_sq, pc6_sq]

theorem pc2_inverse_right (X : SplitOctF2) :
    pc2Fun (pc6Fun (pc2Fun X)) = X := by
  rw [← pc2_pc6, pc2_sq, pc6_sq]

theorem pc3_pc6 (X : SplitOctF2) :
    pc3Fun (pc6Fun X) = pc6Fun (pc3Fun X) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc3Fun, pc6Fun, bitToF2_xor] <;>
    ring

theorem pc3_inverse_left (X : SplitOctF2) :
    pc6Fun (pc3Fun (pc3Fun X)) = X := by
  rw [pc3_sq, pc6_sq]

theorem pc3_inverse_right (X : SplitOctF2) :
    pc3Fun (pc6Fun (pc3Fun X)) = X := by
  rw [← pc3_pc6, pc3_sq, pc6_sq]

def involutiveEquiv (f : SplitOctF2 → SplitOctF2)
    (hf : ∀ X, f (f X) = X) : SplitOctF2 ≃ SplitOctF2 where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

def pc1Aut : SplitOctF2Aut :=
  ⟨involutiveEquiv pc1Fun pc1_sq, pc1_one, pc1_add, pc1_mul⟩

def pc4Aut : SplitOctF2Aut :=
  ⟨involutiveEquiv pc4Fun pc4_sq, pc4_one, pc4_add, pc4_mul⟩

def pc5Aut : SplitOctF2Aut :=
  ⟨involutiveEquiv pc5Fun pc5_sq, pc5_one, pc5_add, pc5_mul⟩

def pc6Aut : SplitOctF2Aut :=
  ⟨involutiveEquiv pc6Fun pc6_sq, pc6_one, pc6_add, pc6_mul⟩

def pc2Equiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := pc2Fun
  invFun := fun X => pc6Fun (pc2Fun X)
  left_inv := pc2_inverse_left
  right_inv := pc2_inverse_right

def pc2Aut : SplitOctF2Aut :=
  ⟨pc2Equiv, pc2_one, pc2_add, pc2_mul⟩

def pc3Equiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := pc3Fun
  invFun := fun X => pc6Fun (pc3Fun X)
  left_inv := pc3_inverse_left
  right_inv := pc3_inverse_right

def pc3Aut : SplitOctF2Aut :=
  ⟨pc3Equiv, pc3_one, pc3_add, pc3_mul⟩

/-! The two non-involutory PC generators have square `pc6Aut`, as in the
    CAS power relations.  These lemmas keep the relative PC orders separate
    from the actual orders of the concrete carrier automorphisms. -/

theorem pc2Aut_sq_eq_pc6Aut : pc2Aut * pc2Aut = pc6Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  exact pc2_sq X

theorem pc3Aut_sq_eq_pc6Aut : pc3Aut * pc3Aut = pc6Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  exact pc3_sq X

theorem pc2Aut_inv_eq : pc2Aut⁻¹ = pc6Aut * pc2Aut := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Equiv.ext
  intro X
  show pc2Fun (pc2Fun (pc6Fun X)) = X
  rw [pc2_pc6, pc2_inverse_right]

theorem pc3Aut_inv_eq : pc3Aut⁻¹ = pc6Aut * pc3Aut := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Equiv.ext
  intro X
  show pc3Fun (pc3Fun (pc6Fun X)) = X
  rw [pc3_pc6, pc3_inverse_right]

theorem pc2Aut_pow_four : pc2Aut ^ 4 = 1 := by
  calc
    pc2Aut ^ 4 = (pc2Aut * pc2Aut) * (pc2Aut * pc2Aut) := by
      simp [pow_succ, mul_assoc]
    _ = pc6Aut * pc6Aut := by rw [pc2Aut_sq_eq_pc6Aut]
    _ = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro X
      change pc6Fun (pc6Fun X) = X
      exact pc6_sq X

theorem pc3Aut_pow_four : pc3Aut ^ 4 = 1 := by
  calc
    pc3Aut ^ 4 = (pc3Aut * pc3Aut) * (pc3Aut * pc3Aut) := by
      simp [pow_succ, mul_assoc]
    _ = pc6Aut * pc6Aut := by rw [pc3Aut_sq_eq_pc6Aut]
    _ = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro X
      change pc6Fun (pc6Fun X) = X
      exact pc6_sq X

theorem pc6Aut_ne_one : pc6Aut ≠ 1 := by
  intro h
  have hx := congrArg (fun f : SplitOctF2Aut => (f.1 (basis8 7)).y0) h
  revert hx
  decide

def pcGenerator : Fin 6 → SplitOctF2Aut
  | 0 => pc1Aut
  | 1 => pc2Aut
  | 2 => pc3Aut
  | 3 => pc4Aut
  | 4 => pc5Aut
  | 5 => pc6Aut

def pcSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure (Set.range pcGenerator)

theorem pcGenerator_mem_pcSubgroup (i : Fin 6) :
    pcGenerator i ∈ pcSubgroup := by
  exact Subgroup.subset_closure ⟨i, rfl⟩

def pcWord (e : Fin 6 → Bool) : SplitOctF2Aut :=
  (List.ofFn (fun i : Fin 6 => if e i then pcGenerator i else 1)).prod

theorem pcWord_mem_pcSubgroup (e : Fin 6 → Bool) :
    pcWord e ∈ pcSubgroup := by
  have hprod : ∀ (l : List SplitOctF2Aut),
      (∀ x ∈ l, x ∈ pcSubgroup) → l.prod ∈ pcSubgroup := by
    intro l
    induction l with
    | nil =>
        intro _
        exact pcSubgroup.one_mem
    | cons a l ih =>
        intro h
        exact pcSubgroup.mul_mem (h a (by simp))
          (ih (fun x hx => h x (by simp [hx])))
  unfold pcWord
  apply hprod
  rw [List.forall_mem_ofFn_iff]
  intro i
  by_cases h : e i
  · simp [h, pcGenerator_mem_pcSubgroup i]
  · simp [h, pcSubgroup.one_mem]

theorem pcWords_mul_mem_pcSubgroup (e f : Fin 6 → Bool) :
    pcWord e * pcWord f ∈ pcSubgroup := by
  exact pcSubgroup.mul_mem (pcWord_mem_pcSubgroup e) (pcWord_mem_pcSubgroup f)

theorem pcWords_inv_mem_pcSubgroup (e : Fin 6 → Bool) :
    (pcWord e)⁻¹ ∈ pcSubgroup := by
  exact pcSubgroup.inv_mem (pcWord_mem_pcSubgroup e)

theorem pcWord_parameter_card : Fintype.card (Fin 6 → Bool) = 64 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

end InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
