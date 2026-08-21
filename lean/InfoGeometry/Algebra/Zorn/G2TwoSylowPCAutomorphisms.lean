import InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

set_option maxHeartbeats 1000000

namespace InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

theorem pc1_add (X Y : SplitOctF2) :
    pc1Fun (add X Y) = add (pc1Fun X) (pc1Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc1Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem pc2_add (X Y : SplitOctF2) :
    pc2Fun (add X Y) = add (pc2Fun X) (pc2Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc2Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem pc3_add (X Y : SplitOctF2) :
    pc3Fun (add X Y) = add (pc3Fun X) (pc3Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc3Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem pc4_add (X Y : SplitOctF2) :
    pc4Fun (add X Y) = add (pc4Fun X) (pc4Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc4Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem pc5_add (X Y : SplitOctF2) :
    pc5Fun (add X Y) = add (pc5Fun X) (pc5Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc5Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem pc6_add (X Y : SplitOctF2) :
    pc6Fun (add X Y) = add (pc6Fun X) (pc6Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc6Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem pc1_one : pc1Fun one = one := by rfl
theorem pc2_one : pc2Fun one = one := by rfl
theorem pc3_one : pc3Fun one = one := by rfl
theorem pc4_one : pc4Fun one = one := by rfl
theorem pc5_one : pc5Fun one = one := by rfl
theorem pc6_one : pc6Fun one = one := by rfl

theorem pc2_pc6 (X : SplitOctF2) :
    pc2Fun (pc6Fun X) = pc6Fun (pc2Fun X) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [pc2Fun, pc6Fun, Bool.xor_left_comm, Bool.xor_comm]

theorem pc2_inverse_left (X : SplitOctF2) :
    pc6Fun (pc2Fun (pc2Fun X)) = X := by
  rw [pc2_sq, pc6_sq]

theorem pc2_inverse_right (X : SplitOctF2) :
    pc2Fun (pc6Fun (pc2Fun X)) = X := by
  rw [← pc2_pc6, pc2_sq, pc6_sq]

theorem pc3_pc6 (X : SplitOctF2) :
    pc3Fun (pc6Fun X) = pc6Fun (pc3Fun X) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [pc3Fun, pc6Fun, Bool.xor_left_comm, Bool.xor_comm]

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
  ⟨involutiveEquiv pc4Fun pc4_sq, by exact pc4_one, pc4_add, pc4_mul⟩

def pc5Aut : SplitOctF2Aut :=
  ⟨involutiveEquiv pc5Fun pc5_sq, by exact pc5_one, pc5_add, pc5_mul⟩

def pc6Aut : SplitOctF2Aut :=
  ⟨involutiveEquiv pc6Fun pc6_sq, by exact pc6_one, pc6_add, pc6_mul⟩

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

end InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
