import InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

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
  ext <;> simp [pc2Fun, pc6Fun, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem pc2_inverse_left (X : SplitOctF2) :
    pc6Fun (pc2Fun (pc2Fun X)) = X := by
  rw [pc2_sq, pc6_sq]

theorem pc2_inverse_right (X : SplitOctF2) :
    pc2Fun (pc6Fun (pc2Fun X)) = X := by
  rw [← pc2_pc6, pc2_sq, pc6_sq]

end InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
