import InfoGeometry.Algebra.SplitCayleyF2DeltaAutomorphism

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-! Native-carrier consequences of the internally proved Cayley delta laws. -/

theorem delta1_zero_parameter (x : Cayley) :
    delta1 (0 : Vec3) x = x := by
  cases x with
  | mk xa xu xv xb =>
    apply Cayley.ext
    · simp [delta1, dot]
    · funext i
      fin_cases i <;> simp [delta1, dot]
    · funext i
      fin_cases i <;> simp [delta1, cross]
    · simp [delta1, dot]

theorem delta2_zero_parameter (x : Cayley) :
    delta2 (0 : Vec3) x = x := by
  cases x with
  | mk xa xu xv xb =>
    apply Cayley.ext
    · simp [delta2, dot]
    · funext i
      fin_cases i <;> simp [delta2, cross]
    · funext i
      fin_cases i <;> simp [delta2, dot]
    · simp [delta2, dot]

theorem delta1NativeAutomorphism_zero_parameter (x : SplitOctF2) :
    (delta1NativeAutomorphism 0).1 x = x := by
  apply cayleySplitOctF2Equiv.symm.injective
  change cayleySplitOctF2Equiv.symm
      ((delta1AddMulAutomorphism 0).toSplitOctF2Equiv x) =
    cayleySplitOctF2Equiv.symm x
  rw [AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback]
  exact delta1_zero_parameter _

theorem delta2NativeAutomorphism_zero_parameter (x : SplitOctF2) :
    (delta2NativeAutomorphism 0).1 x = x := by
  apply cayleySplitOctF2Equiv.symm.injective
  change cayleySplitOctF2Equiv.symm
      ((delta2AddMulAutomorphism 0).toSplitOctF2Equiv x) =
    cayleySplitOctF2Equiv.symm x
  rw [AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback]
  exact delta2_zero_parameter _

theorem delta1_parameter_add_of_trivial (r s : Vec3) (x : Cayley)
    (h : r = 0 ∨ s = 0 ∨ r = s) :
    delta1 r (delta1 s x) = delta1 (r + s) x := by
  rcases h with h | h | h
  · subst r
    simp [delta1_zero_parameter]
  · subst s
    simp [delta1_zero_parameter]
  · subst s
    have hrs : r + r = (0 : Vec3) := by
      have htwo : ∀ a : Scalar, a + a = 0 := by
        intro a
        fin_cases a <;> rfl
      funext i
      fin_cases i <;> simp [htwo]
    rw [hrs]
    simp [delta1_zero_parameter, delta1_involutive]

theorem delta2_parameter_add_of_trivial (r s : Vec3) (x : Cayley)
    (h : r = 0 ∨ s = 0 ∨ r = s) :
    delta2 r (delta2 s x) = delta2 (r + s) x := by
  rcases h with h | h | h
  · subst r
    simp [delta2_zero_parameter]
  · subst s
    simp [delta2_zero_parameter]
  · subst s
    have hrs : r + r = (0 : Vec3) := by
      have htwo : ∀ a : Scalar, a + a = 0 := by
        intro a
        fin_cases a <;> rfl
      funext i
      fin_cases i <;> simp [htwo]
    rw [hrs]
    simp [delta2_zero_parameter, delta2_involutive]

theorem delta1Native_parameter_add_of_trivial (r s : Vec3) (x : SplitOctF2)
    (h : r = 0 ∨ s = 0 ∨ r = s) :
    (delta1NativeAutomorphism r).1
        ((delta1NativeAutomorphism s).1 x) =
      (delta1NativeAutomorphism (r + s)).1 x := by
  apply cayleySplitOctF2Equiv.symm.injective
  change cayleySplitOctF2Equiv.symm
      ((delta1AddMulAutomorphism r).toSplitOctF2Equiv
        ((delta1AddMulAutomorphism s).toSplitOctF2Equiv x)) =
    cayleySplitOctF2Equiv.symm
      ((delta1AddMulAutomorphism (r + s)).toSplitOctF2Equiv x)
  rw [AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback,
    AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback,
    AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback]
  exact delta1_parameter_add_of_trivial r s _ h

theorem delta2Native_parameter_add_of_trivial (r s : Vec3) (x : SplitOctF2)
    (h : r = 0 ∨ s = 0 ∨ r = s) :
    (delta2NativeAutomorphism r).1
        ((delta2NativeAutomorphism s).1 x) =
      (delta2NativeAutomorphism (r + s)).1 x := by
  apply cayleySplitOctF2Equiv.symm.injective
  change cayleySplitOctF2Equiv.symm
      ((delta2AddMulAutomorphism r).toSplitOctF2Equiv
        ((delta2AddMulAutomorphism s).toSplitOctF2Equiv x)) =
    cayleySplitOctF2Equiv.symm
      ((delta2AddMulAutomorphism (r + s)).toSplitOctF2Equiv x)
  rw [AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback,
    AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback,
    AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback]
  exact delta2_parameter_add_of_trivial r s _ h

theorem delta1NativeAutomorphism_mul_of_trivial
    (r s : Vec3) (h : r = 0 ∨ s = 0 ∨ r = s) :
    delta1NativeAutomorphism r * delta1NativeAutomorphism s =
      delta1NativeAutomorphism (r + s) := by
  have hs : s = 0 ∨ r = 0 ∨ s = r := by
    rcases h with hr | hs | hrs
    · exact Or.inr (Or.inl hr)
    · exact Or.inl hs
    · exact Or.inr (Or.inr hrs.symm)
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (delta1NativeAutomorphism s).1
      ((delta1NativeAutomorphism r).1 x) =
    (delta1NativeAutomorphism (r + s)).1 x
  rw [add_comm r s]
  exact delta1Native_parameter_add_of_trivial s r x hs

theorem delta2NativeAutomorphism_mul_of_trivial
    (r s : Vec3) (h : r = 0 ∨ s = 0 ∨ r = s) :
    delta2NativeAutomorphism r * delta2NativeAutomorphism s =
      delta2NativeAutomorphism (r + s) := by
  have hs : s = 0 ∨ r = 0 ∨ s = r := by
    rcases h with hr | hs | hrs
    · exact Or.inr (Or.inl hr)
    · exact Or.inl hs
    · exact Or.inr (Or.inr hrs.symm)
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (delta2NativeAutomorphism s).1
      ((delta2NativeAutomorphism r).1 x) =
    (delta2NativeAutomorphism (r + s)).1 x
  rw [add_comm r s]
  exact delta2Native_parameter_add_of_trivial s r x hs

theorem delta1Native_map_add (r : Vec3) (x y : SplitOctF2) :
    (delta1NativeAutomorphism r).1
        (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
        ((delta1NativeAutomorphism r).1 x) ((delta1NativeAutomorphism r).1 y) := by
  exact (delta1NativeAutomorphism r).2.2.1 x y

theorem delta1Native_map_mul (r : Vec3) (x y : SplitOctF2) :
    (delta1NativeAutomorphism r).1
        (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        ((delta1NativeAutomorphism r).1 x) ((delta1NativeAutomorphism r).1 y) := by
  exact (delta1NativeAutomorphism r).2.2.2 x y

theorem delta2Native_map_add (r : Vec3) (x y : SplitOctF2) :
    (delta2NativeAutomorphism r).1
        (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
        ((delta2NativeAutomorphism r).1 x) ((delta2NativeAutomorphism r).1 y) := by
  exact (delta2NativeAutomorphism r).2.2.1 x y

theorem delta2Native_map_mul (r : Vec3) (x y : SplitOctF2) :
    (delta2NativeAutomorphism r).1
        (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        ((delta2NativeAutomorphism r).1 x) ((delta2NativeAutomorphism r).1 y) := by
  exact (delta2NativeAutomorphism r).2.2.2 x y

theorem delta1Native_map_one (r : Vec3) :
    (delta1NativeAutomorphism r).1
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one := by
  exact (delta1NativeAutomorphism r).2.1

theorem delta2Native_map_one (r : Vec3) :
    (delta2NativeAutomorphism r).1
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one := by
  exact (delta2NativeAutomorphism r).2.1

theorem delta1NativeAutomorphism_square (r : Vec3) (x : SplitOctF2) :
    (delta1NativeAutomorphism r).1 ((delta1NativeAutomorphism r).1 x) = x := by
  apply cayleySplitOctF2Equiv.symm.injective
  change cayleySplitOctF2Equiv.symm
      ((delta1AddMulAutomorphism r).toSplitOctF2Equiv
        ((delta1AddMulAutomorphism r).toSplitOctF2Equiv x)) =
    cayleySplitOctF2Equiv.symm x
  rw [AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback,
    AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback]
  exact delta1_involutive r _

theorem delta2NativeAutomorphism_square (r : Vec3) (x : SplitOctF2) :
    (delta2NativeAutomorphism r).1 ((delta2NativeAutomorphism r).1 x) = x := by
  apply cayleySplitOctF2Equiv.symm.injective
  change cayleySplitOctF2Equiv.symm
      ((delta2AddMulAutomorphism r).toSplitOctF2Equiv
        ((delta2AddMulAutomorphism r).toSplitOctF2Equiv x)) =
    cayleySplitOctF2Equiv.symm x
  rw [AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback,
    AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback]
  exact delta2_involutive r _

theorem delta1NativeAutomorphism_pow_two (r : Vec3) :
    delta1NativeAutomorphism r ^ 2 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (delta1NativeAutomorphism r).1
      ((delta1NativeAutomorphism r).1 x) = x
  exact delta1NativeAutomorphism_square r x

end InfoGeometry.Algebra.SplitCayleyF2
