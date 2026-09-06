import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.SplitCayleyF2NormStructural
import InfoGeometry.Algebra.SplitCayleyF2DeltaStructural
import InfoGeometry.Algebra.SplitCayleyF2DeltaComponents
import InfoGeometry.Algebra.SplitCayleyF2Delta2Components
import InfoGeometry.Algebra.SplitCayleyF2DeltaInvolutions
import InfoGeometry.Algebra.SplitCayleyF2CarrierAlignment

namespace InfoGeometry.Algebra.SplitCayleyF2

theorem cayley_card : Fintype.card Cayley = 256 := by native_decide

theorem splitOctF2_card :
    Fintype.card InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2 = 256 := by
  rw [← cayley_card_eq_splitOctF2_card]
  exact cayley_card
@[simp] theorem norm_one : norm (1 : Cayley) = 1 := by
  change (1 : Scalar) * 1 - (0 * 0 + 0 * 0 + 0 * 0) = 1
  decide

theorem norm_mul (x y : Cayley) : norm (x * y) = norm x * norm y := by
  exact norm_mul_structural x y

theorem delta1_norm (r : Vec3) (x : Cayley) : norm (delta1 r x) = norm x := by
  exact delta1_norm_structural r x

theorem delta2_norm (r : Vec3) (x : Cayley) : norm (delta2 r x) = norm x := by
  exact delta2_norm_structural r x

theorem delta1_mul (r : Vec3) (x y : Cayley) :
    delta1 r (x * y) = delta1 r x * delta1 r y := by
  exact delta1_mul_structural r x y

theorem delta2_mul (r : Vec3) (x y : Cayley) :
    delta2 r (x * y) = delta2 r x * delta2 r y := by
  exact delta2_mul_structural r x y

theorem cyclicAction_mul (x y : Cayley) :
    cyclicAction (x * y) = cyclicAction x * cyclicAction y := by
  apply Cayley.ext
  · exact cyclic_mul_alpha_structural x y
  · exact cyclic_mul_u_structural x y
  · exact cyclic_mul_v_structural x y
  · exact cyclic_mul_beta_structural x y

@[simp] theorem cyclicAction_one : cyclicAction (1 : Cayley) = 1 := by
  apply Cayley.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem shearAction_mul (x y : Cayley) :
    shearAction (x * y) = shearAction x * shearAction y := by
  apply Cayley.ext
  · exact shear_mul_alpha_structural x y
  · exact shear_mul_u_structural x y
  · exact shear_mul_v_structural x y
  · exact shear_mul_beta_structural x y

@[simp] theorem shearAction_one : shearAction (1 : Cayley) = 1 := by
  apply Cayley.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem cyclicAction_three (x : Cayley) :
    cyclicAction (cyclicAction (cyclicAction x)) = x := by
  cases x with
  | mk α u v β =>
    apply Cayley.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl

theorem shearAction_square (x : Cayley) :
    shearAction (shearAction x) = x := by
  cases x with
  | mk xa xu xv xb =>
    have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
    apply Cayley.ext
    · rfl
    · funext i
      fin_cases i <;> simp [shearAction, shearU, shearV]
      all_goals try ring_nf
      all_goals try simp [htwo]
    · funext i
      fin_cases i <;> simp [shearAction, shearU, shearV]
      all_goals try ring_nf
      all_goals try simp [htwo]
    · rfl

@[simp] theorem delta1_one_finite (r : Vec3) : delta1 r (1 : Cayley) = 1 := by
  change delta1 r {α := 1, u := ![0, 0, 0], v := ![0, 0, 0], β := 1} =
    {α := 1, u := ![0, 0, 0], v := ![0, 0, 0], β := 1}
  apply Cayley.ext
  · simp [delta1, dot]
  · funext i
    fin_cases i <;> simp [delta1, dot, cross]
  · funext i
    fin_cases i <;> simp [delta1, dot, cross]
  · simp [delta1, dot]

@[simp] theorem delta2_one_finite (r : Vec3) : delta2 r (1 : Cayley) = 1 := by
  have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
  have hone : (1 : Scalar) + 1 = 0 := by
    simpa using htwo
  change delta2 r {α := 1, u := ![0, 0, 0], v := ![0, 0, 0], β := 1} =
    {α := 1, u := ![0, 0, 0], v := ![0, 0, 0], β := 1}
  apply Cayley.ext
  · simp [delta2, dot]
  · funext i
    fin_cases i <;> simp [delta2, dot, cross]
  · funext i
    fin_cases i <;> simp [delta2, dot, cross, hone]
  · simp [delta2, dot]

noncomputable def delta1Automorphism (r : Vec3) : Automorphism where
  toEquiv := Equiv.ofBijective (delta1 r)
    ⟨(fun x y h => by
        rw [← delta1_involutive_structural r x, ← delta1_involutive_structural r y, h]),
      (fun y => ⟨delta1 r y, delta1_involutive_structural r y⟩)⟩
  map_mul' := delta1_mul r
  map_one' := delta1_one_finite r

noncomputable def delta2Automorphism (r : Vec3) : Automorphism where
  toEquiv := Equiv.ofBijective (delta2 r)
    ⟨(fun x y h => by
        rw [← delta2_involutive_structural r x, ← delta2_involutive_structural r y, h]),
      (fun y => ⟨delta2 r y, delta2_involutive_structural r y⟩)⟩
  map_mul' := delta2_mul r
  map_one' := delta2_one_finite r

noncomputable def cyclicAutomorphism : Automorphism where
  toEquiv := Equiv.ofBijective cyclicAction
    ⟨(fun x y h => by
        rw [← cyclicAction_three x, ← cyclicAction_three y, h]),
      (fun y => ⟨cyclicAction (cyclicAction y), cyclicAction_three y⟩)⟩
  map_mul' := cyclicAction_mul
  map_one' := cyclicAction_one

noncomputable def shearAutomorphism : Automorphism where
  toEquiv := Equiv.ofBijective shearAction
    ⟨(fun x y h => by
        rw [← shearAction_square x, ← shearAction_square y, h]),
      (fun y => ⟨shearAction y, shearAction_square y⟩)⟩
  map_mul' := shearAction_mul
  map_one' := shearAction_one

end InfoGeometry.Algebra.SplitCayleyF2
