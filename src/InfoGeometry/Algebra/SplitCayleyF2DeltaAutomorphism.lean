import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SplitCayleyF2DeltaComponents
import InfoGeometry.Algebra.SplitCayleyF2Delta2Components
import InfoGeometry.Algebra.SplitCayleyF2AddMulAutomorphism
import InfoGeometry.Algebra.SplitCayleyF2AutomorphismTransport

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem delta1_involutive (r : Vec3) (x : Cayley) :
    delta1 r (delta1 r x) = x := by
  cases x with
  | mk xa xu xv xb =>
    have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
    have hfour : (4 : Scalar) = 0 := by decide
    have hneg : ∀ a : Scalar, -a = a := fun a => by fin_cases a <;> rfl
    apply Cayley.ext
    · simp [delta1, dot, cross]
      ring_nf
      simp [htwo]
    · funext i
      fin_cases i <;> simp [delta1, dot, cross]
      all_goals ring_nf
      all_goals simp only [sub_eq_add_neg, hneg, htwo, hfour]
      all_goals ring
    · funext i
      fin_cases i <;> simp [delta1, dot, cross]
      all_goals ring_nf
      all_goals simp only [sub_eq_add_neg, hneg, htwo]
      all_goals ring
    · simp [delta1, dot, cross]
      ring_nf
      simp [htwo]

theorem delta2_involutive (r : Vec3) (x : Cayley) :
    delta2 r (delta2 r x) = x := by
  cases x with
  | mk xa xu xv xb =>
    have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
    have hneg : ∀ a : Scalar, -a = a := fun a => by fin_cases a <;> rfl
    apply Cayley.ext
    · simp [delta2, dot, cross]
      ring_nf
      simp [htwo]
    · funext i
      fin_cases i <;> simp [delta2, dot, cross]
      all_goals ring_nf
      all_goals simp only [sub_eq_add_neg, hneg, htwo]
      all_goals ring
    · funext i
      fin_cases i <;> simp [delta2, dot, cross]
      all_goals ring_nf
      all_goals simp only [sub_eq_add_neg, hneg, htwo]
      all_goals ring
    · simp [delta2, dot, cross]
      ring_nf
      simp only [sub_eq_add_neg, hneg, htwo]
      ring

theorem delta1_zero (r : Vec3) : delta1 r zero = zero := by
  apply Cayley.ext
  · simp [delta1, zero, dot]
  · funext i
    fin_cases i <;> simp [delta1, zero, dot]
  · funext i
    fin_cases i <;> simp [delta1, zero, cross]
  · simp [delta1, zero, dot]

theorem delta2_zero (r : Vec3) : delta2 r zero = zero := by
  apply Cayley.ext
  · simp [delta2, zero, dot]
  · funext i
    fin_cases i <;> simp [delta2, zero, cross]
  · funext i
    fin_cases i <;> simp [delta2, zero, dot]
  · simp [delta2, zero, dot]

theorem delta1_one (r : Vec3) : delta1 r one = one := by
  apply Cayley.ext
  · simp [delta1, one, dot]
  · funext i
    fin_cases i <;> simp [delta1, one, dot]
  · funext i
    fin_cases i <;> simp [delta1, one, cross]
  · simp [delta1, one, dot]

theorem delta2_one (r : Vec3) : delta2 r one = one := by
  apply Cayley.ext
  · simp [delta2, one, dot]
  · funext i
    fin_cases i <;> simp [delta2, one, cross]
  · funext i
    fin_cases i <;> { simp [delta2, one, dot]; left; exact CharP.cast_eq_zero Scalar 2 }
  · simp [delta2, one, dot]

theorem delta1_add (r : Vec3) (x y : Cayley) :
    delta1 r (add x y) = add (delta1 r x) (delta1 r y) := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      apply Cayley.ext
      · simp [delta1, add, dot]
        ring
      · funext i
        fin_cases i <;> simp [delta1, add, dot]
        all_goals ring
      · funext i
        fin_cases i <;> simp [delta1, add, cross]
        all_goals ring
      · simp [delta1, add, dot]
        ring

theorem delta2_add (r : Vec3) (x y : Cayley) :
    delta2 r (add x y) = add (delta2 r x) (delta2 r y) := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      apply Cayley.ext
      · simp [delta2, add, dot]
        ring
      · funext i
        fin_cases i <;> simp [delta2, add, cross]
        all_goals ring
      · funext i
        fin_cases i <;> simp [delta2, add, dot]
        all_goals ring
      · simp [delta2, add, dot]
        ring

def delta1Equiv (r : Vec3) : Cayley ≃ Cayley where
  toFun := delta1 r
  invFun := delta1 r
  left_inv := delta1_involutive r
  right_inv := delta1_involutive r

def delta2Equiv (r : Vec3) : Cayley ≃ Cayley where
  toFun := delta2 r
  invFun := delta2 r
  left_inv := delta2_involutive r
  right_inv := delta2_involutive r

def delta1AddMulAutomorphism (r : Vec3) : AddMulAutomorphism where
  toEquiv := delta1Equiv r
  map_zero' := delta1_zero r
  map_add' := delta1_add r
  map_mul' := delta1_mul_structural r
  map_one' := delta1_one r

def delta2AddMulAutomorphism (r : Vec3) : AddMulAutomorphism where
  toEquiv := delta2Equiv r
  map_zero' := delta2_zero r
  map_add' := delta2_add r
  map_mul' := delta2_mul_structural r
  map_one' := delta2_one r

noncomputable def delta1NativeAutomorphism (r : Vec3) : SplitOctF2Aut :=
  (delta1AddMulAutomorphism r).toSplitOctF2Aut

noncomputable def delta2NativeAutomorphism (r : Vec3) : SplitOctF2Aut :=
  (delta2AddMulAutomorphism r).toSplitOctF2Aut

end InfoGeometry.Algebra.SplitCayleyF2
