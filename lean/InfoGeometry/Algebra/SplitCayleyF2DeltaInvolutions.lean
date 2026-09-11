import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SplitCayleyF2DeltaComponents
import InfoGeometry.Algebra.SplitCayleyF2Delta2Components

namespace InfoGeometry.Algebra.SplitCayleyF2

/-! Involutivity of the two native delta maps, before packaging them as
automorphisms.  Keeping this owner below the packaging layer makes the
bijectivity proof independent of finite enumeration. -/

theorem delta1_involutive_structural (r : Vec3) (x : Cayley) :
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

theorem delta2_involutive_structural (r : Vec3) (x : Cayley) :
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

end InfoGeometry.Algebra.SplitCayleyF2
