import InfoGeometry.Exceptional.FiniteJ3ZornCarrier
import InfoGeometry.Exceptional.ZornMatrixRealCanonicalBridge

namespace InfoGeometry.Exceptional.FiniteJ3Zorn

open InfoGeometry.Exceptional.RealZorn
open InfoGeometry.Algebra

def canonicalEntry (X : J3) : Fin 3 → Fin 3 → ZornVectorMatrix ℝ :=
  fun i j => canonicalEquiv (X i j)

@[simp] theorem canonicalEntry_apply (X : J3) (i j : Fin 3) :
    canonicalEntry X i j = canonicalEquiv (X i j) := rfl

theorem canonicalEntry_zornHalf (X : J3) (i j : Fin 3) :
    canonicalEntry (fun r k => zornHalf (X r k)) i j =
      ZornVectorMatrix.smul (2 : ℝ)⁻¹ (canonicalEntry X i j) := by
  exact canonicalEquiv_zornHalf (X i j)

theorem canonicalEntry_zornConj (X : J3) (i j : Fin 3) :
    canonicalEquiv (zornConj (X i j)) =
      ZornVectorMatrix.conj (canonicalEntry X i j) := by
  have h : zornConj (X i j) = InfoGeometry.Exceptional.RealZorn.realConj (X i j) := by
    apply InfoGeometry.Exceptional.RealZorn.ZornMatrixReal.ext
    · rfl
    · rfl
    · rfl
    · rfl
  rw [h]
  exact InfoGeometry.Exceptional.RealZorn.canonicalEquiv_conj (X i j)

theorem canonicalEntry_add (X Y : J3) (i j : Fin 3) :
    canonicalEntry (X + Y) i j =
      ZornVectorMatrix.add (canonicalEntry X i j) (canonicalEntry Y i j) := by
  exact toCanonical_add (X i j) (Y i j)

theorem canonicalEntry_mul (X Y : J3) (i j : Fin 3) :
    canonicalEntry (fun r k => X r k * Y r k) i j =
      ZornVectorMatrix.mul (canonicalEntry X i j) (canonicalEntry Y i j) := by
  exact canonicalEquiv_mul (X i j) (Y i j)

theorem canonicalEntry_j3RawMul (X Y : J3) (i k : Fin 3) :
    canonicalEquiv (j3RawMul X Y i k) =
      ∑ j : Fin 3,
        ZornVectorMatrix.mul (canonicalEquiv (X i j))
          (canonicalEquiv (Y j k)) := by
  simp only [j3RawMul, Fin.sum_univ_three]
  rw [canonicalEquiv_add, canonicalEquiv_add,
    canonicalEquiv_mul, canonicalEquiv_mul, canonicalEquiv_mul]
  rfl

theorem canonicalEntry_jordanProduct (X Y : J3) (i k : Fin 3) :
    canonicalEquiv (jordanProduct X Y i k) =
      ZornVectorMatrix.smul (2 : ℝ)⁻¹
        (ZornVectorMatrix.add
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (X i j))
              (canonicalEquiv (Y j k)))
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (Y i j))
              (canonicalEquiv (X j k)))) := by
  rw [jordanProduct_apply, canonicalEquiv_zornHalf,
    canonicalEquiv_add, canonicalEntry_j3RawMul,
    canonicalEntry_j3RawMul]

theorem canonicalEntry_jordanProduct_a (X Y : J3) (i k : Fin 3) :
    (canonicalEquiv (jordanProduct X Y i k)).a =
      (ZornVectorMatrix.smul (2 : ℝ)⁻¹
        (ZornVectorMatrix.add
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (X i j))
              (canonicalEquiv (Y j k)))
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (Y i j))
              (canonicalEquiv (X j k))))).a := by
  exact congrArg ZornVectorMatrix.a (canonicalEntry_jordanProduct X Y i k)

theorem canonicalEntry_jordanProduct_b (X Y : J3) (i k : Fin 3) :
    (canonicalEquiv (jordanProduct X Y i k)).b =
      (ZornVectorMatrix.smul (2 : ℝ)⁻¹
        (ZornVectorMatrix.add
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (X i j))
              (canonicalEquiv (Y j k)))
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (Y i j))
              (canonicalEquiv (X j k))))).b := by
  exact congrArg ZornVectorMatrix.b (canonicalEntry_jordanProduct X Y i k)

theorem canonicalEntry_jordanProduct_v (X Y : J3) (i k : Fin 3) :
    (canonicalEquiv (jordanProduct X Y i k)).v =
      (ZornVectorMatrix.smul (2 : ℝ)⁻¹
        (ZornVectorMatrix.add
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (X i j))
              (canonicalEquiv (Y j k)))
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (Y i j))
              (canonicalEquiv (X j k))))).v := by
  exact congrArg ZornVectorMatrix.v (canonicalEntry_jordanProduct X Y i k)

theorem canonicalEntry_jordanProduct_w (X Y : J3) (i k : Fin 3) :
    (canonicalEquiv (jordanProduct X Y i k)).w =
      (ZornVectorMatrix.smul (2 : ℝ)⁻¹
        (ZornVectorMatrix.add
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (X i j))
              (canonicalEquiv (Y j k)))
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (Y i j))
              (canonicalEquiv (X j k))))).w := by
  exact congrArg ZornVectorMatrix.w (canonicalEntry_jordanProduct X Y i k)

end InfoGeometry.Exceptional.FiniteJ3Zorn
