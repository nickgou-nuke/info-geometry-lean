import InfoGeometry.Exceptional.FiniteJ3ZornCarrier
import InfoGeometry.Exceptional.ZornMatrixRealCanonicalBridge
import InfoGeometry.Algebra.QuadraticJordanH3Zorn

namespace InfoGeometry.Exceptional.FiniteJ3Zorn

open InfoGeometry.Exceptional.RealZorn
open InfoGeometry.Algebra

def hermitianToH3 (X : HermitianJ3) : H3Zorn ℝ :=
  { α₁ := (X.1 0 0).a
    α₂ := (X.1 1 1).a
    α₃ := (X.1 2 2).a
    a := canonicalEquiv (X.1 0 1)
    b := canonicalEquiv (X.1 1 2)
    c := canonicalEquiv (X.1 2 0) }

@[simp] theorem hermitianToH3_alpha₁ (X : HermitianJ3) :
    (hermitianToH3 X).α₁ = (X.1 0 0).a := rfl

@[simp] theorem hermitianToH3_alpha₂ (X : HermitianJ3) :
    (hermitianToH3 X).α₂ = (X.1 1 1).a := rfl

@[simp] theorem hermitianToH3_alpha₃ (X : HermitianJ3) :
    (hermitianToH3 X).α₃ = (X.1 2 2).a := rfl

@[simp] theorem hermitianToH3_a (X : HermitianJ3) :
    (hermitianToH3 X).a = canonicalEquiv (X.1 0 1) := rfl

@[simp] theorem hermitianToH3_b (X : HermitianJ3) :
    (hermitianToH3 X).b = canonicalEquiv (X.1 1 2) := rfl

@[simp] theorem hermitianToH3_c (X : HermitianJ3) :
    (hermitianToH3 X).c = canonicalEquiv (X.1 2 0) := rfl

theorem canonicalEquiv_zornHalf (X : ZornMatrixReal) :
    canonicalEquiv (zornHalf X) =
      ZornVectorMatrix.smul (2 : ℝ)⁻¹ (canonicalEquiv X) := by
  apply ZornVectorMatrix.ext
  · simp [canonicalEquiv, toCanonical, vecToCanonical, zornHalf,
      ZornVectorMatrix.smul, RealZorn.smul]
    ring
  · funext k
    fin_cases k <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical, zornHalf,
        ZornVectorMatrix.smul, RealZorn.smul]
  · funext k
    fin_cases k <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical, zornHalf,
        ZornVectorMatrix.smul, RealZorn.smul]
  · simp [canonicalEquiv, toCanonical, vecToCanonical, zornHalf,
      ZornVectorMatrix.smul, RealZorn.smul]
    ring

def canonicalEntry (X : J3) : Fin 3 → Fin 3 → ZornVectorMatrix ℝ :=
  fun i j => canonicalEquiv (X i j)

theorem canonicalEntry_zornHalf (X : J3) (i j : Fin 3) :
    canonicalEquiv (zornHalf (X i j)) =
      ZornVectorMatrix.smul (2 : ℝ)⁻¹ (canonicalEntry X i j) := by
  apply ZornVectorMatrix.ext
  · simp [canonicalEquiv, canonicalEntry, toCanonical, vecToCanonical,
      zornHalf, ZornVectorMatrix.smul, RealZorn.smul]
    ring
  · funext k
    fin_cases k <;>
      simp [canonicalEquiv, canonicalEntry, toCanonical, vecToCanonical,
        zornHalf, ZornVectorMatrix.smul, RealZorn.smul]
  · funext k
    fin_cases k <;>
      simp [canonicalEquiv, canonicalEntry, toCanonical, vecToCanonical,
        zornHalf, ZornVectorMatrix.smul, RealZorn.smul]
  · simp [canonicalEquiv, canonicalEntry, toCanonical, vecToCanonical,
      zornHalf, ZornVectorMatrix.smul, RealZorn.smul]
    ring

@[simp] theorem canonicalEntry_apply (X : J3) (i j : Fin 3) :
    canonicalEntry X i j = canonicalEquiv (X i j) := rfl

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

theorem canonicalEntry_j3RawMul (X Y : J3) (i k : Fin 3) :
    canonicalEquiv (j3RawMul X Y i k) =
      ∑ j : Fin 3,
        ZornVectorMatrix.mul (canonicalEquiv (X i j))
          (canonicalEquiv (Y j k)) := by
  simp only [j3RawMul]
  rw [canonicalEquiv_add, canonicalEquiv_add]
  rw [canonicalEquiv_mul, canonicalEquiv_mul, canonicalEquiv_mul]
  simp [Fin.sum_univ_three, ZornVectorMatrix.add_assoc]

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
  unfold jordanProduct
  rw [canonicalEquiv_zornHalf, canonicalEquiv_add,
    canonicalEntry_j3RawMul,
    canonicalEntry_j3RawMul]

end InfoGeometry.Exceptional.FiniteJ3Zorn
