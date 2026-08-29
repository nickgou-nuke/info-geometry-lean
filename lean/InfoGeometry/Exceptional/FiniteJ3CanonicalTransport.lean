import InfoGeometry.Exceptional.FiniteJ3ZornCarrier
import InfoGeometry.Exceptional.ZornMatrixRealCanonicalBridge
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment
import InfoGeometry.Algebra.RealSplitOctSimp

namespace InfoGeometry.Exceptional.FiniteJ3Zorn

open InfoGeometry.Exceptional.RealZorn
open InfoGeometry.Algebra
open InfoGeometry.Algebra.RealSplitOctZornAlignment

def hermitianToH3 (X : HermitianJ3) : H3Zorn ℝ :=
  { α₁ := (X.1 0 0).a
    α₂ := (X.1 1 1).a
    α₃ := (X.1 2 2).a
    a := canonicalEquiv (X.1 0 1)
    b := canonicalEquiv (X.1 1 2)
    c := canonicalEquiv (X.1 2 0) }

def scalarZorn (r : ℝ) : ZornMatrixReal :=
  { a := r, b := r, u := (0, 0, 0), v := (0, 0, 0) }

def h3ToHermitian (Z : H3Zorn ℝ) : J3 := fun i j =>
  if i = 0 ∧ j = 0 then scalarZorn Z.α₁
  else if i = 1 ∧ j = 1 then scalarZorn Z.α₂
  else if i = 2 ∧ j = 2 then scalarZorn Z.α₃
  else if i = 0 ∧ j = 1 then canonicalEquiv.symm Z.a
  else if i = 1 ∧ j = 0 then zornConj (canonicalEquiv.symm Z.a)
  else if i = 1 ∧ j = 2 then canonicalEquiv.symm Z.b
  else if i = 2 ∧ j = 1 then zornConj (canonicalEquiv.symm Z.b)
  else if i = 2 ∧ j = 0 then canonicalEquiv.symm Z.c
  else zornConj (canonicalEquiv.symm Z.c)

theorem scalarZorn_conj (r : ℝ) :
    zornConj (scalarZorn r) = scalarZorn r := by
  apply ZornMatrixReal.ext <;> simp [scalarZorn, zornConj, smul]

theorem h3ToHermitian_hermitian (Z : H3Zorn ℝ) :
    hermitianStar (h3ToHermitian Z) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp_all [h3ToHermitian, scalarZorn, zornConj, smul,
      vecFromCanonical, zornConj_involutive]

def h3ToHermitianSubtype (Z : H3Zorn ℝ) : HermitianJ3 :=
  ⟨h3ToHermitian Z, h3ToHermitian_hermitian Z⟩

theorem hermitianToH3_h3ToHermitian (Z : H3Zorn ℝ) :
    hermitianToH3 (h3ToHermitianSubtype Z) = Z := by
  apply H3Zorn.ext_h3
  · rfl
  · rfl
  · rfl
  · exact canonicalEquiv.apply_symm_apply Z.a
  · exact canonicalEquiv.apply_symm_apply Z.b
  · exact canonicalEquiv.apply_symm_apply Z.c

theorem h3ToHermitian_hermitianToH3_00 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 0 0 = X.1 0 0 := by
  have h := hermitian_diagonal_scalar X 0
  apply ZornMatrixReal.ext
  · rfl
  · exact h.1
  · exact h.2.1.symm
  · exact h.2.2.symm

theorem h3ToHermitian_hermitianToH3_11 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 1 1 = X.1 1 1 := by
  have h := hermitian_diagonal_scalar X 1
  apply ZornMatrixReal.ext
  · rfl
  · exact h.1
  · exact h.2.1.symm
  · exact h.2.2.symm

theorem h3ToHermitian_hermitianToH3_22 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 2 2 = X.1 2 2 := by
  have h := hermitian_diagonal_scalar X 2
  apply ZornMatrixReal.ext
  · rfl
  · exact h.1
  · exact h.2.1.symm
  · exact h.2.2.symm

theorem h3ToHermitian_hermitianToH3_01 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 0 1 = X.1 0 1 := by
  change canonicalEquiv.symm (canonicalEquiv (X.1 0 1)) = X.1 0 1
  exact canonicalEquiv.symm_apply_apply (X.1 0 1)

theorem h3ToHermitian_hermitianToH3_10 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 1 0 = X.1 1 0 := by
  have h := congrArg zornConj (X.property 0 1)
  rw [zornConj_involutive] at h
  change zornConj (canonicalEquiv.symm (canonicalEquiv (X.1 0 1))) = X.1 1 0
  rw [canonicalEquiv.symm_apply_apply]
  exact h

theorem h3ToHermitian_hermitianToH3_12 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 1 2 = X.1 1 2 := by
  change canonicalEquiv.symm (canonicalEquiv (X.1 1 2)) = X.1 1 2
  exact canonicalEquiv.symm_apply_apply (X.1 1 2)

theorem h3ToHermitian_hermitianToH3_21 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 2 1 = X.1 2 1 := by
  have h := congrArg zornConj (X.property 1 2)
  rw [zornConj_involutive] at h
  change zornConj (canonicalEquiv.symm (canonicalEquiv (X.1 1 2))) = X.1 2 1
  rw [canonicalEquiv.symm_apply_apply]
  exact h

theorem h3ToHermitian_hermitianToH3_20 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 2 0 = X.1 2 0 := by
  change canonicalEquiv.symm (canonicalEquiv (X.1 2 0)) = X.1 2 0
  exact canonicalEquiv.symm_apply_apply (X.1 2 0)

theorem h3ToHermitian_hermitianToH3_02 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 0 2 = X.1 0 2 := by
  have h := congrArg zornConj (X.property 2 0)
  rw [zornConj_involutive] at h
  change zornConj (canonicalEquiv.symm (canonicalEquiv (X.1 2 0))) = X.1 0 2
  rw [canonicalEquiv.symm_apply_apply]
  exact h

theorem h3ToHermitian_hermitianToH3 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) = X.1 := by
  apply J3_ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h3ToHermitian_hermitianToH3_00 X
  · exact h3ToHermitian_hermitianToH3_01 X
  · exact h3ToHermitian_hermitianToH3_02 X
  · exact h3ToHermitian_hermitianToH3_10 X
  · exact h3ToHermitian_hermitianToH3_11 X
  · exact h3ToHermitian_hermitianToH3_12 X
  · exact h3ToHermitian_hermitianToH3_20 X
  · exact h3ToHermitian_hermitianToH3_21 X
  · exact h3ToHermitian_hermitianToH3_22 X

def hermitianH3Equiv : HermitianJ3 ≃ H3Zorn ℝ where
  toFun := hermitianToH3
  invFun := h3ToHermitianSubtype
  left_inv := by
    intro X
    exact Subtype.ext (h3ToHermitian_hermitianToH3 X)
  right_inv := hermitianToH3_h3ToHermitian

def hermitianRealAlbertEquiv : HermitianJ3 ≃ RealAlbertMatrix :=
  hermitianH3Equiv.trans
    InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.symm

theorem realAlbertEquiv_hermitianRealAlbertEquiv (X : HermitianJ3) :
    InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv
        (hermitianRealAlbertEquiv X) = hermitianToH3 X := by
  exact InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.apply_symm_apply
    (hermitianToH3 X)

theorem hermitianRealAlbertEquiv_z₁_readback (X : HermitianJ3) :
    (hermitianRealAlbertEquiv X).z₁ =
      (InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.symm
        (hermitianToH3 X)).z₁ := rfl

theorem hermitianToH3_b (X : HermitianJ3) :
    (hermitianToH3 X).b = canonicalEquiv (X.1 1 2) := rfl

theorem hermitianRealAlbertEquiv_z₂_readback (X : HermitianJ3) :
    (hermitianRealAlbertEquiv X).z₂ =
      (InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.symm
        (hermitianToH3 X)).z₂ := rfl

theorem hermitianToH3_c (X : HermitianJ3) :
    (hermitianToH3 X).c = canonicalEquiv (X.1 2 0) := rfl

theorem hermitianRealAlbertEquiv_z₃_readback (X : HermitianJ3) :
    (hermitianRealAlbertEquiv X).z₃ =
      (InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.symm
        (hermitianToH3 X)).z₃ := rfl

theorem hermitianToH3_a (X : HermitianJ3) :
    (hermitianToH3 X).a = canonicalEquiv (X.1 0 1) := rfl

@[simp] theorem hermitianRealAlbertEquiv_alpha₁ (X : HermitianJ3) :
    (hermitianRealAlbertEquiv X).α₁ = (X.1 0 0).a := rfl

@[simp] theorem hermitianRealAlbertEquiv_alpha₂ (X : HermitianJ3) :
    (hermitianRealAlbertEquiv X).α₂ = (X.1 1 1).a := rfl

@[simp] theorem hermitianRealAlbertEquiv_alpha₃ (X : HermitianJ3) :
    (hermitianRealAlbertEquiv X).α₃ = (X.1 2 2).a := rfl

theorem hermitianRealAlbertEquiv_z₁ (X : HermitianJ3) :
    (hermitianRealAlbertEquiv X).z₁ =
      InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (X.1 1 2)) := by
  rfl

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁ =
      InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 1 2)) := by
  rfl

theorem hermitianRealAlbertEquiv_z₂ (X : HermitianJ3) :
    (hermitianRealAlbertEquiv X).z₂ =
      InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (X.1 2 0)) := by
  rfl

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₂
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₂ =
      InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 2 0)) := by
  rfl

theorem hermitianRealAlbertEquiv_z₃ (X : HermitianJ3) :
    (hermitianRealAlbertEquiv X).z₃ =
      InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (X.1 0 1)) := by
  rfl

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₃
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₃ =
      InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 0 1)) := by
  rfl

theorem hermitianRealAlbertEquiv_finiteJordanProduct_alpha₁
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).α₁ =
      (j3RawMul X.1 Y.1 0 0).a / 2 +
        (j3RawMul Y.1 X.1 0 0).a / 2 := by
  rw [hermitianRealAlbertEquiv_alpha₁]
  change (jordanProduct X.1 Y.1 0 0).a = _
  exact jordanProduct_a X.1 Y.1 0 0

theorem hermitianRealAlbertEquiv_finiteJordanProduct_alpha₂
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).α₂ =
      (j3RawMul X.1 Y.1 1 1).a / 2 +
        (j3RawMul Y.1 X.1 1 1).a / 2 := by
  rw [hermitianRealAlbertEquiv_alpha₂]
  change (jordanProduct X.1 Y.1 1 1).a = _
  exact jordanProduct_a X.1 Y.1 1 1

theorem hermitianRealAlbertEquiv_finiteJordanProduct_alpha₃
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).α₃ =
      (j3RawMul X.1 Y.1 2 2).a / 2 +
        (j3RawMul Y.1 X.1 2 2).a / 2 := by
  rw [hermitianRealAlbertEquiv_alpha₃]
  change (jordanProduct X.1 Y.1 2 2).a = _
  exact jordanProduct_a X.1 Y.1 2 2


theorem hermitianRealAlbertEquiv_finiteJordanProduct_h3_b
    (X Y : HermitianJ3) :
    (InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv
      (hermitianRealAlbertEquiv (finiteJordanProduct X Y))).b =
        canonicalEquiv (jordanProduct X.1 Y.1 1 2) := by
  rw [realAlbertEquiv_hermitianRealAlbertEquiv]
  rfl

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

theorem canonicalEntry_j3RawMul_a (X Y : J3) (i k : Fin 3) :
    (canonicalEquiv (j3RawMul X Y i k)).a =
      (∑ j : Fin 3,
        ZornVectorMatrix.mul (canonicalEquiv (X i j))
          (canonicalEquiv (Y j k))).a := by
  exact congrArg ZornVectorMatrix.a (canonicalEntry_j3RawMul X Y i k)

theorem hermitianToH3_finiteJordanProduct_α₁_canonical
    (X Y : HermitianJ3) :
    (hermitianToH3 (finiteJordanProduct X Y)).α₁ =
      (canonicalEquiv (jordanProduct X.1 Y.1 0 0)).a := by
  rfl

theorem hermitianToH3_finiteJordanProduct_α₁_sum
    (X Y : HermitianJ3) :
    (hermitianToH3 (finiteJordanProduct X Y)).α₁ =
      (ZornVectorMatrix.smul (2 : ℝ)⁻¹
        (ZornVectorMatrix.add
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (X.1 0 j))
              (canonicalEquiv (Y.1 j 0)))
          (∑ j : Fin 3,
            ZornVectorMatrix.mul (canonicalEquiv (Y.1 0 j))
              (canonicalEquiv (X.1 j 0))))).a := by
  calc
    (hermitianToH3 (finiteJordanProduct X Y)).α₁ =
        (canonicalEquiv (jordanProduct X.1 Y.1 0 0)).a :=
      hermitianToH3_finiteJordanProduct_α₁_canonical X Y
    _ = _ := canonicalEntry_jordanProduct_a X.1 Y.1 0 0

theorem realConj_eq_zornConj (A : ZornMatrixReal) :
    realConj A = zornConj A := by
  rfl

theorem canonicalEquiv_zornConj (A : ZornMatrixReal) :
    canonicalEquiv (zornConj A) =
      ZornVectorMatrix.conj (canonicalEquiv A) := by
  rw [← realConj_eq_zornConj A]
  exact canonicalEquiv_conj A

theorem canonicalEquiv_mul_a (A B : ZornMatrixReal) :
    (canonicalEquiv (A * B)).a =
      (canonicalEquiv A).a * (canonicalEquiv B).a +
        ZornVec3.dot (canonicalEquiv A).v (canonicalEquiv B).w := by
  rw [canonicalEquiv_mul]
  rfl

theorem canonicalMul_a (A B : ZornVectorMatrix ℝ) :
    (ZornVectorMatrix.mul A B).a = A.a * B.a + ZornVec3.dot A.v B.w := by
  rfl

theorem canonicalEquiv_mul_v (A B : ZornMatrixReal) (i : Fin 3) :
    (canonicalEquiv (A * B)).v i =
      (canonicalEquiv A).a * (canonicalEquiv B).v i +
        (canonicalEquiv B).b * (canonicalEquiv A).v i -
          ZornVec3.cross (canonicalEquiv A).w (canonicalEquiv B).w i := by
  rw [canonicalEquiv_mul]
  rfl

theorem canonicalEquiv_mul_w (A B : ZornMatrixReal) (i : Fin 3) :
    (canonicalEquiv (A * B)).w i =
      (canonicalEquiv B).a * (canonicalEquiv A).w i +
        (canonicalEquiv A).b * (canonicalEquiv B).w i +
          ZornVec3.cross (canonicalEquiv A).v (canonicalEquiv B).v i := by
  rw [canonicalEquiv_mul]
  rfl

theorem canonicalEquiv_mul_b (A B : ZornMatrixReal) :
    (canonicalEquiv (A * B)).b =
      ZornVec3.dot (canonicalEquiv A).w (canonicalEquiv B).v +
        (canonicalEquiv A).b * (canonicalEquiv B).b := by
  rw [canonicalEquiv_mul]
  rfl

/-! Finite matrix multiplication uses a three-term sum. -/
theorem fromZorn_sum_fin3 (f : Fin 3 → ZornVectorMatrix ℝ) :
    InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn (∑ i, f i) =
      ∑ i, InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn (f i) := by
  rw [Fin.sum_univ_three]
  rw [fromZorn_add, fromZorn_add]
  rw [Fin.sum_univ_three]

theorem fromZorn_jordanProduct_entry (X Y : J3) (i k : Fin 3) :
    InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X Y i k)) =
      (2 : ℝ)⁻¹ •
        (∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X i j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y i j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X j k)))) := by
  rw [canonicalEntry_jordanProduct]
  change fromZorn ((2 : ℝ)⁻¹ •
      ((∑ j : Fin 3, ZornVectorMatrix.mul (canonicalEquiv (X i j))
          (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3, ZornVectorMatrix.mul (canonicalEquiv (Y i j))
          (canonicalEquiv (X j k)))) = _
  rw [fromZorn_smul, fromZorn_add, fromZorn_sum_fin3, fromZorn_sum_fin3]
  simp_rw [InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn_mul]

theorem fromZorn_jordanProduct_entry_a (X Y : J3) (i k : Fin 3) :
    (fromZorn (canonicalEquiv (jordanProduct X Y i k))).a =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3,
          RealSplitOct.mul
            (fromZorn (canonicalEquiv (X i j)))
            (fromZorn (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3,
          RealSplitOct.mul
            (fromZorn (canonicalEquiv (Y i j)))
            (fromZorn (canonicalEquiv (X j k))))).a := by
  exact congrArg RealSplitOct.a (fromZorn_jordanProduct_entry X Y i k)

theorem canonicalEquiv_v_fst (A : ZornMatrixReal) :
    (canonicalEquiv A).v 0 = A.u.1 := by
  rfl

theorem canonicalEquiv_v_snd_fst (A : ZornMatrixReal) :
    (canonicalEquiv A).v 1 = A.u.2.1 := by
  rfl

theorem canonicalEquiv_v_snd_snd (A : ZornMatrixReal) :
    (canonicalEquiv A).v 2 = A.u.2.2 := by
  rfl

theorem hermitian_entry_a_eq_b (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).a = (X.1 j i).b := by
  have h := congrArg ZornMatrixReal.a (X.property i j)
  simpa [zornConj] using h

theorem hermitian_entry_b_eq_a (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).b = (X.1 j i).a := by
  have h := congrArg ZornMatrixReal.b (X.property i j)
  simpa [zornConj] using h

theorem hermitian_entry_u_eq_neg_u (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).u = smul (-1) (X.1 j i).u := by
  have h := congrArg ZornMatrixReal.u (X.property i j)
  simpa [zornConj] using h

theorem hermitian_entry_v_eq_neg_v (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).v = smul (-1) (X.1 j i).v := by
  have h := congrArg ZornMatrixReal.v (X.property i j)
  simpa [zornConj] using h

theorem hermitian_entry_u_fst (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).u.1 = - (X.1 j i).u.1 := by
  have h := hermitian_entry_u_eq_neg_u X i j
  simpa [smul] using congrArg Prod.fst h

theorem hermitian_entry_u_snd_fst (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).u.2.1 = - (X.1 j i).u.2.1 := by
  have h := hermitian_entry_u_eq_neg_u X i j
  simpa [smul] using congrArg (fun q => q.2.1) h

theorem hermitian_entry_u_snd_snd (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).u.2.2 = - (X.1 j i).u.2.2 := by
  have h := hermitian_entry_u_eq_neg_u X i j
  simpa [smul] using congrArg (fun q => q.2.2) h

theorem hermitian_entry_v_fst (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).v.1 = - (X.1 j i).v.1 := by
  have h := hermitian_entry_v_eq_neg_v X i j
  simpa [smul] using congrArg Prod.fst h

theorem hermitian_entry_v_snd_fst (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).v.2.1 = - (X.1 j i).v.2.1 := by
  have h := hermitian_entry_v_eq_neg_v X i j
  simpa [smul] using congrArg (fun q => q.2.1) h

theorem hermitian_entry_v_snd_snd (X : HermitianJ3) (i j : Fin 3) :
    (X.1 i j).v.2.2 = - (X.1 j i).v.2.2 := by
  have h := hermitian_entry_v_eq_neg_v X i j
  simpa [smul] using congrArg (fun q => q.2.2) h

theorem realZorn_dot_smul_neg_left (u v : Vec3Real) :
    dot (smul (-1) u) v = - dot u v := by
  dsimp [dot, smul]
  ring

theorem realZorn_dot_smul_neg_right (u v : Vec3Real) :
    dot u (smul (-1) v) = - dot u v := by
  dsimp [dot, smul]
  ring

theorem realZorn_dot_smul_neg_both (u v : Vec3Real) :
    dot (smul (-1) u) (smul (-1) v) = dot u v := by
  dsimp [dot, smul]
  ring

theorem vecToCanonical_dot (u v : Vec3Real) :
    ZornVec3.dot (vecToCanonical u) (vecToCanonical v) = dot u v := by
  simp [ZornVec3.dot, dot, vecToCanonical, Fin.sum_univ_three]

theorem vecToCanonical_smul (r : ℝ) (u : Vec3Real) :
    vecToCanonical (smul r u) = (fun i => r * vecToCanonical u i) := by
  funext i
  fin_cases i <;> rfl

theorem vecToCanonical_neg (u : Vec3Real) :
    vecToCanonical (smul (-1) u) = (fun i => - vecToCanonical u i) := by
  simpa using vecToCanonical_smul (-1 : ℝ) u

theorem vecToCanonical_add (u v : Vec3Real) :
    vecToCanonical (add u v) =
      (fun i => vecToCanonical u i + vecToCanonical v i) := by
  funext i
  fin_cases i <;> rfl

theorem canonicalHermitianEntry (X : HermitianJ3) (i j : Fin 3) :
    canonicalEquiv (X.1 j i) =
      ZornVectorMatrix.conj (canonicalEquiv (X.1 i j)) := by
  rw [← canonicalEquiv_conj (X.1 i j)]
  congr 1
  rw [realConj_eq_zornConj]
  exact X.property j i

theorem canonicalHermitianEntry_a (X : HermitianJ3) (i j : Fin 3) :
    (canonicalEquiv (X.1 j i)).a =
      (ZornVectorMatrix.conj (canonicalEquiv (X.1 i j))).a := by
  exact congrArg ZornVectorMatrix.a (canonicalHermitianEntry X i j)

theorem canonicalHermitianEntry_b (X : HermitianJ3) (i j : Fin 3) :
    (canonicalEquiv (X.1 j i)).b =
      (ZornVectorMatrix.conj (canonicalEquiv (X.1 i j))).b := by
  exact congrArg ZornVectorMatrix.b (canonicalHermitianEntry X i j)

theorem canonicalHermitianEntry_v (X : HermitianJ3) (i j : Fin 3) :
    (canonicalEquiv (X.1 j i)).v =
      (ZornVectorMatrix.conj (canonicalEquiv (X.1 i j))).v := by
  exact congrArg ZornVectorMatrix.v (canonicalHermitianEntry X i j)

theorem canonicalHermitianEntry_w (X : HermitianJ3) (i j : Fin 3) :
    (canonicalEquiv (X.1 j i)).w =
      (ZornVectorMatrix.conj (canonicalEquiv (X.1 i j))).w := by
  exact congrArg ZornVectorMatrix.w (canonicalHermitianEntry X i j)

end InfoGeometry.Exceptional.FiniteJ3Zorn
