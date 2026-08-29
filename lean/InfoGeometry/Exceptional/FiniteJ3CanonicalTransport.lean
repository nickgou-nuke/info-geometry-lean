import InfoGeometry.Exceptional.FiniteJ3ZornCarrier
import InfoGeometry.Exceptional.ZornMatrixRealCanonicalBridge
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment

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

theorem hermitianToH3_finiteJordanProduct_α₁
    (X Y : HermitianJ3) :
    (hermitianToH3 (finiteJordanProduct X Y)).α₁ =
      (candidateJordanMul (hermitianToH3 X) (hermitianToH3 Y)).α₁ := by
  change (jordanProduct X.1 Y.1 0 0).a = _
  rw [jordanProduct_a, candidateJordanMul_trace_formula]
  rw [H3Zorn.linearTrace_crossProduct]
  rw [H3Zorn.smul_readback, H3Zorn.sub_readback, H3Zorn.add_readback]
  simp only [H3ZornCoordinateReadback.crossProduct_α₁,
    H3ZornCoordinateReadback.adjointQuad_α₁,
    H3ZornCoordinateReadback.linearTrace_coordinate,
    H3ZornCoordinateReadback.traceBilin_coordinate,
    H3ZornCoordinateReadback.add_α₁,
    H3ZornCoordinateReadback.add_α₂,
    H3ZornCoordinateReadback.add_α₃,
    H3ZornCoordinateReadback.smul_α₁,
    H3ZornCoordinateReadback.smul_α₂,
    H3ZornCoordinateReadback.smul_α₃,
    H3Zorn.add_readback, H3Zorn.smul_readback, H3Zorn.one_readback]
  simp [hermitianToH3, H3Zorn.linearTrace, H3Zorn.crossProduct,
    H3Zorn.adjointQuad, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.sub,
    ZornVectorMatrix.neg, ZornVec3.dot, ZornVec3.cross,
    Fin.sum_univ_three]
  ring

end InfoGeometry.Exceptional.FiniteJ3Zorn
