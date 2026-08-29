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

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₀_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.x0 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 1 2))).x0 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₁_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.x1 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 1 2))).x1 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₂_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.x2 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 1 2))).x2 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_y₀_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.y0 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 1 2))).y0 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_y₁_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.y1 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 1 2))).y1 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_y₂_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.y2 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 1 2))).y2 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁]

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

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₂_x₀_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₂.x0 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 2 0))).x0 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₂]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₂_x₁_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₂.x1 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 2 0))).x1 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₂]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₂_x₂_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₂.x2 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 2 0))).x2 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₂]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₂_y₀_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₂.y0 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 2 0))).y0 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₂]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₂_y₁_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₂.y1 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 2 0))).y1 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₂]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₂_y₂_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₂.y2 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 2 0))).y2 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₂]

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

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₃_x₀_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₃.x0 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 0 1))).x0 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₃]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₃_x₁_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₃.x1 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 0 1))).x1 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₃]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₃_x₂_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₃.x2 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 0 1))).x2 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₃]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₃_y₀_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₃.y0 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 0 1))).y0 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₃]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₃_y₁_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₃.y1 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 0 1))).y1 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₃]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₃_y₂_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₃.y2 =
      (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
        (canonicalEquiv (jordanProduct X.1 Y.1 0 1))).y2 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₃]

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

theorem fromZorn_jordanProduct_entry_b (X Y : J3) (i k : Fin 3) :
    (fromZorn (canonicalEquiv (jordanProduct X Y i k))).b =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3,
          RealSplitOct.mul
            (fromZorn (canonicalEquiv (X i j)))
            (fromZorn (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3,
          RealSplitOct.mul
            (fromZorn (canonicalEquiv (Y i j)))
            (fromZorn (canonicalEquiv (X j k))))).b := by
  exact congrArg RealSplitOct.b (fromZorn_jordanProduct_entry X Y i k)

theorem fromZorn_jordanProduct_entry_x0 (X Y : J3) (i k : Fin 3) :
    (fromZorn (canonicalEquiv (jordanProduct X Y i k))).x0 =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3,
          RealSplitOct.mul
            (fromZorn (canonicalEquiv (X i j)))
            (fromZorn (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3,
          RealSplitOct.mul
            (fromZorn (canonicalEquiv (Y i j)))
            (fromZorn (canonicalEquiv (X j k))))).x0 := by
  exact congrArg RealSplitOct.x0 (fromZorn_jordanProduct_entry X Y i k)

theorem realSplitOct_sum_mul_x0 (f g : Fin 3 → RealSplitOct) :
    (∑ j : Fin 3, RealSplitOct.mul (f j) (g j)).x0 =
      ∑ j : Fin 3,
        ((f j).a * (g j).x0 + (g j).b * (f j).x0 -
          ((f j).y1 * (g j).y2 - (f j).y2 * (g j).y1)) := by
  simp [RealSplitOct.mul, Fin.sum_univ_three]
  ring

theorem realSplitOct_sum_mul_x1 (f g : Fin 3 → RealSplitOct) :
    (∑ j : Fin 3, RealSplitOct.mul (f j) (g j)).x1 =
      ∑ j : Fin 3,
        ((f j).a * (g j).x1 + (g j).b * (f j).x1 -
          ((f j).y2 * (g j).y0 - (f j).y0 * (g j).y2)) := by
  simp [RealSplitOct.mul, Fin.sum_univ_three]
  ring

theorem realSplitOct_sum_mul_x2 (f g : Fin 3 → RealSplitOct) :
    (∑ j : Fin 3, RealSplitOct.mul (f j) (g j)).x2 =
      ∑ j : Fin 3,
        ((f j).a * (g j).x2 + (g j).b * (f j).x2 -
          ((f j).y0 * (g j).y1 - (f j).y1 * (g j).y0)) := by
  simp [RealSplitOct.mul, Fin.sum_univ_three]
  ring

theorem realSplitOct_sum_mul_y0 (f g : Fin 3 → RealSplitOct) :
    (∑ j : Fin 3, RealSplitOct.mul (f j) (g j)).y0 =
      ∑ j : Fin 3,
        ((g j).a * (f j).y0 + (f j).b * (g j).y0 +
          ((f j).x1 * (g j).x2 - (f j).x2 * (g j).x1)) := by
  simp [RealSplitOct.mul, Fin.sum_univ_three]

theorem realSplitOct_sum_mul_y1 (f g : Fin 3 → RealSplitOct) :
    (∑ j : Fin 3, RealSplitOct.mul (f j) (g j)).y1 =
      ∑ j : Fin 3,
        ((g j).a * (f j).y1 + (f j).b * (g j).y1 +
          ((f j).x2 * (g j).x0 - (f j).x0 * (g j).x2)) := by
  simp [RealSplitOct.mul, Fin.sum_univ_three]

theorem realSplitOct_sum_mul_y2 (f g : Fin 3 → RealSplitOct) :
    (∑ j : Fin 3, RealSplitOct.mul (f j) (g j)).y2 =
      ∑ j : Fin 3,
        ((g j).a * (f j).y2 + (f j).b * (g j).y2 +
          ((f j).x0 * (g j).x1 - (f j).x1 * (g j).x0)) := by
  simp [RealSplitOct.mul, Fin.sum_univ_three]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₀_sum_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.x0 =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 1 j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 j 2))) +
        ∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 1 j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 j 2))))).x0 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁]
  rw [fromZorn_jordanProduct_entry_x0]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₀_explicit
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.x0 =
      (2 : ℝ)⁻¹ *
        (∑ j : Fin 3,
          ((InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 1 j))).a *
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (Y.1 j 2))).x0 +
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 j 2))).b *
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (X.1 1 j))).x0 -
            ((InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (X.1 1 j))).y1 *
                (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                  (canonicalEquiv (Y.1 j 2))).y2 -
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (X.1 1 j))).y2 *
                (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                  (canonicalEquiv (Y.1 j 2))).y1)) +
        ∑ j : Fin 3,
          ((InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 1 j))).a *
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (X.1 j 2))).x0 +
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 j 2))).b *
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (Y.1 1 j))).x0 -
            ((InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (Y.1 1 j))).y1 *
                (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                  (canonicalEquiv (X.1 j 2))).y2 -
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (Y.1 1 j))).y2 *
                (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                  (canonicalEquiv (X.1 j 2))).y1))) := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₀_sum_readback]
  simp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul,
    Fin.sum_univ_three]
  ring

theorem fromZorn_jordanProduct_entry_x1 (X Y : J3) (i k : Fin 3) :
    (fromZorn (canonicalEquiv (jordanProduct X Y i k))).x1 =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (X i j)))
          (fromZorn (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (Y i j)))
          (fromZorn (canonicalEquiv (X j k))))).x1 := by
  exact congrArg RealSplitOct.x1 (fromZorn_jordanProduct_entry X Y i k)

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₁_sum_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.x1 =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 1 j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 j 2))) +
        ∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 1 j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 j 2))))).x1 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁]
  rw [fromZorn_jordanProduct_entry_x1]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₁_explicit
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.x1 =
      (2 : ℝ)⁻¹ *
        (∑ j : Fin 3,
          ((InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 1 j))).a *
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (Y.1 j 2))).x1 +
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 j 2))).b *
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (X.1 1 j))).x1 -
            ((InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (X.1 1 j))).y2 *
                (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                  (canonicalEquiv (Y.1 j 2))).y0 -
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (X.1 1 j))).y0 *
                (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                  (canonicalEquiv (Y.1 j 2))).y2)) +
        ∑ j : Fin 3,
          ((InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 1 j))).a *
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (X.1 j 2))).x1 +
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 j 2))).b *
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (Y.1 1 j))).x1 -
            ((InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (Y.1 1 j))).y2 *
                (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                  (canonicalEquiv (X.1 j 2))).y0 -
              (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                (canonicalEquiv (Y.1 1 j))).y0 *
                (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
                  (canonicalEquiv (X.1 j 2))).y2))) := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₁_sum_readback]
  simp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul,
    Fin.sum_univ_three]
  ring

theorem fromZorn_jordanProduct_entry_x2 (X Y : J3) (i k : Fin 3) :
    (fromZorn (canonicalEquiv (jordanProduct X Y i k))).x2 =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (X i j)))
          (fromZorn (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (Y i j)))
          (fromZorn (canonicalEquiv (X j k))))).x2 := by
  exact congrArg RealSplitOct.x2 (fromZorn_jordanProduct_entry X Y i k)

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₂_sum_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.x2 =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 1 j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 j 2))) +
        ∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 1 j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 j 2))))).x2 := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁]
  rw [fromZorn_jordanProduct_entry_x2]

theorem hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₂_scalar_readback
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).z₁.x2 =
      (2 : ℝ)⁻¹ *
        ((∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 1 j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 j 2)))).x2 +
        (∑ j : Fin 3,
          RealSplitOct.mul
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (Y.1 1 j)))
            (InfoGeometry.Algebra.RealSplitOctZornAlignment.fromZorn
              (canonicalEquiv (X.1 j 2)))).x2) := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_z₁_x₂_sum_readback]
  simp [RealSplitOct.smul, RealSplitOct.add]
  ring

theorem fromZorn_jordanProduct_entry_y0 (X Y : J3) (i k : Fin 3) :
    (fromZorn (canonicalEquiv (jordanProduct X Y i k))).y0 =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (X i j)))
          (fromZorn (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (Y i j)))
          (fromZorn (canonicalEquiv (X j k))))).y0 := by
  exact congrArg RealSplitOct.y0 (fromZorn_jordanProduct_entry X Y i k)

theorem fromZorn_jordanProduct_entry_y1 (X Y : J3) (i k : Fin 3) :
    (fromZorn (canonicalEquiv (jordanProduct X Y i k))).y1 =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (X i j)))
          (fromZorn (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (Y i j)))
          (fromZorn (canonicalEquiv (X j k))))).y1 := by
  exact congrArg RealSplitOct.y1 (fromZorn_jordanProduct_entry X Y i k)

theorem fromZorn_jordanProduct_entry_y2 (X Y : J3) (i k : Fin 3) :
    (fromZorn (canonicalEquiv (jordanProduct X Y i k))).y2 =
      ((2 : ℝ)⁻¹ •
        (∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (X i j)))
          (fromZorn (canonicalEquiv (Y j k))) +
        ∑ j : Fin 3, RealSplitOct.mul
          (fromZorn (canonicalEquiv (Y i j)))
          (fromZorn (canonicalEquiv (X j k))))).y2 := by
  exact congrArg RealSplitOct.y2 (fromZorn_jordanProduct_entry X Y i k)

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

theorem hermitianEntry_conj_reverse (X : HermitianJ3) (i j : Fin 3) :
    zornConj (X.1 i j) = X.1 j i := by
  exact (X.property j i).symm

theorem hermitian_diagonal_u_zero (X : HermitianJ3) (i : Fin 3) :
    (X.1 i i).u = (0, 0, 0) := by
  have h := hermitian_entry_u_eq_neg_u X i i
  apply Prod.ext
  · apply InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _ |>.mp
    simpa [smul] using (congrArg Prod.fst h).symm
  · apply Prod.ext
    · apply InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _ |>.mp
      simpa [smul] using (congrArg (fun q : Vec3Real => q.2.1) h).symm
    · apply InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _ |>.mp
      simpa [smul] using (congrArg (fun q : Vec3Real => q.2.2) h).symm

theorem hermitian_diagonal_v_zero (X : HermitianJ3) (i : Fin 3) :
    (X.1 i i).v = (0, 0, 0) := by
  have h := hermitian_entry_v_eq_neg_v X i i
  apply Prod.ext
  · apply InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _ |>.mp
    simpa [smul] using (congrArg Prod.fst h).symm
  · apply Prod.ext
    · apply InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _ |>.mp
      simpa [smul] using (congrArg (fun q : Vec3Real => q.2.1) h).symm
    · apply InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _ |>.mp
      simpa [smul] using (congrArg (fun q : Vec3Real => q.2.2) h).symm

theorem hermitianRealAlbertEquiv_finiteJordanProduct_mul_α₁
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).α₁ =
      (RealAlbertMatrix.mul (hermitianRealAlbertEquiv X)
        (hermitianRealAlbertEquiv Y)).α₁ := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_alpha₁]
  have hY10 : Y.1 1 0 = zornConj (Y.1 0 1) := Y.property 1 0
  have hX20 : X.1 2 0 = zornConj (X.1 0 2) := X.property 2 0
  have hX10 : X.1 1 0 = zornConj (X.1 0 1) := X.property 1 0
  have hY20 : Y.1 2 0 = zornConj (Y.1 0 2) := Y.property 2 0
  have hX00 := hermitian_diagonal_scalar X 0
  have hY00 := hermitian_diagonal_scalar Y 0
  have hX11 := hermitian_diagonal_scalar X 1
  have hY11 := hermitian_diagonal_scalar Y 1
  have hX22 := hermitian_diagonal_scalar X 2
  have hY22 := hermitian_diagonal_scalar Y 2
  simp [j3RawMul, hY10, hX20, hX00, hY00, hX11, hY11, hX22, hY22,
    RealAlbertMatrix.mul, hermitianRealAlbertEquiv,
    hermitianH3Equiv, RealAlbertH3ZornCarrierAlignment.equiv,
    RealAlbertH3ZornCarrierAlignment.fromH3,
    RealAlbertH3ZornCarrierAlignment.toH3, hermitianToH3,
    canonicalEquiv, toCanonical, fromCanonical,
    RealSplitOctZornAlignment.fromZorn, RealSplitOctZornAlignment.toZorn,
    RealSplitOct.conj, RealSplitOct.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
  simp only [hY10, hX20, hX10, hY20]
  simp [zornConj, smul, vecToCanonical, dot]
  ring

theorem hermitianRealAlbertEquiv_finiteJordanProduct_mul_α₂
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).α₂ =
      (RealAlbertMatrix.mul (hermitianRealAlbertEquiv X)
        (hermitianRealAlbertEquiv Y)).α₂ := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_alpha₂]
  have hX01 : X.1 0 1 = zornConj (X.1 1 0) := X.property 0 1
  have hY01 : Y.1 0 1 = zornConj (Y.1 1 0) := Y.property 0 1
  have hX21 : X.1 2 1 = zornConj (X.1 1 2) := X.property 2 1
  have hY21 : Y.1 2 1 = zornConj (Y.1 1 2) := Y.property 2 1
  have hX00 := hermitian_diagonal_scalar X 0
  have hY00 := hermitian_diagonal_scalar Y 0
  have hX11 := hermitian_diagonal_scalar X 1
  have hY11 := hermitian_diagonal_scalar Y 1
  have hX22 := hermitian_diagonal_scalar X 2
  have hY22 := hermitian_diagonal_scalar Y 2
  simp [j3RawMul, hX01, hY01, hX21, hY21, hX00, hY00, hX11, hY11,
    hX22, hY22, RealAlbertMatrix.mul, hermitianRealAlbertEquiv,
    hermitianH3Equiv, RealAlbertH3ZornCarrierAlignment.equiv,
    RealAlbertH3ZornCarrierAlignment.fromH3,
    RealAlbertH3ZornCarrierAlignment.toH3, hermitianToH3,
    canonicalEquiv, toCanonical, fromCanonical,
    RealSplitOctZornAlignment.fromZorn, RealSplitOctZornAlignment.toZorn,
    RealSplitOct.conj, RealSplitOct.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
  try simp only [hX01, hY01, hX21, hY21]
  simp [zornConj, smul, vecToCanonical, dot] <;> ring

theorem hermitianRealAlbertEquiv_finiteJordanProduct_mul_α₃
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv (finiteJordanProduct X Y)).α₃ =
      (RealAlbertMatrix.mul (hermitianRealAlbertEquiv X)
        (hermitianRealAlbertEquiv Y)).α₃ := by
  rw [hermitianRealAlbertEquiv_finiteJordanProduct_alpha₃]
  change _ = _
  simp only [RealAlbertMatrix.mul, hermitianRealAlbertEquiv,
    hermitianH3Equiv, RealAlbertH3ZornCarrierAlignment.equiv,
    RealAlbertH3ZornCarrierAlignment.fromH3,
    RealAlbertH3ZornCarrierAlignment.toH3, hermitianToH3,
    canonicalEquiv, toCanonical, fromCanonical,
    RealSplitOctZornAlignment.fromZorn, RealSplitOctZornAlignment.toZorn,
    RealSplitOct.conj, RealSplitOct.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
  have hX02 : X.1 0 2 = zornConj (X.1 2 0) := X.property 0 2
  have hY02 : Y.1 0 2 = zornConj (Y.1 2 0) := Y.property 0 2
  have hX12 : X.1 1 2 = zornConj (X.1 2 1) := X.property 1 2
  have hY12 : Y.1 1 2 = zornConj (Y.1 2 1) := Y.property 1 2
  have hX00 := hermitian_diagonal_scalar X 0
  have hY00 := hermitian_diagonal_scalar Y 0
  have hX11 := hermitian_diagonal_scalar X 1
  have hY11 := hermitian_diagonal_scalar Y 1
  have hX22 := hermitian_diagonal_scalar X 2
  have hY22 := hermitian_diagonal_scalar Y 2
  simp [j3RawMul, hX02, hY02, hX12, hY12, hX00, hY00, hX11, hY11,
    hX22, hY22, RealAlbertMatrix.mul, hermitianRealAlbertEquiv,
    hermitianH3Equiv, RealAlbertH3ZornCarrierAlignment.equiv,
    RealAlbertH3ZornCarrierAlignment.fromH3,
    RealAlbertH3ZornCarrierAlignment.toH3, hermitianToH3,
    canonicalEquiv, toCanonical, fromCanonical,
    RealSplitOctZornAlignment.fromZorn, RealSplitOctZornAlignment.toZorn,
    RealSplitOct.conj, RealSplitOct.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
  try simp only [hX02, hY02, hX12, hY12]
  simp [zornConj, smul, vecToCanonical, dot] <;> ring

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
