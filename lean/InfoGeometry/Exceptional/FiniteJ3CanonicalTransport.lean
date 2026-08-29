import InfoGeometry.Exceptional.FiniteJ3ZornCarrier
import InfoGeometry.Exceptional.ZornMatrixRealCanonicalBridge
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.H3ZornJordanIdentity
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

theorem scalarZorn_conj (r : ℝ) : zornConj (scalarZorn r) = scalarZorn r := by
  apply ZornMatrixReal.ext <;>
    simp [scalarZorn, zornConj, smul]

theorem h3ToHermitian_hermitian (Z : H3Zorn ℝ) :
    hermitianStar (h3ToHermitian Z) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [h3ToHermitian, scalarZorn, zornConj, smul]

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

theorem h3ToHermitian_hermitianToH3_01 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 0 1 = X.1 0 1 := by
  change canonicalEquiv.symm (canonicalEquiv (X.1 0 1)) = X.1 0 1
  exact canonicalEquiv.symm_apply_apply (X.1 0 1)

theorem h3ToHermitian_hermitianToH3_12 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 1 2 = X.1 1 2 := by
  change canonicalEquiv.symm (canonicalEquiv (X.1 1 2)) = X.1 1 2
  exact canonicalEquiv.symm_apply_apply (X.1 1 2)

theorem h3ToHermitian_hermitianToH3_20 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 2 0 = X.1 2 0 := by
  change canonicalEquiv.symm (canonicalEquiv (X.1 2 0)) = X.1 2 0
  exact canonicalEquiv.symm_apply_apply (X.1 2 0)

theorem h3ToHermitian_hermitianToH3_10 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 1 0 = X.1 1 0 := by
  have h := congrArg zornConj (X.property 0 1)
  rw [zornConj_involutive] at h
  change zornConj (canonicalEquiv.symm (canonicalEquiv (X.1 0 1))) = X.1 1 0
  rw [canonicalEquiv.symm_apply_apply, h]

theorem h3ToHermitian_hermitianToH3_21 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 2 1 = X.1 2 1 := by
  have h := congrArg zornConj (X.property 1 2)
  rw [zornConj_involutive] at h
  change zornConj (canonicalEquiv.symm (canonicalEquiv (X.1 1 2))) = X.1 2 1
  rw [canonicalEquiv.symm_apply_apply, h]

theorem h3ToHermitian_hermitianToH3_02 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 0 2 = X.1 0 2 := by
  have h := congrArg zornConj (X.property 2 0)
  rw [zornConj_involutive] at h
  change zornConj (canonicalEquiv.symm (canonicalEquiv (X.1 2 0))) = X.1 0 2
  rw [canonicalEquiv.symm_apply_apply, h]

theorem h3ToHermitian_hermitianToH3_00 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 0 0 = X.1 0 0 := by
  change scalarZorn (X.1 0 0).a = X.1 0 0
  have h := hermitian_diagonal_scalar X 0
  apply ZornMatrixReal.ext
  · rfl
  · exact h.1
  · exact h.2.1.symm
  · exact h.2.2.symm

theorem h3ToHermitian_hermitianToH3_11 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 1 1 = X.1 1 1 := by
  change scalarZorn (X.1 1 1).a = X.1 1 1
  have h := hermitian_diagonal_scalar X 1
  apply ZornMatrixReal.ext
  · rfl
  · exact h.1
  · exact h.2.1.symm
  · exact h.2.2.symm

theorem h3ToHermitian_hermitianToH3_22 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) 2 2 = X.1 2 2 := by
  change scalarZorn (X.1 2 2).a = X.1 2 2
  have h := hermitian_diagonal_scalar X 2
  apply ZornMatrixReal.ext
  · rfl
  · exact h.1
  · exact h.2.1.symm
  · exact h.2.2.symm

theorem h3ToHermitian_hermitianToH3 (X : HermitianJ3) :
    h3ToHermitian (hermitianToH3 X) = X.1 := by
  funext i j
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
    apply Subtype.ext
    exact h3ToHermitian_hermitianToH3 X
  right_inv := by
    intro Z
    exact hermitianToH3_h3ToHermitian Z

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

theorem hermitian_diagonal_eq_scalarZorn (X : HermitianJ3) (i : Fin 3) :
    X.1 i i = scalarZorn (X.1 i i).a := by
  have h := X.property i i
  apply ZornMatrixReal.ext
  · rfl
  · simpa [zornConj] using congrArg ZornMatrixReal.b h
  · have hu := congrArg ZornMatrixReal.u h
    apply Prod.ext
    · have h₀ := congrArg Prod.fst hu
      exact (InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _).mp (by simpa [zornConj, smul] using h₀.symm)
    · apply Prod.ext
      · have h₁ := congrArg (fun v => v.2.1) hu
        exact (InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _).mp (by simpa [zornConj, smul] using h₁.symm)
      · have h₂ := congrArg (fun v => v.2.2) hu
        exact (InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _).mp (by simpa [zornConj, smul] using h₂.symm)
  · have hv := congrArg ZornMatrixReal.v h
    apply Prod.ext
    · have h₀ := congrArg Prod.fst hv
      exact (InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _).mp (by simpa [zornConj, smul] using h₀.symm)
    · apply Prod.ext
      · have h₁ := congrArg (fun v => v.2.1) hv
        exact (InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _).mp (by simpa [zornConj, smul] using h₁.symm)
      · have h₂ := congrArg (fun v => v.2.2) hv
        exact (InfoGeometry.Exceptional.RealZorn.neg_one_smul_eq_self_iff _).mp (by simpa [zornConj, smul] using h₂.symm)

theorem hermitian_readback_10 (X : HermitianJ3) :
    X.1 1 0 = zornConj (X.1 0 1) := X.property 1 0

theorem hermitian_readback_21 (X : HermitianJ3) :
    X.1 2 1 = zornConj (X.1 1 2) := X.property 2 1

theorem hermitian_readback_02 (X : HermitianJ3) :
    X.1 0 2 = zornConj (X.1 2 0) := X.property 0 2

theorem hermitian_readback_01 (X : HermitianJ3) :
    X.1 0 1 = zornConj (X.1 1 0) := X.property 0 1

theorem hermitian_readback_12 (X : HermitianJ3) :
    X.1 1 2 = zornConj (X.1 2 1) := X.property 1 2

theorem hermitian_readback_20 (X : HermitianJ3) :
    X.1 2 0 = zornConj (X.1 0 2) := X.property 2 0

theorem h3ToHermitianSubtype_hermitianToH3 (X : HermitianJ3) :
    h3ToHermitianSubtype (hermitianToH3 X) = X := by
  apply HermitianJ3_ext
  funext i j
  fin_cases i <;> fin_cases j
  · exact (hermitian_diagonal_eq_scalarZorn X 0).symm
  · exact (h3ToHermitian_hermitianToH3_01 X).symm
  · exact h3ToHermitian_hermitianToH3_02 X
  · exact h3ToHermitian_hermitianToH3_10 X
  · exact (hermitian_diagonal_eq_scalarZorn X 1).symm
  · exact (h3ToHermitian_hermitianToH3_12 X).symm
  · exact (h3ToHermitian_hermitianToH3_20 X).symm
  · exact h3ToHermitian_hermitianToH3_21 X
  · exact (hermitian_diagonal_eq_scalarZorn X 2).symm

@[simp] theorem hermitianH3Equiv_apply (X : HermitianJ3) :
    hermitianH3Equiv X = hermitianToH3 X := rfl

@[simp] theorem hermitianH3Equiv_symm_apply (Z : H3Zorn ℝ) :
    hermitianH3Equiv.symm Z = h3ToHermitianSubtype Z := rfl

noncomputable def inducedH3JordanMul (U V : H3Zorn ℝ) : H3Zorn ℝ :=
  hermitianH3Equiv
    (finiteJordanProduct (hermitianH3Equiv.symm U) (hermitianH3Equiv.symm V))

theorem inducedH3JordanMul_comm (U V : H3Zorn ℝ) :
    inducedH3JordanMul U V = inducedH3JordanMul V U := by
  unfold inducedH3JordanMul
  rw [finiteJordanProduct_comm]

def hermitianRealAlbertEquiv : HermitianJ3 ≃ RealAlbertMatrix :=
  hermitianH3Equiv.trans
    InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.symm

@[simp] theorem hermitianRealAlbertEquiv_apply (X : HermitianJ3) :
    hermitianRealAlbertEquiv X =
      InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv.symm
        (hermitianH3Equiv X) := rfl

@[simp] theorem hermitianRealAlbertEquiv_symm_apply (X : RealAlbertMatrix) :
    hermitianRealAlbertEquiv.symm X =
      hermitianH3Equiv.symm
        (InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv X) := rfl

/-
theorem hermitianRealAlbertEquiv_jordanProduct_α₁
    (X Y : HermitianJ3) :
    (hermitianRealAlbertEquiv
      ⟨jordanProduct X.1 Y.1,
        jordanProduct_hermitian_closed X Y⟩).α₁ =
      (RealAlbertMatrix.mul
        (hermitianRealAlbertEquiv X)
        (hermitianRealAlbertEquiv Y)).α₁ := by
  change (jordanProduct X.1 Y.1 0 0).a = _
  dsimp [RealAlbertMatrix.mul, jordanProduct, j3RawMul,
    hermitianRealAlbertEquiv, hermitianH3Equiv, hermitianToH3,
    InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.equiv,
    InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment.fromH3]
  have hm₁ := InfoGeometry.Exceptional.RealZorn.fromCanonical_mul_a
    (X.1 0 1) (Y.1 0 1)
  have hm₂ := InfoGeometry.Exceptional.RealZorn.fromCanonical_mul_a
    (Y.1 0 1) (X.1 0 1)
  have hm₃ := InfoGeometry.Exceptional.RealZorn.fromCanonical_mul_a
    (X.1 2 0) (Y.1 2 0)
  have hm₄ := InfoGeometry.Exceptional.RealZorn.fromCanonical_mul_a
    (Y.1 2 0) (X.1 2 0)
  have hc₁ := InfoGeometry.Exceptional.RealZorn.fromCanonical_conj_a
    (Y.1 0 1)
  have hc₂ := InfoGeometry.Exceptional.RealZorn.fromCanonical_conj_a
    (X.1 0 1)
  simp only [InfoGeometry.Exceptional.RealZorn.canonicalEquiv_apply] at hm₁ hm₂ hm₃ hm₄ hc₁ hc₂
  rw [hm₁, hm₂, hm₃, hm₄, hc₁, hc₂]
  rw [hermitian_readback_10 X, hermitian_readback_02 X,
    hermitian_readback_10 Y, hermitian_readback_02 Y]
  simp [zornHalf, smul, zornConj_involutive]
-/
end InfoGeometry.Exceptional.FiniteJ3Zorn
