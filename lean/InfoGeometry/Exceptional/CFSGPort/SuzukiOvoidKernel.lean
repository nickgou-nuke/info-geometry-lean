/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.SuzukiOvoid

/-!
# The projective kernel of the Suzuki ovoid action

The five explicit ovoid points at infinity, the origin, `(1,0)`, `(0,1)`,
and `(1,1)` determine a projective linear transformation up to a common
scalar. This is the coordinate-kernel step in the local port of the external
Suzuki simplicity proof.
-/

public noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Exceptional.CFSGPort.Suzuki

variable {K : Type} [Field K]

/-- An operator fixing every point of the normalized Suzuki ovoid is scalar.
The proof uses the explicit noncommutative linear action on projective space;
the scalar is the unavoidable kernel of projectivization. -/
theorem suzukiOvoid_fixed_operator_is_scalar [CharP K 2]
    (pi : K ≃+* K) (A : Matrix.GeneralLinearGroup (Fin 4) K)
    (hA : ∀ z, z ∈ ovoid pi →
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z = z) :
    ∃ c : K, (A : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (Fin 4) c := by
  have hthree : (1 : K) + 1 + 1 = 1 := by
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination htwo
  have hpoint10 : Projectivization.mk K
      (![1, 0, 1, 1] : Fin 4 → K) (by simp) = ovoidPoint pi 1 0 := by
    simp [ovoidPoint]
  have hpoint01 : Projectivization.mk K
      (![1, 1, 0, 1] : Fin 4 → K) (by simp) = ovoidPoint pi 0 1 := by
    simp [ovoidPoint]
  have hpoint11 : Projectivization.mk K
      (![1, 1, 1, 1] : Fin 4 → K) (by simp) = ovoidPoint pi 1 1 := by
    simp [ovoidPoint, hthree]
  have hmem10 : ovoidPoint pi 1 0 ∈ ovoid pi := Or.inr ⟨(1, 0), rfl⟩
  have hmem01 : ovoidPoint pi 0 1 ∈ ovoid pi := Or.inr ⟨(0, 1), rfl⟩
  have hmem11 : ovoidPoint pi 1 1 ∈ ovoid pi := Or.inr ⟨(1, 1), rfl⟩
  obtain ⟨cInf, hInf⟩ := projective_fixed_vector_is_eigenvector A
    (![1, 0, 0, 0] : Fin 4 → K) (by simp) (by
      change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv •
        ovoidInfinity = ovoidInfinity
      exact hA _ (by simp [ovoid]))
  obtain ⟨cZero, hZero⟩ := projective_fixed_vector_is_eigenvector A
    (![0, 0, 0, 1] : Fin 4 → K) (by simp) (by
      change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv •
        Projectivization.mk K (![0, 0, 0, 1] : Fin 4 → K) (by simp) = _
      simpa [ovoidInfinity, ovoidPoint] using
        hA (ovoidPoint pi 0 0) (Or.inr ⟨(0, 0), rfl⟩))
  obtain ⟨c10, h10⟩ := projective_fixed_vector_is_eigenvector A
    (![1, 0, 1, 1] : Fin 4 → K) (by simp) (by
      rw [hpoint10]
      exact hA _ hmem10)
  obtain ⟨c01, h01⟩ := projective_fixed_vector_is_eigenvector A
    (![1, 1, 0, 1] : Fin 4 → K) (by simp) (by
      rw [hpoint01]
      exact hA _ hmem01)
  obtain ⟨c11, h11⟩ := projective_fixed_vector_is_eigenvector A
    (![1, 1, 1, 1] : Fin 4 → K) (by simp) (by
      rw [hpoint11]
      exact hA _ hmem11)
  let M : Matrix (Fin 4) (Fin 4) K := A
  have hInf' (i : Fin 4) : M i 0 = cInf * (![1, 0, 0, 0] : Fin 4 → K) i := by
    simpa [M] using hInf i
  have hZero' (i : Fin 4) : M i 3 = cZero * (![0, 0, 0, 1] : Fin 4 → K) i := by
    simpa [M] using hZero i
  have h10' (i : Fin 4) : M i 0 + M i 2 + M i 3 =
      c10 * (![1, 0, 1, 1] : Fin 4 → K) i := by
    simpa [M] using h10 i
  have h01' (i : Fin 4) : M i 0 + M i 1 + M i 3 =
      c01 * (![1, 1, 0, 1] : Fin 4 → K) i := by
    simpa [M] using h01 i
  have h11' (i : Fin 4) : M i 0 + M i 1 + M i 2 + M i 3 =
      c11 * (![1, 1, 1, 1] : Fin 4 → K) i := by
    simpa [M] using h11 i
  have i00 : M 0 0 = cInf := by simpa using hInf' 0
  have i10 : M 1 0 = 0 := by simpa using hInf' 1
  have i20 : M 2 0 = 0 := by simpa using hInf' 2
  have i30 : M 3 0 = 0 := by simpa using hInf' 3
  have z03 : M 0 3 = 0 := by simpa using hZero' 0
  have z13 : M 1 3 = 0 := by simpa using hZero' 1
  have z23 : M 2 3 = 0 := by simpa using hZero' 2
  have z33 : M 3 3 = cZero := by simpa using hZero' 3
  have a0 : M 0 0 + M 0 2 + M 0 3 = c10 := by simpa using h10' 0
  have a1 : M 1 0 + M 1 2 + M 1 3 = 0 := by simpa using h10' 1
  have a2 : M 2 0 + M 2 2 + M 2 3 = c10 := by simpa using h10' 2
  have a3 : M 3 0 + M 3 2 + M 3 3 = c10 := by simpa using h10' 3
  have b0 : M 0 0 + M 0 1 + M 0 3 = c01 := by simpa using h01' 0
  have b1 : M 1 0 + M 1 1 + M 1 3 = c01 := by simpa using h01' 1
  have b2 : M 2 0 + M 2 1 + M 2 3 = 0 := by simpa using h01' 2
  have b3 : M 3 0 + M 3 1 + M 3 3 = c01 := by simpa using h01' 3
  have d0 : M 0 0 + M 0 1 + M 0 2 + M 0 3 = c11 := by simpa using h11' 0
  have d1 : M 1 0 + M 1 1 + M 1 2 + M 1 3 = c11 := by simpa using h11' 1
  have d2 : M 2 0 + M 2 1 + M 2 2 + M 2 3 = c11 := by simpa using h11' 2
  have d3 : M 3 0 + M 3 1 + M 3 2 + M 3 3 = c11 := by simpa using h11' 3
  have a02 : M 0 2 = c10 - cInf := by linear_combination a0 - i00 - z03
  have a12 : M 1 2 = 0 := by linear_combination a1 - i10 - z13
  have a22 : M 2 2 = c10 := by linear_combination a2 - i20 - z23
  have a32 : M 3 2 = c10 - cZero := by linear_combination a3 - i30 - z33
  have b01 : M 0 1 = c01 - cInf := by linear_combination b0 - i00 - z03
  have b11 : M 1 1 = c01 := by linear_combination b1 - i10 - z13
  have b21 : M 2 1 = 0 := by linear_combination b2 - i20 - z23
  have b31 : M 3 1 = c01 - cZero := by linear_combination b3 - i30 - z33
  have hc11 : c11 = c01 := by
    calc
      c11 = M 1 0 + M 1 1 + M 1 2 + M 1 3 := d1.symm
      _ = M 1 0 + M 1 1 + M 1 3 := by rw [a12]; simp
      _ = c01 := b1
  have hc10 : c10 = c01 := by
    calc
      c10 = c11 := by
        calc
          c10 = M 2 0 + M 2 2 + M 2 3 := a2.symm
          _ = M 2 0 + M 2 1 + M 2 2 + M 2 3 := by rw [b21]; simp
          _ = c11 := d2
      _ = c01 := hc11
  have hcInf : cInf = c01 := by
    have hrow : cInf + (c01 - cInf) + (c10 - cInf) = c11 := by
      calc
        cInf + (c01 - cInf) + (c10 - cInf) =
            M 0 0 + M 0 1 + M 0 2 + M 0 3 := by
              rw [i00, b01, a02, z03]
              ring
        _ = c11 := d0
    linear_combination -hrow + hc10 - hc11
  have hcZero : cZero = c01 := by
    have hrow : M 3 0 + (c01 - cZero) + (c10 - cZero) + cZero = c11 := by
      calc
        M 3 0 + (c01 - cZero) + (c10 - cZero) + cZero =
            M 3 0 + M 3 1 + M 3 2 + M 3 3 := by
              rw [b31, a32, z33]
        _ = c11 := d3
    rw [i30] at hrow
    linear_combination -hrow + hc10 - hc11
  refine ⟨c01, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, M, i00, i10, i20, i30, z03, z13, z23, z33,
      a02, a12, a22, a32, b01, b11, b21, b31, hc10, hcInf, hcZero]

/-- The Suzuki upper-matrix subgroup acts faithfully on its projective
ovoid: an element fixing every ovoid point is scalar by the coordinate
kernel theorem, then determinant one forces that scalar to be the identity. -/
theorem suzukiUpperMatrixGroup_ovoid_action_trivial [CharP K 2] (a : ℕ)
    (pi : K ≃+* K) (g : Chevalley.suzukiUpperMatrixGroup a K)
    (hfix : ∀ z, z ∈ ovoid pi →
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z = z) :
    (g : Matrix.GeneralLinearGroup (Fin 4) K) = 1 := by
  obtain ⟨c, hc⟩ := suzukiOvoid_fixed_operator_is_scalar pi
    (g : Matrix.GeneralLinearGroup (Fin 4) K) hfix
  have hcenter :
      (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 4) K) := by
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    exact ⟨c, hc.symm⟩
  exact suzukiUpperMatrixGroup_center_trivial (K := K) a g.property hcenter

/-- Faithfulness of the actual upper-matrix Suzuki group on the projective
ovoid. The action is restricted from its four-dimensional linear action, and
its kernel is the subgroup kernel proved above. -/
theorem suzukiUpperMatrixGroup_faithful_ovoid [Finite K] [CharP K 2] (a : ℕ)
    (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0) :
    let G := Chevalley.suzukiUpperMatrixGroup a K
    let ρ : G →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
      (Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp G.subtype
    letI : MulAction G (ℙ K (Fin 4 → K)) := MulAction.compHom _ ρ
    let Ω : SubMulAction G (ℙ K (Fin 4 → K)) :=
      { carrier := ovoid pi
        smul_mem' := by
          intro g z hz
          exact suzukiUpperMatrixGroup_smul_mem_ovoid
            a pi hpi_sq hpi_formula hnorm_zero g z hz }
    letI : MulAction G Ω := {
      smul g z := ⟨ρ g • z.1, Ω.smul_mem' g z.2⟩
      one_smul z := by
        apply Subtype.ext
        simp
      mul_smul g h z := by
        apply Subtype.ext
        change ρ (g * h) • (z : ℙ K (Fin 4 → K)) =
          ρ g • (ρ h • (z : ℙ K (Fin 4 → K)))
        rw [map_mul]
        exact mul_smul _ _ _
    }
    FaithfulSMul G Ω := by
  let G := Chevalley.suzukiUpperMatrixGroup a K
  let ρ : G →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    (Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp G.subtype
  letI : MulAction G (ℙ K (Fin 4 → K)) := MulAction.compHom _ ρ
  let Ω : SubMulAction G (ℙ K (Fin 4 → K)) :=
    { carrier := ovoid pi
      smul_mem' := by
        intro g z hz
        exact suzukiUpperMatrixGroup_smul_mem_ovoid
          a pi hpi_sq hpi_formula hnorm_zero g z hz }
  letI : MulAction G Ω := {
    smul g z := ⟨ρ g • z.1, Ω.smul_mem' g z.2⟩
    one_smul z := by
      apply Subtype.ext
      simp
    mul_smul g h z := by
      apply Subtype.ext
      change ρ (g * h) • (z : ℙ K (Fin 4 → K)) =
        ρ g • (ρ h • (z : ℙ K (Fin 4 → K)))
      rw [map_mul]
      exact mul_smul _ _ _
  }
  rw [faithfulSMul_iff]
  intro g hg
  apply Subtype.ext
  apply suzukiUpperMatrixGroup_ovoid_action_trivial (K := K) a pi g
  intro z hz
  have h := congrArg Subtype.val (hg ⟨z, hz⟩)
  change (ρ g).toLinearEquiv • z = z at h
  simpa [ρ] using h

end InfoGeometry.Exceptional.CFSGPort.Suzuki
