import InfoGeometry.Clifford.SplitOctonionChiralMatrixProduct
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitQ44
import InfoGeometry.Clifford.Cl44Spinors

namespace InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout

noncomputable section
set_option maxHeartbeats 1000000

def chiralToSplit44 : (Fin 8 → ℝ) ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun x :=
    ![(x 0 + x 4) / 2, (x 1 + x 5) / 2, (x 2 + x 6) / 2,
      (x 3 + x 7) / 2, (x 0 - x 4) / 2, (x 1 - x 5) / 2,
      (x 2 - x 6) / 2, (x 3 - x 7) / 2]
  invFun y :=
    ![y 0 + y 4, y 1 + y 5, y 2 + y 6, y 3 + y 7,
      y 0 - y 4, y 1 - y 5, y 2 - y 6, y 3 - y 7]
  left_inv x := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_succ, Matrix.cons_val_zero] <;> ring
  right_inv y := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_succ, Matrix.cons_val_zero] <;> ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

noncomputable def chiralToSplit44_isometry :
    chiralQuadratic.IsometryEquiv
      InfoGeometry.Clifford.splitQ44 := by
  refine { chiralToSplit44 with map_app' := ?_ }
  intro x
  simp only [InfoGeometry.Clifford.splitQ44_apply, chiralQuadratic_apply]
  dsimp [chiralToSplit44]
  ring

noncomputable def chiralCliffordToCl44 :
    CliffordAlgebra chiralQuadratic ≃ₐ[ℝ]
      InfoGeometry.Clifford.Cl44 :=
  CliffordAlgebra.equivOfIsometry chiralToSplit44_isometry

noncomputable def chiralVacuumIdempotent : CliffordAlgebra chiralQuadratic :=
  chiralCliffordToCl44.symm InfoGeometry.Clifford.Cl44Spinors.vacuumIdempotent

theorem vacuumIdempotent_ne_zero :
    InfoGeometry.Clifford.Cl44Spinors.vacuumIdempotent ≠ 0 := by
  intro h
  have hCAR := InfoGeometry.Clifford.Cl44Witt.cl11_witt_CAR_eq
  have hadag : InfoGeometry.Clifford.Cl44Witt.adag11 *
      InfoGeometry.Clifford.Cl44Witt.a11 = 1 := by
    rw [show InfoGeometry.Clifford.Cl44Spinors.vacuumIdempotent =
      InfoGeometry.Clifford.Cl44Witt.a11 * InfoGeometry.Clifford.Cl44Witt.adag11
      by rfl] at h
    rw [h, zero_add] at hCAR
    exact hCAR
  have hz : InfoGeometry.Clifford.Cl44Witt.adag11 = 0 := by
    calc
      InfoGeometry.Clifford.Cl44Witt.adag11 =
          InfoGeometry.Clifford.Cl44Witt.adag11 * 1 := by simp
      _ = InfoGeometry.Clifford.Cl44Witt.adag11 *
          (InfoGeometry.Clifford.Cl44Witt.adag11 *
            InfoGeometry.Clifford.Cl44Witt.a11) := by rw [hadag]
      _ = (InfoGeometry.Clifford.Cl44Witt.adag11 *
          InfoGeometry.Clifford.Cl44Witt.adag11) *
            InfoGeometry.Clifford.Cl44Witt.a11 := by simp [mul_assoc]
      _ = 0 := by rw [InfoGeometry.Clifford.Cl44Witt.cl11_adag_sq_zero]; simp
  have h01 : (1 : InfoGeometry.Clifford.Cl44) = 0 := by
    rw [← InfoGeometry.Clifford.Cl44Witt.cl11_witt_CAR_eq]
    rw [hz] at hCAR
    simpa using hCAR.symm
  exact one_ne_zero h01

theorem chiralVacuumIdempotent_ne_zero :
    chiralVacuumIdempotent ≠ 0 := by
  intro h
  apply vacuumIdempotent_ne_zero
  have := congrArg chiralCliffordToCl44 h
  simpa [chiralVacuumIdempotent] using this

theorem chiralVacuumIdempotent_idem :
    chiralVacuumIdempotent * chiralVacuumIdempotent =
      chiralVacuumIdempotent := by
  apply chiralCliffordToCl44.injective
  simp [chiralVacuumIdempotent,
    InfoGeometry.Clifford.Cl44Spinors.vacuumIdempotent_idem]

def ChiralMinimalSpinor :=
  { x : CliffordAlgebra chiralQuadratic //
      x * chiralVacuumIdempotent = x }

def chiralMinimalSpinorToCl44 :
    ChiralMinimalSpinor ≃
      InfoGeometry.Clifford.Cl44Spinors.MinimalSpinor where
  toFun x :=
    ⟨chiralCliffordToCl44 x.1,
      by
        have h := congrArg chiralCliffordToCl44 x.2
        simpa [chiralVacuumIdempotent] using h⟩
  invFun x :=
    ⟨chiralCliffordToCl44.symm x.1,
      by
        change chiralCliffordToCl44.symm x.1 * chiralVacuumIdempotent =
          chiralCliffordToCl44.symm x.1
        have h := congrArg chiralCliffordToCl44.symm x.2
        simpa [chiralVacuumIdempotent, map_mul] using h⟩
  left_inv x := by
    apply Subtype.ext
    exact chiralCliffordToCl44.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact chiralCliffordToCl44.apply_symm_apply x.1

/-! The chiral quadratic form is presented in a hyperbolic basis.  It is
not definitionally the diagonal `(4,4)` form used by the Witt owner. -/

theorem chiralQuadratic_ne_splitQ44 :
    chiralQuadratic ≠ InfoGeometry.Clifford.splitQ44 := by
  intro h
  have h0 := congrArg (fun Q : QuadraticForm ℝ (Fin 8 → ℝ) =>
    Q (Pi.single 0 1)) h
  change chiralQuadratic (Pi.single 0 1) =
    InfoGeometry.Clifford.splitQ44 (Pi.single 0 1) at h0
  rw [chiralQuadratic_apply, InfoGeometry.Clifford.splitQ44_apply] at h0
  norm_num [Pi.single_eq_same, Pi.single_eq_of_ne, Fin.ext_iff] at h0

end
end InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout
