import Mathlib.Tactic
import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Projective.Cl55NullBoundaryBridge

/-!
# Native bridge from the PAC `(5,5)` record to `Cl(5,5)` vectors

`PACSplit55` is a coordinate record, while the native Clifford owner uses
`V55 = (Fin 5 → ℝ) × (Fin 5 → ℝ)`.  This file identifies those coordinate
carriers, transports the quadratic form, and derives the null-generator
square-zero theorem.  It deliberately does not quotient the Clifford algebra
by projective rescaling: a projective line determines a Clifford line, not a
canonical degree-one element.
-/

noncomputable section

namespace InfoGeometry.Canonical.PACNativeCliffordBridge

open ProjectiveAffineConformalClosure55
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Projective
open InfoGeometry.Projective.Cl55NullBoundaryBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryDatum

def pac55ToV55 (X : PACSplit55) : V55 :=
  (![X.x0, X.x1, X.x2, X.x3, X.u],
    ![X.y0, X.y1, X.y2, X.y3, X.v])

def v55ToPac55 (X : V55) : PACSplit55 where
  x0 := X.1 0
  x1 := X.1 1
  x2 := X.1 2
  x3 := X.1 3
  y0 := X.2 0
  y1 := X.2 1
  y2 := X.2 2
  y3 := X.2 3
  u := X.1 4
  v := X.2 4

@[simp] theorem v55ToPac55_pac55ToV55 (X : PACSplit55) :
    v55ToPac55 (pac55ToV55 X) = X := by
  cases X
  rfl

@[simp] theorem pac55ToV55_v55ToPac55 (X : V55) :
    pac55ToV55 (v55ToPac55 X) = X := by
  rcases X with ⟨x, y⟩
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

def pac55Equiv : PACSplit55 ≃ V55 where
  toFun := pac55ToV55
  invFun := v55ToPac55
  left_inv := v55ToPac55_pac55ToV55
  right_inv := pac55ToV55_v55ToPac55

theorem pac55ToV55_Q55 (X : PACSplit55) :
    InfoGeometry.Clifford.Clifford55.Q55 (pac55ToV55 X) =
      ProjectiveAffineConformalClosure55.Q55 X := by
  classical
  rw [InfoGeometry.Clifford.Clifford55.Q55_apply]
  unfold ProjectiveAffineConformalClosure55.Q55 pac55ToV55
  simp [Fin.sum_univ_succ]
  ring

def pac44NativeNullVector (x : PACSplit44) : V55 :=
  pac55ToV55 (conformalEmbed44to55 x)

theorem pac44NativeNullVector_Q55 (x : PACSplit44) :
    InfoGeometry.Clifford.Clifford55.Q55 (pac44NativeNullVector x) = 0 := by
  rw [pac44NativeNullVector, pac55ToV55_Q55]
  exact conformalEmbed44to55_null x

theorem pac44NativeNullClifford_sq_zero (x : PACSplit44) :
    ι55 (pac44NativeNullVector x) * ι55 (pac44NativeNullVector x) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, pac44NativeNullVector_Q55]
  simp

theorem pac55ToV55_smul (a : ℝ) (X : PACSplit55) :
    pac55ToV55 (smul55 a X) = a • pac55ToV55 X := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem pac55ToV55_clifford_smul (a : ℝ) (X : PACSplit55) :
    ι55 (pac55ToV55 (smul55 a X)) =
      a • ι55 (pac55ToV55 X) := by
  rw [pac55ToV55_smul]
  exact (ι55 : V55 →ₗ[ℝ] Cl55).map_smul a (pac55ToV55 X)

@[simp] theorem pac55ToV55_pacSplit55Zero :
    pac55ToV55 pacSplit55Zero = (0 : V55) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem pac55ToV55_projective_line_readout
    {X Y : PACSplit55} (h : sameProjectiveLine55 X Y) :
    ∃ a : ℝ, a ≠ 0 ∧
      ι55 (pac55ToV55 Y) = a • ι55 (pac55ToV55 X) := by
  rcases h with ⟨a, ha, rfl⟩
  exact ⟨a, ha, pac55ToV55_clifford_smul a X⟩

/-! ## Native projective-null boundary descent -/

/-- The chosen nonzero null representative of a PAC projective point,
transported to the native V55 carrier and then quotiented by native unit
scaling. The choice is harmless because the target is already a projective
quotient; all subsequent Pin actions use the native boundary owner. -/
noncomputable def pacProjectiveNonzeroNull55_to_nativeBoundary
    (P : ProjectiveNonzeroNull55) : Cl55NullBoundaryBridge.Boundary :=
  nullMk datum
    { Z := pac55ToV55 (projectiveNonzeroNull55_representative P)
      null := by
        change Q55 (pac55ToV55 (projectiveNonzeroNull55_representative P)) = 0
        rw [pac55ToV55_Q55]
        exact projectiveNonzeroNull55_representative_null P
      nonzero := by
        intro hzero
        change pac55ToV55 (projectiveNonzeroNull55_representative P) =
          (0 : V55) at hzero
        have hzero' :
            pac55ToV55 (projectiveNonzeroNull55_representative P) =
              pac55ToV55 pacSplit55Zero := by
          rw [pac55ToV55_pacSplit55Zero]
          exact hzero
        have hrep :
            projectiveNonzeroNull55_representative P =
              pacSplit55Zero := by
          exact pac55Equiv.injective hzero'
        exact projectiveNonzeroNull55_representative_nonzero P hrep }

@[simp] theorem pacProjectiveNonzeroNull55_to_nativeBoundary_mk
    (P : ProjectiveNonzeroNull55) :
    pacProjectiveNonzeroNull55_to_nativeBoundary P =
      nullMk datum
        { Z := pac55ToV55 (projectiveNonzeroNull55_representative P)
          null := by
            change Q55 (pac55ToV55 (projectiveNonzeroNull55_representative P)) = 0
            rw [pac55ToV55_Q55]
            exact projectiveNonzeroNull55_representative_null P
          nonzero := by
            intro hzero
            change pac55ToV55 (projectiveNonzeroNull55_representative P) =
              (0 : V55) at hzero
            have hzero' :
                pac55ToV55 (projectiveNonzeroNull55_representative P) =
                  pac55ToV55 pacSplit55Zero := by
              rw [pac55ToV55_pacSplit55Zero]
              exact hzero
            have hrep :
                projectiveNonzeroNull55_representative P =
                  pacSplit55Zero :=
              pac55Equiv.injective hzero'
            exact projectiveNonzeroNull55_representative_nonzero P hrep } :=
  rfl

theorem pacProjectiveNonzeroNull55_to_nativeBoundary_eq_of_eq
    {P Q : ProjectiveNonzeroNull55} (hPQ : P = Q) :
    pacProjectiveNonzeroNull55_to_nativeBoundary P =
      pacProjectiveNonzeroNull55_to_nativeBoundary Q := by
  rw [hPQ]

/-- Any other nonzero null representative of the same PAC projective point
gives the same native projective-null boundary point. -/
theorem pacProjectiveNonzeroNull55_to_nativeBoundary_independent
    (P : ProjectiveNonzeroNull55)
    (X : PACSplit55)
    (hPX : projectiveMk55 X = P.1)
    (hXnull : Q55 X = 0)
    (hXne : X ≠ pacSplit55Zero) :
    pacProjectiveNonzeroNull55_to_nativeBoundary P =
      nullMk datum
        { Z := pac55ToV55 X
          null := by
            change Q55 (pac55ToV55 X) = 0
            rw [pac55ToV55_Q55]
            exact hXnull
          nonzero := by
            intro hzero
            change pac55ToV55 X = (0 : V55) at hzero
            apply hXne
            apply pac55Equiv.injective
            change pac55ToV55 X = pac55ToV55 pacSplit55Zero
            rw [pac55ToV55_pacSplit55Zero]
            exact hzero } := by
  have hproj :
      projectiveMk55 (projectiveNonzeroNull55_representative P) =
        projectiveMk55 X := by
    exact
      (projectiveNonzeroNull55_representative_projective P).trans hPX.symm
  have hline :
      sameProjectiveLine55
        (projectiveNonzeroNull55_representative P) X := by
    exact Quotient.exact hproj
  rcases hline with ⟨a, ha, hscale⟩
  rw [pacProjectiveNonzeroNull55_to_nativeBoundary_mk]
  apply (nullMk_eq_iff_rayRel datum _ _).2
  refine ⟨Units.mk0 a ha, ?_⟩
  change
    (a : ℝ) •
        pac55ToV55 (projectiveNonzeroNull55_representative P) =
      pac55ToV55 X
  rw [← pac55ToV55_smul, hscale]

end InfoGeometry.Canonical.PACNativeCliffordBridge

end
