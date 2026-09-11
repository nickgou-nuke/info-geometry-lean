import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- Origin in PAC (5,5) coordinates. -/
def pacSplit55Zero : PACSplit55 where
  x0 := 0; x1 := 0; x2 := 0; x3 := 0
  y0 := 0; y1 := 0; y2 := 0; y3 := 0
  u := 0; v := 0

@[simp] theorem v55ToPac55_zero :
    v55ToPac55 (0 : V55) = pacSplit55Zero := rfl

@[simp] theorem pac55ToV55_pacSplit55Zero :
    pac55ToV55 pacSplit55Zero = (0 : V55) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem pac55ToV55_eq_zero_iff (X : PACSplit55) :
    pac55ToV55 X = 0 ↔ X = pacSplit55Zero := by
  constructor
  · intro h
    have := congrArg v55ToPac55 h
    rw [v55ToPac55_pac55ToV55, v55ToPac55_zero] at this
    exact this
  · rintro rfl
    exact pac55ToV55_pacSplit55Zero

theorem pac55ToV55_projective_line_readout
    {X Y : PACSplit55} (h : sameProjectiveLine55 X Y) :
    ∃ a : ℝ, a ≠ 0 ∧
      ι55 (pac55ToV55 Y) = a • ι55 (pac55ToV55 X) := by
  rcases h with ⟨a, ha, rfl⟩
  exact ⟨a, ha, pac55ToV55_clifford_smul a X⟩

/-! ## Native projective-null boundary descent -/

/-- Map from a nonzero null PAC vector to the native Cl(5,5) projective null boundary. -/
def pacNullToNativeBoundary
    (X : PACSplit55)
    (hnull : ProjectiveAffineConformalClosure55.Q55 X = 0)
    (hne : X ≠ pacSplit55Zero) :
    Cl55NullBoundaryBridge.Boundary :=
  nullMk datum
    { Z := pac55ToV55 X
      null := by
        change InfoGeometry.Clifford.Clifford55.Q55 (pac55ToV55 X) = 0
        rw [pac55ToV55_Q55]
        exact hnull
      nonzero := by
        intro hzero
        apply hne
        exact (pac55ToV55_eq_zero_iff X).mp hzero }

/-- Two nonzero null PAC vectors defining the same projective line descend
to the exact same native projective null boundary point. -/
theorem pacNullToNativeBoundary_eq_of_sameProjectiveLine
    {X Y : PACSplit55}
    (hnullX : ProjectiveAffineConformalClosure55.Q55 X = 0)
    (hneX : X ≠ pacSplit55Zero)
    (hnullY : ProjectiveAffineConformalClosure55.Q55 Y = 0)
    (hneY : Y ≠ pacSplit55Zero)
    (hline : sameProjectiveLine55 X Y) :
    pacNullToNativeBoundary X hnullX hneX =
      pacNullToNativeBoundary Y hnullY hneY := by
  rcases hline with ⟨a, ha, rfl⟩
  apply Quotient.sound
  refine ⟨Units.mk0 a ha, ?_⟩
  change (a : ℝ) • pac55ToV55 X = pac55ToV55 (smul55 a X)
  rw [pac55ToV55_smul]

/-- The conformal embedding of any 4+4 split vector is never the zero vector. -/
theorem conformalEmbed44to55_ne_zero (x : PACSplit44) :
    conformalEmbed44to55 x ≠ pacSplit55Zero := by
  intro h
  have hu : (conformalEmbed44to55 x).u = 0 := by rw [h]; rfl
  have hv : (conformalEmbed44to55 x).v = 0 := by rw [h]; rfl
  dsimp [conformalEmbed44to55] at hu hv
  have hsum : (1 - Q44 x) / 2 + (1 + Q44 x) / 2 = 0 := by rw [hu, hv, add_zero]
  have hone : (1 : ℝ) = 0 := by
    calc (1 : ℝ) = (1 - Q44 x) / 2 + (1 + Q44 x) / 2 := by ring
    _ = 0 := hsum
  exact one_ne_zero hone

/-- Canonical descent of any 4+4 affine coordinate to the native Cl(5,5) projective null boundary. -/
def pac44ToNativeBoundary (x : PACSplit44) : Cl55NullBoundaryBridge.Boundary :=
  pacNullToNativeBoundary (conformalEmbed44to55 x)
    (conformalEmbed44to55_null x)
    (conformalEmbed44to55_ne_zero x)

end PACNativeCliffordBridge

end Canonical
