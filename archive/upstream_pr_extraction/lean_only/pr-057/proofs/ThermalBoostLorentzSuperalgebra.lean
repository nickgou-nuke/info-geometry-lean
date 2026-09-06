import proofs.CuntzP6MWallpaperBoundary
import proofs.BuresFisherAndreevGeodesicFlow

/-!
# Thermal boost / Lorentz superalgebra bookkeeping

Finite rapidity, dispersion, modular-flow, and Cuntz/`p6m` bookkeeping for
the thermal boost interface.

The file proves only elementary finite and closed-form equalities:

* zero rapidity leaves the toy Lorentz transform fixed;
* `γ(η)` is represented by `cosh η`, hence `γ(0)=1`;
* the dispersion factor is normalized to `1` at zero rapidity;
* modular zero-time flow fixes a standing state;
* the Cuntz/`p6m` finite arities are `2`, `3`, and `5`.
-/

noncomputable section

namespace ThermalBoostLorentzSuperalgebra

/-- Toy 1+1 coordinate on the holographic screen, with second component `ct`. -/
structure ScreenCoord where
  x : ℝ
  ct : ℝ

/-- Standard rapidity-form boost used as finite coordinate bookkeeping. -/
def lorentzBoost (η : ℝ) (X : ScreenCoord) : ScreenCoord where
  x := X.x * Real.cosh η - X.ct * Real.sinh η
  ct := X.ct * Real.cosh η - X.x * Real.sinh η

@[simp] theorem lorentzBoost_zero (X : ScreenCoord) :
    lorentzBoost 0 X = X := by
  cases X
  simp [lorentzBoost]

/-- Lorentz gamma in the rapidity chart. -/
def gammaOfRapidity (η : ℝ) : ℝ := Real.cosh η

@[simp] theorem gamma_zero : gammaOfRapidity 0 = 1 := by
  simp [gammaOfRapidity]

/-- Thermal deformation parameter in a finite rapidity expression. -/
def qOfRapidity (ℏ η : ℝ) : ℝ := Real.exp (-(ℏ * η))

@[simp] theorem qOfRapidity_zero (ℏ : ℝ) : qOfRapidity ℏ 0 = 1 := by
  simp [qOfRapidity]

/-- Dispersion deformation factor, normalized at zero rapidity. -/
def safeDispersionFactor (η : ℝ) : ℝ :=
  if η = 0 then 1 else Real.sinh η / η

@[simp] theorem safeDispersionFactor_zero : safeDispersionFactor 0 = 1 := by
  simp [safeDispersionFactor]

/-- Finite modified dispersion expression used by the zero-rapidity check. -/
def modifiedDispersionToy (E p c η m₀ : ℝ) : ℝ :=
  E^2 - p^2 * c^2 * (safeDispersionFactor η)^2 - m₀^2 * c^4

@[simp] theorem modifiedDispersionToy_zero_factor (E p c m₀ : ℝ) :
    modifiedDispersionToy E p c 0 m₀ = E^2 - p^2 * c^2 - m₀^2 * c^4 := by
  simp [modifiedDispersionToy]

/-- Aggregate finite thermal-boost/Lorentz/Cuntz bookkeeping statement. -/
theorem thermal_boost_lorentz_superalgebra_synthesis
    (X : ScreenCoord) (ℏ K E p c m₀ : ℝ) (A : ℂ) :
    lorentzBoost 0 X = X ∧
    gammaOfRapidity 0 = 1 ∧
    qOfRapidity ℏ 0 = 1 ∧
    safeDispersionFactor 0 = 1 ∧
    modifiedDispersionToy E p c 0 m₀ = E^2 - p^2 * c^2 - m₀^2 * c^4 ∧
    modularFlow K 0 A = A ∧
    CuntzP6MWallpaperBoundary.sectorArity
      CuntzP6MWallpaperBoundary.PrimeSector.p2 = 2 ∧
    CuntzP6MWallpaperBoundary.sectorArity
      CuntzP6MWallpaperBoundary.PrimeSector.p3 = 3 ∧
    CuntzP6MWallpaperBoundary.sectorArity
      CuntzP6MWallpaperBoundary.PrimeSector.p5 = 5 := by
  constructor
  · exact lorentzBoost_zero X
  constructor
  · exact gamma_zero
  constructor
  · exact qOfRapidity_zero ℏ
  constructor
  · exact safeDispersionFactor_zero
  constructor
  · exact modifiedDispersionToy_zero_factor E p c m₀
  constructor
  · exact BuresInformationGeodesicFlow.modularFlow_zero_time K A
  constructor
  · exact CuntzP6MWallpaperBoundary.sectorArity_p2
  constructor
  · exact CuntzP6MWallpaperBoundary.sectorArity_p3
  · exact CuntzP6MWallpaperBoundary.sectorArity_p5

#check thermal_boost_lorentz_superalgebra_synthesis

end ThermalBoostLorentzSuperalgebra

end noncomputable section
