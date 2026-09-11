import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The doubled Peirce complex structure

The real Peirce carrier has no canonical square root of `-1`.  Its doubled
carrier does: the standard rotation of the two copies is a genuine real
linear complex structure.  This is the concrete algebraic predecessor for a
DIII time-reversal operator; no identification with an abstract `Op` is made.
-/

namespace InfoGeometry.Lie.PeirceDoubledComplexStructure

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

abbrev DoubledPeirce := PeirceCarrier × PeirceCarrier

def theta : DoubledPeirce →ₗ[ℝ] DoubledPeirce where
  toFun x := (-x.2, x.1)
  map_add' x y := by
    ext <;> simp; abel
  map_smul' c x := by
    ext <;> simp

theorem theta_apply (x : DoubledPeirce) :
    theta x = (-x.2, x.1) := rfl

theorem theta_sq : theta.comp theta = -LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rfl

theorem theta_sq_apply (x : DoubledPeirce) :
    theta (theta x) = -x := by
  have h := congrArg (fun T : DoubledPeirce →ₗ[ℝ] DoubledPeirce => T x)
    theta_sq
  simpa [LinearMap.comp_apply] using h

def xi : DoubledPeirce →ₗ[ℝ] DoubledPeirce where
  toFun x := (x.1, -x.2)
  map_add' x y := by
    ext <;> simp; abel
  map_smul' c x := by
    ext <;> simp

def chi : DoubledPeirce →ₗ[ℝ] DoubledPeirce := theta.comp xi

theorem xi_sq : xi.comp xi = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [xi, LinearMap.comp_apply]

theorem theta_xi_anticommute :
    theta.comp xi = -(xi.comp theta) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [theta, xi, LinearMap.comp_apply]

theorem chi_sq : chi.comp chi = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [chi, theta, xi, LinearMap.comp_apply]

theorem chi_eq_theta_comp_xi : chi = theta.comp xi := rfl

/-! The doubled carrier is finite-dimensional, so the same operators admit
continuous-linear realizations without changing their underlying maps. -/

noncomputable def thetaCLM : DoubledPeirce →L[ℝ] DoubledPeirce :=
  LinearMap.toContinuousLinearMap theta

noncomputable def xiCLM : DoubledPeirce →L[ℝ] DoubledPeirce :=
  LinearMap.toContinuousLinearMap xi

noncomputable def chiCLM : DoubledPeirce →L[ℝ] DoubledPeirce :=
  LinearMap.toContinuousLinearMap chi

@[simp] theorem thetaCLM_toLinearMap :
    thetaCLM.toLinearMap = theta := rfl

@[simp] theorem xiCLM_toLinearMap :
    xiCLM.toLinearMap = xi := rfl

@[simp] theorem chiCLM_toLinearMap :
    chiCLM.toLinearMap = chi := rfl

theorem thetaCLM_sq : thetaCLM.comp thetaCLM =
  -(ContinuousLinearMap.id ℝ DoubledPeirce) := by
  apply DFunLike.ext _ _
  intro p
  change theta (theta p) = -p
  exact theta_sq_apply p

theorem xiCLM_sq : xiCLM.comp xiCLM =
  ContinuousLinearMap.id ℝ DoubledPeirce := by
  apply DFunLike.ext _ _
  intro p
  change xi (xi p) = p
  have h := congrArg (fun T : DoubledPeirce →ₗ[ℝ] DoubledPeirce => T p) xi_sq
  simpa [LinearMap.comp_apply] using h

theorem chiCLM_sq : chiCLM.comp chiCLM =
  ContinuousLinearMap.id ℝ DoubledPeirce := by
  apply DFunLike.ext _ _
  intro p
  change chi (chi p) = p
  have h := congrArg (fun T : DoubledPeirce →ₗ[ℝ] DoubledPeirce => T p) chi_sq
  simpa [LinearMap.comp_apply] using h

end InfoGeometry.Lie.PeirceDoubledComplexStructure
