import InfoGeometry.KK.GradedEigenspaceBridge
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

namespace InfoGeometry.Krein.RealPlaneMatrixBridge

open InfoGeometry.Clifford.Cl11Matrix

abbrev Plane := HilbertDoubled ℝ

local instance planeGrading : KreinGradedModule Plane :=
  instKreinGradedModuleHilbertDoubled (E := ℝ)

def coordinates : Plane ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun vector := ![(HilbertDoubled.ofLp vector).1, (HilbertDoubled.ofLp vector).2]
  invFun vector := HilbertDoubled.toLp (vector 0, vector 1)
  left_inv vector := by
    apply HilbertDoubled.ext
    rfl
  right_inv vector := by
    ext index
    fin_cases index <;> rfl
  map_add' first second := by
    ext index
    fin_cases index <;> rfl
  map_smul' scalar vector := by
    ext index
    fin_cases index <;> rfl

def endToMatrix : Module.End ℝ Plane ≃ₐ[ℝ] Mat2 :=
  (coordinates.conjAlgEquiv ℝ).trans LinearMap.toMatrixAlgEquiv'

theorem fundamental_matrix :
    endToMatrix (KreinSpace.jCLM (H := Plane)).toLinearMap = Eplus := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [endToMatrix, LinearMap.toMatrixAlgEquiv'_apply,
      LinearEquiv.conjAlgEquiv_apply, coordinates, Eplus]

theorem grading_matrix :
    endToMatrix (KreinGradedModule.gradeCLM (H := Plane)).toLinearMap = J1 := by
  rw [gradeCLM_eq_hilbertSwapCLM (E := ℝ)]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [endToMatrix, LinearMap.toMatrixAlgEquiv'_apply,
      LinearEquiv.conjAlgEquiv_apply, coordinates, J1]

theorem rotation_matrix :
    endToMatrix (hilbertComplexI (E := ℝ)).toLinearMap = -Eminus := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [endToMatrix, LinearMap.toMatrixAlgEquiv'_apply,
      LinearEquiv.conjAlgEquiv_apply, coordinates, Eminus]

def dirac (parameter : ℝ) : Plane →L[ℝ] Plane :=
  parameter • KreinSpace.jCLM

theorem dirac_selfAdjoint (parameter : ℝ) :
    KreinSpace.kreinAdjoint (dirac parameter) = dirac parameter := by
  simp [dirac, kreinAdjoint_jCLM_hilbert]

theorem dirac_odd (parameter : ℝ) :
    KreinGradedModule.IsOdd (dirac parameter) := by
  apply ContinuousLinearMap.ext
  intro vector
  unfold KreinGradedModule.gradeConj
  rw [gradeCLM_eq_hilbertSwapCLM (E := ℝ)]
  apply coordinates.injective
  ext index
  fin_cases index <;>
    simp [dirac, coordinates]

def pairedEigenspaces (parameter eigenvalue : ℝ) :
    Module.End.eigenspace (dirac parameter).toLinearMap eigenvalue ≃ₗ[ℝ]
      Module.End.eigenspace (dirac parameter).toLinearMap (-eigenvalue) :=
  InfoGeometry.KK.GradedEigenspaceBridge.oddEigenspaceEquiv
    (dirac parameter) (dirac_odd parameter) eigenvalue

theorem dirac_kernel_of_ne_zero (parameter : ℝ) (hnonzero : parameter ≠ 0) :
    LinearMap.ker (dirac parameter).toLinearMap = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro first second hequal
  have hmetric : KreinSpace.jCLM first = KreinSpace.jCLM second :=
    (smul_right_injective Plane hnonzero) hequal
  exact (KreinSpace.J (H := Plane)).injective hmetric

theorem dirac_kernel_at_zero :
    LinearMap.ker (dirac 0).toLinearMap = ⊤ := by
  simp [dirac]

end InfoGeometry.Krein.RealPlaneMatrixBridge
