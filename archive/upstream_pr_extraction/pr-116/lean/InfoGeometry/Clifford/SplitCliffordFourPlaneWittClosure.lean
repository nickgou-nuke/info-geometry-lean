import InfoGeometry.Clifford.Cl44Witt
import InfoGeometry.Clifford.Cl55CAROperatorLift
import InfoGeometry.Physics.SplitCliffordAlgebras
import InfoGeometry.Canonical.SplitCliffordTensorBridge

/-!
# Four split planes, Witt coordinates, and the recursive split Clifford tower

The paired vectors `(e i, f i)` are orthogonal quadratic planes in the
underlying `(4,4)` carrier.  The Clifford algebra, not the split-octonion
product, is where these planes become associative `Cl(1,1)` factors.
This file records the finite plane calculation, the existing Witt/CAR packet,
the native recursive tensor steps for `Cl(4,4)` and `Cl(5,5)`, and the genuine
operator-valued left regular representation already available for `Cl(5,5)`.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitCliffordFourPlaneWittClosure

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower
open SplitClifford

/-! ## The four orthogonal hyperbolic planes -/

def planeVector (i : Fin 4) (x : ℝ × ℝ) : Fin 8 → ℝ :=
  x.1 • eVec i + x.2 • fVec i

theorem planeVector_q (i : Fin 4) (x : ℝ × ℝ) :
    splitQ44 (planeVector i x) = x.1 * x.1 - x.2 * x.2 := by
  fin_cases i <;>
    simp [planeVector, eVec, fVec, splitQ44_apply]

theorem plane_decomposition (v : Fin 8 → ℝ) :
    v = planeVector 0 (v 0, v 4) + planeVector 1 (v 1, v 5) +
      planeVector 2 (v 2, v 6) + planeVector 3 (v 3, v 7) := by
  funext k
  fin_cases k <;>
    simp [planeVector, eVec, fVec]

theorem planeVector_isOrtho (i j : Fin 4) (hij : i ≠ j)
    (x y : ℝ × ℝ) :
    QuadraticMap.IsOrtho splitQ44 (planeVector i x) (planeVector j y) := by
  unfold QuadraticMap.IsOrtho
  fin_cases i <;> fin_cases j <;>
    simp [planeVector, eVec, fVec, splitQ44_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne, Fin.ext_iff] at hij ⊢ <;> ring

theorem four_plane_orthogonal_packet :
    ∀ i j : Fin 4, i ≠ j → ∀ x y : ℝ × ℝ,
      QuadraticMap.IsOrtho splitQ44 (planeVector i x) (planeVector j y) := by
  intro i j hij x y
  exact planeVector_isOrtho i j hij x y

/-! ## Witt/CAR coordinates (the native Cl(4,4) owner) -/

theorem witt_packet :
    (∀ i : Fin 4, a i * a i = 0) ∧
    (∀ i : Fin 4, adag i * adag i = 0) ∧
    (∀ i j : Fin 4, a i * adag j + adag j * a i =
      if i = j then 1 else 0) ∧
    (∀ i j : Fin 4, a i * a j + a j * a i = 0) ∧
    (∀ i j : Fin 4, adag i * adag j + adag j * adag i = 0) := by
  exact ⟨a_sq_zero, adag_sq_zero, witt_CAR,
    witt_annihilation_anticomm, witt_creation_anticomm⟩

/-! ## Native graded tensor steps -/

noncomputable abbrev cl44_tensor_step :
    SplitCl44Alg ≃ₐ[ℝ] SplitClNNTensorStep 3 :=
  splitCliffordTensorStepEquiv 3

noncomputable abbrev cl55_tensor_step :
    SplitCl55Alg ≃ₐ[ℝ] SplitClNNTensorStep 4 :=
  splitCliffordTensorStepEquiv 4

theorem cl44_tensor_step_head (x : ℝ × ℝ) :
    cl44_tensor_step (CliffordAlgebra.ι SplitCl44Quad (headPair 3 x)) =
      (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 x)
        ᵍ⊗ₜ (1 : CliffordAlgebra (InfoGeometry.CliffordTower.Qsplit 3)) := by
  exact splitCl44_headFactor x

theorem cl55_tensor_step_head (x : ℝ × ℝ) :
    cl55_tensor_step (CliffordAlgebra.ι SplitCl55Quad (headPair 4 x)) =
      (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 x)
        ᵍ⊗ₜ (1 : CliffordAlgebra (InfoGeometry.CliffordTower.Qsplit 4)) := by
  exact splitCl55_headFactor x

/-! ## Operator-valued chiral realization -/

def leftAction55RingHom : Clifford55.Cl55 →+* Cl55Operator where
  toFun := leftAction55
  map_one' := leftAction55_one
  map_mul' := leftAction55_mul
  map_zero' := leftAction55_zero
  map_add' := leftAction55_add

@[simp] theorem leftAction55RingHom_apply (a : Clifford55.Cl55) :
    leftAction55RingHom a = leftAction55 a := rfl

theorem operator_witt_CAR (i j : Fin 5) :
    leftAction55 (annihilation55 i) * leftAction55 (creation55 j) +
        leftAction55 (creation55 j) * leftAction55 (annihilation55 i) =
      if i = j then 1 else 0 :=
  cl55CAR_leftAction_anticommutator_general i j

end InfoGeometry.Clifford.SplitCliffordFourPlaneWittClosure
