import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralBasisChangeMatrix

namespace InfoGeometry.Topology

noncomputable section

abbrev RealChiralBasisCoordinates := InfoGeometry.Algebra.FiniteSpin.Vec8R

/-!
The scalar extension of the rational chiral/native soldering matrix.  The
coordinate order is the one used by the canonical matrix owner:
`(α, x₀, x₁, x₂, β, y₀, y₁, y₂)` to `(1, ℓ, i, iℓ, j, jℓ, k, kℓ)`.
-/
def realChiralToNative : RealChiralBasisCoordinates ≃ₜ RealChiralBasisCoordinates where
  toFun c := fun i => match i with
    | 0 => (c 0 + c 4) / 2
    | 1 => (c 0 - c 4) / 2
    | 2 => (-c 1 + c 5) / 2
    | 3 => (c 1 + c 5) / 2
    | 4 => (-c 2 + c 6) / 2
    | 5 => (c 2 + c 6) / 2
    | 6 => (-c 3 + c 7) / 2
    | 7 => (c 3 + c 7) / 2
  invFun d := fun i => match i with
    | 0 => d 0 + d 1
    | 1 => d 3 - d 2
    | 2 => d 5 - d 4
    | 3 => d 7 - d 6
    | 4 => d 0 - d 1
    | 5 => d 3 + d 2
    | 6 => d 5 + d 4
    | 7 => d 7 + d 6
  left_inv := by
    intro c
    funext i
    fin_cases i <;> simp <;> ring
  right_inv := by
    intro d
    funext i
    fin_cases i <;> simp <;> ring
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem realChiralToNative_apply_zero (c : RealChiralBasisCoordinates) :
    realChiralToNative c 0 = (c 0 + c 4) / 2 := rfl

@[simp] theorem realChiralToNative_apply_one (c : RealChiralBasisCoordinates) :
    realChiralToNative c 1 = (c 0 - c 4) / 2 := rfl

theorem realChiralToNative_matches_matrix (c : RealChiralBasisCoordinates) :
    realChiralToNative c = fun i =>
      match i with
      | 0 => (c 0 + c 4) / 2
      | 1 => (c 0 - c 4) / 2
      | 2 => (-c 1 + c 5) / 2
      | 3 => (c 1 + c 5) / 2
      | 4 => (-c 2 + c 6) / 2
      | 5 => (c 2 + c 6) / 2
      | 6 => (-c 3 + c 7) / 2
      | 7 => (c 3 + c 7) / 2 := by
  funext i
  fin_cases i <;> rfl

theorem realChiralToNative_isEmbedding :
    Function.Injective (realChiralToNative : RealChiralBasisCoordinates → RealChiralBasisCoordinates) :=
  realChiralToNative.injective

end
end InfoGeometry.Topology
