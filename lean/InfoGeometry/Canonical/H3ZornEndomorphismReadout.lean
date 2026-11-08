import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Canonical.H3ZornCoordinateBasisBridge

/-! Faithful coordinate readout for endomorphisms of the certified H3Zorn carrier. -/

namespace InfoGeometry.Canonical.H3ZornEndomorphismReadout

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornBasis

abbrev EndH3 := Module.End ℝ (H3Zorn ℝ)
abbrev ActionCoord := Fin 27 → Fin 27 → ℝ

def readout (D : EndH3) : ActionCoord := fun r c =>
  (h3ZornCoordinateBasis.repr (D (h3ZornCoordinateBasis r))) c

def readoutLinear : EndH3 →ₗ[ℝ] ActionCoord where
  toFun := readout
  map_add' D E := by
    funext r c
    simp [readout]
  map_smul' a D := by
    funext r c
    simp [readout]

theorem readout_injective : Function.Injective readoutLinear := by
  intro D E h
  apply LinearMap.ext
  intro X
  rw [← h3ZornCoordinateBasis.sum_repr X]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r hr
  have heq : D (h3ZornCoordinateBasis r) = E (h3ZornCoordinateBasis r) := by
    apply h3ZornCoordinateBasis.repr.injective
    ext c
    exact congrFun (congrFun h r) c
  exact congrArg (fun z : H3Zorn ℝ =>
    (h3ZornCoordinateBasis.repr X r) • z) heq

end
end InfoGeometry.Canonical.H3ZornEndomorphismReadout
