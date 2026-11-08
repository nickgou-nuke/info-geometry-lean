import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Cl55SpinorCartanFock

noncomputable section
namespace InfoGeometry.Physics.Cl55PinorChiralSwapBridge

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Physics.Cl55SpinorCartanFock

def IsPlusChiral (ψ : Spinor32) : Prop := gammaChiral *ᵥ ψ = ψ
def IsMinusChiral (ψ : Spinor32) : Prop := gammaChiral *ᵥ ψ = -ψ

theorem anticommuting_operator_maps_plus_to_minus
    (X : MatStage 5) (hX : gammaChiral * X = -(X * gammaChiral))
    {ψ : Spinor32} (hψ : IsPlusChiral ψ) :
    IsMinusChiral (X *ᵥ ψ) := by
  unfold IsPlusChiral at hψ
  unfold IsMinusChiral
  rw [Matrix.mulVec_mulVec, hX]
  simp only [Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec, hψ]

theorem anticommuting_operator_maps_minus_to_plus
    (X : MatStage 5) (hX : gammaChiral * X = -(X * gammaChiral))
    {ψ : Spinor32} (hψ : IsMinusChiral ψ) :
    IsPlusChiral (X *ᵥ ψ) := by
  unfold IsMinusChiral at hψ
  unfold IsPlusChiral
  rw [Matrix.mulVec_mulVec, hX]
  simp only [Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec, hψ]
  simp [Matrix.mulVec_neg]

theorem creation_maps_plus_to_minus (a : Fin 5) {ψ : Spinor32}
    (hψ : IsPlusChiral ψ) : IsMinusChiral (e a *ᵥ ψ) :=
  anticommuting_operator_maps_plus_to_minus (e a) (gammaChiral_e_anticomm a) hψ

theorem creation_maps_minus_to_plus (a : Fin 5) {ψ : Spinor32}
    (hψ : IsMinusChiral ψ) : IsPlusChiral (e a *ᵥ ψ) :=
  anticommuting_operator_maps_minus_to_plus (e a) (gammaChiral_e_anticomm a) hψ

theorem annihilation_maps_plus_to_minus (a : Fin 5) {ψ : Spinor32}
    (hψ : IsPlusChiral ψ) : IsMinusChiral (f a *ᵥ ψ) :=
  anticommuting_operator_maps_plus_to_minus (f a) (gammaChiral_f_anticomm a) hψ

theorem annihilation_maps_minus_to_plus (a : Fin 5) {ψ : Spinor32}
    (hψ : IsMinusChiral ψ) : IsPlusChiral (f a *ᵥ ψ) :=
  anticommuting_operator_maps_minus_to_plus (f a) (gammaChiral_f_anticomm a) hψ

theorem odd_creation_swaps_plus_to_minus (a : Fin 5) (ψ : Spinor32)
    (hψ : gammaChiral *ᵥ ψ = ψ) : gammaChiral *ᵥ (e a *ᵥ ψ) = -(e a *ᵥ ψ) :=
  creation_maps_plus_to_minus a hψ

theorem odd_creation_swaps_minus_to_plus (a : Fin 5) (ψ : Spinor32)
    (hψ : gammaChiral *ᵥ ψ = -ψ) : gammaChiral *ᵥ (e a *ᵥ ψ) = e a *ᵥ ψ :=
  creation_maps_minus_to_plus a hψ

theorem odd_annihilation_swaps_plus_to_minus (a : Fin 5) (ψ : Spinor32)
    (hψ : gammaChiral *ᵥ ψ = ψ) : gammaChiral *ᵥ (f a *ᵥ ψ) = -(f a *ᵥ ψ) :=
  annihilation_maps_plus_to_minus a hψ

theorem odd_annihilation_swaps_minus_to_plus (a : Fin 5) (ψ : Spinor32)
    (hψ : gammaChiral *ᵥ ψ = -ψ) : gammaChiral *ᵥ (f a *ᵥ ψ) = f a *ᵥ ψ :=
  annihilation_maps_minus_to_plus a hψ

end InfoGeometry.Physics.Cl55PinorChiralSwapBridge
