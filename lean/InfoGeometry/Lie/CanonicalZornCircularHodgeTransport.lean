import InfoGeometry.Lie.PeirceExteriorHodgeTransport
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Circular Hodge and chirality transport to the native Zorn carrier

The repository already owns the `1 + 3 + 3 + 1` Hodge involution and graded
chirality on the circular Peirce coordinate carrier.  This file transports
both operators through the actual Mathlib basis equivalence

`circularPeirceBasis.equivFun : ZornMatrix R ≃ₗ[R] (Fin 8 → R)`.

The resulting maps are genuine endomorphisms of the native real Zorn carrier.
No multiplicative compatibility with the nonassociative Zorn product is
asserted.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornCircularHodgeTransport

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.PeirceExteriorHodgeTransport

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- Hodge involution transported from circular Peirce coordinates to the
native canonical Zorn carrier. -/
def circularHodgeStar : EndCZ :=
  circularPeirceBasis.equivFun.symm.toLinearMap.comp
    (peirceHodgeStar.comp circularPeirceBasis.equivFun.toLinearMap)

/-- Graded chirality transported to the native canonical Zorn carrier. -/
def circularGradedChirality : EndCZ :=
  circularPeirceBasis.equivFun.symm.toLinearMap.comp
    (peirceGradedChirality.comp circularPeirceBasis.equivFun.toLinearMap)

/-- Index involution implementing `Λᵏ ↔ Λ³⁻ᵏ` in the established circular
Peirce order. -/
def circularHodgeIndex : Fin 8 → Fin 8 :=
  ![4, 5, 6, 7, 0, 1, 2, 3]

@[simp] theorem circularHodgeIndex_involutive (i : Fin 8) :
    circularHodgeIndex (circularHodgeIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem circularHodgeStar_apply (x : CZ) :
    circularHodgeStar x =
      circularPeirceBasis.equivFun.symm
        (peirceHodgeStar (circularPeirceBasis.equivFun x)) :=
  rfl

@[simp] theorem circularGradedChirality_apply (x : CZ) :
    circularGradedChirality x =
      circularPeirceBasis.equivFun.symm
        (peirceGradedChirality (circularPeirceBasis.equivFun x)) :=
  rfl

/-- Circular-coordinate readout of the native Hodge operator. -/
theorem circularHodgeStar_coordinate (x : CZ) :
    circularPeirceBasis.equivFun (circularHodgeStar x) =
      ![(circularPeirceBasis.equivFun x) 4,
        (circularPeirceBasis.equivFun x) 5,
        (circularPeirceBasis.equivFun x) 6,
        (circularPeirceBasis.equivFun x) 7,
        (circularPeirceBasis.equivFun x) 0,
        (circularPeirceBasis.equivFun x) 1,
        (circularPeirceBasis.equivFun x) 2,
        (circularPeirceBasis.equivFun x) 3] := by
  rw [circularHodgeStar_apply,
    LinearEquiv.apply_symm_apply,
    peirceHodgeStar_coordinate]

/-- The native Hodge operator sends each circular Peirce basis vector to its
complementary exterior degree. -/
theorem circularHodgeStar_basis (i : Fin 8) :
    circularHodgeStar (circularPeirceBasis i) =
      circularPeirceBasis (circularHodgeIndex i) := by
  apply circularPeirceBasis.equivFun.injective
  rw [circularHodgeStar_coordinate]
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [circularHodgeIndex, Basis.equivFun_self]

/-- The transported three-dimensional Hodge star is an involution. -/
theorem circularHodgeStar_sq :
    circularHodgeStar * circularHodgeStar = 1 := by
  apply LinearMap.ext
  intro x
  have hstar := LinearMap.congr_fun peirceHodgeStar_sq
    (circularPeirceBasis.equivFun x)
  change peirceHodgeStar
      (peirceHodgeStar (circularPeirceBasis.equivFun x)) =
    circularPeirceBasis.equivFun x at hstar
  change circularPeirceBasis.equivFun.symm
      (peirceHodgeStar
        (circularPeirceBasis.equivFun
          (circularPeirceBasis.equivFun.symm
            (peirceHodgeStar (circularPeirceBasis.equivFun x))))) = x
  rw [LinearEquiv.apply_symm_apply, hstar,
    LinearEquiv.symm_apply_apply]

/-- The transported graded chirality is an involution. -/
theorem circularGradedChirality_sq :
    circularGradedChirality * circularGradedChirality = 1 := by
  apply LinearMap.ext
  intro x
  have hchirality := LinearMap.congr_fun peirceGradedChirality_sq
    (circularPeirceBasis.equivFun x)
  change peirceGradedChirality
      (peirceGradedChirality (circularPeirceBasis.equivFun x)) =
    circularPeirceBasis.equivFun x at hchirality
  change circularPeirceBasis.equivFun.symm
      (peirceGradedChirality
        (circularPeirceBasis.equivFun
          (circularPeirceBasis.equivFun.symm
            (peirceGradedChirality (circularPeirceBasis.equivFun x))))) = x
  rw [LinearEquiv.apply_symm_apply, hchirality,
    LinearEquiv.symm_apply_apply]

/-- Hodge duality anticommutes with graded chirality after transport to the
native Zorn carrier. -/
theorem circularHodgeStar_gradedChirality_anticommutes :
    circularHodgeStar * circularGradedChirality =
      -(circularGradedChirality * circularHodgeStar) := by
  apply LinearMap.ext
  intro x
  apply circularPeirceBasis.equivFun.injective
  have hanti := LinearMap.congr_fun
    peirceHodgeStar_gradedChirality_anticommutes
    (circularPeirceBasis.equivFun x)
  change peirceHodgeStar
      (peirceGradedChirality (circularPeirceBasis.equivFun x)) =
    -peirceGradedChirality
      (peirceHodgeStar (circularPeirceBasis.equivFun x)) at hanti
  simpa [circularHodgeStar, circularGradedChirality,
    Module.End.mul_apply] using hanti

end InfoGeometry.Lie.CanonicalZornCircularHodgeTransport

