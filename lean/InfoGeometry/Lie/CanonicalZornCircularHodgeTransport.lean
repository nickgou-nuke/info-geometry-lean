import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Lie.PeirceExteriorHodgeTransport
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Circular Hodge and Chirality Transport to the Native Zorn Carrier

This module transports the `1 + 3 + 3 + 1` Hodge involution and graded
chirality from circular Peirce coordinates to the native Zorn carrier
`ZornMatrix ℝ`.

By bundling the coordinate equivalence into the algebra isomorphism
`LinearEquiv.conjAlgEquiv`, all duality laws ($\star^2 = 1$), graded parity ($\Gamma^2 = 1$),
and the anticommutation identity ($\star\Gamma = -\Gamma\star$) are proved
point-free via `AlgEquiv` homomorphisms without point-wise `ext` unfolding.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornCircularHodgeTransport

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.PeirceExteriorHodgeTransport

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ
abbrev EndCoord := Module.End ℝ (Fin 8 → ℝ)

/-- The canonical algebra isomorphism transporting endomorphisms on circular
Peirce coordinates to endomorphisms on the native Zorn carrier. -/
def transportAlgEquiv : EndCoord ≃ₐ[ℝ] EndCZ :=
  circularPeirceBasis.equivFun.symm.conjAlgEquiv ℝ

/-- Hodge involution transported to the native canonical Zorn carrier. -/
def circularHodgeStar : EndCZ :=
  transportAlgEquiv peirceHodgeStar

/-- Graded chirality transported to the native canonical Zorn carrier. -/
def circularGradedChirality : EndCZ :=
  transportAlgEquiv peirceGradedChirality

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
    simp [-circularPeirceBasis_apply, circularHodgeIndex, Module.Basis.equivFun_self]

/-!
## Duality, Parity, and Anticommutation (Point-Free Proofs via AlgEquiv)
-/

/-- The transported three-dimensional Hodge star is an involution ($\star^2 = 1$). -/
theorem circularHodgeStar_sq :
    circularHodgeStar * circularHodgeStar = 1 := by
  rw [circularHodgeStar, ← map_mul, peirceHodgeStar_sq, map_one]

/-- Exponential/power form: $(\star)^2 = 1$. -/
theorem circularHodgeStar_pow_two :
    circularHodgeStar ^ 2 = 1 := by
  rw [sq, circularHodgeStar_sq]

/-- The transported graded chirality is an involution ($\Gamma^2 = 1$). -/
theorem circularGradedChirality_sq :
    circularGradedChirality * circularGradedChirality = 1 := by
  rw [circularGradedChirality, ← map_mul, peirceGradedChirality_sq, map_one]

/-- Exponential/power form: $(\Gamma)^2 = 1$. -/
theorem circularGradedChirality_pow_two :
    circularGradedChirality ^ 2 = 1 := by
  rw [sq, circularGradedChirality_sq]

/-- Hodge duality anticommutes with graded chirality on the native Zorn carrier:
$\star\Gamma = -(\Gamma\star)$. -/
theorem circularHodgeStar_gradedChirality_anticommutes :
    circularHodgeStar * circularGradedChirality =
      -(circularGradedChirality * circularHodgeStar) := by
  rw [circularHodgeStar, circularGradedChirality,
      ← map_mul, ← map_mul,
      peirceHodgeStar_gradedChirality_anticommutes,
      map_neg]

/-- The operator-level complex structure $K := \star\Gamma$ satisfies $K^2 = -1$. -/
theorem circularComplexStructure_sq :
    (circularHodgeStar * circularGradedChirality) *
    (circularHodgeStar * circularGradedChirality) = -1 := by
  have hanti : circularGradedChirality * circularHodgeStar =
      -(circularHodgeStar * circularGradedChirality) := by
    rw [← neg_neg (circularGradedChirality * circularHodgeStar),
        ← circularHodgeStar_gradedChirality_anticommutes]
  calc
    (circularHodgeStar * circularGradedChirality) * (circularHodgeStar * circularGradedChirality)
      = circularHodgeStar * (circularGradedChirality * circularHodgeStar) * circularGradedChirality := by
        simp only [mul_assoc]
    _ = circularHodgeStar * -(circularHodgeStar * circularGradedChirality) * circularGradedChirality := by
        rw [hanti]
    _ = - (circularHodgeStar * circularHodgeStar * (circularGradedChirality * circularGradedChirality)) := by
        simp only [mul_neg, neg_mul, mul_assoc]
    _ = - (1 * 1) := by
        rw [circularHodgeStar_sq, circularGradedChirality_sq]
    _ = -1 := by
        simp only [mul_one]

/-!
## Clifford Algebra Representation of the Hodge-Chirality Atom
-/

/-- The split 2D quadratic space governing the Hodge-Chirality Clifford atom. -/
def splitQuad2D : QuadraticForm ℝ (ℝ × ℝ) :=
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ) +
    QuadraticMap.linMulLin (LinearMap.snd ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)

@[simp] lemma splitQuad2D_apply (v : ℝ × ℝ) :
    splitQuad2D v = v.1 ^ 2 + v.2 ^ 2 := by
  simp [splitQuad2D, sq]

/-- The canonical linear generator map sending (u, v) to u • ⋆ + v • Γ. -/
def hodgeChiralityLinearMap : (ℝ × ℝ) →ₗ[ℝ] EndCZ where
  toFun v := v.1 • circularHodgeStar + v.2 • circularGradedChirality
  map_add' v w := by
    dsimp
    simp only [add_smul]
    abel
  map_smul' a v := by
    dsimp
    simp only [smul_add, mul_smul]

/-- The Clifford condition: (u • ⋆ + v • Γ)² = (u² + v²) • 1. -/
theorem hodge_chirality_clifford_condition (v : ℝ × ℝ) :
    hodgeChiralityLinearMap v * hodgeChiralityLinearMap v =
      (splitQuad2D v) • (1 : EndCZ) := by
  simp only [hodgeChiralityLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    add_mul, mul_add, smul_mul_smul, sq, splitQuad2D_apply]
  rw [circularHodgeStar_sq, circularGradedChirality_sq,
      circularHodgeStar_gradedChirality_anticommutes,
      smul_neg, mul_comm v.2 v.1]
  abel
  rw [← add_smul]

/-- The Universal Clifford Representation of the 1+3+3+1 Hodge atom on Zorn matrices. -/
def zornCliffordRepresentation :
    CliffordAlgebra splitQuad2D →ₐ[ℝ] EndCZ :=
  CliffordAlgebra.lift splitQuad2D ⟨hodgeChiralityLinearMap, hodge_chirality_clifford_condition⟩

end InfoGeometry.Lie.CanonicalZornCircularHodgeTransport

