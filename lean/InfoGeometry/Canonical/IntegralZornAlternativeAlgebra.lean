import InfoGeometry.Canonical.ZornCore
import InfoGeometry.Canonical.IntegralZornII44Bridge
import InfoGeometry.Canonical.IntegralZornCompositionAlgebra
import InfoGeometry.Canonical.CanonicalZornCompositionTriality
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Alternativity and nonassociativity of the integral Zorn algebra

This file records the algebraic properties that distinguish the integral Zorn
composition law from an associative matrix algebra. The canonical complex
product is proved left- and right-alternative by coordinates; injective scalar
extension descends those identities to the integral algebra. A concrete
mixed upper/lower-lane witness proves genuine nonassociativity.
-/

noncomputable section

namespace InfoGeometry.Canonical.IntegralZornAlternativeAlgebra

set_option maxHeartbeats 1000000

open IntegralZornCompositionAlgebra
open IntegralZornII44Bridge
open CanonicalZornCompositionTriality
open InfoGeometry.Physics.SplitOctonionBraidSU3

/-! ## Canonical alternativity -/

theorem canonicalZorn_left_alternative (X Y : Zorn) :
    zornMul (zornMul X X) Y = zornMul X (zornMul X Y) := by
  apply zorn_ext
  · simp [zornMul, dot3, cross3]
    ring
  · funext i
    fin_cases i <;> simp [zornMul, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;> simp [zornMul, dot3, cross3] <;> ring
  · simp [zornMul, dot3, cross3]
    ring

theorem canonicalZorn_right_alternative (X Y : Zorn) :
    zornMul (zornMul X Y) Y = zornMul X (zornMul Y Y) := by
  apply zorn_ext
  · simp [zornMul, dot3, cross3]
    ring
  · funext i
    fin_cases i <;> simp [zornMul, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;> simp [zornMul, dot3, cross3] <;> ring
  · simp [zornMul, dot3, cross3]
    ring

theorem canonicalZorn_conj_mul (X Y : Zorn) :
    zornConj (zornMul X Y) =
      zornMul (zornConj Y) (zornConj X) := by
  apply zorn_ext
  · simp [zornConj, zornMul, dot3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, dot3, cross3] <;> ring
  · simp [zornConj, zornMul, dot3]
    ring

/-! ## Integral descent -/

theorem integralZorn_left_alternative (X Y : IntegralZorn) :
    integralZornMul (integralZornMul X X) Y =
      integralZornMul X (integralZornMul X Y) := by
  apply integralToCoreZorn_injective
  apply InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_injective
  have hXXY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    (integralZornMul X X) Y
  have hX_XY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    X (integralZornMul X Y)
  have hXX := IntegralZornCompositionAlgebra.integralToCoreZorn_mul X X
  have hXY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul X Y
  rw [hXXY, hX_XY,
    hXX, hXY,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_left_alternative
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn X))
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn Y))

theorem integralZorn_right_alternative (X Y : IntegralZorn) :
    integralZornMul (integralZornMul X Y) Y =
      integralZornMul X (integralZornMul Y Y) := by
  apply integralToCoreZorn_injective
  apply InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_injective
  have hXY_Y := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    (integralZornMul X Y) Y
  have hX_YY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    X (integralZornMul Y Y)
  have hXY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul X Y
  have hYY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul Y Y
  rw [hXY_Y, hX_YY,
    hXY, hYY,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_right_alternative
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn X))
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn Y))

theorem integralZornConj_mul (X Y : IntegralZorn) :
    integralZornConj (integralZornMul X Y) =
      integralZornMul (integralZornConj Y) (integralZornConj X) := by
  apply integralToCoreZorn_injective
  apply InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_injective
  have h1 := coreToCanonical_integralZornConj (integralZornMul X Y)
  have h2 := coreToCanonical_integralZornMul (integralZornConj Y) (integralZornConj X)
  rw [h1, h2,
    coreToCanonical_integralZornMul,
    coreToCanonical_integralZornConj,
    coreToCanonical_integralZornConj]
  exact canonicalZorn_conj_mul
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn X))
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn Y))

/-! ## Explicit nonassociativity witness -/

def integralUpper (u : Fin 3 → ℤ) : IntegralZorn :=
  (0, u, ((fun _ => 0), 0))

def integralLower (v : Fin 3 → ℤ) : IntegralZorn :=
  (0, (fun _ => 0), (v, 0))

def integralE1 : Fin 3 → ℤ := ![1, 0, 0]
def integralE2 : Fin 3 → ℤ := ![0, 1, 0]

def integralAssociator (X Y Z : IntegralZorn) : IntegralZorn :=
  integralZornMul (integralZornMul X Y) Z -
    integralZornMul X (integralZornMul Y Z)

theorem integral_mixed_associator_coordinate :
    (integralAssociator
      (integralUpper integralE1)
      (integralLower integralE1)
      (integralUpper integralE2)).u 1 = 1 := by
  norm_num [integralAssociator, integralUpper, integralLower,
    integralE1, integralE2, integralZornMul, integralDot3,
    integralCross3, IntegralZornII44Bridge.IntegralZorn.a,
    IntegralZornII44Bridge.IntegralZorn.u,
    IntegralZornII44Bridge.IntegralZorn.v,
    IntegralZornII44Bridge.IntegralZorn.b, Fin.sum_univ_three]
  all_goals rfl

theorem integralZorn_not_associative :
    ∃ X Y Z : IntegralZorn,
      integralZornMul (integralZornMul X Y) Z ≠
        integralZornMul X (integralZornMul Y Z) := by
  refine ⟨integralUpper integralE1, integralLower integralE1,
    integralUpper integralE2, ?_⟩
  intro h
  have hu := congrArg (fun W : IntegralZorn => W.u 1) h
  change
    (integralZornMul
        (integralZornMul (integralUpper integralE1)
          (integralLower integralE1))
        (integralUpper integralE2)).u 1 =
      (integralZornMul (integralUpper integralE1)
        (integralZornMul (integralLower integralE1)
          (integralUpper integralE2))).u 1 at hu
  have ha := integral_mixed_associator_coordinate
  change
    (integralZornMul
        (integralZornMul (integralUpper integralE1)
          (integralLower integralE1))
        (integralUpper integralE2)).u 1 -
      (integralZornMul (integralUpper integralE1)
        (integralZornMul (integralLower integralE1)
          (integralUpper integralE2))).u 1 = 1 at ha
  rw [hu] at ha
  norm_num at ha

end InfoGeometry.Canonical.IntegralZornAlternativeAlgebra

end noncomputable section
