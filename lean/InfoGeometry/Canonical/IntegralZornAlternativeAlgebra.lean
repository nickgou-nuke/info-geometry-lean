import InfoGeometry.Canonical.ZornCore
import InfoGeometry.Canonical.IntegralZornII44Bridge
import InfoGeometry.Canonical.IntegralZornCompositionAlgebra
import InfoGeometry.Canonical.CanonicalZornCompositionTriality
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge
import InfoGeometry.Algebra.ZornVectorMatrix
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
open CanonicalZornProjectiveTKKBridge
open InfoGeometry.Physics.SplitOctonionBraidSU3

/-! ## Canonical alternativity -/

def physicsToGenericZorn (X : Zorn) : InfoGeometry.Algebra.ZornVectorMatrix ℂ :=
  { a := X.a, v := X.u, w := X.v, b := X.b }

theorem physicsToGenericZorn_injective : Function.Injective physicsToGenericZorn := by
  intro X Y h
  apply zorn_ext
  · simpa [physicsToGenericZorn] using congrArg InfoGeometry.Algebra.ZornVectorMatrix.a h
  · simpa [physicsToGenericZorn] using congrArg InfoGeometry.Algebra.ZornVectorMatrix.v h
  · simpa [physicsToGenericZorn] using congrArg InfoGeometry.Algebra.ZornVectorMatrix.w h
  · simpa [physicsToGenericZorn] using congrArg InfoGeometry.Algebra.ZornVectorMatrix.b h

theorem physicsToGenericZorn_mul (X Y : Zorn) :
    physicsToGenericZorn (zornMul X Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X) (physicsToGenericZorn Y) := by
  ext
  · simp [physicsToGenericZorn, zornMul, dot3, cross3,
      InfoGeometry.Algebra.ZornVectorMatrix.mul,
      InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross,
      Fin.sum_univ_three]
  · rename_i i
    fin_cases i <;> simp [physicsToGenericZorn, zornMul, dot3, cross3,
      InfoGeometry.Algebra.ZornVectorMatrix.mul,
      InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross,
      Fin.sum_univ_three]
  · rename_i i
    fin_cases i <;> simp [physicsToGenericZorn, zornMul, dot3, cross3,
      InfoGeometry.Algebra.ZornVectorMatrix.mul,
      InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross,
      Fin.sum_univ_three]
  · simp [physicsToGenericZorn, zornMul, dot3, cross3,
      InfoGeometry.Algebra.ZornVectorMatrix.mul,
      InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross,
      Fin.sum_univ_three]

theorem physicsToGenericZorn_conj (X : Zorn) :
    physicsToGenericZorn (zornConj X) =
      InfoGeometry.Algebra.ZornVectorMatrix.conj (physicsToGenericZorn X) := by
  ext <;> simp [physicsToGenericZorn, zornConj, InfoGeometry.Algebra.ZornVectorMatrix.conj]

theorem canonicalZorn_left_alternative (X Y : Zorn) :
    zornMul (zornMul X X) Y = zornMul X (zornMul X Y) := by
  apply physicsToGenericZorn_injective
  rw [physicsToGenericZorn_mul, physicsToGenericZorn_mul, physicsToGenericZorn_mul,
    physicsToGenericZorn_mul]
  have h := InfoGeometry.Algebra.ZornVectorMatrix.associator_left_alternative
    (physicsToGenericZorn X) (physicsToGenericZorn Y)
  ext
  · have ha := congrArg InfoGeometry.Algebra.ZornVectorMatrix.a h
    have ha0 : ((InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn X))
        (physicsToGenericZorn Y)).a -
      (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn Y))).a) = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator,
        InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        sub_eq_add_neg, InfoGeometry.Algebra.ZornVectorMatrix.zero] using ha
    exact sub_eq_zero.mp ha0
  · rename_i i
    have hv := congrArg InfoGeometry.Algebra.ZornVectorMatrix.v h
    have hvi := congrArg (fun f : Fin 3 → ℂ => f i) hv
    have hi : ((InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn X))
        (physicsToGenericZorn Y)).v i -
      (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn Y))).v i) = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator,
        InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        sub_eq_add_neg, InfoGeometry.Algebra.ZornVectorMatrix.zero] using hvi
    exact sub_eq_zero.mp hi
  · rename_i i
    have hw := congrArg InfoGeometry.Algebra.ZornVectorMatrix.w h
    have hwi := congrArg (fun f : Fin 3 → ℂ => f i) hw
    have hi : ((InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn X))
        (physicsToGenericZorn Y)).w i -
      (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn Y))).w i) = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator,
        InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        sub_eq_add_neg, InfoGeometry.Algebra.ZornVectorMatrix.zero] using hwi
    exact sub_eq_zero.mp hi
  · have hb := congrArg InfoGeometry.Algebra.ZornVectorMatrix.b h
    have hb0 : ((InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn X))
        (physicsToGenericZorn Y)).b -
      (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn Y))).b) = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator,
        InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        sub_eq_add_neg, InfoGeometry.Algebra.ZornVectorMatrix.zero] using hb
    exact sub_eq_zero.mp hb0

theorem canonicalZorn_right_alternative (X Y : Zorn) :
    zornMul (zornMul X Y) Y = zornMul X (zornMul Y Y) := by
  apply physicsToGenericZorn_injective
  rw [physicsToGenericZorn_mul, physicsToGenericZorn_mul, physicsToGenericZorn_mul,
    physicsToGenericZorn_mul]
  have h := InfoGeometry.Algebra.ZornVectorMatrix.associator_right_alternative
    (physicsToGenericZorn X) (physicsToGenericZorn Y)
  ext
  · have ha := congrArg InfoGeometry.Algebra.ZornVectorMatrix.a h
    have ha0 : ((InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn Y))
        (physicsToGenericZorn Y)).a -
      (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn Y)
          (physicsToGenericZorn Y))).a) = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator,
        InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        sub_eq_add_neg, InfoGeometry.Algebra.ZornVectorMatrix.zero] using ha
    exact sub_eq_zero.mp ha0
  · rename_i i
    have hv := congrArg InfoGeometry.Algebra.ZornVectorMatrix.v h
    have hvi := congrArg (fun f : Fin 3 → ℂ => f i) hv
    have hi : ((InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn Y))
        (physicsToGenericZorn Y)).v i -
      (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn Y)
          (physicsToGenericZorn Y))).v i) = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator,
        InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        sub_eq_add_neg, InfoGeometry.Algebra.ZornVectorMatrix.zero] using hvi
    exact sub_eq_zero.mp hi
  · rename_i i
    have hw := congrArg InfoGeometry.Algebra.ZornVectorMatrix.w h
    have hwi := congrArg (fun f : Fin 3 → ℂ => f i) hw
    have hi : ((InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn Y))
        (physicsToGenericZorn Y)).w i -
      (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn Y)
          (physicsToGenericZorn Y))).w i) = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator,
        InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        sub_eq_add_neg, InfoGeometry.Algebra.ZornVectorMatrix.zero] using hwi
    exact sub_eq_zero.mp hi
  · have hb := congrArg InfoGeometry.Algebra.ZornVectorMatrix.b h
    have hb0 : ((InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
          (physicsToGenericZorn Y))
        (physicsToGenericZorn Y)).b -
      (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn X)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (physicsToGenericZorn Y)
          (physicsToGenericZorn Y))).b) = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator,
        InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        sub_eq_add_neg, InfoGeometry.Algebra.ZornVectorMatrix.zero] using hb
    exact sub_eq_zero.mp hb0

theorem canonicalZorn_conj_mul (X Y : Zorn) :
    zornConj (zornMul X Y) =
      zornMul (zornConj Y) (zornConj X) := by
  apply physicsToGenericZorn_injective
  calc
    physicsToGenericZorn (zornConj (zornMul X Y))
        = InfoGeometry.Algebra.ZornVectorMatrix.conj
            (physicsToGenericZorn (zornMul X Y)) := by
            rw [physicsToGenericZorn_conj]
    _ = InfoGeometry.Algebra.ZornVectorMatrix.conj
          (InfoGeometry.Algebra.ZornVectorMatrix.mul
            (physicsToGenericZorn X) (physicsToGenericZorn Y)) := by
          rw [physicsToGenericZorn_mul]
    _ = InfoGeometry.Algebra.ZornVectorMatrix.mul
          (InfoGeometry.Algebra.ZornVectorMatrix.conj (physicsToGenericZorn Y))
          (InfoGeometry.Algebra.ZornVectorMatrix.conj (physicsToGenericZorn X)) := by
          simpa using
            (InfoGeometry.Algebra.ZornVectorMatrix.conj_mul
              (physicsToGenericZorn X) (physicsToGenericZorn Y))
    _ = physicsToGenericZorn (zornMul (zornConj Y) (zornConj X)) := by
          rw [physicsToGenericZorn_mul, physicsToGenericZorn_conj,
            physicsToGenericZorn_conj]

/-! ## Integral descent -/

theorem integralZorn_left_alternative (X Y : IntegralZorn) :
    integralZornMul (integralZornMul X X) Y =
      integralZornMul X (integralZornMul X Y) := by
  apply integralToCoreZorn_injective
  apply CanonicalZornProjectiveTKKBridge.coreToCanonical_injective
  simpa [coreToCanonical_integralZornMul] using canonicalZorn_left_alternative
    (coreToCanonical (integralToCoreZorn X))
    (coreToCanonical (integralToCoreZorn Y))

theorem integralZorn_right_alternative (X Y : IntegralZorn) :
    integralZornMul (integralZornMul X Y) Y =
      integralZornMul X (integralZornMul Y Y) := by
  apply integralToCoreZorn_injective
  apply CanonicalZornProjectiveTKKBridge.coreToCanonical_injective
  simpa [coreToCanonical_integralZornMul] using canonicalZorn_right_alternative
    (coreToCanonical (integralToCoreZorn X))
    (coreToCanonical (integralToCoreZorn Y))

theorem integralZornConj_mul (X Y : IntegralZorn) :
    integralZornConj (integralZornMul X Y) =
      integralZornMul (integralZornConj Y) (integralZornConj X) := by
  apply integralToCoreZorn_injective
  apply CanonicalZornProjectiveTKKBridge.coreToCanonical_injective
  simpa [coreToCanonical_integralZornConj, coreToCanonical_integralZornMul]
    using canonicalZorn_conj_mul
    (coreToCanonical (integralToCoreZorn X))
    (coreToCanonical (integralToCoreZorn Y))

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
