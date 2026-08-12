import proofs.CanonicalZornIntegralTrialityEquivariance
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Integral Zorn composition algebra

The integral Zorn carrier was previously used only as the quadratic lattice
`II₄,₄`.  This file equips it with the actual integral dot, cross,
conjugation, and Zorn multiplication operations.  Scalar extension is proved
to agree with both the real and canonical complex Zorn products, and the norm
composition identity is descended back to `ℤ`.
-/

noncomputable section

namespace IntegralZornCompositionAlgebra

set_option maxHeartbeats 800000

open IntegralZornII44Bridge
open CanonicalZornProjectiveTKKBridge
open CanonicalZornCompositionTriality
open CanonicalZornIntegralTrialityEquivariance
open CanonicalZornIntegralSpinTrialityClosure
open CanonicalZornCliffordRepresentation
open InfoGeometry.Physics.SplitOctonionBraidSU3

def integralDot3 (u v : Fin 3 → ℤ) : ℤ :=
  ∑ i, u i * v i

def integralCross3 (u v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Integral Zorn multiplication with the same sign convention as the
canonical complex split-octonion algebra. -/
def integralZornMul (X Y : IntegralZorn) : IntegralZorn :=
  (X.a * Y.a + integralDot3 X.u Y.v,
    ((fun i => X.a * Y.u i + Y.b * X.u i -
        integralCross3 X.v Y.v i),
      ((fun i => Y.a * X.v i + X.b * Y.v i +
          integralCross3 X.u Y.u i),
        integralDot3 X.v Y.u + X.b * Y.b)))

def integralZornOne : IntegralZorn :=
  (1, (fun _ => 0), ((fun _ => 0), 1))

def integralZornConj (X : IntegralZorn) : IntegralZorn :=
  (X.b, (fun i => -X.u i), ((fun i => -X.v i), X.a))

theorem integralToCoreZorn_mul (X Y : IntegralZorn) :
    integralToCoreZorn (integralZornMul X Y) =
      integralToCoreZorn X * integralToCoreZorn Y := by
  apply ZornCore.Zorn.ext'
  · simp [integralToCoreZorn, integralZornMul, integralDot3,
      ZornCore.dot, Fin.sum_univ_three, IntegralZorn.a,
      IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
  · funext i
    fin_cases i <;>
      simp [integralToCoreZorn, integralZornMul, integralCross3,
        ZornCore.cross, IntegralZorn.a, IntegralZorn.u,
        IntegralZorn.v, IntegralZorn.b]
  · funext i
    fin_cases i <;>
      simp [integralToCoreZorn, integralZornMul, integralCross3,
        ZornCore.cross, IntegralZorn.a, IntegralZorn.u,
        IntegralZorn.v, IntegralZorn.b]
  · simp [integralToCoreZorn, integralZornMul, integralDot3,
      ZornCore.dot, Fin.sum_univ_three, IntegralZorn.a,
      IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]

theorem coreToCanonical_integralZornMul (X Y : IntegralZorn) :
    coreToCanonical (integralToCoreZorn (integralZornMul X Y)) =
      zornMul (coreToCanonical (integralToCoreZorn X))
        (coreToCanonical (integralToCoreZorn Y)) := by
  rw [integralToCoreZorn_mul, coreToCanonical_mul]

theorem integralToCoreZorn_conj (X : IntegralZorn) :
    integralToCoreZorn (integralZornConj X) =
      { a := (integralToCoreZorn X).b
        u := fun i => -(integralToCoreZorn X).u i
        v := fun i => -(integralToCoreZorn X).v i
        b := (integralToCoreZorn X).a } := by
  apply ZornCore.Zorn.ext'
  · rfl
  · funext i
    simp [integralToCoreZorn, integralZornConj,
      IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
  · funext i
    simp [integralToCoreZorn, integralZornConj,
      IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
  · rfl

theorem coreToCanonical_integralZornConj (X : IntegralZorn) :
    coreToCanonical (integralToCoreZorn (integralZornConj X)) =
      zornConj (coreToCanonical (integralToCoreZorn X)) := by
  apply zorn_ext
  · rfl
  · funext i
    simp [integralToCoreZorn, integralZornConj, coreToCanonical, zornConj,
      IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
  · funext i
    simp [integralToCoreZorn, integralZornConj, coreToCanonical, zornConj,
      IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
  · rfl

theorem integralZornConj_involutive (X : IntegralZorn) :
    integralZornConj (integralZornConj X) = X := by
  rcases X with ⟨a, u, v, b⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      simp [integralZornConj, IntegralZorn.u]
    · apply Prod.ext
      · funext i
        simp [integralZornConj, IntegralZorn.v]
      · rfl

theorem integralZornMul_one (X : IntegralZorn) :
    integralZornMul X integralZornOne = X := by
  rcases X with ⟨a, u, v, b⟩
  apply Prod.ext
  · simp [integralZornMul, integralZornOne, integralDot3,
      IntegralZorn.a, IntegralZorn.u,
      IntegralZorn.v, IntegralZorn.b]
  · apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [integralZornMul, integralZornOne, integralCross3,
          IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
    · apply Prod.ext
      · funext i
        fin_cases i <;>
          simp [integralZornMul, integralZornOne, integralCross3,
            IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
      · simp [integralZornMul, integralZornOne, integralDot3,
          IntegralZorn.a, IntegralZorn.u,
          IntegralZorn.v, IntegralZorn.b]

theorem integralZornOne_mul (X : IntegralZorn) :
    integralZornMul integralZornOne X = X := by
  rcases X with ⟨a, u, v, b⟩
  apply Prod.ext
  · simp [integralZornMul, integralZornOne, integralDot3,
      IntegralZorn.a, IntegralZorn.u,
      IntegralZorn.v, IntegralZorn.b]
  · apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [integralZornMul, integralZornOne, integralCross3,
          IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
    · apply Prod.ext
      · funext i
        fin_cases i <;>
          simp [integralZornMul, integralZornOne, integralCross3,
            IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
      · simp [integralZornMul, integralZornOne, integralDot3,
          IntegralZorn.a, IntegralZorn.u,
          IntegralZorn.v, IntegralZorn.b]

/-- The integral Zorn norm is a composition law. -/
theorem integralZornNorm_mul (X Y : IntegralZorn) :
    integralZornNorm (integralZornMul X Y) =
      integralZornNorm X * integralZornNorm Y := by
  have h := _root_.InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm_mul
    (coreToCanonical (integralToCoreZorn X))
    (coreToCanonical (integralToCoreZorn Y))
  rw [← coreToCanonical_integralZornMul,
    coreToCanonical_norm, integralToCoreZorn_det,
    coreToCanonical_norm, integralToCoreZorn_det,
    coreToCanonical_norm, integralToCoreZorn_det] at h
  exact_mod_cast h

theorem integralZornConj_mul_self (X : IntegralZorn) :
    integralZornMul (integralZornConj X) X =
      integralZornNorm X • integralZornOne := by
  rcases X with ⟨a, u, v, b⟩
  apply Prod.ext
  · simp [integralZornMul, integralZornConj, integralZornOne,
      integralZornNorm, integralDot3, Fin.sum_univ_three,
      IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
    ring
  · apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [integralZornMul, integralZornConj, integralZornOne,
          integralZornNorm, integralCross3, IntegralZorn.a,
          IntegralZorn.u, IntegralZorn.v, IntegralZorn.b] <;> ring
    · apply Prod.ext
      · funext i
        fin_cases i <;>
          simp [integralZornMul, integralZornConj, integralZornOne,
            integralZornNorm, integralCross3, IntegralZorn.a,
            IntegralZorn.u, IntegralZorn.v, IntegralZorn.b] <;> ring
      · simp [integralZornMul, integralZornConj, integralZornOne,
          integralZornNorm, integralDot3, Fin.sum_univ_three,
          IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
        ring

/-- The internal integral axis cycle is an automorphism of the full integral
Zorn multiplication, not merely an isometry of its norm. -/
theorem integralAxisCycle_mul (X Y : IntegralZorn) :
    integralAxisCycle (integralZornMul X Y) =
      integralZornMul (integralAxisCycle X) (integralAxisCycle Y) := by
  apply integralToCoreZorn_injective
  rw [integralToCoreZorn_axisCycle, integralToCoreZorn_mul,
    integralToCoreZorn_mul, integralToCoreZorn_axisCycle,
    integralToCoreZorn_axisCycle]
  apply coreToCanonical_injective
  rw [coreToCanonical_triality, coreToCanonical_mul,
    coreToCanonical_mul, coreToCanonical_triality,
    coreToCanonical_triality, canonicalTriality_mul]

/-- Integral composition-algebra and downstream geometric closure capstone. -/
theorem integral_zorn_composition_triality_fivegrade_projective_closure
    (X Y : IntegralZorn) (Ψ : DiracSpinor16) :
    integralZornNorm (integralZornMul X Y) =
      integralZornNorm X * integralZornNorm Y ∧
    integralAxisCycle (integralZornMul X Y) =
      integralZornMul (integralAxisCycle X) (integralAxisCycle Y) ∧
    integralZornNorm (integralAxisCycle X) = integralZornNorm X ∧
    CanonicalZornCompositionFiveGradeBridge.vectorGradePlus
        (CanonicalZornRealSpin44.realSplit44ToVector8
          (integralZornToRealSplit44 (integralAxisCycle X))) ∈
      CanonicalZornFiveGradedClosure.conformalGrade
        TKKJordanPairData.TKKGrade.p1 ∧
    ProjectiveAffineConformalClosure55.Q55
      (ProjectiveAffineConformalClosure55.conformalEmbed44to55
        (CanonicalZornRealSpin44.realSplit44ToPAC44
          (integralZornToRealSplit44 (integralAxisCycle X)))) = 0 := by
  exact ⟨integralZornNorm_mul X Y, integralAxisCycle_mul X Y,
    integralAxisCycle_norm X,
    (integral_axis_triality_clifford_fivegrade_projective_closure
      X Ψ).2.2.2.2.1,
    (integral_axis_triality_clifford_fivegrade_projective_closure
      X Ψ).2.2.2.2.2⟩

end IntegralZornCompositionAlgebra

end noncomputable section
