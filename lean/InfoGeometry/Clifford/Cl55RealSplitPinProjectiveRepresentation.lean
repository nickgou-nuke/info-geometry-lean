import InfoGeometry.Clifford.Cl55RealSplitPinAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl55ProjectiveBoundary
import InfoGeometry.Canonical.ProjectiveFoundation

namespace InfoGeometry.Clifford.Clifford55

/-!
# Projective representation of the native real split-Pin action

The real split-Pin subgroup already acts by genuine orthogonal linear
equivalences on `V55`.  This file exposes the same action through the
repository's projective-representation owner and its induced action on
`ℙ ℝ V55`.  No coordinate quotient or scalar matrix model is introduced.
-/

noncomputable section

open InfoGeometry.Canonical.ProjectiveFoundation
open InfoGeometry.Canonical.Cl55ProjectiveBoundary
open scoped LinearAlgebra.Projectivization

noncomputable def realSplitPinV55LinearAction :
    realSplitPin55 →* (V55 ≃ₗ[ℝ] V55) where
  toFun := realSplitPinTwistedActionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change realSplitPinTwistedAction (1 : realSplitPin55) v = v
    rw [realSplitPinTwistedAction_one]
    rfl
  map_mul' := by
    intro g h
    exact realSplitPinTwistedActionEquiv_mul g h

noncomputable def realSplitPinProjectiveRepresentation :
    ProjectiveRepresentation ℝ realSplitPin55 V55 :=
  ProjectiveRepresentation.ofLinearHom realSplitPinV55LinearAction

@[simp] theorem realSplitPinProjectiveRepresentation_multiplier
    (g h : realSplitPin55) :
    realSplitPinProjectiveRepresentation.multiplier g h = 1 :=
  rfl

theorem realSplitPinProjectiveRepresentation_map_mul
    (g h : realSplitPin55) (v : V55) :
    realSplitPinProjectiveRepresentation (g * h) v =
      realSplitPinProjectiveRepresentation g
        (realSplitPinProjectiveRepresentation h v) := by
  have hmul := congrArg (fun e : V55 ≃ₗ[ℝ] V55 => e v)
    (realSplitPinTwistedActionEquiv_mul g h)
  simpa [realSplitPinProjectiveRepresentation,
    realSplitPinV55LinearAction] using hmul

noncomputable def realSplitPinProjectivizationAction :
    realSplitPin55 →* Function.End (ℙ ℝ V55) :=
  realSplitPinProjectiveRepresentation.projectivizationAction

theorem realSplitPinProjectivizationAction_map_mul
    (g h : realSplitPin55) :
    realSplitPinProjectivizationAction (g * h) =
      realSplitPinProjectivizationAction g ∘
        realSplitPinProjectivizationAction h := by
  exact realSplitPinProjectiveRepresentation.projectivizationMap_mul g h

/-! ## Native Mathlib action surface -/

noncomputable instance realSplitPinProjectivizationMulAction :
    MulAction realSplitPin55 (ℙ ℝ V55) where
  smul := fun g p =>
    realSplitPinProjectiveRepresentation.projectivizationMap g p
  one_smul := by
    intro p
    exact congrFun
      realSplitPinProjectiveRepresentation.projectivizationMap_one p
  mul_smul := by
    intro g h p
    change realSplitPinProjectiveRepresentation.projectivizationMap (g * h) p =
      realSplitPinProjectiveRepresentation.projectivizationMap g
        (realSplitPinProjectiveRepresentation.projectivizationMap h p)
    rw [realSplitPinProjectiveRepresentation.projectivizationMap_mul]
    rfl

@[simp]
theorem realSplitPinProjectivization_smul_eq
    (g : realSplitPin55) (p : ℙ ℝ V55) :
    g • p = realSplitPinProjectiveRepresentation.projectivizationMap g p :=
  rfl

theorem realSplitPinProjectivization_preserves_null
    (g : realSplitPin55) (p : ℙ ℝ V55)
    (hp : IsProjectiveNull Q55 p) :
    IsProjectiveNull Q55
      (realSplitPinProjectiveRepresentation.projectivizationMap g p) := by
  induction p using Projectivization.ind with
  | h v hv =>
      change Q55 v = 0 at hp
      rw [ProjectiveRepresentation.projectivizationMap_mk]
      change Q55 (realSplitPinTwistedActionEquiv g v) = 0
      change Q55 (realSplitPinTwistedAction g v) = 0
      rw [realSplitPinTwistedAction_preserves_Q55, hp]

theorem realSplitPinProjectivization_smul_preserves_null
    (g : realSplitPin55) (p : ℙ ℝ V55)
    (hp : IsProjectiveNull Q55 p) :
    IsProjectiveNull Q55 (g • p) := by
  change IsProjectiveNull Q55
    (realSplitPinProjectiveRepresentation.projectivizationMap g p)
  exact realSplitPinProjectivization_preserves_null g p hp

end

end InfoGeometry.Clifford.Clifford55
