import InfoGeometry.Lie.CanonicalZornDerivationExponential
import InfoGeometry.Lie.CanonicalZornDerivationLane
import InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Differential transport for the canonical Zorn flow

The canonical Zorn carrier already owns its additive and module structures,
but not a global normed structure.  This module keeps the transported normed
structure local to the differential theorem.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationFlowDerivative

open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.Lie.ContinuousDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge

abbrev CZ := InfoGeometry.Lie.CanonicalZornDerivation.CZ
abbrev EndCZ := InfoGeometry.Lie.CanonicalZornDerivation.EndCZ
abbrev V8 := Fin 8 → ℝ

section

/-- The normed additive structure transported from the canonical coordinates.
The parent additive group is explicitly retained from `ZornSpinor`, avoiding
an instance diamond with the already-owned algebraic carrier. -/
local instance : NormedAddCommGroup CZ :=
  { NormedAddCommGroup.induced CZ V8 coordLE.toAddMonoidHom coordLE.injective with
    toAddCommGroup := inferInstance }

/-- The scalar action is the one already owned by the canonical carrier. -/
local instance : NormedSpace ℝ CZ :=
  NormedSpace.induced ℝ CZ V8 (coordLE : CZ →ₗ[ℝ] V8)

local instance : FiniteDimensional ℝ CZ :=
  coordLE.symm.finiteDimensional

/-- The coordinate Zorn flow has the transported strict derivative. -/
theorem hasStrictDerivAt_zornFlow
    (D : EndCZ) (X : CZ) (t : ℝ) :
    HasStrictDerivAt
      (fun s : ℝ => zornFlowLinearEquiv D s X)
      (D (zornFlowLinearEquiv D t X)) t := by
  have hbase := hasStrictDerivAt_orbit (coordEnd D) (coordLE X) t
  let hmap : V8 →L[ℝ] CZ :=
    LinearMap.toContinuousLinearMap (coordLE.symm : V8 →ₗ[ℝ] CZ)
  have htransport :=
    (hmap.hasStrictFDerivAt.comp t hbase.hasStrictFDerivAt).hasStrictDerivAt
  simpa [hmap, zornFlowLinearEquiv, ContinuousLinearMap.comp_apply,
    coordEnd_apply_coordLE] using htransport

/-- The transported flow has the canonical Zorn derivation as its generator
at time zero. -/
theorem deriv_zornFlow_at_zero
    (D : canonicalZornDerivations) (X : CZ) :
    deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t X) 0 = D.1 X := by
  have h := (hasStrictDerivAt_zornFlow D.1 X 0).hasDerivAt.deriv
  simpa using h

/-- The pointwise tangent action of the transported flow is the underlying
operator of its canonical derivation. -/
theorem deriv_zornFlow_operator_at_zero
    (D : canonicalZornDerivations) :
    (fun X : CZ => deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t X) 0) = D.1 := by
  funext X
  exact deriv_zornFlow_at_zero D X

theorem deriv_zornFlow_at_zero_add
    (D : canonicalZornDerivations) (X Y : CZ) :
    deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t (X + Y)) 0 =
      deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t X) 0 +
        deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t Y) 0 := by
  rw [deriv_zornFlow_at_zero, deriv_zornFlow_at_zero,
    deriv_zornFlow_at_zero]
  exact D.1.map_add X Y

theorem deriv_zornFlow_at_zero_smul
    (D : canonicalZornDerivations) (r : ℝ) (X : CZ) :
    deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t (r • X)) 0 =
      r • deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t X) 0 := by
  rw [deriv_zornFlow_at_zero, deriv_zornFlow_at_zero]
  exact D.1.map_smul r X

/-- The derivative at zero, assembled as a genuine linear operator on the
Zorn carrier. -/
noncomputable def zornFlowTangent (D : canonicalZornDerivations) :
    CZ →ₗ[ℝ] CZ where
  toFun X := deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t X) 0
  map_add' X Y := deriv_zornFlow_at_zero_add D X Y
  map_smul' r X := deriv_zornFlow_at_zero_smul D r X

/-- The assembled tangent operator is exactly the underlying canonical
derivation. -/
theorem zornFlowTangent_eq
    (D : canonicalZornDerivations) : zornFlowTangent D = D.1 := by
  apply LinearMap.ext
  intro X
  exact deriv_zornFlow_at_zero D X

/-- The assembled tangent operator belongs to the native derivation Lie
subalgebra. -/
theorem zornFlowTangent_mem_canonicalZornDerivations
    (D : canonicalZornDerivations) :
    zornFlowTangent D ∈ canonicalZornDerivations := by
  rw [zornFlowTangent_eq]
  exact D.property

/-- The tangent operator, packaged in the native derivation Lie carrier. -/
noncomputable def zornFlowTangentDerivation
    (D : canonicalZornDerivations) : canonicalZornDerivations :=
  ⟨zornFlowTangent D, zornFlowTangent_mem_canonicalZornDerivations D⟩

theorem zornFlowTangentDerivation_eq
    (D : canonicalZornDerivations) : zornFlowTangentDerivation D = D := by
  apply Subtype.ext
  exact zornFlowTangent_eq D

theorem zornFlowTangentDerivation_bracket
    (D E : canonicalZornDerivations) :
    zornFlowTangentDerivation (⁅D, E⁆ : canonicalZornDerivations) =
      ⁅zornFlowTangentDerivation D, zornFlowTangentDerivation E⁆ := by
  rw [zornFlowTangentDerivation_eq, zornFlowTangentDerivation_eq,
    zornFlowTangentDerivation_eq]

/-- The native multiplicative automorphism flow has the same infinitesimal
action as its underlying transported linear equivalence. -/
theorem deriv_zornFlowRealAut_apply_at_zero
    (D : canonicalZornDerivations) (X : CZ) :
    deriv (fun t : ℝ =>
      ((zornFlowRealAut D t : RealSplitOctonionAut) :
        SplitOctonionAutCandidate ℝ) X) 0 = D.1 X := by
  change deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t X) 0 = D.1 X
  exact deriv_zornFlow_at_zero D X

/-- Brackets of tangent generators read back as the native operator
commutator. -/
theorem zornFlowTangent_bracket_apply
    (D E : canonicalZornDerivations) (X : CZ) :
    zornFlowTangent (⁅D, E⁆ : canonicalZornDerivations) X =
      D.1 (E.1 X) - E.1 (D.1 X) := by
  rw [zornFlowTangent_eq]
  rfl

/-- At operator level, the tangent of the bracket flow is the native bracket
of the underlying endomorphisms. -/
theorem zornFlowTangent_bracket_eq
    (D E : canonicalZornDerivations) :
    zornFlowTangent (⁅D, E⁆ : canonicalZornDerivations) =
      ⁅D.1, E.1⁆ := by
  rw [zornFlowTangent_eq]
  rfl

/-- The tangent of the flow is the existing canonical derivation-lane action.
-/
theorem zornFlowTangent_eq_derivationLane_action
    (D : canonicalZornDerivations) (X : CZ) :
    zornFlowTangent D X =
      canonicalZornDerivationLane.operatorAction D X := by
  rw [canonicalZornDerivationLane_operatorAction, zornFlowTangent_eq]

/-- At operator level, the coordinate flow has its native derivation as
infinitesimal generator. -/
theorem deriv_coordFlow_at_zero
    (D : canonicalZornDerivations) :
    deriv (fun t : ℝ => flow (coordEnd D.1) t) 0 = coordEnd D.1 := by
  exact deriv_flow_at_zero (coordEnd D.1)

/-- Algebraic readback of the conjugated infinitesimal generator. -/
theorem coordEnd_symm_readback
    (D : EndCZ) (X : CZ) :
    coordLE.symm (coordEnd D (coordLE X)) = D X := by
  rw [coordEnd_apply_coordLE, coordLE.symm_apply_apply]

/-- The tangent action read back at zero satisfies the native Zorn Leibniz
law. -/
theorem deriv_zornFlow_at_zero_leibniz
    (D : canonicalZornDerivations) (X Y : CZ) :
    deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t (X * Y)) 0 =
      deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t X) 0 * Y +
        X * deriv (fun t : ℝ => zornFlowLinearEquiv D.1 t Y) 0 := by
  rw [deriv_zornFlow_at_zero, deriv_zornFlow_at_zero,
    deriv_zornFlow_at_zero]
  exact D.property X Y

/-- The generator of the flow attached to a Lie bracket is the pointwise
commutator of the two canonical derivations. -/
theorem deriv_zornFlow_lieBracket_at_zero
    (D E : canonicalZornDerivations) (X : CZ) :
    deriv (fun t : ℝ =>
      zornFlowLinearEquiv (⁅D, E⁆ : canonicalZornDerivations).1 t X) 0 =
      D.1 (E.1 X) - E.1 (D.1 X) := by
  rw [deriv_zornFlow_at_zero]
  rfl

end

end InfoGeometry.Lie.CanonicalZornDerivationFlowDerivative
