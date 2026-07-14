import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Canonical.DeterminantCore
import InfoGeometry.Canonical.TypeIIIContinuousCoreReal
import InfoGeometry.Volume.RadonNikodym
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.RNDeterminantConnesChainBridge

Chain-rule bridge with the right primaries:

- projective Radon-Nikodym density cocycle,
- determinant/Jacobian multiplicative homomorphism,
- Connes 1-cocycle chaining on the Type-III modular-flow lane.

This file intentionally avoids asserting operator-level `log (A * B) = log A + log B`
as a primary law.
-/

namespace RNDeterminantConnesChainBridge

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.Determinant
open InfoGeometry.Canonical.TypeIIIContinuousCoreReal
open InfoGeometry.Volume.RadonNikodym
open InfoGeometry.Volume.ConnesCocycle

section FiniteStateChain

variable {n : ℕ} [Nonempty (Fin n)]

/-- State-to-state Radon-Nikodym chain rule on the projective positive-ray lane. -/
@[rep_depth projective]
theorem relativeDensity_state_chain
    (q q0 q1 : PositiveRay (Fin n)) (i : Fin n) :
    relativeDensity (α := Fin n) q q1 i
      = relativeDensity (α := Fin n) q q0 i
          * relativeDensity (α := Fin n) q0 q1 i :=
  relativeDensity_cocycle q q0 q1 i

/-- State-to-state cocycle law for the finite relative modular operator owner `Δ`. -/
@[rep_depth operator]
theorem relativeModularOperator_state_chain
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q1
      = relativeModularOperator (n := n) q q0
          * relativeModularOperator (n := n) q0 q1 :=
  relativeModularOperator_cocycle (n := n) q q0 q1

/--
Determinant/Jacobian shadow chain rule on the finite modular operator lane.
This is the determinant-group-homomorphism form of state-to-state composition.
-/
@[rep_depth operator]
theorem relativeModularVolumeShadow_state_chain
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeModularVolumeShadow (n := n) q q1
      = relativeModularVolumeShadow (n := n) q q0
          * relativeModularVolumeShadow (n := n) q0 q1 :=
  relativeModularVolumeShadow_cocycle (n := n) q q0 q1

/-- Additive scalar potential shadow induced by the multiplicative volume chain. -/
@[rep_depth thermo, capstone]
theorem relativeModularVolumePotential_state_chain
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeModularVolumePotential (n := n) q q1
      = relativeModularVolumePotential (n := n) q q0
          + relativeModularVolumePotential (n := n) q0 q1 :=
  relativeModularVolumePotential_cocycle (n := n) q q0 q1

end FiniteStateChain

section ScalarRNCharacter

variable {A : Type*} [Group A]

/--
Abstract scalar Radon-Nikodym bridge chain rule:
the multiplicative character descends to an additive scalar potential.
-/
@[rep_depth projective]
theorem rn_state_chain
    (B : HasScalarRNBridge A) (f g : A) :
    B.rn (f * g) = B.rn f + B.rn g :=
  B.rn_chain_rule f g

/--
The scalar RN bridge is already a projective cocycle on the trivial base:
composition becomes multiplication after passing through the projective rotor
encoding.
-/
@[rep_depth projective]
theorem rn_projectiveRotorCocycle_chain
    (B : HasScalarRNBridge A) (f g : A) :
    toProjectiveRotorCocycle B.vol (f * g) PUnit.unit =
      toProjectiveRotorCocycle B.vol f PUnit.unit *
        toProjectiveRotorCocycle B.vol g PUnit.unit :=
by
  simp [toProjectiveRotorCocycle, rn_chain_rule]

end ScalarRNCharacter

section DeterminantCharacter

universe u v

/--
Jacobian determinant chain rule in `GL`, as a direct multiplicative character
law (`detHom`).
-/
@[rep_depth operator]
theorem jacobianDeterminant_chain
    (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V]
    (f g : «GL» R V) :
    jacDet R V (f * g) = jacDet R V f * jacDet R V g :=
  jac_det_comp R V f g

end DeterminantCharacter

section TypeIIIConnesChain

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Connes 1-cocycle chain law (state-flow lane): this is the primary noncommutative
chaining identity, without collapsing to operator-log additivity.
-/
@[rep_depth transport]
theorem connesCocycle_state_chain
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → AlgebraEnd E)
    (hCocycle : IsConnesCocycle σ u)
    (s t : ℝ) :
    u (s + t) = u s * σ s (u t) :=
  hCocycle s t

/--
Three-step Connes cocycle chaining law, useful for explicit state-to-state
composition through an intermediate cocycle segment.
-/
@[rep_depth transport]
theorem connesCocycle_state_chain_three
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → AlgebraEnd E)
    (hCocycle : IsConnesCocycle σ u)
    (s t r : ℝ) :
    u (s + (t + r))
      = (u s * σ s (u t)) * σ s (σ t (u r)) := by
  calc
    u (s + (t + r)) = u s * σ s (u (t + r)) := hCocycle s (t + r)
    _ = u s * σ s (u t * σ t (u r)) := by rw [hCocycle t r]
    _ = u s * (σ s (u t) * σ s (σ t (u r))) := by
          exact congrArg (fun x => u s * x) ((σ s).map_mul (u t) (σ t (u r)))
    _ = (u s * σ s (u t)) * σ s (σ t (u r)) := by
          simp [mul_assoc]

/--
Type-III specialized chain law on the flow-unit cocycle associated to the
repo's real doubled continuous-core interface.
-/
@[rep_depth transport]
theorem realTypeIII_flowUnit_state_chain
    (R : RealTypeIIIModularData (E := E))
    (s t : ℝ) :
    flowUnitCocycle (H := E) (R.additiveFlow) (s + t)
      = flowUnitCocycle (H := E) (R.additiveFlow) s
          * R.additiveFlow s (flowUnitCocycle (H := E) (R.additiveFlow) t) := by
  exact
    (flowUnitCocycle_isConnesCocycle (H := E) (R.additiveFlow)) s t

/--
Packaged Type-III cocycle lane:
binary chain, three-step chain, and flow-unit specialization.
-/
@[rep_depth transport, capstone]
theorem typeIII_connes_chain_package
    (R : RealTypeIIIModularData (E := E))
    (u : ℝ → AlgebraEnd E)
    (hCocycle : IsConnesCocycle (R.additiveFlow) u)
    (s t r : ℝ) :
    (u (s + t) = u s * R.additiveFlow s (u t))
      ∧ (u (s + (t + r))
          = (u s * R.additiveFlow s (u t))
              * R.additiveFlow s (R.additiveFlow t (u r)))
      ∧ (flowUnitCocycle (H := E) (R.additiveFlow) (s + t)
          = flowUnitCocycle (H := E) (R.additiveFlow) s
              * R.additiveFlow s (flowUnitCocycle (H := E) (R.additiveFlow) t)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact connesCocycle_state_chain (E := E) (σ := R.additiveFlow) (u := u) hCocycle s t
  · exact connesCocycle_state_chain_three (E := E) (σ := R.additiveFlow) (u := u) hCocycle s t r
  · exact realTypeIII_flowUnit_state_chain (E := E) R s t

end TypeIIIConnesChain

end RNDeterminantConnesChainBridge
