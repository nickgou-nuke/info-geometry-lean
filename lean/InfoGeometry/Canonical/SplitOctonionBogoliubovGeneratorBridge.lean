import InfoGeometry.Canonical.SplitOctonionRegularProjectors
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BogoliubovVielbein
import InfoGeometry.Physics.HestenesKreinOperatorCalculus

/-!
# Split-octonion boost to Bogoliubov generator

The split-octonion carrier is non-associative, so this owner does not invent a
global algebra representation.  It records the supplied representation of the
associative left-regular boost plane and derives the corresponding operator
flow on the doubled carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical

open SplitOctonion
open BogoliubovVielbein
open InfoGeometry.Krein

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- A representation contract for one split-octonion boost plane. -/
structure SplitOctonionBoostRepresentation
    (g : Quaternion ℝ) (V : BogoliubovVielbeinBundle (E := E)) where
  rho : Module.End ℝ SplitOctonion → EndH
  map_add : ∀ A B, rho (A + B) = rho A + rho B
  map_smul : ∀ (c : ℝ) A, rho (c • A) = c • rho A
  map_comp : ∀ A B, rho (A.comp B) = (rho A).comp (rho B)
  map_id : rho (LinearMap.id) = ContinuousLinearMap.id ℝ H₂
  generator_eq : rho (hyperbolicAxisOperator g) = V.connectionGenerator

namespace SplitOctonionBoostRepresentation

theorem generator_sq
    (R : SplitOctonionBoostRepresentation (E := E) g V)
    (hg : Quaternion.normSq g = 1) :
    (V.connectionGenerator).comp V.connectionGenerator =
      ContinuousLinearMap.id ℝ H₂ := by
  calc
    V.connectionGenerator.comp V.connectionGenerator =
        (R.rho (hyperbolicAxisOperator g)).comp
          (R.rho (hyperbolicAxisOperator g)) := by
            rw [R.generator_eq]
    _ = R.rho ((hyperbolicAxisOperator g).comp
          (hyperbolicAxisOperator g)) := by
            rw [R.map_comp]
    _ = R.rho (LinearMap.id) := by
          rw [hyperbolicAxisOperator_sq g hg]
    _ = ContinuousLinearMap.id ℝ H₂ := R.map_id

/-- The represented hyperbolic propagator. -/
def propagator
    (R : SplitOctonionBoostRepresentation (E := E) g V) (eta : ℝ) : EndH :=
  Real.cosh eta • (ContinuousLinearMap.id ℝ H₂) +
    Real.sinh eta • V.connectionGenerator

/-- The representation transports the split-octonion hyperbolic flow to the
    corresponding doubled-space propagator.  This is the precise finite-flow
    statement available from the representation contract; it does not identify
    this direct action with the adjoint `expTransport` used by `localFrame`. -/
theorem rho_hyperbolicOperatorFlow_eq_propagator
    (R : SplitOctonionBoostRepresentation (E := E) g V) (eta : ℝ) :
    R.rho (hyperbolicOperatorFlow g eta) = R.propagator eta := by
  unfold hyperbolicOperatorFlow propagator
  rw [R.map_add, R.map_smul, R.map_smul, R.map_id, R.generator_eq]

/-- The represented hyperbolic propagator is the genuine exponential flow of
the Bogoliubov connection generator.  The square-one identity is supplied by
the representation contract, and the closed `cosh`/`sinh` form is the native
Mathlib exponential theorem. -/
theorem propagator_eq_normedSpace_exp
    (R : SplitOctonionBoostRepresentation (E := E) g V)
    (hg : Quaternion.normSq g = 1) (eta : ℝ) :
    NormedSpace.exp (eta • V.connectionGenerator) = R.propagator eta := by
  have hsq : V.connectionGenerator ^ 2 = (1 : EndH) := by
    change V.connectionGenerator.comp V.connectionGenerator =
      ContinuousLinearMap.id ℝ H₂
    exact R.generator_sq hg
  simpa [propagator] using
    (InfoGeometry.Physics.HestenesKreinOperatorCalculus.exp_of_sq_eq_one
      V.connectionGenerator hsq eta)

theorem propagator_zero
    (R : SplitOctonionBoostRepresentation (E := E) g V) :
    R.propagator 0 = ContinuousLinearMap.id ℝ H₂ := by
  simp only [propagator, Real.cosh_zero, Real.sinh_zero, one_smul]
  apply ContinuousLinearMap.ext
  intro z
  simp

theorem propagator_add
    (R : SplitOctonionBoostRepresentation (E := E) g V)
    (hg : Quaternion.normSq g = 1) (s t : ℝ) :
    (R.propagator s).comp (R.propagator t) = R.propagator (s + t) := by
  apply ContinuousLinearMap.ext
  intro z
  have hK : V.connectionGenerator (V.connectionGenerator z) = z := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : EndH => T z) (R.generator_sq hg)
  change Real.cosh s •
      (Real.cosh t • z + Real.sinh t • V.connectionGenerator z) +
      Real.sinh s • V.connectionGenerator
        (Real.cosh t • z + Real.sinh t • V.connectionGenerator z) =
    Real.cosh (s + t) • z +
      Real.sinh (s + t) • V.connectionGenerator z
  simp [map_add, map_smul]
  rw [hK]
  rw [Real.cosh_add, Real.sinh_add]
  module

theorem propagator_inverse
    (R : SplitOctonionBoostRepresentation (E := E) g V)
    (hg : Quaternion.normSq g = 1) (eta : ℝ) :
    (R.propagator (-eta)).comp (R.propagator eta) =
        ContinuousLinearMap.id ℝ H₂ ∧
      (R.propagator eta).comp (R.propagator (-eta)) =
        ContinuousLinearMap.id ℝ H₂ := by
  constructor
  · rw [R.propagator_add hg, neg_add_cancel, R.propagator_zero]
  · rw [R.propagator_add hg, add_neg_cancel, R.propagator_zero]

/-- The finite hyperbolic transport packaged as an additive-to-multiplicative
    homomorphism.  `Multiplicative` changes the target operation only; no
    analytic path integral is involved. -/
def hyperbolicPropagatorHom
    (R : SplitOctonionBoostRepresentation (E := E) g V)
    (hg : Quaternion.normSq g = 1) :
    Multiplicative ℝ →* EndH where
  toFun eta := R.propagator (Multiplicative.toAdd eta)
  map_one' := by
    change R.propagator 0 = ContinuousLinearMap.id ℝ H₂
    exact R.propagator_zero
  map_mul' s t := by
    change R.propagator (Multiplicative.toAdd s + Multiplicative.toAdd t) =
      (R.propagator (Multiplicative.toAdd s)).comp
        (R.propagator (Multiplicative.toAdd t))
    rw [R.propagator_add hg]

@[simp] theorem hyperbolicPropagatorHom_apply
    (R : SplitOctonionBoostRepresentation (E := E) g V)
    (hg : Quaternion.normSq g = 1) (eta : ℝ) :
    R.hyperbolicPropagatorHom hg (Multiplicative.ofAdd eta) = R.propagator eta := by
  rfl

end SplitOctonionBoostRepresentation

end InfoGeometry.Canonical
