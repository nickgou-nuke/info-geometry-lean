import InfoGeometry.Canonical.SplitOctonionDoubledLoxodromic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BogoliubovVielbein
import InfoGeometry.Projective.QuaternionicDoubledKrein
import Mathlib.Analysis.Normed.Algebra.QuaternionExponential

/-!
# Split-octonion doubled carrier bridge

The split-octonion and Bogoliubov owners use different carriers.  This file
records the missing identification explicitly instead of pretending that the
two types are definitionally equal.  Once a linear carrier equivalence and its
generator intertwining law are supplied, the finite hyperbolic transport is
transported to the Bogoliubov carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical

open SplitOctonion
open BogoliubovVielbein
open InfoGeometry.Krein

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "DSO" => SplitOctonion.DoubledSplitOctonion
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-! The canonical root `SplitOctonion` is already a quaternionic pair.  This
    carrier equivalence is only real-linear: the projective split-octonion
    multiplication owner is a distinct structure and is intentionally not
    identified here. -/
noncomputable def splitOctonionQuaternionicCarrierEquiv :
    SplitOctonion ≃ₗ[ℝ] DoubledSpace (Quaternion ℝ) :=
  { toFun := fun z => to_doubled z.a z.b
    invFun := fun u => ⟨WithLp.fst u, WithLp.snd u⟩
    left_inv := by
      intro z
      cases z
      rfl
    right_inv := by
      intro u
      apply DoubledSpace.ext <;> rfl
    map_add' := by
      intro z w
      apply DoubledSpace.ext <;> rfl
    map_smul' := by
      intro c z
      apply DoubledSpace.ext <;> rfl }

/-! Public names for the primary (8-dimensional) quaternionic carrier bridge.
    These deliberately mention `LinearEquiv`, not a continuous equivalence on
    the split-octonion source. -/
noncomputable abbrev splitOctonionQuaternionicLinearEquiv :
    SplitOctonion ≃ₗ[ℝ] DoubledSpace (Quaternion ℝ) :=
  splitOctonionQuaternionicCarrierEquiv

noncomputable def quaternionicTransportedHyperbolicAxisOperator (g : Quaternion ℝ) :
    Module.End ℝ (DoubledSpace (Quaternion ℝ)) :=
  (splitOctonionQuaternionicCarrierEquiv.toLinearMap.comp
      (hyperbolicAxisOperator g)).comp
    splitOctonionQuaternionicCarrierEquiv.symm.toLinearMap

noncomputable abbrev quaternionicHyperbolicGenerator (g : Quaternion ℝ) :
    Module.End ℝ (DoubledSpace (Quaternion ℝ)) :=
  quaternionicTransportedHyperbolicAxisOperator g

theorem quaternionicHyperbolicGenerator_intertwines (g : Quaternion ℝ) :
    ∀ x : SplitOctonion,
      splitOctonionQuaternionicLinearEquiv (hyperbolicAxisOperator g x) =
        quaternionicHyperbolicGenerator g
          (splitOctonionQuaternionicLinearEquiv x) := by
  intro x
  rfl

theorem quaternionicTransportedHyperbolicAxisOperator_intertwines
    (g : Quaternion ℝ) (x : SplitOctonion) :
    splitOctonionQuaternionicCarrierEquiv (hyperbolicAxisOperator g x) =
      quaternionicTransportedHyperbolicAxisOperator g
        (splitOctonionQuaternionicCarrierEquiv x) := by
  rfl

noncomputable def quaternionicTransportedHyperbolicOperatorFlow
    (g : Quaternion ℝ) (η : ℝ) :
    Module.End ℝ (DoubledSpace (Quaternion ℝ)) :=
  (splitOctonionQuaternionicCarrierEquiv.toLinearMap.comp
      (hyperbolicOperatorFlow g η)).comp
    splitOctonionQuaternionicCarrierEquiv.symm.toLinearMap

theorem quaternionicTransportedHyperbolicOperatorFlow_eq_polynomial
    (g : Quaternion ℝ) (η : ℝ) :
    quaternionicTransportedHyperbolicOperatorFlow g η =
      (Real.cosh η) • LinearMap.id +
        (Real.sinh η) • quaternionicTransportedHyperbolicAxisOperator g := by
  apply LinearMap.ext
  intro u
  simp [quaternionicTransportedHyperbolicOperatorFlow,
    hyperbolicOperatorFlow, quaternionicTransportedHyperbolicAxisOperator,
    LinearMap.comp_apply, smul_add, add_smul]

theorem quaternionicTransportedHyperbolicAxisOperator_sq (g : Quaternion ℝ)
    (hg : Quaternion.normSq g = 1) :
    (quaternionicTransportedHyperbolicAxisOperator g).comp
        (quaternionicTransportedHyperbolicAxisOperator g) =
      LinearMap.id := by
  apply LinearMap.ext
  intro u
  have h := LinearMap.congr_fun
    (hyperbolicAxisOperator_sq g hg)
    (splitOctonionQuaternionicCarrierEquiv.symm u)
  simpa [quaternionicTransportedHyperbolicAxisOperator, LinearMap.comp_apply] using
    congrArg splitOctonionQuaternionicCarrierEquiv h

noncomputable def quaternionicTransportedHyperbolicAxisOperatorCLM (g : Quaternion ℝ) :
    DoubledSpace (Quaternion ℝ) →L[ℝ] DoubledSpace (Quaternion ℝ) :=
  LinearMap.toContinuousLinearMap (quaternionicTransportedHyperbolicAxisOperator g)

noncomputable def canonicalQuaternionicBogoliubovVielbein (g : Quaternion ℝ) :
    BogoliubovVielbeinBundle (E := Quaternion ℝ) :=
  { reference := ContinuousLinearMap.id ℝ _
    connectionGenerator := quaternionicTransportedHyperbolicAxisOperatorCLM g }

noncomputable abbrev canonicalQuaternionicSplitOctonionVielbein (g : Quaternion ℝ) :
    BogoliubovVielbeinBundle (E := Quaternion ℝ) :=
  canonicalQuaternionicBogoliubovVielbein g

@[simp] theorem canonicalQuaternionicSplitOctonionVielbein_generator (g : Quaternion ℝ) :
    (canonicalQuaternionicSplitOctonionVielbein g).connectionGenerator =
      quaternionicTransportedHyperbolicAxisOperatorCLM g := by
  rfl

/-! The generic `localFrame` is exponential conjugation of the reference.
    For this canonical bundle the reference is the identity, so that frame is
    transport-fixed; it is therefore intentionally distinct from the
    transported hyperbolic flow above. -/
theorem canonicalQuaternionicSplitOctonionVielbein_localFrame (g : Quaternion ℝ)
    (t : ℝ) :
    (canonicalQuaternionicSplitOctonionVielbein g).localFrame t =
      ContinuousLinearMap.id ℝ _ := by
  rw [BogoliubovVielbeinBundle.localFrame]
  exact expTransport_eq_self_of_commute _ _ _ (Commute.one_left _)

theorem canonicalQuaternionicBogoliubovVielbein_generator (g : Quaternion ℝ) :
    (canonicalQuaternionicBogoliubovVielbein g).connectionGenerator.toLinearMap =
      quaternionicTransportedHyperbolicAxisOperator g := by
  rfl

/-! A concrete finite carrier used below for the canonical coordinate model. -/
abbrev SplitOctonionCoordinateSpace :=
  EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)

abbrev QuaternionCoordinateSpace := EuclideanSpace ℝ (Fin 4)

noncomputable def quaternionCoordinateEquiv :
    Quaternion ℝ ≃ₗ[ℝ] QuaternionCoordinateSpace :=
  (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1 : ℝ)).trans
    (WithLp.linearEquiv (2 : ENNReal) ℝ (Fin 4 → ℝ)).symm

noncomputable def splitOctonionCoordinateEquiv :
    SplitOctonion ≃ₗ[ℝ] SplitOctonionCoordinateSpace :=
  { toFun := fun z =>
      (quaternionCoordinateEquiv z.a, quaternionCoordinateEquiv z.b)
    invFun := fun z =>
      ⟨quaternionCoordinateEquiv.symm z.1, quaternionCoordinateEquiv.symm z.2⟩
    left_inv := by intro z; cases z; simp
    right_inv := by
      intro z
      apply Prod.ext
      · simpa using quaternionCoordinateEquiv.apply_symm_apply z.1
      · simpa using quaternionCoordinateEquiv.apply_symm_apply z.2
    map_add' := by intro z w; cases z; cases w; simp
    map_smul' := by intro c z; cases z; simp }

noncomputable def doubledSplitOctonionCoordinateEquiv :
    SplitOctonion.DoubledSplitOctonion ≃ₗ[ℝ] DoubledSpace SplitOctonionCoordinateSpace :=
  (LinearEquiv.prodCongr splitOctonionCoordinateEquiv splitOctonionCoordinateEquiv).trans
    (WithLp.linearEquiv (2 : ENNReal) ℝ
      (SplitOctonionCoordinateSpace × SplitOctonionCoordinateSpace)).symm

/-! The one-doubling carrier: one split octonion is a quaternionic pair. -/
noncomputable def splitOctonionDoubledQuaternionEquiv :
    SplitOctonion ≃ₗ[ℝ] DoubledSpace QuaternionCoordinateSpace :=
  splitOctonionCoordinateEquiv.trans
    (WithLp.linearEquiv (2 : ENNReal) ℝ SplitOctonionCoordinateSpace).symm

noncomputable def canonicalQuaternionDoubledGenerator (g : Quaternion ℝ) :
    Module.End ℝ (DoubledSpace QuaternionCoordinateSpace) :=
  (splitOctonionDoubledQuaternionEquiv.toLinearMap.comp
      (hyperbolicAxisOperator g)).comp
    splitOctonionDoubledQuaternionEquiv.symm.toLinearMap

noncomputable def canonicalQuaternionDoubledGeneratorCLM (g : Quaternion ℝ) :
    DoubledSpace QuaternionCoordinateSpace →L[ℝ]
      DoubledSpace QuaternionCoordinateSpace :=
  LinearMap.toContinuousLinearMap (canonicalQuaternionDoubledGenerator g)

noncomputable def canonicalQuaternionDoubledVielbein (g : Quaternion ℝ) :
    BogoliubovVielbeinBundle (E := QuaternionCoordinateSpace) :=
  { reference := ContinuousLinearMap.id ℝ _
    connectionGenerator := canonicalQuaternionDoubledGeneratorCLM g }

theorem canonicalQuaternionDoubledVielbein_generator (g : Quaternion ℝ) :
    (canonicalQuaternionDoubledVielbein g).connectionGenerator.toLinearMap =
      canonicalQuaternionDoubledGenerator g := by
  rfl

theorem canonicalQuaternionDoubledGenerator_sq (g : Quaternion ℝ)
    (hg : Quaternion.normSq g = 1) :
    (canonicalQuaternionDoubledGenerator g).comp
        (canonicalQuaternionDoubledGenerator g) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg)
    (splitOctonionDoubledQuaternionEquiv.symm x)
  simpa [canonicalQuaternionDoubledGenerator, LinearMap.comp_apply] using
    congrArg splitOctonionDoubledQuaternionEquiv h

/-- The exact datum needed to compare the two existing carrier owners. -/
structure SplitOctonionBogoliubovCarrierDatum
    (g : Quaternion ℝ) (V : BogoliubovVielbeinBundle (E := E)) where
  carrierEquiv : DSO ≃ₗ[ℝ] H₂
  generator_intertwines :
    (carrierEquiv.toLinearMap.comp
        (doubledHyperbolicOperator g)).comp carrierEquiv.symm.toLinearMap =
      V.connectionGenerator.toLinearMap

namespace SplitOctonionBogoliubovCarrierDatum

/-- The split-octonion generator transported to the Bogoliubov carrier. -/
def transportedGenerator
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V) : Module.End ℝ H₂ :=
  (D.carrierEquiv.toLinearMap.comp
      (doubledHyperbolicOperator g)).comp D.carrierEquiv.symm.toLinearMap

theorem transportedGenerator_eq_connectionGenerator
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V) :
    D.transportedGenerator = V.connectionGenerator.toLinearMap :=
  D.generator_intertwines

theorem transportedGenerator_sq
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V)
    (hg : Quaternion.normSq g = 1) :
    D.transportedGenerator.comp D.transportedGenerator = LinearMap.id := by
  rw [D.transportedGenerator_eq_connectionGenerator]
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (doubledHyperbolicOperator_sq g hg)
    (D.carrierEquiv.symm x)
  calc
    V.connectionGenerator.toLinearMap
          (V.connectionGenerator.toLinearMap x) =
        D.transportedGenerator (D.transportedGenerator x) := by
          rw [D.transportedGenerator_eq_connectionGenerator]
    _ = x := by
      simpa [transportedGenerator, LinearMap.comp_apply] using
        congrArg D.carrierEquiv h

/-- Finite hyperbolic transport after applying the carrier identification. -/
def transportedFlow
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V) (η : ℝ) : Module.End ℝ H₂ :=
  (Real.cosh η) • LinearMap.id + (Real.sinh η) • D.transportedGenerator

theorem transportedFlow_eq_bogoliubovGeneratorFlow
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V) (η : ℝ) :
    D.transportedFlow η =
      (Real.cosh η) • LinearMap.id +
        (Real.sinh η) • V.connectionGenerator.toLinearMap := by
  simp [transportedFlow, D.transportedGenerator_eq_connectionGenerator]

theorem transportedGenerator_apply
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V) (x : H₂) :
    transportedGenerator D x =
      D.carrierEquiv ((doubledHyperbolicOperator g)
        (D.carrierEquiv.symm x)) := by
  rfl

theorem transportedGenerator_sq_apply
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V)
    (hg : Quaternion.normSq g = 1) (x : H₂) :
    D.transportedGenerator (D.transportedGenerator x) = x := by
  simpa using LinearMap.congr_fun (D.transportedGenerator_sq hg) x

theorem transportedFlow_apply
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V)
    (η : ℝ) (x : H₂) :
    D.transportedFlow η x =
      Real.cosh η • x + Real.sinh η • D.transportedGenerator x := by
  simp [transportedFlow]

theorem transportedFlow_comp
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V)
    (hg : Quaternion.normSq g = 1) (η ζ : ℝ) :
    (D.transportedFlow η).comp (D.transportedFlow ζ) =
      D.transportedFlow (η + ζ) := by
  apply LinearMap.ext
  intro x
  have hG : D.transportedGenerator (D.transportedGenerator x) = x :=
    D.transportedGenerator_sq_apply hg x
  change
    (Real.cosh η) •
          ((Real.cosh ζ) • x + (Real.sinh ζ) • D.transportedGenerator x) +
        (Real.sinh η) •
          D.transportedGenerator
            ((Real.cosh ζ) • x + (Real.sinh ζ) • D.transportedGenerator x) =
      (Real.cosh (η + ζ)) • x +
        (Real.sinh (η + ζ)) • D.transportedGenerator x
  rw [map_add, map_smul, map_smul, hG]
  rw [Real.cosh_add, Real.sinh_add]
  module

theorem transportedFlow_inverse
    (D : SplitOctonionBogoliubovCarrierDatum (E := E) g V)
    (hg : Quaternion.normSq g = 1) (η : ℝ) :
    (D.transportedFlow (-η)).comp (D.transportedFlow η) = LinearMap.id ∧
      (D.transportedFlow η).comp (D.transportedFlow (-η)) = LinearMap.id := by
  constructor
  · rw [D.transportedFlow_comp hg (-η) η]
    simp [transportedFlow]
  · rw [D.transportedFlow_comp hg η (-η)]
    simp [transportedFlow]

end SplitOctonionBogoliubovCarrierDatum

end InfoGeometry.Canonical
