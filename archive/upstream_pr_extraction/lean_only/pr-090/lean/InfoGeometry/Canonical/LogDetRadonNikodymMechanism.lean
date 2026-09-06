import InfoGeometry.Canonical.MultiplicativeToAdditiveBridge
import InfoGeometry.Canonical.TypeIIIContinuousCoreReal
import InfoGeometry.Volume.ConnesCocycle

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.LogDetRadonNikodymMechanism

Repository-native package for the "multiplicative to additive" mechanism behind
log-det potentials and noncommutative Radon-Nikodym cocycles.

The module has two layers:

1. abstract abelianizing descent (`Exact/DefectiveMultiplicativeToAdditiveBridge`);
2. Type-III modular cocycle packaging (`TypeIIILogDetRNPackage`).
-/

namespace InfoGeometry.Canonical.LogDetRadonNikodymMechanism

open InfoGeometry.Canonical
open InfoGeometry.Canonical.TypeIIIContinuousCoreReal
open InfoGeometry.Volume.ConnesCocycle

section AbstractDescent

variable {M S A : Type*} [Monoid M] [CommMonoid S] [AddCommMonoid A]

/-- Additive potential induced by exact multiplicative descent. -/
abbrev LogPotential
    (B : ExactMultiplicativeToAdditiveBridge M S A) : M → A :=
  B.additiveInvariant

/-- Exact chain rule for the descended additive potential. -/
theorem logPotential_mul
    (B : ExactMultiplicativeToAdditiveBridge M S A) (x y : M) :
    LogPotential B (x * y) = LogPotential B x + LogPotential B y :=
  B.additiveInvariant_mul x y

/-- Additive potential induced by defective multiplicative descent. -/
abbrev DefectiveLogPotential
    (B : DefectiveMultiplicativeToAdditiveBridge M S A) : M → A :=
  B.additiveInvariant

/-- Additive anomaly term induced by the multiplicative descent defect. -/
abbrev DefectiveAnomaly
    (B : DefectiveMultiplicativeToAdditiveBridge M S A) : M → M → A :=
  B.additiveDefect

/-- Defective chain rule: additive potential plus additive anomaly. -/
theorem defectiveLogPotential_mul
    (B : DefectiveMultiplicativeToAdditiveBridge M S A) (x y : M) :
    DefectiveLogPotential B (x * y)
      = DefectiveAnomaly B x y + (DefectiveLogPotential B x + DefectiveLogPotential B y) :=
  B.additiveInvariant_mul x y

end AbstractDescent

section TypeIII

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Concrete Type-III package: modular flow, Connes cocycle, and scalar bridge.
This is the noncommutative Radon-Nikodym mechanism in bundled form.
-/
@[rep_depth transport]
structure TypeIIILogDetRNPackage where
  base : RealTypeIIIModularData (E := E)
  cocycle : ℝ → AlgebraEnd E
  isCocycle : IsConnesCocycle base.additiveFlow cocycle
  scalarBridge : ScalarCocycleBridge (H := E) base.additiveFlow

namespace TypeIIILogDetRNPackage

/-- Logarithmic potential extracted from the Connes cocycle bridge. -/
noncomputable def logPotential (P : TypeIIILogDetRNPackage (E := E)) : ℝ → ℝ :=
  cocycleLogPotential (H := E) P.base.additiveFlow P.cocycle P.scalarBridge

/-- Additivity of the logarithmic potential. -/
theorem logPotential_add (P : TypeIIILogDetRNPackage (E := E)) (s t : ℝ) :
    P.logPotential (s + t) = P.logPotential s + P.logPotential t := by
  simpa [logPotential] using
    (cocycleLogPotential_add (H := E) P.base.additiveFlow P.cocycle P.isCocycle P.scalarBridge s t)

/-- The Type-III log potential is an additive monoid homomorphism. -/
noncomputable def logPotentialHom (P : TypeIIILogDetRNPackage (E := E)) : ℝ →+ ℝ where
  toFun := P.logPotential
  map_zero' := by
    simpa [logPotential] using
      (cocycleLogPotential_zero (H := E) P.base.additiveFlow P.cocycle P.isCocycle
        P.scalarBridge)
  map_add' := P.logPotential_add

/-- The cocycle law is the noncommutative chain rule. -/
theorem cocycle_chain_rule (P : TypeIIILogDetRNPackage (E := E)) (s t : ℝ) :
    P.cocycle (s + t) = P.cocycle s * P.base.additiveFlow s (P.cocycle t) :=
  P.isCocycle s t

/-- Existing Type-III entropy potential is exactly this log potential. -/
@[simp] theorem logPotential_eq_boltzmannEntropyPotential
    (P : TypeIIILogDetRNPackage (E := E)) :
    P.logPotential = P.base.boltzmannEntropyPotential P.cocycle P.scalarBridge := rfl

end TypeIIILogDetRNPackage

end TypeIII

end InfoGeometry.Canonical.LogDetRadonNikodymMechanism
