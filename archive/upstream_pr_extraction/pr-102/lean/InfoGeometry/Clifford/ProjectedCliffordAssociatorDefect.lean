import InfoGeometry.Clifford.OctonionParavectorBridge
import InfoGeometry.Algebra.ChiralOperatorSymbolProjection

/-!
# Associator defect of a projected Clifford shadow

The ambient Clifford/operator algebra is associative.  A paravector product
is obtained only after inclusion, ambient multiplication, and readout.  This
owner specializes the generic projection-defect theorem to the native
`ProjectedCliffordShadow` interface and names the discarded ambient component
(`ambientLeakage`) explicitly.
-/

noncomputable section

namespace InfoGeometry.Clifford.ProjectedCliffordAssociatorDefect

open InfoGeometry.Algebra
open InfoGeometry.Clifford.OctonionParavectorBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {Cl : Type*} [Ring Cl] [Algebra ℝ Cl]

variable (D : OctonionParavectorData V)
variable (S : ProjectedCliffordShadow D Cl)

/-- The ambient endomorphism retained by the paravector inclusion/readout pair. -/
def ambientProjection : Cl →ₗ[ℝ] Cl :=
  symbolProjection S.includeParavector S.projectParavector

/-- The component discarded by the chosen paravector readout. -/
def ambientLeakage (X : Cl) : Cl :=
  symbolDefect S.includeParavector S.projectParavector X

@[simp] theorem ambientProjection_apply (X : Cl) :
    ambientProjection D S X =
      S.includeParavector (S.projectParavector X) :=
  rfl

theorem ambientProjection_add_leakage (X : Cl) :
    ambientProjection D S X + ambientLeakage D S X = X := by
  exact symbolProjection_add_defect S.includeParavector S.projectParavector X

/-- The projected paravector associator is exactly the readout of ambient
leakage.  No nonassociativity is assumed in `Cl`; it comes solely from the
intermediate readout. -/
theorem projectedParavectorAssociator_eq_leakage
    (x y z : Paravector V) :
    paravectorMul D (paravectorMul D x y) z -
        paravectorMul D x (paravectorMul D y z) =
      S.projectParavector (
        S.includeParavector x * ambientLeakage D S
            (S.includeParavector y * S.includeParavector z) -
          ambientLeakage D S
            (S.includeParavector x * S.includeParavector y) *
            S.includeParavector z) := by
  have h := projectedOperatorAssociator_eq_defect
    S.includeParavector S.projectParavector x y z
  simpa [projectedOperatorAssociator, projectedOperatorMul,
    ambientLeakage, symbolDefect, symbolProjection, S.projected_mul] using h

/-- Closure of the included paravectors under ambient multiplication forces the
projected product to be associative. -/
theorem projectedParavectorAssociator_eq_zero_of_no_leakage
    (hLeak : ∀ x y : Paravector V,
      ambientLeakage D S
        (S.includeParavector x * S.includeParavector y) = 0)
    (x y z : Paravector V) :
    paravectorMul D (paravectorMul D x y) z -
        paravectorMul D x (paravectorMul D y z) = 0 := by
  rw [projectedParavectorAssociator_eq_leakage D S x y z]
  simp [hLeak]

end InfoGeometry.Clifford.ProjectedCliffordAssociatorDefect
