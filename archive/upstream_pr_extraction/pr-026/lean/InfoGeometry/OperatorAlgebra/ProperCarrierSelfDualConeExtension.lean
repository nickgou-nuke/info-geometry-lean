import InfoGeometry.OperatorAlgebra.SelfDualConeColimit

/-!
# InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension

Proper-carrier induction and colimit extension for self-dual cone owners.

This file packages the next owner-side step after finite commutant closure and
abstract self-dual-colimit transport:

* a proper carrier is modeled as an increasing sequence of finite/staged
  carriers;
* dual positivity on the directed union is detected by an explicit finite-stage
  witness;
* the self-dual cone then extends to the whole algebraic colimit carrier.

#### BUCKET 1: CLOSED FINITE/COLIMIT THEOREMS
[selfDualCone_dual_exhaustive_of_stage_detector,
 properCarrier_selfDualCone_extends_to_algebra]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The extension theorem is conditional on:
* monotone proper-carrier inclusions;
* self-duality at each finite carrier stage;
* an explicit stage detector witnessing that dual positivity forces membership
  in some finite carrier.

#### BUCKET 3: OPEN CLOSURE DEBT
No Tomita--Takesaki theorem. No standard-form theorem. No Type III/predual
claim. No KMS theorem. No modular-conjugation theorem. This file proves only
proper-carrier detection and self-dual extension to the algebraic colimit.
-/

namespace InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension

open SelfDualConeColimit

/--
A stage detector upgrades dual positivity on the directed union to explicit
membership in some finite carrier stage.
-/
theorem selfDualCone_dual_exhaustive_of_stage_detector
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hdetect :
      ∀ x, (∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y) → ∃ n : ℕ, x ∈ K n) :
    ∀ x, (∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y) → x ∈ Set.iUnion K := by
  intro x hx
  rcases hdetect x hx with ⟨n, hxn⟩
  exact Set.mem_iUnion.mpr ⟨n, hxn⟩

/--
Proper-carrier induction plus an explicit finite-stage detector extends a
stagewise self-dual cone family to the whole algebraic colimit carrier.
-/
theorem properCarrier_selfDualCone_extends_to_algebra
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    (hdetect :
      ∀ x, (∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y) → ∃ n : ℕ, x ∈ K n) :
    IsSelfDualCone pairing (Set.iUnion K) := by
  apply selfDualCone_extends_to_colimit pairing K hmono hself
  exact selfDualCone_dual_exhaustive_of_stage_detector pairing K hdetect

end InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension
