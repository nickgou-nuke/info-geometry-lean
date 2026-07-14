import InfoGeometry.OperatorAlgebra.ProperCarrierStageDetector
import InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension

/-!
# InfoGeometry.Canonical.ProperCarrierInductiveColimit

Owner-level inductive-colimit bridge for proper carriers.

This file does not introduce any new carrier theory.  It specializes the
already-owned proper-carrier self-dual cone lemmas to the infinite stage union
and packages the stage-index readback as a theorem chain.

#### BUCKET 1: CLOSED FINITE/COLIMIT THEOREMS
- `properCarrier_inductiveColimit_selfDualCone`
- `properCarrier_inductiveColimit_eq_univ`
- `properCarrier_inductiveColimit_mem_iff_dualPositive`
- `properCarrier_inductiveColimit_stage_readback`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The theorems are conditional on:
* monotone stage inclusions;
* stagewise self-duality; and
* an explicit finite-stage witness for every ambient element.

#### BUCKET 3: OPEN CLOSURE DEBT
No Tomita--Takesaki theorem, Type III classification, or analytic completion is
claimed here.  The file only transports the proper-carrier stage geometry to
its infinite directed union.
-/

namespace ProperCarrierInductiveColimit

open InfoGeometry.OperatorAlgebra.SelfDualConeColimit
open InfoGeometry.OperatorAlgebra.ProperCarrierStageDetector
open InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension

universe u

/--
Proper-carrier data for a stagewise self-dual cone tower.

The carrier is a monotone family of subsets, the pairing is fixed, and every
element is assigned an explicit finite stage.
-/
structure ProperCarrierColimitPacket {E : Type u} (pairing : E → E → ℝ) where
  carrier : ℕ → Set E
  mono : Monotone carrier
  selfDual : ∀ n : ℕ, IsSelfDualCone pairing (carrier n)
  stageIndex : HasFiniteCarrierStage carrier

namespace ProperCarrierColimitPacket

variable {E : Type u} {pairing : E → E → ℝ}
variable (P : ProperCarrierColimitPacket (E := E) pairing)

/-- The infinite proper-carrier union is self-dual. -/
theorem properCarrier_inductiveColimit_selfDualCone :
    IsSelfDualCone pairing (Set.iUnion P.carrier) := by
  exact properCarrier_selfDualCone_extends_of_stageIndex
    pairing P.carrier P.mono P.selfDual P.stageIndex

/-- The stagewise proper-carrier union exhausts the whole ambient carrier. -/
theorem properCarrier_inductiveColimit_eq_univ :
    Set.iUnion P.carrier = (Set.univ : Set E) := by
  exact iUnion_eq_univ_of_finiteCarrierStage P.carrier P.stageIndex

/-- Membership in the inductive colimit is exactly dual positivity. -/
theorem properCarrier_inductiveColimit_mem_iff_dualPositive
    (x : E) :
    x ∈ Set.iUnion P.carrier ↔
      ∀ y, y ∈ Set.iUnion P.carrier → 0 ≤ pairing x y := by
  exact (P.properCarrier_inductiveColimit_selfDualCone x)

/-- A finite stage readback is already a colimit readback. -/
theorem properCarrier_inductiveColimit_stage_readback
    (x : E) (hx : x ∈ P.carrier (P.stageIndex.stage x)) :
    x ∈ Set.iUnion P.carrier := by
  exact Set.mem_iUnion.mpr ⟨P.stageIndex.stage x, hx⟩

end ProperCarrierColimitPacket

/--
Standalone colimit theorem for a proper-carrier tower.

This is the theorem form most callers want: the finite carrier family is
monotone, stagewise self-dual, and finitely staged, therefore the infinite
union is self-dual.
-/
theorem properCarrier_inductiveColimit_selfDualCone
    {E : Type u}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    (hstage : HasFiniteCarrierStage K) :
    IsSelfDualCone pairing (Set.iUnion K) :=
  properCarrier_selfDualCone_extends_of_stageIndex pairing K hmono hself hstage

/-- Standalone stage-index theorem: the proper carrier union is the whole ambient set. -/
theorem properCarrier_inductiveColimit_eq_univ
    {E : Type u}
    (K : ℕ → Set E)
    (hstage : HasFiniteCarrierStage K) :
    Set.iUnion K = (Set.univ : Set E) :=
  iUnion_eq_univ_of_finiteCarrierStage K hstage

/-- Standalone colimit membership readback: membership is dual positivity. -/
theorem properCarrier_inductiveColimit_mem_iff_dualPositive
    {E : Type u}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    (hstage : HasFiniteCarrierStage K)
    (x : E) :
    x ∈ Set.iUnion K ↔
      ∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y := by
  have hcone : IsSelfDualCone pairing (Set.iUnion K) :=
    properCarrier_inductiveColimit_selfDualCone pairing K hmono hself hstage
  exact hcone x

end ProperCarrierInductiveColimit
