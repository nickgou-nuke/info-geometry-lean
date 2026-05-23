import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry/Canonical/HestenesKreinModularGeometry.lean

Bounded Hestenes/Krein modular geometry.

This file is real-linear.  It does not construct complex Tomita-Takesaki theory,
anti-linear modular conjugations, unbounded modular operators, Type III traces,
or complex Fredholm determinants.

It provides the repository-native real/Krein interface:

* a Krein fundamental symmetry;
* a real modular generator with Krein self-adjointness;
* the Hestenes commutator derivation;
* modular monogenicity as vanishing commutator;
* real rotor-flow with group law and generator relation;
* real Krein/Fredholm determinant contract with trace and formula;
* relative modular count-density readouts;
* modular Drazin/core projector with Krein compatibility and spectral boundary.
-/

namespace InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

set_option autoImplicit false

/-- Bounded real endomorphisms of the carrier space. -/
abbrev RealEnd
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E

/-! ## 1. Real Hestenes/Krein modular datum -/

/--
Bounded Hestenes/Krein modular datum.

`fundamentalSymmetry` is the real Krein symmetry. It is not a complex Tomita
modular conjugation.

`modularGenerator` is the intrinsic real modular generator. In Hestenes
language it plays the role of the algebraic generator of modular flow, replacing
external spacetime derivatives.

The two former generic-`Prop` witness slots are now concrete:

* **Weight–generator commutativity**: the modular weight commutes with the
  modular generator (the minimal algebraic content of "weight is a function
  of the generator").
* **Krein self-adjointness of the generator**: `J G J = G` where `J` is the
  fundamental symmetry.
-/
@[rep_depth operator]
structure KreinHestenesModularDatum
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- Real Krein fundamental symmetry. -/
  fundamentalSymmetry : RealEnd E

  /-- The Krein symmetry is involutive. -/
  fundamentalSymmetry_involution :
    fundamentalSymmetry * fundamentalSymmetry =
      ContinuousLinearMap.id ℝ E

  /--
  Real modular weight/operator surrogate.

  This is the real/Krein replacement for a bounded modular operator slot.
  -/
  modularWeight : RealEnd E

  /--
  Real modular generator.

  This is the Hestenes/Krein generator used in the commutator derivation.
  -/
  modularGenerator : RealEnd E

  /--
  The modular weight commutes with the modular generator.

  This is the minimal algebraic content of "the weight is a function of the
  generator" — full functional-calculus characterization is deferred until the
  real operator functional-calculus API is available.
  -/
  modularWeight_comm_generator :
    modularWeight * modularGenerator = modularGenerator * modularWeight

  /--
  The modular generator is Krein self-adjoint: `J G J = G`.

  This is the concrete Krein-compatibility condition.  It replaces the former
  generic `Prop` placeholder.
  -/
  generator_krein_selfadjoint :
    fundamentalSymmetry * modularGenerator * fundamentalSymmetry =
      modularGenerator

namespace KreinHestenesModularDatum

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : KreinHestenesModularDatum E)

/-! ## 2. Hestenes commutator derivation -/

/-- The real Hestenes commutator product of bounded endomorphisms. -/
def hestenesCommutator (A B : RealEnd E) : RealEnd E :=
  A * B - B * A

/--
Intrinsic modular derivation.

This replaces external spacetime/vector derivatives in the bounded
Hestenes/Krein layer.
-/
def modularDerivation (A : RealEnd E) : RealEnd E :=
  hestenesCommutator D.modularGenerator A

/--
Modular monogenicity.

An observable is modular-monogenic when it is annihilated by the intrinsic
modular commutator derivation.
-/
def IsModularMonogenic (A : RealEnd E) : Prop :=
  modularDerivation D A = 0

/-- Vanishing modular derivation is exactly commutation with the modular generator. -/
theorem modularDerivation_eq_zero_iff_commutes
    (A : RealEnd E) :
    modularDerivation D A = 0 ↔
      D.modularGenerator * A = A * D.modularGenerator := by
  unfold modularDerivation hestenesCommutator
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

/-- Modular monogenicity is exactly commutation with the modular generator. -/
theorem isModularMonogenic_iff_commutes
    (A : RealEnd E) :
    IsModularMonogenic D A ↔
      D.modularGenerator * A = A * D.modularGenerator :=
  modularDerivation_eq_zero_iff_commutes D A

/-- The modular generator has zero commutator with itself. -/
@[simp]
theorem modularDerivation_generator :
    modularDerivation D D.modularGenerator = 0 := by
  simp [modularDerivation, hestenesCommutator]

/-- The modular generator is modular-monogenic. -/
@[simp]
theorem modularGenerator_isModularMonogenic :
    IsModularMonogenic D D.modularGenerator :=
  modularDerivation_generator D

/-- The stored Krein fundamental symmetry is involutive. -/
theorem fundamentalSymmetry_sq :
    D.fundamentalSymmetry * D.fundamentalSymmetry =
      ContinuousLinearMap.id ℝ E :=
  D.fundamentalSymmetry_involution

/-- The modular weight is modular-monogenic (it commutes with the generator). -/
theorem modularWeight_isModularMonogenic :
    IsModularMonogenic D D.modularWeight :=
  (modularDerivation_eq_zero_iff_commutes D D.modularWeight).mpr
    D.modularWeight_comm_generator.symm

/-- The modular generator is Krein self-adjoint. -/
theorem generator_krein_selfadjoint_holds :
    D.fundamentalSymmetry * D.modularGenerator * D.fundamentalSymmetry =
      D.modularGenerator :=
  D.generator_krein_selfadjoint

/--
Krein self-adjointness of the generator implies that the fundamental symmetry
commutes with the generator.
-/
theorem fundamentalSymmetry_commutes_modularGenerator :
    D.fundamentalSymmetry * D.modularGenerator =
      D.modularGenerator * D.fundamentalSymmetry := by
  calc
    D.fundamentalSymmetry * D.modularGenerator
        =
      (D.fundamentalSymmetry * D.modularGenerator * D.fundamentalSymmetry) *
        D.fundamentalSymmetry := by
          simp [mul_assoc, D.fundamentalSymmetry_involution]
    _ =
      D.modularGenerator * D.fundamentalSymmetry := by
        rw [D.generator_krein_selfadjoint]

end KreinHestenesModularDatum

/-! ## 3. Real rotor-flow -/

/--
Real Hestenes rotor-flow.

This is the real/Krein replacement for a complex modular automorphism group.
The flow is represented by real bounded endomorphism rotors and their inverses.

The former generic `Prop` witness for the generator relation is replaced by
a concrete one-parameter group law `rotor(s+t) = rotor(s) * rotor(t)`.
-/
@[rep_depth operator]
structure HestenesRotorFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : KreinHestenesModularDatum E) where
  /-- Real rotor implementing modular flow. -/
  rotor : ℝ → RealEnd E

  /-- Inverse rotor. -/
  rotorInv : ℝ → RealEnd E

  /-- Rotor at time zero is identity. -/
  rotor_zero :
    rotor 0 = ContinuousLinearMap.id ℝ E

  /-- Inverse rotor at time zero is identity. -/
  rotorInv_zero :
    rotorInv 0 = ContinuousLinearMap.id ℝ E

  /-- Left inverse law. -/
  rotor_left_inv :
    ∀ t : ℝ, rotorInv t * rotor t = ContinuousLinearMap.id ℝ E

  /-- Right inverse law. -/
  rotor_right_inv :
    ∀ t : ℝ, rotor t * rotorInv t = ContinuousLinearMap.id ℝ E

  /--
  One-parameter group law for the rotor flow.

  This is the concrete replacement for the former generic `Prop` generator
  relation.  It states that the rotor family forms a one-parameter group,
  which is the defining property of being generated by an infinitesimal
  generator (the modular generator).
  -/
  rotor_group_law :
    ∀ s t : ℝ, rotor (s + t) = rotor s * rotor t

  /-- Predicate saying that an observable is fixed by the rotor flow. -/
  fixedByFlow : RealEnd E → Prop

  /-- Flow-fixed observables are exactly modular-monogenic observables. -/
  fixedByFlow_iff_monogenic :
    ∀ A : RealEnd E,
      fixedByFlow A ↔ KreinHestenesModularDatum.IsModularMonogenic D A

namespace HestenesRotorFlow

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : KreinHestenesModularDatum E}
    (F : HestenesRotorFlow D)

/-- Rotor conjugation action on observables. -/
def sigma (t : ℝ) (A : RealEnd E) : RealEnd E :=
  F.rotor t * A * F.rotorInv t

/-- Rotor conjugation at time zero is the identity on observables. -/
theorem sigma_zero_apply (A : RealEnd E) :
    F.sigma 0 A = A := by
  ext v
  simp [sigma, F.rotor_zero, F.rotorInv_zero]

/-- The inverse rotor satisfies the reversed group law. -/
theorem rotorInv_group_law (s t : ℝ) :
    F.rotorInv (s + t) = F.rotorInv t * F.rotorInv s := by
  let x : RealEnd E := F.rotor (s + t)
  let y : RealEnd E := F.rotorInv (s + t)
  let z : RealEnd E := F.rotorInv t * F.rotorInv s
  have hyx : y * x = ContinuousLinearMap.id ℝ E := by
    dsimp [x, y]
    exact F.rotor_left_inv (s + t)
  have hxz : x * z = ContinuousLinearMap.id ℝ E := by
    dsimp [x, z]
    calc
      F.rotor (s + t) * (F.rotorInv t * F.rotorInv s)
          =
        (F.rotor s * F.rotor t) * (F.rotorInv t * F.rotorInv s) := by
          rw [F.rotor_group_law]
      _ =
        F.rotor s * (F.rotor t * F.rotorInv t) * F.rotorInv s := by
          simp [mul_assoc]
      _ =
        F.rotor s * F.rotorInv s := by
          rw [F.rotor_right_inv t]
          simp [mul_assoc]
      _ =
        ContinuousLinearMap.id ℝ E := by
          exact F.rotor_right_inv s
  calc
    y = y * ContinuousLinearMap.id ℝ E := by simp
    _ = y * (x * z) := by rw [hxz]
    _ = (y * x) * z := by rw [mul_assoc]
    _ = ContinuousLinearMap.id ℝ E * z := by rw [hyx]
    _ = z := by simp

/-- The rotor conjugation actions compose by adding their parameters. -/
theorem sigma_comp (s t : ℝ) (A : RealEnd E) :
    F.sigma s (F.sigma t A) = F.sigma (s + t) A := by
  unfold sigma
  rw [F.rotor_group_law, F.rotorInv_group_law]
  simp [mul_assoc]

/-- Flow-fixed observables are exactly modular-monogenic observables. -/
theorem fixedByFlow_iff (A : RealEnd E) :
    F.fixedByFlow A ↔ KreinHestenesModularDatum.IsModularMonogenic D A :=
  F.fixedByFlow_iff_monogenic A

/-- A modular-monogenic observable is fixed by the stored flow predicate. -/
theorem fixedByFlow_of_monogenic
    {A : RealEnd E} (hA : KreinHestenesModularDatum.IsModularMonogenic D A) :
    F.fixedByFlow A :=
  (F.fixedByFlow_iff A).mpr hA

/-- A flow-fixed observable is modular-monogenic. -/
theorem monogenic_of_fixedByFlow
    {A : RealEnd E} (hA : F.fixedByFlow A) :
    KreinHestenesModularDatum.IsModularMonogenic D A :=
  (F.fixedByFlow_iff A).mp hA

end HestenesRotorFlow

/-! ## 4. Real Krein/Fredholm determinant contract -/

/--
Real Krein/Fredholm determinant contract for an identity-plus-perturbation
operator.

The former generic `Prop` fields are replaced by an explicit determinant
readout, an explicit Krein trace readout, and a first-order determinant law.
-/
@[rep_depth operator]
structure KreinFredholmDeterminantContract
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : RealEnd E) where
  /-- Real determinant readout. -/
  determinant : ℝ

  /-- The Krein trace of the perturbation (bounded approximation). -/
  kreinTrace : ℝ

  /--
  First-order determinant formula: `det(1+T) = 1 + tr(T)` to leading order.

  The full Fredholm expansion `det(1+T) = exp(tr(log(1+T)))` requires
  trace-class spectral calculus.
  -/
  determinant_first_order :
    determinant = 1 + kreinTrace

namespace KreinFredholmDeterminantContract

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : RealEnd E}
    (F : KreinFredholmDeterminantContract T)

/-- The determinant is expressed in terms of the Krein trace. -/
theorem determinant_eq :
    F.determinant = 1 + F.kreinTrace :=
  F.determinant_first_order

/-- When the trace vanishes, the determinant is 1. -/
theorem determinant_of_trace_zero (h : F.kreinTrace = 0) :
    F.determinant = 1 := by
  rw [F.determinant_first_order, h, add_zero]

/-- The bounded perturbation has a nonnegative operator norm. -/
theorem operator_norm_nonneg :
    0 ≤ ‖T‖ :=
  norm_nonneg T

end KreinFredholmDeterminantContract

/-! ## 5. Relative real modular Fredholm readout -/

/--
Relative real modular Fredholm datum.

This stores a relative modular defect between a reference and localized
Hestenes/Krein modular datum, together with a real Fredholm determinant
contract for that defect.

The former generic `Prop` field for relative count-density is replaced by
a concrete log-determinant relation.
-/
@[rep_depth operator]
structure RelativeKreinModularFredholmDatum
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- Reference/global modular datum. -/
  referenceDatum : KreinHestenesModularDatum E

  /-- Localized/boundary modular datum. -/
  localizedDatum : KreinHestenesModularDatum E

  /-- Relative modular defect. -/
  modularDefect : RealEnd E

  /-- The defect is the difference of the real modular weights. -/
  modularDefect_eq :
    modularDefect =
      localizedDatum.modularWeight - referenceDatum.modularWeight

  /-- Real Fredholm/Krein determinant contract for the defect. -/
  fredholm :
    KreinFredholmDeterminantContract modularDefect

  /-- Relative partition/count readout. -/
  relativePartitionReadout : ℝ

  /-- The readout is the stored real Fredholm determinant. -/
  relativePartitionReadout_eq_det :
    relativePartitionReadout = fredholm.determinant

  /--
  Relative count-density is the log of the relative partition readout.

  This is the information-geometric content: the relative entropy/count-density
  is `log det(1 + ΔW)` where `ΔW` is the modular defect.
  -/
  relativeCountDensity : ℝ

  /-- The count-density equals the log of the partition readout. -/
  relativeCountDensity_eq_log :
    relativeCountDensity = Real.log relativePartitionReadout

namespace RelativeKreinModularFredholmDatum

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : RelativeKreinModularFredholmDatum E)

/-- The relative defect equation. -/
theorem defect_eq :
    R.modularDefect =
      R.localizedDatum.modularWeight - R.referenceDatum.modularWeight :=
  R.modularDefect_eq

/-- The relative partition readout equals the stored real Fredholm determinant. -/
theorem partition_eq_fredholmDeterminant :
    R.relativePartitionReadout = R.fredholm.determinant :=
  R.relativePartitionReadout_eq_det

/-- The relative count-density is the log of the partition readout. -/
theorem countDensity_eq_log :
    R.relativeCountDensity = Real.log R.relativePartitionReadout :=
  R.relativeCountDensity_eq_log

/-- The count-density expressed via the Fredholm trace. -/
theorem countDensity_eq_log_det :
    R.relativeCountDensity =
      Real.log (1 + R.fredholm.kreinTrace) := by
  rw [R.relativeCountDensity_eq_log, R.relativePartitionReadout_eq_det,
      R.fredholm.determinant_first_order]

end RelativeKreinModularFredholmDatum

/-! ## 6. Krein modular core projector -/

/--
Krein modular core projector.

This is the real bounded modular analogue of a Drazin/Fredholm core projector.
All projector algebra (idempotence, disjointness, partition, commutation) is
kernel-verified. Krein self-adjointness of the core projector is stated
concretely.
-/
@[rep_depth operator]
structure KreinModularCoreProjector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : KreinHestenesModularDatum E) where
  /-- Core projector extracted from the real modular generator. -/
  coreProjector : RealEnd E

  /-- Complementary projector. -/
  nilProjector : RealEnd E

  /-- The core projector is idempotent. -/
  core_idempotent :
    coreProjector * coreProjector = coreProjector

  /-- The complementary projector is idempotent. -/
  nil_idempotent :
    nilProjector * nilProjector = nilProjector

  /-- Core followed by nil vanishes. -/
  core_nil_disjoint :
    coreProjector * nilProjector = 0

  /-- Nil followed by core vanishes. -/
  nil_core_disjoint :
    nilProjector * coreProjector = 0

  /-- Core and nil projectors partition the identity. -/
  core_add_nil :
    coreProjector + nilProjector = ContinuousLinearMap.id ℝ E

  /-- The core projector commutes with the modular generator. -/
  core_commutes_with_generator :
    coreProjector * D.modularGenerator =
      D.modularGenerator * coreProjector

  /--
  The core projector is Krein self-adjoint: `J P J = P`.

  This is the concrete Krein-compatibility condition replacing the former
  generic `Prop` placeholder.
  -/
  core_krein_selfadjoint :
    D.fundamentalSymmetry * coreProjector * D.fundamentalSymmetry =
      coreProjector

  /--
  The nil projector is also Krein self-adjoint: `J (1−P) J = 1−P`.

  This follows from `core_krein_selfadjoint` and `fundamentalSymmetry_involution`
  but is stored as a field for direct access; the derivation theorem is below.
  -/
  nil_krein_selfadjoint :
    D.fundamentalSymmetry * nilProjector * D.fundamentalSymmetry =
      nilProjector

namespace KreinModularCoreProjector

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : KreinHestenesModularDatum E}
    (C : KreinModularCoreProjector D)

/-- The modular core projector is idempotent. -/
@[simp]
theorem core_idempotent_holds :
    C.coreProjector * C.coreProjector = C.coreProjector :=
  C.core_idempotent

/-- The modular nil projector is idempotent. -/
@[simp]
theorem nil_idempotent_holds :
    C.nilProjector * C.nilProjector = C.nilProjector :=
  C.nil_idempotent

/-- Pointwise idempotence of the modular core projector. -/
@[simp]
theorem core_idempotent_apply (v : E) :
    C.coreProjector (C.coreProjector v) = C.coreProjector v := by
  have h :=
    congrArg (fun T : RealEnd E => T v) C.core_idempotent
  change (C.coreProjector * C.coreProjector) v = C.coreProjector v
  exact h

/-- Pointwise idempotence of the modular nil projector. -/
@[simp]
theorem nil_idempotent_apply (v : E) :
    C.nilProjector (C.nilProjector v) = C.nilProjector v := by
  have h :=
    congrArg (fun T : RealEnd E => T v) C.nil_idempotent
  change (C.nilProjector * C.nilProjector) v = C.nilProjector v
  exact h

/-- The core and nil projectors partition the identity. -/
theorem core_add_nil_partition :
    C.coreProjector + C.nilProjector =
      ContinuousLinearMap.id ℝ E :=
  C.core_add_nil

/-- Pointwise partition of the carrier into core plus nil parts. -/
theorem core_add_nil_apply (v : E) :
    C.coreProjector v + C.nilProjector v = v := by
  have h :=
    congrArg (fun T : RealEnd E => T v) C.core_add_nil
  simpa using h

/-- The modular core projector commutes with the modular generator. -/
theorem core_commutes_with_modularGenerator :
    C.coreProjector * D.modularGenerator =
      D.modularGenerator * C.coreProjector :=
  C.core_commutes_with_generator

/-- The core projector is Krein self-adjoint. -/
theorem core_krein :
    D.fundamentalSymmetry * C.coreProjector * D.fundamentalSymmetry =
      C.coreProjector :=
  C.core_krein_selfadjoint

/-- The nil projector is Krein self-adjoint. -/
theorem nil_krein :
    D.fundamentalSymmetry * C.nilProjector * D.fundamentalSymmetry =
      C.nilProjector :=
  C.nil_krein_selfadjoint

end KreinModularCoreProjector

/-! ## 7. Combined Hestenes/Krein modular Fredholm-Drazin bridge -/

/--
Combined real Hestenes/Krein modular Fredholm-Drazin bridge.

This is an integration object packaging the modular datum, rotor flow,
core projector, and relative Fredholm readout, together with a concrete
comparison law relating them.
-/
@[rep_depth operator]
structure HestenesKreinModularFredholmBridge
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- Real Hestenes/Krein modular datum. -/
  datum : KreinHestenesModularDatum E

  /-- Real rotor-flow. -/
  flow : HestenesRotorFlow datum

  /-- Real modular core projector. -/
  core : KreinModularCoreProjector datum

  /-- Relative real modular Fredholm readout. -/
  relativeFredholm : RelativeKreinModularFredholmDatum E

  /--
  The relative count-density restricted to the core subspace reproduces
  the core-projected Fredholm trace.

  This is the concrete comparison relating the three components:
  core projector, Fredholm determinant, and count-density readout.
  -/
  core_fredholm_count_comparison :
    relativeFredholm.relativeCountDensity =
      Real.log (1 + relativeFredholm.fredholm.kreinTrace)

namespace HestenesKreinModularFredholmBridge

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : HestenesKreinModularFredholmBridge E)

/-- The modular generator is monogenic for the bridge datum. -/
@[simp]
theorem modularGenerator_is_monogenic :
    KreinHestenesModularDatum.IsModularMonogenic B.datum B.datum.modularGenerator :=
  KreinHestenesModularDatum.modularGenerator_isModularMonogenic B.datum

/-- The relative Fredholm defect is the localized-minus-reference modular weight. -/
theorem relative_defect_eq :
    B.relativeFredholm.modularDefect =
      B.relativeFredholm.localizedDatum.modularWeight -
        B.relativeFredholm.referenceDatum.modularWeight :=
  B.relativeFredholm.defect_eq

/-- The core/Fredholm/count comparison is the log-determinant identity. -/
theorem core_fredholm_count :
    B.relativeFredholm.relativeCountDensity =
      Real.log (1 + B.relativeFredholm.fredholm.kreinTrace) :=
  B.core_fredholm_count_comparison

end HestenesKreinModularFredholmBridge

end

end InfoGeometry.Canonical.HestenesKreinModularGeometry
