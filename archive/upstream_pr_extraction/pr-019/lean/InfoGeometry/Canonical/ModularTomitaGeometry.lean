import InfoGeometry.Canonical.HestenesKreinModularGeometry

/-!
# InfoGeometry/Canonical/ModularTomitaGeometry.lean

Compatibility import for the real Hestenes/Krein modular layer.

The active owner surface is
`InfoGeometry.Canonical.HestenesKreinModularGeometry`.  This path is retained
for downstream imports, but the module is now real-linear and routed through
the Hestenes/Krein interface: real endomorphisms, Krein symmetry, rotor flow,
commutator derivations, and witness-gated Fredholm/core packets.
-/

/-
import Mathlib
import InfoGeometry.Canonical.RealTomitaCore
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
import InfoGeometry.Canonical.DrazinFredholmBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry/Canonical/ModularTomitaGeometry.lean

Bounded real Majorana/Krein shadow of modular Tomita geometry.

This file is deliberately not a construction of complex Hilbert-space
Tomita-Takesaki theory.  In this repository the operational lane is the doubled
real Majorana/BdG carrier: the complex-linear/anti-linear split has already
been translated into real `J`, `ε`, and `K = Jε` operators.  Here we record the
bounded doubled-real interface used by downstream finite/operator modules:

* a real bounded modular datum on `DoubledSpace E`;
* the intrinsic modular commutator derivation `δ(A) = K A - A K`;
* modular-monogenicity as the bounded centralizer condition;
* proof-carrying resolvent, core projection, and Fredholm determinant packets.

No fake resolvent, fake Fredholm determinant, global trace theorem, or
unbounded Tomita object is introduced.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ModularTomitaGeometry

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealTomitaCore

noncomputable section

set_option autoImplicit false

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- Real bounded endomorphisms of the repository's doubled Majorana carrier. -/
abbrev DoubledEnd
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E →L[ℝ] DoubledSpace E

local notation "EndH₂" => DoubledEnd E

/-! ## 1. Bounded doubled-real Tomita shadow -/

/--
Bounded real/Krein shadow of Tomita modular data on the doubled carrier.

The fields `J`, `eps`, and `phaseAxis` are stored rather than reconstructed so
non-canonical bounded models can still be represented, while the canonical
constructor below pins them to the repository's root owners.
-/
@[rep_depth krein]
structure BoundedTomitaKreinDatum where
  /-- Real-linear shadow of modular conjugation. -/
  J : EndH₂

  /-- Real-linear grading/sign involution. -/
  eps : EndH₂

  /-- Hestenes phase axis, intended as `Jε`. -/
  phaseAxis : EndH₂

  /-- `J` is involutive in the bounded real shadow. -/
  J_involutive :
    J * J = 1

  /-- `ε` is involutive in the bounded real shadow. -/
  eps_involutive :
    eps * eps = 1

  /-- The phase axis is the geometric product `Jε`. -/
  phaseAxis_eq_J_mul_eps :
    phaseAxis = J * eps

  /-- The Hestenes phase axis squares to `-1`. -/
  phaseAxis_sq :
    phaseAxis * phaseAxis = -1

  /-- Bounded modular-operator shadow `Δ`. -/
  modularOperator : EndH₂

  /-- Bounded modular-Hamiltonian shadow `K_mod`. -/
  modularHamiltonian : EndH₂

  /--
  Future bounded functional-calculus statement relating `Δ` and `K_mod`.
  For example, a later model may set `Δ = exp(-K_mod)`.
  -/
  delta_exp_statement : Prop

  /-- Proof of the stored bounded modular relation. -/
  delta_exp_witness :
    delta_exp_statement

namespace BoundedTomitaKreinDatum

/--
Canonical bounded Tomita/Krein datum from the repository's doubled-space root
owners `modular_j`, `spectral_epsilon`, and `clockAxis`.
-/
@[rep_depth krein]
def canonical
    (modularOperator modularHamiltonian : EndH₂)
    (delta_exp_statement : Prop)
    (delta_exp_witness : delta_exp_statement) :
    BoundedTomitaKreinDatum (E := E) where
  J := modular_j (E := E)
  eps := spectral_epsilon (E := E)
  phaseAxis := clockAxis (E := E)
  J_involutive := by
    change (modular_j (E := E)).comp (modular_j (E := E)) =
      ContinuousLinearMap.id ℝ H₂
    exact modular_j_involution E
  eps_involutive := by
    change (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E)) =
      ContinuousLinearMap.id ℝ H₂
    exact spectral_epsilon_involution E
  phaseAxis_eq_J_mul_eps := by
    change clockAxis (E := E) = (modular_j (E := E)).comp (spectral_epsilon (E := E))
    rfl
  phaseAxis_sq := by
    change (clockAxis (E := E)).comp (clockAxis (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂)
    exact clockAxis_sq E
  modularOperator := modularOperator
  modularHamiltonian := modularHamiltonian
  delta_exp_statement := delta_exp_statement
  delta_exp_witness := delta_exp_witness

variable (T : BoundedTomitaKreinDatum (E := E))

/-- The bounded modular commutator `K_mod A - A K_mod`. -/
@[rep_depth operator]
def modularDerivation (A : EndH₂) : EndH₂ :=
  T.modularHamiltonian * A - A * T.modularHamiltonian

/-- Modular-monogenicity/centralizer condition in the bounded shadow. -/
@[rep_depth operator]
def IsModularMonogenic (A : EndH₂) : Prop :=
  T.modularDerivation A = 0

/-- Modular-monogenicity is exactly commutation with the modular Hamiltonian. -/
@[rep_depth operator]
theorem isModularMonogenic_iff_commutes (A : EndH₂) :
    T.IsModularMonogenic A ↔
      T.modularHamiltonian * A = A * T.modularHamiltonian := by
  unfold IsModularMonogenic modularDerivation
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

/-- The identity operator is modular-monogenic. -/
@[simp, rep_depth operator]
theorem isModularMonogenic_one :
    T.IsModularMonogenic (1 : EndH₂) := by
  simp [IsModularMonogenic, modularDerivation]

/-- The modular Hamiltonian is modular-monogenic. -/
@[simp, rep_depth operator]
theorem modularHamiltonian_isModularMonogenic :
    T.IsModularMonogenic T.modularHamiltonian := by
  simp [IsModularMonogenic, modularDerivation]

/-- The modular derivation obeys the Leibniz rule on the bounded operator algebra. -/
@[rep_depth operator]
theorem modularDerivation_mul (A B : EndH₂) :
    T.modularDerivation (A * B) =
      T.modularDerivation A * B + A * T.modularDerivation B := by
  ext x <;> simp [modularDerivation, sub_eq_add_neg, add_assoc]

/-- Products of modular-monogenic operators are modular-monogenic. -/
@[rep_depth operator]
theorem IsModularMonogenic.mul
    {A B : EndH₂}
    (hA : T.IsModularMonogenic A)
    (hB : T.IsModularMonogenic B) :
    T.IsModularMonogenic (A * B) := by
  unfold IsModularMonogenic at *
  rw [T.modularDerivation_mul A B, hA, hB]
  simp

/-- The stored modular relation witness. -/
@[rep_depth operator]
theorem delta_exp_relation :
    T.delta_exp_statement :=
  T.delta_exp_witness

/-- The stored phase axis squares to `-1`. -/
@[rep_depth krein]
theorem phaseAxis_square :
    T.phaseAxis * T.phaseAxis = -1 :=
  T.phaseAxis_sq

/-! ## 2. Modular resolvent witnesses, not fake resolvents -/

/-- The bounded real modular resolvent denominator `λ I - K_mod`. -/
@[rep_depth operator]
def modularResolventDenominator (lam : ℝ) : EndH₂ :=
  lam • (1 : EndH₂) - T.modularHamiltonian

/-- Proof-carrying inverse witness for `λ I - K_mod`. -/
@[rep_depth operator]
structure ModularResolventWitness (lam : ℝ) where
  /-- Candidate inverse of `λ I - K_mod`. -/
  R : EndH₂

  /-- Left inverse law. -/
  left_inverse :
    T.modularResolventDenominator lam * R = 1

  /-- Right inverse law. -/
  right_inverse :
    R * T.modularResolventDenominator lam = 1

namespace ModularResolventWitness

variable {T : BoundedTomitaKreinDatum (E := E)}
variable {lam : ℝ}
variable (Rlam : T.ModularResolventWitness lam)

@[simp, rep_depth operator]
theorem left_inverse_apply :
    T.modularResolventDenominator lam * Rlam.R = 1 :=
  Rlam.left_inverse

@[simp, rep_depth operator]
theorem right_inverse_apply :
    Rlam.R * T.modularResolventDenominator lam = 1 :=
  Rlam.right_inverse

end ModularResolventWitness

/-! ## 3. Modular Drazin/core projection witness -/

/--
Modular core/nil projection packet.

This is the modular analogue of a Drazin core split for the bounded modular
Hamiltonian shadow.  The projection laws are supplied as data.
-/
@[rep_depth operator]
structure ModularCoreProjectionWitness where
  Pcore : EndH₂
  Pnil : EndH₂

  core_idempotent :
    Pcore * Pcore = Pcore

  nil_idempotent :
    Pnil * Pnil = Pnil

  complementary :
    Pcore + Pnil = 1

  core_nil_disjoint :
    Pcore * Pnil = 0

  nil_core_disjoint :
    Pnil * Pcore = 0

  core_commutes_with_modularHamiltonian :
    Pcore * T.modularHamiltonian = T.modularHamiltonian * Pcore

  nil_eventually_annihilated :
    ∃ k : ℕ, T.modularHamiltonian ^ k * Pnil = 0

namespace ModularCoreProjectionWitness

variable {T : BoundedTomitaKreinDatum (E := E)}
variable (W : T.ModularCoreProjectionWitness)

@[simp, rep_depth operator]
theorem Pcore_idempotent :
    W.Pcore * W.Pcore = W.Pcore :=
  W.core_idempotent

@[simp, rep_depth operator]
theorem Pnil_idempotent :
    W.Pnil * W.Pnil = W.Pnil :=
  W.nil_idempotent

@[rep_depth operator]
theorem Pcore_add_Pnil :
    W.Pcore + W.Pnil = 1 :=
  W.complementary

@[simp, rep_depth operator]
theorem Pcore_mul_Pnil :
    W.Pcore * W.Pnil = 0 :=
  W.core_nil_disjoint

@[simp, rep_depth operator]
theorem Pnil_mul_Pcore :
    W.Pnil * W.Pcore = 0 :=
  W.nil_core_disjoint

@[rep_depth operator]
theorem Pcore_commutes_with_K :
    W.Pcore * T.modularHamiltonian =
      T.modularHamiltonian * W.Pcore :=
  W.core_commutes_with_modularHamiltonian

@[rep_depth operator]
theorem Pnil_power_annihilated :
    ∃ k : ℕ, T.modularHamiltonian ^ k * W.Pnil = 0 :=
  W.nil_eventually_annihilated

end ModularCoreProjectionWitness

end BoundedTomitaKreinDatum

/-! ## 4. Relative modular Fredholm determinant interface -/

/-- Relative bounded modular defect `Δ_local - Δ_reference`. -/
@[rep_depth operator]
def relativeModularDefect
    (reference localDatum : BoundedTomitaKreinDatum (E := E)) : EndH₂ :=
  localDatum.modularOperator - reference.modularOperator

/--
Proof-carrying Fredholm determinant readout for a relative modular defect.

`TraceClass` and `FredholmDeterminant` are supplied predicates.  This keeps the
usual trace-class gate explicit and avoids defining any fake determinant.
-/
@[rep_depth operator]
structure RelativeFredholmDeterminantWitness
    (TraceClass : EndH₂ → Prop)
    (FredholmDeterminant : EndH₂ → ℝ → Prop)
    (reference localDatum : BoundedTomitaKreinDatum (E := E)) where
  traceClass_defect :
    TraceClass (relativeModularDefect reference localDatum)

  determinant : ℝ

  determinant_spec :
    FredholmDeterminant
      (relativeModularDefect reference localDatum)
      determinant

namespace RelativeFredholmDeterminantWitness

variable
    {TraceClass : DoubledEnd E → Prop}
    {FredholmDeterminant : DoubledEnd E → ℝ → Prop}
    {reference localDatum : BoundedTomitaKreinDatum (E := E)}

/-- The stored trace-class gate for the relative defect. -/
@[rep_depth operator]
theorem traceClass :
    RelativeFredholmDeterminantWitness TraceClass FredholmDeterminant reference localDatum →
    TraceClass (relativeModularDefect reference localDatum) :=
  RelativeFredholmDeterminantWitness.traceClass_defect

/-- The stored Fredholm determinant specification. -/
@[rep_depth operator]
theorem determinant_spec_holds
    (W : RelativeFredholmDeterminantWitness TraceClass FredholmDeterminant reference localDatum) :
    FredholmDeterminant (relativeModularDefect reference localDatum) W.determinant :=
  RelativeFredholmDeterminantWitness.determinant_spec W

end RelativeFredholmDeterminantWitness

/-- Fredholm partition-function readout from the supplied determinant. -/
@[rep_depth operator]
def relativePartitionFunction
    {TraceClass : EndH₂ → Prop}
    {FredholmDeterminant : EndH₂ → ℝ → Prop}
    {reference localDatum : BoundedTomitaKreinDatum (E := E)}
    (W : RelativeFredholmDeterminantWitness TraceClass FredholmDeterminant reference localDatum) :
    ℝ :=
  W.determinant

/-- Logarithmic relative-count-density readout. -/
@[rep_depth operator]
def relativeCountDensity
    {TraceClass : EndH₂ → Prop}
    {FredholmDeterminant : EndH₂ → ℝ → Prop}
    {reference localDatum : BoundedTomitaKreinDatum (E := E)}
    (W : RelativeFredholmDeterminantWitness TraceClass FredholmDeterminant reference localDatum) :
    ℝ :=
  Real.log |W.determinant|

/--
Entropy bridge from a relative modular Fredholm determinant.

The equality with entropy is not asserted globally; it is stored as a witness.
-/
@[rep_depth operator]
structure RelativeModularEntropyBridge
    (TraceClass : EndH₂ → Prop)
    (FredholmDeterminant : EndH₂ → ℝ → Prop)
    (reference localDatum : BoundedTomitaKreinDatum (E := E)) where
  fredholm :
    RelativeFredholmDeterminantWitness TraceClass FredholmDeterminant reference localDatum

  entropy : ℝ

  entropy_eq_relativeCountDensity :
    entropy = relativeCountDensity fredholm

namespace RelativeModularEntropyBridge

variable
    {TraceClass : DoubledEnd E → Prop}
    {FredholmDeterminant : DoubledEnd E → ℝ → Prop}
    {reference localDatum : BoundedTomitaKreinDatum (E := E)}
    (B : RelativeModularEntropyBridge TraceClass FredholmDeterminant reference localDatum)

/-- The entropy readout is the logarithmic Fredholm determinant readout. -/
@[rep_depth operator]
theorem entropy_eq_logDet :
    B.entropy = relativeCountDensity B.fredholm :=
  B.entropy_eq_relativeCountDensity

end RelativeModularEntropyBridge

/-! ## 5. Combined bounded modular Fredholm/Drazin bridge -/

/--
Combined bounded modular Fredholm/Drazin bridge.

This packages the bounded Tomita/Krein shadow, a core projection witness, and a
relative Fredholm determinant readout.  The final comparison remains a stored
proof-carrying statement.
-/
structure ModularFredholmDrazinBridge
    (TraceClass : EndH₂ → Prop)
    (FredholmDeterminant : EndH₂ → ℝ → Prop) where
  referenceDatum : BoundedTomitaKreinDatum (E := E)
  localizedDatum : BoundedTomitaKreinDatum (E := E)

  core :
    localizedDatum.ModularCoreProjectionWitness

  relativeFredholm :
    RelativeFredholmDeterminantWitness TraceClass FredholmDeterminant
      referenceDatum localizedDatum

  core_fredholm_entropy_statement : Prop

  core_fredholm_entropy_witness :
    core_fredholm_entropy_statement

namespace ModularFredholmDrazinBridge

/-- The stored modular core/Fredholm/entropy comparison witness. -/
theorem core_fredholm_entropy
    (TraceClass : EndH₂ → Prop)
    (FredholmDeterminant : EndH₂ → ℝ → Prop)
    (B : ModularFredholmDrazinBridge (E := E) TraceClass FredholmDeterminant) :
    B.core_fredholm_entropy_statement :=
  B.core_fredholm_entropy_witness

/-- The localized modular Hamiltonian is modular-monogenic for its own datum. -/
@[simp]
theorem localized_modularHamiltonian_is_monogenic
    (TraceClass : EndH₂ → Prop)
    (FredholmDeterminant : EndH₂ → ℝ → Prop)
    (B : ModularFredholmDrazinBridge (E := E) TraceClass FredholmDeterminant) :
    B.localizedDatum.IsModularMonogenic B.localizedDatum.modularHamiltonian :=
  B.localizedDatum.modularHamiltonian_isModularMonogenic

end ModularFredholmDrazinBridge

end

end InfoGeometry.Canonical.ModularTomitaGeometry
-/
