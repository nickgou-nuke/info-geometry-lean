import Mathlib.Tactic

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Quantum.ThermofieldDouble

/--
Finite quantum spectrum for theorem-safe TFD coefficient transport.
-/
structure FiniteQuantumSpectrum (Level : Type*) [DecidableEq Level] where
  /-- Finite spectrum support. -/
  levels : Finset Level
  /-- Energy function. -/
  energy : Level → ℝ

namespace FiniteQuantumSpectrum

variable {Level : Type*} [DecidableEq Level]

/-- Finite Gibbs partition function `Z(β) = ∑_n e^{-βE_n}`. -/
def partition (S : FiniteQuantumSpectrum Level) (β : ℝ) : ℝ :=
  Finset.sum S.levels (fun n => Real.exp (-β * S.energy n))

/-- Partition function is nonnegative. -/
theorem partition_nonneg (S : FiniteQuantumSpectrum Level) (β : ℝ) : 0 ≤ partition S β := by
  unfold partition
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- Nonempty finite partition is strictly positive. -/
theorem partition_pos (S : FiniteQuantumSpectrum Level) (β : ℝ) (h : S.levels.Nonempty) :
    0 < partition S β := by
  unfold partition
  exact Finset.sum_pos (fun _ _ => by positivity) h

/-- Nonempty support yields a nonzero Gibbs partition value. -/
theorem partition_pos_ne_zero (S : FiniteQuantumSpectrum Level) (β : ℝ) (h : S.levels.Nonempty) :
    partition S β ≠ 0 := by
  exact ne_of_gt (partition_pos S β h)

/-- Denominator nonzero for nonempty finite partition. -/
theorem sqrt_partition_ne_zero (S : FiniteQuantumSpectrum Level) (β : ℝ) (h : S.levels.Nonempty) :
    (Real.sqrt (partition S β) : ℂ) ≠ 0 := by
  have hsqrt : Real.sqrt (partition S β) ≠ 0 := by
    exact (Real.sqrt_ne_zero (partition_nonneg S β)).2 (partition_pos_ne_zero S β h)
  exact Complex.ofReal_ne_zero.mpr hsqrt

/--
TFD coefficient with independent left/right boundary times.

The phase is `exp(-i (tL + tR) E_n)`.
-/
def tfdCoeff
    (S : FiniteQuantumSpectrum Level) (β tL tR : ℝ) (n : Level) : ℂ :=
  Complex.exp
      (-(β / 2 : ℂ) * (S.energy n : ℂ)
        - Complex.I * ((tL + tR : ℝ) : ℂ) * (S.energy n : ℂ))
    / (Real.sqrt (partition S β) : ℂ)

/-- Zero-time specialization recovers the thermal coefficient. -/
theorem tfdCoeff_zero_time
    (S : FiniteQuantumSpectrum Level) (β : ℝ) (n : Level) :
    S.tfdCoeff β 0 0 n =
      Complex.exp (-(β / 2 : ℂ) * (S.energy n : ℂ)) / (Real.sqrt (partition S β) : ℂ) := by
  simp [tfdCoeff]

/-- TFD coefficient restricted to the finite support indices. -/
def tfdCoeffOnSupport
    (S : FiniteQuantumSpectrum Level) (β tL tR : ℝ) (n : {n : Level // n ∈ S.levels}) : ℂ :=
  S.tfdCoeff β tL tR n.1

/-- Zero-extension of the TFD coefficient outside the finite support. -/
def tfdCoeffSupported
    (S : FiniteQuantumSpectrum Level) (β tL tR : ℝ) (n : Level) : ℂ :=
  if n ∈ S.levels then S.tfdCoeff β tL tR n else 0

/-- Support-vanishing is definitional by construction. -/
theorem tfdCoeffSupported_eq_zero_of_not_mem
    (S : FiniteQuantumSpectrum Level) (β tL tR : ℝ) {n : Level}
    (hn : n ∉ S.levels) :
    S.tfdCoeffSupported β tL tR n = 0 := by
  simp [tfdCoeffSupported, hn]

/-- Restricted support map is the restriction of the extension map. -/
theorem tfdCoeffOnSupport_eq_supported
    (S : FiniteQuantumSpectrum Level) (β tL tR : ℝ) (n : {n : Level // n ∈ S.levels}) :
    S.tfdCoeffOnSupport β tL tR n = S.tfdCoeffSupported β tL tR n.1 := by
  simp [tfdCoeffOnSupport, tfdCoeffSupported, n.property]

end FiniteQuantumSpectrum

/--
Bulk geometry for bridge calibrations.  Connectivity is the native Mathlib
topological predicate on an explicit bulk carrier.
-/
structure BulkGeometry
    (Point : Type*) [TopologicalSpace Point] where
  /-- Points belonging to the modeled bulk region. -/
  carrier : Set Point
  /-- The modeled bulk region is nonempty and preconnected. -/
  connected : IsConnected carrier
  /-- Bulk interior-volume readout. -/
  interiorVolume : ℝ → ℝ

/--
Entanglement↔ER bridge calibration for a concrete model.

This is intentionally a data contract, not a global axiom.
-/
structure EREPRCalibration (BoundaryState Bulk : Type*) where
  /-- Entanglement predicate on boundary data. -/
  isEPR : BoundaryState → Prop

  /-- Existence predicate for a bridge in a bulk state. -/
  hasERBridge : Bulk → Prop

  /-- State-bulk realization relation. -/
  realizes : BoundaryState → Bulk → Prop

  /-- Entanglement plus realization implies a bridge in this model. -/
  er_of_epr :
    ∀ ψ : BoundaryState, ∀ g : Bulk,
      realizes ψ g →
      isEPR ψ → hasERBridge g

  /-- Bridge plus realization implies entanglement in this model. -/
  epr_of_er :
    ∀ ψ : BoundaryState, ∀ g : Bulk,
      realizes ψ g →
      hasERBridge g → isEPR ψ

namespace EREPRCalibration

variable {BoundaryState Bulk : Type*}
variable (C : EREPRCalibration BoundaryState Bulk)

/-- Entanglement/bridge exchange by calibration fields on a given realization. -/
theorem er_iff_epr_on_realization
    {ψ : BoundaryState} {g : Bulk}
    (hrealizes : C.realizes ψ g) :
    C.hasERBridge g ↔ C.isEPR ψ := by
  constructor
  · exact C.epr_of_er ψ g hrealizes
  · exact C.er_of_epr ψ g hrealizes

end EREPRCalibration

/--
RT/HRT-style entropy-area calibration.

This is a model-specific witness that must be supplied to use the law.
-/
structure RyuTakayanagiCalibration (Region Surface : Type*) where
  entropy : Region → ℝ
  area : Surface → ℝ
  extremalSurfaceOf : Region → Surface
  NewtonConstant : ℝ
  NewtonConstant_pos : 0 < NewtonConstant

  /-- Calibrated area law for each region. -/
  entropy_eq_area_div :
    ∀ A : Region,
      entropy A = area (extremalSurfaceOf A) / (4 * NewtonConstant)

namespace RyuTakayanagiCalibration

variable {Region Surface : Type*}
variable (R : RyuTakayanagiCalibration Region Surface)

/-- Area calibration projection from a supplied calibration witness. -/
theorem entropy_eq_area_over_fourG (A : Region) :
    R.entropy A = R.area (R.extremalSurfaceOf A) / (4 * R.NewtonConstant) :=
  R.entropy_eq_area_div A

end RyuTakayanagiCalibration

/--
Exact bridge-volume growth law (model-supplied).
-/
structure ExactERBridgeGrowth
    (Point : Type*) [TopologicalSpace Point] where
  bulk : BulkGeometry Point
  rate : ℝ

  /-- Exact affine growth law between two times. -/
  linearGrowth : ∀ t₁ t₂ : ℝ,
    bulk.interiorVolume t₂ - bulk.interiorVolume t₁ = rate * (t₂ - t₁)

namespace ExactERBridgeGrowth

variable {Point : Type*} [TopologicalSpace Point]
variable (G : ExactERBridgeGrowth Point)

/-- Linear-in-time law is exactly the supplied bridge growth witness. -/
theorem volume_difference_eq_rate_mul_time (t₁ t₂ : ℝ) :
    G.bulk.interiorVolume t₂ - G.bulk.interiorVolume t₁ = G.rate * (t₂ - t₁) :=
  G.linearGrowth t₁ t₂

end ExactERBridgeGrowth

/--
Prime-bit spectral specialization.

This realizes finite bit-energy from a finite prime support and proves
`E(ε) = log n(ε)`.
-/
structure PrimeBitSpectrum where
  /-- Finite profile index type. -/
  Index : Type*
  /-- Finiteness and decidable equality on profile indices. -/
  fintypeIndex : Fintype Index
  decEqIndex : DecidableEq Index
  /-- Prime label assignment on profile indices. -/
  prime : Index → ℕ
  /-- Prime label validity. -/
  isPrime : ∀ i : Index, Nat.Prime (prime i)
  /-- Distinct indices have distinct prime labels. -/
  prime_injective : Function.Injective prime

namespace PrimeBitSpectrum

attribute [instance] PrimeBitSpectrum.fintypeIndex
attribute [instance] PrimeBitSpectrum.decEqIndex

/-- Profile on the finite prime index type. -/
abbrev Profile (P : PrimeBitSpectrum) : Type :=
  P.Index → Bool

/-- Energy on a Boolean occupancy configuration. -/
def bitEnergy (P : PrimeBitSpectrum) (ε : P.Profile) : ℝ :=
  ∑ i : P.Index, if ε i then Real.log (P.prime i) else 0

/-- Integer label attached to the same finite occupancy. -/
def bitInteger (P : PrimeBitSpectrum) (ε : P.Profile) : ℕ :=
  ∏ i : P.Index, if ε i then P.prime i else 1

/-- Finite prime support log identity: `E(ε) = log n(ε)`. -/
theorem bitEnergy_eq_log_bitInteger (P : PrimeBitSpectrum) (ε : P.Profile) :
    P.bitEnergy ε = Real.log (P.bitInteger ε) := by
  have hlog_term :
      ∀ i : P.Index, (if ε i then (P.prime i : ℝ) else 1) ≠ 0 := by
    intro i
    by_cases hpε : ε i
    · simpa [hpε] using (by
        exact_mod_cast (P.isPrime i).ne_zero : (P.prime i : ℝ) ≠ 0)
    · simp [hpε]

  have hlog_term_univ :
      ∀ i ∈ (Finset.univ : Finset P.Index),
        (if ε i then (P.prime i : ℝ) else 1) ≠ 0 := by
    intro i hi
    exact hlog_term i

  calc
    P.bitEnergy ε
        = ∑ i : P.Index, Real.log (if ε i then (P.prime i : ℝ) else 1) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hpε : ε i
          · simp [hpε]
          · simp [hpε]
    _ = Real.log (∏ i : P.Index, if ε i then (P.prime i : ℝ) else 1) := by
          symm
          exact Real.log_prod hlog_term_univ
    _ = Real.log (P.bitInteger ε : ℝ) := by
          simp [bitInteger]

/-- Arithmetic TFD coefficient for finite prime-bit profiles. -/
def arithmeticTFDCoeff
    (P : PrimeBitSpectrum)
    (β t : ℝ)
    (ε : P.Profile) (Z : ℝ) : ℂ :=
  let n : ℝ := (P.bitInteger ε : ℝ)
  Complex.exp
      (-(((β / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (Real.log n : ℂ))
    / (Real.sqrt Z : ℂ)

/-- Profile-level partial order used for primitive-set antichain checks. -/
def profileLe (P : PrimeBitSpectrum) (ε η : P.Profile) : Prop :=
  ∀ i : P.Index, ε i = true → η i = true

/-- Profile antichain predicate. -/
def isAntichain (P : PrimeBitSpectrum) (S : Set P.Profile) : Prop :=
  ∀ ε η, ε ∈ S → η ∈ S → ε ≠ η → ¬ profileLe P ε η

/-- Integer primitiveness predicate for integer image sets. -/
def isPrimitive (S : Set ℕ) : Prop :=
  ∀ n ∈ S, ∀ m ∈ S, n ≠ m → ¬ n ∣ m

/--
Calibration bridge from finite-profile antichains to primitive integer families.
-/
structure PrimitiveAntichainCalibration (P : PrimeBitSpectrum) where
  primitive_iff_antichain :
    ∀ S : Set P.Profile,
      isAntichain P S ↔ isPrimitive (P.bitInteger '' S)

/-- Arithmetic modular calibration for prime-bit state profiles. -/
structure ArithmeticModularCalibration (P : PrimeBitSpectrum) where
  State : Type*
  modular_hamiltonian_val : State → ℝ
  profileOf : State → P.Profile
  modular_eq_arithmetic :
    ∀ s : State,
      modular_hamiltonian_val s = P.bitEnergy (profileOf s)

namespace ArithmeticModularCalibration

variable {P : PrimeBitSpectrum}
variable (C : ArithmeticModularCalibration P)

/-- The calibrated modular Hamiltonian value is the log of the arithmetic integer readout. -/
theorem modular_hamiltonian_val_eq_log_bitInteger
    (s : C.State) :
    C.modular_hamiltonian_val s =
      Real.log (P.bitInteger (C.profileOf s) : ℝ) := by
  calc
    C.modular_hamiltonian_val s
        = P.bitEnergy (C.profileOf s) :=
            C.modular_eq_arithmetic s
    _ = Real.log (P.bitInteger (C.profileOf s) : ℝ) :=
            P.bitEnergy_eq_log_bitInteger (C.profileOf s)

end ArithmeticModularCalibration

end PrimeBitSpectrum

end InfoGeometry.Quantum.ThermofieldDouble
