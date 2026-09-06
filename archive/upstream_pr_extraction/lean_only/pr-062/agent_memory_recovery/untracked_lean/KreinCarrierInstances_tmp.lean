import InfoGeometry.Topology.WallpaperSymmetry
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

open InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

/-!
# Concrete Klein-carrier Hestenes/Krein datum

This file supplies one explicit real two-dimensional carrier for the bounded
Hestenes/Krein modular interface.  The split Krein operator is the sign flip
`J(x,y) = (x,-y)` and the modular generator is the diagonal reflection
`G(x,y) = (-x,y)`.

The file deliberately uses the owner structures and lemmas from
`HestenesKreinModularGeometry`; it does not introduce placeholder predicates.
-/

/-- The concrete Klein-bottle chart carrier used by this module.

This is the `L²` product carrier from mathlib, not the raw product type.  The
actual Klein bottle quotient is represented separately by the imported `pg`
wallpaper action. -/
abbrev KleinBottleCarrier : Type := WithLp (2 : ENNReal) (ℝ × ℝ)

/-- The Möbius/glide chart symmetry `(x,y) ↦ (x + 1/2, -y)`. -/
def MoebiusSymmetry : KleinBottleCarrier ≃ KleinBottleCarrier where
  toFun p := WithLp.toLp (2 : ENNReal) (WithLp.fst p + (1 / 2 : ℝ), -WithLp.snd p)
  invFun p := WithLp.toLp (2 : ENNReal) (WithLp.fst p - (1 / 2 : ℝ), -WithLp.snd p)
  left_inv p := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp
  right_inv p := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp

/-- The canonical imported concrete `pg` wallpaper package. -/
def ConcretePG : InfoGeometry.Topology.Wallpaper.WallpaperGroupPG :=
  InfoGeometry.Topology.Wallpaper.concretePG

/-- The split fundamental symmetry `J(x,y) = (x,-y)`. -/
def fundamentalSymmetryKlein : KleinBottleCarrier →L[ℝ] KleinBottleCarrier where
  toFun p := WithLp.toLp (2 : ENNReal) (WithLp.fst p, -WithLp.snd p)
  map_add' p q := by
    simpa [WithLp.add_fst, WithLp.add_snd, neg_add, add_comm] using
      (WithLp.toLp_add (p := (2 : ENNReal))
        (x := (WithLp.fst p, -WithLp.snd p))
        (y := (WithLp.fst q, -WithLp.snd q)))
  map_smul' c p := by
    simpa [WithLp.smul_fst, WithLp.smul_snd, smul_neg] using
      (WithLp.toLp_smul (p := (2 : ENNReal)) (c := c)
        (x := (WithLp.fst p, -WithLp.snd p)))
  cont := by
    simpa using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).comp
        ((WithLp.continuous_fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).prodMk
          ((WithLp.continuous_snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).neg))

/-- The diagonal modular generator `G(x,y) = (-x,y)`. -/
def modularGeneratorKlein : KleinBottleCarrier →L[ℝ] KleinBottleCarrier where
  toFun p := WithLp.toLp (2 : ENNReal) (-WithLp.fst p, WithLp.snd p)
  map_add' p q := by
    simpa [WithLp.add_fst, WithLp.add_snd, neg_add, add_comm] using
      (WithLp.toLp_add (p := (2 : ENNReal))
        (x := (-WithLp.fst p, WithLp.snd p))
        (y := (-WithLp.fst q, WithLp.snd q)))
  map_smul' c p := by
    simpa [WithLp.smul_fst, WithLp.smul_snd, smul_neg] using
      (WithLp.toLp_smul (p := (2 : ENNReal)) (c := c)
        (x := (-WithLp.fst p, WithLp.snd p)))
  cont := by
    simpa using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).comp
        (((WithLp.continuous_fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).neg).prodMk
          (WithLp.continuous_snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)))

/-- The identity real endomorphism on the Klein carrier. -/
def idMapKlein : KleinBottleCarrier →L[ℝ] KleinBottleCarrier :=
  ContinuousLinearMap.id ℝ KleinBottleCarrier

@[simp]
theorem fundamentalSymmetryKlein_apply (p : KleinBottleCarrier) :
    fundamentalSymmetryKlein p =
      WithLp.toLp (2 : ENNReal) (WithLp.fst p, -WithLp.snd p) := by
  rfl

@[simp]
theorem modularGeneratorKlein_apply (p : KleinBottleCarrier) :
    modularGeneratorKlein p =
      WithLp.toLp (2 : ENNReal) (-WithLp.fst p, WithLp.snd p) := by
  rfl

/-- The split fundamental symmetry is involutive. -/
theorem fundamentalSymmetryKlein_sq :
    fundamentalSymmetryKlein * fundamentalSymmetryKlein =
      ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext p
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext <;> simp [fundamentalSymmetryKlein]

/-- The identity modular weight commutes with the generator. -/
theorem idMapKlein_comm_modularGenerator :
    idMapKlein * modularGeneratorKlein =
      modularGeneratorKlein * idMapKlein := by
  ext p
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext <;> simp [idMapKlein, modularGeneratorKlein]

/-- The generator is Krein self-adjoint for `J(x,y) = (x,-y)`. -/
theorem modularGeneratorKlein_krein_selfadjoint :
    fundamentalSymmetryKlein * modularGeneratorKlein * fundamentalSymmetryKlein =
      modularGeneratorKlein := by
  ext p
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext <;> simp [fundamentalSymmetryKlein, modularGeneratorKlein]

/-- Concrete bounded Hestenes/Krein modular datum on the L² Klein carrier. -/
def concreteKreinDatumKlein : KreinHestenesModularDatum KleinBottleCarrier where
  fundamentalSymmetry := fundamentalSymmetryKlein
  fundamentalSymmetry_involution := fundamentalSymmetryKlein_sq
  modularWeight := idMapKlein
  modularGenerator := modularGeneratorKlein
  modularWeight_comm_generator := idMapKlein_comm_modularGenerator
  generator_krein_selfadjoint := modularGeneratorKlein_krein_selfadjoint

/--
The concrete datum uses the native owner theorem:
monogenicity is exactly commutation with the modular generator.
-/
theorem concreteKreinDatumKlein_isMonogenic_iff_commutes
    (A : RealEnd KleinBottleCarrier) :
    KreinHestenesModularDatum.IsMonogenic concreteKreinDatumKlein A ↔
      concreteKreinDatumKlein.modularGenerator * A =
        A * concreteKreinDatumKlein.modularGenerator := by
  exact KreinHestenesModularDatum.isMonogenic_iff_commutes concreteKreinDatumKlein A

def concreteRotorFlowKlein_rotor : ℝ → RealEnd KleinBottleCarrier :=
  fun _ => ContinuousLinearMap.id ℝ KleinBottleCarrier

def concreteRotorFlowKlein_rotorInv : ℝ → RealEnd KleinBottleCarrier :=
  fun _ => ContinuousLinearMap.id ℝ KleinBottleCarrier

theorem concreteRotorFlowKlein_rotor_zero :
    concreteRotorFlowKlein_rotor 0 = ContinuousLinearMap.id ℝ KleinBottleCarrier := rfl

theorem concreteRotorFlowKlein_rotorInv_zero :
    concreteRotorFlowKlein_rotorInv 0 = ContinuousLinearMap.id ℝ KleinBottleCarrier := rfl

theorem concreteRotorFlowKlein_rotor_left_inv (t : ℝ) :
    concreteRotorFlowKlein_rotorInv t * concreteRotorFlowKlein_rotor t = ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext; simp [concreteRotorFlowKlein_rotor, concreteRotorFlowKlein_rotorInv]

theorem concreteRotorFlowKlein_rotor_right_inv (t : ℝ) :
    concreteRotorFlowKlein_rotor t * concreteRotorFlowKlein_rotorInv t = ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext; simp [concreteRotorFlowKlein_rotor, concreteRotorFlowKlein_rotorInv]

theorem concreteRotorFlowKlein_rotor_group (s t : ℝ) :
    concreteRotorFlowKlein_rotor (s + t) = concreteRotorFlowKlein_rotor s * concreteRotorFlowKlein_rotor t := by
  ext; simp [concreteRotorFlowKlein_rotor]

def concreteRotorFlowKlein_fixedByFlow
    (D : KreinHestenesModularDatum KleinBottleCarrier) : RealEnd KleinBottleCarrier → Prop :=
  fun A => D.modularGenerator * A = A * D.modularGenerator

theorem concreteRotorFlowKlein_fixedByFlow_iff_monogenic
    (D : KreinHestenesModularDatum KleinBottleCarrier) (A : RealEnd KleinBottleCarrier) :
    concreteRotorFlowKlein_fixedByFlow D A ↔ KreinHestenesModularDatum.IsMonogenic D A := by
  exact (KreinHestenesModularDatum.isMonogenic_iff_commutes D A).symm

/-- Trivial identity rotor flow, with the fixed predicate identified with monogenicity. -/
def concreteRotorFlowKlein
    (D : KreinHestenesModularDatum KleinBottleCarrier) : HestenesRotorFlow D where
  rotor := concreteRotorFlowKlein_rotor
  rotorInv := concreteRotorFlowKlein_rotorInv
  rotor_zero := concreteRotorFlowKlein_rotor_zero
  rotorInv_zero := concreteRotorFlowKlein_rotorInv_zero
  rotor_left_inv := concreteRotorFlowKlein_rotor_left_inv
  rotor_right_inv := concreteRotorFlowKlein_rotor_right_inv
  rotor_group_True := concreteRotorFlowKlein_rotor_group
  fixedByFlow := concreteRotorFlowKlein_fixedByFlow D
  fixedByFlow_iff_monogenic := concreteRotorFlowKlein_fixedByFlow_iff_monogenic D

def concreteCoreProjectorKlein_coreProjector : RealEnd KleinBottleCarrier :=
  ContinuousLinearMap.id ℝ KleinBottleCarrier

def concreteCoreProjectorKlein_nilProjector : RealEnd KleinBottleCarrier :=
  0

theorem concreteCoreProjectorKlein_core_idempotent :
    concreteCoreProjectorKlein_coreProjector * concreteCoreProjectorKlein_coreProjector =
      concreteCoreProjectorKlein_coreProjector := by
  ext; simp [concreteCoreProjectorKlein_coreProjector]

theorem concreteCoreProjectorKlein_nil_idempotent :
    concreteCoreProjectorKlein_nilProjector * concreteCoreProjectorKlein_nilProjector =
      concreteCoreProjectorKlein_nilProjector := by
  ext; simp [concreteCoreProjectorKlein_nilProjector]

theorem concreteCoreProjectorKlein_core_nil_disjoint :
    concreteCoreProjectorKlein_coreProjector * concreteCoreProjectorKlein_nilProjector = 0 := by
  ext; simp [concreteCoreProjectorKlein_coreProjector, concreteCoreProjectorKlein_nilProjector]

theorem concreteCoreProjectorKlein_nil_core_disjoint :
    concreteCoreProjectorKlein_nilProjector * concreteCoreProjectorKlein_coreProjector = 0 := by
  ext; simp [concreteCoreProjectorKlein_coreProjector, concreteCoreProjectorKlein_nilProjector]

theorem concreteCoreProjectorKlein_core_add_nil :
    concreteCoreProjectorKlein_coreProjector + concreteCoreProjectorKlein_nilProjector =
      ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext; simp [concreteCoreProjectorKlein_coreProjector, concreteCoreProjectorKlein_nilProjector]

theorem concreteCoreProjectorKlein_core_commutes_with_generator
    (D : KreinHestenesModularDatum KleinBottleCarrier) :
    concreteCoreProjectorKlein_coreProjector * D.modularGenerator =
      D.modularGenerator * concreteCoreProjectorKlein_coreProjector := by
  ext; simp [concreteCoreProjectorKlein_coreProjector]

theorem concreteCoreProjectorKlein_core_krein_selfadjoint
    (D : KreinHestenesModularDatum KleinBottleCarrier) :
    D.fundamentalSymmetry * concreteCoreProjectorKlein_coreProjector * D.fundamentalSymmetry =
      concreteCoreProjectorKlein_coreProjector := by
  simpa [concreteCoreProjectorKlein_coreProjector] using D.fundamentalSymmetry_involution

/-- Identity-core, zero-nil modular core projector. -/
def concreteCoreProjectorKlein
    (D : KreinHestenesModularDatum KleinBottleCarrier) : KreinModularCoreProjector D where
  coreProjector := concreteCoreProjectorKlein_coreProjector
  nilProjector := concreteCoreProjectorKlein_nilProjector
  core_idempotent := concreteCoreProjectorKlein_core_idempotent
  nil_idempotent := concreteCoreProjectorKlein_nil_idempotent
  core_nil_disjoint := concreteCoreProjectorKlein_core_nil_disjoint
  nil_core_disjoint := concreteCoreProjectorKlein_nil_core_disjoint
  core_add_nil := concreteCoreProjectorKlein_core_add_nil
  core_commutes_with_generator := concreteCoreProjectorKlein_core_commutes_with_generator D
  core_krein_selfadjoint := concreteCoreProjectorKlein_core_krein_selfadjoint D

def concreteRelativeFredholmKlein_modularDefect : RealEnd KleinBottleCarrier := 0

theorem concreteRelativeFredholmKlein_modularDefect_eq :
    concreteRelativeFredholmKlein_modularDefect =
      concreteKreinDatumKlein.modularWeight - concreteKreinDatumKlein.modularWeight := by
  ext; simp [concreteRelativeFredholmKlein_modularDefect, concreteKreinDatumKlein]

def concreteRelativeFredholmKlein_fredholm_determinant : ℝ := 1

def concreteRelativeFredholmKlein_fredholm_kreinTrace : ℝ := 0

theorem concreteRelativeFredholmKlein_fredholm_determinant_first_order :
    concreteRelativeFredholmKlein_fredholm_determinant = 1 + concreteRelativeFredholmKlein_fredholm_kreinTrace := by
  norm_num [concreteRelativeFredholmKlein_fredholm_determinant, concreteRelativeFredholmKlein_fredholm_kreinTrace]

def concreteRelativeFredholmKlein_fredholm : KreinFredholmDeterminantContract concreteRelativeFredholmKlein_modularDefect where
  determinant := concreteRelativeFredholmKlein_fredholm_determinant
  kreinTrace := concreteRelativeFredholmKlein_fredholm_kreinTrace
  determinant_first_order := concreteRelativeFredholmKlein_fredholm_determinant_first_order

def concreteRelativeFredholmKlein_relativePartitionReadout : ℝ := 1

theorem concreteRelativeFredholmKlein_relativePartitionReadout_eq_det :
    concreteRelativeFredholmKlein_relativePartitionReadout = concreteRelativeFredholmKlein_fredholm.determinant := by
  rfl

def concreteRelativeFredholmKlein_relativeCountDensity : ℝ := 0

theorem concreteRelativeFredholmKlein_relativeCountDensity_eq_log :
    concreteRelativeFredholmKlein_relativeCountDensity = Real.log concreteRelativeFredholmKlein_relativePartitionReadout := by
  dsimp [concreteRelativeFredholmKlein_relativeCountDensity, concreteRelativeFredholmKlein_relativePartitionReadout]
  rw [Real.log_one]

/-- Concrete zero-defect relative Fredholm datum. -/
def concreteRelativeFredholmKlein : RelativeKreinModularFredholmDatum KleinBottleCarrier where
  referenceDatum := concreteKreinDatumKlein
  localizedDatum := concreteKreinDatumKlein
  modularDefect := concreteRelativeFredholmKlein_modularDefect
  modularDefect_eq := concreteRelativeFredholmKlein_modularDefect_eq
  fredholm := concreteRelativeFredholmKlein_fredholm
  relativePartitionReadout := concreteRelativeFredholmKlein_relativePartitionReadout
  relativePartitionReadout_eq_det := concreteRelativeFredholmKlein_relativePartitionReadout_eq_det
  relativeCountDensity := concreteRelativeFredholmKlein_relativeCountDensity
  relativeCountDensity_eq_log := concreteRelativeFredholmKlein_relativeCountDensity_eq_log

theorem concreteBridgeKlein_core_fredholm_count_comparison :
    concreteRelativeFredholmKlein.relativeCountDensity =
      Real.log (1 + concreteRelativeFredholmKlein.fredholm.kreinTrace) := by
  dsimp [concreteRelativeFredholmKlein, concreteRelativeFredholmKlein_relativeCountDensity, concreteRelativeFredholmKlein_fredholm, concreteRelativeFredholmKlein_fredholm_kreinTrace]
  rw [add_zero, Real.log_one]

/-- Concrete Hestenes/Krein modular Fredholm bridge on the Klein carrier. -/
def concreteBridgeKlein : HestenesKreinModularFredholmBridge KleinBottleCarrier where
  datum := concreteKreinDatumKlein
  flow := concreteRotorFlowKlein concreteKreinDatumKlein
  core := concreteCoreProjectorKlein concreteKreinDatumKlein
  relativeFredholm := concreteRelativeFredholmKlein
  core_fredholm_count_comparison := concreteBridgeKlein_core_fredholm_count_comparison

/-- The concrete bridge has zero Krein trace by explicit construction. -/
theorem concreteBridgeKlein_kreinTrace :
    concreteBridgeKlein.relativeFredholm.fredholm.kreinTrace = 0 := by
  rfl

/-- The arithmetic input for `137`: its 2-adic valuation is zero. -/
theorem padicValNat_two_137 : padicValNat 2 137 = 0 := by
  norm_num [padicValNat.eq_zero_of_not_dvd]

/--
The concrete bridge has the stated trace-zero law for `137`.  The proof is
still a hardcoded readout of this concrete zero-defect bridge; it is not an
unconditional p-adic anomaly theorem.
-/
theorem concreteBridgeKlein_traceZeroAnomalyResolution_137 :
    HestenesKreinModularFredholmBridge.TraceZeroAnomalyResolution
      concreteBridgeKlein 137 := by
  intro _h137
  exact concreteBridgeKlein_kreinTrace

/-- Read back trace zero from the explicit `137` p-adic valuation law. -/
theorem concreteBridgeKlein_traceZero_of_padicValNat_137 :
    concreteBridgeKlein.relativeFredholm.fredholm.kreinTrace = 0 :=
  concreteBridgeKlein_traceZeroAnomalyResolution_137 padicValNat_two_137

end
