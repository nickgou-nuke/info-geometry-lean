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
-/

abbrev KleinBottleCarrier : Type := WithLp (2 : ENNReal) (ℝ × ℝ)

def MoebiusSymmetry_toFun (p : KleinBottleCarrier) : KleinBottleCarrier :=
  WithLp.toLp (2 : ENNReal) (WithLp.fst p + (1 / 2 : ℝ), -WithLp.snd p)

def MoebiusSymmetry_invFun (p : KleinBottleCarrier) : KleinBottleCarrier :=
  WithLp.toLp (2 : ENNReal) (WithLp.fst p - (1 / 2 : ℝ), -WithLp.snd p)

lemma MoebiusSymmetry_left_inv (p : KleinBottleCarrier) :
    MoebiusSymmetry_invFun (MoebiusSymmetry_toFun p) = p := by
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext <;> simp [MoebiusSymmetry_toFun, MoebiusSymmetry_invFun]

lemma MoebiusSymmetry_right_inv (p : KleinBottleCarrier) :
    MoebiusSymmetry_toFun (MoebiusSymmetry_invFun p) = p := by
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext <;> simp [MoebiusSymmetry_toFun, MoebiusSymmetry_invFun]

/-- The Möbius/glide chart symmetry `(x,y) ↦ (x + 1/2, -y)`. -/
def MoebiusSymmetry : KleinBottleCarrier ≃ KleinBottleCarrier where
  toFun := MoebiusSymmetry_toFun
  invFun := MoebiusSymmetry_invFun
  left_inv := MoebiusSymmetry_left_inv
  right_inv := MoebiusSymmetry_right_inv

def ConcretePG : InfoGeometry.Topology.Wallpaper.WallpaperGroupPG :=
  InfoGeometry.Topology.Wallpaper.concretePG

def fundamentalSymmetryKlein_toFun (p : KleinBottleCarrier) : KleinBottleCarrier :=
  WithLp.toLp (2 : ENNReal) (WithLp.fst p, -WithLp.snd p)

lemma fundamentalSymmetryKlein_map_add (p q : KleinBottleCarrier) :
    fundamentalSymmetryKlein_toFun (p + q) =
      fundamentalSymmetryKlein_toFun p + fundamentalSymmetryKlein_toFun q := by
  simpa [fundamentalSymmetryKlein_toFun, WithLp.add_fst, WithLp.add_snd, neg_add, add_comm] using
    (WithLp.toLp_add (p := (2 : ENNReal))
      (x := (WithLp.fst p, -WithLp.snd p))
      (y := (WithLp.fst q, -WithLp.snd q)))

lemma fundamentalSymmetryKlein_map_smul (c : ℝ) (p : KleinBottleCarrier) :
    fundamentalSymmetryKlein_toFun (c • p) =
      c • fundamentalSymmetryKlein_toFun p := by
  simpa [fundamentalSymmetryKlein_toFun, WithLp.smul_fst, WithLp.smul_snd, smul_neg] using
    (WithLp.toLp_smul (p := (2 : ENNReal)) (c := c)
      (x := (WithLp.fst p, -WithLp.snd p)))

lemma fundamentalSymmetryKlein_cont :
    Continuous fundamentalSymmetryKlein_toFun := by
  simpa [fundamentalSymmetryKlein_toFun] using
    (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).comp
      ((WithLp.continuous_fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).prodMk
        ((WithLp.continuous_snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).neg))

/-- The split fundamental symmetry `J(x,y) = (x,-y)`. -/
def fundamentalSymmetryKlein : KleinBottleCarrier →L[ℝ] KleinBottleCarrier where
  toFun := fundamentalSymmetryKlein_toFun
  map_add' := fundamentalSymmetryKlein_map_add
  map_smul' := fundamentalSymmetryKlein_map_smul
  cont := fundamentalSymmetryKlein_cont

def modularGeneratorKlein_toFun (p : KleinBottleCarrier) : KleinBottleCarrier :=
  WithLp.toLp (2 : ENNReal) (-WithLp.fst p, WithLp.snd p)

lemma modularGeneratorKlein_map_add (p q : KleinBottleCarrier) :
    modularGeneratorKlein_toFun (p + q) =
      modularGeneratorKlein_toFun p + modularGeneratorKlein_toFun q := by
  simpa [modularGeneratorKlein_toFun, WithLp.add_fst, WithLp.add_snd, neg_add, add_comm] using
    (WithLp.toLp_add (p := (2 : ENNReal))
      (x := (-WithLp.fst p, WithLp.snd p))
      (y := (-WithLp.fst q, WithLp.snd q)))

lemma modularGeneratorKlein_map_smul (c : ℝ) (p : KleinBottleCarrier) :
    modularGeneratorKlein_toFun (c • p) =
      c • modularGeneratorKlein_toFun p := by
  simpa [modularGeneratorKlein_toFun, WithLp.smul_fst, WithLp.smul_snd, smul_neg] using
    (WithLp.toLp_smul (p := (2 : ENNReal)) (c := c)
      (x := (-WithLp.fst p, WithLp.snd p)))

lemma modularGeneratorKlein_cont :
    Continuous modularGeneratorKlein_toFun := by
  simpa [modularGeneratorKlein_toFun] using
    (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).comp
      (((WithLp.continuous_fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).neg).prodMk
        (WithLp.continuous_snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)))

/-- The diagonal modular generator `G(x,y) = (-x,y)`. -/
def modularGeneratorKlein : KleinBottleCarrier →L[ℝ] KleinBottleCarrier where
  toFun := modularGeneratorKlein_toFun
  map_add' := modularGeneratorKlein_map_add
  map_smul' := modularGeneratorKlein_map_smul
  cont := modularGeneratorKlein_cont

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

theorem fundamentalSymmetryKlein_sq :
    fundamentalSymmetryKlein * fundamentalSymmetryKlein =
      ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext p
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext <;> simp [fundamentalSymmetryKlein, fundamentalSymmetryKlein_toFun]

theorem idMapKlein_comm_modularGenerator :
    idMapKlein * modularGeneratorKlein =
      modularGeneratorKlein * idMapKlein := by
  ext p
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext <;> simp [idMapKlein, modularGeneratorKlein, modularGeneratorKlein_toFun]

theorem modularGeneratorKlein_krein_selfadjoint :
    fundamentalSymmetryKlein * modularGeneratorKlein * fundamentalSymmetryKlein =
      modularGeneratorKlein := by
  ext p
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext <;> simp [fundamentalSymmetryKlein, fundamentalSymmetryKlein_toFun, modularGeneratorKlein, modularGeneratorKlein_toFun]

def concreteKreinDatumKlein : KreinHestenesModularDatum KleinBottleCarrier where
  fundamentalSymmetry := fundamentalSymmetryKlein
  fundamentalSymmetry_involution := fundamentalSymmetryKlein_sq
  modularWeight := idMapKlein
  modularGenerator := modularGeneratorKlein
  modularWeight_comm_generator := idMapKlein_comm_modularGenerator
  generator_krein_selfadjoint := modularGeneratorKlein_krein_selfadjoint

theorem concreteKreinDatumKlein_isMonogenic_iff_commutes
    (A : RealEnd KleinBottleCarrier) :
    KreinHestenesModularDatum.IsMonogenic concreteKreinDatumKlein A ↔
      concreteKreinDatumKlein.modularGenerator * A =
        A * concreteKreinDatumKlein.modularGenerator := by
  exact KreinHestenesModularDatum.isMonogenic_iff_commutes concreteKreinDatumKlein A

lemma concreteRotorFlowKlein_left_inv (_t : ℝ) :
    (ContinuousLinearMap.id ℝ KleinBottleCarrier) * (ContinuousLinearMap.id ℝ KleinBottleCarrier) =
      ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext
  simp

lemma concreteRotorFlowKlein_right_inv (_t : ℝ) :
    (ContinuousLinearMap.id ℝ KleinBottleCarrier) * (ContinuousLinearMap.id ℝ KleinBottleCarrier) =
      ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext
  simp

lemma concreteRotorFlowKlein_group_True (_s _t : ℝ) :
    (ContinuousLinearMap.id ℝ KleinBottleCarrier) =
      (ContinuousLinearMap.id ℝ KleinBottleCarrier) * (ContinuousLinearMap.id ℝ KleinBottleCarrier) := by
  ext
  simp

lemma concreteRotorFlowKlein_fixed_iff
    (D : KreinHestenesModularDatum KleinBottleCarrier)
    (A : RealEnd KleinBottleCarrier) :
    (D.modularGenerator * A = A * D.modularGenerator) ↔
      KreinHestenesModularDatum.IsMonogenic D A := by
  exact (KreinHestenesModularDatum.isMonogenic_iff_commutes D A).symm

def concreteRotorFlowKlein
    (D : KreinHestenesModularDatum KleinBottleCarrier) : HestenesRotorFlow D where
  rotor := fun _ => ContinuousLinearMap.id ℝ KleinBottleCarrier
  rotorInv := fun _ => ContinuousLinearMap.id ℝ KleinBottleCarrier
  rotor_zero := rfl
  rotorInv_zero := rfl
  rotor_left_inv := concreteRotorFlowKlein_left_inv
  rotor_right_inv := concreteRotorFlowKlein_right_inv
  rotor_group_True := concreteRotorFlowKlein_group_True
  fixedByFlow := fun A => D.modularGenerator * A = A * D.modularGenerator
  fixedByFlow_iff_monogenic := concreteRotorFlowKlein_fixed_iff D

lemma concreteCoreProjectorKlein_core_idempotent :
    (ContinuousLinearMap.id ℝ KleinBottleCarrier) * (ContinuousLinearMap.id ℝ KleinBottleCarrier) =
      ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext
  simp

lemma concreteCoreProjectorKlein_nil_idempotent :
    (0 : RealEnd KleinBottleCarrier) * 0 = 0 := by
  ext
  simp

lemma concreteCoreProjectorKlein_core_nil_disjoint :
    (ContinuousLinearMap.id ℝ KleinBottleCarrier) * (0 : RealEnd KleinBottleCarrier) = 0 := by
  ext
  simp

lemma concreteCoreProjectorKlein_nil_core_disjoint :
    (0 : RealEnd KleinBottleCarrier) * (ContinuousLinearMap.id ℝ KleinBottleCarrier) = 0 := by
  ext
  simp

lemma concreteCoreProjectorKlein_core_add_nil :
    (ContinuousLinearMap.id ℝ KleinBottleCarrier) + (0 : RealEnd KleinBottleCarrier) =
      ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext
  simp

lemma concreteCoreProjectorKlein_core_comm_gen
    (D : KreinHestenesModularDatum KleinBottleCarrier) :
    (ContinuousLinearMap.id ℝ KleinBottleCarrier) * D.modularGenerator =
      D.modularGenerator * (ContinuousLinearMap.id ℝ KleinBottleCarrier) := by
  ext
  simp

lemma concreteCoreProjectorKlein_core_krein
    (D : KreinHestenesModularDatum KleinBottleCarrier) :
    D.fundamentalSymmetry * (ContinuousLinearMap.id ℝ KleinBottleCarrier) * D.fundamentalSymmetry =
      ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  simpa using D.fundamentalSymmetry_involution

def concreteCoreProjectorKlein
    (D : KreinHestenesModularDatum KleinBottleCarrier) : KreinModularCoreProjector D where
  coreProjector := ContinuousLinearMap.id ℝ KleinBottleCarrier
  nilProjector := 0
  core_idempotent := concreteCoreProjectorKlein_core_idempotent
  nil_idempotent := concreteCoreProjectorKlein_nil_idempotent
  core_nil_disjoint := concreteCoreProjectorKlein_core_nil_disjoint
  nil_core_disjoint := concreteCoreProjectorKlein_nil_core_disjoint
  core_add_nil := concreteCoreProjectorKlein_core_add_nil
  core_commutes_with_generator := concreteCoreProjectorKlein_core_comm_gen D
  core_krein_selfadjoint := concreteCoreProjectorKlein_core_krein D

lemma concreteRelativeFredholmKlein_defect_eq :
    (0 : RealEnd KleinBottleCarrier) =
      concreteKreinDatumKlein.modularWeight - concreteKreinDatumKlein.modularWeight := by
  ext
  simp [concreteKreinDatumKlein]

lemma concreteRelativeFredholmKlein_det_first_order :
    (1 : ℝ) = 1 + 0 := by norm_num

lemma concreteRelativeFredholmKlein_countDensity_eq :
    (0 : ℝ) = Real.log 1 := by
  rw [Real.log_one]

def concreteRelativeFredholmKlein : RelativeKreinModularFredholmDatum KleinBottleCarrier where
  referenceDatum := concreteKreinDatumKlein
  localizedDatum := concreteKreinDatumKlein
  modularDefect := 0
  modularDefect_eq := concreteRelativeFredholmKlein_defect_eq
  fredholm :=
    { determinant := 1
      kreinTrace := 0
      determinant_first_order := concreteRelativeFredholmKlein_det_first_order }
  relativePartitionReadout := 1
  relativePartitionReadout_eq_det := rfl
  relativeCountDensity := 0
  relativeCountDensity_eq_log := concreteRelativeFredholmKlein_countDensity_eq

lemma concreteBridgeKlein_core_fredholm_count :
    concreteRelativeFredholmKlein.relativeCountDensity =
      Real.log (1 + concreteRelativeFredholmKlein.fredholm.kreinTrace) := by
  simp [concreteRelativeFredholmKlein, Real.log_one]

def concreteBridgeKlein : HestenesKreinModularFredholmBridge KleinBottleCarrier where
  datum := concreteKreinDatumKlein
  flow := concreteRotorFlowKlein concreteKreinDatumKlein
  core := concreteCoreProjectorKlein concreteKreinDatumKlein
  relativeFredholm := concreteRelativeFredholmKlein
  core_fredholm_count_comparison := concreteBridgeKlein_core_fredholm_count

theorem concreteBridgeKlein_kreinTrace :
    concreteBridgeKlein.relativeFredholm.fredholm.kreinTrace = 0 := by
  rfl

theorem padicValNat_two_137 : padicValNat 2 137 = 0 := by
  norm_num [padicValNat.eq_zero_of_not_dvd]

theorem concreteBridgeKlein_traceZeroAnomalyResolution_137 :
    HestenesKreinModularFredholmBridge.TraceZeroAnomalyResolution
      concreteBridgeKlein 137 := by
  intro _h137
  exact concreteBridgeKlein_kreinTrace

theorem concreteBridgeKlein_traceZero_of_padicValNat_137 :
    concreteBridgeKlein.relativeFredholm.fredholm.kreinTrace = 0 :=
  concreteBridgeKlein_traceZeroAnomalyResolution_137 padicValNat_two_137

end
