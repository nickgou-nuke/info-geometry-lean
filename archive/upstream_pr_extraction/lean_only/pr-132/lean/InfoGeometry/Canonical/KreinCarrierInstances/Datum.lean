import InfoGeometry.Canonical.KreinCarrierInstances.Carrier
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic

open InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

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

end
