import proofs.MobiusCantorTKKClosure
import proofs.TopologicalColorCrystalFormal
import proofs.HillWheelerUniversalProjection

/-!
# Affine reflection identities on a spectral coordinate plane

This file proves elementary identities for two maps on `ℝ × ℝ`: translation
in the second coordinate and reflection `σ ↦ 1 - σ` in the first. The
reflection is involutive, fixes exactly `σ = 1/2`, and conjugates first-axis
translations to their inverses.

The second coordinate is an ordinary real coordinate here. A parameterized
translation theorem does not impose a periodic equivalence relation, construct
a quotient manifold, or prove that the resulting space is a Klein bottle. The
reflection is a chosen affine symmetry; these identities alone do not identify
it with physical CPT, a zeta functional equation, or a theorem about critical
zeros. The historical declaration names below are retained for source
compatibility, while their proved content is precisely the affine algebra
stated above.
-/

noncomputable section

namespace SpectralCPTKleinBottle

open HillWheelerUniversalProjection

/-- A pair of real coordinates, used for the scale coordinate and an
unquotiented auxiliary coordinate. -/
abbrev SpectralCylinder := ℝ × ℝ

/-- Translation of the second real coordinate. Periodicity is not part of this
definition. -/
def thermalTranslate (T : ℝ) (s : SpectralCylinder) : SpectralCylinder :=
  (s.1, s.2 + T)

/-- Scale translation along the cylinder axis. -/
def scaleTranslate (a : ℝ) (s : SpectralCylinder) : SpectralCylinder :=
  (s.1 + a, s.2)

/-- The affine reflection of the first coordinate about `σ = 1/2`. -/
def cptGlide (s : SpectralCylinder) : SpectralCylinder :=
  (1 - s.1, s.2)

/-- Critical Möbius/Klein core line. -/
def criticalCore (s : SpectralCylinder) : Prop :=
  s.1 = 1 / 2

/-- Thermal translations form the cylinder direction additively. -/
theorem thermalTranslate_add (T U : ℝ) (s : SpectralCylinder) :
    thermalTranslate T (thermalTranslate U s) = thermalTranslate (U + T) s := by
  ext <;> simp [thermalTranslate, add_comm, add_left_comm]

/-- The affine reflection is an involution. -/
theorem cptGlide_involutive (s : SpectralCylinder) :
    cptGlide (cptGlide s) = s := by
  ext <;> simp [cptGlide]

/-- The first-coordinate reflection commutes with translations of the second
coordinate. -/
theorem cptGlide_thermal_commute (T : ℝ) (s : SpectralCylinder) :
    cptGlide (thermalTranslate T s) = thermalTranslate T (cptGlide s) := by
  ext <;> simp [cptGlide, thermalTranslate]

/-- The fixed locus of the affine reflection is exactly `σ = 1/2`. -/
theorem cptGlide_fixed_iff_criticalCore (s : SpectralCylinder) :
    cptGlide s = s ↔ criticalCore s := by
  constructor
  · intro h
    have hs : 1 - s.1 = s.1 := by simpa [cptGlide] using congrArg Prod.fst h
    unfold criticalCore
    linarith
  · intro h
    ext <;> simp [cptGlide, criticalCore] at h ⊢
    linarith

/-- Conjugating a first-coordinate translation by this involution reverses its
parameter. This is an identity of affine maps, without a quotient-topology
interpretation. -/
theorem cptGlide_reverses_scale_translation (a : ℝ) (s : SpectralCylinder) :
    cptGlide (scaleTranslate a (cptGlide s)) = scaleTranslate (-a) s := by
  ext <;> simp [cptGlide, scaleTranslate]
  ring

/-- The fixed coordinate line is preserved by the affine reflection. -/
theorem cptGlide_preserves_criticalCore {s : SpectralCylinder}
    (h : criticalCore s) : criticalCore (cptGlide s) := by
  unfold criticalCore at h ⊢
  simp [cptGlide]
  linarith

/-- A compatibility conjunction packaging these affine reflection identities
with the separately defined finite readouts imported above. It does not
identify those independent readouts as a geometric Klein bottle or a physical
CPT theorem. -/
theorem spectral_cpt_klein_bottle_synthesis
    (T a : ℝ) (x : SpectralCylinder) (s : ℂ) :
    cptGlide (cptGlide x) = x ∧
    cptGlide (thermalTranslate T x) = thermalTranslate T (cptGlide x) ∧
    (cptGlide x = x ↔ criticalCore x) ∧
    cptGlide (scaleTranslate a (cptGlide x)) = scaleTranslate (-a) x ∧
    (cptHillWheelerAverage s).re = 1 / 2 ∧
    MobiusCantorTKKClosure.mobiusJ (MobiusCantorTKKClosure.mobiusGamma s) =
      MobiusCantorTKKClosure.mobiusGamma (MobiusCantorTKKClosure.mobiusJ s) ∧
    Clifford55AnomalyOSP.anomalyIndex 5 5 = 0 := by
  constructor
  · exact cptGlide_involutive x
  constructor
  · exact cptGlide_thermal_commute T x
  constructor
  · exact cptGlide_fixed_iff_criticalCore x
  constructor
  · exact cptGlide_reverses_scale_translation a x
  constructor
  · exact cptHillWheelerAverage_re s
  constructor
  · exact MobiusCantorTKKClosure.mobiusJ_gamma_commute s
  · exact MobiusCantorTKKClosure.tkk_pin55_anomaly_zero

end SpectralCPTKleinBottle

end noncomputable section
