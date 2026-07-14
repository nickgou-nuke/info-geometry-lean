import InfoGeometry.Clifford.STAOperators
import InfoGeometry.Physics.Section28EinsteinTorsionSpinor
import InfoGeometry.Physics.Section34StrengthenedFormalism

/-!
# Universe 2024, 10, 333: finite spin-torsion scale ledger

The PDF `/home/goutev/Downloads/drazin/universe-10-00333.pdf` is
Chen--Wang, *Quantum Effects on Cosmic Scales as an Alternative to Dark Matter
and Dark Energy*, Universe 2024, 10, 333.

This module extracts only theorem-safe finite algebraic bookkeeping from the
paper's spin-torsion/Dirac-Hestenes discussion:

* mass density divided by a scale-dependent mass gives a number-density readout;
* spin density is the finite scalar multiple `(hbar/2) * numberDensity`;
* scaling the mass by a positive factor rescales number density by the inverse
  factor;
* a quantum-potential-energy term is represented only as an additive mass ledger;
* existing finite owners supply the Dirac/STA square laws and symmetric
  spinor/torsion stress shadows.

It records no observational-fit theorem, large-scale dynamics theorem, smooth
spinor PDE theorem, or full geometric field-system theorem.
-/

noncomputable section

namespace Universe1000333SpinTorsionScale

open InfoGeometry.Physics.Section28EinsteinTorsionSpinor

/-- Number-density readout `ρ = ρ_m / m(λ)`. -/
def numberDensity (massDensity scaleMass : ℝ) : ℝ :=
  massDensity / scaleMass

/-- Spin-density magnitude readout `|S| = (ℏ/2) ρ`. -/
def spinDensityMagnitude (hbar massDensity scaleMass : ℝ) : ℝ :=
  (hbar / 2) * numberDensity massDensity scaleMass

/-- Additive mass ledger with a quantum-potential-energy term. -/
def effectiveMassLedger (restMass qpe : ℝ) : ℝ :=
  restMass + qpe

/-- Residual for a static scalar balance between ordinary and quantum-potential terms. -/
def scalarBalanceResidual (ordinary qpe : ℝ) : ℝ :=
  ordinary + qpe

/-- The spin-density definition is exactly `(ℏ/2) * (ρ_m / m(λ))`. -/
theorem spinDensityMagnitude_eq (hbar massDensity scaleMass : ℝ) :
    spinDensityMagnitude hbar massDensity scaleMass =
      (hbar / 2) * (massDensity / scaleMass) := by
  rfl

/-- Scaling the mass by a nonzero factor rescales number density by the inverse factor. -/
theorem numberDensity_scaled_mass
    (massDensity scaleMass scaleFactor : ℝ) (hscale : scaleFactor ≠ 0) :
    numberDensity massDensity (scaleMass * scaleFactor) =
      numberDensity massDensity scaleMass / scaleFactor := by
  unfold numberDensity
  field_simp [hscale]

/-- Spin-density bookkeeping obeys the same inverse scale law. -/
theorem spinDensity_scaled_mass
    (hbar massDensity scaleMass scaleFactor : ℝ) (hscale : scaleFactor ≠ 0) :
    spinDensityMagnitude hbar massDensity (scaleMass * scaleFactor) =
      spinDensityMagnitude hbar massDensity scaleMass / scaleFactor := by
  unfold spinDensityMagnitude
  rw [numberDensity_scaled_mass massDensity scaleMass scaleFactor hscale]
  ring

/-- The additive effective mass ledger exposes the QPE contribution as a difference. -/
theorem effectiveMassLedger_sub_restMass (restMass qpe : ℝ) :
    effectiveMassLedger restMass qpe - restMass = qpe := by
  unfold effectiveMassLedger
  ring

/-- A scalar balance residual vanishes when the QPE term is the negative ordinary term. -/
theorem scalarBalanceResidual_eq_zero_of_qpe_neg (ordinary : ℝ) :
    scalarBalanceResidual ordinary (-ordinary) = 0 := by
  unfold scalarBalanceResidual
  ring

/-- Existing STA owner: the Hestenes spin-plane phase squares to `-1`. -/
theorem sta_spin_plane_square_neg :
    InfoGeometry.Clifford.STAOperators.staPhaseBivector *
        InfoGeometry.Clifford.STAOperators.staPhaseBivector = -1 :=
  InfoGeometry.Clifford.STAOperators.staPhaseBivector_mul_self

/-- Existing finite torsion owner: torsion stress is symmetric under symmetric inputs. -/
theorem torsionStress_symmetric_readout
    {g B : Tensor2} {torsionNorm alpha2 : ℝ}
    (hg : Symmetric2 g) (hB : Symmetric2 B) :
    Symmetric2 (torsionStressShadow g B torsionNorm alpha2) :=
  torsionStressShadow_symmetric hg hB

/-- Existing finite spinor owner: spinor stress is symmetric under a symmetric metric. -/
theorem spinorStress_symmetric_readout
    {g A : Tensor2} {trA : ℝ} (hg : Symmetric2 g) :
    Symmetric2 (spinorStressShadow g A trA) :=
  spinorStressShadow_symmetric hg

/-- Consolidated finite algebraic packet for the Universe 10:333 scale ledger. -/
theorem universe1000333_finite_scale_packet
    (hbar massDensity scaleMass scaleFactor restMass qpe ordinary : ℝ)
    (hscale : scaleFactor ≠ 0) :
    spinDensityMagnitude hbar massDensity scaleMass =
        (hbar / 2) * (massDensity / scaleMass) ∧
      numberDensity massDensity (scaleMass * scaleFactor) =
        numberDensity massDensity scaleMass / scaleFactor ∧
      spinDensityMagnitude hbar massDensity (scaleMass * scaleFactor) =
        spinDensityMagnitude hbar massDensity scaleMass / scaleFactor ∧
      effectiveMassLedger restMass qpe - restMass = qpe ∧
      scalarBalanceResidual ordinary (-ordinary) = 0 ∧
      InfoGeometry.Clifford.STAOperators.staPhaseBivector *
          InfoGeometry.Clifford.STAOperators.staPhaseBivector = -1 := by
  exact ⟨spinDensityMagnitude_eq hbar massDensity scaleMass,
    numberDensity_scaled_mass massDensity scaleMass scaleFactor hscale,
    spinDensity_scaled_mass hbar massDensity scaleMass scaleFactor hscale,
    effectiveMassLedger_sub_restMass restMass qpe,
    scalarBalanceResidual_eq_zero_of_qpe_neg ordinary,
    sta_spin_plane_square_neg⟩

end Universe1000333SpinTorsionScale

end noncomputable section
