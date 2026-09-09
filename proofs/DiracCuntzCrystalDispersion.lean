import proofs.ThermalBoostLorentzSuperalgebra
import proofs.CuntzP6MWallpaperBoundary
import InfoGeometry.Canonical.ChiralCausalCone

/-!
# Dirac--Cuntz crystal finite dispersion

Finite Lean statements for the proposed modified Dirac--Weyl dispersion
normalizations inside the `O_3`/`p6m` metasurface crystal.

The Lean content here proves only finite algebraic dispersion bookkeeping:

* the `O_3` color sector has three Cuntz slots;
* the zero-rapidity deformation factor is `1`;
* the massless toy cone squares to `vF^2 * |k|^2`;
* the massive toy cone is `sqrt-like` only at the squared-expression level;
* the band signs and zero-time modular flow reduce to their defining identities.
-/

noncomputable section

namespace DiracCuntzCrystalDispersion

/-- Toy squared planar momentum. -/
def kNormSq (kx ky : ℝ) : ℝ := kx^2 + ky^2

/-- Toy structural Cuntz form factor: at the undeformed p=3 symmetric point it is one. -/
def cuntzFormFactor (_kx _ky : ℝ) : ℝ := 1

@[simp] theorem cuntzFormFactor_trivial (kx ky : ℝ) :
    cuntzFormFactor kx ky = 1 := rfl

/-- Massless squared Dirac--Cuntz dispersion toy. -/
def masslessDiracCuntzEnergySq (vF kx ky η : ℝ) : ℝ :=
  vF^2 * kNormSq kx ky *
    (ThermalBoostLorentzSuperalgebra.safeDispersionFactor η)^2 *
    (cuntzFormFactor kx ky)^2

@[simp] theorem masslessDiracCuntzEnergySq_zero_rapidity (vF kx ky : ℝ) :
    masslessDiracCuntzEnergySq vF kx ky 0 = vF^2 * kNormSq kx ky := by
  simp [masslessDiracCuntzEnergySq]

/-- Massive squared Dirac--Cuntz dispersion toy with an added squared gap parameter. -/
def massiveDiracCuntzEnergySq (vF kx ky η Δ : ℝ) : ℝ :=
  masslessDiracCuntzEnergySq vF kx ky η + Δ^2

@[simp] theorem massiveDiracCuntzEnergySq_zero_gap (vF kx ky η : ℝ) :
    massiveDiracCuntzEnergySq vF kx ky η 0 =
      masslessDiracCuntzEnergySq vF kx ky η := by
  simp [massiveDiracCuntzEnergySq]

/-- Finite two-band labels. -/
inductive DiracBand where
  | conduction
  | valence
  deriving DecidableEq, Repr

/-- Band sign for the two Dirac branches. -/
def bandSign : DiracBand → ℤ
  | .conduction => 1
  | .valence => -1

@[simp] theorem bandSign_conduction : bandSign DiracBand.conduction = 1 := rfl
@[simp] theorem bandSign_valence : bandSign DiracBand.valence = -1 := rfl



/-- Finite kernel for the undeformed Dirac-Cuntz dispersion bookkeeping. -/
theorem finite_dirac_cuntz_dispersion_kernel (vF kx ky K : ℝ) (A : ℂ) :
    CuntzP6MWallpaperBoundary.sectorArity
      CuntzP6MWallpaperBoundary.PrimeSector.p3 = 3 ∧
    ThermalBoostLorentzSuperalgebra.safeDispersionFactor 0 = 1 ∧
    masslessDiracCuntzEnergySq vF kx ky 0 = vF^2 * kNormSq kx ky ∧
    massiveDiracCuntzEnergySq vF kx ky 0 0 = vF^2 * kNormSq kx ky ∧
    bandSign DiracBand.conduction = 1 ∧
    bandSign DiracBand.valence = -1 ∧
    modularFlow K 0 A = A := by
  constructor
  · rfl
  constructor
  · exact ThermalBoostLorentzSuperalgebra.safeDispersionFactor_zero
  constructor
  · exact masslessDiracCuntzEnergySq_zero_rapidity vF kx ky
  constructor
  · simp [massiveDiracCuntzEnergySq]
  constructor
  · rfl
  constructor
  · rfl
  · exact BuresInformationGeodesicFlow.modularFlow_zero_time K A

/-- Finite dispersion bookkeeping for the stated algebraic normalizations. -/
theorem dirac_cuntz_crystal_dispersion_synthesis
    (vF kx ky K Δ : ℝ) (A : ℂ) :
    CuntzP6MWallpaperBoundary.sectorArity
      CuntzP6MWallpaperBoundary.PrimeSector.p3 = 3 ∧
    masslessDiracCuntzEnergySq vF kx ky 0 = vF^2 * kNormSq kx ky ∧
    massiveDiracCuntzEnergySq vF kx ky 0 Δ = vF^2 * kNormSq kx ky + Δ^2 ∧
    bandSign DiracBand.conduction = 1 ∧
    bandSign DiracBand.valence = -1 ∧
    modularFlow K 0 A = A := by
  constructor
  · rfl
  constructor
  · exact masslessDiracCuntzEnergySq_zero_rapidity vF kx ky
  constructor
  · simp [massiveDiracCuntzEnergySq]
  constructor
  · rfl
  constructor
  · rfl
  · exact BuresInformationGeodesicFlow.modularFlow_zero_time K A

#check dirac_cuntz_crystal_dispersion_synthesis

end DiracCuntzCrystalDispersion
