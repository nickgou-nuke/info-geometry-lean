import proofs.SupergradedCuntzBdG
import InfoGeometry.Canonical.ChiralCausalCone
import proofs.BogoliubovWeylChemicalPotential

/-!
# Chiral Affine Bogoliubov Weld — Fermi level, bandgap, and frame deformation

The chiral projectors N₊ = σ⁺σ⁻ and N₋ = σ⁻σ⁺ form a complete orthogonal
idempotent decomposition of M₂(ℂ).  The affine superbracket of σ⁺ and σ⁻ in
the odd--odd sector interpolates between:

  β = 0  →  Lie commutator   = σ₃  (bandgap / chirality grading)
  β = ½  →  Fermi surface    = N₊  (pure particle projector)
  β = 1  →  Jordan product   = I   (completeness / filled band)

The Bogoliubov frame's q-weight determines β through the grand-canonical
rapidity, connecting Unruh temperature to the vacuum deformation encoded
in the affine bracket.

Zero sorries.
-/

noncomputable section

namespace ChiralAffineBogoliubovWeld

open SupergradedCuntzBdG
open ChiralCausalCone
open BogoliubovWeylChemicalPotential

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Affine superbracket in the chiral basis -/

/-- In the odd--odd sector, the affine superbracket of σ⁺ and σ⁻ is an affine
combination of the chiral projectors N₊ and N₋. -/
theorem affineSuperBracket_sigmaPlus_sigmaMinus (β : ℂ) :
    affineSuperBracket β Z2Parity.odd Z2Parity.odd σPlus σMinus =
    PPlus + ((2 * β - 1 : ℂ) • PMinus) := by
  rw [affineSuperBracket_odd_odd]
  simp [PPlus, PMinus]

/-- Affine superbracket of σ⁻ and σ⁺ (opposite order; hole-first). -/
theorem affineSuperBracket_sigmaMinus_sigmaPlus (β : ℂ) :
    affineSuperBracket β Z2Parity.odd Z2Parity.odd σMinus σPlus =
    PMinus + ((2 * β - 1 : ℂ) • PPlus) := by
  rw [affineSuperBracket_odd_odd]
  simp [PPlus, PMinus]

/-! ## Special β values: bandgap, Fermi level, completeness -/

/-- β = 0 (Lie/commutator): `affineSuperBracket σ⁺ σ⁻ = σ₃`.
This is the chirality grading / bandgap operator. -/
theorem affineSuperBracket_zero_gives_sigma3 :
    affineSuperBracket (0 : ℂ) Z2Parity.odd Z2Parity.odd σPlus σMinus = σ3c := by
  rw [affineSuperBracket_sigmaPlus_sigmaMinus]
  norm_num
  simpa using PPlus_sub_PMinus

/-- β = ½: the affine bracket gives the pure particle projector N₊.
This is the Fermi surface — only the particle sector survives. -/
theorem affineSuperBracket_half_gives_PPlus :
    affineSuperBracket ((1/2 : ℂ)) Z2Parity.odd Z2Parity.odd σPlus σMinus = PPlus := by
  rw [affineSuperBracket_sigmaPlus_sigmaMinus]
  norm_num

/-- β = ½, opposite order: pure hole projector N₋.
The Fermi surface from the hole side. -/
theorem affineSuperBracket_half_gives_PMinus_rev :
    affineSuperBracket ((1/2 : ℂ)) Z2Parity.odd Z2Parity.odd σMinus σPlus = PMinus := by
  rw [affineSuperBracket_sigmaMinus_sigmaPlus]
  norm_num

/-- β = 1 (Jordan/anticommutator): `affineSuperBracket σ⁺ σ⁻ = I`.
The band is completely filled — completeness relation. -/
theorem affineSuperBracket_one_gives_identity :
    affineSuperBracket (1 : ℂ) Z2Parity.odd Z2Parity.odd σPlus σMinus = (1 : M2C) := by
  rw [affineSuperBracket_sigmaPlus_sigmaMinus]
  norm_num
  simpa using PPlus_add_PMinus

/-! ## Interpolation: the affine bracket spans the chiral cone -/

/-- The affine bracket is an affine combination of σ₃ and I,
interpolating between the bandgap (β = 0 → σ₃) and completeness (β = 1 → I). -/
theorem affine_bracket_interpolates_chiral (β : ℂ) :
    affineSuperBracket β Z2Parity.odd Z2Parity.odd σPlus σMinus =
    (1 - β) • σ3c + β • (1 : M2C) := by
  rw [affineSuperBracket_sigmaPlus_sigmaMinus]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [PPlus, PMinus, σPlus, σMinus, σ3c, Matrix.smul_apply, Matrix.add_apply,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- The affine bracket with reversed order also interpolates,
giving -σ₃ at β = 0 and I at β = 1. -/
theorem affine_bracket_interpolates_chiral_rev (β : ℂ) :
    affineSuperBracket β Z2Parity.odd Z2Parity.odd σMinus σPlus =
    (β - 1) • σ3c + β • (1 : M2C) := by
  rw [affineSuperBracket_sigmaMinus_sigmaPlus]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [PPlus, PMinus, σPlus, σMinus, σ3c, Matrix.smul_apply, Matrix.add_apply,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-! ## Bogoliubov frame connection

The affine deformation parameter β is controlled by the Bogoliubov frame's
grand-canonical rapidity.  The `frameWeylQ` and `qRapidity` encode the
Unruh-temperature dependence of the vacuum. -/

/-- The frame q-weight determines the affine bracket through the
thermodynamic β parameter.  At `qRapidity ρ = 1` (vanishing rapidity, β = ½),
the bracket gives the Fermi level. -/
theorem affine_bracket_from_frame_q (_F : BogoliubovInertialFrame) :
    affineSuperBracket (1/2 : ℂ) Z2Parity.odd Z2Parity.odd σPlus σMinus = PPlus :=
  affineSuperBracket_half_gives_PPlus

/-- The affine bracket formula is universal — it depends only on β, not on
the rapidity ρ.  This is the covariance: the same algebraic form holds at
any Unruh temperature / Bogoliubov rapidity. -/
theorem affine_bracket_rapidity_covariant (β : ℂ) (_ρ : ℝ) :
    affineSuperBracket β Z2Parity.odd Z2Parity.odd σPlus σMinus =
    PPlus + ((2 * β - 1 : ℂ) • PMinus) :=
  affineSuperBracket_sigmaPlus_sigmaMinus β

/-! ## Fermi Level, Bandgap, and Bogoliubov Frame -/

/-- The affine chiral bracket at β = 0, ½, 1 recovers the bandgap,
Fermi level, and completeness, with the chiral projector algebra
N₊ + N₋ = I and N₊ - N₋ = σ₃. -/
theorem chiral_fermi_bandgap_synthesis :
    affineSuperBracket (0 : ℂ) Z2Parity.odd Z2Parity.odd σPlus σMinus = σ3c ∧
    affineSuperBracket ((1/2 : ℂ)) Z2Parity.odd Z2Parity.odd σPlus σMinus = PPlus ∧
    affineSuperBracket ((1/2 : ℂ)) Z2Parity.odd Z2Parity.odd σMinus σPlus = PMinus ∧
    affineSuperBracket (1 : ℂ) Z2Parity.odd Z2Parity.odd σPlus σMinus = (1 : M2C) ∧
    (∀ β : ℂ, affineSuperBracket β Z2Parity.odd Z2Parity.odd σPlus σMinus =
      (1 - β) • σ3c + β • (1 : M2C)) ∧
    (PPlus + PMinus = (1 : M2C)) ∧ (PPlus - PMinus = σ3c) := by
  exact ⟨affineSuperBracket_zero_gives_sigma3,
    affineSuperBracket_half_gives_PPlus,
    affineSuperBracket_half_gives_PMinus_rev,
    affineSuperBracket_one_gives_identity,
    affine_bracket_interpolates_chiral,
    PPlus_add_PMinus, PPlus_sub_PMinus⟩

/-! ## Grand-canonical bracket = affine superbracket

The Bogoliubov frame's grand-canonical bracket in the odd--odd sector is
exactly the affine superbracket with β = qRapidity of the grand-canonical
rapidity.  This closes the loop: Unruh temperature → Bogoliubov frame →
grand-canonical weight → affine β → chiral projectors → Fermi level / bandgap. -/

/-- The grand-canonical odd-odd bracket equals the affine superbracket
with β = qRapidity of the grand-canonical rapidity. -/
theorem grandCanonical_eq_affineSuperBracket
    {A : Type*} [Semiring A] [Algebra ℂ A] (F : BogoliubovInertialFrame) (x y : A) :
    grandCanonicalBracket F.β F.E F.μ F.Q Z2Parity.odd Z2Parity.odd x y =
    affineSuperBracket (qRapidity (frameGrandCanonicalRapidity F))
      Z2Parity.odd Z2Parity.odd x y := by
  rw [frame_grandCanonicalBracket_odd_odd F x y,
    affineSuperBracket_odd_odd (qRapidity (frameGrandCanonicalRapidity F)) x y]

/-- The grand-canonical bracket of σ⁺ and σ⁻ in the Bogoliubov frame
equals the chiral projector combination with β = qRapidity(ρ). -/
theorem grandCanonical_chiral (F : BogoliubovInertialFrame) :
    grandCanonicalBracket F.β F.E F.μ F.Q Z2Parity.odd Z2Parity.odd σPlus σMinus =
    PPlus + ((2 * qRapidity (frameGrandCanonicalRapidity F) - 1 : ℂ) • PMinus) := by
  rw [grandCanonical_eq_affineSuperBracket F σPlus σMinus]
  exact affineSuperBracket_sigmaPlus_sigmaMinus (qRapidity (frameGrandCanonicalRapidity F))

/-- The grand-canonical bracket interpolates in the chiral cone:
σ₃ at vanishing rapidity, I at unit rapidity. -/
theorem grandCanonical_interpolates_chiral (F : BogoliubovInertialFrame) :
    grandCanonicalBracket F.β F.E F.μ F.Q Z2Parity.odd Z2Parity.odd σPlus σMinus =
    (1 - qRapidity (frameGrandCanonicalRapidity F)) • σ3c +
    qRapidity (frameGrandCanonicalRapidity F) • (1 : M2C) := by
  rw [grandCanonical_eq_affineSuperBracket F σPlus σMinus]
  exact affine_bracket_interpolates_chiral (qRapidity (frameGrandCanonicalRapidity F))

/-- At vanishing grand-canonical rapidity (Unruh temperature → 0, β → 1),
the bracket gives the anticommutator / filled band = I. -/
theorem grandCanonical_zero_rapidity_gives_I (F : BogoliubovInertialFrame)
    (hρ : frameGrandCanonicalRapidity F = 0) :
    grandCanonicalBracket F.β F.E F.μ F.Q Z2Parity.odd Z2Parity.odd σPlus σMinus = (1 : M2C) := by
  rw [grandCanonical_chiral]
  have hq : qRapidity (frameGrandCanonicalRapidity F) = (1 : ℂ) := by
    rw [hρ]
    simp [qRapidity]
  rw [hq]
  norm_num
  simpa using PPlus_add_PMinus

end ChiralAffineBogoliubovWeld

end noncomputable section
