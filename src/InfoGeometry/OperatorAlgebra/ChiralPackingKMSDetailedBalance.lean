import InfoGeometry.OperatorAlgebra.ChiralPackingEnergy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Thermo.CantorGibbsModularBridge

/-!
# Chiral packing energies and the finite Gibbs/modular bridge

This owner connects the existing sign-valued packing Hamiltonian to the
already verified one-site Gibbs and CAR modular packet.  The packing owner
continues to own exchange/curvature energy statements; this file only adds
the finite thermal readout.

The real matrix modular shift uses the convention of `FiniteDiagonal`.  Its
time parameter is therefore recorded explicitly below: the Gibbs population
ratio and the real conjugation flow are inverse conventions on the
annihilation corner.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralPackingKMSDetailedBalance

open InfoGeometry.OperatorAlgebra.ChiralPackingEnergy
open InfoGeometry.Thermo.CantorGibbsModularBridge
open InfoGeometry.OperatorAlgebra.CrossoverResidue
open InfoGeometry.Canonical.SplitCliffordCantorFock

/-- The local curvature bias appearing in the two-sheet atom. -/
def curvatureBias {Site : Type*}
    (H : ChiralPackingHamiltonian Site) (i : Site) : ℝ :=
  H.curvatureCoupling * H.curvature i

/-- Symmetric two-sheet energies `E_χ = g χ`. -/
def sheetEnergy (g : ℝ) (χ : Chirality) : ℝ :=
  g * chiralityRealSign χ

theorem sheetEnergy_left (g : ℝ) : sheetEnergy g Chirality.left = g := by
  simp [sheetEnergy]

theorem sheetEnergy_right (g : ℝ) : sheetEnergy g Chirality.right = -g := by
  simp [sheetEnergy]

theorem sheetEnergy_flip (g : ℝ) (χ : Chirality) :
    sheetEnergy g (Chirality.flip χ) = -sheetEnergy g χ := by
  cases χ <;> simp [sheetEnergy, Chirality.flip]

theorem sheetEnergy_gap (g : ℝ) :
    sheetEnergy g Chirality.left - sheetEnergy g Chirality.right = 2 * g := by
  simp [sheetEnergy]
  ring

/-- Gibbs weights for the symmetric two-sheet atom, implemented by the
one-site finite Gibbs owner with energy gap `-2g`. -/
noncomputable def sheetWeightPlus (β g : ℝ) : ℝ :=
  localWeightPlus β (-2 * g)

noncomputable def sheetWeightMinus (β g : ℝ) : ℝ :=
  localWeightMinus β (-2 * g)

theorem sheetWeights_sum_one (β g : ℝ) :
    sheetWeightPlus β g + sheetWeightMinus β g = 1 := by
  exact localWeights_sum_one β (-2 * g)

theorem sheetWeight_ratio (β g : ℝ) :
    sheetWeightPlus β g = Real.exp (-2 * β * g) * sheetWeightMinus β g := by
  rw [sheetWeightPlus, sheetWeightMinus, localWeightPlus_eq, localWeightMinus_eq]
  have hexp : Real.exp (-β * (-2 * g)) = Real.exp (2 * β * g) := by
    congr 1
    ring
  rw [hexp]
  have hne : 1 + Real.exp (2 * β * g) ≠ 0 := by
    positivity
  field_simp [hne, Real.exp_ne_zero]
  simpa [← Real.exp_add] using (Real.exp_zero : Real.exp (0 : ℝ) = 1)

theorem sheetWeight_inverse_ratio (β g : ℝ) :
    sheetWeightMinus β g / sheetWeightPlus β g = Real.exp (2 * β * g) := by
  have hp : sheetWeightPlus β g ≠ 0 :=
    ne_of_gt (localWeightPlus_pos β (-2 * g))
  have hm : sheetWeightMinus β g ≠ 0 :=
    ne_of_gt (localWeightMinus_pos β (-2 * g))
  rw [sheetWeight_ratio β g]
  field_simp [hp, hm, Real.exp_ne_zero]
  simpa [← Real.exp_add] using (Real.exp_zero : Real.exp (0 : ℝ) = 1)

theorem sheetWeight_beta_zero (g : ℝ) :
    sheetWeightPlus 0 g = 1 / 2 ∧ sheetWeightMinus 0 g = 1 / 2 := by
  exact ⟨localWeightPlus_beta_zero (-2 * g),
    localWeightMinus_beta_zero (-2 * g)⟩

theorem curvature_bias_energy_left_right {Site : Type*}
    (H : ChiralPackingHamiltonian Site) (i : Site) :
    sheetEnergy (curvatureBias H i) Chirality.left = curvatureBias H i ∧
      sheetEnergy (curvatureBias H i) Chirality.right = -curvatureBias H i := by
  exact ⟨sheetEnergy_left _, sheetEnergy_right _⟩

theorem chiral_modular_annihilation_eigenmode (β g : ℝ) :
    localModularShift (-2 * g) (-β) a_op =
      Real.exp (-2 * β * g) • a_op := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (localModularShift_annihilation_eigenmode (-2 * g) (-β))

theorem chiral_modular_creation_eigenmode (β g : ℝ) :
    localModularShift (-2 * g) (-β) aDag_op =
      Real.exp (2 * β * g) • aDag_op := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (localModularShift_creation_eigenmode (-2 * g) (-β))

theorem chiral_modular_frequency_pair (β g : ℝ) :
    (Real.exp (-2 * β * g), Real.exp (2 * β * g)) =
      (sheetWeightPlus β g / sheetWeightMinus β g,
        sheetWeightMinus β g / sheetWeightPlus β g) := by
  have hp := localWeightPlus_pos β (-2 * g)
  have hm := localWeightMinus_pos β (-2 * g)
  apply Prod.ext
  · rw [sheetWeightPlus, sheetWeightMinus, localWeightPlus_eq,
      localWeightMinus_eq]
    have hne : 1 + Real.exp (2 * β * g) ≠ 0 := by positivity
    field_simp [hne, Real.exp_ne_zero]
    rw [← Real.exp_add]
    ring_nf
    simp
  · rw [sheetWeightPlus, sheetWeightMinus, localWeightPlus_eq,
      localWeightMinus_eq]
    have hne : 1 + Real.exp (2 * β * g) ≠ 0 := by positivity
    field_simp [hne, Real.exp_ne_zero]

/-! The conversion rates below use the population of the target sheet. -/

noncomputable def cayleyPlusToMinusRate (β g κ : ℝ) : ℝ :=
  κ * sheetWeightMinus β g

noncomputable def cayleyMinusToPlusRate (β g κ : ℝ) : ℝ :=
  κ * sheetWeightPlus β g

theorem cayley_conversion_detailed_balance (β g κ : ℝ) (hκ : κ ≠ 0) :
    cayleyPlusToMinusRate β g κ /
        cayleyMinusToPlusRate β g κ = Real.exp (2 * β * g) := by
  unfold cayleyPlusToMinusRate cayleyMinusToPlusRate
  have hp : sheetWeightPlus β g ≠ 0 :=
    ne_of_gt (localWeightPlus_pos β (-2 * g))
  have hm : sheetWeightMinus β g ≠ 0 :=
    ne_of_gt (localWeightMinus_pos β (-2 * g))
  rw [div_eq_iff (mul_ne_zero hκ hp)]
  rw [sheetWeight_ratio β g]
  have hexp : Real.exp (2 * β * g) * Real.exp (-2 * β * g) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    κ * sheetWeightMinus β g =
        (Real.exp (2 * β * g) * Real.exp (-2 * β * g)) *
          (κ * sheetWeightMinus β g) := by rw [hexp]; ring
    _ = Real.exp (2 * β * g) *
          (κ * (Real.exp (-2 * β * g) * sheetWeightMinus β g)) := by ring

end InfoGeometry.OperatorAlgebra.ChiralPackingKMSDetailedBalance
