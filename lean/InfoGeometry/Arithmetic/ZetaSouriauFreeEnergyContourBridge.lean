import InfoGeometry.Arithmetic.ZetaSouriauEntropyMetriplecticBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.ZetaSouriauSymmetryThermodynamics
import InfoGeometry.Arithmetic.ZetaSouriauHorizontalFlow

/-!
# Finite Souriau free-energy contours on the centered zeta chart

This owner isolates the theorem-safe contour layer from the zeta-flow
specification.  A real Massieu readout is supplied on the finite chart and
free energy is its negative.  Invariance of the supplied readout transports
its level sets through the native semidirect `MulAction`.

No analytic `log ζ` branch, complex free-energy formula, or infinite
thermodynamic limit is asserted here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaSouriauFreeEnergyContourBridge

open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart
open InfoGeometry.Arithmetic.ZetaSouriauSymmetryThermodynamics

abbrev Chart := ZetaCenteredChart

/-! ## Finite Massieu/free-energy readouts -/

/-- A supplied real Massieu potential on the centered chart. -/
def massieuReadout (Φ : Chart → ℝ) (x : Chart) : ℝ := Φ x

/-- Finite free energy is the negative Massieu readout. -/
def freeEnergyReadout (Φ : Chart → ℝ) (x : Chart) : ℝ := -massieuReadout Φ x

/-- The free-energy contour at level `r`. -/
def freeEnergyLevelSet (Φ : Chart → ℝ) (r : ℝ) : Set Chart :=
  {x | freeEnergyReadout Φ x = r}

theorem mem_freeEnergyLevelSet_iff (Φ : Chart → ℝ) (r : ℝ) (x : Chart) :
    x ∈ freeEnergyLevelSet Φ r ↔ freeEnergyReadout Φ x = r := Iff.rfl

/-! ## Symmetry transport -/

/-- An invariant Massieu readout is also an invariant free-energy readout. -/
theorem freeEnergyReadout_eq_of_invariant
    {Φ : Chart → ℝ}
    (hΦ : ZetaSouriauLieSymmetry.PotentialInvariant Φ)
    (A : ZetaSouriauLieSymmetry) (x : Chart) :
    freeEnergyReadout Φ (A.act x) = freeEnergyReadout Φ x := by
  change -Φ (A.act x) = -Φ x
  rw [hΦ A x]

/-- Semidirect chart symmetries preserve free-energy contours. -/
theorem freeEnergyLevelSet_mem_iff_of_invariant
    {Φ : Chart → ℝ}
    (hΦ : ZetaSouriauLieSymmetry.PotentialInvariant Φ)
    (A : ZetaSouriauLieSymmetry) (r : ℝ) (x : Chart) :
    A.act x ∈ freeEnergyLevelSet Φ r ↔ x ∈ freeEnergyLevelSet Φ r := by
  change freeEnergyReadout Φ (A.act x) = r ↔ freeEnergyReadout Φ x = r
  rw [freeEnergyReadout_eq_of_invariant hΦ A x]

/-- The free-energy contour through a point is transported into itself. -/
theorem freeEnergyLevelSet_map_mem_of_invariant
    {Φ : Chart → ℝ}
    (hΦ : ZetaSouriauLieSymmetry.PotentialInvariant Φ)
    (A : ZetaSouriauLieSymmetry) (x : Chart) :
    A.act x ∈ freeEnergyLevelSet Φ (freeEnergyReadout Φ x) := by
  rw [freeEnergyLevelSet_mem_iff_of_invariant hΦ A (freeEnergyReadout Φ x) x]
  rfl

/-! ## Generic phase/isophase contours -/

/-- A supplied real phase readout on the centered chart. -/
def phaseReadout (Θ : Chart → ℝ) (x : Chart) : ℝ := Θ x

/-- The isophase contour at level `r`. -/
def phaseLevelSet (Θ : Chart → ℝ) (r : ℝ) : Set Chart :=
  {x | phaseReadout Θ x = r}

theorem mem_phaseLevelSet_iff (Θ : Chart → ℝ) (r : ℝ) (x : Chart) :
    x ∈ phaseLevelSet Θ r ↔ phaseReadout Θ x = r := Iff.rfl

theorem phaseLevelSet_mem_iff_of_invariant
    {Θ : Chart → ℝ}
    (hΘ : ZetaSouriauLieSymmetry.PotentialInvariant Θ)
    (A : ZetaSouriauLieSymmetry) (r : ℝ) (x : Chart) :
    A.act x ∈ phaseLevelSet Θ r ↔ x ∈ phaseLevelSet Θ r := by
  change Θ (A.act x) = r ↔ Θ x = r
  rw [hΘ A x]

/-! ## Canonical finite displacement-Massieu free energy -/

/-- Negative finite displacement Massieu potential. -/
def displacementFreeEnergy
    {State : Type*} [Fintype State]
    (moment : State → Chart) (beta : Chart) : ℝ :=
  -zetaSouriauDisplacementMassieu moment beta

theorem displacementFreeEnergy_invariant
    {State : Type*} [Fintype State]
    (A : ZetaSouriauLieSymmetry)
    (moment : State → Chart) (beta : Chart) :
    displacementFreeEnergy (fun x => A.act (moment x)) (A.act beta) =
      displacementFreeEnergy moment beta := by
  unfold displacementFreeEnergy
  rw [zetaSouriauDisplacementMassieu_invariant]

def displacementFreeEnergyLevelSet
    {State : Type*} [Fintype State]
    (moment : State → Chart) (r : ℝ) : Set Chart :=
  {beta | displacementFreeEnergy moment beta = r}

theorem mem_displacementFreeEnergyLevelSet_iff
    {State : Type*} [Fintype State]
    (moment : State → Chart) (r : ℝ) (beta : Chart) :
    beta ∈ displacementFreeEnergyLevelSet moment r ↔
      displacementFreeEnergy moment beta = r := Iff.rfl

theorem displacementFreeEnergyLevelSet_mem_iff
    {State : Type*} [Fintype State]
    (A : ZetaSouriauLieSymmetry)
    (moment : State → Chart) (r : ℝ) (beta : Chart) :
    A.act beta ∈ displacementFreeEnergyLevelSet
      (fun x => A.act (moment x)) r ↔
      beta ∈ displacementFreeEnergyLevelSet moment r := by
  change displacementFreeEnergy
      (fun x => A.act (moment x)) (A.act beta) = r ↔
    displacementFreeEnergy moment beta = r
  rw [displacementFreeEnergy_invariant]

theorem displacementFreeEnergyLevelSet_map_mem_of_invariant
    {State : Type*} [Fintype State]
    (A : ZetaSouriauLieSymmetry)
    (moment : State → Chart) (beta : Chart) :
    A.act beta ∈ displacementFreeEnergyLevelSet
      (fun x => A.act (moment x))
      (displacementFreeEnergy moment beta) := by
  rw [mem_displacementFreeEnergyLevelSet_iff]
  exact displacementFreeEnergy_invariant A moment beta

theorem zetaSouriauDisplacementPartition_pos
    {State : Type*} [Fintype State] [Nonempty State]
    (moment : State → Chart) (beta : Chart) :
    0 < zetaSouriauDisplacementPartition moment beta := by
  unfold zetaSouriauDisplacementPartition
  have hne : (Finset.univ : Finset State).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty State)
    exact ⟨x, Finset.mem_univ x⟩
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) hne

theorem zetaSouriauDisplacementPartition_ne_zero
    {State : Type*} [Fintype State] [Nonempty State]
    (moment : State → Chart) (beta : Chart) :
    zetaSouriauDisplacementPartition moment beta ≠ 0 :=
  ne_of_gt (zetaSouriauDisplacementPartition_pos moment beta)

theorem displacementFreeEnergy_master_packet
    {State : Type*} [Fintype State] [Nonempty State]
    (A : ZetaSouriauLieSymmetry)
    (moment : State → Chart) (beta : Chart) :
    (0 < zetaSouriauDisplacementPartition moment beta) ∧
    (zetaSouriauDisplacementPartition moment beta ≠ 0) ∧
    (displacementFreeEnergy (fun x => A.act (moment x)) (A.act beta) =
      displacementFreeEnergy moment beta) ∧
    (A.act beta ∈ displacementFreeEnergyLevelSet
      (fun x => A.act (moment x))
      (displacementFreeEnergy moment beta)) := by
  refine ⟨zetaSouriauDisplacementPartition_pos moment beta,
    zetaSouriauDisplacementPartition_ne_zero moment beta,
    displacementFreeEnergy_invariant A moment beta,
    displacementFreeEnergyLevelSet_map_mem_of_invariant A moment beta⟩

end InfoGeometry.Arithmetic.ZetaSouriauFreeEnergyContourBridge
