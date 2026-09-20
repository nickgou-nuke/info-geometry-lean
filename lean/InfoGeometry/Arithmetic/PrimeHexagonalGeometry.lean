import InfoGeometry.Canonical.D6ReciprocalLatticeBrillouinZone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

namespace InfoGeometry.Arithmetic.PrimeHexagonalGeometry

open InfoGeometry.Canonical.D6ReciprocalLatticeBrillouinZone

namespace ProofDependency

inductive Archetype
  | primeLogEnergy
  | reciprocalRotation
  | invariantMetric
  | cyclotomicSpectrum
  | voronoiCell
  | primeLabelCovariance
  deriving DecidableEq, Fintype

def prerequisites : Archetype → Finset Archetype
  | .primeLogEnergy => {.primeLogEnergy}
  | .reciprocalRotation => {.reciprocalRotation}
  | .invariantMetric => {.reciprocalRotation, .invariantMetric}
  | .cyclotomicSpectrum => {.reciprocalRotation, .cyclotomicSpectrum}
  | .voronoiCell => {.reciprocalRotation, .invariantMetric, .voronoiCell}
  | .primeLabelCovariance => {.primeLogEnergy, .reciprocalRotation, .primeLabelCovariance}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem cell_and_arithmetic_incomparable :
    ¬ Archetype.voronoiCell ≤ Archetype.primeLogEnergy ∧
    ¬ Archetype.primeLogEnergy ≤ Archetype.voronoiCell := by
  change
    ¬ prerequisites .voronoiCell ⊆ prerequisites .primeLogEnergy ∧
    ¬ prerequisites .primeLogEnergy ⊆ prerequisites .voronoiCell
  decide

end ProofDependency

noncomputable section

abbrev Plane := Fin 2 → ℝ

def latticeEmbedding (point : ReciprocalCoord) : Plane :=
  fun coordinate => (point coordinate : ℝ)

def triangularNormSq (point : Plane) : ℝ :=
  point 0 ^ 2 + point 0 * point 1 + point 1 ^ 2

theorem triangular_norm_nonneg (point : Plane) :
    0 ≤ triangularNormSq point := by
  dsimp [triangularNormSq]
  nlinarith [sq_nonneg (point 0 + point 1), sq_nonneg (point 0), sq_nonneg (point 1)]

theorem triangular_norm_eq_zero_iff (point : Plane) :
    triangularNormSq point = 0 ↔ point = 0 := by
  constructor
  · intro norm_zero
    have first_zero : point 0 = 0 := by
      dsimp [triangularNormSq] at norm_zero
      nlinarith [sq_nonneg (point 0 + point 1), sq_nonneg (point 1)]
    have second_zero : point 1 = 0 := by
      simpa [triangularNormSq, first_zero] using norm_zero
    ext coordinate
    fin_cases coordinate <;> assumption
  · rintro rfl
    simp [triangularNormSq]

theorem triangular_norm_rotate (point : Plane) :
    triangularNormSq (realAxialRotate point) = triangularNormSq point := by
  simp [triangularNormSq, realAxialRotate]
  ring

theorem triangular_norm_reflect (point : Plane) :
    triangularNormSq (realAxialReflect point) = triangularNormSq point := by
  simp [triangularNormSq, realAxialReflect]
  ring

theorem rotation_lattice_difference (point : Plane) (lattice : ReciprocalCoord) :
    realAxialRotate (point - latticeEmbedding lattice) =
      realAxialRotate point - latticeEmbedding (axialRotate lattice) := by
  ext coordinate
  fin_cases coordinate <;> simp [realAxialRotate, axialRotate, latticeEmbedding] <;> ring

def originVoronoiCell : Set Plane :=
  {point | ∀ lattice : ReciprocalCoord,
    triangularNormSq point ≤ triangularNormSq (point - latticeEmbedding lattice)}

theorem origin_voronoi_rotation_invariant (point : Plane) :
    realAxialRotate point ∈ originVoronoiCell ↔ point ∈ originVoronoiCell := by
  constructor
  · intro membership lattice
    have bound := membership (axialRotate lattice)
    rw [← rotation_lattice_difference, triangular_norm_rotate, triangular_norm_rotate] at bound
    exact bound
  · intro membership lattice
    calc
      triangularNormSq (realAxialRotate point) = triangularNormSq point :=
        triangular_norm_rotate point
      _ ≤ triangularNormSq (point - latticeEmbedding (axialRotateInv lattice)) :=
        membership (axialRotateInv lattice)
      _ = triangularNormSq (realAxialRotate point - latticeEmbedding lattice) := by
        rw [← triangular_norm_rotate (point - latticeEmbedding (axialRotateInv lattice)),
          rotation_lattice_difference, axialRotateInv_right]

def nearestRootCell : Set Plane :=
  {point | ∀ root : Fin 6,
    triangularNormSq point ≤ triangularNormSq (point - latticeEmbedding (hexStarFin root))}

theorem origin_voronoi_subset_nearest_root_cell : originVoronoiCell ⊆ nearestRootCell := by
  intro point membership root
  exact membership (hexStarFin root)

theorem nearest_root_cell_iff_six_halfplanes (point : Plane) :
    point ∈ nearestRootCell ↔
      |2 * point 0 + point 1| ≤ 1 ∧
      |point 0 + 2 * point 1| ≤ 1 ∧
      |point 0 - point 1| ≤ 1 := by
  simp [nearestRootCell, triangularNormSq, latticeEmbedding, hexStarFin,
    Fin.forall_fin_succ, abs_le]
  aesop (add safe (by nlinarith))

def dualCoordinates (point : Plane) : Plane :=
  ![2 * point 0 + point 1, -(point 0 + 2 * point 1)]

theorem nearest_root_cell_iff_hexagonal_dual (point : Plane) :
    point ∈ nearestRootCell ↔
      max (max |dualCoordinates point 0| |dualCoordinates point 1|)
        |dualCoordinates point 0 + dualCoordinates point 1| ≤ 1 := by
  rw [nearest_root_cell_iff_six_halfplanes]
  have dual_sum : dualCoordinates point 0 + dualCoordinates point 1 = point 0 - point 1 := by
    simp [dualCoordinates]
    ring
  have negative_norm : |dualCoordinates point 1| = |point 0 + 2 * point 1| := by
    exact abs_neg _
  rw [max_le_iff, max_le_iff, dual_sum, negative_norm]
  exact and_assoc.symm

def rotationMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 1]

theorem rotation_matrix_apply (point : Plane) :
    rotationMatrix.mulVec point = realAxialRotate point := by
  ext coordinate
  fin_cases coordinate <;> simp [rotationMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, realAxialRotate]

theorem rotation_charpoly_eq_cyclotomic_six :
    rotationMatrix.charpoly = Polynomial.cyclotomic 6 ℝ := by
  rw [Matrix.charpoly_fin_two, Polynomial.cyclotomic_six]
  norm_num [rotationMatrix, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two]

def primeLinearEnergy (first second : Nat.Primes) (point : Plane) : ℝ :=
  Real.log (first : ℝ) * point 0 + Real.log (second : ℝ) * point 1

theorem prime_energy_reflection_covariance (first second : Nat.Primes) (point : Plane) :
    primeLinearEnergy first second (realAxialReflect point) =
      primeLinearEnergy second first point := by
  simp [primeLinearEnergy, realAxialReflect, add_comm]

theorem prime_energy_reflection_invariant_iff (first second : Nat.Primes) :
    (∀ point, primeLinearEnergy first second (realAxialReflect point) =
      primeLinearEnergy first second point) ↔ first = second := by
  constructor
  · intro invariant
    have log_equal : Real.log (first : ℝ) = Real.log (second : ℝ) := by
      simpa [primeLinearEnergy, realAxialReflect] using (invariant ![1, 0]).symm
    have first_pos : 0 < (first : ℝ) := by exact_mod_cast first.property.pos
    have second_pos : 0 < (second : ℝ) := by exact_mod_cast second.property.pos
    have real_equal := Real.log_injOn_pos first_pos second_pos log_equal
    apply Subtype.ext
    exact_mod_cast real_equal
  · rintro rfl point
    exact prime_energy_reflection_covariance first first point

end

end InfoGeometry.Arithmetic.PrimeHexagonalGeometry
