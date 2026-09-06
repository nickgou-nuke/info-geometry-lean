import InfoGeometry.Canonical.V4SemidirectS3Bridge
import InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleFormulas
import InfoGeometry.Physics.SouriauMassieuPlanckFunctional
import InfoGeometry.Topology.O55V4KleinBottleFinite
import InfoGeometry.Algebra.SplitOctonionPeirceExteriorBridge

/-!
# Finite Peirce-parity and `V₄` grand-canonical character readout

This owner is deliberately finite.  It uses the repository's actual `V₄`
group, the finite Souriau partition function, and the finite `O(5,5)`
coordinate shadow.  It does not introduce a Haar integral on the non-compact
group `O(5,5)`, nor identify this finite packet with a Chern character or an
infinite-dimensional index.
-/

noncomputable section

namespace InfoGeometry.Canonical.PeirceV4GrandCanonicalCharacterBridge

open scoped BigOperators
open InfoGeometry.Canonical.V4SemidirectS3Bridge
open V4Element
open InfoGeometry.Physics.SouriauMassieuPlanckFunctional
open InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleFormulas
open InfoGeometry.Topology.O55V4KleinBottleFinite
open InfoGeometry.Algebra.SplitOctonionPeirceExteriorBridge

/-! ## The concrete `V₄` Peirce grading -/

/-- Peirce occupation parity on the four concrete `V₄` sectors. -/
def peirceParity : V4Element → ℕ
  | I => 0
  | J => 1
  | S => 1
  | JS => 0

/-- The associated Frobenius--Schur sign. -/
def peirceSign (g : V4Element) : ℤ := (-1 : ℤ) ^ peirceParity g

@[simp] theorem peirceParity_values :
    peirceParity I = 0 ∧ peirceParity J = 1 ∧
      peirceParity S = 1 ∧ peirceParity JS = 0 := by
  simp [peirceParity]

@[simp] theorem peirceSign_values :
    peirceSign I = 1 ∧ peirceSign J = -1 ∧
      peirceSign S = -1 ∧ peirceSign JS = 1 := by
  norm_num [peirceSign, peirceParity]

/-- The Peirce sign is a genuine one-dimensional character of `V₄`. -/
theorem peirceSign_mul (g h : V4Element) :
    peirceSign (g * h) = peirceSign g * peirceSign h := by
  cases g <;> cases h <;> norm_num [peirceSign, peirceParity]

theorem peirceSign_one : peirceSign (1 : V4Element) = 1 := by
  norm_num [peirceSign, peirceParity]

/-! ## Souriau and grand-canonical readouts -/

/-- Finite parity energy used by the concrete Souriau ensemble. -/
def peirceEnergy (g : V4Element) : ℝ := peirceParity g

/-- The finite Souriau partition for the four Peirce sectors. -/
def peirceSouriauPartition (β : ℝ) : ℝ :=
  souriauPartition β peirceEnergy

theorem peirceSouriauPartition_pos (β : ℝ) :
    0 < peirceSouriauPartition β := by
  exact souriauPartition_pos β peirceEnergy

/-- Grand-canonical effective energy with Peirce parity as particle number. -/
def peirceEffectiveEnergy (μ : ℝ) (g : V4Element) : ℝ :=
  effectiveEnergy (fun _ : V4Element => 0) peirceEnergy μ g

theorem peirceEffectiveEnergy_eq (μ : ℝ) (g : V4Element) :
    peirceEffectiveEnergy μ g = -μ * peirceEnergy g := by
  unfold peirceEffectiveEnergy effectiveEnergy
  ring

/-- Finite parity-twisted Souriau partition; positivity is not asserted because
the character is signed. -/
def peirceCharacterPartition (β : ℝ) : ℝ :=
  ∑ g : V4Element, (peirceSign g : ℝ) * Real.exp (-β * peirceEnergy g)

theorem peirceCharacterPartition_eq_even_sub_odd (β : ℝ) :
    peirceCharacterPartition β =
      Real.exp (-β * peirceEnergy I) + Real.exp (-β * peirceEnergy JS) -
      (Real.exp (-β * peirceEnergy J) + Real.exp (-β * peirceEnergy S)) := by
  classical
  unfold peirceCharacterPartition
  have huniv : (Finset.univ : Finset V4Element) = {I, J, S, JS} := by
    ext g
    cases g <;> simp
  rw [huniv]
  simp [peirceSign, peirceParity, peirceEnergy]
  ring

/-! ## The concrete `(1,3,3,1)` coordinate character polynomials

`ExteriorThreeSpace` is the repository's finite coordinate carrier for the
four Peirce grades.  The following are polynomial readouts of its four grade
multiplicities; they do not assert a trace theorem for an unrelated matrix
representation.
-/

def peirceExteriorPartition (q : ℝ) : ℝ := 1 + 3 * q + 3 * q ^ 2 + q ^ 3

def peirceExteriorParityPartition (q : ℝ) : ℝ :=
  1 + 3 * q - 3 * q ^ 2 - q ^ 3

def peirceExteriorChiralityPartition (q : ℝ) : ℝ :=
  1 - 3 * q + 3 * q ^ 2 - q ^ 3

def peirceExteriorMiddlePartition (q : ℝ) : ℝ :=
  1 - 3 * q - 3 * q ^ 2 + q ^ 3

theorem peirceExteriorPartition_eq_binomial (q : ℝ) :
    peirceExteriorPartition q = (1 + q) ^ 3 := by
  dsimp [peirceExteriorPartition]
  ring

theorem peirceExteriorParityPartition_eq_factor (q : ℝ) :
    peirceExteriorParityPartition q = (1 - q) * (q ^ 2 + 4 * q + 1) := by
  dsimp [peirceExteriorParityPartition]
  ring

theorem peirceExteriorChiralityPartition_eq_factor (q : ℝ) :
    peirceExteriorChiralityPartition q = (1 - q) ^ 3 := by
  dsimp [peirceExteriorChiralityPartition]
  ring

theorem peirceExteriorMiddlePartition_eq_factor (q : ℝ) :
    peirceExteriorMiddlePartition q = (1 + q) * (q ^ 2 - 4 * q + 1) := by
  dsimp [peirceExteriorMiddlePartition]
  ring

theorem peirceExterior_character_values :
    peirceExteriorPartition 1 = 8 ∧
    peirceExteriorParityPartition 1 = 0 ∧
    peirceExteriorChiralityPartition 1 = 0 ∧
    peirceExteriorMiddlePartition 1 = -4 := by
  norm_num [peirceExteriorPartition, peirceExteriorParityPartition,
    peirceExteriorChiralityPartition, peirceExteriorMiddlePartition]

/-! ## Finite `O(5,5)` readback -/

theorem peirce_v4_o55_finite_packet (x y : Vec55) :
    splitPair55 (negAll x) (negAll y) = splitPair55 x y ∧
    splitPair55 (reflPair0 x) (reflPair0 y) = splitPair55 x y ∧
    splitPair55 (reflPair1 x) (reflPair1 y) = splitPair55 x y ∧
    reflPair0 (reflPair1 x) = reflPair1 (reflPair0 x) := by
  exact ⟨negAll_preserves_splitPair x y,
    reflPair0_preserves_splitPair x y,
    reflPair1_preserves_splitPair x y,
    reflPair0_comm_reflPair1 x⟩

end InfoGeometry.Canonical.PeirceV4GrandCanonicalCharacterBridge
