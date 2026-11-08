import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical Souriau Thermodynamics for Pauli Algebra (toy finite model)

This file gives a finite formal model of the canonical Souriau statement
for Pauli thermodynamics, keeping the Pauli paravector slot as a free
Weyl gauge component.
-/

noncomputable section

open Complex Matrix
open scoped BigOperators

namespace CanonicalSouriauPauliThermodynamics

/-- Pauli dual space in the su(2) lane: 3 real components. -/
abbrev PauliDual : Type := InfoGeometry.Algebra.FiniteSpin.Vec3R

/-- Full Pauli/paravector dual space: 4 real components `(s₀,s₁,s₂,s₃)`. -/
abbrev PauliParavector : Type := InfoGeometry.Algebra.FiniteSpin.Vec4R

/-- Canonical 3-component pairing `⟨β, J⟩ = ∑ β_i J_i`. -/
def pauliPairing (β J : PauliDual) : ℝ :=
  ∑ i : Fin 3, β i * J i

/-- Full 4-component paravector pairing `⟨β, J⟩ = ∑ β_A J_A`. -/
def pauliParavectorPairing (β J : PauliParavector) : ℝ :=
  ∑ i : Fin 4, β i * J i

/-- Dual-space Gibbs/Boltzmann factor for a 3-vector Pauli moment. -/
def pauliBoltzmannWeight (β J : PauliDual) : ℝ :=
  Real.exp (-(pauliPairing β J))

/-- Dual-space Gibbs/Boltzmann factor for a full 4-vector Pauli paravector moment. -/
def pauliParavectorBoltzmannWeight (β J : PauliParavector) : ℝ :=
  Real.exp (-(pauliParavectorPairing β J))

/-- One-mode Pauli grand-canonical local factor: `1 + exp(-⟨β, J⟩)`. -/
def pauliLocalPartition (β J : PauliDual) : ℝ :=
  1 + pauliBoltzmannWeight β J

/-- One-mode Pauli full-paravector local factor: `1 + exp(-⟨β, J⟩)`. -/
def pauliParavectorLocalPartition (β J : PauliParavector) : ℝ :=
  1 + pauliParavectorBoltzmannWeight β J

/-- Concrete 3-axis embedding `i=0 ↦ a, i=1 ↦ b, i=2 ↦ c`. -/
def pauliAxis (a b c : ℝ) : PauliDual :=
  fun i => if i.1 = 0 then a else if i.1 = 1 then b else c

/-- Concrete 4-axis embedding `(t,x,y,z)`. -/
def pauliParavectorAxis (t x y z : ℝ) : PauliParavector :=
  fun i => if i.1 = 0 then t else if i.1 = 1 then x else if i.1 = 2 then y else z

/-- Lift a spatial 3-vector to a 4-vector by adding scalar slot `s₀ := s0`. -/
def pauliParavectorFrom3 (s0 : ℝ) (β : PauliDual) : PauliParavector :=
  fun i => if i.1 = 0 then s0 else if i.1 = 1 then β 0 else if i.1 = 2 then β 1 else β 2

/-- Pairing is the standard Euclidean dot-product formula in the 3-coordinate basis. -/
theorem pauliPairing_axis (a b c p q r : ℝ) :
    pauliPairing (pauliAxis a b c) (pauliAxis p q r) = a * p + b * q + c * r := by
  simp [pauliPairing, pauliAxis, Fin.sum_univ_three]

/-- Pairing is the standard Euclidean dot-product formula in the 4-coordinate basis. -/
theorem pauliParavectorPairing_axis (t x y z p q r s : ℝ) :
    pauliParavectorPairing (pauliParavectorAxis t x y z) (pauliParavectorAxis p q r s)
      = t * p + x * q + y * r + z * s := by
  simp [pauliParavectorPairing, pauliParavectorAxis, Fin.sum_univ_four, add_assoc]

/-- Decomposition for both source and target lifted from spatial components, keeping
    both scalar slots `β₀` and `J₀` free.

    This is the “free Weyl gauge” version: no gauge fixing `J₀ = 1` is imposed.
-/
theorem pauliParavectorPairing_from3_free (β0 J0 : ℝ) (β J : PauliDual) :
    pauliParavectorPairing (pauliParavectorFrom3 β0 β) (pauliParavectorFrom3 J0 J)
      = β0 * J0 + pauliPairing β J := by
  have h3 : (∑ i : Fin 3, β i * J i) = β 0 * J 0 + β 1 * J 1 + β 2 * J 2 := by
    simp [Fin.sum_univ_three, add_assoc]
  rw [pauliPairing, h3]
  simp [pauliParavectorPairing, pauliParavectorFrom3, Fin.sum_univ_four, add_assoc]

/-- Decomposition in the gauge choice `J₀ = 1`; this is recovered from
    `pauliParavectorPairing_from3_free`.
-/
theorem pauliParavectorPairing_from3_with_identity (β0 : ℝ) (β J : PauliDual) :
    pauliParavectorPairing (pauliParavectorFrom3 β0 β) (pauliParavectorFrom3 1 J)
      = β0 + pauliPairing β J := by
  simpa using (pauliParavectorPairing_from3_free β0 1 β J)

/-- Specialization to a single (spin-axis) inverse temperature component (3-vector lane). -/
theorem pauliPairing_single_axis (βz ξz : ℝ) :
    pauliPairing (pauliAxis 0 0 βz) (pauliAxis 0 0 ξz) = βz * ξz := by
  simp [pauliPairing, pauliAxis, Fin.sum_univ_three]

/-- Canonical local partition reduces to the usual scalar Pauli-mode expression (3-vector lane). -/
theorem pauliLocalPartition_single_axis (βz ξz : ℝ) :
    pauliLocalPartition (pauliAxis 0 0 βz) (pauliAxis 0 0 ξz)
      = (1 + Real.exp (-(βz * ξz))) := by
  simp [pauliLocalPartition, pauliBoltzmannWeight, pauliPairing_single_axis]

/-- Full-paravector scalar-slot normalization in a fixed identity source `J₀ = 1`:

`exp(-(β₀ + ⟨β⃗, J⃗⟩)) = exp(-β₀) * exp(-⟨β⃗, J⃗⟩)`.
So the identity component is an overall Gibbs prefactor in that gauge.
-/
theorem pauliParavectorBoltzmann_with_identity (β0 : ℝ) (β J : PauliDual) :
    pauliParavectorBoltzmannWeight (pauliParavectorFrom3 β0 β) (pauliParavectorFrom3 1 J)
      = Real.exp (-β0) * pauliBoltzmannWeight β J := by
  rw [pauliParavectorBoltzmannWeight, pauliBoltzmannWeight,
    pauliParavectorPairing_from3_with_identity]
  have hsplit : -(β0 + pauliPairing β J) = (-β0) + (-(pauliPairing β J)) := by ring
  rw [hsplit]
  rw [Real.exp_add]

/-- Corresponding full local partition formula in the same gauge:
`1 + exp(-(β₀ + ⟨β⃗, J⃗⟩)) = 1 + exp(-β₀) * exp(-⟨β⃗, J⃗⟩)` -/
theorem pauliParavectorLocalPartition_with_identity (β0 : ℝ) (β J : PauliDual) :
    pauliParavectorLocalPartition (pauliParavectorFrom3 β0 β) (pauliParavectorFrom3 1 J)
      = 1 + Real.exp (-β0) * pauliBoltzmannWeight β J := by
  simp [pauliParavectorLocalPartition, pauliParavectorBoltzmann_with_identity]

/-- Free Weyl scaling on paravectors: `β ↦ σβ`, `J ↦ σ⁻¹J`. -/
def pauliWeylScale (σ : ℝˣ) (v : PauliParavector) : PauliParavector :=
  fun i => (σ : ℝ) * v i

/-- Pauli pairing is Weyl-scale neutral when dual and primal scales are inverse. -/
theorem pauliParavectorPairing_weyl (σ : ℝˣ) (β J : PauliParavector) :
    pauliParavectorPairing (pauliWeylScale σ β) (pauliWeylScale σ⁻¹ J)
      = pauliParavectorPairing β J := by
  unfold pauliParavectorPairing pauliWeylScale
  have hs : ((↑σ : ℝ) * ((↑σ)⁻¹ : ℝ)) = 1 := by simp
  have hsum : ∑ i, (↑σ : ℝ) * β i * (((↑σ)⁻¹ : ℝ) * J i) = ∑ i, β i * J i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      (↑σ : ℝ) * β i * (((↑σ)⁻¹ : ℝ) * J i)
          = ((↑σ : ℝ) * ((↑σ)⁻¹ : ℝ)) * (β i * J i) := by ring
      _ = β i * J i := by rw [hs]; ring
  simpa [show (↑(σ⁻¹) : ℝ) = ((↑σ)⁻¹ : ℝ) by simp] using hsum

/-- Corresponding Boltzmann factor is Weyl-gauge invariant. -/
theorem pauliParavectorBoltzmannWeight_weyl (σ : ℝˣ) (β J : PauliParavector) :
    pauliParavectorBoltzmannWeight (pauliWeylScale σ β) (pauliWeylScale σ⁻¹ J)
      = pauliParavectorBoltzmannWeight β J := by
  rw [pauliParavectorBoltzmannWeight, pauliParavectorBoltzmannWeight, pauliParavectorPairing_weyl]

/-- Corresponding local partition is Weyl-gauge invariant. -/
theorem pauliParavectorLocalPartition_weyl (σ : ℝˣ) (β J : PauliParavector) :
    pauliParavectorLocalPartition (pauliWeylScale σ β) (pauliWeylScale σ⁻¹ J)
      = pauliParavectorLocalPartition β J := by
  simp [pauliParavectorLocalPartition, pauliParavectorBoltzmannWeight_weyl]

-- Bridge note to `determinant_weyl_gauge`:
-- we keep the same free Weyl idea, now internalized here:
--
-- a scalar rescaling of a `2 × 2` real seed does not change the sign sector
-- classified by determinant (`+`, `-`, or null).

/-- Sign sector by determinant (positive / negative / null) for a `2×2` real matrix. -/
def pauliWeylSector (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Fin 3 :=
  if 0 < M.det then 0 else if M.det < 0 then 1 else 2

/-- Rescaling a real seed by a nonzero scalar preserves the sign sector. -/
theorem free_weyl_scale_preserves_determinant_sector
    (σ : ℝˣ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    pauliWeylSector ((σ : ℝ) • M) = pauliWeylSector M := by
  have hsq : 0 < (σ : ℝ) ^ 2 := by
    exact sq_pos_of_ne_zero (show (σ : ℝ) ≠ 0 by exact_mod_cast (Units.ne_zero σ))
  have hdet0 : (σ : ℝ) ^ 2 * M.det = 0 ↔ M.det = 0 := by
    constructor
    · intro h
      have hmul : ((σ : ℝ) ^ 2 = 0) ∨ M.det = 0 := by
        exact mul_eq_zero.mp h
      rcases hmul with hσ0 | hM
      · exfalso
        exact (sq_pos_of_ne_zero (show (σ : ℝ) ≠ 0 by exact_mod_cast (Units.ne_zero σ))).ne' hσ0
      · simpa using hM
    · intro hM
      simp [hM]
  have hpos : 0 < (σ : ℝ) ^ 2 * M.det ↔ 0 < M.det := by
    exact mul_pos_iff_of_pos_left hsq
  have hneg : (σ : ℝ) ^ 2 * M.det < 0 ↔ M.det < 0 := by
    constructor
    · intro h
      have h' : (σ : ℝ) ^ 2 * M.det < (σ : ℝ) ^ 2 * 0 := by simpa using h
      exact lt_of_mul_lt_mul_left h' (le_of_lt hsq)
    · intro h
      exact mul_neg_of_pos_of_neg hsq h
  simp [pauliWeylSector, hpos, hneg]

/--
Dictionary bridge from free-Souriau Weyl scaling to the determinant Weyl-sector
pattern in `determinant_weyl_gauge.lean`:
- paravector Gibbs data are invariant under inverse dual/primal scaling, and so is the
  determinant sign sector of a real `2×2` seed.
-/
theorem dictionary_weyl_gauge_souriau :
    (∀ σ : ℝˣ, ∀ β J : PauliParavector,
      pauliParavectorPairing (pauliWeylScale σ β) (pauliWeylScale σ⁻¹ J)
        = pauliParavectorPairing β J) ∧
    (∀ σ : ℝˣ, ∀ β J : PauliParavector,
      pauliParavectorBoltzmannWeight (pauliWeylScale σ β) (pauliWeylScale σ⁻¹ J)
        = pauliParavectorBoltzmannWeight β J) ∧
    (∀ σ : ℝˣ, ∀ β J : PauliParavector,
      pauliParavectorLocalPartition (pauliWeylScale σ β) (pauliWeylScale σ⁻¹ J)
        = pauliParavectorLocalPartition β J) ∧
    (∀ σ : ℝˣ, ∀ M : Matrix (Fin 2) (Fin 2) ℝ,
      pauliWeylSector ((σ : ℝ) • M) = pauliWeylSector M) := by
  exact ⟨pauliParavectorPairing_weyl, pauliParavectorBoltzmannWeight_weyl,
    pauliParavectorLocalPartition_weyl, free_weyl_scale_preserves_determinant_sector⟩

/-- Pauli generators over `ℂ` used for a concrete Hamiltonian model. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- Pauli-form Hamiltonian: `H = h0 I + hx σx + hy σy + hz σz`. -/
def pauliHamiltonian (h0 hx hy hz : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(h0:ℂ) + hz, hx - (Complex.I : ℂ) * hy; hx + (Complex.I : ℂ) * hy, (h0:ℂ) - hz]

/-- Determinant recovers the Pauli quadratic form `h0^2 - |h|^2`. -/
theorem pauliHamiltonian_det (h0 hx hy hz : ℝ) :
    (pauliHamiltonian h0 hx hy hz).det =
      ((h0 ^ 2 - (hx ^ 2 + hy ^ 2 + hz ^ 2) : ℝ) : ℂ) := by
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by simp
  simp [pauliHamiltonian, Matrix.det_fin_two]
  ring_nf
  rw [hI]
  ring

/-- Trace is the scalar part `2 h0`. -/
theorem pauliHamiltonian_trace (h0 hx hy hz : ℝ) :
    Matrix.trace (pauliHamiltonian h0 hx hy hz) = ((2 * h0 : ℝ) : ℂ) := by
  simp [pauliHamiltonian, Matrix.trace]
  ring

/-- Combined finite synthesis package for this module. -/
theorem canonical_souriau_pauli_thermo_synthesis :
    (∀ β J, pauliPairing β J = ∑ i : Fin 3, β i * J i) ∧
    (∀ β J, pauliBoltzmannWeight β J = Real.exp (-(pauliPairing β J))) ∧
    (∀ β J, pauliLocalPartition β J = 1 + pauliBoltzmannWeight β J) ∧
    (∀ a b c p q r, pauliPairing (pauliAxis a b c) (pauliAxis p q r) = a * p + b * q + c * r) ∧
    (∀ βz ξz, pauliLocalPartition (pauliAxis 0 0 βz) (pauliAxis 0 0 ξz) =
      (1 + Real.exp (-(βz * ξz)))) ∧
    (∀ β0 J0 β J,
      pauliParavectorPairing (pauliParavectorFrom3 β0 β) (pauliParavectorFrom3 J0 J)
        = β0 * J0 + pauliPairing β J) ∧
    (∀ β0 β J,
      pauliParavectorBoltzmannWeight (pauliParavectorFrom3 β0 β) (pauliParavectorFrom3 1 J)
        = Real.exp (-β0) * pauliBoltzmannWeight β J) ∧
    (∀ β0 β J,
      pauliParavectorLocalPartition (pauliParavectorFrom3 β0 β) (pauliParavectorFrom3 1 J)
        = 1 + Real.exp (-β0) * pauliBoltzmannWeight β J) ∧
    (∀ σ β J,
      pauliParavectorPairing (pauliWeylScale σ β) (pauliWeylScale σ⁻¹ J)
        = pauliParavectorPairing β J) ∧
    (∀ σ β J,
      pauliParavectorBoltzmannWeight (pauliWeylScale σ β) (pauliWeylScale σ⁻¹ J)
        = pauliParavectorBoltzmannWeight β J) ∧
    (∀ σ β J,
      pauliParavectorLocalPartition (pauliWeylScale σ β) (pauliWeylScale σ⁻¹ J)
        = pauliParavectorLocalPartition β J) ∧
    (∀ σ : ℝˣ, ∀ M,
      pauliWeylSector ((σ : ℝ) • M) = pauliWeylSector M) ∧
    (∀ h0 hx hy hz,
      (pauliHamiltonian h0 hx hy hz).det =
      ((h0 ^ 2 - (hx ^ 2 + hy ^ 2 + hz ^ 2) : ℝ) : ℂ)) ∧
    (∀ h0 hx hy hz,
      Matrix.trace (pauliHamiltonian h0 hx hy hz) = ((2 * h0 : ℝ) : ℂ)) := by
  exact ⟨
    fun _ _ => rfl,
    fun _ _ => rfl,
    fun _ _ => rfl,
    fun a b c p q r => pauliPairing_axis a b c p q r,
    fun βz ξz => pauliLocalPartition_single_axis βz ξz,
    fun β0 J0 β J => pauliParavectorPairing_from3_free β0 J0 β J,
    fun β0 β J => pauliParavectorBoltzmann_with_identity β0 β J,
    fun β0 β J => pauliParavectorLocalPartition_with_identity β0 β J,
    fun σ β J => pauliParavectorPairing_weyl σ β J,
    fun σ β J => pauliParavectorBoltzmannWeight_weyl σ β J,
    fun σ β J => pauliParavectorLocalPartition_weyl σ β J,
    fun σ M => free_weyl_scale_preserves_determinant_sector σ M,
    pauliHamiltonian_det,
    pauliHamiltonian_trace
  ⟩

end CanonicalSouriauPauliThermodynamics
