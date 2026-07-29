import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import InfoGeometry.Section5

open scoped BigOperators

/-!
# Section 13: Fibrations and the Structure of Two-Qubit Space

This file formalizes the finite algebraic core of the two-qubit fibration
section.

It does not claim a full topological construction.  The honest Hopf-level map is
the pre-projective quaternionic projection `S^7 -> HP^1 ~= S^4` with `S^3`
fiber.  After quotienting by global phase, the projective map `CP^3 -> S^4` is
the twistor fibration, with projective fiber `CP^1 ~= S^2`, not a Hopf
fibration.  This file proves the finite algebra that the section uses:

* normalized two-qubit vectors are the `S^7` finite shadow;
* norm-preserving local-unitary shadows preserve normalization and define fiber
  orbits;
* product states have zero concurrence determinant;
* pure-state density matrices satisfy the rank-one minor identity;
* gamma/Horodecki-style coordinates are expectation-value readouts built from
  the Section 5 Pauli-Dirac gamma matrices.
-/

noncomputable section

namespace Section13

open Matrix

abbrev TwoQubitVec := Fin 4 → ℂ
abbrev OneQubitVec := Fin 2 → ℂ
abbrev DiracMatrix := Section5.DiracMatrix

/-! ## 13.1 The finite `S^7` shadow -/

/-- Squared norm of a two-qubit vector. -/
def stateNormSq (ψ : TwoQubitVec) : ℂ :=
  ∑ i : Fin 4, star (ψ i) * ψ i

/-- Squared norm of a one-qubit vector. -/
def oneQubitNormSq (ψ : OneQubitVec) : ℂ :=
  ∑ i : Fin 2, star (ψ i) * ψ i

/-- Normalized two-qubit vectors are the finite algebraic shadow of `S^7`. -/
def IsNormalized (ψ : TwoQubitVec) : Prop :=
  stateNormSq ψ = 1

/-- The `S^7` shadow as a subtype of normalized two-qubit vectors. -/
def S7Shadow := {ψ : TwoQubitVec // IsNormalized ψ}

namespace S7Shadow

def vec (ψ : S7Shadow) : TwoQubitVec := ψ.1

theorem normalized (ψ : S7Shadow) : IsNormalized ψ.vec := ψ.2

def mk (vec : TwoQubitVec) (normalized : IsNormalized vec) : S7Shadow :=
  ⟨vec, normalized⟩

end S7Shadow

/-- Computational tensor product of two one-qubit vectors. -/
def tensor2 (u v : OneQubitVec) : TwoQubitVec
  | 0 => u 0 * v 0
  | 1 => u 0 * v 1
  | 2 => u 1 * v 0
  | 3 => u 1 * v 1

/-- Norm multiplicativity for product two-qubit states. -/
theorem stateNormSq_tensor2 (u v : OneQubitVec) :
    stateNormSq (tensor2 u v) = oneQubitNormSq u * oneQubitNormSq v := by
  simp [stateNormSq, oneQubitNormSq, tensor2, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

/-- If both one-qubit factors are normalized, their tensor product is normalized. -/
theorem tensor2_normalized_of_factors
    (u v : OneQubitVec) (hu : oneQubitNormSq u = 1) (hv : oneQubitNormSq v = 1) :
    IsNormalized (tensor2 u v) := by
  unfold IsNormalized
  rw [stateNormSq_tensor2, hu, hv]
  ring

/-! ## 13.1 Fibers as local-unitary orbits -/

/--
A finite local-unitary shadow is an invertible norm-preserving endomorphism of
two-qubit vectors.  This is the algebraic orbit/fiber layer, not a topological
construction of `SU(2)`.
-/
structure LocalUnitaryShadow where
  map : TwoQubitVec → TwoQubitVec
  inv : TwoQubitVec → TwoQubitVec
  left_inv : ∀ ψ : TwoQubitVec, inv (map ψ) = ψ
  right_inv : ∀ ψ : TwoQubitVec, map (inv ψ) = ψ
  norm_preserving : ∀ ψ : TwoQubitVec, stateNormSq (map ψ) = stateNormSq ψ

namespace LocalUnitaryShadow

/-- Identity local-unitary shadow. -/
def id : LocalUnitaryShadow where
  map := fun ψ => ψ
  inv := fun ψ => ψ
  left_inv := by intro ψ; rfl
  right_inv := by intro ψ; rfl
  norm_preserving := by intro ψ; rfl

/-- Inverse local-unitary shadow. -/
def symm (U : LocalUnitaryShadow) : LocalUnitaryShadow where
  map := U.inv
  inv := U.map
  left_inv := U.right_inv
  right_inv := U.left_inv
  norm_preserving := by
    intro ψ
    rw [← U.norm_preserving (U.inv ψ), U.right_inv ψ]

/-- Composition of local-unitary shadows. -/
def comp (V U : LocalUnitaryShadow) : LocalUnitaryShadow where
  map := fun ψ => V.map (U.map ψ)
  inv := fun ψ => U.inv (V.inv ψ)
  left_inv := by
    intro ψ
    rw [V.left_inv, U.left_inv]
  right_inv := by
    intro ψ
    rw [U.right_inv, V.right_inv]
  norm_preserving := by
    intro ψ
    rw [V.norm_preserving, U.norm_preserving]

/-- A local-unitary shadow preserves the `S^7` normalization predicate. -/
theorem preserves_normalized (U : LocalUnitaryShadow)
    (ψ : TwoQubitVec) (hψ : IsNormalized ψ) :
    IsNormalized (U.map ψ) := by
  unfold IsNormalized at hψ ⊢
  rw [U.norm_preserving, hψ]

/-- A local-unitary shadow acts on the normalized-state subtype. -/
def mapS7 (U : LocalUnitaryShadow) (ψ : S7Shadow) : S7Shadow :=
  S7Shadow.mk (U.map ψ.vec) (U.preserves_normalized ψ.vec ψ.normalized)

end LocalUnitaryShadow

/-- Same-fiber relation: two states are connected by a local-unitary shadow. -/
def sameFiber (ψ φ : TwoQubitVec) : Prop :=
  ∃ U : LocalUnitaryShadow, U.map ψ = φ

/-- Reflexivity of the explicitly defined same-fiber relation, witnessed by the identity shadow. -/
theorem sameFiber_refl (ψ : TwoQubitVec) : sameFiber ψ ψ := by
  exact ⟨LocalUnitaryShadow.id, rfl⟩

theorem sameFiber_symm {ψ φ : TwoQubitVec} (h : sameFiber ψ φ) :
    sameFiber φ ψ := by
  rcases h with ⟨U, hU⟩
  refine ⟨U.symm, ?_⟩
  calc
    U.inv φ = U.inv (U.map ψ) := by rw [hU]
    _ = ψ := U.left_inv ψ

theorem sameFiber_trans {ψ φ χ : TwoQubitVec}
    (hψφ : sameFiber ψ φ) (hφχ : sameFiber φ χ) :
    sameFiber ψ χ := by
  rcases hψφ with ⟨U, hU⟩
  rcases hφχ with ⟨V, hV⟩
  refine ⟨V.comp U, ?_⟩
  simp [LocalUnitaryShadow.comp, hU, hV]

/-- Same-fiber is an equivalence relation. -/
theorem sameFiber_equivalence : Equivalence sameFiber where
  refl := sameFiber_refl
  symm := by intro ψ φ h; exact sameFiber_symm h
  trans := by intro ψ φ χ hψφ hφχ; exact sameFiber_trans hψφ hφχ

/-- Same-fiber states share normalization because the witness is norm-preserving. -/
theorem sameFiber_preserves_normalized {ψ φ : TwoQubitVec}
    (hFiber : sameFiber ψ φ) (hψ : IsNormalized ψ) :
    IsNormalized φ := by
  rcases hFiber with ⟨U, hU⟩
  unfold IsNormalized at hψ ⊢
  rw [← hU, U.norm_preserving, hψ]

/-! ## 13.1 Separable states and concurrence determinant -/

/-- Concurrence amplitude `ad - bc` for a two-qubit pure state. -/
def concurrenceAmplitude (ψ : TwoQubitVec) : ℂ :=
  ψ 0 * ψ 3 - ψ 1 * ψ 2

/-- Product states have zero concurrence amplitude. -/
theorem concurrenceAmplitude_tensor2 (u v : OneQubitVec) :
    concurrenceAmplitude (tensor2 u v) = 0 := by
  simp [concurrenceAmplitude, tensor2]
  ring

/-! ## 13.1 Pure density matrix algebra -/

/-- Pure-state density matrix `rho = |psi><psi|`. -/
def density (ψ : TwoQubitVec) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => ψ i * star (ψ j)

/-- The density trace is the squared state norm. -/
theorem density_trace_eq_norm (ψ : TwoQubitVec) :
    (∑ i : Fin 4, density ψ i i) = stateNormSq ψ := by
  unfold density stateNormSq
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A normalized pure-state density matrix has trace one. -/
theorem density_trace_eq_one_of_normalized
    (ψ : TwoQubitVec) (hψ : IsNormalized ψ) :
    (∑ i : Fin 4, density ψ i i) = 1 := by
  rw [density_trace_eq_norm, hψ]

/-- Rank-one minor identity for pure-state density matrices. -/
theorem density_rank_one_minor
    (ψ : TwoQubitVec) (i j k l : Fin 4) :
    density ψ i j * density ψ k l = density ψ i l * density ψ k j := by
  simp [density]
  ring

/-! ## 13.2 Gamma/Horodecki-style base readouts -/

/-- Expectation-value coordinate `⟨ψ|A|ψ⟩`. -/
def gammaExpectation (A : DiracMatrix) (ψ : TwoQubitVec) : ℂ :=
  ∑ i : Fin 4, star (ψ i) * (∑ j : Fin 4, A i j * ψ j)

/-- The five gamma matrices used as the finite `S^4` base-coordinate readout. -/
def hopfGamma : Fin 5 → DiracMatrix
  | 0 => Section5.γ0
  | 1 => Section5.γ1
  | 2 => Section5.γ2
  | 3 => Section5.γ3
  | 4 => Section5.γ5

/-- Gamma expectation coordinates, the finite algebraic base readout. -/
def hopfBaseReadout (ψ : TwoQubitVec) : Fin 5 → ℂ :=
  fun a => gammaExpectation (hopfGamma a) ψ

/-- Definitional zero-state check: every gamma expectation vanishes on the zero vector. -/
theorem gammaExpectation_zero_state (A : DiracMatrix) :
    gammaExpectation A 0 = 0 := by
  simp [gammaExpectation]

theorem hopfBaseReadout_zero :
    hopfBaseReadout 0 = 0 := by
  funext a
  fin_cases a <;> simp [hopfBaseReadout, hopfGamma, gammaExpectation_zero_state]

/-- Section 5 gamma matrices provide the Clifford relation used by the readout. -/
theorem gamma5_anticommutes_gamma0 :
    Section5.γ5 * Section5.γ0 + Section5.γ0 * Section5.γ5 =
      (0 : DiracMatrix) :=
  (Section5.γ5_anticomm).1

/-- Capstone packet for the finite algebraic Section 13 surface. -/
theorem section13_capstone :
    (∀ u v : OneQubitVec,
      stateNormSq (tensor2 u v) = oneQubitNormSq u * oneQubitNormSq v) ∧
    (∀ ψ φ : TwoQubitVec, sameFiber ψ φ → IsNormalized ψ → IsNormalized φ) ∧
    (∀ u v : OneQubitVec, concurrenceAmplitude (tensor2 u v) = 0) ∧
    (∀ ψ : TwoQubitVec, (∑ i : Fin 4, density ψ i i) = stateNormSq ψ) ∧
    (∀ ψ : TwoQubitVec, ∀ i j k l : Fin 4,
      density ψ i j * density ψ k l = density ψ i l * density ψ k j) ∧
    hopfBaseReadout 0 = 0 ∧
    Section5.γ5 * Section5.γ0 + Section5.γ0 * Section5.γ5 =
      (0 : DiracMatrix) := by
  exact ⟨stateNormSq_tensor2,
    (fun ψ φ hFiber hψ => sameFiber_preserves_normalized hFiber hψ),
    concurrenceAmplitude_tensor2, density_trace_eq_norm, density_rank_one_minor,
    hopfBaseReadout_zero, gamma5_anticommutes_gamma0⟩

end Section13
