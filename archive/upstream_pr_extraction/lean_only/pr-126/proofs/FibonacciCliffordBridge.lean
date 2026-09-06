import Mathlib

/-!
# Fibonacci seed to Clifford atom bridge

This file formalizes the finite bridge asserted in the narrative:
Fibonacci fusion (`τ ⊗ τ = 1 ⊕ τ`) supplies the golden-ratio seed, while the
small even `osp(1|2)`/`sl₂` lanes are represented by the `Cl(1,1)` Pauli atom.
A two-atom tensor channel and finite prime-labelled product close the finite
holographic/tensor-network approximation.
-/

noncomputable section

open Matrix Real
open scoped BigOperators

namespace InfoGeometry.GrandUnification.FibonacciCliffordBridge

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M4R := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

/-- Golden ratio. -/
def φ : ℝ := (1 + Real.sqrt 5) / 2

lemma h5sq : (Real.sqrt 5)^2 = (5 : ℝ) :=
  Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

theorem golden_identity : φ^2 = φ + 1 := by
  dsimp [φ]
  calc
    ((1 + Real.sqrt 5) / 2)^2 = ((1 + Real.sqrt 5)^2) / 4 := by ring
    _ = (1 + 2*Real.sqrt 5 + (Real.sqrt 5)^2) / 4 := by ring
    _ = (1 + 2*Real.sqrt 5 + 5) / 4 := by rw [h5sq]
    _ = (6 + 2*Real.sqrt 5) / 4 := by ring
    _ = (3 + Real.sqrt 5) / 2 := by ring
    _ = (1 + Real.sqrt 5) / 2 + 1 := by ring

/-- Fibonacci sectors: vacuum and the nontrivial anyon `τ`. -/
inductive FibSector where
  | one | tau
  deriving DecidableEq, Repr

/-- Fibonacci fusion rule `τ ⊗ τ = 1 ⊕ τ`. -/
def fibFuse : FibSector → FibSector → List FibSector
  | FibSector.one, x => [x]
  | x, FibSector.one => [x]
  | FibSector.tau, FibSector.tau => [FibSector.one, FibSector.tau]

/-- Quantum dimension: `dim(τ)=φ`. -/
def fibDim : FibSector → ℝ
  | FibSector.one => 1
  | FibSector.tau => φ

theorem tau_fusion_dimension : fibDim FibSector.tau ^ 2 = fibDim FibSector.one + fibDim FibSector.tau := by
  simp [fibDim, golden_identity, add_comm]

/-- Chiral grading / `e₁` generator of the `Cl(1,1)` atom. -/
def sigma3 : M2R := !![1, 0; 0, -1]

/-- Real representative of `iσ₂`; `e₂²=-1`. -/
def iSigma2 : M2R := !![0, 1; -1, 0]

/-- Nilpotent raising/shear channel. -/
def sigmaPlus : M2R := !![0, 1; 0, 0]

/-- Clifford atom image of the Fibonacci sector. -/
def fibSectorToAtom : FibSector → M2R
  | FibSector.one => 1
  | FibSector.tau => sigma3

theorem sigma3_sq : sigma3 * sigma3 = (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigma3]

theorem iSigma2_sq : iSigma2 * iSigma2 = -(1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [iSigma2]

theorem sigma3_iSigma2_anticomm : sigma3 * iSigma2 + iSigma2 * sigma3 = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigma3, iSigma2]

theorem sigmaPlus_sq : sigmaPlus * sigmaPlus = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigmaPlus]

theorem sigma3_cubed : sigma3 * sigma3 * sigma3 = sigma3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigma3]

/-- The nontrivial Fibonacci sector maps to the tripotent Clifford/Witten grading. -/
theorem tau_maps_to_tripotent :
    fibSectorToAtom FibSector.tau * fibSectorToAtom FibSector.tau * fibSectorToAtom FibSector.tau =
      fibSectorToAtom FibSector.tau := by
  simpa [fibSectorToAtom] using sigma3_cubed

/-- Toy `osp(1|2) → Clifford atom` even-generator dictionary. -/
def ospEvenRotation : M2R := iSigma2

def ospEvenBoost : M2R := sigma3

def ospEvenNilpotent : M2R := sigmaPlus

/-- The even `osp(1|2)` toy generators reduce to the KAN Clifford-atom lanes. -/
theorem osp_even_to_clifford_atom_package :
    ospEvenRotation * ospEvenRotation = -(1 : M2R) ∧
    ospEvenBoost * ospEvenBoost = (1 : M2R) ∧
    ospEvenBoost * ospEvenRotation + ospEvenRotation * ospEvenBoost = (0 : M2R) ∧
    ospEvenNilpotent * ospEvenNilpotent = (0 : M2R) := by
  exact ⟨iSigma2_sq, sigma3_sq, sigma3_iSigma2_anticomm, sigmaPlus_sq⟩

/-- Compact rotation. -/
def KAtom (θ : ℝ) : M2R := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Abelian boost / local Souriau temperature lane. -/
def AAtom (α : ℝ) : M2R := !![Real.exp α, 0; 0, Real.exp (-α)]

/-- Nilpotent shear. -/
def NAtom (n : ℝ) : M2R := !![1, n; 0, 1]

/-- Atomic normal form with displayed entries: `K N A`. -/
def atomicNormalForm (θ α n : ℝ) : M2R := KAtom θ * NAtom n * AAtom α

/-- Witten supertrace. -/
def atomicSupertrace (M : M2R) : ℝ := Matrix.trace (sigma3 * M)

theorem atomicSupertrace_formula (θ α n : ℝ) :
    atomicSupertrace (atomicNormalForm θ α n) =
      2 * Real.sinh α * Real.cos θ - n * Real.exp (-α) * Real.sin θ := by
  simp [atomicSupertrace, atomicNormalForm, KAtom, NAtom, AAtom, sigma3, Matrix.trace]
  rw [Real.sinh_eq]
  ring

theorem atomicSupertrace_pure_squeeze (α : ℝ) :
    atomicSupertrace (atomicNormalForm 0 α 0) = 2 * Real.sinh α := by
  simpa using atomicSupertrace_formula 0 α 0

/-- Sum over a two-atom basis is four explicit components. -/
lemma sum_fin2_pair (f : Fin 2 × Fin 2 → ℝ) :
    (∑ x, f x) = f (0,0) + f (0,1) + f (1,0) + f (1,1) := by
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  simp [Fin.sum_univ_two, add_comm, add_left_comm, add_assoc]

/-- Kronecker/tensor product of two neighbouring atoms. -/
def kron2 (A B : M2R) : M4R :=
  fun ij kl => A ij.1 kl.1 * B ij.2 kl.2

/-- Two-atom Witten parity. -/
def twoAtomParity : M4R := kron2 sigma3 sigma3

/-- Two-atom nilpotent defect channel. -/
def twoAtomNilpotent : M4R := kron2 sigmaPlus sigmaPlus

theorem twoAtomParity_sq : twoAtomParity * twoAtomParity = (1 : M4R) := by
  ext a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    simp [twoAtomParity, kron2, sigma3, Matrix.mul_apply, sum_fin2_pair] <;> norm_num

theorem twoAtomNilpotent_sq : twoAtomNilpotent * twoAtomNilpotent = (0 : M4R) := by
  ext a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    simp [twoAtomNilpotent, kron2, sigmaPlus, Matrix.mul_apply, sum_fin2_pair] <;> norm_num

/-- Finite prime-labelled tensor approximation of the global Witten index. -/
def finitePrimeAtomIndex (S : Finset ℕ) (α : ℕ → ℝ) : ℝ :=
  ∏ p ∈ S, atomicSupertrace (atomicNormalForm 0 (α p) 0)

theorem finitePrimeAtomIndex_eq (S : Finset ℕ) (α : ℕ → ℝ) :
    finitePrimeAtomIndex S α = ∏ p ∈ S, 2 * Real.sinh (α p) := by
  unfold finitePrimeAtomIndex
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact atomicSupertrace_pure_squeeze (α p)

/-- Consolidated bridge from Fibonacci seed to Clifford atom and finite prime tensor network. -/
theorem fibonacci_clifford_bridge_synthesis :
    φ ^ 2 = φ + 1 ∧
    fibDim FibSector.tau ^ 2 = fibDim FibSector.one + fibDim FibSector.tau ∧
    fibSectorToAtom FibSector.tau * fibSectorToAtom FibSector.tau * fibSectorToAtom FibSector.tau =
      fibSectorToAtom FibSector.tau ∧
    (ospEvenRotation * ospEvenRotation = -(1 : M2R) ∧
      ospEvenBoost * ospEvenBoost = (1 : M2R) ∧
      ospEvenBoost * ospEvenRotation + ospEvenRotation * ospEvenBoost = (0 : M2R) ∧
      ospEvenNilpotent * ospEvenNilpotent = (0 : M2R)) ∧
    (∀ α, atomicSupertrace (atomicNormalForm 0 α 0) = 2 * Real.sinh α) ∧
    twoAtomParity * twoAtomParity = (1 : M4R) ∧
    twoAtomNilpotent * twoAtomNilpotent = (0 : M4R) ∧
    (∀ S α, finitePrimeAtomIndex S α = ∏ p ∈ S, 2 * Real.sinh (α p)) := by
  exact ⟨golden_identity, tau_fusion_dimension, tau_maps_to_tripotent,
    osp_even_to_clifford_atom_package, atomicSupertrace_pure_squeeze,
    twoAtomParity_sq, twoAtomNilpotent_sq, finitePrimeAtomIndex_eq⟩

end InfoGeometry.GrandUnification.FibonacciCliffordBridge

end noncomputable section