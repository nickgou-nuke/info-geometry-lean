import InfoGeometry.Canonical.FibonacciHexagonEquationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Categorical.FibonacciBraidedCategory
import InfoGeometry.Categorical.FibonacciHexagon
import InfoGeometry.Categorical.FibonacciFusionCategoryData

noncomputable section

namespace InfoGeometry.Categorical.FibonacciSymbolCoherence

open FibonacciHexagonEquationBridge
open FibonacciHexagonEquationBridge.Hexagon
open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciHexagon
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciFusionCategoryData

/-!
# Finite Fibonacci symbol coherence

This owner reuses the existing label-indexed scalar `fSymbolC`.  It does not
introduce a second fusion carrier or a second matrix presentation.  The
equation below is the multiplicity-free scalar pentagon shape; categorical
packaging on `FibHom` remains a separate naturality problem.
-/

/-- Explicit convention bridge from the legacy symbol labels to the native
categorical simple-object labels. -/
def anyonToSimple : FibonacciAnyon ≃ FibSimple where
  toFun := fun a =>
    match a with
    | FibonacciAnyon.vacuum => FibSimple.unit
    | FibonacciAnyon.tau => FibSimple.tau
  invFun := fun a =>
    match a with
    | FibSimple.unit => FibonacciAnyon.vacuum
    | FibSimple.tau => FibonacciAnyon.tau
  left_inv := by intro a; cases a <;> rfl
  right_inv := by intro a; cases a <;> rfl

theorem fusionMultiplicity_preserved
    (a b c : FibonacciAnyon) :
    FibSimple.fusionMultiplicity (anyonToSimple a) (anyonToSimple b)
        (anyonToSimple c) =
      match a, b, c with
      | FibonacciAnyon.vacuum, FibonacciAnyon.vacuum, FibonacciAnyon.vacuum => 1
      | FibonacciAnyon.vacuum, FibonacciAnyon.tau, FibonacciAnyon.tau => 1
      | FibonacciAnyon.tau, FibonacciAnyon.vacuum, FibonacciAnyon.tau => 1
      | FibonacciAnyon.tau, FibonacciAnyon.tau, FibonacciAnyon.vacuum => 1
      | FibonacciAnyon.tau, FibonacciAnyon.tau, FibonacciAnyon.tau => 1
      | _, _, _ => 0 := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The existing scalar symbol readout, transported to the native categorical
label type. -/
def nativeFSymbol (a b c d e f : FibSimple) : ℂ :=
  fSymbolC (anyonToSimple.symm a) (anyonToSimple.symm b)
    (anyonToSimple.symm c) (anyonToSimple.symm d)
    (anyonToSimple.symm e) (anyonToSimple.symm f)

/-- Parametric native Fibonacci `F`-symbol convention.  The four nontrivial
entries are the existing fusion matrix entries; all unit channels retain the
existing normalized admissibility cases. -/
def parametricFSymbol (τ s : ℂ) (a b c d e f : FibSimple) : ℂ :=
  match a, b, c, d, e, f with
  | .tau, .tau, .tau, .tau, .unit, .unit => τ
  | .tau, .tau, .tau, .tau, .unit, .tau => s
  | .tau, .tau, .tau, .tau, .tau, .unit => s
  | .tau, .tau, .tau, .tau, .tau, .tau => -τ
  | .unit, b, c, d, e, f => if e = b ∧ f = d ∧ c = d then 1 else 0
  | a, .unit, c, d, e, f => if e = a ∧ f = c ∧ a = e then 1 else 0
  | a, b, .unit, d, e, f => if e = d ∧ f = b ∧ a = e then 1 else 0
  | _, _, _, _, _, _ => 0

/-- Explicit matrix carrier for the two-dimensional nontrivial Fibonacci
fusion block. -/
noncomputable def parametricFTauMatrix (τ s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    parametricFSymbol τ s FibSimple.tau FibSimple.tau FibSimple.tau
      FibSimple.tau (if i = 0 then FibSimple.unit else FibSimple.tau)
      (if j = 0 then FibSimple.unit else FibSimple.tau)

theorem parametricFTauMatrix_eq_fibonacciFusionMatrix (τ s : ℂ) :
    parametricFTauMatrix τ s = fibonacciFusionMatrix τ s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [parametricFTauMatrix, parametricFSymbol, fibonacciFusionMatrix]

theorem parametricFTauMatrix_sq
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    parametricFTauMatrix τ s * parametricFTauMatrix τ s = 1 := by
  rw [parametricFTauMatrix_eq_fibonacciFusionMatrix]
  exact fibonacciFusionMatrix_sq hs hτ

theorem parametricFTauMatrix_kron_identity_sq
    (n : ℕ) (τ s : ℂ) (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    kron (parametricFTauMatrix τ s)
        (1 : Matrix (Fin n) (Fin n) ℂ) *
      kron (parametricFTauMatrix τ s)
        (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [← kron_mul]
  rw [parametricFTauMatrix_sq τ s hs hτ]
  simp [kron]

/-! The external multiplicity action commutes with the Fibonacci block. -/

theorem kron_identity_commutes_kron_identity
    (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) :
    kron (1 : Matrix (Fin 2) (Fin 2) ℂ) K *
        kron A (1 : Matrix (Fin n) (Fin n) ℂ) =
      kron A (1 : Matrix (Fin n) (Fin n) ℂ) *
        kron (1 : Matrix (Fin 2) (Fin 2) ℂ) K := by
  rw [← kron_mul, ← kron_mul]
  simp

theorem kron_structural_multiplicity_commute
    {n m : ℕ}
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (K : Matrix (Fin n) (Fin m) ℂ) :
    kron (1 : Matrix (Fin 2) (Fin 2) ℂ) K *
        kron A (1 : Matrix (Fin m) (Fin m) ℂ) =
      kron A (1 : Matrix (Fin n) (Fin n) ℂ) *
        kron (1 : Matrix (Fin 2) (Fin 2) ℂ) K := by
  rw [← kron_mul, ← kron_mul]
  simp

/-! The actual multiplicity block used by a global τ-output associator. -/

noncomputable def globalTauFusionBlock (n : ℕ) (τ s : ℂ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  kron (parametricFTauMatrix τ s) (1 : Matrix (Fin n) (Fin n) ℂ)

theorem globalTauFusionBlock_sq
    (n : ℕ) (τ s : ℂ) (hs : s ^ 2 = τ)
    (hτ : τ ^ 2 + τ = 1) :
    globalTauFusionBlock n τ s * globalTauFusionBlock n τ s = 1 := by
  exact parametricFTauMatrix_kron_identity_sq n τ s hs hτ

theorem parametricFSymbol_tau_block
    (τ s : ℂ) :
    (fun i j : Fin 2 =>
      parametricFSymbol τ s FibSimple.tau FibSimple.tau FibSimple.tau
        FibSimple.tau (if i = 0 then FibSimple.unit else FibSimple.tau)
        (if j = 0 then FibSimple.unit else FibSimple.tau)) =
      fibonacciFusionMatrix τ s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [parametricFSymbol, fibonacciFusionMatrix]

/-- The multiplicity-free scalar `R`-symbol convention used by the existing
finite Fibonacci matrix: the two nontrivial `τ ⊗ τ` channels carry the two
diagonal phases, while the unit channels are normalized to one. -/
def nativeRSymbol (q : Units ℂ) (a b c : FibSimple) : ℂ :=
  match a, b, c with
  | FibSimple.tau, FibSimple.tau, FibSimple.unit => (q ^ (-4 : ℤ) : ℂ)
  | FibSimple.tau, FibSimple.tau, FibSimple.tau => (q : ℂ) ^ 3
  | _, _, _ => 1

/-- The two-channel matrix readout of the native scalar `R` symbols. -/
def nativeRMatrix (q : Units ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![nativeRSymbol q FibSimple.tau FibSimple.tau FibSimple.unit, 0;
     0, nativeRSymbol q FibSimple.tau FibSimple.tau FibSimple.tau]

theorem nativeRMatrix_eq_fibonacciRMatrix (q : Units ℂ) :
    nativeRMatrix q = fibonacciRMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nativeRMatrix, nativeRSymbol, fibonacciRMatrix]
  · rfl

theorem native_symbol_hexagon_forward
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    fibonacciBMatrix q τ s * nativeRMatrix q * fibonacciBMatrix q τ s =
      nativeRMatrix q * fibonacciBMatrix q τ s * nativeRMatrix q := by
  rw [nativeRMatrix_eq_fibonacciRMatrix]
  exact fibonacci_hexagon_coherence q τ s
    hq_inv hq_pow3 hq5 h_poly hτ hs

theorem native_symbol_hexagon_reverse
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    nativeRMatrix q * fibonacciBMatrix q τ s * nativeRMatrix q =
      fibonacciBMatrix q τ s * nativeRMatrix q * fibonacciBMatrix q τ s := by
  exact (native_symbol_hexagon_forward q τ s hq_inv hq_pow3 hq5 h_poly hτ hs).symm

theorem nativeRSymbol_inverse (q : Units ℂ) (a b c : FibSimple) :
    nativeRSymbol q a b c * nativeRSymbol q⁻¹ a b c = 1 := by
  cases a <;> cases b <;> cases c <;>
    simp [nativeRSymbol, zpow_neg, Units.ne_zero q]
  · exact inv_mul_cancel₀ (pow_ne_zero 4 (Units.ne_zero q))

def nativePentagonLHS
    (a b c d e f g k l : FibSimple) : ℂ :=
  nativeFSymbol f c d e g l * nativeFSymbol a b l e f k

def nativePentagonRHS
    (a b c d e f g k l : FibSimple) : ℂ :=
  (nativeFSymbol a b c g f FibSimple.unit *
      nativeFSymbol a FibSimple.unit d e g k *
      nativeFSymbol b c d k FibSimple.unit l) +
    (nativeFSymbol a b c g f FibSimple.tau *
      nativeFSymbol a FibSimple.tau d e g k *
      nativeFSymbol b c d k FibSimple.tau l)

theorem native_pentagon_vacuum_boundary
    (a b c d e f g k l : FibSimple)
    (ha : a = FibSimple.unit)
    (hb : b = FibSimple.unit)
    (hc : c = FibSimple.unit)
    :
    nativePentagonLHS a b c d e f g k l =
      nativePentagonRHS a b c d e f g k l := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    cases f <;> cases g <;> cases k <;> cases l <;>
    simp_all [nativePentagonLHS, nativePentagonRHS, nativeFSymbol,
      anyonToSimple, fSymbolC]

theorem parametric_pentagon_vacuum_boundary
    (τ s : ℂ) (a b c d e f g k l : FibSimple)
    (ha : a = FibSimple.unit)
    (hb : b = FibSimple.unit)
    (hc : c = FibSimple.unit) :
    (parametricFSymbol τ s f c d e g l *
        parametricFSymbol τ s a b l e f k) =
      (parametricFSymbol τ s a b c g f FibSimple.unit *
          parametricFSymbol τ s a FibSimple.unit d e g k *
          parametricFSymbol τ s b c d k FibSimple.unit l) +
        (parametricFSymbol τ s a b c g f FibSimple.tau *
          parametricFSymbol τ s a FibSimple.tau d e g k *
          parametricFSymbol τ s b c d k FibSimple.tau l) := by
  subst a
  subst b
  subst c
  cases d <;> cases e <;> cases f <;> cases g <;> cases k <;> cases l <;>
    simp [parametricFSymbol]

def pentagonLHS (a b c d e f g k l : FibonacciAnyon) : ℂ :=
  fSymbolC f c d e g l * fSymbolC a b l e f k

def pentagonRHS (a b c d e f g k l : FibonacciAnyon) : ℂ :=
  (fSymbolC a b c g f FibonacciAnyon.vacuum *
      fSymbolC a FibonacciAnyon.vacuum d e g k *
      fSymbolC b c d k FibonacciAnyon.vacuum l) +
    (fSymbolC a b c g f FibonacciAnyon.tau *
      fSymbolC a FibonacciAnyon.tau d e g k *
      fSymbolC b c d k FibonacciAnyon.tau l)

theorem pentagon_scalar_vacuum_boundary
    (a b c d e f g k l : FibonacciAnyon)
    (ha : a = FibonacciAnyon.vacuum)
    (hb : b = FibonacciAnyon.vacuum)
    (hc : c = FibonacciAnyon.vacuum) :
    pentagonLHS a b c d e f g k l =
      pentagonRHS a b c d e f g k l := by
  subst a
  subst b
  subst c
  cases d <;> cases e <;> cases f <;> cases g <;> cases k <;> cases l <;>
    simp [pentagonLHS, pentagonRHS, fSymbolC]

end InfoGeometry.Categorical.FibonacciSymbolCoherence
