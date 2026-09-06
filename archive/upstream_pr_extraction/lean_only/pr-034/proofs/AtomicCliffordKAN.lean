import Mathlib

/-!
# Atomic Clifford KAN/Witten Calculation

A finite `2 × 2` real matrix realization of the local `Cl(1,1)` atom:
rotation `K`, boost `A`, nilpotent shear `N`, chiral grading `σ₃`, and the
atomic Witten/supertrace.
-/

noncomputable section

open Matrix Real
open scoped BigOperators

namespace InfoGeometry.GrandUnification.AtomicCliffordKAN

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Chiral grading / parity operator; this is the `e₁` generator of the atom. -/
def sigma3 : M2R := !![1, 0; 0, -1]

/-- Real representative of `iσ₂`; this is the `e₂` generator with square `-1`. -/
def iSigma2 : M2R := !![0, 1; -1, 0]

/-- Nilpotent raising/shear generator. -/
def sigmaPlus : M2R := !![0, 1; 0, 0]

/-- Positive chirality projector. -/
def Pplus : M2R := (1 / 2 : ℝ) • ((1 : M2R) + sigma3)

/-- Negative chirality projector. -/
def Pminus : M2R := (1 / 2 : ℝ) • ((1 : M2R) - sigma3)

/-- Drazin/null projector for the invertible Clifford atom; it vanishes until the singular boundary is added. -/
def Pzero : M2R := (1 : M2R) - sigma3 * sigma3

/-- Compact real rotation. -/
def KAtom (θ : ℝ) : M2R :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Abelian Souriau boost. -/
def AAtom (α : ℝ) : M2R :=
  !![Real.exp α, 0; 0, Real.exp (-α)]

/-- Nilpotent shear. -/
def NAtom (n : ℝ) : M2R :=
  !![1, n; 0, 1]

/-- Atomic normal form matching the supertrace formula in the note: `K N A`. -/
def atomicNormalForm (θ α n : ℝ) : M2R :=
  KAtom θ * NAtom n * AAtom α

/-- Witten supertrace with chiral grading `σ₃`. -/
def atomicSupertrace (M : M2R) : ℝ :=
  Matrix.trace (sigma3 * M)

/-- The nilpotent generator squares to zero. -/
theorem sigmaPlus_sq : sigmaPlus * sigmaPlus = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigmaPlus]

/-- First Clifford relation: `e₁² = +1`. -/
theorem sigma3_sq : sigma3 * sigma3 = (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigma3]

/-- Second Clifford relation: `e₂² = -1`. -/
theorem iSigma2_sq : iSigma2 * iSigma2 = -(1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [iSigma2]

/-- Clifford anticommutation relation `{e₁,e₂}=0`. -/
theorem sigma3_iSigma2_anticomm : sigma3 * iSigma2 + iSigma2 * sigma3 = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigma3, iSigma2]

/-- The chiral grading is tripotent, the local `OP³ = OP` atom. -/
theorem sigma3_cubed : sigma3 * sigma3 * sigma3 = sigma3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [sigma3]

/-- The invertible Clifford atom has no Drazin-null component. -/
theorem Pzero_eq_zero : Pzero = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Pzero, sigma3]

/-- Explicit positive chirality projection. -/
theorem Pplus_eq : Pplus = !![1, 0; 0, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Pplus, sigma3] <;> norm_num

/-- Explicit negative chirality projection. -/
theorem Pminus_eq : Pminus = !![0, 0; 0, 1] := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Pminus, sigma3] <;> norm_num

/-- Explicit atomic normal form. -/
theorem atomicNormalForm_eq (θ α n : ℝ) :
    atomicNormalForm θ α n =
      !![Real.exp α * Real.cos θ,
         Real.exp (-α) * (n * Real.cos θ - Real.sin θ);
         Real.exp α * Real.sin θ,
         Real.exp (-α) * (n * Real.sin θ + Real.cos θ)] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [atomicNormalForm, KAtom, NAtom, AAtom] <;> ring

/-- Closed formula for the local Witten index `Tr(σ₃ K N A)`. -/
theorem atomicSupertrace_formula (θ α n : ℝ) :
    atomicSupertrace (atomicNormalForm θ α n) =
      2 * Real.sinh α * Real.cos θ - n * Real.exp (-α) * Real.sin θ := by
  rw [atomicSupertrace, atomicNormalForm_eq]
  simp [sigma3, Matrix.trace]
  rw [Real.sinh_eq]
  ring

/-- Pure squeeze limit: `K = I`, `N = I`, so the atom gives `2 sinh α`. -/
theorem atomicSupertrace_pure_squeeze (α : ℝ) :
    atomicSupertrace (atomicNormalForm 0 α 0) = 2 * Real.sinh α := by
  simpa using atomicSupertrace_formula 0 α 0

/-- Traceless Pauli-split matrix in the real split lane. -/
def tracelessSplit (p w z : ℝ) : M2R :=
  !![z, p + w; w - p, -z]

/-- The split determinant is the light-cone quadratic form. -/
theorem tracelessSplit_det (p w z : ℝ) :
    (tracelessSplit p w z).det = p ^ 2 - w ^ 2 - z ^ 2 := by
  simp [tracelessSplit, Matrix.det_fin_two]
  ring

/-- The chiral supertrace extracts only the `σ₃`/boost coefficient. -/
theorem atomicSupertrace_tracelessSplit (p w z : ℝ) :
    atomicSupertrace (tracelessSplit p w z) = 2 * z := by
  simp [atomicSupertrace, tracelessSplit, sigma3, Matrix.trace]
  ring

/-- Full split paravector: scalar slot plus the traceless Clifford atom. -/
def paravectorSplit (t p w z : ℝ) : M2R :=
  !![t + z, p + w; w - p, t - z]

/-- Determinant of the full split paravector: the chiral light-cone quadratic form. -/
theorem paravectorSplit_det (t p w z : ℝ) :
    (paravectorSplit t p w z).det = t ^ 2 + p ^ 2 - w ^ 2 - z ^ 2 := by
  simp [paravectorSplit, Matrix.det_fin_two]
  ring

/-- The null-boundary predicate for the local atom. -/
def onChiralLightCone (t p w z : ℝ) : Prop :=
  (paravectorSplit t p w z).det = 0

/-- Coordinate form of the light-cone boundary. -/
theorem onChiralLightCone_iff (t p w z : ℝ) :
    onChiralLightCone t p w z ↔ t ^ 2 + p ^ 2 = w ^ 2 + z ^ 2 := by
  unfold onChiralLightCone
  rw [paravectorSplit_det]
  constructor <;> intro h <;> nlinarith

/-- Finite prime-labelled tensor approximation of the global Witten index. -/
def finiteBulkWittenIndex (S : Finset ℕ) (α : ℕ → ℝ) : ℝ :=
  ∏ p ∈ S, atomicSupertrace (atomicNormalForm 0 (α p) 0)

/-- Finite product is exactly the product of the local pure-squeeze atom indices. -/
theorem finiteBulkWittenIndex_eq (S : Finset ℕ) (α : ℕ → ℝ) :
    finiteBulkWittenIndex S α = ∏ p ∈ S, 2 * Real.sinh (α p) := by
  unfold finiteBulkWittenIndex
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact atomicSupertrace_pure_squeeze (α p)

/-- Adding one prime/mode multiplies the finite tensor-network index by one more atom. -/
theorem finiteBulkWittenIndex_insert {S : Finset ℕ} {p : ℕ} (hp : p ∉ S) (α : ℕ → ℝ) :
    finiteBulkWittenIndex (insert p S) α =
      (2 * Real.sinh (α p)) * finiteBulkWittenIndex S α := by
  rw [finiteBulkWittenIndex_eq, Finset.prod_insert hp, finiteBulkWittenIndex_eq]

/-- Consolidated finite Clifford-atom package. -/
theorem atomic_clifford_kan_synthesis :
    sigmaPlus * sigmaPlus = (0 : M2R) ∧
    sigma3 * sigma3 = (1 : M2R) ∧
    iSigma2 * iSigma2 = -(1 : M2R) ∧
    sigma3 * iSigma2 + iSigma2 * sigma3 = (0 : M2R) ∧
    sigma3 * sigma3 * sigma3 = sigma3 ∧
    Pzero = (0 : M2R) ∧
    (∀ θ α n, atomicSupertrace (atomicNormalForm θ α n) =
      2 * Real.sinh α * Real.cos θ - n * Real.exp (-α) * Real.sin θ) ∧
    (∀ α, atomicSupertrace (atomicNormalForm 0 α 0) = 2 * Real.sinh α) ∧
    (∀ p w z, (tracelessSplit p w z).det = p ^ 2 - w ^ 2 - z ^ 2) ∧
    (∀ p w z, atomicSupertrace (tracelessSplit p w z) = 2 * z) ∧
    (∀ t p w z, (paravectorSplit t p w z).det = t ^ 2 + p ^ 2 - w ^ 2 - z ^ 2) ∧
    (∀ t p w z, onChiralLightCone t p w z ↔ t ^ 2 + p ^ 2 = w ^ 2 + z ^ 2) ∧
    (∀ S α, finiteBulkWittenIndex S α = ∏ p ∈ S, 2 * Real.sinh (α p)) := by
  exact ⟨sigmaPlus_sq, sigma3_sq, iSigma2_sq, sigma3_iSigma2_anticomm,
    sigma3_cubed, Pzero_eq_zero, atomicSupertrace_formula,
    atomicSupertrace_pure_squeeze, tracelessSplit_det,
    atomicSupertrace_tracelessSplit, paravectorSplit_det,
    onChiralLightCone_iff, finiteBulkWittenIndex_eq⟩

end InfoGeometry.GrandUnification.AtomicCliffordKAN
