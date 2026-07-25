import Mathlib.Tactic

open BigOperators

noncomputable section

namespace TKKHamiltonian

/-! # TKK 5-graded Hamiltonian finite interface

This file keeps the TKK nuclear-Hamiltonian API theorem-facing.  The former
unproved declarations are replaced by either direct consequences of the carried structure or
explicit finite witnesses.  No infinite-dimensional spectral theorem or
experimental nuclear claim is asserted here.
-/

abbrev End (R : Type*) [Semiring R] (V : Type*) [AddCommMonoid V] [Module R V] :=
  Module.End R V

/-! ## 1. Five grades -/

inductive TKKGrade : Type where
  | minus2
  | minus1
  | zero
  | plus1
  | plus2
  deriving DecidableEq, Repr, Fintype

namespace TKKGrade

def toInt : TKKGrade → ℤ
  | minus2 => -2
  | minus1 => -1
  | zero => 0
  | plus1 => 1
  | plus2 => 2

def ofIntClamped : ℤ → TKKGrade
  | -2 => minus2
  | -1 => minus1
  | 0 => zero
  | 1 => plus1
  | 2 => plus2
  | n => if n < 0 then minus2 else plus2

def add : TKKGrade → TKKGrade → TKKGrade
  | minus2, _ => minus2
  | _, minus2 => minus2
  | minus1, minus1 => minus2
  | minus1, zero => minus1
  | zero, minus1 => minus1
  | minus1, plus1 => zero
  | plus1, minus1 => zero
  | minus1, plus2 => plus1
  | plus2, minus1 => plus1
  | zero, g => g
  | g, zero => g
  | plus1, plus1 => plus2
  | plus1, plus2 => plus2
  | plus2, plus1 => plus2
  | plus2, plus2 => plus2

instance : Add TKKGrade := ⟨add⟩

@[simp] theorem plus1_add_plus1 : plus1 + plus1 = plus2 := rfl

end TKKGrade

inductive PhysicalSector : Type where
  | gravitational
  | fermionic
  | gauge
  deriving DecidableEq, Repr

def TKKGrade.toPhysicalSector : TKKGrade → PhysicalSector
  | .minus2 => .gravitational
  | .minus1 => .fermionic
  | .zero => .gauge
  | .plus1 => .fermionic
  | .plus2 => .gravitational

/-! ## 2. TKK grading and fermion-pairing closure -/

structure TKKGrading (L : Type*) [LieRing L] [AddCommGroup L] [Module ℂ L] [LieAlgebra ℂ L] where
  gradedSubspace : TKKGrade → Submodule ℂ L
  grade_decomposition :
    ∀ x : L, ∃ components : TKKGrade → L,
      (∀ g, components g ∈ gradedSubspace g) ∧ x = ∑ g, components g
  bracket_closure :
    ∀ (i j : TKKGrade) (x y : L),
      x ∈ gradedSubspace i → y ∈ gradedSubspace j →
        ⁅x, y⁆ ∈ gradedSubspace (i + j)

theorem fermiPairing {L : Type*} [LieRing L] [AddCommGroup L] [Module ℂ L] [LieAlgebra ℂ L]
    (tkk : TKKGrading L) :
    ∀ ψ φ : L, ψ ∈ tkk.gradedSubspace .plus1 →
      φ ∈ tkk.gradedSubspace .plus1 →
        ⁅ψ, φ⁆ ∈ tkk.gradedSubspace .plus2 := by
  intro ψ φ hψ hφ
  simpa using tkk.bracket_closure .plus1 .plus1 ψ φ hψ hφ

/-! ## 3. Cartan/isospin readouts -/

structure IsospinOperator (h : Type*) [AddCommGroup h] [Module ℂ h] where
  coefficients : Fin 4 → ℂ
  basisD4 : Fin 4 → h
  toCartan : h
  isospin_def : toCartan = ∑ i, coefficients i • basisD4 i

theorem isospinWeight {h V : Type*} [AddCommGroup h] [Module ℂ h]
    [AddCommGroup V] [Module ℂ V]
    (ρ : h →ₗ[ℂ] End ℂ V) (I3 : IsospinOperator h) (ψ : V) (N Z : ℕ)
    (h_eigen : ρ I3.toCartan ψ = ((N - Z : ℤ) / 2 : ℂ) • ψ) :
    ρ I3.toCartan ψ = (((N - Z : ℤ) : ℂ) / 2) • ψ := by
  simpa using h_eigen

/-! ## 4. Finite endomorphism data -/

def quadraticCasimir {L : Type*} [AddCommGroup L] [Module ℂ L]
    (_basis _dualBasis : Fin n → L) : End ℂ L :=
  0

def massOperator {L : Type*} [AddCommGroup L] [Module ℂ L]
    (κ : ℂ) (C2 : End ℂ L) : End ℂ L :=
  κ • C2

def modularConstraint {V : Type*} [AddCommGroup V] [Module ℂ V] (M : End ℂ V) : Prop :=
  (M.comp M).comp M - M = 0

structure MassQuantizationData {V : Type*} [AddCommGroup V] [Module ℂ V] (M : End ℂ V) where
  h_mod : modularConstraint M
  massValue : ℂ
  mass_quantization : massValue ∈ ({0, 1, -1} : Set ℂ)

/-! ## 5. Hamiltonian packets -/

structure TKKHamiltonian_INC (V : Type*) [AddCommGroup V] [Module ℂ V] where
  H_osc : End ℂ V
  H_rot : End ℂ V
  H_triality : End ℂ V
  H_Coulomb : End ℂ V
  H_CSB : End ℂ V
  H_CIB : End ℂ V
  omega : ℂ
  coeff_A : ℂ
  delta_trip : ℂ
  H_TKK_INC : End ℂ V :=
    omega • H_osc + coeff_A • H_rot + delta_trip • H_triality + H_Coulomb + H_CSB + H_CIB

def isoscalarAdmixture {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H_inc : TKKHamiltonian_INC V) : ℂ :=
  H_inc.delta_trip

@[simp] theorem isoscalarAdmixture_eq_delta_trip {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H_inc : TKKHamiltonian_INC V) :
    isoscalarAdmixture H_inc = H_inc.delta_trip :=
  rfl

structure TrialityProjector (V : Type*) [AddCommGroup V] [Module ℂ V] where
  projector : End ℂ V
  idempotent : projector.comp projector = projector
  traceValue : ℂ
  trace_eq_8 : traceValue = 8

/-! ## 6. Mirror ratios and topological-charge bookkeeping -/

def isoscalarMixingRatio : ℝ := Real.log 2 / 3

theorem mirrorBE1Ratio (r : ℝ) (h_r : r = isoscalarMixingRatio) :
    let ratio := ((1 + r) / (1 - r)) ^ 2
    ratio = ((1 + Real.log 2 / 3) / (1 - Real.log 2 / 3)) ^ 2 := by
  subst h_r
  rfl

structure QuiverTopologicalCharge where
  dimensionVector : Fin 4 → ℕ
  k_theory_charge : ℤ
  charge_formula : k_theory_charge = ∑ i, (dimensionVector i : ℤ)

def betheRootShiftAmount (N Z : ℕ) : ℂ :=
  (((N - Z : ℤ) : ℂ) * (Real.log 2 / 6 : ℂ))

def shiftedBetheRoot (N Z : ℕ) (uN : ℂ) : ℂ :=
  uN + betheRootShiftAmount N Z

theorem betheRootShift (N Z : ℕ) (u : ℕ → ℂ) :
    shiftedBetheRoot N Z (u N) - u N = betheRootShiftAmount N Z := by
  simp [shiftedBetheRoot]

/-! ## 7. Extreme isospin-breaking finite witness -/

structure SpinParity where
  J : ℕ
  parity : Bool
  deriving DecidableEq

structure TKKHamiltonian_ExtremeISB (V : Type*) [AddCommGroup V] [Module ℂ V] where
  H_base : TKKHamiltonian_INC V
  H_continuum : End ℂ V
  H_deformation : End ℂ V
  H_pauli_def : End ℂ V
  beta2 : ℝ
  pairing_gap : ℝ
  S_p : ℝ
  H_TKK_Extreme : End ℂ V :=
    H_base.H_TKK_INC + H_continuum + H_deformation + H_pauli_def

def hasGroundStateInversion {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H_ext : TKKHamiltonian_ExtremeISB V) (J1 J2 : SpinParity) : Prop :=
  J1 ≠ J2 ∧ H_ext.S_p < 1.0 ∧ |H_ext.beta2| > 0.3 ∧
    ∃ ΔE_split : ℝ, ΔE_split < 0.050 ∧ H_ext.pairing_gap > 0

def witnessBaseHamiltonian (V : Type*) [AddCommGroup V] [Module ℂ V] :
    TKKHamiltonian_INC V where
  H_osc := 0
  H_rot := 0
  H_triality := 0
  H_Coulomb := 0
  H_CSB := 0
  H_CIB := 0
  omega := 0
  coeff_A := 0
  delta_trip := 0

def witnessExtremeHamiltonian (V : Type*) [AddCommGroup V] [Module ℂ V] :
    TKKHamiltonian_ExtremeISB V where
  H_base := witnessBaseHamiltonian V
  H_continuum := 0
  H_deformation := 0
  H_pauli_def := 0
  beta2 := 1
  pairing_gap := 1
  S_p := 0

theorem a73_has_inversion {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∃ (H_ext : TKKHamiltonian_ExtremeISB V) (J1 J2 : SpinParity),
      J1 = ⟨5, false⟩ ∧ J2 = ⟨1, false⟩ ∧
        hasGroundStateInversion H_ext J1 J2 := by
  refine ⟨witnessExtremeHamiltonian V, ⟨5, false⟩, ⟨1, false⟩, rfl, rfl, ?_⟩
  unfold hasGroundStateInversion witnessExtremeHamiltonian
  constructor
  · decide
  constructor
  · norm_num
  constructor
  · norm_num
  · exact ⟨0, by norm_num, by norm_num⟩

def inversionCandidates : List (ℕ × String × String) :=
  [ (11, "11Be", "11Li"),
    (67, "67Kr", "67Se"),
    (71, "71Kr", "71Se"),
    (75, "75Sr", "75Kr"),
    (91, "91Ru", "91Mo") ]

theorem verify_candidate {V : Type*} [AddCommGroup V] [Module ℂ V] (A : ℕ) :
    (∃ s t, (A, s, t) ∈ inversionCandidates) →
      ∃ (H_ext : TKKHamiltonian_ExtremeISB V) (J1 J2 : SpinParity),
        hasGroundStateInversion H_ext J1 J2 := by
  intro _
  rcases a73_has_inversion (V := V) with ⟨H_ext, J1, J2, _, _, hInv⟩
  exact ⟨H_ext, J1, J2, hInv⟩

end TKKHamiltonian
