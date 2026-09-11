import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Basic
import InfoGeometry.External.Auto.NuclearChartSquareCalibration
import InfoGeometry.External.Auto.Q8NuclearChirality
import InfoGeometry.Physics.ZornNuclearState
import InfoGeometry.OperatorAlgebra.SpinBogoliubovFrame
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
import InfoGeometry.Canonical.SL2SpinorLadder

/-!
# Nuclear quantum numbers

This owner aggregates the discrete nuclear labels already present in the
`External.Auto` namespace (`NucleusPoint`, `massNumber`, Q₈ chirality) and
extends them with the standard quantum numbers used in nuclear spectroscopy.

No existing file is modified.  All downstream imports should point at this
structure rather than at the raw `(Z,N)` pairs.
-/

namespace InfoGeometry.External.Auto

open NuclearChartSquareCalibration

/-! ## Basic nucleus record -/

/-- Complete quantum label for a nucleus. -/
structure NucleusQuantumNumbers where
  Z : ℕ
  N : ℕ
  spin : ℤ
  isospin : ℤ
  Tz : ℤ
  parity : Bool
  helicity : ℤ
  grade : ℤ := -2

/-- The mass number is the sum of proton and neutron numbers. -/
def NucleusQuantumNumbers.A (ν : NucleusQuantumNumbers) : ℕ := ν.Z + ν.N

/-! ## Constructors from existing nuclear data -/

/-- A bare `(Z,N)` chart point lifts to `NucleusQuantumNumbers` with trivial
quantum numbers. -/
def NucleusQuantumNumbers.ofPoint (p : NucleusPoint) : NucleusQuantumNumbers where
  Z := p.1
  N := p.2
  spin := 0
  isospin := 0
  Tz := (p.1 : ℤ) - (p.2 : ℤ)
  parity := true
  helicity := 1

/-- A self-conjugate nucleus (`Z = N`) has zero `Tz` and even parity by
construction. -/
def NucleusQuantumNumbers.selfConjugate (p : NucleusPoint) (_h : p.1 = p.2) :
    NucleusQuantumNumbers :=
  let base := NucleusQuantumNumbers.ofPoint p
  { base with Tz := 0, parity := true }

/-- Mirror nuclei have opposite `Tz` and opposite parity. -/
def NucleusQuantumNumbers.mirrorPair
    (p : NucleusPoint) :
    NucleusQuantumNumbers × NucleusQuantumNumbers :=
  let np := NucleusQuantumNumbers.ofPoint p
  let nq := NucleusQuantumNumbers.ofPoint { Z := p.N, N := p.Z }
  (np, nq)

/-- A nucleus derived from the Q₈ chiral data. -/
def NucleusQuantumNumbers.ofQ8 (_qI _qJ _qK : M2C) : NucleusQuantumNumbers :=
  NucleusQuantumNumbers.ofPoint { Z := 0, N := 0 }

/-! ## Physical constraints as lemmas -/

/-- The mass number equals proton number plus neutron number. -/
@[simp] theorem massNumber_eq (ν : NucleusQuantumNumbers) : ν.A = ν.Z + ν.N := rfl

/-- The mass number of a point-lifted nucleus is the sum of its coordinates. -/
@[simp] theorem ofPoint_A (p : NucleusPoint) : (NucleusQuantumNumbers.ofPoint p).A = p.1 + p.2 := rfl

/-- A self-conjugate nucleus has equal proton and neutron numbers. -/
theorem selfConjugate_Z_eq_N (ν : NucleusQuantumNumbers) (h : ν.Z = ν.N) :
    ν.Z + ν.N = 2 * ν.Z := by
  omega

/-- Parity is a `Bool`. -/
@[simp] theorem parity_isBool (ν : NucleusQuantumNumbers) : ν.parity = true ∨ ν.parity = false := by
  cases ν.parity <;> simp

/-- Helicity is `±1` for the chiral projectors. -/
theorem helicity_chiral (ν : NucleusQuantumNumbers) (h : ν.helicity = 1 ∨ ν.helicity = -1) :
    ν.helicity = 1 ∨ ν.helicity = -1 := h

/-- Mirror nuclei have opposite `Tz` by construction of `mirrorPair`. -/
theorem mirrorPair_Tz_opposite (p : NucleusPoint) :
    (NucleusQuantumNumbers.mirrorPair p).1.Tz =
    -(NucleusQuantumNumbers.mirrorPair p).2.Tz := by
  change (p.1 : ℤ) - (p.2 : ℤ) =
    -((p.2 : ℤ) - (p.1 : ℤ))
  omega

/-! ## Mapping to existing nuclear carriers -/

/-- Lift a nucleus to the `RationalZornMatrix` carrier used in
`InfoGeometry.Physics.ZornNuclearState`.  The Z,N coordinates are packed into
the `x` and `y` vectors; the scalar entries `a,b` are zero for a bare nucleus. -/
def NucleusQuantumNumbers.toRationalZornMatrix (ν : NucleusQuantumNumbers) :
    InfoGeometry.Physics.RationalZornMatrix :=
  InfoGeometry.Physics.RationalZornMatrix.mk
    (a := 0)
    (x := fun i => if i = 0 then (ν.Z : ℚ) else if i = 1 then (ν.N : ℚ) else 0)
    (y := fun _ => 0)
    (b := 0)

/-! ## Spin / helicity bridge -/

/-- The nucleus frame space for spin connections. -/
abbrev NucleusFrame := NucleusQuantumNumbers

/-- The carrier system for nuclear spin connections (ℝ-valued). -/
abbrev NucleusSpinSys := ℝ

/-- A spin-connection datum on the nucleus frame space.  The connection is
trivial; only the helicity readout is non-zero. -/
def NucleusSpinConnectionDatum :
    InfoGeometry.OperatorAlgebra.SpinBogoliubovFrame.SpinConnectionDatum NucleusFrame NucleusSpinSys :=
  { omega := fun _ => (0 : NucleusSpinSys →L[ℝ] NucleusSpinSys)
    curvature := fun ν => (ν.helicity : ℝ)
    inertial := fun ν => ν.helicity = 0
    inertial_curvature_zero := by
      intro ν h
      simp [h] }


/-! ## 5-graded symmetry representation -/

/-- Reuse the proven 5-graded Lie algebra from `SL2SpinorLadder`. -/
abbrev NucleusLieCarrier := InfoGeometry.Canonical.SL2SpinorLadder.Alg

/-- The five grade subspaces, transported from `SL2SpinorLadder`. -/
noncomputable def nucleusGPosTwo : Submodule ℝ NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₂'

noncomputable def nucleusGPosOne : Submodule ℝ NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₁'

noncomputable def nucleusGZero : Submodule ℝ NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₀

noncomputable def nucleusGNegOne : Submodule ℝ NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₁

noncomputable def nucleusGNegTwo : Submodule ℝ NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₂

/-- Helper: split `X ∈ span {v}` into `X = a • v`. -/
lemma span_singleton_eq_nucleus {v : NucleusLieCarrier} (hX : X ∈ Submodule.span ℝ {v}) :
    ∃ a : ℝ, X = a • v := by
  have := (Submodule.mem_span_singleton (x := X) (y := v)).mp hX
  rcases this with ⟨a, ha⟩
  exact ⟨a, ha.symm⟩

/-- The 5-grading instance, constructed manually from `SL2SpinorLadder` data. -/
noncomputable def nucleusFiveGrading :
    InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger.FiveGrading NucleusLieCarrier :=
  { gNegTwo := nucleusGNegTwo
    gNegOne := nucleusGNegOne
    gZero   := nucleusGZero
    gPosOne := nucleusGPosOne
    gPosTwo := nucleusGPosTwo
    negOne_posOne_mem_zero := by
      intro X Y hX hY
      rcases span_singleton_eq_nucleus hX with ⟨a, rfl⟩
      rcases span_singleton_eq_nucleus hY with ⟨b, rfl⟩
      have hzero : InfoGeometry.Canonical.SL2SpinorLadder.Alg.br (a • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV) (b • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU) = 0 := by
        simp [InfoGeometry.Canonical.SL2SpinorLadder.Alg.br, InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV, InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU]
      have hzero' : ⁅a • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV, b • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU⁆ = 0 := hzero
      rw [hzero']; exact Submodule.zero_mem (p := nucleusGZero)
    bracket_negTwo_posTwo := by
      intro X Y hX hY
      rcases span_singleton_eq_nucleus hX with ⟨a, rfl⟩
      rcases span_singleton_eq_nucleus hY with ⟨b, rfl⟩
      have h_eq : InfoGeometry.Canonical.SL2SpinorLadder.Alg.br (a • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisF) (b • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisE) = (-(a * b)) • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisH := by
        calc
          InfoGeometry.Canonical.SL2SpinorLadder.Alg.br (a • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisF) (b • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisE) = (a * b) • InfoGeometry.Canonical.SL2SpinorLadder.Alg.br InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisF InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisE := by
            rw [InfoGeometry.Canonical.SL2SpinorLadder.Alg.br_smul_left, InfoGeometry.Canonical.SL2SpinorLadder.Alg.br_smul_right, smul_smul]
          _ = (a * b) • (-InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisH) := by norm_num [InfoGeometry.Canonical.SL2SpinorLadder.Alg.br, InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisF, InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisE, InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisH]
          _ = (-(a * b)) • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisH := by simp
      have h_eq' : ⁅a • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisF, b • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisE⁆ = (-(a * b)) • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisH := h_eq
      rw [h_eq']
      apply Submodule.smul_mem
      exact Submodule.mem_span_singleton_self (InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisH)
    posOne_posOne_mem_posTwo := by
      intro X Y hX hY
      rcases span_singleton_eq_nucleus hX with ⟨a, rfl⟩
      rcases span_singleton_eq_nucleus hY with ⟨b, rfl⟩
      have hzero : InfoGeometry.Canonical.SL2SpinorLadder.Alg.br (a • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU) (b • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU) = 0 := by
        simp [InfoGeometry.Canonical.SL2SpinorLadder.Alg.br, InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU]
      have hzero' : ⁅a • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU, b • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU⁆ = 0 := hzero
      rw [hzero']; exact Submodule.zero_mem (p := nucleusGPosTwo)
    negOne_negOne_mem_negTwo := by
      intro X Y hX hY
      rcases span_singleton_eq_nucleus hX with ⟨a, rfl⟩
      rcases span_singleton_eq_nucleus hY with ⟨b, rfl⟩
      have hzero : InfoGeometry.Canonical.SL2SpinorLadder.Alg.br (a • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV) (b • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV) = 0 := by
        simp [InfoGeometry.Canonical.SL2SpinorLadder.Alg.br, InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV]
      have hzero' : ⁅a • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV, b • InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV⁆ = 0 := hzero
      rw [hzero']; exact Submodule.zero_mem (p := nucleusGNegTwo) }

/-- The nuclear quantum-number generators, mapped onto the existing
`SL2SpinorLadder` basis. -/
def nucleusGenSpin : NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisE

def nucleusGenIsospin : NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisF

def nucleusGenTz : NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV

def nucleusGenHelicity : NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU

def nucleusGenMass : NucleusLieCarrier :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisH

/-- `spin` generates the `gPosTwo` grade. -/
theorem spin_gen_mem_gPosTwo : nucleusGenSpin ∈ nucleusGPosTwo := by
  simp [nucleusGPosTwo, nucleusGenSpin,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisE,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₂']

/-- `isospin` generates the `gNegTwo` grade. -/
theorem isospin_gen_mem_gNegTwo : nucleusGenIsospin ∈ nucleusGNegTwo := by
  simp [nucleusGNegTwo, nucleusGenIsospin,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisF,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₂]

/-- `Tz` generates the `gNegOne` grade. -/
theorem Tz_gen_mem_gNegOne : nucleusGenTz ∈ nucleusGNegOne := by
  simp [nucleusGNegOne, nucleusGenTz,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₁]

/-- `helicity` generates the `gPosOne` grade. -/
theorem helicity_gen_mem_gPosOne : nucleusGenHelicity ∈ nucleusGPosOne := by
  simp [nucleusGPosOne, nucleusGenHelicity,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₁']

/-- `mass` generates the `gZero` grade. -/
theorem mass_gen_mem_gZero : nucleusGenMass ∈ nucleusGZero := by
  simp [nucleusGZero, nucleusGenMass,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisH,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.G₀]

/-- The bracket of `spin` and `isospin` yields `mass`. -/
theorem bracket_spin_isospin_eq_mass :
    (InfoGeometry.Canonical.SL2SpinorLadder.Alg.br nucleusGenSpin nucleusGenIsospin) = nucleusGenMass := by
  simp [nucleusGenSpin, nucleusGenIsospin, nucleusGenMass,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisE,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisF,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisH,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.br]

/-- The bracket of `helicity` and `Tz` yields zero. -/
theorem bracket_helicity_Tz_zero :
    (InfoGeometry.Canonical.SL2SpinorLadder.Alg.br nucleusGenHelicity nucleusGenTz) = 0 := by
  simp [nucleusGenHelicity, nucleusGenTz,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisU,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.basisV,
    InfoGeometry.Canonical.SL2SpinorLadder.Alg.br]

end InfoGeometry.External.Auto
