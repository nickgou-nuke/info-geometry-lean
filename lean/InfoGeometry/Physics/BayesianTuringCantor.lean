import Mathlib.Tactic
import InfoGeometry.Physics.MDPASJMSouriauCantorColimit
import InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge

/-!
# Bayesian/Turing finite Cantor layer

This module extracts the theorem-safe mathematical content from the
Bayesian-machine/Turing-tape discussion.

Closed Lean content:

* an infinite Turing tape is the repo-owned Cantor boundary `ℕ → Bool`;
* finite programs/events are cylinder predicates on `BitWord n`;
* observing a finite prefix is evaluation of the corresponding cylinder;
* Bayesian conditioning on an observed atom is an exact finite-rational update;
* the shift/head movement on tapes has the expected prefix readout;
* finite logarithmic-ratio, twistor-incidence, and `dQ/Q` residue identities are
  algebraic certificates only.

No analytic Radon-measure theorem, Tychonoff compactness theorem, Tomita--
Takesaki construction, Grothendieck motive, positive Grassmannian theorem, or
amplituhedron theorem is claimed here.
-/

noncomputable section

namespace InfoGeometry.Physics.BayesianTuringCantor

open BigOperators
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge

/-- The deterministic infinite Turing tape is the Cantor boundary. -/
abbrev TuringTape := CantorBoundary

/-- A finite program/decidable observation at stage `n`: a set of accepted prefixes. -/
abbrev FiniteProgram (n : ℕ) := Set (BitWord n)

/-- A tape satisfies a finite program when its prefix lies in the program cylinder. -/
def tapeSatisfies (n : ℕ) (P : FiniteProgram n) (τ : TuringTape) : Prop :=
  boundaryPrefix n τ ∈ P

/-- The cylinder of a finite program as a set of infinite tapes. -/
def programCylinder (n : ℕ) (P : FiniteProgram n) : Set TuringTape :=
  {τ | tapeSatisfies n P τ}

@[simp] theorem mem_programCylinder_iff (n : ℕ) (P : FiniteProgram n) (τ : TuringTape) :
    τ ∈ programCylinder n P ↔ boundaryPrefix n τ ∈ P :=
  Iff.rfl

/-- Cylinder intersection is finite-program intersection. -/
theorem programCylinder_inter (n : ℕ) (P Q : FiniteProgram n) :
    programCylinder n (P ∩ Q) = programCylinder n P ∩ programCylinder n Q := by
  ext τ
  rfl

/-- Cylinder union is finite-program union. -/
theorem programCylinder_union (n : ℕ) (P Q : FiniteProgram n) :
    programCylinder n (P ∪ Q) = programCylinder n P ∪ programCylinder n Q := by
  ext τ
  rfl

/-- Cylinder complement is finite-program complement. -/
theorem programCylinder_compl (n : ℕ) (P : FiniteProgram n) :
    programCylinder n Pᶜ = (programCylinder n P)ᶜ := by
  ext τ
  rfl

/-- The Turing-head shift: drop the first bit. -/
def tapeShift (τ : TuringTape) : TuringTape :=
  fun i => τ (i + 1)

/-- Prefix readout after one shift is the tail block of the old prefix. -/
theorem boundaryPrefix_tapeShift (n : ℕ) (τ : TuringTape) (i : Fin n) :
    boundaryPrefix n (tapeShift τ) i =
      boundaryPrefix (n + 1) τ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ :=
  rfl

/-- Exact finite-rational prior over length-`n` tape windows. -/
structure FiniteTapePrior (n : ℕ) where
  mass : BitWord n → ℚ
  nonneg : ∀ w, 0 ≤ mass w
  total : (∑ w : BitWord n, mass w) = 1

namespace FiniteTapePrior

variable {n : ℕ}

/-- Probability of a finite event/program. -/
def eventProb (μ : FiniteTapePrior n) (P : FiniteProgram n) : ℚ :=
  ∑ w : BitWord n, @ite ℚ (w ∈ P) (Classical.propDecidable (w ∈ P)) (μ.mass w) 0

/-- The atom event selecting one observed prefix. -/
def atomEvent (w : BitWord n) : FiniteProgram n :=
  {v | v = w}

/-- Point mass at a finite observed prefix. -/
def dirac (w : BitWord n) : FiniteTapePrior n where
  mass := fun v => if v = w then 1 else 0
  nonneg := by
    intro v
    by_cases h : v = w <;> simp [h]
  total := by
    classical
    simp

/-- Conditioning on an observed atom collapses to the corresponding Dirac mass. -/
def conditionOnObservedPrefix (_μ : FiniteTapePrior n) (w : BitWord n) : FiniteTapePrior n :=
  dirac w

@[simp] theorem conditionOnObservedPrefix_mass_self
    (μ : FiniteTapePrior n) (w : BitWord n) :
    (conditionOnObservedPrefix μ w).mass w = 1 := by
  simp [conditionOnObservedPrefix, dirac]

@[simp] theorem conditionOnObservedPrefix_mass_ne
    (μ : FiniteTapePrior n) {w v : BitWord n} (h : v ≠ w) :
    (conditionOnObservedPrefix μ w).mass v = 0 := by
  simp [conditionOnObservedPrefix, dirac, h]

/-- The conditioned atom has probability one. -/
theorem eventProb_atom_conditioned_self (μ : FiniteTapePrior n) (w : BitWord n) :
    eventProb (conditionOnObservedPrefix μ w) (atomEvent w) = 1 := by
  classical
  simp [eventProb, atomEvent, conditionOnObservedPrefix, dirac]

/-- A different atom has conditioned probability zero. -/
theorem eventProb_atom_conditioned_ne
    (μ : FiniteTapePrior n) {w v : BitWord n} (h : v ≠ w) :
    eventProb (conditionOnObservedPrefix μ w) (atomEvent v) = 0 := by
  classical
  simp [eventProb, atomEvent, conditionOnObservedPrefix, dirac, h]

/-- Exact Bayesian normalization for the finite observed-prefix update. -/
theorem conditionOnObservedPrefix_total (μ : FiniteTapePrior n) (w : BitWord n) :
    (∑ v : BitWord n, (conditionOnObservedPrefix μ w).mass v) = 1 :=
  (conditionOnObservedPrefix μ w).total

end FiniteTapePrior

/-! ## Finite algebraic shadows of the logarithmic/twistor discussion -/

/-- A two-component Weyl spinor over exact rationals. -/
abbrev WeylSpinor := Fin 2 → ℚ

/-- A `2 × 2` rational matrix acting on Weyl spinors. -/
abbrev Matrix2Q := Fin 2 → Fin 2 → ℚ

/-- Matrix-vector action for the finite twistor-incidence socket. -/
def matVec (X : Matrix2Q) (π : WeylSpinor) : WeylSpinor :=
  fun i => ∑ j : Fin 2, X i j * π j

/-- A finite twistor is a pair `(ω, π)`. -/
structure TwistorQ where
  omega : WeylSpinor
  pi : WeylSpinor

/-- Twistor incidence over a rational `2 × 2` matrix. -/
def TwistorIncident (X : Matrix2Q) (Z : TwistorQ) : Prop :=
  Z.omega = matVec X Z.pi

/-- Zero spacetime matrix gives the zero-omega incidence relation. -/
theorem twistorIncident_zero (π : WeylSpinor) :
    TwistorIncident (fun _ _ => 0) ⟨fun _ => 0, π⟩ := by
  ext i
  simp [matVec]

/-- Finite logarithmic Radon--Nikodym potential as an additive rational coordinate. -/
def logRNIncrement (φ ψ : ℚ) : ℚ :=
  ψ - φ

/-- Logarithmic increments satisfy the cocycle/telescoping identity. -/
theorem logRNIncrement_cocycle (φ ψ χ : ℚ) :
    logRNIncrement φ ψ + logRNIncrement ψ χ = logRNIncrement φ χ := by
  unfold logRNIncrement
  ring_nf

/-- A closed three-edge loop has zero total finite logarithmic increment. -/
theorem logRNIncrement_loop_zero (a b c : ℚ) :
    logRNIncrement a b + logRNIncrement b c + logRNIncrement c a = 0 := by
  unfold logRNIncrement
  ring_nf

/-- Exact rational `dQ/Q` residue for a nonzero scalar finite cell. -/
def logResidue (Q dQ : ℚ) : ℚ :=
  dQ / Q

/-- If the finite boundary variation equals the nonzero coordinate, the residue is one. -/
theorem logResidue_self {Q : ℚ} (hQ : Q ≠ 0) :
    logResidue Q Q = 1 := by
  unfold logResidue
  field_simp [hQ]

/-- Finite packet collecting the theorem-safe Bayesian/Turing/logarithmic layer. -/
structure BayesianTuringPacket where
  tape_carrier : Type
  tape_carrier_eq : tape_carrier = TuringTape
  finite_program_closed_under_intersection : ∀ n (P Q : FiniteProgram n),
    programCylinder n (P ∩ Q) = programCylinder n P ∩ programCylinder n Q
  finite_log_cocycle : ∀ φ ψ χ : ℚ,
    logRNIncrement φ ψ + logRNIncrement ψ χ = logRNIncrement φ χ
  residue_one : ∀ {Q : ℚ}, Q ≠ 0 → logResidue Q Q = 1

/-- Main theorem-safe readout: the finite Bayesian/Turing layer is closed algebraically. -/
def bayesian_turing_cantor_packet : BayesianTuringPacket where
  tape_carrier := TuringTape
  tape_carrier_eq := rfl
  finite_program_closed_under_intersection := programCylinder_inter
  finite_log_cocycle := logRNIncrement_cocycle
  residue_one := logResidue_self

end InfoGeometry.Physics.BayesianTuringCantor
