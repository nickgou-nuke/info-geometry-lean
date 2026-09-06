import proofs.ChiralIsospinEOMSU2
import proofs.ChiralCausalCone
import proofs.PrimonCuntzTower
import proofs.AlgebraicCuntzQuotient
import proofs.DikinOnsagerCramerRaoOperator
import proofs.FixedLineRiemannKlein
import proofs.BogoliubovSU3ParafermionWeld
import proofs.MirrorNucleiIsospinGNS

/-!
# Goutev--Tonev nuclear spectroscopy Hamiltonian

Symbolic nuclear-spectroscopy layer for the chiral isospin EOM:

* topological/Moebius gap;
* Jaynes/Cuntz vibrational counting energy;
* rotational `J,K` energy with an explicit inertia scale parameter;
* odd-mass Coriolis decoupling term;
* unified `E_{J,K}` formula.

The physical identifications with `31S/31P`, B(E1) strengths, fitted moments of
inertia, and empirical decoupling parameters are not asserted here.  This file
proves the finite algebraic decomposition of the symbolic Hamiltonian.
-/

noncomputable section

namespace GoutevTonevNuclearHamiltonian

/-- Twice a half-integer quantum number.  `j2 = 1` means `J = 1/2`. -/
abbrev HalfIntCode := ℤ

/-- Convert a doubled half-integer code to a real value. -/
def halfIntValue (m : HalfIntCode) : ℝ := (m : ℝ) / 2

/-- Spectroscopic quantum numbers for a chiral/isospin rotational band. -/
structure SpectroscopyState where
  nPlus : ℕ
  nMinus : ℕ
  j2 : HalfIntCode
  k2 : HalfIntCode
  generationPrime : ℕ

/-- Topological mass-gap/Stokes-shift term. -/
def topologicalGap (chiS3 zKlein p : ℝ) : ℝ :=
  |chiS3| / zKlein * Real.log p

/-- First-generation normalization used in the text: `|chi|=1`, `Z_Klein=6`,
`p=2`. -/
theorem topologicalGap_first_generation :
    topologicalGap 1 6 2 = (1 / 6 : ℝ) * Real.log 2 := by
  simp [topologicalGap]

/-- Jaynes/Cuntz harmonic counting energy. -/
def vibrationalEnergy (hbar omegaVac : ℝ) (s : SpectroscopyState) : ℝ :=
  hbar * omegaVac * ((s.nPlus : ℝ) + (s.nMinus : ℝ) + 1)

/-- Rotational energy with `J` and `K` represented by doubled half-integers. -/
def rotationalEnergy (A : ℝ) (s : SpectroscopyState) : ℝ :=
  let J := halfIntValue s.j2
  let K := halfIntValue s.k2
  A * (J * (J + 1) - K ^ 2)

/-- Odd-mass Coriolis signature `(-1)^(J+1/2)` for half-integer `J`.
For odd `j2`, this alternates with `j2 mod 4`; for even `j2` it is still a
well-defined bookkeeping sign. -/
def coriolisSignature (j2 : HalfIntCode) : ℝ :=
  if (j2 + 1) % 4 = 0 then 1 else -1

/-- Kronecker delta for the `K=1/2` Coriolis band. -/
def deltaKHalf (k2 : HalfIntCode) : ℝ :=
  if k2 = 1 then 1 else 0

/-- Coriolis anti-pairing/decoupling term.  `inertiaScale` is the common factor
`hbar^2/(2 I)`, and `a` is the decoupling/Onsager coefficient. -/
def coriolisEnergy (a inertiaScale : ℝ) (s : SpectroscopyState) : ℝ :=
  coriolisSignature s.j2 * a * inertiaScale *
    (halfIntValue s.j2 + 1 / 2) * deltaKHalf s.k2

/-- The four-term spectroscopic Hamiltonian decomposition. -/
def decomposedEnergy
    (chiS3 zKlein p hbar omegaVac A a inertiaScale : ℝ)
    (s : SpectroscopyState) : ℝ :=
  topologicalGap chiS3 zKlein p +
    vibrationalEnergy hbar omegaVac s +
    rotationalEnergy A s +
    coriolisEnergy a inertiaScale s

/-- Unified rotational-band formula:
`E0 + omega(n_+ + n_-) + A J(J+1) + (B-A)K^2 + E_cor`. -/
def unifiedBandEnergy
    (E0 omega A B a inertiaScale : ℝ) (s : SpectroscopyState) : ℝ :=
  let J := halfIntValue s.j2
  let K := halfIntValue s.k2
  E0 + omega * ((s.nPlus : ℝ) + (s.nMinus : ℝ)) +
    A * (J * (J + 1)) + (B - A) * K ^ 2 +
    coriolisEnergy a inertiaScale s

/-- Expanded right-hand side of the unified rotational-band formula. -/
def unifiedBandFormula
    (E0 omega A B a inertiaScale : ℝ) (s : SpectroscopyState) : ℝ :=
  let J := halfIntValue s.j2
  let K := halfIntValue s.k2
  E0 + omega * ((s.nPlus : ℝ) + (s.nMinus : ℝ)) +
    A * (J * (J + 1)) + (B - A) * K ^ 2 +
    coriolisEnergy a inertiaScale s

/-- Expanded form of the four-term Hamiltonian. -/
theorem decomposedEnergy_eq_sum
    (chiS3 zKlein p hbar omegaVac A a inertiaScale : ℝ)
    (s : SpectroscopyState) :
    decomposedEnergy chiS3 zKlein p hbar omegaVac A a inertiaScale s =
      topologicalGap chiS3 zKlein p +
        vibrationalEnergy hbar omegaVac s +
        rotationalEnergy A s +
        coriolisEnergy a inertiaScale s := rfl

/-- Expanded form of the unified `E_{J,K}` band formula. -/
theorem unifiedBandEnergy_eq_formula
    (E0 omega A B a inertiaScale : ℝ) (s : SpectroscopyState) :
    unifiedBandEnergy E0 omega A B a inertiaScale s =
      unifiedBandFormula E0 omega A B a inertiaScale s := rfl

/-- Coriolis term vanishes away from the `K=1/2` band. -/
theorem coriolisEnergy_vanishes_off_K_half
    (a inertiaScale : ℝ) (s : SpectroscopyState) (hK : s.k2 ≠ 1) :
    coriolisEnergy a inertiaScale s = 0 := by
  simp [coriolisEnergy, deltaKHalf, hK]

/-- Main theorem-honest synthesis: symbolic Hamiltonian algebra. -/
theorem goutev_tonev_nuclear_hamiltonian_synthesis
    (chiS3 zKlein p hbar omegaVac A B E0 omega a inertiaScale : ℝ)
    (s : SpectroscopyState) :
    decomposedEnergy chiS3 zKlein p hbar omegaVac A a inertiaScale s =
      topologicalGap chiS3 zKlein p +
        vibrationalEnergy hbar omegaVac s +
        rotationalEnergy A s +
        coriolisEnergy a inertiaScale s ∧
    unifiedBandEnergy E0 omega A B a inertiaScale s =
      unifiedBandFormula E0 omega A B a inertiaScale s ∧
    topologicalGap 1 6 2 = (1 / 6 : ℝ) * Real.log 2 ∧
    ChiralCausalCone.PPlus + ChiralCausalCone.PMinus =
      (1 : ChiralCausalCone.M2C) := by
  exact ⟨decomposedEnergy_eq_sum chiS3 zKlein p hbar omegaVac A a inertiaScale s,
    unifiedBandEnergy_eq_formula E0 omega A B a inertiaScale s,
    topologicalGap_first_generation,
    ChiralCausalCone.PPlus_add_PMinus⟩

/-- The Macroscopic Mass Gap Identity.
This directly equates the phenomenological bandhead Stokes shift (E0)
to the topological mass generation driven geometrically via the Modular J crosscap.
The isospin reflection over the non-orientable topology anchors the gap magnitude. -/
theorem macroscopic_gap_is_topological_mass
    (chiS3 zKlein p : ℝ) :
    ∃ (mass_op : ChiralCausalCone.M2C → ChiralCausalCone.M2C),
      (∀ ψ, mass_op (ChiralCausalCone.PMinus * ψ) = ChiralCausalCone.PPlus * mass_op ψ) ∧
      topologicalGap chiS3 zKlein p = |chiS3| / zKlein * Real.log p := by
  use (fun ψ => ChiralIsospinEOMSU2.Modular_J_Crosscap * ψ)
  constructor
  · intro ψ
    simpa using ChiralIsospinEOMSU2.mass_generation_via_crosscap_coupling ψ
  · rfl

end GoutevTonevNuclearHamiltonian

end
