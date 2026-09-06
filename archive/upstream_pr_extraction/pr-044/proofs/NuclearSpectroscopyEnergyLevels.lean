import proofs.TrappedHarmonicModes

/-!
# Nuclear spectroscopy energy levels

This file translates the trapped-mode and chiral-isospin story into standard
rotational-vibrational nuclear spectroscopy notation.  The formulas are finite
algebraic bookkeeping over `ℝ`; the physical interpretation involving
mirror-nucleus spectra, Higgs/Möbius mass gaps, B(E1) transition data, and
Standard-Model energy levels is kept outside this algebraic layer.
-/

noncomputable section

namespace NuclearSpectroscopyEnergyLevels

/-- Dimensionless/real parameters of the Goutev--Tonev spectroscopic Hamiltonian.
`coriolisParity` is the real sign `(-1)^(J+1/2)` after the half-integer spin
sector has been selected externally. -/
structure SpectroscopyParams where
  chiS3 : ℝ
  kleinPartition : ℝ
  hbarOmegaVac : ℝ
  Arot : ℝ
  Brot : ℝ
  decoupling : ℝ
  inertiaFactor : ℝ
  coriolisParity : ℝ

/-- Quantum-number labels.  `p` is the primon generation label; `J` and `K` are
stored as real-valued spectroscopy labels to keep the formula layer lightweight. -/
structure QuantumNumbers where
  nPlus : ℕ
  nMinus : ℕ
  J : ℝ
  K : ℝ
  p : ℕ

/-- Kronecker switch for the `K = 1/2` Coriolis band. -/
def deltaKHalf (K : ℝ) : ℝ := if K = (1 / 2 : ℝ) then 1 else 0

@[simp] theorem deltaKHalf_half : deltaKHalf (1 / 2 : ℝ) = 1 := by
  simp [deltaKHalf]

/-- Topological/Möbius mass-gap term. -/
def ETop (P : SpectroscopyParams) (Q : QuantumNumbers) : ℝ :=
  |P.chiS3| / P.kleinPartition * Real.log Q.p

/-- Vibrational Jaynes/Cuntz counting energy. -/
def EVib (P : SpectroscopyParams) (Q : QuantumNumbers) : ℝ :=
  P.hbarOmegaVac * ((Q.nPlus : ℝ) + (Q.nMinus : ℝ) + 1)

/-- Axially symmetric rotational energy. -/
def ERot (P : SpectroscopyParams) (Q : QuantumNumbers) : ℝ :=
  P.Arot * (Q.J * (Q.J + 1) - Q.K ^ 2)

/-- Coriolis anti-pairing / decoupling contribution for the `K = 1/2` band. -/
def ECoriolis (P : SpectroscopyParams) (Q : QuantumNumbers) : ℝ :=
  P.coriolisParity * P.decoupling * P.inertiaFactor * (Q.J + 1 / 2) * deltaKHalf Q.K

/-- Total decomposed Hamiltonian energy. -/
def ETotal (P : SpectroscopyParams) (Q : QuantumNumbers) : ℝ :=
  ETop P Q + EVib P Q + ERot P Q + ECoriolis P Q

/-- Publication-style unified rotational-vibrational formula. -/
def EUnified (P : SpectroscopyParams) (Q : QuantumNumbers) : ℝ :=
  (|P.chiS3| / P.kleinPartition * Real.log Q.p + P.hbarOmegaVac) +
    P.hbarOmegaVac * ((Q.nPlus : ℝ) + (Q.nMinus : ℝ)) +
    P.Arot * (Q.J * (Q.J + 1)) +
    (P.Brot - P.Arot) * Q.K ^ 2 +
    ECoriolis P Q

/-- The exact decomposition statement for the total Hamiltonian. -/
theorem total_hamiltonian_decomposition (P : SpectroscopyParams) (Q : QuantumNumbers) :
    ETotal P Q = ETop P Q + EVib P Q + ERot P Q + ECoriolis P Q := rfl

/-- If `B = 0`, the publication-style formula is exactly the decomposed formula
after expanding the oscillator zero-point term.  The more general `B` term is
kept separate as the standard asymmetric-rotor extension. -/
theorem unified_formula_matches_decomposition_when_B_zero
    (P : SpectroscopyParams) (Q : QuantumNumbers) (hB : P.Brot = 0) :
    EUnified P Q = ETotal P Q := by
  simp [EUnified, ETotal, ETop, EVib, ERot, hB]
  ring

/-- First-generation topological gap formula. -/
theorem first_generation_top_gap (P : SpectroscopyParams)
    (Q : QuantumNumbers) (hp : Q.p = 2) :
    ETop P Q = |P.chiS3| / P.kleinPartition * Real.log 2 := by
  simp [ETop, hp]

/-- For the normalized `|χ|=1`, `Z_Klein=6`, `p=2` model, the topological gap is
`log 2 / 6`. -/
theorem normalized_first_generation_top_gap
    (P : SpectroscopyParams) (Q : QuantumNumbers)
    (hchi : |P.chiS3| = 1) (hZ : P.kleinPartition = 6) (hp : Q.p = 2) :
    ETop P Q = Real.log 2 / 6 := by
  simp [ETop, hchi, hZ, hp]
  ring

/-- Capstone synthesis: formulas and finite selection rules compile. -/
theorem nuclear_spectroscopy_energy_level_synthesis
    (P : SpectroscopyParams) (Q : QuantumNumbers) :
    ETotal P Q = ETop P Q + EVib P Q + ERot P Q + ECoriolis P Q ∧
    deltaKHalf (1 / 2 : ℝ) = 1 ∧
    TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.fundamental = true ∧
    TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.firstOvertone = true ∧
    TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.secondOvertone = true ∧
    TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.evanescent = false ∧
    TrappedHarmonicModes.primonOvertonePrimes.length = 3 ∧
    ProjectiveWallpaperGaugePSA.WallpaperGroup.pg ≠
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m := by
  constructor
  · exact total_hamiltonian_decomposition P Q
  constructor
  · exact deltaKHalf_half
  constructor
  · exact TrappedHarmonicModes.fundamental_trapped
  constructor
  · exact TrappedHarmonicModes.first_overtone_trapped
  constructor
  · exact TrappedHarmonicModes.second_overtone_trapped
  constructor
  · exact TrappedHarmonicModes.evanescent_not_trapped
  constructor
  · exact TrappedHarmonicModes.primon_overtone_count
  · decide

end NuclearSpectroscopyEnergyLevels

end noncomputable section
