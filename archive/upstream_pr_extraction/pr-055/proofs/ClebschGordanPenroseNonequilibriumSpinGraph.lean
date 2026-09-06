import proofs.NuclearWallpaperSpectraClassification
import proofs.ChiralTensorRecoupling
import proofs.PenroseSpinIncidenceTessellation
import proofs.BraidedCocycleWilsonEntropy

/-!
# Clebsch--Gordan / Penrose nonequilibrium spin graph

This capstone records the user's dictionary:

```text
Clebsch--Gordan recoupling / Penrose spin networks
  → asymmetric nonequilibrium spin graph nets
  → wallpaper nuclear extinction rules
```

The kernel proves only finite recoupling/selection bookkeeping: a toy SU(2)
Clebsch--Gordan table, Temperley--Lieb idempotency, Penrose incidence edge
counts, and a nonzero Wilson/entropy circulation.  Actual numerical CG
coefficients, Wigner 6j/10j evaluations, nuclear transition amplitudes, and
physical nonequilibrium dynamics are external targets.
-/

noncomputable section

namespace ClebschGordanPenroseNonequilibriumSpinGraph

/-- Minimal spin labels for finite Clebsch--Gordan bookkeeping. -/
inductive SpinLabel where
  | j0
  | jHalf
  | j1
  | jThreeHalf
  deriving DecidableEq, Repr

/-- A tiny Clebsch--Gordan admissibility table.  It includes the familiar
`1/2 ⊗ 1/2 → 0 ⊕ 1` and `1 ⊗ 1/2 → 1/2 ⊕ 3/2` channels. -/
def CGAllowed : SpinLabel → SpinLabel → SpinLabel → Bool
  | .jHalf, .jHalf, .j0 => true
  | .jHalf, .jHalf, .j1 => true
  | .j1, .jHalf, .jHalf => true
  | .jHalf, .j1, .jHalf => true
  | .j1, .jHalf, .jThreeHalf => true
  | .jHalf, .j1, .jThreeHalf => true
  | .j0, j, k => decide (j = k)
  | j, .j0, k => decide (j = k)
  | _, _, _ => false

@[simp] theorem half_tensor_half_allows_singlet :
    CGAllowed SpinLabel.jHalf SpinLabel.jHalf SpinLabel.j0 = true := rfl

@[simp] theorem half_tensor_half_allows_triplet :
    CGAllowed SpinLabel.jHalf SpinLabel.jHalf SpinLabel.j1 = true := rfl

@[simp] theorem half_tensor_half_forbids_threeHalf :
    CGAllowed SpinLabel.jHalf SpinLabel.jHalf SpinLabel.jThreeHalf = false := rfl

@[simp] theorem one_tensor_half_allows_half :
    CGAllowed SpinLabel.j1 SpinLabel.jHalf SpinLabel.jHalf = true := rfl

@[simp] theorem one_tensor_half_allows_threeHalf :
    CGAllowed SpinLabel.j1 SpinLabel.jHalf SpinLabel.jThreeHalf = true := rfl

/-- Spin graph regimes: symmetric/equilibrium versus asymmetric driven net. -/
inductive SpinGraphRegime where
  | equilibriumSymmetric
  | nonequilibriumAsymmetric
  deriving DecidableEq, Repr

/-- The entropy-producing triangle is classified as the asymmetric regime. -/
def regimeOfWilson (w : ℤ) : SpinGraphRegime :=
  if w = 0 then .equilibriumSymmetric else .nonequilibriumAsymmetric

@[simp] theorem entropyCycle_is_nonequilibrium :
    regimeOfWilson (BraidedCocycleWilsonEntropy.triangleWilson
      BraidedCocycleWilsonEntropy.entropyCycle) =
      SpinGraphRegime.nonequilibriumAsymmetric := by
  simp [regimeOfWilson]

@[simp] theorem flatAffinity_is_equilibrium :
    regimeOfWilson (BraidedCocycleWilsonEntropy.triangleWilson
      BraidedCocycleWilsonEntropy.flatAffinity) =
      SpinGraphRegime.equilibriumSymmetric := by
  simp [regimeOfWilson]


/-- Capstone synthesis: finite recoupling and nonequilibrium graph facts compile;
actual CG/Wigner/nuclear amplitudes are external targets. -/
theorem cg_penrose_nonequilibrium_spin_graph_synthesis :
    CGAllowed SpinLabel.jHalf SpinLabel.jHalf SpinLabel.j0 = true ∧
    CGAllowed SpinLabel.jHalf SpinLabel.jHalf SpinLabel.j1 = true ∧
    CGAllowed SpinLabel.jHalf SpinLabel.jHalf SpinLabel.jThreeHalf = false ∧
    CGAllowed SpinLabel.j1 SpinLabel.jHalf SpinLabel.jHalf = true ∧
    CGAllowed SpinLabel.j1 SpinLabel.jHalf SpinLabel.jThreeHalf = true ∧
    ChiralTensorRecoupling.e * ChiralTensorRecoupling.e =
      (2 : ℂ) • ChiralTensorRecoupling.e ∧
    Fintype.card PenroseSpinTilingConfig.SpinTileGenerator = 6 ∧
    BraidedCocycleWilsonEntropy.triangleWilson
      BraidedCocycleWilsonEntropy.entropyCycle = 3 ∧
    BraidedCocycleWilsonEntropy.BrokenDetailedBalance
      BraidedCocycleWilsonEntropy.entropyCycle ∧
    regimeOfWilson (BraidedCocycleWilsonEntropy.triangleWilson
      BraidedCocycleWilsonEntropy.entropyCycle) =
      SpinGraphRegime.nonequilibriumAsymmetric ∧
    NuclearWallpaperSpectraClassification.transitionAllowed
      ProjectiveWallpaperGaugePSA.WallpaperGroup.pg
      NuclearWallpaperSpectraClassification.NuclearTransition.deltaJOneDoubletMixing = false ∧
    NuclearWallpaperSpectraClassification.transitionAllowed
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m
      NuclearWallpaperSpectraClassification.NuclearTransition.nonsingletColorMode = false := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact ChiralTensorRecoupling.e_sq
  constructor
  · exact PenroseSpinIncidenceTessellation.incidence_edge_generator_card
  constructor
  · exact BraidedCocycleWilsonEntropy.entropyCycle_wilson
  constructor
  · exact BraidedCocycleWilsonEntropy.entropyCycle_breaks_detailedBalance
  constructor
  · exact entropyCycle_is_nonequilibrium
  constructor
  · exact NuclearWallpaperSpectraClassification.pg_forbids_deltaJ_one_doublet_mixing
  · exact NuclearWallpaperSpectraClassification.p6m_forbids_nonsinglet_color_modes

end ClebschGordanPenroseNonequilibriumSpinGraph

end noncomputable section
