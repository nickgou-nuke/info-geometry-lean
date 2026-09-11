import InfoGeometry.Clifford.Cl11InfiniteCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Inductive colimit crystal readout

This module gives theorem-safe names to the finite-to-infinite crystal analogy.
The atom is a finite `Cl(1,1)` tensor-tower stage, binding is finite tensor
advance, and the crystal carrier is the repository-owned algebraic direct
limit.

No Bloch-wave continuum theorem, Klein-bottle Brillouin-zone theorem, mass-gap
theorem, or physical condensed-matter classification is asserted here.  The
closed content is algebraic: finite advances have the same direct-limit image,
inner commutators transport, and normalized trace/log-det readouts are stable
along the tower.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.InductiveColimitCrystal

open InfoGeometry.Clifford.Cl11InfiniteCarrier

/-- The finite-dimensional atom at tensor depth `n`. -/
abbrev AtomStage (n : ℕ) : Type := Stage n

/-- The algebraic inductive-colimit carrier: the finite atoms after binding. -/
abbrev CrystalCarrier : Type := CompatibleCarrier

/-- The finite binding/advance operation from depth `m` to depth `m + k`. -/
def bindAtoms (m k : ℕ) : AtomStage m →+* AtomStage (m + k) :=
  finiteAdvance m k

/-- The canonical map from a finite atom into the crystal carrier. -/
def intoCrystal (n : ℕ) : AtomStage n →+* CrystalCarrier :=
  intoCarrier n

/-- Binding finitely many atoms does not change the represented crystal element. -/
theorem bindAtoms_same_crystal_site
    (m k : ℕ) (A : AtomStage m) :
    intoCrystal (m + k) (bindAtoms m k A) = intoCrystal m A := by
  exact intoCarrier_finiteAdvance m k A

/-- Square-zero finite atoms remain square-zero in the crystal carrier. -/
theorem squareZero_atom_to_crystal
    {n : ℕ} {A : AtomStage n} (hA : A * A = 0) :
    intoCrystal n A * intoCrystal n A = 0 := by
  exact InfoGeometry.Clifford.Cl11TensorTowerLimit.limit_square_zero (n := n) hA

/-- Idempotent finite atoms remain idempotent in the crystal carrier. -/
theorem idempotent_atom_to_crystal
    {n : ℕ} {P : AtomStage n} (hP : P * P = P) :
    intoCrystal n P * intoCrystal n P = intoCrystal n P := by
  exact InfoGeometry.Clifford.Cl11TensorTowerLimit.limit_idempotent (n := n) hP

/-- Finite binding transports inner-commutator waves exactly. -/
theorem bindAtoms_ringCommutator
    (m k : ℕ) (K X : AtomStage m) :
    bindAtoms m k (ringCommutator K X) =
      ringCommutator (bindAtoms m k K) (bindAtoms m k X) := by
  exact finiteAdvance_ringCommutator m k K X

/-- Inner commutators are derivations on the crystal carrier. -/
theorem crystal_ringCommutator_isDerivation
    (K X Y : CrystalCarrier) :
    ringCommutator K (X * Y) = ringCommutator K X * Y + X * ringCommutator K Y := by
  exact carrier_ringCommutator_isDerivation K X Y

/-- The direct-limit carrier reads a commutator and any finite advance identically. -/
theorem crystal_reads_finite_advance_commutator
    (m k : ℕ) (K X : AtomStage m) :
    intoCrystal (m + k)
        (ringCommutator (bindAtoms m k K) (bindAtoms m k X)) =
      intoCrystal m (ringCommutator K X) := by
  exact intoCarrier_finiteAdvance_ringCommutator m k K X

/-- The normalized Markov trace readout is stable along finite crystal binding. -/
theorem crystal_markovTrace_stable
    (m n : ℕ) (h : m ≤ n) (A : AtomStage m) :
    InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace n
        (InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11InductiveAlgebraNet.embedMap m n h A) =
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace m A := by
  exact compatibleMarkovTrace_stable m n h A

/-- The normalized log-determinant readout is stable under one crystal binding step. -/
theorem crystal_normalizedLogDet_one_step_stable
    (n : ℕ) (A : AtomStage n) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (n + 1)
        (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed n A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet n A := by
  exact compatibleLogDet_one_step n A

/-- Finite binding preserves the normalized trace for any finite number of steps. -/
theorem bindAtoms_normalizedTrace_stable
    (m k : ℕ) (A : AtomStage m) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace (m + k) (bindAtoms m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace m A := by
  exact InfoGeometry.Clifford.Cl11TensorTowerIteration.iteratedStageEmbed_normalizedTrace m k A

/-- Finite binding preserves the normalized log-absolute determinant readout. -/
theorem bindAtoms_normalizedLogAbsDet_stable
    (m k : ℕ) (A : AtomStage m) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (m + k) (bindAtoms m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet m A := by
  exact InfoGeometry.Clifford.Cl11TensorTowerIteration.iteratedStageEmbed_normalizedLogAbsDet m k A

end InfoGeometry.Clifford.InductiveColimitCrystal

end noncomputable section
