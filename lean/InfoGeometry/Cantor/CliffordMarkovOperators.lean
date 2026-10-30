/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Cantor.CantorRandomWalk
import InfoGeometry.Clifford.ClNNPermutationSymmetry
import InfoGeometry.Clifford.ClNNFockRepresentation

/-!
# Cantor finite-mode operators on the split Clifford Fock carrier

Finite-mode steps are represented as operators on the actual Fock module by
the noncommutative split Clifford algebra action. This is the operator owner
for Cantor finite-mode work; transition matrices may later supply coefficients
for averages, but do not serve as the operator carrier.
-/

noncomputable section

namespace InfoGeometry.Cantor.CliffordMarkovOperators

open InfoGeometry.Clifford.ClNNFockRepresentation
open InfoGeometry.Clifford.ClNNPermutationSymmetry
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.FockSpaceCAR
open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable (n : ℕ)

/-- A normalized finite mode and its evaluation covector, as one neutral
split-Clifford direction. -/
def cantorNeutralMode (i : Fin n) : Neutral n :=
  (Pi.single i (1 : ℝ), LinearMap.proj i)

/-- The represented Clifford operator of a finite Cantor mode on the actual
primal-sheet Fock space. Its carrier is an endomorphism algebra under
composition, and its action comes from `Cl(n,n)`. -/
def cantorModeCliffordOperator (i : Fin n) :
    Module.End ℝ (FockSpace (PrimalSheet n)) :=
  towerFockRep n
    (CliffordAlgebra.ι (TowerForm n)
      (neutralToSplit n (cantorNeutralMode n i)))

/-- Each normalized finite-mode Clifford operator is an involution. -/
theorem cantorModeCliffordOperator_sq (i : Fin n) :
    cantorModeCliffordOperator n i * cantorModeCliffordOperator n i = 1 := by
  ext ψ
  change towerFockRep n
      (CliffordAlgebra.ι (TowerForm n)
        (neutralToSplit n (cantorNeutralMode n i)))
      (towerFockRep n
        (CliffordAlgebra.ι (TowerForm n)
          (neutralToSplit n (cantorNeutralMode n i))) ψ) = ψ
  rw [towerFockRep_neutral_generator_sq]
  simp [cantorNeutralMode, Qsplit_neutralToSplit,
    canonicalNeutralFormUnscaled_apply]

/-- Distinct finite modes satisfy the fermionic cross-mode relation in the
actual operator algebra. In particular, the finite-mode carrier retains the
noncommutative CAR structure. -/
theorem cantorModeCliffordOperator_cross_CAR {i j : Fin n} (hij : i ≠ j) :
    cantorModeCliffordOperator n i * cantorModeCliffordOperator n j +
      cantorModeCliffordOperator n j * cantorModeCliffordOperator n i = 0 := by
  ext ψ
  change
    towerFockRep n
        (CliffordAlgebra.ι (TowerForm n)
          (neutralToSplit n (cantorNeutralMode n i)))
        (towerFockRep n
          (CliffordAlgebra.ι (TowerForm n)
            (neutralToSplit n (cantorNeutralMode n j))) ψ) +
      towerFockRep n
        (CliffordAlgebra.ι (TowerForm n)
          (neutralToSplit n (cantorNeutralMode n j)))
        (towerFockRep n
          (CliffordAlgebra.ι (TowerForm n)
            (neutralToSplit n (cantorNeutralMode n i))) ψ) = 0
  rw [towerFockRep_neutral_generator_anticommutator]
  have hpolar :
      QuadraticMap.polar (TowerForm n)
        (neutralToSplit n (cantorNeutralMode n i))
        (neutralToSplit n (cantorNeutralMode n j)) = 0 := by
    rw [neutralToSplit_polar, chevelleyQsplit_eq_neutralForm,
      canonicalNeutralFormUnscaled_polar]
    simp [cantorNeutralMode, canonicalNeutralBilin_apply, hij]
  simp [hpolar]

/-- The actual finite Fock symmetry closure permutes the represented Cantor
mode operators by conjugation. This identifies the Clifford generators with
the operators averaged by the Birkhoff Markov channel. -/
theorem fockPermutation_conj_cantorMode
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    fockOperatorPermutationEquiv n σ (cantorModeCliffordOperator n i) =
      cantorModeCliffordOperator n (σ i) := by
  have hmode :
      neutralModePermutation n σ (cantorNeutralMode n i) =
        cantorNeutralMode n (σ i) := by
    apply Prod.ext
    · ext j
      by_cases h : j = σ i
      · subst j
        simp [cantorNeutralMode, neutralModePermutation, modePermutationLinearEquiv]
      · have h' : σ.symm j ≠ i := by
          intro hs
          apply h
          calc
            j = σ (σ.symm j) := by simp
            _ = σ i := congrArg σ hs
        simp [cantorNeutralMode, neutralModePermutation, modePermutationLinearEquiv,
          Pi.single_apply, h, h']
    · ext x
      simp [cantorNeutralMode, neutralModePermutation, modePermutationLinearEquiv,
        LinearEquiv.dualMap_symm, LinearEquiv.dualMap_apply]
  rw [cantorModeCliffordOperator,
    fockOperatorPermutation_towerFockRep_neutralGenerator]
  rw [hmode]
  rfl

/-- A finite Birkhoff Markov average acts on each represented Cantor mode by
the corresponding weighted sum of permuted noncommutative Fock operators. -/
theorem randomFockAverage_cantorMode
    (w : Equiv.Perm (Fin n) → ℝ) (i : Fin n) :
    randomFockOperatorAverage n w (cantorModeCliffordOperator n i) =
      ∑ σ : Equiv.Perm (Fin n),
        w σ • cantorModeCliffordOperator n (σ i) := by
  classical
  simp [randomFockOperatorAverage, fockPermutation_conj_cantorMode]

end InfoGeometry.Cantor.CliffordMarkovOperators
