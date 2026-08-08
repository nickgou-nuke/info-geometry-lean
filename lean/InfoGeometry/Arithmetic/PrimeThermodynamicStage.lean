import InfoGeometry.Arithmetic.ChiralPrimonGas
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

/-!
# Prime thermodynamic stages

Canonical cutoff-indexed state stages for the finite primon grand-canonical system.

This file reuses `ChiralPrimonGas.primeCutoffRegister` and
`PrimeGrandCanonicalEnsemble.PrimeState`. It adds only the order-preserving maps
between cutoffs. No limit, completion, or convergence statement is made here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeThermodynamicStage

open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

/-- Prime cutoffs are monotone in the cutoff parameter. -/
theorem primesUpto_mono {n m : ℕ} (h : n ≤ m) :
    primesUpto n ⊆ primesUpto m := by
  intro p hp
  rw [mem_primesUpto_iff] at hp ⊢
  exact ⟨hp.1.trans h, hp.2⟩

/-- The canonical property prime register at cutoff `n`. -/
abbrev PrimeStageRegister (n : ℕ) :=
  primeCutoffRegister n

/-- The finite prime-occupation state space at cutoff `n`. -/
abbrev PrimeStageState (n : ℕ) :=
  PrimeState (PrimeStageRegister n)

/-- Embed a state into a larger prime cutoff without changing its occupations. -/
def embedState {n m : ℕ} (h : n ≤ m) : PrimeStageState n → PrimeStageState m :=
  fun S =>
    ⟨S.1, Finset.mem_powerset.mpr fun _p hp =>
      primesUpto_mono h (Finset.mem_powerset.mp S.2 hp)⟩

/-- Cutoff state embeddings are injective. -/
theorem embedState_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (embedState h) := by
  intro S T hST
  apply Subtype.ext
  exact congrArg (fun U : PrimeStageState m => U.1) hST

/-- A cutoff embedding leaves the occupied prime set unchanged. -/
@[simp]
theorem occupied_embedState {n m : ℕ} (h : n ≤ m) (S : PrimeStageState n) :
    occupied (embedState h S) = occupied S :=
  rfl

/-- A cutoff embedding preserves the occupation-number observable. -/
@[simp]
theorem stateNumber_embedState {n m : ℕ} (h : n ≤ m) (S : PrimeStageState n) :
    stateNumber (embedState h S) = stateNumber S :=
  rfl

/-- A cutoff embedding preserves every prime-weighted energy observable. -/
@[simp]
theorem stateEnergy_embedState {n m : ℕ} (h : n ≤ m)
    (energyWeight : ℕ → ℝ) (S : PrimeStageState n) :
    stateEnergy energyWeight (embedState h S) = stateEnergy energyWeight S :=
  rfl

/-- Embedding a state into the same cutoff is the identity. -/
@[simp]
theorem embedState_refl {n : ℕ} (S : PrimeStageState n) :
    embedState (n := n) (m := n) le_rfl S = S := by
  exact Subtype.ext rfl

/-- Cutoff embeddings compose according to the order relation. -/
theorem embedState_trans {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k)
    (S : PrimeStageState n) :
    embedState (hnm.trans hmk) S = embedState hmk (embedState hnm S) := by
  exact Subtype.ext rfl

end InfoGeometry.Arithmetic.PrimeThermodynamicStage
