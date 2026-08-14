import InfoGeometry.Arithmetic.ChiralPrimonGas
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeThermodynamicStage

open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

theorem primesUpto_mono {n m : ℕ} (h : n ≤ m) :
    primesUpto n ⊆ primesUpto m := by
  intro p hp
  rw [mem_primesUpto_iff] at hp ⊢
  exact ⟨hp.1.trans h, hp.2⟩

abbrev PrimeStageRegister (n : ℕ) :=
  primeCutoffRegister n

abbrev PrimeStageState (n : ℕ) :=
  PrimeState (PrimeStageRegister n)

def embedState {n m : ℕ} (h : n ≤ m) : PrimeStageState n → PrimeStageState m :=
  fun S =>
    ⟨S.1, Finset.mem_powerset.mpr fun _p hp =>
      primesUpto_mono h (Finset.mem_powerset.mp S.2 hp)⟩

theorem embedState_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (embedState h) := by
  intro S T hST
  apply Subtype.ext
  exact congrArg (fun U : PrimeStageState m => U.1) hST

@[simp]
theorem occupied_embedState {n m : ℕ} (h : n ≤ m) (S : PrimeStageState n) :
    occupied (embedState h S) = occupied S :=
  rfl

@[simp]
theorem stateNumber_embedState {n m : ℕ} (h : n ≤ m) (S : PrimeStageState n) :
    stateNumber (embedState h S) = stateNumber S :=
  rfl

@[simp]
theorem stateEnergy_embedState {n m : ℕ} (h : n ≤ m)
    (energyWeight : ℕ → ℝ) (S : PrimeStageState n) :
    stateEnergy energyWeight (embedState h S) = stateEnergy energyWeight S :=
  rfl

@[simp]
theorem embedState_refl {n : ℕ} (S : PrimeStageState n) :
    embedState (n := n) (m := n) le_rfl S = S := by
  exact Subtype.ext rfl

theorem embedState_trans {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k)
    (S : PrimeStageState n) :
    embedState (hnm.trans hmk) S = embedState hmk (embedState hnm S) := by
  exact Subtype.ext rfl

end InfoGeometry.Arithmetic.PrimeThermodynamicStage
