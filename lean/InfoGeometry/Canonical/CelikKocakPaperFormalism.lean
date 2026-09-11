import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import InfoGeometry.Canonical.CelikKocakCantorOperators
import InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge
import InfoGeometry.Clifford.Cl11Matrix

/-!
# InfoGeometry.Canonical.CelikKocakPaperFormalism

Paper-facing consolidation for the Çelik--Koçak finite Cantor representation.

This file re-exports theorem-backed operator identities from the finite
Cantor address model:

* finite addresses `V_n = Fin n → Bool`,
* tilt/switch operators,
* the canonical finite basis on endpoint functions.

No witness-only basis packet is used here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open InfoGeometry.Canonical.CelikKocakCantorOperators
open InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge
open InfoGeometry.Clifford.Cl11Matrix
open scoped Kronecker
open scoped TensorProduct

/-- Paper-facing alias for the finite Cantor address space. -/
abbrev CantorAddress (n : ℕ) := InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress n

/-- Paper-facing alias for the finite endpoint function space. -/
abbrev FunctionSpace (n : ℕ) := InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace n

namespace FunctionSpace

variable {n : ℕ}

/-- Paper-facing tilt operator law. -/
theorem tilt_sq (j : Fin n) :
    (FunctionSpace.tilt (n := n) j) * (FunctionSpace.tilt (n := n) j) = 1 :=
  InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.tilt_sq (n := n) j

/-- Paper-facing switch operator law. -/
theorem switch_sq (j : Fin n) :
    (FunctionSpace.switch (n := n) j) * (FunctionSpace.switch (n := n) j) = 1 :=
  InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.switch_sq (n := n) j

/-- Paper-facing tilt commutation at different slots. -/
theorem tilt_comm {i j : Fin n} :
    (FunctionSpace.tilt (n := n) i) * (FunctionSpace.tilt (n := n) j)
      = (FunctionSpace.tilt (n := n) j) * (FunctionSpace.tilt (n := n) i) :=
  InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.tilt_comm (n := n) (i := i) (j := j)

/-- Paper-facing switch commutation at different slots. -/
theorem switch_comm {i j : Fin n} (hij : i ≠ j) :
    (FunctionSpace.switch (n := n) i) * (FunctionSpace.switch (n := n) j)
      = (FunctionSpace.switch (n := n) j) * (FunctionSpace.switch (n := n) i) :=
  InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.switch_comm (n := n) hij

/-- Paper-facing tilt/switch commutation at different slots. -/
theorem tilt_switch_comm_of_ne {i j : Fin n} (hij : i ≠ j) :
    (FunctionSpace.tilt (n := n) i) * (FunctionSpace.switch (n := n) j)
      = (FunctionSpace.switch (n := n) j) * (FunctionSpace.tilt (n := n) i) :=
  InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.tilt_switch_comm_of_ne (n := n) hij

/-- Paper-facing tilt/switch anticommutation at the same slot. -/
theorem tilt_switch_anticomm (j : Fin n) :
    (FunctionSpace.tilt (n := n) j) * (FunctionSpace.switch (n := n) j)
      = - ((FunctionSpace.switch (n := n) j) * (FunctionSpace.tilt (n := n) j)) :=
  InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.tilt_switch_anticomm (n := n) j

/-- Paper-facing local pair operator `T_j * S_j`. -/
def pairTerm (j : ℕ) : FunctionSpace n →ₗ[ℂ] FunctionSpace n :=
  if hj : j < n then FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩ else 1

@[simp] theorem pairTerm_of_lt {j : ℕ} (hj : j < n) :
    pairTerm (n := n) j = FunctionSpace.tilt (n := n) ⟨j, hj⟩ *
      FunctionSpace.switch (n := n) ⟨j, hj⟩ :=
  by simp [pairTerm, hj]

@[simp] theorem pairTerm_of_not_lt {j : ℕ} (hj : ¬ j < n) :
    pairTerm (n := n) j = 1 :=
  by simp [pairTerm, hj]

theorem pairTerm_sq {j : ℕ} (hj : j < n) :
    pairTerm (n := n) j * pairTerm (n := n) j = - (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n) :=
  by
    rw [pairTerm_of_lt (n := n) hj]
    calc
      (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩)
          * (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩)
        = (-(FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩))
            * (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩) := by
                rw [tilt_switch_anticomm (n := n) ⟨j, hj⟩]
      _ = - ((FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
            * (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩)) := by
                exact neg_mul (FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
                  (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩)
      _ = - (FunctionSpace.switch (n := n) ⟨j, hj⟩
            * ((FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
              * FunctionSpace.switch (n := n) ⟨j, hj⟩)) := by
                exact congrArg Neg.neg (by
                  calc
                    (FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
                        * (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩)
                      = FunctionSpace.switch (n := n) ⟨j, hj⟩
                          * (FunctionSpace.tilt (n := n) ⟨j, hj⟩
                            * (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩)) := by
                            rw [mul_assoc]
                    _ = FunctionSpace.switch (n := n) ⟨j, hj⟩
                          * ((FunctionSpace.tilt (n := n) ⟨j, hj⟩
                            * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
                            * FunctionSpace.switch (n := n) ⟨j, hj⟩) := by
                            simp [mul_assoc]
                  )
      _ = - (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n) := by
                simp [tilt_sq, switch_sq]

theorem pairTerm_commute_of_ne {i j : ℕ} (hij : i ≠ j) :
    Commute (pairTerm (n := n) i) (pairTerm (n := n) j) :=
  by
    by_cases hi : i < n
    · by_cases hj : j < n
      ·
        have hti_tj : Commute (FunctionSpace.tilt (n := n) ⟨i, hi⟩)
            (FunctionSpace.tilt (n := n) ⟨j, hj⟩) := by
          exact FunctionSpace.tilt_comm (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
        have hti_sj : Commute (FunctionSpace.tilt (n := n) ⟨i, hi⟩)
            (FunctionSpace.switch (n := n) ⟨j, hj⟩) := by
          exact FunctionSpace.tilt_switch_comm_of_ne (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by
            intro h; exact hij (congrArg Fin.val h))
        have hsi_tj : Commute (FunctionSpace.switch (n := n) ⟨i, hi⟩)
            (FunctionSpace.tilt (n := n) ⟨j, hj⟩) := by
          have h := FunctionSpace.tilt_switch_comm_of_ne (n := n) (i := ⟨j, hj⟩) (j := ⟨i, hi⟩) (by
            intro h; exact hij (congrArg Fin.val h.symm))
          simpa [Commute, mul_assoc] using h.symm
        have hsi_sj : Commute (FunctionSpace.switch (n := n) ⟨i, hi⟩)
            (FunctionSpace.switch (n := n) ⟨j, hj⟩) := by
          exact FunctionSpace.switch_comm (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by
            intro h; exact hij (congrArg Fin.val h))
        have hti_pair : Commute (FunctionSpace.tilt (n := n) ⟨i, hi⟩) (pairTerm (n := n) j) := by
          simpa [pairTerm_of_lt (n := n) hj] using hti_tj.mul_right hti_sj
        have hsi_pair : Commute (FunctionSpace.switch (n := n) ⟨i, hi⟩) (pairTerm (n := n) j) := by
          simpa [pairTerm_of_lt (n := n) hj] using hsi_tj.mul_right hsi_sj
        simpa [pairTerm_of_lt (n := n) hi, pairTerm_of_lt (n := n) hj, mul_assoc] using
          (Commute.mul_left hti_pair hsi_pair)
      · simp [pairTerm, hj]
    · simp [pairTerm, hi]

/-- Recursive prefix product of the local pair operators `T_j * S_j`. -/
def pairPrefix : ℕ → FunctionSpace n →ₗ[ℂ] FunctionSpace n
  | 0 => 1
  | m + 1 => pairPrefix m * pairTerm (n := n) m

@[simp] theorem pairPrefix_zero :
    pairPrefix (n := n) 0 = 1 := by
  rfl

@[simp] theorem pairPrefix_succ (m : ℕ) :
    pairPrefix (n := n) (m + 1) = pairPrefix (n := n) m * pairTerm (n := n) m := by
  rfl

/-- The `m`-th pair operator commutes with the prefix product up to `m`. -/
theorem pairTerm_commute_pairPrefix {m i : ℕ} (hmi : m ≤ i) :
    Commute (pairTerm (n := n) i) (pairPrefix (n := n) m) := by
  induction m with
  | zero =>
      simp [pairPrefix]
  | succ m ih =>
      have hmi' : m ≤ i := Nat.le_of_succ_le hmi
      have hi_ne_m : i ≠ m := by
        intro h
        have : m + 1 ≤ m := by
          rwa [h] at hmi
        exact (Nat.not_succ_le_self m) this
      have hcomm_prefix : Commute (pairTerm (n := n) i) (pairPrefix (n := n) m) := ih hmi'
      have hcomm_pair : Commute (pairTerm (n := n) i) (pairTerm (n := n) m) := by
        exact pairTerm_commute_of_ne (n := n) hi_ne_m
      simpa [pairPrefix_succ, mul_assoc] using (hcomm_prefix.mul_right hcomm_pair)

/-- The recursive prefix product squares to the expected scalar sign. -/
theorem pairPrefix_sq {m : ℕ} (hm : m ≤ n) :
    pairPrefix (n := n) m * pairPrefix (n := n) m
      = ((-1 : ℂ) ^ m) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n) := by
  induction m with
  | zero =>
      simp [pairPrefix]
  | succ m ih =>
      have hcomm : Commute (pairTerm (n := n) m) (pairPrefix (n := n) m) :=
        pairTerm_commute_pairPrefix (n := n) (m := m) (i := m) (by rfl)
      have hlt : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm
      change (pairPrefix (n := n) m * pairTerm (n := n) m)
          * (pairPrefix (n := n) m * pairTerm (n := n) m)
          = ((-1 : ℂ) ^ (m + 1)) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n)
      calc
        (pairPrefix (n := n) m * pairTerm (n := n) m)
            * (pairPrefix (n := n) m * pairTerm (n := n) m)
          = pairPrefix (n := n) m
              * (pairTerm (n := n) m * pairPrefix (n := n) m)
              * pairTerm (n := n) m := by
                  simp [mul_assoc]
        _ = pairPrefix (n := n) m
              * (pairPrefix (n := n) m * pairTerm (n := n) m)
              * pairTerm (n := n) m := by
                  rw [hcomm.eq]
        _ = (pairPrefix (n := n) m * pairPrefix (n := n) m)
              * (pairTerm (n := n) m * pairTerm (n := n) m) := by
                  simp [mul_assoc]
        _ = (((-1 : ℂ) ^ m) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n))
              * (- (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n)) := by
                  rw [ih (Nat.le_of_succ_le hm), pairTerm_sq (n := n) (j := m) hlt]
        _ = - (((-1 : ℂ) ^ m) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n)) := by
                  simp
        _ = ((-((-1 : ℂ) ^ m)) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n)) := by
                  exact (neg_smul (((-1 : ℂ) ^ m)) (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n)).symm
        _ = ((-1 : ℂ) ^ (m + 1)) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n) := by
                  simp [pow_succ, mul_comm]

theorem tilt_comm_pairPrefix {m j : ℕ} (hmj : m ≤ j) (hj : j < n) :
    Commute (FunctionSpace.tilt (n := n) ⟨j, hj⟩) (pairPrefix (n := n) m) := by
  induction m with
  | zero =>
      simp [pairPrefix]
  | succ m ih =>
      have hmj' : m ≤ j := Nat.le_of_succ_le hmj
      have hltj : m < j := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hmj
      have hlt : m < n := lt_of_lt_of_le hltj (Nat.le_of_lt hj)
      have hcomm_prefix : Commute (FunctionSpace.tilt (n := n) ⟨j, hj⟩) (pairPrefix (n := n) m) :=
        ih hmj'
      have hmne : m ≠ j := Nat.ne_of_lt hltj
      have hmneNat : j ≠ m := by intro h; exact hmne h.symm
      have hcomm_pair : Commute (FunctionSpace.tilt (n := n) ⟨j, hj⟩) (pairTerm (n := n) m) := by
        have hti : Commute (FunctionSpace.tilt (n := n) ⟨j, hj⟩)
            (FunctionSpace.tilt (n := n) ⟨m, hlt⟩) := by
          exact FunctionSpace.tilt_comm (n := n) (i := ⟨j, hj⟩) (j := ⟨m, hlt⟩)
        have hsi : Commute (FunctionSpace.tilt (n := n) ⟨j, hj⟩)
            (FunctionSpace.switch (n := n) ⟨m, hlt⟩) := by
          exact FunctionSpace.tilt_switch_comm_of_ne (n := n) (i := ⟨j, hj⟩) (j := ⟨m, hlt⟩) (by
            intro h; exact hmneNat (congrArg Fin.val h))
        simpa [pairTerm_of_lt (n := n) hlt] using hti.mul_right hsi
      simpa [pairPrefix_succ, mul_assoc] using (hcomm_prefix.mul_right hcomm_pair)

theorem switch_comm_pairPrefix {m j : ℕ} (hmj : m ≤ j) (hj : j < n) :
    Commute (FunctionSpace.switch (n := n) ⟨j, hj⟩) (pairPrefix (n := n) m) := by
  induction m with
  | zero =>
      simp [pairPrefix]
  | succ m ih =>
      have hmj' : m ≤ j := Nat.le_of_succ_le hmj
      have hltj : m < j := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hmj
      have hlt : m < n := lt_of_lt_of_le hltj (Nat.le_of_lt hj)
      have hcomm_prefix : Commute (FunctionSpace.switch (n := n) ⟨j, hj⟩) (pairPrefix (n := n) m) :=
        ih hmj'
      have hmne : m ≠ j := Nat.ne_of_lt hltj
      have hmneNat : j ≠ m := by intro h; exact hmne h.symm
      have hcomm_pair : Commute (FunctionSpace.switch (n := n) ⟨j, hj⟩) (pairTerm (n := n) m) := by
        have hst : Commute (FunctionSpace.switch (n := n) ⟨j, hj⟩)
            (FunctionSpace.tilt (n := n) ⟨m, hlt⟩) := by
          have h := FunctionSpace.tilt_switch_comm_of_ne (n := n) (i := ⟨m, hlt⟩) (j := ⟨j, hj⟩) (by
            intro h; exact hmneNat (congrArg Fin.val h.symm))
          simpa [Commute, mul_assoc] using h.symm
        have hss : Commute (FunctionSpace.switch (n := n) ⟨j, hj⟩)
            (FunctionSpace.switch (n := n) ⟨m, hlt⟩) := by
          exact FunctionSpace.switch_comm (n := n) (i := ⟨j, hj⟩) (j := ⟨m, hlt⟩) (by
            intro h; exact hmneNat (congrArg Fin.val h))
        simpa [pairTerm_of_lt (n := n) hlt] using (Commute.mul_right hst hss)
      simpa [pairPrefix_succ, mul_assoc] using (hcomm_prefix.mul_right hcomm_pair)

/-- Normalized phase factor used for the paper generators.

NOTE: This uses the complex scalar `Complex.I` as the phase.  In the real
doubled Hestenes/Krein picture, this corresponds to the phase axis `K = Jε`
via the bilingual dictionary (`BilingualRealHestenesDictionary`).
-/
def paperPhase (j : ℕ) : ℂ :=
  Complex.I ^ j

/-- The paper's odd generator in normalized Cantor form. -/
def paperOddGenerator (j : ℕ) (hj : j < n) : FunctionSpace n →ₗ[ℂ] FunctionSpace n :=
  paperPhase j • (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)

/-- The paper's even generator in normalized Cantor form. -/
def paperEvenGenerator (j : ℕ) (hj : j < n) : FunctionSpace n →ₗ[ℂ] FunctionSpace n :=
  paperPhase j • (FunctionSpace.switch (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)

theorem paperPhase_sq (j : ℕ) :
    paperPhase j * paperPhase j = ((-1 : ℂ) ^ j) := by
  induction j with
  | zero =>
      simp [paperPhase]
  | succ j ih =>
      calc
        paperPhase (j + 1) * paperPhase (j + 1)
          = (paperPhase j * Complex.I) * (paperPhase j * Complex.I) := by
              simp [paperPhase, pow_succ]
        _ = (paperPhase j * paperPhase j) * (Complex.I * Complex.I) := by
              ring
        _ = ((-1 : ℂ) ^ j) * (Complex.I * Complex.I) := by
              rw [ih]
        _ = ((-1 : ℂ) ^ j) * (-1) := by
              rw [Complex.I_mul_I]
        _ = ((-1 : ℂ) ^ (j + 1)) := by
              simp [pow_succ]

theorem paperOddGenerator_sq (j : ℕ) (hj : j < n) :
    paperOddGenerator (n := n) j hj * paperOddGenerator (n := n) j hj = 1 := by
  have hcomm : Commute (FunctionSpace.tilt (n := n) ⟨j, hj⟩) (pairPrefix (n := n) j) :=
    tilt_comm_pairPrefix (n := n) (m := j) (j := j) (Nat.le_refl j) hj
  have hpair_sq : pairPrefix (n := n) j * pairPrefix (n := n) j
      = ((-1 : ℂ) ^ j) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n) :=
    pairPrefix_sq (n := n) (m := j) (Nat.le_of_lt hj)
  calc
    paperOddGenerator (n := n) j hj * paperOddGenerator (n := n) j hj
      = (paperPhase j * paperPhase j) •
          ((FunctionSpace.tilt (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)
            * (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)) := by
              simp [paperOddGenerator, mul_smul]
    _ = ((-1 : ℂ) ^ j) •
          ((FunctionSpace.tilt (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)
            * (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)) := by
              rw [paperPhase_sq]
    _ = ((-1 : ℂ) ^ j) •
          ((FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
            * (pairPrefix (n := n) j * pairPrefix (n := n) j)) := by
              simpa [mul_assoc] using
                (hcomm.symm.mul_mul_mul_comm
                  (a := FunctionSpace.tilt (n := n) ⟨j, hj⟩)
                  (d := pairPrefix (n := n) j))
    _ = ((-1 : ℂ) ^ j) •
          (((FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩))
            * (((-1 : ℂ) ^ j) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n))) := by
              rw [hpair_sq]
    _ = 1 := by
              have hsign : ((-1 : ℂ) ^ j) * ((-1 : ℂ) ^ j) = 1 := by
                rw [← mul_pow]
                simp
              simp [tilt_sq, smul_smul, hsign]

theorem paperEvenGenerator_sq (j : ℕ) (hj : j < n) :
    paperEvenGenerator (n := n) j hj * paperEvenGenerator (n := n) j hj = 1 := by
  have hcomm : Commute (FunctionSpace.switch (n := n) ⟨j, hj⟩) (pairPrefix (n := n) j) :=
    switch_comm_pairPrefix (n := n) (m := j) (j := j) (Nat.le_refl j) hj
  have hpair_sq : pairPrefix (n := n) j * pairPrefix (n := n) j
      = ((-1 : ℂ) ^ j) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n) :=
    pairPrefix_sq (n := n) (m := j) (Nat.le_of_lt hj)
  calc
    paperEvenGenerator (n := n) j hj * paperEvenGenerator (n := n) j hj
      = (paperPhase j * paperPhase j) •
          ((FunctionSpace.switch (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)
            * (FunctionSpace.switch (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)) := by
              simp [paperEvenGenerator, mul_smul]
    _ = ((-1 : ℂ) ^ j) •
          ((FunctionSpace.switch (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)
            * (FunctionSpace.switch (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)) := by
              rw [paperPhase_sq]
    _ = ((-1 : ℂ) ^ j) •
          ((FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩)
            * (pairPrefix (n := n) j * pairPrefix (n := n) j)) := by
              simpa [mul_assoc] using
                (hcomm.symm.mul_mul_mul_comm
                  (a := FunctionSpace.switch (n := n) ⟨j, hj⟩)
                  (d := pairPrefix (n := n) j))
    _ = ((-1 : ℂ) ^ j) •
          (((FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩))
            * (((-1 : ℂ) ^ j) • (1 : FunctionSpace n →ₗ[ℂ] FunctionSpace n))) := by
              rw [hpair_sq]
    _ = 1 := by
              have hsign : ((-1 : ℂ) ^ j) * ((-1 : ℂ) ^ j) = 1 := by
                rw [← mul_pow]
                simp
              simp [switch_sq, smul_smul, hsign]

/-- The normalized odd and even generators at the same slot anticommute. -/
theorem paperOddGenerator_anticomm_paperEvenGenerator (j : ℕ) (hj : j < n) :
    paperOddGenerator (n := n) j hj * paperEvenGenerator (n := n) j hj
      = - (paperEvenGenerator (n := n) j hj * paperOddGenerator (n := n) j hj) := by
  have hti : Commute (FunctionSpace.tilt (n := n) ⟨j, hj⟩) (pairPrefix (n := n) j) :=
    tilt_comm_pairPrefix (n := n) (m := j) (j := j) (Nat.le_refl j) hj
  have hst : Commute (FunctionSpace.switch (n := n) ⟨j, hj⟩) (pairPrefix (n := n) j) :=
    switch_comm_pairPrefix (n := n) (m := j) (j := j) (Nat.le_refl j) hj
  have hOE :
      paperOddGenerator (n := n) j hj * paperEvenGenerator (n := n) j hj
        = ((-1 : ℂ) ^ j) •
            ((FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩)
              * (pairPrefix (n := n) j * pairPrefix (n := n) j)) := by
    calc
      paperOddGenerator (n := n) j hj * paperEvenGenerator (n := n) j hj
        = (paperPhase j * paperPhase j) •
            ((FunctionSpace.tilt (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)
              * (FunctionSpace.switch (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)) := by
                simp [paperOddGenerator, paperEvenGenerator, mul_smul]
      _ = ((-1 : ℂ) ^ j) •
            ((FunctionSpace.tilt (n := n) ⟨j, hj⟩ * FunctionSpace.switch (n := n) ⟨j, hj⟩)
              * (pairPrefix (n := n) j * pairPrefix (n := n) j)) := by
                rw [paperPhase_sq]
                simpa [mul_assoc] using
                  (hst.symm.mul_mul_mul_comm
                    (a := FunctionSpace.tilt (n := n) ⟨j, hj⟩)
                    (d := pairPrefix (n := n) j))
  have hEO :
      paperEvenGenerator (n := n) j hj * paperOddGenerator (n := n) j hj
        = ((-1 : ℂ) ^ j) •
            ((FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
              * (pairPrefix (n := n) j * pairPrefix (n := n) j)) := by
    calc
      paperEvenGenerator (n := n) j hj * paperOddGenerator (n := n) j hj
        = (paperPhase j * paperPhase j) •
            ((FunctionSpace.switch (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)
              * (FunctionSpace.tilt (n := n) ⟨j, hj⟩ * pairPrefix (n := n) j)) := by
                simp [paperOddGenerator, paperEvenGenerator, mul_smul]
      _ = ((-1 : ℂ) ^ j) •
            ((FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
              * (pairPrefix (n := n) j * pairPrefix (n := n) j)) := by
                rw [paperPhase_sq]
                simpa [mul_assoc] using
                  (hti.symm.mul_mul_mul_comm
                    (a := FunctionSpace.switch (n := n) ⟨j, hj⟩)
                    (d := pairPrefix (n := n) j))
  have hneg :
      (-(FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩))
          * (pairPrefix (n := n) j * pairPrefix (n := n) j)
        = - ((FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
            * (pairPrefix (n := n) j * pairPrefix (n := n) j)) := by
    exact (neg_mul
      (FunctionSpace.switch (n := n) ⟨j, hj⟩ * FunctionSpace.tilt (n := n) ⟨j, hj⟩)
      (pairPrefix (n := n) j * pairPrefix (n := n) j)).symm
  rw [hOE, hEO]
  rw [tilt_switch_anticomm (n := n) ⟨j, hj⟩]
  rw [hneg]
  rw [smul_neg]

/-- Paper-facing finite endpoint basis. -/
noncomputable def endpointBasis (n : ℕ) :
    Module.Basis (CantorAddress n) ℂ (FunctionSpace n) :=
  InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n)

@[simp] theorem endpointBasis_apply (n : ℕ) (x : CantorAddress n) :
    endpointBasis (n := n) x = Pi.single x (1 : ℂ) :=
  InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis_apply (n := n) x

theorem endpointBasis_repr_apply (n : ℕ) (f : FunctionSpace n) (x : CantorAddress n) :
    (endpointBasis (n := n)).repr f x = f x :=
  InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis_repr_apply (n := n) f x

/-- A pure tensor of endpoint basis vectors is the corresponding tensor basis vector. -/
@[simp] theorem endpointBasis_tensorProduct_apply {m n : ℕ}
    (x : CantorAddress m) (y : CantorAddress n) :
    (endpointBasis (n := m)).tensorProduct (endpointBasis (n := n)) (x, y)
      = (endpointBasis (n := m) x) ⊗ₜ (endpointBasis (n := n) y) := by
  simp [endpointBasis]

/-- The finite endpoint bases satisfy the tensor-product matrix identity from Mathlib. -/
theorem endpointBasis_tensorProduct_toMatrix {m n : ℕ}
    (f : FunctionSpace m →ₗ[ℂ] FunctionSpace m)
    (g : FunctionSpace n →ₗ[ℂ] FunctionSpace n) :
    LinearMap.toMatrix
        ((endpointBasis (n := m)).tensorProduct (endpointBasis (n := n)))
        ((endpointBasis (n := m)).tensorProduct (endpointBasis (n := n)))
        (TensorProduct.map f g)
      =
      LinearMap.toMatrix (endpointBasis (n := m)) (endpointBasis (n := m)) f ⊗ₖ
        LinearMap.toMatrix (endpointBasis (n := n)) (endpointBasis (n := n)) g := by
  simpa using
    (TensorProduct.toMatrix_map
      (bM := endpointBasis (n := m)) (bN := endpointBasis (n := n))
      (bM' := endpointBasis (n := m)) (bN' := endpointBasis (n := n)) f g)

end FunctionSpace

/-- The paper's `n = 1` finite Pauli bridge is theorem-backed. -/
theorem cl11PauliBridge_target :
    (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma
        ⟨0, by decide⟩ = Eplus ∧
      (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma
        ⟨1, by decide⟩ = J1 ∧
      (∀ i : Fin (2 * 1),
        (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma i *
          (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma i = 1) ∧
      (∀ {i j : Fin (2 * 1)}, i ≠ j →
        (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma i *
            (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma j +
          (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma j *
            (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma i = 0) :=
by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge_psiGamma_zero
  · exact InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge_psiGamma_one
  · intro i
    exact
      (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).clifford_sq i
  · intro i j hij
    rw [
      (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).clifford_anticomm i j hij]
    simp

/-- The first paper generator in the `n = 1` matrix base case. -/
theorem cl11PauliBridge_psiGamma_zero :
    (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma ⟨0, by decide⟩
      = Eplus :=
  InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge_psiGamma_zero

/-- The second paper generator in the `n = 1` matrix base case. -/
theorem cl11PauliBridge_psiGamma_one :
    (InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge).psiGamma ⟨1, by decide⟩
      = J1 :=
  InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge_psiGamma_one

/-- The `Cl(1,1)` matrix isomorphism underlying the paper's base case. -/
noncomputable def cl11PauliMatrixEquiv :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 ≃ₐ[ℝ] Mat2 :=
  InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat

/-- The concrete `Cl(1,1)` map sends `e₁` to the first Pauli matrix. -/
theorem cl11ToMat_map_e1 :
    InfoGeometry.Clifford.Cl11Matrix.cl11ToMat
      (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) = Eplus := by
  rw [InfoGeometry.Clifford.Cl11Matrix.cl11ToMat]
  simp [InfoGeometry.Clifford.Cl11Matrix.gen, Eplus, Eminus]

/-- The concrete `Cl(1,1)` map sends `e₂` to the second Pauli matrix. -/
theorem cl11ToMat_map_e2 :
    InfoGeometry.Clifford.Cl11Matrix.cl11ToMat
      (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1)) = Eminus := by
  rw [InfoGeometry.Clifford.Cl11Matrix.cl11ToMat]
  simp [InfoGeometry.Clifford.Cl11Matrix.gen, Eplus, Eminus]

/-- The `Cl(1,1)` generator `e₁` maps to the first real Pauli matrix. -/
theorem cl11PauliMatrixEquiv_map_e1 :
    cl11PauliMatrixEquiv (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) = Eplus :=
  by
    simpa [cl11PauliMatrixEquiv] using cl11ToMat_map_e1

/-- The `Cl(1,1)` generator `e₂` maps to the second real Pauli matrix. -/
theorem cl11PauliMatrixEquiv_map_e2 :
    cl11PauliMatrixEquiv (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1)) = Eminus :=
  by
    simpa [cl11PauliMatrixEquiv] using cl11ToMat_map_e2

/-- The `Cl(1,1)` matrix representation decomposes in the Pauli basis. -/
theorem cl11PauliMatrixEquiv_decompose (M : Mat2) :
    M =
      (InfoGeometry.Clifford.Cl11Matrix.alpha M) • (1 : Mat2) +
      (InfoGeometry.Clifford.Cl11Matrix.beta M) • Eplus +
      (InfoGeometry.Clifford.Cl11Matrix.gamma M) • Eminus +
      (InfoGeometry.Clifford.Cl11Matrix.delta M) • J1 :=
  InfoGeometry.Clifford.Cl11Matrix.mat2_decompose M

end InfoGeometry.Canonical.CelikKocakPaperFormalism
