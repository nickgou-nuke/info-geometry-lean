/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesKreinMatrixBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesCircularSheetCARFinite
import InfoGeometry.Canonical.HestenesRealGradedTensorRepresentation

/-! # Circular CAR transported into native `Cl⁺(1,3)` -/

noncomputable section
namespace HestenesCircularCARTransport

open HestenesCl14
open HestenesEvenPauliEquiv
open HestenesPauliSheetBridge
open HestenesCircularSheetCAR
open InfoGeometry.Canonical.HestenesRealGradedTensorRepresentation

def cliffordUPlus : ClPlus14 := clPlusPauliAlgEquiv.symm uPlus
def cliffordUMinus : ClPlus14 := clPlusPauliAlgEquiv.symm uMinus
def cliffordCPlus : ClPlus14 := clPlusPauliAlgEquiv.symm cPlus
def cliffordCMinus : ClPlus14 := clPlusPauliAlgEquiv.symm cMinus

@[simp] theorem map_cliffordUPlus :
    clPlusPauliAlgEquiv cliffordUPlus = uPlus := by
  simp [cliffordUPlus]

@[simp] theorem map_cliffordUMinus :
    clPlusPauliAlgEquiv cliffordUMinus = uMinus := by
  simp [cliffordUMinus]

@[simp] theorem map_cliffordCPlus :
    clPlusPauliAlgEquiv cliffordCPlus = cPlus := by
  simp [cliffordCPlus]

@[simp] theorem map_cliffordCMinus :
    clPlusPauliAlgEquiv cliffordCMinus = cMinus := by
  simp [cliffordCMinus]

@[simp] theorem cliffordUPlus_sq : cliffordUPlus * cliffordUPlus = cliffordUPlus := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordUMinus_sq : cliffordUMinus * cliffordUMinus = cliffordUMinus := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordUPlus_cliffordUMinus :
    cliffordUPlus * cliffordUMinus = 0 := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordUMinus_cliffordUPlus :
    cliffordUMinus * cliffordUPlus = 0 := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordUPlus_add_cliffordUMinus :
    cliffordUPlus + cliffordUMinus = 1 := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordCPlus_sq : cliffordCPlus * cliffordCPlus = 0 := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordCMinus_sq : cliffordCMinus * cliffordCMinus = 0 := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordCPlus_cliffordCMinus :
    cliffordCPlus * cliffordCMinus = cliffordUPlus := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordCMinus_cliffordCPlus :
    cliffordCMinus * cliffordCPlus = cliffordUMinus := by
  apply clPlusPauliAlgEquiv.injective
  simp

theorem native_clifford_circular_car_packet :
    cliffordUPlus * cliffordUPlus = cliffordUPlus ∧
      cliffordUMinus * cliffordUMinus = cliffordUMinus ∧
      cliffordUPlus * cliffordUMinus = 0 ∧
      cliffordUMinus * cliffordUPlus = 0 ∧
      cliffordUPlus + cliffordUMinus = 1 ∧
      cliffordCPlus * cliffordCPlus = 0 ∧
      cliffordCMinus * cliffordCMinus = 0 ∧
      cliffordCPlus * cliffordCMinus = cliffordUPlus ∧
      cliffordCMinus * cliffordCPlus = cliffordUMinus := by
  exact ⟨cliffordUPlus_sq, cliffordUMinus_sq,
    cliffordUPlus_cliffordUMinus, cliffordUMinus_cliffordUPlus,
    cliffordUPlus_add_cliffordUMinus, cliffordCPlus_sq,
    cliffordCMinus_sq, cliffordCPlus_cliffordCMinus,
    cliffordCMinus_cliffordCPlus⟩

/-- The circular CAR anticommutator with real coefficients is realized
inside the real Hestenes even algebra. No complex coefficient field is used;
the Clifford carrier and the coefficient scalars are both real. -/
theorem real_circularCAR_anticommutator (r s : ℝ) :
    (r • cliffordCPlus) * (s • cliffordCMinus) +
      (s • cliffordCMinus) * (r • cliffordCPlus) =
        (r * s) • (1 : ClPlus14) := by
  apply clPlusPauliAlgEquiv.injective
  change clPlusToPauli
      ((r • cliffordCPlus) * (s • cliffordCMinus) +
        (s • cliffordCMinus) * (r • cliffordCPlus)) =
    clPlusToPauli ((r * s) • (1 : ClPlus14))
  rw [map_add, map_mul, map_mul, map_smul, map_smul, map_smul, map_one]
  have hplus : clPlusToPauli cliffordCPlus = cPlus := by
    change clPlusPauliAlgEquiv cliffordCPlus = cPlus
    exact map_cliffordCPlus
  have hminus : clPlusToPauli cliffordCMinus = cMinus := by
    change clPlusPauliAlgEquiv cliffordCMinus = cMinus
    exact map_cliffordCMinus
  rw [hplus, hminus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
    HestenesCircularSheetCAR.cPlus_cMinus,
    HestenesCircularSheetCAR.cMinus_cPlus]
  rw [mul_comm s r, ← smul_add,
    HestenesCircularSheetCAR.uPlus_add_uMinus]

/-- The same real-coefficient CAR identity acts on the existing doubled
Krein carrier through the native Hestenes representation. -/
theorem real_circularCAR_anticommutator_on_doubledKrein (r s : ℝ) :
    hestenesEvenOnDoubledKrein (r • cliffordCPlus) *
        hestenesEvenOnDoubledKrein (s • cliffordCMinus) +
      hestenesEvenOnDoubledKrein (s • cliffordCMinus) *
        hestenesEvenOnDoubledKrein (r • cliffordCPlus) =
      hestenesEvenOnDoubledKrein ((r * s) • (1 : ClPlus14)) := by
  calc
    _ = hestenesEvenOnDoubledKrein
        ((r • cliffordCPlus) * (s • cliffordCMinus) +
          (s • cliffordCMinus) * (r • cliffordCPlus)) := by
      simp only [map_add, map_mul]
    _ = hestenesEvenOnDoubledKrein
        ((r * s) • (1 : ClPlus14)) := by
      rw [real_circularCAR_anticommutator]

end HestenesCircularCARTransport
end noncomputable section
