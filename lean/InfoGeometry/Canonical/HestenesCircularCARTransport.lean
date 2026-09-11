import InfoGeometry.Canonical.HestenesKreinMatrixBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesCircularSheetCARFinite

/-! # Circular CAR transported into native `Cl⁺(1,3)` -/

noncomputable section
namespace HestenesCircularCARTransport

open HestenesCl14
open HestenesEvenPauliEquiv
open HestenesCircularSheetCAR

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

end HestenesCircularCARTransport
end noncomputable section
