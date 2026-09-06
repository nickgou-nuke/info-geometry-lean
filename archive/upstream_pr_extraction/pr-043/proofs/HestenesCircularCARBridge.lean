import proofs.HestenesEvenPauliEquiv
import proofs.CircularCARQuarticCapstone

/-!
# Real Clifford pullback of the circular Pauli/CAR capstone

The matrix CAR identities live in the associative `M₂(ℂ)` carrier.  This
owner transports them through the independently proved real algebra
 equivalence `Cl⁺(1,3) ≃ₐ[ℝ] M₂(ℂ)`.  It does not identify the transported
associative product with any nonassociative split-octonion product.
-/

noncomputable section
namespace HestenesCircularCARBridge

open HestenesCl14 HestenesEvenPauliEquiv HestenesPauliSheetBridge
open HestenesCircularSheetCAR CircularCARQuarticCapstone
open TwoSheetThreeColorWeyl TwelveFoldSheetColorOmega

abbrev EvenAlgebra := ClPlus14
abbrev Sheet := M2C

/-- Clifford pullbacks of the matrix Peirce/CAR generators. -/
def clUPlus : EvenAlgebra := clPlusPauliAlgEquiv.symm uPlus
def clUMinus : EvenAlgebra := clPlusPauliAlgEquiv.symm uMinus
def clCPlus : EvenAlgebra := clPlusPauliAlgEquiv.symm cPlus
def clCMinus : EvenAlgebra := clPlusPauliAlgEquiv.symm cMinus

def clOmegaChi : EvenAlgebra := clPlusPauliAlgEquiv.symm omegaSheet
def clOmegaChiInv : EvenAlgebra := clPlusPauliAlgEquiv.symm omegaChiInv

def clComplexSmul (z : ℂ) (x : EvenAlgebra) : EvenAlgebra :=
  liftComplexCoeff z x

@[simp] theorem map_clComplexSmul (z : ℂ) (x : EvenAlgebra) :
    clPlusPauliAlgEquiv (clComplexSmul z x) =
      z • clPlusPauliAlgEquiv x := by
  change clPlusToPauli (liftComplexCoeff z x) =
    z • clPlusToPauli x
  exact clPlusToPauli_liftComplexCoeff z x

@[simp] theorem map_clUPlus :
    clPlusPauliAlgEquiv clUPlus = uPlus := by
  simp [clUPlus]

@[simp] theorem map_clUMinus :
    clPlusPauliAlgEquiv clUMinus = uMinus := by
  simp [clUMinus]

@[simp] theorem map_clCPlus :
    clPlusPauliAlgEquiv clCPlus = cPlus := by
  simp [clCPlus]

@[simp] theorem map_clCMinus :
    clPlusPauliAlgEquiv clCMinus = cMinus := by
  simp [clCMinus]

@[simp] theorem map_clOmegaChi :
    clPlusPauliAlgEquiv clOmegaChi = omegaSheet := by
  simp [clOmegaChi]

@[simp] theorem map_clOmegaChiInv :
    clPlusPauliAlgEquiv clOmegaChiInv = omegaChiInv := by
  simp [clOmegaChiInv]

@[simp] theorem clUPlus_sq : clUPlus * clUPlus = clUPlus := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clUMinus_sq : clUMinus * clUMinus = clUMinus := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clUPlus_clUMinus : clUPlus * clUMinus = 0 := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clUMinus_clUPlus : clUMinus * clUPlus = 0 := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clUPlus_add_clUMinus :
    clUPlus + clUMinus = (1 : EvenAlgebra) := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clCPlus_sq : clCPlus * clCPlus = 0 := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clCMinus_sq : clCMinus * clCMinus = 0 := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clCPlus_clCMinus : clCPlus * clCMinus = clUPlus := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clCMinus_clCPlus : clCMinus * clCPlus = clUMinus := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clOmegaChi_clOmegaChiInv :
    clOmegaChi * clOmegaChiInv = (1 : EvenAlgebra) := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem clOmegaChiInv_clOmegaChi :
    clOmegaChiInv * clOmegaChi = (1 : EvenAlgebra) := by
  apply clPlusPauliAlgEquiv.injective
  simp

theorem clOmegaChi_sq :
    clOmegaChi ^ 2 = clPlusPauliAlgEquiv.symm sheetGamma := by
  apply clPlusPauliAlgEquiv.injective
  rw [map_pow, map_clOmegaChi, AlgEquiv.apply_symm_apply]
  exact omegaSheet_sq

theorem clOmegaChi_four :
    clOmegaChi ^ 4 = (1 : EvenAlgebra) := by
  apply clPlusPauliAlgEquiv.injective
  simpa [pow_two] using omegaSheet_four

theorem clOmegaChi_clCPlus_phase :
    clOmegaChi * clCPlus * clOmegaChiInv =
      clComplexSmul (-Complex.I) clCPlus := by
  apply clPlusPauliAlgEquiv.injective
  simp

theorem clOmegaChi_clCMinus_phase :
    clOmegaChi * clCMinus * clOmegaChiInv =
      clComplexSmul Complex.I clCMinus := by
  apply clPlusPauliAlgEquiv.injective
  simp

theorem hestenes_circular_car_bridge_packet :
    clCPlus * clCPlus = 0 ∧
      clCMinus * clCMinus = 0 ∧
      clCPlus * clCMinus = clUPlus ∧
      clCMinus * clCPlus = clUMinus ∧
      clOmegaChi * clCPlus * clOmegaChiInv =
        clComplexSmul (-Complex.I) clCPlus ∧
      clOmegaChi * clCMinus * clOmegaChiInv =
        clComplexSmul Complex.I clCMinus := by
  exact ⟨clCPlus_sq, clCMinus_sq, clCPlus_clCMinus,
    clCMinus_clCPlus, clOmegaChi_clCPlus_phase,
    clOmegaChi_clCMinus_phase⟩

end HestenesCircularCARBridge
end noncomputable section
