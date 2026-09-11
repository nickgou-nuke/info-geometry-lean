import InfoGeometry.Canonical.ModularZ2CubeGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Operator-valued grand-canonical chiral generators

This file is the abstract noncommutative layer.  The two sheet number
operators and both chemical potentials are elements of the same ring; no
scalar diagonalisation is used.  Concrete CAR and Clifford realizations are
provided by their owner files.
-/

namespace InfoGeometry.OperatorAlgebra

variable {A : Type*} [Ring A]

def grandCanonicalCommutator (x y : A) : A := x * y - y * x

def totalNumber (Nplus Nminus : A) : A := Nplus + Nminus

def chiralCharge (Nplus Nminus : A) : A := Nplus - Nminus

def grandCanonicalGenerator
    (H Nplus Nminus μ μχ : A) : A :=
  H - μ * totalNumber Nplus Nminus - μχ * chiralCharge Nplus Nminus

def modularGrandCanonicalGenerator
    (β H Nplus Nminus μ μχ : A) : A :=
  β * grandCanonicalGenerator H Nplus Nminus μ μχ

theorem sheetNumber_reconstruct_plus
    (t Nplus Nminus : A) (ht : t + t = 1) :
    t * totalNumber Nplus Nminus +
        t * chiralCharge Nplus Nminus = Nplus := by
  unfold totalNumber chiralCharge
  calc
    t * (Nplus + Nminus) + t * (Nplus - Nminus) =
        (t + t) * Nplus := by noncomm_ring
    _ = Nplus := by rw [ht, one_mul]

theorem sheetNumber_reconstruct_minus
    (t Nplus Nminus : A) (ht : t + t = 1) :
    t * totalNumber Nplus Nminus -
        t * chiralCharge Nplus Nminus = Nminus := by
  unfold totalNumber chiralCharge
  calc
    t * (Nplus + Nminus) - t * (Nplus - Nminus) =
        (t + t) * Nminus := by noncomm_ring
    _ = Nminus := by rw [ht, one_mul]

theorem chemicalPotentialTerm_sheet_split
    (Nplus Nminus μ μχ : A) :
    μ * totalNumber Nplus Nminus + μχ * chiralCharge Nplus Nminus =
      (μ + μχ) * Nplus + (μ - μχ) * Nminus := by
  unfold totalNumber chiralCharge
  noncomm_ring

theorem grandCanonicalGenerator_sheet_split
    (H Nplus Nminus μ μχ : A) :
    grandCanonicalGenerator H Nplus Nminus μ μχ =
      H - (μ + μχ) * Nplus - (μ - μχ) * Nminus := by
  unfold grandCanonicalGenerator totalNumber chiralCharge
  noncomm_ring

theorem RingHom.map_totalNumber
    {B : Type*} [Ring B] (φ : A →+* B) (Nplus Nminus : A) :
    φ (totalNumber Nplus Nminus) =
      totalNumber (φ Nplus) (φ Nminus) := by
  simp [totalNumber]

theorem RingHom.map_chiralCharge
    {B : Type*} [Ring B] (φ : A →+* B) (Nplus Nminus : A) :
    φ (chiralCharge Nplus Nminus) =
      chiralCharge (φ Nplus) (φ Nminus) := by
  simp [chiralCharge]

theorem RingHom.map_grandCanonicalGenerator
    {B : Type*} [Ring B] (φ : A →+* B)
    (H Nplus Nminus μ μχ : A) :
    φ (grandCanonicalGenerator H Nplus Nminus μ μχ) =
      grandCanonicalGenerator (φ H) (φ Nplus) (φ Nminus)
        (φ μ) (φ μχ) := by
  simp [grandCanonicalGenerator, totalNumber, chiralCharge]

theorem RingHom.map_modularGrandCanonicalGenerator
    {B : Type*} [Ring B] (φ : A →+* B)
    (β H Nplus Nminus μ μχ : A) :
    φ (modularGrandCanonicalGenerator β H Nplus Nminus μ μχ) =
      modularGrandCanonicalGenerator (φ β) (φ H) (φ Nplus) (φ Nminus)
        (φ μ) (φ μχ) := by
  simp [modularGrandCanonicalGenerator, grandCanonicalGenerator,
    totalNumber, chiralCharge]

theorem RingHom.map_grandCanonicalCommutator
    {B : Type*} [Ring B] (φ : A →+* B) (x y : A) :
    φ (grandCanonicalCommutator x y) =
      grandCanonicalCommutator (φ x) (φ y) := by
  simp [grandCanonicalCommutator]

theorem RingHom.map_grandCanonicalConservation
    {B : Type*} [Ring B] (φ : A →+* B)
    (G Q : A) (hGQ : grandCanonicalCommutator G Q = 0) :
    grandCanonicalCommutator (φ G) (φ Q) = 0 := by
  rw [← φ.map_zero, ← hGQ, RingHom.map_grandCanonicalCommutator]

theorem grandCanonicalCommutator_add_left (x y z : A) :
    grandCanonicalCommutator (x + y) z =
      grandCanonicalCommutator x z + grandCanonicalCommutator y z := by
  unfold grandCanonicalCommutator
  noncomm_ring

theorem grandCanonicalCommutator_sub_left (x y z : A) :
    grandCanonicalCommutator (x - y) z =
      grandCanonicalCommutator x z - grandCanonicalCommutator y z := by
  unfold grandCanonicalCommutator
  noncomm_ring

theorem grandCanonicalCommutator_mul_central_left
    (c x y : A) (hc : ∀ z : A, c * z = z * c) :
    grandCanonicalCommutator (c * x) y = c * grandCanonicalCommutator x y := by
  unfold grandCanonicalCommutator
  calc
    c * x * y - y * (c * x) = c * (x * y) - c * (y * x) := by
      rw [mul_assoc, ← mul_assoc y c x, ← hc y]
      congr 1
      rw [← mul_assoc]
    _ = c * (x * y - y * x) := by rw [mul_sub]

theorem grandCanonicalCommutator_self (x : A) :
    grandCanonicalCommutator x x = 0 := by
  unfold grandCanonicalCommutator
  exact sub_self (x * x)

theorem grandCanonicalCommutator_totalNumber_chiralCharge
    (Nplus Nminus : A)
    (hcomm : Nplus * Nminus = Nminus * Nplus) :
    grandCanonicalCommutator (totalNumber Nplus Nminus)
      (chiralCharge Nplus Nminus) = 0 := by
  unfold grandCanonicalCommutator totalNumber chiralCharge
  rw [add_mul, mul_sub, sub_mul, mul_add]
  rw [hcomm]
  noncomm_ring

theorem grandCanonicalCommutator_grandCanonicalGenerator_chiralCharge
    (H Nplus Nminus μ μχ : A)
    (hH : grandCanonicalCommutator H (chiralCharge Nplus Nminus) = 0)
    (hN : Nplus * Nminus = Nminus * Nplus)
    (hμ : ∀ z : A, μ * z = z * μ)
    (hμχ : ∀ z : A, μχ * z = z * μχ) :
    grandCanonicalCommutator
        (grandCanonicalGenerator H Nplus Nminus μ μχ)
        (chiralCharge Nplus Nminus) = 0 := by
  unfold grandCanonicalGenerator
  rw [grandCanonicalCommutator_sub_left, grandCanonicalCommutator_sub_left,
    grandCanonicalCommutator_mul_central_left μ
      (totalNumber Nplus Nminus) (chiralCharge Nplus Nminus) hμ,
    grandCanonicalCommutator_mul_central_left μχ
      (chiralCharge Nplus Nminus) (chiralCharge Nplus Nminus) hμχ]
  rw [hH, grandCanonicalCommutator_totalNumber_chiralCharge Nplus Nminus hN,
    grandCanonicalCommutator_self]
  simp

theorem grandCanonicalCommutator_modularGrandCanonicalGenerator_chiralCharge
    (β H Nplus Nminus μ μχ : A)
    (hH : grandCanonicalCommutator H (chiralCharge Nplus Nminus) = 0)
    (hN : Nplus * Nminus = Nminus * Nplus)
    (hβ : ∀ z : A, β * z = z * β)
    (hμ : ∀ z : A, μ * z = z * μ)
    (hμχ : ∀ z : A, μχ * z = z * μχ) :
    grandCanonicalCommutator
        (modularGrandCanonicalGenerator β H Nplus Nminus μ μχ)
        (chiralCharge Nplus Nminus) = 0 := by
  unfold modularGrandCanonicalGenerator
  rw [grandCanonicalCommutator_mul_central_left β
    (grandCanonicalGenerator H Nplus Nminus μ μχ)
    (chiralCharge Nplus Nminus) hβ]
  rw [grandCanonicalCommutator_grandCanonicalGenerator_chiralCharge
    H Nplus Nminus μ μχ hH hN hμ hμχ]
  simp

theorem totalNumber_isFullyEven
    {Γ_R Γ_χ Γ_N Nplus Nminus : A}
    (hPlus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nplus)
    (hMinus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nminus) :
    ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
      (totalNumber Nplus Nminus) := by
  unfold totalNumber ModularZ2CubeGrading.isFullyEven at *
  rcases hPlus with ⟨hPR, hPχ, hPN⟩
  rcases hMinus with ⟨hMR, hMχ, hMN⟩
  exact ⟨ModularZ2CubeGrading.hasGrading_add hPR hMR,
    ModularZ2CubeGrading.hasGrading_add hPχ hMχ,
    ModularZ2CubeGrading.hasGrading_add hPN hMN⟩

theorem chiralCharge_isFullyEven
    {Γ_R Γ_χ Γ_N Nplus Nminus : A}
    (hPlus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nplus)
    (hMinus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nminus) :
    ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
      (chiralCharge Nplus Nminus) := by
  unfold chiralCharge ModularZ2CubeGrading.isFullyEven at *
  rcases hPlus with ⟨hPR, hPχ, hPN⟩
  rcases hMinus with ⟨hMR, hMχ, hMN⟩
  exact ⟨ModularZ2CubeGrading.hasGrading_sub hPR hMR,
    ModularZ2CubeGrading.hasGrading_sub hPχ hMχ,
    ModularZ2CubeGrading.hasGrading_sub hPN hMN⟩

theorem grandCanonicalGenerator_isFullyEven
    {Γ_R Γ_χ Γ_N H Nplus Nminus μ μχ : A}
    (hH : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N H)
    (hPlus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nplus)
    (hMinus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nminus)
    (hμ : ∀ z : A, μ * z = z * μ)
    (hμχ : ∀ z : A, μχ * z = z * μχ) :
    ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
      (grandCanonicalGenerator H Nplus Nminus μ μχ) := by
  unfold grandCanonicalGenerator ModularZ2CubeGrading.isFullyEven
  rcases hH with ⟨hHR, hHχ, hHN⟩
  have hTot := totalNumber_isFullyEven hPlus hMinus
  have hCharge := chiralCharge_isFullyEven hPlus hMinus
  exact ⟨ModularZ2CubeGrading.hasGrading_sub
      (ModularZ2CubeGrading.hasGrading_sub hHR
        (ModularZ2CubeGrading.hasGrading_mul_of_commute hTot.1 (hμ Γ_R)))
      (ModularZ2CubeGrading.hasGrading_mul_of_commute hCharge.1 (hμχ Γ_R)),
    ModularZ2CubeGrading.hasGrading_sub
      (ModularZ2CubeGrading.hasGrading_sub hHχ
        (ModularZ2CubeGrading.hasGrading_mul_of_commute hTot.2.1 (hμ Γ_χ)))
      (ModularZ2CubeGrading.hasGrading_mul_of_commute hCharge.2.1 (hμχ Γ_χ)),
    ModularZ2CubeGrading.hasGrading_sub
      (ModularZ2CubeGrading.hasGrading_sub hHN
        (ModularZ2CubeGrading.hasGrading_mul_of_commute hTot.2.2 (hμ Γ_N)))
      (ModularZ2CubeGrading.hasGrading_mul_of_commute hCharge.2.2 (hμχ Γ_N))⟩

end InfoGeometry.OperatorAlgebra
