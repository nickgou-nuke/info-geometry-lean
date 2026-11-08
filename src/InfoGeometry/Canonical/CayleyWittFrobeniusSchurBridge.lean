import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Cayley-Witt Operator, Peirce Defect Parity, and the Frobenius-Schur Identity

This module formalizes the exact foundational identity connecting the Cayley involution $C$,
the Witt complex structure $K$, and the Peirce defect parity $M = (-1)^{F_P}$:

$$(C K)^2 = (-1)^{F_P} \cdot I = M \cdot I$$

This rigorously establishes that:
1. **Longitudinal Sector ($F_P = 0$, Time / Mass):**
   $$(C K)^2 = +I \implies \nu = +1 \quad (\text{Real / Orthogonal / Majorana})$$
2. **Transverse Sector ($F_P = 1$, Space / Spin):**
   $$(C K)^2 = -I \implies \nu = -1 \quad (\text{Pseudoreal / Quaternionic / Kramers})$$

The operator identities below are checked by Lean.  Frobenius--Schur and
Majorana interpretations require the explicit representation data supplied
by downstream owners.
-/

namespace InfoGeometry.Canonical.CayleyWittFrobeniusSchur

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Abstract Cayley-Witt-Peirce operator datum on a module M over R -/
structure CayleyWittDatum (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  /-- Cayley involution C -/
  C : M →ₗ[R] M
  /-- C is an involution: C² = I -/
  C_sq : C.comp C = LinearMap.id
  /-- Witt complex structure K -/
  K : M →ₗ[R] M
  /-- K is a complex structure: K² = -I -/
  K_sq : K.comp K = -LinearMap.id
  /-- Peirce parity sign s ∈ R (s = +1 for F_P = 0, s = -1 for F_P = 1) -/
  s : R
  /-- The twisted Cayley-Hestenes commutation relation: C K = -s • (K C) -/
  twisted_comm : C.comp K = (-s) • (K.comp C)

/-- The composite real CPT / modular operator J = C ∘ K -/
def J_operator (D : CayleyWittDatum R M) : M →ₗ[R] M :=
  D.C.comp D.K

/-- 🏆 THEOREM 1: (C K) C = -s • K -/
theorem CKC_eq_neg_s_K (D : CayleyWittDatum R M) :
    (D.C.comp D.K).comp D.C = (-D.s) • D.K := by
  calc (D.C.comp D.K).comp D.C
    _ = ((-D.s) • (D.K.comp D.C)).comp D.C := by rw [D.twisted_comm]
    _ = (-D.s) • ((D.K.comp D.C).comp D.C) := by rw [LinearMap.smul_comp]
    _ = (-D.s) • (D.K.comp (D.C.comp D.C)) := by rw [LinearMap.comp_assoc]
    _ = (-D.s) • (D.K.comp LinearMap.id) := by rw [D.C_sq]
    _ = (-D.s) • D.K := by rw [LinearMap.comp_id]

/-- 🏆 THEOREM 2: The Master Frobenius-Schur Identity: J² = (C K)² = s • I -/
theorem J_operator_sq_eq_smul_id (D : CayleyWittDatum R M) :
    (J_operator D).comp (J_operator D) = D.s • LinearMap.id := by
  dsimp [J_operator]
  calc (D.C.comp D.K).comp (D.C.comp D.K)
    _ = ((D.C.comp D.K).comp D.C).comp D.K := by rw [← LinearMap.comp_assoc]
    _ = ((-D.s) • D.K).comp D.K := by rw [CKC_eq_neg_s_K]
    _ = (-D.s) • (D.K.comp D.K) := by rw [LinearMap.smul_comp]
    _ = (-D.s) • (-LinearMap.id) := by rw [D.K_sq]
    _ = -((-D.s) • LinearMap.id) := by rw [smul_neg]
    _ = -(- (D.s • LinearMap.id)) := by rw [neg_smul]
    _ = D.s • LinearMap.id := by rw [neg_neg]

/-- 🏆 THEOREM 3: Longitudinal Sector (s = +1) gives Real / Majorana Structure J² = +I -/
theorem longitudinal_majorana_real (D : CayleyWittDatum R M) (hs : D.s = 1) :
    (J_operator D).comp (J_operator D) = LinearMap.id := by
  rw [J_operator_sq_eq_smul_id, hs, one_smul]

/-- 🏆 THEOREM 4: Transverse Sector (s = -1) gives Quaternionic / Kramers Structure J² = -I -/
theorem transverse_kramers_pseudoreal (D : CayleyWittDatum R M) (hs : D.s = -1) :
    (J_operator D).comp (J_operator D) = -LinearMap.id := by
  rw [J_operator_sq_eq_smul_id, hs, neg_one_smul]

/-- 🏆 THEOREM 5: Complete Grand Synthesis of Cayley-Witt-Frobenius-Schur Identity -/
theorem cayley_witt_frobenius_schur_synthesis (D : CayleyWittDatum R M) :
    ((J_operator D).comp (J_operator D) = D.s • LinearMap.id) ∧
    (D.s = 1 → (J_operator D).comp (J_operator D) = LinearMap.id) ∧
    (D.s = -1 → (J_operator D).comp (J_operator D) = -LinearMap.id) :=
  ⟨J_operator_sq_eq_smul_id D,
   longitudinal_majorana_real D,
   transverse_kramers_pseudoreal D⟩

end InfoGeometry.Canonical.CayleyWittFrobeniusSchur
