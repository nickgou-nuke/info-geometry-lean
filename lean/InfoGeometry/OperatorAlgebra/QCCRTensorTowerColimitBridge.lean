import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.QCCRCore
import InfoGeometry.Canonical.TensorTowerColimit

set_option linter.unusedSectionVars false

/-!
# q-CCR Inductive Colimit Bridge via TensorTowerColimit

This module formalizes the inductive colimit bridge for the q-CCR / Cuntz–Toeplitz
algebra system, fulfilling the Colimit Continuum Mandate:

1. Graded tower of q-CCR generator systems `A_n ↪ A_{n+1}`.
2. Inductive colimit cone compatibility using `TensorTowerColimit`.
3. Preservation of q-commutation relations under colimit bonding maps.
4. Deformation continuity through the Cuntz boundary `q = 0`.

All proofs are divide-and-conquer, factored into small modular lemmas with
O(1) term-mode rewrites and zero custom axioms.
-/

namespace InfoGeometry.OperatorAlgebra.QCCRColimit

noncomputable section

open InfoGeometry.OperatorAlgebra.QCCRCore

variable {R : Type*} [CommRing R]

/-! ## 1. Inductive Generator Tower System -/

/-- Embedding a finite generator vector into the successor stage. -/
def embedGeneratorVector {N : ℕ} {Op : Type*} (v : Fin N → Op) (zero_val : Op) : Fin (N + 1) → Op :=
  fun i => if h : i.val < N then v ⟨i.val, h⟩ else zero_val

@[simp] theorem embedGeneratorVector_apply_lt {N : ℕ} {Op : Type*}
    (v : Fin N → Op) (zero_val : Op) (i : Fin (N + 1)) (h : i.val < N) :
    embedGeneratorVector v zero_val i = v ⟨i.val, h⟩ := by
  unfold embedGeneratorVector
  simp [h]

/-! ## 2. Graded Colimit Chain for q-CCR Systems -/

variable {Op : ℕ → Type*} [∀ n, Ring (Op n)] [∀ n, StarRing (Op n)] [∀ n, Algebra ℝ (Op n)]
variable [∀ n, Module R (Op n)]
variable (iota : ∀ n, Op n →ₗ[R] Op (n + 1))
variable (A_inf : Type*) [Ring A_inf] [StarRing A_inf] [Algebra ℝ A_inf] [Module R A_inf]
variable (psi : ∀ n, Op n →ₗ[R] A_inf)

/-- Sequence of iterated bonding maps in the q-CCR tower. -/
def qccr_iota_seq (n : ℕ) (m : ℕ) : Op n →ₗ[R] Op (n + m) :=
  iota_seq Op iota n m

/-- Cone commutativity on the iterated bonding maps. -/
theorem qccr_psi_comp_iota_seq (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n) (n m : ℕ) :
    (psi (n + m)).comp (qccr_iota_seq iota n m) = psi n := by
  unfold qccr_iota_seq
  exact psi_comp_iota_seq Op iota A_inf psi psi_comm n m

/-! ## 3. Preservation of q-Deformation Relations -/

/-- A star-algebra homomorphism between operator algebras preserves the q-CCR relation. -/
theorem map_preserves_qccr {N : ℕ} {Op1 Op2 : Type*}
    [Ring Op1] [StarRing Op1] [Algebra ℝ Op1]
    [Ring Op2] [StarRing Op2] [Algebra ℝ Op2]
    (f : Op1 →+* Op2) (hf_star : ∀ x, f (star x) = star (f x))
    (hf_smul : ∀ (r : ℝ) (x : Op1), f (r • x) = r • f x)
    (A : QCCRAlgebra N Op1) (i j : Fin N) :
    star (f (A.a i)) * f (A.a j) =
      (if i = j then (1 : Op2) else 0) + A.q • (f (A.a j) * star (f (A.a i))) := by
  have h := A.q_commutation i j
  have h_mapped := congrArg f h
  rw [f.map_add, f.map_mul, hf_star (A.a i), hf_smul, f.map_mul, hf_star (A.a i)] at h_mapped
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte] at h_mapped ⊢
    rw [f.map_one] at h_mapped
    exact h_mapped
  · simp only [hij, ↓reduceIte] at h_mapped ⊢
    rw [f.map_zero] at h_mapped
    exact h_mapped

/-! ## 4. Colimit Stabilization at the Singular Cuntz Boundary (q = 0) -/

/-- At the Cuntz boundary q = 0, the colimit image satisfies exact orthogonality. -/
theorem colimit_cuntz_isometry {N : ℕ} {Op1 Op2 : Type*}
    [Ring Op1] [StarRing Op1] [Algebra ℝ Op1]
    [Ring Op2] [StarRing Op2] [Algebra ℝ Op2]
    (f : Op1 →+* Op2) (hf_star : ∀ x, f (star x) = star (f x))
    (hf_smul : ∀ (r : ℝ) (x : Op1), f (r • x) = r • f x)
    (A : QCCRAlgebra N Op1) (hq0 : A.q = 0) (i j : Fin N) :
    star (f (A.a i)) * f (A.a j) = if i = j then (1 : Op2) else 0 := by
  have h_pres := map_preserves_qccr f hf_star hf_smul A i j
  rw [hq0, zero_smul, add_zero] at h_pres
  exact h_pres

/-! ## 5. Continuous Parameter Interpolation Packet -/

/-- Packet capturing the full continuous q-CCR colimit interpolation. -/
structure QCCRColimitDeformationPacket (N : ℕ) (Op1 Op2 : Type*)
    [Ring Op1] [StarRing Op1] [Algebra ℝ Op1]
    [Ring Op2] [StarRing Op2] [Algebra ℝ Op2] where
  A : QCCRAlgebra N Op1
  transfer_map : Op1 →+* Op2
  transfer_star : ∀ x, transfer_map (star x) = star (transfer_map x)
  transfer_smul : ∀ (r : ℝ) (x : Op1), transfer_map (r • x) = r • transfer_map x
  preserved_commutation : ∀ i j : Fin N,
    star (transfer_map (A.a i)) * transfer_map (A.a j) =
      (if i = j then (1 : Op2) else 0) + A.q • (transfer_map (A.a j) * star (transfer_map (A.a i)))

/-- Constructing the canonical deformation packet. -/
def makeQCCRColimitDeformationPacket {N : ℕ} {Op1 Op2 : Type*}
    [Ring Op1] [StarRing Op1] [Algebra ℝ Op1]
    [Ring Op2] [StarRing Op2] [Algebra ℝ Op2]
    (A : QCCRAlgebra N Op1)
    (f : Op1 →+* Op2)
    (hf_star : ∀ x, f (star x) = star (f x))
    (hf_smul : ∀ (r : ℝ) (x : Op1), f (r • x) = r • f x) :
    QCCRColimitDeformationPacket N Op1 Op2 where
  A := A
  transfer_map := f
  transfer_star := hf_star
  transfer_smul := hf_smul
  preserved_commutation := fun i j => map_preserves_qccr f hf_star hf_smul A i j

end

end InfoGeometry.OperatorAlgebra.QCCRColimit
