import Mathlib.Tactic
import InfoGeometry.Algebraic.SplitQuadraticForm

/-!
# Cl(n,n) CAR algebra — n fermionic modes

Generalizes Cl(4,4) to arbitrary Cl(n,n) = Cl(n,0)⊗Cl(0,n) with
n positive + n negative generators. Using isotropic vectors and
the polar form of the split quadratic form, we obtain n fermionic
creation/annihilation pairs with the full CAR algebra.

  p_i² = 1, n_i² = -1  (i = 0,…,n-1)
  a_i  = ½(p_i + n_i)   annihilation
  a_i† = ½(p_i - n_i)   creation

CAR identities:
  a_i² = 0, a_i†² = 0
  {a_i, a_j} = {a_i†, a_j†} = 0
  {a_i, a_j†} = δ_{ij}·1

Proof method: algebraic, not finite-case — uses the general polar form
and quadratic form properties of `splitQuadraticForm n`.
-/

open CliffordAlgebra
open InfoGeometry.Algebraic.SplitSignature

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CliffordCAR

variable (n : ℕ)

abbrev Clnn := CliffordAlgebra (splitQuadraticForm n)
abbrev Qn := splitQuadraticForm n

/-- Positive basis vector. -/
def pVec (i : Fin n) : SplitModule n := splitBasisVector (Sum.inl i)
/-- Negative basis vector. -/
def nVec (i : Fin n) : SplitModule n := splitBasisVector (Sum.inr i)

def p (i : Fin n) : Clnn n := ι (Qn n) (pVec n i)
def n (i : Fin n) : Clnn n := ι (Qn n) (nVec n i)

@[simp] theorem p_sq (i : Fin n) : p n i * p n i = 1 := by
  calc
    p n i * p n i = algebraMap ℝ (Clnn n) ((Qn n) (pVec n i)) := ι_sq_scalar _ _
    _ = algebraMap ℝ (Clnn n) (1 : ℝ) := by rw [Qn, pVec, splitQuadraticForm_posBasisVector]
    _ = 1 := by simp

@[simp] theorem n_sq (i : Fin n) : n n i * n n i = -1 := by
  calc
    n n i * n n i = algebraMap ℝ (Clnn n) ((Qn n) (nVec n i)) := ι_sq_scalar _ _
    _ = algebraMap ℝ (Clnn n) (-1 : ℝ) := by rw [Qn, nVec, splitQuadraticForm_negBasisVector]
    _ = -1 := by simp

theorem p_n_anticomm (i j : Fin n) : p n i * n n j + n n j * p n i = 0 := by
  have h : QuadraticMap.polar (Qn n) (pVec n i) (nVec n j) = 0 := by
    dsimp [Qn, pVec, nVec]
    rw [QuadraticMap.polar]
    simp [splitQuadraticForm, splitBasisVector]
  rw [p, n, ι_mul_ι_add_swap, h]
  simp

/-- Annihilation vector: a_i = ½(p_i + n_i), isotropic for the split quadratic form. -/
def aVec (i : Fin n) : SplitModule n := (1/2 : ℝ) • (pVec n i + nVec n i)

/-- Creation vector: a_i† = ½(p_i - n_i), also isotropic. -/
def aDagVec (i : Fin n) : SplitModule n := (1/2 : ℝ) • (pVec n i - nVec n i)

/-- Isotropic: Q(annihilation vector) = 0 for all i. -/
@[simp] theorem Q_aVec (i : Fin n) : (Qn n) (aVec n i) = 0 := by
  dsimp [Qn, aVec, pVec, nVec]
  calc
    splitQuadraticForm n ((1/2 : ℝ) • (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i)))
        = (1/2) ^ 2 • splitQuadraticForm n (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i)) := by
      simp [QuadraticMap.map_smul]
    _ = (1/4) • (splitQuadraticForm n (splitBasisVector (Sum.inl i)) +
                 splitQuadraticForm n (splitBasisVector (Sum.inr i))) := by
      simp [QuadraticMap.map_add, splitQuadraticForm_posBasisVector, splitQuadraticForm_negBasisVector]
    _ = (1/4) • ((1 : ℝ) + (-1 : ℝ)) := by simp
    _ = 0 := by ring

/-- Isotropic: Q(creation vector) = 0 for all i. -/
@[simp] theorem Q_aDagVec (i : Fin n) : (Qn n) (aDagVec n i) = 0 := by
  dsimp [Qn, aDagVec, pVec, nVec]
  calc
    splitQuadraticForm n ((1/2 : ℝ) • (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i)))
        = (1/2) ^ 2 • splitQuadraticForm n (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i)) := by
      simp [QuadraticMap.map_smul]
    _ = (1/4) • (splitQuadraticForm n (splitBasisVector (Sum.inl i)) +
                 splitQuadraticForm n (splitBasisVector (Sum.inr i))) := by
      simp [QuadraticMap.map_add, QuadraticMap.map_neg, splitQuadraticForm_posBasisVector,
        splitQuadraticForm_negBasisVector]
    _ = (1/4) • ((1 : ℝ) + (-1 : ℝ)) := by simp
    _ = 0 := by ring

def a (i : Fin n) : Clnn n := ι (Qn n) (aVec n i)
def aDag (i : Fin n) : Clnn n := ι (Qn n) (aDagVec n i)

/-- CAR nilpotence: a_i² = 0. -/
@[simp] theorem a_sq_zero (i : Fin n) : a n i * a n i = 0 := by
  rw [a, ι_sq_scalar, Q_aVec]; simp

/-- CAR nilpotence: a_i†² = 0. -/
@[simp] theorem aDag_sq_zero (i : Fin n) : aDag n i * aDag n i = 0 := by
  rw [aDag, ι_sq_scalar, Q_aDagVec]; simp

/--
Cross polar form: polar(a_i, a_j†) = δ_{ij}.
Algebraic proof using the general polar form.
-/
theorem polar_a_aDag (i j : Fin n) :
    QuadraticMap.polar (Qn n) (aVec n i) (aDagVec n j) = if i = j then 1 else 0 := by
  dsimp [aVec, aDagVec]
  -- Expand polar of scaled sums
  simp_rw [QuadraticMap.polar_add_add, QuadraticMap.polar_smul_smul,
    QuadraticMap.polar_self, QuadraticMap.polar_comm]
  -- Now we have (1/4) * (polar(p_i,p_j) - polar(p_i,n_j) + polar(n_i,p_j) - polar(n_i,n_j))
  dsimp [Qn, pVec, nVec]
  -- polar(pVec i, pVec j) = 2*Q(pVec i)*δ_{ij} (since Q(pVec i)=1)
  -- polar(nVec i, nVec j) = -2*δ_{ij} (since Q(nVec i)=-1)
  -- polar(pVec i, nVec j) = 0 (orthogonal)
  -- So: (1/4)*(2δ - 0 + 0 - (-2δ)) = δ
  simp [splitQuadraticForm_posBasisVector, splitQuadraticForm_negBasisVector,
    splitQuadraticForm_basisVector, QuadraticMap.polar, splitBasisVector]
  by_cases h : i = j
  · subst j; norm_num
  · simp [h]

/-- CAR mixed identity: {a_i, a_j†} = δ_{ij}·1. -/
theorem car_identity (i j : Fin n) :
    a n i * aDag n j + aDag n j * a n i = (if i = j then (1 : Clnn n) else 0) := by
  rw [a, aDag, ι_mul_ι_add_swap, polar_a_aDag]
  split_ifs <;> simp

/-- Polar form of two annihilation vectors: always zero. -/
theorem polar_a_a (i j : Fin n) :
    QuadraticMap.polar (Qn n) (aVec n i) (aVec n j) = 0 := by
  dsimp [aVec]; simp_rw [QuadraticMap.polar_add_add, QuadraticMap.polar_smul_smul]
  dsimp [Qn, pVec, nVec]
  simp [splitQuadraticForm_posBasisVector, splitQuadraticForm_negBasisVector,
    splitQuadraticForm_basisVector, QuadraticMap.polar, splitBasisVector]
  by_cases h : i = j; · subst j; norm_num; · simp [h]

/-- Polar form of two creation vectors: always zero. -/
theorem polar_aDag_aDag (i j : Fin n) :
    QuadraticMap.polar (Qn n) (aDagVec n i) (aDagVec n j) = 0 := by
  dsimp [aDagVec]; simp_rw [QuadraticMap.polar_add_add, QuadraticMap.polar_smul_smul]
  dsimp [Qn, pVec, nVec]
  simp [splitQuadraticForm_posBasisVector, splitQuadraticForm_negBasisVector,
    splitQuadraticForm_basisVector, QuadraticMap.polar, splitBasisVector]
  by_cases h : i = j; · subst j; norm_num; · simp [h]

/-- CAR same-kind anticommutation: {a_i, a_j} = 0. -/
theorem a_a_anticomm (i j : Fin n) : a n i * a n j + a n j * a n i = 0 := by
  by_cases h : i = j; · subst j; simp [a_sq_zero]
  · rw [a, a, ι_mul_ι_add_swap, polar_a_a n i j]; simp

/-- CAR same-kind anticommutation: {a_i†, a_j†} = 0. -/
theorem aDag_aDag_anticomm (i j : Fin n) :
    aDag n i * aDag n j + aDag n j * aDag n i = 0 := by
  by_cases h : i = j; · subst j; simp [aDag_sq_zero]
  · rw [aDag, aDag, ι_mul_ι_add_swap, polar_aDag_aDag n i j]; simp

/-- Complete CAR packet for n fermionic modes from Cl(n,n). -/
theorem car_packet (n : ℕ) :
    (∀ i : Fin n, a n i * a n i = 0) ∧
    (∀ i : Fin n, aDag n i * aDag n i = 0) ∧
    (∀ i j : Fin n, a n i * a n j + a n j * a n i = 0) ∧
    (∀ i j : Fin n, aDag n i * aDag n j + aDag n j * aDag n i = 0) ∧
    (∀ i j : Fin n,
      a n i * aDag n j + aDag n j * a n i = if i = j then (1 : Clnn n) else 0) := by
  exact ⟨a_sq_zero n, aDag_sq_zero n, a_a_anticomm n, aDag_aDag_anticomm n, car_identity n⟩

end InfoGeometry.OperatorAlgebra.CliffordCAR
