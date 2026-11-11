/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.TwoQubitPauliGeometry
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Real phase conventions for two-qubit Weyl matrices

Changing the sign of each ordered Weyl word changes its product cocycle by a
binary coboundary. The symplectic pairing still governs order reversal, and
the square/transpose parity is unchanged. In particular the sign `(-1)^(x · z)`
reverses the ordered cocycle; it does not make every word Hermitian.

All products below use the actual four-by-four Kronecker matrices. Labels are
interleaved as `((x₁,z₁),(x₂,z₂))`. The identities hold over a commutative ring;
characteristic zero is required for the converses that distinguish the signs.
-/

namespace InfoGeometry.Quantum.TwoQubitPauli

open Matrix
open scoped Kronecker
open Projective.BinarySymplectic BinaryWeyl

variable {R : Type*} [CommRing R]

/-- A real-sign change of the existing ordered matrix representatives. -/
def rephasedPauli (f : Label → Bit) (v : Label) : Operator R :=
  phase (R := R) (f v) • pauli v

theorem rephasedPauli_zero (f : Label → Bit) :
    rephasedPauli (R := R) f 0 = phase (R := R) (f 0) • (1 : Operator R) := by
  simp [rephasedPauli]

theorem rephasedPauli_zero_of_normalized (f : Label → Bit) (hf : f 0 = 0) :
    rephasedPauli (R := R) f 0 = 1 := by
  simp [rephasedPauli_zero, hf]

@[simp] theorem phase_smul_rephasedPauli (f : Label → Bit) (v : Label) :
    phase (R := R) (f v) • rephasedPauli f v = pauli (R := R) v := by
  rw [rephasedPauli, smul_smul, phase_mul_self, one_smul]

/-- Rephasing does not lose scalar information from an invertible matrix word. -/
theorem smul_rephasedPauli_injective (f : Label → Bit) (v : Label) :
    Function.Injective (fun r : R => r • rephasedPauli (R := R) f v) := by
  intro r s h
  apply smul_pauli_injective v
  have he := congrArg (fun A : Operator R => phase (R := R) (f v) • A) h
  simpa only [smul_comm (phase (R := R) (f v)) r,
    smul_comm (phase (R := R) (f v)) s, phase_smul_rephasedPauli] using he

/-- The ordered product retains the coboundary-adjusted cocycle. -/
theorem rephasedPauli_mul (f : Label → Bit) (v w : Label) :
    rephasedPauli (R := R) f v * rephasedPauli f w =
      phase (R := R) (rephasedCocycle f v w) • rephasedPauli f (v + w) := by
  simp only [rephasedPauli, smul_mul_assoc, mul_smul_comm, pauli_mul,
    smul_smul, ← phase_add]
  congr 2
  simp [rephasedCocycle, add_assoc, CharTwo.add_self_eq_zero, add_comm, add_left_comm]

/-- No normalization assumption on `f` is needed for the matrix square law. -/
theorem rephasedPauli_mul_self (f : Label → Bit) (v : Label) :
    rephasedPauli (R := R) f v * rephasedPauli f v =
      phase (R := R) (quadraticPhase v) • (1 : Operator R) := by
  simp only [rephasedPauli, smul_mul_assoc, mul_smul_comm,
    smul_smul, phase_mul_self, one_smul]
  exact pauli_mul_self v

/-- The symplectic form controls order reversal for every real-sign convention. -/
theorem rephasedPauli_phase_commutation (f : Label → Bit) (v w : Label) :
    rephasedPauli (R := R) f v * rephasedPauli f w =
      phase (R := R) (symplectic v w) • (rephasedPauli f w * rephasedPauli f v) := by
  rw [rephasedPauli_mul, rephasedPauli_mul, smul_smul, ← phase_add, add_comm w v]
  congr 2
  rw [← rephasedCocycle_symplectic f v w, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

theorem rephasedPauli_commute_iff [CharZero R] (f : Label → Bit) (v w : Label) :
    Commute (rephasedPauli (R := R) f v) (rephasedPauli f w) ↔ symplectic v w = 0 := by
  change rephasedPauli (R := R) f v * rephasedPauli f w =
    rephasedPauli f w * rephasedPauli f v ↔ _
  rw [rephasedPauli_mul, rephasedPauli_mul, add_comm w v]
  constructor
  · intro h
    have hc := phase_injective (smul_rephasedPauli_injective f (v + w) h)
    rw [← rephasedCocycle_symplectic f v w, hc, CharTwo.add_self_eq_zero]
  · intro h
    have hc := CharTwo.add_eq_zero.mp ((rephasedCocycle_symplectic f v w).trans h)
    rw [hc]

/-- Noncommutativity remains on the same matrix carrier after any sign change. -/
theorem rephasedPauli_first_factor_noncommute [CharZero R] (f : Label → Bit) :
    rephasedPauli (R := R) f ((1, 0), (0, 0)) * rephasedPauli f ((0, 1), (0, 0)) ≠
      rephasedPauli f ((0, 1), (0, 0)) * rephasedPauli f ((1, 0), (0, 0)) := by
  intro h
  have hc := (rephasedPauli_commute_iff (R := R) f ((1, 0), (0, 0))
    ((0, 1), (0, 0))).mp h
  norm_num [symplectic, cocycle] at hc

/-- The symplectic form cannot itself be the product cocycle in any real-sign gauge. -/
theorem not_rephasedPauli_symplectic_product [CharZero R] (f : Label → Bit) :
    ¬ (∀ v w, rephasedPauli (R := R) f v * rephasedPauli f w =
      phase (R := R) (symplectic v w) • rephasedPauli f (v + w)) := by
  intro h
  apply rephasedPauli_first_factor_noncommute (R := R) f
  rw [h, h, symplectic_comm ((0, 1), (0, 0)) ((1, 0), (0, 0)),
    add_comm ((0, 1), (0, 0)) ((1, 0), (0, 0))]

/-- Transpose of the ordered two-factor word detects the same quadratic parity as its square. -/
theorem pauli_transpose (v : Label) :
    (pauli (R := R) v)ᵀ = phase (R := R) (quadraticPhase v) • pauli v := by
  simp only [pauli, Matrix.kronecker, ← Matrix.kroneckerMap_transpose, word_transpose]
  change (phase (R := R) (v.1.1 * v.1.2) • word v.1.1 v.1.2) ⊗ₖ
    (phase (R := R) (v.2.1 * v.2.2) • word v.2.1 v.2.2) = _
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, ← phase_add]
  congr 2
  simp only [quadraticPhase, cocycle, mul_comm, add_comm]

theorem rephasedPauli_transpose (f : Label → Bit) (v : Label) :
    (rephasedPauli (R := R) f v)ᵀ =
      phase (R := R) (quadraticPhase v) • rephasedPauli f v := by
  rw [rephasedPauli, Matrix.transpose_smul, pauli_transpose, smul_comm]

/-- A real sign cannot change whether a word is symmetric. -/
theorem rephasedPauli_isSymm_iff [CharZero R] (f : Label → Bit) (v : Label) :
    (rephasedPauli (R := R) f v).IsSymm ↔ quadraticPhase v = 0 := by
  change (rephasedPauli (R := R) f v)ᵀ = rephasedPauli f v ↔ _
  rw [rephasedPauli_transpose]
  constructor
  · intro h
    have hs : phase (R := R) (quadraticPhase v) = 1 :=
      smul_rephasedPauli_injective f v (by simpa only [one_smul] using h)
    exact phase_injective (by simpa only [phase_zero] using hs)
  · intro h
    simp [h]

/-- For a trivial coefficient involution, in particular over the reals, Hermitian means symmetric. -/
theorem rephasedPauli_isHermitian_iff [CharZero R] [Star R] [TrivialStar R]
    (f : Label → Bit) (v : Label) :
    (rephasedPauli (R := R) f v).IsHermitian ↔ quadraticPhase v = 0 := by
  rw [Matrix.isHermitian_iff_isSymm, rephasedPauli_isSymm_iff]

/-- Every real-sign choice leaves the first-factor `XZ` word nonsymmetric. -/
theorem rephasedPauli_xz_not_isSymm [CharZero R] (f : Label → Bit) :
    ¬ (rephasedPauli (R := R) f ((1, 1), (0, 0))).IsSymm := by
  rw [rephasedPauli_isSymm_iff]
  norm_num [quadraticPhase, cocycle]

/-- The requested quadratic sign convention has the opposite ordered product cocycle. -/
theorem quadraticPauli_mul (v w : Label) :
    rephasedPauli (R := R) quadraticPhase v * rephasedPauli quadraticPhase w =
      phase (R := R) (cocycle w v) • rephasedPauli quadraticPhase (v + w) := by
  rw [rephasedPauli_mul, rephasedCocycle_quadraticPhase]

theorem quadraticPauli_eq_transpose (v : Label) :
    rephasedPauli (R := R) quadraticPhase v = (pauli v)ᵀ :=
  (pauli_transpose v).symm

/-- The same convention reverses `X` and `Z` inside each Kronecker factor. -/
theorem quadraticPauli_eq_reverse (v : Label) :
    rephasedPauli (R := R) quadraticPhase v =
      (clock ^ v.1.2.val * shift ^ v.1.1.val) ⊗ₖ
        (clock ^ v.2.2.val * shift ^ v.2.1.val) := by
  rw [quadraticPauli_eq_transpose]
  simp only [pauli, Matrix.kronecker, ← Matrix.kroneckerMap_transpose,
    word_transpose_eq_reverse]

/-- The quadratic phase gives the inverse of the ordered matrix word. -/
theorem pauli_mul_quadraticPauli (v : Label) :
    pauli (R := R) v * rephasedPauli quadraticPhase v = 1 :=
  pauli_mul_inverse v

theorem quadraticPauli_mul_pauli (v : Label) :
    rephasedPauli (R := R) quadraticPhase v * pauli v = 1 := by
  rw [rephasedPauli, smul_mul_assoc, pauli_mul_self,
    smul_smul, quadraticPhase, phase_mul_self, one_smul]

/-- A concrete counterexample to replacing the product cocycle by the alternating pairing. -/
theorem quadraticPauli_xz_square :
    rephasedPauli (R := R) quadraticPhase ((1, 1), (0, 0)) *
      rephasedPauli quadraticPhase ((1, 1), (0, 0)) = -(1 : Operator R) := by
  rw [rephasedPauli_mul_self]
  norm_num [quadraticPhase, cocycle]

theorem quadraticPauli_xz_product_ne_symplectic [CharZero R] :
    rephasedPauli (R := R) quadraticPhase ((1, 1), (0, 0)) *
      rephasedPauli quadraticPhase ((1, 1), (0, 0)) ≠
        phase (R := R) (symplectic ((1, 1), (0, 0)) ((1, 1), (0, 0))) •
          rephasedPauli quadraticPhase (((1, 1), (0, 0)) + ((1, 1), (0, 0))) := by
  rw [quadraticPauli_xz_square, symplectic_self, phase_zero, one_smul, label_add_self,
    rephasedPauli_zero, quadraticPhase_zero, phase_zero, one_smul]
  intro h
  have he := congrArg (fun A : Operator R => A (0, 0) (0, 0)) h
  norm_num at he

end InfoGeometry.Quantum.TwoQubitPauli
