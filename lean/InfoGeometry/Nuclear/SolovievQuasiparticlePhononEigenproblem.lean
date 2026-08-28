import Mathlib
import InfoGeometry.Nuclear.NuclearQuasiparticleCARBridge
import InfoGeometry.Nuclear.NuclearPhononRPAAlgebra

/-!
# Finite Soloviev-style quasiparticle--phonon eigenproblem

This owner is the first spectral step beyond the graded bath-commutant channel
architecture.  It uses the smallest nontrivial truncation: one bare
quasiparticle amplitude and one quasiparticle--phonon amplitude.  The projected
Hamiltonian is therefore an exact `2 × 2` block matrix.

The theorem below is linear algebra only.  It does not claim that the supplied
energies and coupling have already been derived from a microscopic nuclear
Hamiltonian, nor does it promote the finite phonon channel to an exact bosonic
CCR representation.
-/

noncomputable section

open scoped Matrix

namespace InfoGeometry.Nuclear.SolovievQuasiparticlePhononEigenproblem

abbrev Channel2 := Fin 2
abbrev Vec2 := Channel2 → ℝ
abbrev Mat2 := Matrix Channel2 Channel2 ℝ

/-- Two-channel coefficient vector: bare quasiparticle amplitude `C` and
quasiparticle--phonon amplitude `D`. -/
def qpnmState (C D : ℝ) : Vec2 := ![C, D]

/-- Smallest nontrivial projected QPNM Hamiltonian.

`Eqp` is the bare quasiparticle energy, `Ephon` the coupled
quasiparticle--phonon channel energy, and `V` the mixing matrix element. -/
def qpnmHamiltonian (Eqp Ephon V : ℝ) : Mat2 :=
  !![Eqp, V; V, Ephon]

@[simp] theorem qpnmHamiltonian_mulVec_zero
    (Eqp Ephon V C D : ℝ) :
    (qpnmHamiltonian Eqp Ephon V).mulVec (qpnmState C D) 0 =
      Eqp * C + V * D := by
  simp [qpnmHamiltonian, qpnmState, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

@[simp] theorem qpnmHamiltonian_mulVec_one
    (Eqp Ephon V C D : ℝ) :
    (qpnmHamiltonian Eqp Ephon V).mulVec (qpnmState C D) 1 =
      V * C + Ephon * D := by
  simp [qpnmHamiltonian, qpnmState, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- Exact equivalence between the projected eigenvector equation and the two
coupled Soloviev-style secular equations. -/
theorem qpnm_eigenproblem_iff_secular
    (Eqp Ephon V E C D : ℝ) :
    (qpnmHamiltonian Eqp Ephon V).mulVec (qpnmState C D) =
        E • qpnmState C D ↔
      Eqp * C + V * D = E * C ∧
      V * C + Ephon * D = E * D := by
  constructor
  · intro h
    constructor
    · have h0 := congrFun h (0 : Fin 2)
      simpa [qpnmState] using h0
    · have h1 := congrFun h (1 : Fin 2)
      simpa [qpnmState] using h1
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simpa [qpnmState] using h0
    · simpa [qpnmState] using h1

/-- Determinant of the shifted two-channel Hamiltonian. -/
def secularDeterminant (Eqp Ephon V E : ℝ) : ℝ :=
  (Eqp - E) * (Ephon - E) - V ^ 2

/-- Every nonzero eigenvector of the two-channel QPNM matrix satisfies the
usual quadratic secular determinant equation. -/
theorem secularDeterminant_eq_zero_of_eigenvector
    (Eqp Ephon V E C D : ℝ)
    (heig : (qpnmHamiltonian Eqp Ephon V).mulVec (qpnmState C D) =
      E • qpnmState C D)
    (hnonzero : C ≠ 0 ∨ D ≠ 0) :
    secularDeterminant Eqp Ephon V E = 0 := by
  have hsec := (qpnm_eigenproblem_iff_secular Eqp Ephon V E C D).mp heig
  rcases hsec with ⟨h0, h1⟩
  unfold secularDeterminant
  rcases hnonzero with hC | hD
  · have h0' : (Eqp - E) * C + V * D = 0 := by linarith
    have h1' : V * C + (Ephon - E) * D = 0 := by linarith
    have hmul0 := congrArg (fun x : ℝ => (Ephon - E) * x) h0'
    have hmul1 := congrArg (fun x : ℝ => V * x) h1'
    have hprod : (((Eqp - E) * (Ephon - E) - V ^ 2) * C) = 0 := by
      nlinarith [hmul0, hmul1]
    exact (mul_eq_zero.mp hprod).resolve_right hC
  · have h0' : (Eqp - E) * C + V * D = 0 := by linarith
    have h1' : V * C + (Ephon - E) * D = 0 := by linarith
    have hmul0 := congrArg (fun x : ℝ => V * x) h0'
    have hmul1 := congrArg (fun x : ℝ => (Eqp - E) * x) h1'
    have hprod : (((Eqp - E) * (Ephon - E) - V ^ 2) * D) = 0 := by
      nlinarith [hmul0, hmul1]
    exact (mul_eq_zero.mp hprod).resolve_right hD

end InfoGeometry.Nuclear.SolovievQuasiparticlePhononEigenproblem

end noncomputable section
