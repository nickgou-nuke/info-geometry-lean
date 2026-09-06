import Mathlib.Tactic
import InfoGeometry.External.Auto.CasimirIsospinHamiltonian
import InfoGeometry.External.Auto.IsospinSymmetryBreaking
import InfoGeometry.Physics.NuclearPhysicalDegreeZero

/-!
# Physical Hamiltonian readout for the nuclear five-grade program

The abstract five-grading remains an algebraic transition carrier.  This file
uses the existing shell-model Hamiltonian and records its physical split into
an isospin-symmetric part and explicit charge-symmetry-breaking terms.
-/

namespace InfoGeometry.Physics.NuclearFiveGradedPhysicalBridge

open CasimirIsospinHamiltonian
open IsospinSymmetryBreaking

noncomputable section

variable {n : ℕ}

def symmetricPart (H : ShellModelHamiltonian) :
    Matrix (Fin n) (Fin n) ℂ := H.H_0 (n := n)

def breakingPart (H : ShellModelHamiltonian) :
    Matrix (Fin n) (Fin n) ℂ :=
      H.H_C (n := n) + H.H_CSB (n := n) + H.H_CIB (n := n)

def totalPart (H : ShellModelHamiltonian) :
    Matrix (Fin n) (Fin n) ℂ :=
  symmetricPart H + breakingPart H

theorem totalPart_eq_sum (H : ShellModelHamiltonian) :
    totalPart H = H.H_0 (n := n) + H.H_C (n := n) +
      H.H_CSB (n := n) + H.H_CIB (n := n) := by
  simp [totalPart, symmetricPart, breakingPart, add_assoc]

def isChargeSymmetric (H : ShellModelHamiltonian) : Prop :=
  H.H_C (n := n) = 0 ∧ H.H_CSB (n := n) = 0 ∧ H.H_CIB (n := n) = 0

theorem breakingPart_eq_zero_of_chargeSymmetric
    (H : ShellModelHamiltonian)
    (h : isChargeSymmetric (n := n) H) :
    breakingPart (n := n) H = 0 := by
  rcases h with ⟨hC, hCSB, hCIB⟩
  simp [breakingPart, hC, hCSB, hCIB]

theorem totalPart_eq_symmetric_of_chargeSymmetric
    (H : ShellModelHamiltonian)
    (h : isChargeSymmetric (n := n) H) :
    totalPart (n := n) H = symmetricPart (n := n) H := by
  rw [totalPart, breakingPart_eq_zero_of_chargeSymmetric (n := n) H h, add_zero]

theorem imme_mirror_even_odd
    (a b c t : Q) :
    mirrorSum (imme a b c) t = 2 * (a + c * t ^ 2) ∧
      mirrorDifference (imme a b c) t = 2 * b * t := by
  constructor
  · rw [imme_mirror_sum]
    ring
  · exact imme_mirror_difference a b c t

end

end InfoGeometry.Physics.NuclearFiveGradedPhysicalBridge
