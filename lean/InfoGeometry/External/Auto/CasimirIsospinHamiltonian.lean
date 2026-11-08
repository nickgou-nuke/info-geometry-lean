import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace CasimirIsospinHamiltonian

abbrev Q := ℚ

def massCasimir (m2 : Q) : Q := -m2
def spinCasimir (J : Q) : Q := J * (J + 1)
def isospinCasimir (T : Q) : Q := T * (T + 1)
def seniorityCasimir (v : Q) : Q := v * (v + 1)
def casimirStiffness (C : Q) : Q := -C

def imme (a b c Tz : Q) : Q :=
  a + b * Tz + c * Tz ^ 2

def pnPairProjector (T : ℕ) : Q :=
  if T = 0 then 1 else if T = 1 then 1 else 0

def pairHamiltonian (k0 k1 : Q) : Q :=
  k0 * pnPairProjector 0 + k1 * pnPairProjector 1

def casimirHamiltonian
    (α β γ δ m2 J T v : Q) : Q :=
  α * massCasimir m2 + β * spinCasimir J + γ * isospinCasimir T + δ * seniorityCasimir v

def generalizedHamiltonian
    (α β γ δ a b c k0 k1 spring m2 J T v Tz : Q) : Q :=
  casimirHamiltonian α β γ δ m2 J T v + imme a b c Tz + pairHamiltonian k0 k1 + spring

def mirrorDifference (H : Q → Q) (t : Q) : Q :=
  H t - H (-t)

def mirrorSum (H : Q → Q) (t : Q) : Q :=
  H t + H (-t)

def pd94_T : Q := 1
def pd94_isospinCasimir : Q := isospinCasimir pd94_T
def pd94_massNumber : Q := 94
def pd94_massCasimir : Q := massCasimir pd94_massNumber
def pd94_springStiffness : Q := casimirStiffness pd94_massCasimir

theorem isospin_casimir_T1 :
    isospinCasimir 1 = 2 := by
  norm_num [isospinCasimir]

theorem isospin_casimir_half :
    isospinCasimir (1 / 2) = 3 / 4 := by
  norm_num [isospinCasimir]

theorem mass_casimir_stiffness (m2 : Q) :
    casimirStiffness (massCasimir m2) = m2 := by
  simp [casimirStiffness, massCasimir]

theorem imme_mirror_difference (a b c t : Q) :
    mirrorDifference (imme a b c) t = 2 * b * t := by
  unfold mirrorDifference imme
  ring

theorem imme_mirror_sum (a b c t : Q) :
    mirrorSum (imme a b c) t = 2 * a + 2 * c * t ^ 2 := by
  unfold mirrorSum imme
  ring

theorem pnPairProjector_zero :
    pnPairProjector 0 = 1 := by
  norm_num [pnPairProjector]

theorem pnPairProjector_one :
    pnPairProjector 1 = 1 := by
  norm_num [pnPairProjector]

theorem pnPairProjector_two :
    pnPairProjector 2 = 0 := by
  norm_num [pnPairProjector]

theorem pair_hamiltonian_extracts_channels (k0 k1 : Q) :
    pairHamiltonian k0 k1 = k0 + k1 := by
  norm_num [pairHamiltonian, pnPairProjector]

theorem casimir_hamiltonian_linear (α β γ δ m2 J T v : Q) :
    casimirHamiltonian α β γ δ m2 J T v =
      α * (-m2) + β * (J * (J + 1)) + γ * (T * (T + 1)) + δ * (v * (v + 1)) := by
  simp [casimirHamiltonian, massCasimir, spinCasimir, isospinCasimir, seniorityCasimir]

theorem generalized_hamiltonian_mirror_difference
    (α β γ δ a b c k0 k1 spring m2 J T v t : Q) :
    mirrorDifference
      (fun Tz => generalizedHamiltonian α β γ δ a b c k0 k1 spring m2 J T v Tz) t =
      2 * b * t := by
  unfold mirrorDifference generalizedHamiltonian casimirHamiltonian massCasimir spinCasimir
    isospinCasimir seniorityCasimir imme pairHamiltonian pnPairProjector
  ring

theorem generalized_hamiltonian_mirror_sum
    (α β γ δ a b c k0 k1 spring m2 J T v t : Q) :
    mirrorSum
      (fun Tz => generalizedHamiltonian α β γ δ a b c k0 k1 spring m2 J T v Tz) t =
      2 * (casimirHamiltonian α β γ δ m2 J T v + a + pairHamiltonian k0 k1 + spring) +
        2 * c * t ^ 2 := by
  unfold mirrorSum generalizedHamiltonian imme
  ring

theorem pd94_isospinCasimir_eq_two :
    pd94_isospinCasimir = 2 := by
  norm_num [pd94_isospinCasimir, pd94_T, isospinCasimir]

theorem pd94_massCasimir_eq_neg :
    pd94_massCasimir = -94 := by
  norm_num [pd94_massCasimir, pd94_massNumber, massCasimir]

theorem pd94_springStiffness_eq :
    pd94_springStiffness = 94 := by
  norm_num [pd94_springStiffness, pd94_massCasimir, pd94_massNumber, massCasimir,
    casimirStiffness]

end CasimirIsospinHamiltonian

end noncomputable section
