import Mathlib

/-!
# Two-strand Jones projector and spin Casimir

The carrier is the finite coordinate realization of two spinor factors,
`Fin 2 → Fin 2 → ℂ`.  It is the standard basis model of the tensor product
of two two-component spinor spaces.  All identities below are explicit finite
matrix identities; no infinite-dimensional or representation-theoretic
assumption is used.
-/

noncomputable section

namespace InfoGeometry.Physics.TwoStrandJonesCasimir

open scoped Matrix

abbrev Spinor := Fin 2 → ℂ
abbrev TwoStrandState := Fin 2 → Fin 2 → ℂ
abbrev TwoStrandOperator := Module.End ℂ TwoStrandState

def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def leftAction (A : Matrix (Fin 2) (Fin 2) ℂ) : TwoStrandOperator where
  toFun ψ i j := ∑ k : Fin 2, A i k * ψ k j
  map_add' ψ φ := by
    funext i j
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c ψ := by
    funext i j
    simp [Fin.sum_univ_succ]
    ring

def rightAction (A : Matrix (Fin 2) (Fin 2) ℂ) : TwoStrandOperator where
  toFun ψ i j := ∑ k : Fin 2, A j k * ψ i k
  map_add' ψ φ := by
    funext i j
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c ψ := by
    funext i j
    simp [Fin.sum_univ_succ]
    ring

def singletProjector : TwoStrandOperator where
  toFun ψ i j :=
    let c := (1 / 2 : ℂ) * (ψ 0 1 - ψ 1 0)
    if i = 0 ∧ j = 1 then c
    else if i = 1 ∧ j = 0 then -c else 0
  map_add' ψ φ := by
    funext i j
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c ψ := by
    funext i j
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp only [RingHom.id_apply] <;> ring

def spinX : TwoStrandOperator :=
  (1 / 2 : ℂ) • (leftAction sigmaX + rightAction sigmaX)

def spinY : TwoStrandOperator :=
  (1 / 2 : ℂ) • (leftAction sigmaY + rightAction sigmaY)

def spinZ : TwoStrandOperator :=
  (1 / 2 : ℂ) • (leftAction sigmaZ + rightAction sigmaZ)

def spinSquared : TwoStrandOperator :=
  spinX.comp spinX + spinY.comp spinY + spinZ.comp spinZ

theorem singletProjector_idem :
    singletProjector.comp singletProjector = singletProjector := by
  apply LinearMap.ext
  intro ψ
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [singletProjector]
    <;> ring

theorem spinSquared_eq_two_complement_singlet :
    spinSquared = 2 • ((1 : TwoStrandOperator) - singletProjector) := by
  apply LinearMap.ext
  intro ψ
  funext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [spinSquared, spinX, spinY, spinZ, leftAction, rightAction,
      sigmaX, sigmaY, sigmaZ, singletProjector, Fin.sum_univ_succ,
      LinearMap.comp_apply]
    simp_rw [← mul_assoc]
    try simp [Complex.I_mul_I]
    ring_nf
    rw [Complex.I_sq]
    ring

def twoStrandCasimir (M : ℂ) : TwoStrandOperator :=
  (-M ^ 2) • spinSquared

theorem twoStrandCasimir_eq_projector_polynomial (M : ℂ) :
    twoStrandCasimir M =
      (-2 * M ^ 2) • ((1 : TwoStrandOperator) - singletProjector) := by
  rw [twoStrandCasimir, spinSquared_eq_two_complement_singlet]
  module

end InfoGeometry.Physics.TwoStrandJonesCasimir
