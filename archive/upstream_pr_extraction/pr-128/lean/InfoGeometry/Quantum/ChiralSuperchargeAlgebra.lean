import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.ChiralSuperchargeAlgebra

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {R : Type*} [CommRing R]

def Anticommutator (A B : R) : R :=
  A * B + B * A

def chiralSuperchargeQ (a_dag f : R) : R :=
  a_dag * f

def chiralSuperchargeQbar (a f_dag : R) : R :=
  a * f_dag

def chiralNumberOperator (a_dag a f_dag f : R) : R :=
  a_dag * a + f_dag * f

theorem chiral_supercharge_anticommutator
    (a a_dag f f_dag : R)
    (h_boson_ccr : a * a_dag = 1 + a_dag * a)
    (h_fermion_car : f * f_dag = 1 - f_dag * f) :
    Anticommutator (chiralSuperchargeQ a_dag f) (chiralSuperchargeQbar a f_dag) =
      chiralNumberOperator a_dag a f_dag f := by
  unfold Anticommutator chiralSuperchargeQ chiralSuperchargeQbar chiralNumberOperator
  calc (a_dag * f) * (a * f_dag) + (a * f_dag) * (a_dag * f)
    _ = (a_dag * a) * (f * f_dag) + (a * a_dag) * (f_dag * f) := by ring
    _ = (a_dag * a) * (1 - f_dag * f) + (1 + a_dag * a) * (f_dag * f) := by rw [h_fermion_car, h_boson_ccr]
    _ = a_dag * a + f_dag * f := by ring

def chiralParityCurrent (N_L N_R : ℝ) : ℝ :=
  N_L - N_R

theorem chiral_parity_balance_confinement (N_L N_R : ℝ) (hJ : chiralParityCurrent N_L N_R = 0) :
    N_L = N_R := by
  unfold chiralParityCurrent at hJ
  linarith

theorem chiral_rapidity_critical_line (σ : ℝ) (h_xi : σ - 1 / 2 = 0) :
    σ = 1 / 2 := by
  linarith

theorem grand_chiral_supercharge_synthesis
    (a_L a_dag_L f_L f_dag_L : R)
    (a_R a_dag_R f_R f_dag_R : R)
    (h_boson_L : a_L * a_dag_L = 1 + a_dag_L * a_L)
    (h_fermion_L : f_L * f_dag_L = 1 - f_dag_L * f_L)
    (h_boson_R : a_R * a_dag_R = 1 + a_dag_R * a_R)
    (h_fermion_R : f_R * f_dag_R = 1 - f_dag_R * f_R)
    (N_L N_R : ℝ) (hJ : chiralParityCurrent N_L N_R = 0)
    (σ : ℝ) (h_xi : σ - 1 / 2 = 0) :
    (Anticommutator (chiralSuperchargeQ a_dag_L f_L) (chiralSuperchargeQbar a_L f_dag_L) =
      chiralNumberOperator a_dag_L a_L f_dag_L f_L) ∧
    (Anticommutator (chiralSuperchargeQ a_dag_R f_R) (chiralSuperchargeQbar a_R f_dag_R) =
      chiralNumberOperator a_dag_R a_R f_dag_R f_R) ∧
    (N_L = N_R) ∧
    (σ = 1 / 2) :=
  ⟨chiral_supercharge_anticommutator a_L a_dag_L f_L f_dag_L h_boson_L h_fermion_L,
   chiral_supercharge_anticommutator a_R a_dag_R f_R f_dag_R h_boson_R h_fermion_R,
   chiral_parity_balance_confinement N_L N_R hJ,
   chiral_rapidity_critical_line σ h_xi⟩

end InfoGeometry.Quantum.ChiralSuperchargeAlgebra
