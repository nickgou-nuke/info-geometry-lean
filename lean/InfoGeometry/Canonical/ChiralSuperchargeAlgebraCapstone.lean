import InfoGeometry.Quantum.ChiralSuperchargeAlgebra

namespace InfoGeometry.Canonical.ChiralSuperchargeAlgebraCapstone

open InfoGeometry.Quantum.ChiralSuperchargeAlgebra

/-! Direct finite synthesis: each sector uses the native CCR/CAR lemma, while
the balance and critical-line conclusions use their scalar owners. -/
theorem capstone_chiral_supercharge_synthesis
    {R : Type*} [CommRing R]
    (a_L a_dag_L f_L f_dag_L : R)
    (a_R a_dag_R f_R f_dag_R : R)
    (h_boson_L : a_L * a_dag_L = 1 + a_dag_L * a_L)
    (h_fermion_L : f_L * f_dag_L = 1 - f_dag_L * f_L)
    (h_boson_R : a_R * a_dag_R = 1 + a_dag_R * a_R)
    (h_fermion_R : f_R * f_dag_R = 1 - f_dag_R * f_R)
    (N_L N_R : ℝ) (hJ : chiralParityCurrent N_L N_R = 0)
    (σ : ℝ) (h_xi : σ - 1 / 2 = 0) :
    (Anticommutator (chiralSuperchargeQ a_dag_L f_L)
        (chiralSuperchargeQbar a_L f_dag_L) =
      chiralNumberOperator a_dag_L a_L f_dag_L f_L) ∧
    (Anticommutator (chiralSuperchargeQ a_dag_R f_R)
        (chiralSuperchargeQbar a_R f_dag_R) =
      chiralNumberOperator a_dag_R a_R f_dag_R f_R) ∧
    (N_L = N_R) ∧
    (σ = 1 / 2) := by
  exact ⟨chiral_supercharge_anticommutator a_L a_dag_L f_L f_dag_L
      h_boson_L h_fermion_L,
    chiral_supercharge_anticommutator a_R a_dag_R f_R f_dag_R
      h_boson_R h_fermion_R,
    chiral_parity_balance_confinement N_L N_R hJ,
    chiral_rapidity_critical_line σ h_xi⟩

end InfoGeometry.Canonical.ChiralSuperchargeAlgebraCapstone
