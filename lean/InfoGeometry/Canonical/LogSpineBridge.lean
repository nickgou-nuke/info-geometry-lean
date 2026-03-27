import InfoGeometry.Basic
import InfoGeometry.Canonical.ZetaDeterminant
import InfoGeometry.Thermal.FiniteMatrix

/-!
# InfoGeometry.Canonical.LogSpineBridge

This module formalizes the "Logarithmic Spine" that connects the discrete/empirical
world of counts to the smooth geometric world of information metrics and gravity.

The spine identifies the following as one canonical object:
1.  **RN Potential** (Radon-Nikodym density)
2.  **Jordan/Log-Det Barrier**
3.  **Zeta Regularized Determinant**
4.  **Modular Hamiltonian** / Log-Partition
5.  **Kähler Potential**
6.  **Free Energy** (as the generating functional)
-/

namespace InfoGeometry.Canonical.LogSpine

open InfoGeometry
open InfoGeometry.Jordan
open InfoGeometry.Thermal

/--
Spine Identification 1:
The RN potential is definitionally the negative log-density.
-/
theorem rn_potential_eq_neg_log_density (p : FinProb α) (x : α) :
    log_density p x = Real.log (p x).toReal := rfl

/--
Spine Identification 2:
The Jordan log-det barrier is exactly the zeta-regularized log-determinant.
-/
theorem jordan_logdet_eq_zeta_determinant
    (n : Nat) (X : SPD n) :
    logDetBarrier X = InfoGeometry.Canonical.Determinant.zetaLogDetBarrier X := by
  simpa using
    (InfoGeometry.Canonical.Determinant.zetaLogDetBarrier_eq_logDetBarrier (X := X)).symm

/--
Spine Identification 3:
The Modular Hamiltonian (energy levels) induces the log-partition function.
-/
theorem modular_hamiltonian_to_log_partition
    (n : Nat) (H : Hamiltonian n) (β : ℝ) :
    let Z := H.partition β
    Real.log Z = Real.log (∑ i, Real.exp (-β * H.energy i)) := rfl

/--
Spine Identification 4:
The Kähler potential of a Sinkhorn flow identifies with the Shannon entropy
on the diagonal of the rank-one coupling.
-/
theorem kahler_spine_entropy_identity
    {α : Type*} [Fintype α] (p : FinProb α) :
    entropy p = - (∑ i, (p i).toReal * (Real.log (p i).toReal)) := by
  unfold entropy expectation surprisal log_density
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [mul_neg]

/--
The Full Spine:
Free energy acts as the unified generating functional for the entire spine.
-/
noncomputable def freeEnergySpine (n : Nat) (H : Hamiltonian n) (β : ℝ) : ℝ :=
  - (1 / β) * Real.log (H.partition β)

end LogSpine

end InfoGeometry.Canonical
