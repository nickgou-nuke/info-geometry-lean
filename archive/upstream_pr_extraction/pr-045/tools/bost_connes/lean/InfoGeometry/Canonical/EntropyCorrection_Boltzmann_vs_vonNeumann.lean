import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.DeRhamBoltzmannModular
import InfoGeometry.Capstone.GrandIdentityDeRhamModular

noncomputable section

namespace InfoGeometry.Canonical.EntropyCorrection

open InfoGeometry
open InfoGeometry.Capstone.GrandIdentityDeRhamModular

/-!
# EntropyCorrection_Boltzmann_vs_vonNeumann

This auxiliary file records a theorem-honest local packet separating two scalar
surfaces:

- the Boltzmann log-potential `S_B(β) = log Q(β)`, and
- a packaged von Neumann-style readout `S_vN(β) = S_B(β) + β * Kexp(β)`.

It does not prove a global operator-algebraic identification of von Neumann
entropy, nor any de Rham/modular/time equivalence.  It only packages exact
scalar formulas already verified elsewhere in the repository.
-/

/-- Scalar Boltzmann entropy packet. -/
def boltzmannEntropy (Q : ℝ → ℝ) (β : ℝ) : ℝ :=
  Real.log (Q β)

/-- Auxiliary scalar readout in the von-Neumann-style Legendre packet. -/
def vonNeumannPacket (Q Kexp : ℝ → ℝ) (β : ℝ) : ℝ :=
  boltzmannEntropy Q β + β * Kexp β

@[simp] theorem boltzmannEntropy_eq_log (Q : ℝ → ℝ) (β : ℝ) :
    boltzmannEntropy Q β = Real.log (Q β) := rfl

@[simp] theorem vonNeumannPacket_eq_boltzmann_plus_beta_expectation
    (Q Kexp : ℝ → ℝ) (β : ℝ) :
    vonNeumannPacket Q Kexp β = boltzmannEntropy Q β + β * Kexp β := rfl

/--
Exact local derivative consequence for the auxiliary packet.
-/
theorem first_law_packet
    (Q Kexp : ℝ → ℝ) (β : ℝ)
    (hB : DifferentiableAt ℝ (boltzmannEntropy Q) β)
    (hK : DifferentiableAt ℝ Kexp β)
    (hBoltzFlat : deriv (boltzmannEntropy Q) β = 0) :
    deriv (vonNeumannPacket Q Kexp) β = Kexp β + β * deriv Kexp β := by
  change deriv (fun x => boltzmannEntropy Q x + x * Kexp x) β =
    Kexp β + β * deriv Kexp β
  have hfun : (fun x => boltzmannEntropy Q x + x * Kexp x) =
      ((boltzmannEntropy Q) + (Kexp * fun x => x)) := by
    funext x
    simp [Pi.add_apply, Pi.mul_apply, mul_comm, add_comm]
  rw [hfun]
  have hProd : HasDerivAt (Kexp * fun x => x) (Kexp β + β * deriv Kexp β) β := by
    simpa [one_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
      using hK.hasDerivAt.mul (hasDerivAt_id' β)
  have hSum : HasDerivAt ((boltzmannEntropy Q) + (Kexp * fun x => x))
      (0 + (Kexp β + β * deriv Kexp β)) β := by
    simpa [hBoltzFlat] using hB.hasDerivAt.add hProd
  simpa using hSum.deriv

/--
The de Rham scalar `d(log Q)` is exactly the rescaled derivative of the
Boltzmann packet.
-/
theorem de_rham_is_boltzmann_gradient (Q : ℝ) (kB : ℝ) (_hQ : 0 < Q) (hkB : kB ≠ 0) :
    deriv Real.log Q = (1 / kB) * deriv (fun q => kB * Real.log q) Q := by
  rw [deriv_const_mul_field]
  field_simp [hkB]

/--
The scalar Boltzmann derivative equals `kB * d(log Q)`.
-/
theorem boltzmann_gradient_eq_kB_log_deriv (Q : ℝ) (kB : ℝ) (_hQ : 0 < Q) :
    deriv (fun q => kB * Real.log q) Q = kB * deriv Real.log Q := by
  rw [deriv_const_mul_field]

/--
Concrete two-level specialization imported from the verified scalar packet.
-/
@[simp] theorem twoLevel_boltzmannEntropy_eq
    (r β : ℝ) :
    boltzmannEntropy (partitionQ r) β = entropyPotential r β := by
  rfl

/--
The two-level partition function is pointwise positive.
-/
theorem twoLevel_partition_pos (r β : ℝ) : 0 < partitionQ r β :=
  partitionQ_pos r β

/--
There exists a concrete local witness for the entropy-correction packet.
-/
theorem exists_twoLevel_entropy_packet :
    ∃ Q : ℝ → ℝ, ∀ β : ℝ, 0 < Q β := by
  refine ⟨partitionQ 1, ?_⟩
  intro β
  exact partitionQ_pos 1 β

end InfoGeometry.Canonical.EntropyCorrection
