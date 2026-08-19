import proofs.ChiralCausalCone
import proofs.GNSModularObservables
import proofs.EntropicChiralDeRhamFormalization

/-!
# Chiral cone algebra finality

This module packages the local alphabet

`{N₊, N₋, s₊, s₋, s₃}`

as a theorem-honest capstone over `ChiralCausalCone`.  It proves the finite `M₂(ℂ)`
matrix facts in the kernel:

* `s₊²=s₋²=0`;
* `N₊=s₊s₋`, `N₋=s₋s₊`;
* `N₊+N₋=1`, `N₊N₋=0`;
* `s₃=N₊-N₋`;
* `[s₃,s₊]=2s₊`, `[s₃,s₋]=-2s₋`;
* the normalized GNS trace gives `τ(N₊)=τ(N₋)=1/2`;
* the determinant of the nilpotent transitions vanishes.
-/

noncomputable section

namespace ChiralConeAlgebraFinality

open Matrix
open ChiralCausalCone

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Chiral raising/null transition. -/
def sPlus : M2C := σPlus

/-- Chiral lowering/null transition. -/
def sMinus : M2C := σMinus

/-- Positive/source occupation projector. -/
def NPlus : M2C := sPlus * sMinus

/-- Negative/range occupation projector. -/
def NMinus : M2C := sMinus * sPlus

/-- Chiral parity/grading axis. -/
def s3 : M2C := NPlus - NMinus

/-- Determinant-barrier potential on the local `2x2` tile. -/
def detQ (A : M2C) : ℂ := A.det

/-- Normalized GNS trace inherited from `GNSModularObservables`. -/
def τ (A : M2C) : ℂ := GNSModularObservables.gnsTrace A

@[simp] theorem NPlus_eq_PPlus : NPlus = PPlus := rfl

@[simp] theorem NMinus_eq_PMinus : NMinus = PMinus := rfl

@[simp] theorem s3_eq_σ3c : s3 = σ3c := by
  unfold s3 NPlus NMinus sPlus sMinus
  exact comm_σPlus_σMinus

@[simp] theorem sPlus_sq_zero : sPlus * sPlus = 0 := σPlus_sq

@[simp] theorem sMinus_sq_zero : sMinus * sMinus = 0 := σMinus_sq

theorem nilpotent_transitions_have_zero_det :
    detQ sPlus = 0 ∧ detQ sMinus = 0 := by
  constructor <;>
    simp [detQ, sPlus, sMinus, σPlus, σMinus, Matrix.det_fin_two]

@[simp] theorem NPlus_idempotent : NPlus * NPlus = NPlus := PPlus_idempotent

@[simp] theorem NMinus_idempotent : NMinus * NMinus = NMinus := PMinus_idempotent

@[simp] theorem NPlus_NMinus_zero : NPlus * NMinus = 0 := PPlus_PMinus_orthogonal

@[simp] theorem NMinus_NPlus_zero : NMinus * NPlus = 0 := PMinus_PPlus_orthogonal

theorem chiral_projector_completeness : NPlus + NMinus = (1 : M2C) :=
  PPlus_add_PMinus

theorem chiral_parity_from_projectors : s3 = NPlus - NMinus := rfl

theorem chiral_parity_sq : s3 * s3 = (1 : M2C) := by
  rw [s3_eq_σ3c]
  exact σ3c_sq

theorem chiral_lie_axis_relations :
    s3 * sPlus - sPlus * s3 = (2 : ℂ) • sPlus ∧
    s3 * sMinus - sMinus * s3 = (-2 : ℂ) • sMinus := by
  rw [s3_eq_σ3c]
  exact ⟨comm_σ3_σPlus, comm_σ3_σMinus⟩

theorem chiral_transition_car :
    sPlus * sMinus + sMinus * sPlus = (1 : M2C) ∧
    sPlus * sMinus - sMinus * sPlus = s3 := by
  rw [s3_eq_σ3c]
  exact ⟨anti_σPlus_σMinus, comm_σPlus_σMinus⟩

theorem thermal_self_dual_occupations :
    τ NPlus = 1 / 2 ∧ τ NMinus = 1 / 2 ∧ τ (NPlus + NMinus) = 1 := by
  simpa [τ, NPlus_eq_PPlus, NMinus_eq_PMinus] using
    GNSModularObservables.gnsTrace_chiral_projectors

theorem apex_pauli_exclusion :
    NPlus * NMinus = 0 ∧ NMinus * NPlus = 0 := by
  exact ⟨NPlus_NMinus_zero, NMinus_NPlus_zero⟩

/-- Finite capstone for the requested alphabet.  The kernel proves the local
matrix algebra. -/
theorem chiral_cone_alphabet_synthesis :
    sPlus * sPlus = 0 ∧
    sMinus * sMinus = 0 ∧
    detQ sPlus = 0 ∧
    detQ sMinus = 0 ∧
    NPlus * NPlus = NPlus ∧
    NMinus * NMinus = NMinus ∧
    NPlus + NMinus = (1 : M2C) ∧
    NPlus * NMinus = 0 ∧
    s3 = NPlus - NMinus ∧
    s3 * s3 = (1 : M2C) ∧
    s3 * sPlus - sPlus * s3 = (2 : ℂ) • sPlus ∧
    s3 * sMinus - sMinus * s3 = (-2 : ℂ) • sMinus ∧
    τ NPlus = 1 / 2 ∧
    τ NMinus = 1 / 2 := by
  rcases nilpotent_transitions_have_zero_det with ⟨hDetPlus, hDetMinus⟩
  rcases chiral_lie_axis_relations with ⟨hPlus, hMinus⟩
  rcases thermal_self_dual_occupations with ⟨hTauPlus, hTauMinus, _hTauUnit⟩
  exact ⟨sPlus_sq_zero, sMinus_sq_zero, hDetPlus, hDetMinus,
    NPlus_idempotent, NMinus_idempotent, chiral_projector_completeness,
    NPlus_NMinus_zero, chiral_parity_from_projectors, chiral_parity_sq,
    hPlus, hMinus, hTauPlus, hTauMinus⟩

#check sPlus_sq_zero
#check sMinus_sq_zero
#check nilpotent_transitions_have_zero_det
#check chiral_projector_completeness
#check chiral_lie_axis_relations
#check thermal_self_dual_occupations
#check chiral_cone_alphabet_synthesis

end ChiralConeAlgebraFinality

end noncomputable section
