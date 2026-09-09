import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.TraceFormula.ItakuraSaitoMongeAmpere
import InfoGeometry.Canonical.NormalizedISZetaDeterminantBridge
import InfoGeometry.TraceFormula.DeRhamHolonomyStokes
import InfoGeometry.TraceFormula.FiniteISColimitInverseLimitSearch
import InfoGeometry.KMSGNS

/-!
# Finite-to-colimit Primon Hamiltonian readouts

This file assembles the existing finite matrix tower, finite Itakura--Saito
channel, normalized colimit trace, and finite holonomy confinement theorem.  The backward
state lane is represented by its explicit compatible family of linear
readouts; no completed projective-limit object or uniqueness theorem is
introduced here.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.PrimonHamiltonianColimit

open Matrix
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.TraceFormula.ColimitTrace
open InfoGeometry.TraceFormula.ItakuraSaito
open InfoGeometry.TraceFormula.DeRhamHolonomy
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.NormalizedISZetaDeterminantBridge

/-! ## Finite stage -/

/-- The finite Itakura--Saito energy relative to the identity reference. -/
def stageEffectiveHamiltonian (n : ℕ) (P : MatrixStage n) : ℝ :=
  itakuraSaitoDivergence n P (1 : MatrixStage n)

/-- The finite inverse-congruence Hessian readout. -/
def stageFisherHessian (n : ℕ) (P X : MatrixStage n) : MatrixStage n :=
  P⁻¹ * X * P⁻¹

/-- The inverse-congruence Hessian is self-adjoint for the trace pairing. -/
theorem stageFisherHessian_selfAdjoint (n : ℕ) (P X Y : MatrixStage n) :
    rawTrace n (Y * stageFisherHessian n P X) =
      rawTrace n (stageFisherHessian n P Y * X) := by
  unfold rawTrace stageFisherHessian
  calc
    Matrix.trace (Y * (P⁻¹ * X * P⁻¹)) =
        Matrix.trace ((Y * P⁻¹ * X) * P⁻¹) := by
          simp only [mul_assoc]
    _ = Matrix.trace (P⁻¹ * (Y * P⁻¹ * X)) := by
          exact Matrix.trace_mul_comm (Y * P⁻¹ * X) P⁻¹
    _ = Matrix.trace ((P⁻¹ * Y * P⁻¹) * X) := by
          simp only [mul_assoc]

/-! The inverse-congruence Hessian is compatible with the native matrix bond.
    The only hypothesis is the same finite nonsingularity condition used by
    the determinant owner for transport of inverses. -/

theorem stageFisherHessian_bond_compatible
    (n : ℕ) (P X : MatrixStage n) (hP : IsUnit P.det) :
    stageFisherHessian (n + 1) (matrixBond n P) (matrixBond n X) =
      matrixBond n (stageFisherHessian n P X) := by
  unfold stageFisherHessian
  rw [matrixBond_inv n P hP]
  rw [← map_mul, ← map_mul]

theorem isUnit_det_matrixBond
    (n : ℕ) (Q : MatrixStage n) (hQ : IsUnit Q.det) :
    IsUnit (matrixBond n Q).det := by
  rw [determinant_bond_block]
  exact IsUnit.pow 2 hQ

theorem isUnit_det_bondMap
    (m n : ℕ) (h : m ≤ n) (Q : MatrixStage m) (hQ : IsUnit Q.det) :
    IsUnit (bondMap matrixBond m n h Q).det := by
  refine Nat.le_induction
    (m := m)
    (P := fun t _ => ∀ ht : m ≤ t, IsUnit (bondMap matrixBond m t ht Q).det)
    ?base ?succ n h
    h
  · intro ht
    have hproof : ht = le_rfl := Subsingleton.elim ht le_rfl
    subst hproof
    rw [bondMap_refl]
    exact hQ
  · intro t hmt iht ht
    have hproof : ht = Nat.le_trans hmt (Nat.le_succ t) :=
      Subsingleton.elim ht (Nat.le_trans hmt (Nat.le_succ t))
    subst hproof
    rw [bondMap_succ matrixBond m t hmt]
    dsimp
    exact isUnit_det_matrixBond t (bondMap matrixBond m t hmt Q) (iht hmt)

theorem bondMap_apply_succ
    (m n : ℕ) (h : m ≤ n) (x : MatrixStage m) :
    bondMap matrixBond m (n + 1) (Nat.le_trans h (Nat.le_succ n)) x =
      matrixBond n (bondMap matrixBond m n h x) := by
  have h_eq := bondMap_succ matrixBond m n h
  rw [h_eq]
  rfl

theorem stageFisherHessian_bondMap_compatible
    (m n : ℕ) (h : m ≤ n) (P X : MatrixStage m) (hP : IsUnit P.det) :
    stageFisherHessian n (bondMap matrixBond m n h P)
        (bondMap matrixBond m n h X) =
      bondMap matrixBond m n h (stageFisherHessian m P X) := by
  refine Nat.le_induction
    (m := m)
    (P := fun t _ => ∀ ht : m ≤ t,
      stageFisherHessian t (bondMap matrixBond m t ht P)
          (bondMap matrixBond m t ht X) =
        bondMap matrixBond m t ht (stageFisherHessian m P X))
    ?base ?succ n h
    h
  · intro ht
    have hproof : ht = le_rfl := Subsingleton.elim ht le_rfl
    subst hproof
    rw [bondMap_refl]
    rfl
  · intro t hmt iht ht
    have hproof : ht = Nat.le_trans hmt (Nat.le_succ t) :=
      Subsingleton.elim ht (Nat.le_trans hmt (Nat.le_succ t))
    subst hproof
    have hBondDet : IsUnit (bondMap matrixBond m t hmt P).det :=
      isUnit_det_bondMap m t hmt P hP
    rw [bondMap_apply_succ m t hmt P,
        bondMap_apply_succ m t hmt X,
        bondMap_apply_succ m t hmt (stageFisherHessian m P X)]
    rw [stageFisherHessian_bond_compatible t (bondMap matrixBond m t hmt P) (bondMap matrixBond m t hmt X) hBondDet]
    rw [iht hmt]

theorem stageFisherHessian_normalizedTrace_selfAdjoint
    (n : ℕ) (P X Y : MatrixStage n) :
    normalizedTrace n (Y * stageFisherHessian n P X) =
      normalizedTrace n (stageFisherHessian n P Y * X) := by
  simpa [normalizedTrace] using
    congrArg (fun t : ℝ => t / (2 ^ n : ℝ))
      (stageFisherHessian_selfAdjoint n P X Y)

/-! The normalized trace pairing is preserved by the Hessian bond. -/

theorem stageFisherHessian_pairing_bond_compatible
    (n : ℕ) (P X Y : MatrixStage n) (hP : IsUnit P.det) :
    normalizedTrace (n + 1)
        (matrixBond n Y *
          stageFisherHessian (n + 1) (matrixBond n P) (matrixBond n X)) =
      normalizedTrace n (Y * stageFisherHessian n P X) := by
  rw [stageFisherHessian_bond_compatible n P X hP]
  rw [← map_mul]
  exact normalizedTrace_compatible n
    (Y * stageFisherHessian n P X)

theorem stageEffectiveHamiltonian_identity_minimum (n : ℕ) :
    stageEffectiveHamiltonian n (1 : MatrixStage n) = -Real.log 1 := by
  unfold stageEffectiveHamiltonian
  apply itakuraSaito_self
  simp

theorem stageEffectiveHamiltonian_bond_compatible
    (n : ℕ) (P : MatrixStage n) :
    stageEffectiveHamiltonian (n + 1) (matrixBond n P) =
      2 * stageEffectiveHamiltonian n P := by
  unfold stageEffectiveHamiltonian
  simpa only [map_one] using
    (itakuraSaito_bond_compatible n P (1 : MatrixStage n) (by simp))

theorem normalized_stageEffectiveHamiltonian_bond_compatible
    (n : ℕ) (P : MatrixStage n) :
    (1 / (2 ^ (n + 1) : ℝ)) *
        stageEffectiveHamiltonian (n + 1) (matrixBond n P) =
      (1 / (2 ^ n : ℝ)) * stageEffectiveHamiltonian n P := by
  rw [stageEffectiveHamiltonian_bond_compatible n P]
  have hpow : (2 ^ (n + 1) : ℝ) = 2 ^ n * 2 := by ring
  rw [hpow]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

theorem normalized_stageEffectiveHamiltonian_bondMap_compatible
    (m n : ℕ) (h : m ≤ n) (P : MatrixStage m) :
    (1 / (2 ^ n : ℝ)) *
        stageEffectiveHamiltonian n (bondMap matrixBond m n h P) =
      (1 / (2 ^ m : ℝ)) * stageEffectiveHamiltonian m P := by
  simpa only [stageEffectiveHamiltonian, map_one] using
    (normalized_itakuraSaito_bondMap_compatible m n h P
      (1 : MatrixStage m) (by simp))

/-! ## Forward colimit -/

/-- A finite Hamiltonian observable viewed in the algebraic colimit. -/
def colimitHamiltonianObservable (n : ℕ) (H : MatrixStage n) :
    PrimonUHFAlgebra :=
  toColimit n H

/-- The nonlinear normalized Itakura--Saito energy descended to the
algebraic matrix colimit.  Its well-definedness uses the arbitrary-jump
compatibility theorem, not linearity of the energy. -/
noncomputable def colimitEffectiveHamiltonian : PrimonUHFAlgebra → ℝ :=
  DirectLimit.lift
    (fun _ _ hij => bondMap matrixBond _ _ hij)
    (fun n P => (1 / (2 ^ n : ℝ)) * stageEffectiveHamiltonian n P)
    (by
      intro m n h P
      exact (normalized_stageEffectiveHamiltonian_bondMap_compatible m n h P).symm)

@[simp] theorem colimitEffectiveHamiltonian_stage
    (n : ℕ) (P : MatrixStage n) :
    colimitEffectiveHamiltonian (toColimit n P) =
      (1 / (2 ^ n : ℝ)) * stageEffectiveHamiltonian n P := by
  rfl

theorem colimitEffectiveHamiltonian_diagonal_zeta_readout
    (n : ℕ) (lam : BitWord n → ℝ) (hpos : ∀ i, 0 < lam i) :
    colimitEffectiveHamiltonian
        (toColimit n (Matrix.diagonal lam)) =
      normalizedTrace n (Matrix.diagonal lam) +
        normalizedSpectralZetaDerivativeAtZero lam - 1 := by
  rw [colimitEffectiveHamiltonian_stage]
  exact normalizedDiagonalItakuraSaito_eq_trace_plus_zetaDerivative_sub_one n lam hpos

@[simp] theorem colimitEffectiveHamiltonian_bond
    (n : ℕ) (P : MatrixStage n) :
    colimitEffectiveHamiltonian
        (toColimit (n + 1) (matrixBond n P)) =
      colimitEffectiveHamiltonian (toColimit n P) := by
  rw [colimitEffectiveHamiltonian_stage, colimitEffectiveHamiltonian_stage]
  exact normalized_stageEffectiveHamiltonian_bond_compatible n P

theorem colimitEffectiveHamiltonian_bondMap
    (m n : ℕ) (h : m ≤ n) (P : MatrixStage m) :
    colimitEffectiveHamiltonian
        (toColimit n (bondMap matrixBond m n h P)) =
      colimitEffectiveHamiltonian (toColimit m P) := by
  rw [colimitEffectiveHamiltonian_stage, colimitEffectiveHamiltonian_stage]
  exact normalized_stageEffectiveHamiltonian_bondMap_compatible m n h P

@[simp] theorem colimitHamiltonian_bond (n : ℕ) (H : MatrixStage n) :
    colimitHamiltonianObservable (n + 1) (matrixBond n H) =
      colimitHamiltonianObservable n H := by
  exact toColimit_bond n H

/-! ## Compatible backward state readouts -/

/-- The normalized state at each finite stage. -/
abbrev projectiveTracialSequence (n : ℕ) : MatrixStage n →ₗ[ℝ] ℝ :=
  normalizedTraceLin n

/-! The nonlinear energy has its own compatible inverse-side family.  It is
kept as a function family rather than incorrectly packaged as a linear map. -/
def projectiveEffectiveHamiltonian (n : ℕ) : MatrixStage n → ℝ :=
  fun P => (1 / (2 ^ n : ℝ)) * stageEffectiveHamiltonian n P

theorem projectiveEffectiveHamiltonian_compatible
    (m n : ℕ) (h : m ≤ n) (P : MatrixStage m) :
    projectiveEffectiveHamiltonian n (bondMap matrixBond m n h P) =
      projectiveEffectiveHamiltonian m P := by
  exact normalized_stageEffectiveHamiltonian_bondMap_compatible m n h P

theorem projectiveEffectiveHamiltonian_stage
    (n : ℕ) (P : MatrixStage n) :
    projectiveEffectiveHamiltonian n P =
      colimitEffectiveHamiltonian (toColimit n P) := by
  rfl

/-- The nonlinear Itakura--Saito readout as an explicit coherent inverse-side
family. -/
def projectiveEffectiveHamiltonianFamily :
    {ρ : ∀ n : ℕ, MatrixStage n → ℝ //
      ∀ (m n : ℕ) (h : m ≤ n) (P : MatrixStage m),
        ρ n (bondMap matrixBond m n h P) = ρ m P} :=
  ⟨projectiveEffectiveHamiltonian, projectiveEffectiveHamiltonian_compatible⟩

@[simp] theorem projectiveEffectiveHamiltonianFamily_apply
    (n : ℕ) (P : MatrixStage n) :
    projectiveEffectiveHamiltonianFamily.1 n P =
      projectiveEffectiveHamiltonian n P :=
  rfl

theorem projectiveEffectiveHamiltonianFamily_compatible
    (m n : ℕ) (h : m ≤ n) (P : MatrixStage m) :
    projectiveEffectiveHamiltonianFamily.1 n
        (bondMap matrixBond m n h P) =
      projectiveEffectiveHamiltonianFamily.1 m P := by
  exact projectiveEffectiveHamiltonianFamily.2 m n h P

/-! The descended functional is characterized uniquely by its finite-stage
readbacks. -/

theorem colimitEffectiveHamiltonian_unique
    (F : PrimonUHFAlgebra → ℝ)
    (hF : ∀ (n : ℕ) (P : MatrixStage n),
      F (toColimit n P) =
        (1 / (2 ^ n : ℝ)) * stageEffectiveHamiltonian n P) :
    F = colimitEffectiveHamiltonian := by
  funext x
  induction x using DirectLimit.induction with
  | _ n P =>
      change F (toColimit n P) = colimitEffectiveHamiltonian (toColimit n P)
      rw [hF n P]
      rfl

theorem projective_trace_step (n : ℕ) (M : MatrixStage n) :
    projectiveTracialSequence (n + 1) (matrixBond n M) =
      projectiveTracialSequence n M := by
  change normalizedTrace (n + 1) (matrixBond n M) = normalizedTrace n M
  exact normalizedTrace_compatible n M

theorem projective_trace_iterated
    (m n : ℕ) (h : m ≤ n) (M : MatrixStage m) :
    projectiveTracialSequence n
        (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap
          matrixBond m n h M) =
      projectiveTracialSequence m M := by
  exact normalizedTraceLin_compatible m n h M

theorem colimit_vacuum_energy_evaluation (n : ℕ) (M : MatrixStage n) :
      InfoGeometry.TraceFormula.ColimitTrace.colimitTrace
        (colimitHamiltonianObservable n M) =
      projectiveTracialSequence n M := by
  change InfoGeometry.TraceFormula.ColimitTrace.colimitTrace (toColimit n M) =
    normalizedTrace n M
  exact InfoGeometry.TraceFormula.ColimitTrace.colimitTrace_evaluate_ringhom n M

/-! ## Native inverse-limit carrier -/

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology

variable {A : Type*} [TopologicalSpace A] [CompactSpace A] [T2Space A]

/-- The compact-Hausdorff inverse-limit carrier already owned by the topology
    subsystem.  This is a carrier comparison, not a new projective trace. -/
abbrev inverseLimitCarrier : CompHaus :=
  symbolicBoundaryPrefixLimitCompHaus (A := A)

def inverseLimitCarrierIso :
    symbolicBoundaryCompHaus (A := A) ≅ inverseLimitCarrier (A := A) :=
  symbolicBoundaryPrefixLimitCompHausIso (A := A)

theorem inverseLimitCarrierIso_hom_inv_id :
    (inverseLimitCarrierIso (A := A)).hom ≫
        (inverseLimitCarrierIso (A := A)).inv = 𝟙 _ :=
  (inverseLimitCarrierIso (A := A)).hom_inv_id

theorem inverseLimitCarrierIso_inv_hom_id :
    (inverseLimitCarrierIso (A := A)).inv ≫
        (inverseLimitCarrierIso (A := A)).hom = 𝟙 _ :=
  (inverseLimitCarrierIso (A := A)).inv_hom_id

/-! ## Finite holonomy confinement readout -/

theorem colimit_holonomy_confinement (σ t : ℝ)
    (h_unitary :
      (translatedMonodromyGenerator σ t).transpose =
        -(translatedMonodromyGenerator σ t)) :
    σ = 1 / 2 :=
  stokes_holonomy_forces_critical_line σ t h_unitary

end InfoGeometry.TraceFormula.PrimonHamiltonianColimit
