
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open scoped BigOperators


universe u v

namespace JaynesInfoStatMech
open scoped BigOperators
variable {Ω : Type u} [Fintype Ω]

/-!
## 1. Finite probability distributions and Shannon entropy
(Jaynes 1957; Shannon entropy as the unique measure of “uncertainty”.)
-/

/-- A probability distribution on a finite sample space `Ω`, valued in `ℝ`. -/
structure ProbDist (Ω : Type u) [Fintype Ω] where
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_one : (∑ ω, p ω) = 1

/-- An (ℝ-valued) observable on `Ω`. -/
abbrev Observable (Ω : Type u) := Ω → ℝ

/-- Expectation `E_P[f] = ∑ ω p(ω) f(ω)` on a finite space. -/
noncomputable def expectedValue (P : ProbDist Ω) (f : Observable Ω) : ℝ :=
  ∑ ω, P.p ω * f ω

/--
Shannon entropy (Jaynes uses `K` as a constant; information-theory often takes `K = 1`):
`H_K(P) = -K * ∑ ω p(ω) log(p(ω))`.
-/
noncomputable def shannonEntropy (P : ProbDist Ω) (K : ℝ := 1) : ℝ :=
  -K * ∑ ω, P.p ω * Real.log (P.p ω)
/-!
## 2. MaxEnt constraints (index by a finite type, not a `List`)
This is the canonical Mathlib style: use an index type `ι` with `[Fintype ι]`.
-/

/-- A family of expectation constraints: observables `f r` with target values `d r`. -/
structure ConstraintFamily (ι : Type v) (Ω : Type u) where
  f : ι → Observable Ω
  d : ι → ℝ

variable {ι : Type v} [Fintype ι]

/-- `P` is feasible if it satisfies all constraints `E_P[f r] = d r`. -/
def IsFeasible (P : ProbDist Ω) (C : ConstraintFamily ι Ω) : Prop :=
  ∀ r, expectedValue P (C.f r) = C.d r

/-!
## 3. The exponential family (partition function, MaxEnt distribution)
Jaynes’ general solution: `p(ω) ∝ exp(-∑ r lam_r f_r(ω))`.
-/





section MaxEnt
variable [Nonempty Ω]

/-- Unnormalized weight `w(ω;lam) = exp(-∑ r lam_r f_r(ω))`. -/
noncomputable def weight (C : ConstraintFamily ι Ω) (lam : ι → ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(∑ r, (lam r) * (C.f r ω)))

/-- Partition function `Z(lam) = ∑ ω exp(-∑ r lam_r f_r(ω))`. -/
noncomputable def partitionFunction (C : ConstraintFamily ι Ω) (lam : ι → ℝ) : ℝ :=
  ∑ ω, weight C lam ω

/-- `Z(lam) > 0` on a nonempty finite space since it is a sum of positive exponentials. -/
theorem partitionFunction_pos (C : ConstraintFamily ι Ω) (lam : ι → ℝ) :
    0 < partitionFunction C lam := by
  classical
  simpa [partitionFunction, weight] using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Ω))
      (f := fun ω => Real.exp (-(∑ r, lam r * C.f r ω)))
      (by intro ω _; exact Real.exp_pos _) Finset.univ_nonempty)

/-- log-partition `log Z(lam)` --/
noncomputable def logZ (C : ConstraintFamily ι Ω) (lam : ι → ℝ) : ℝ :=
  Real.log (partitionFunction C lam)

/-- MaxEnt / Gibbs distribution: p(ω) = w(ω)/Z. -/
noncomputable def maxEntDist (C : ConstraintFamily ι Ω) (lam : ι → ℝ) : ProbDist Ω := by
  classical
  have Z_pos : 0 < partitionFunction C lam := partitionFunction_pos (C := C) (lam := lam)
  have Z_ne : partitionFunction C lam ≠ 0 := ne_of_gt Z_pos
  exact {
    p := fun ω => weight C lam ω / partitionFunction C lam,
    nonneg := fun ω =>
      div_nonneg
        (le_of_lt (Real.exp_pos (-(∑ r, lam r * C.f r ω))))
        (le_of_lt Z_pos),
    sum_one := by
      calc
        (∑ ω, weight C lam ω / partitionFunction C lam)
          = (∑ ω, weight C lam ω) / partitionFunction C lam := by
              symm
              simpa using
                (Finset.sum_div
                  (s := (Finset.univ : Finset Ω))
                  (f := fun ω => weight C lam ω)
                  (a := partitionFunction C lam))
        _ = partitionFunction C lam / partitionFunction C lam := rfl
        _ = 1 := div_self Z_ne
  }

end MaxEnt
section StatMech
variable [Nonempty Ω]

/-- One-observable constraint family indexed by `Unit`. -/
def energyFamily (E : Observable Ω) (U : ℝ := 0) : ConstraintFamily Unit Ω :=
  { f := fun _ => E, d := fun _ => U }

/-- In statistical mechanics, `β = 1/(kT)` (parameters `k,T`). -/
noncomputable def beta (k T : ℝ) : ℝ :=
  1 / (k * T)

/-- Physical regime where `β = 1/(kT)` is meaningful. -/
def ThermodynamicRegime (k T : ℝ) : Prop :=
  k * T ≠ 0

/-- `β` specialized to the physical regime (`kT ≠ 0`). -/
noncomputable def betaInRegime (k T : ℝ) (_h : ThermodynamicRegime k T) : ℝ :=
  beta k T

/-- Boltzmann distribution: MaxEnt with a single observable (energy) and multiplier `β`. -/
noncomputable def boltzmannDist (E : Observable Ω) (b : ℝ) : ProbDist Ω :=
  maxEntDist (energyFamily E) (fun _ => b)

/-- Helmholtz free energy `F = -k T * log Z(β)`. -/
noncomputable def helmholtzFreeEnergy (E : Observable Ω) (k T : ℝ) : ℝ :=
  -k * T * Real.log (partitionFunction (energyFamily E) (fun _ => beta k T))

end StatMech

/-!
# Finite-Dimensional Thermal Model (Diagonal Matrix / Commuting Subalgebra)

Finite matrix-valued thermal layer over diagonal observables:
- diagonal Hamiltonian `H`
- Gibbs density `ρ_β = diag(p_β)`
- explicit modular conjugation on entries
- Gibbs functional on matrices
- KMS-like identity on the diagonal commuting subalgebra
-/

namespace ThermalDiagonal

section Model

variable {n : ℕ} [Nonempty (Fin n)]

/-- Real finite matrices on `Fin n`. -/
abbrev FinMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Diagonal observables (identified with diagonal matrices). -/
abbrev DiagObservable (n : ℕ) := Fin n → ℝ

/-- Diagonal matrix associated to a diagonal observable. -/
def diagMatrix (a : DiagObservable n) : FinMat n :=
  Matrix.diagonal a

/-- Matrix diagonal mass as sum of diagonal entries. -/
noncomputable def diagonalMass (A : FinMat n) : ℝ :=
  ∑ i, A i i

/-- Hamiltonian matrix in diagonal form. -/
def hamiltonianMatrix (H : DiagObservable n) : FinMat n :=
  diagMatrix H

/-- Gibbs weight `wᵢ = exp(-β Hᵢ)`. -/
noncomputable def gibbsWeight (H : DiagObservable n) (β : ℝ) (i : Fin n) : ℝ :=
  Real.exp (-β * H i)

/-- Partition function `Z(β) = ∑ᵢ exp(-β Hᵢ)`. -/
noncomputable def partitionFunction (H : DiagObservable n) (β : ℝ) : ℝ :=
  ∑ i, gibbsWeight H β i

/-- The diagonal thermal partition function is strictly positive. -/
theorem partitionFunction_pos (H : DiagObservable n) (β : ℝ) :
    0 < partitionFunction H β := by
  classical
  unfold partitionFunction gibbsWeight
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => Real.exp (-β * H i))
      (by
        intro i hi
        exact Real.exp_pos _)
      Finset.univ_nonempty)

/-- The diagonal thermal partition function is nonzero. -/
lemma partitionFunction_ne_zero (H : DiagObservable n) (β : ℝ) :
    partitionFunction H β ≠ 0 :=
  (partitionFunction_pos H β).ne'

/-- Log-partition `log Z(β)`. -/
noncomputable def logPartition (H : DiagObservable n) (β : ℝ) : ℝ :=
  Real.log (partitionFunction H β)

/-- Gibbs probabilities `pᵢ = exp(-β Hᵢ) / Z(β)`. -/
noncomputable def gibbsProb (H : DiagObservable n) (β : ℝ) (i : Fin n) : ℝ :=
  gibbsWeight H β i / partitionFunction H β

/-- Diagonal Gibbs probabilities are strictly positive. -/
lemma gibbsProb_pos (H : DiagObservable n) (β : ℝ) (i : Fin n) :
    0 < gibbsProb H β i := by
  unfold gibbsProb gibbsWeight
  exact div_pos (Real.exp_pos _) (partitionFunction_pos H β)

/-- Diagonal Gibbs probabilities are nonnegative. -/
lemma gibbsProb_nonneg (H : DiagObservable n) (β : ℝ) (i : Fin n) :
    0 ≤ gibbsProb H β i :=
  (gibbsProb_pos H β i).le

/-- Diagonal Gibbs probabilities normalize to one. -/
lemma gibbsProb_sum_one (H : DiagObservable n) (β : ℝ) :
    (∑ i, gibbsProb H β i) = 1 := by
  unfold gibbsProb
  have hZne : partitionFunction H β ≠ 0 := partitionFunction_ne_zero H β
  calc
    (∑ i, gibbsWeight H β i / partitionFunction H β)
        = (∑ i, gibbsWeight H β i) / partitionFunction H β := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun i => gibbsWeight H β i)
                (a := partitionFunction H β))
    _ = partitionFunction H β / partitionFunction H β := by
          rfl
    _ = 1 := div_self hZne

lemma gibbsProb_le_one (H : DiagObservable n) (β : ℝ) (i : Fin n) :
    gibbsProb H β i ≤ 1 := by
  have hnonneg : ∀ j : Fin n, 0 ≤ gibbsProb H β j := fun j => gibbsProb_nonneg H β j
  have hsum : ∑ j : Fin n, gibbsProb H β j = 1 := gibbsProb_sum_one H β
  have hi_le_sum : gibbsProb H β i ≤ ∑ j : Fin n, gibbsProb H β j := by
    exact Finset.single_le_sum (fun j _hj => hnonneg j) (Finset.mem_univ i)
  simpa [hsum] using hi_le_sum

/-- Gibbs density matrix `ρ_β = diag(p_β)`. -/
noncomputable def densityMatrix (H : DiagObservable n) (β : ℝ) : FinMat n :=
  diagMatrix (gibbsProb H β)

omit [Nonempty (Fin n)] in
@[simp] lemma densityMatrix_diag (H : DiagObservable n) (β : ℝ) (i : Fin n) :
    densityMatrix H β i i = gibbsProb H β i := by
  simp [densityMatrix, diagMatrix]

lemma densityMatrix_diag_le_one (H : DiagObservable n) (β : ℝ) (i : Fin n) :
    densityMatrix H β i i ≤ 1 := by
  rw [densityMatrix_diag]
  exact gibbsProb_le_one H β i

omit [Nonempty (Fin n)] in
@[simp] lemma densityMatrix_offdiag
    (H : DiagObservable n) (β : ℝ) {i j : Fin n} (hij : i ≠ j) :
    densityMatrix H β i j = 0 := by
  simp [densityMatrix, diagMatrix, hij]

/-- The Gibbs density matrix has diagonal mass `1`. -/
lemma densityMatrix_diagonalMass_one (H : DiagObservable n) (β : ℝ) :
    diagonalMass (densityMatrix H β) = 1 := by
  unfold diagonalMass
  simpa using gibbsProb_sum_one H β

/-- Pointwise log-density formula `log pᵢ = -β Hᵢ - log Z`. -/
lemma log_gibbsProb (H : DiagObservable n) (β : ℝ) (i : Fin n) :
    Real.log (gibbsProb H β i)
      = -β * H i - logPartition H β := by
  unfold gibbsProb logPartition gibbsWeight
  have hZpos : 0 < partitionFunction H β := partitionFunction_pos H β
  have hnum : Real.exp (-β * H i) ≠ 0 := (Real.exp_pos _).ne'
  have hden : partitionFunction H β ≠ 0 := hZpos.ne'
  rw [Real.log_div hnum hden]
  simp

/-- Log-density matrix (entrywise log on the diagonal). -/
noncomputable def logDensityMatrix (H : DiagObservable n) (β : ℝ) : FinMat n :=
  diagMatrix (fun i => Real.log (gibbsProb H β i))

omit [Nonempty (Fin n)] in
@[simp] lemma logDensityMatrix_diag
    (H : DiagObservable n) (β : ℝ) (i : Fin n) :
    logDensityMatrix H β i i = Real.log (gibbsProb H β i) := by
  simp [logDensityMatrix, diagMatrix]

/-- Affine Hamiltonian form of the log-density on diagonal entries. -/
lemma logDensityMatrix_diag_affine
    (H : DiagObservable n) (β : ℝ) (i : Fin n) :
    logDensityMatrix H β i i = -β * H i - logPartition H β := by
  simp [logDensityMatrix_diag, log_gibbsProb]

/-- Gibbs state functional on matrices: `ω_β(A) = ∑ᵢ pᵢ Aᵢᵢ`. -/
noncomputable def gibbsStateMatrix
    (H : DiagObservable n) (β : ℝ) (A : FinMat n) : ℝ :=
  ∑ i, gibbsProb H β i * A i i

/-- Gibbs state on diagonal observables. -/
noncomputable def gibbsStateDiag
    (H : DiagObservable n) (β : ℝ) (a : DiagObservable n) : ℝ :=
  ∑ i, gibbsProb H β i * a i

omit [Nonempty (Fin n)] in
/-- Matrix and diagonal Gibbs states agree on diagonal observables. -/
lemma gibbsStateMatrix_on_diag
    (H : DiagObservable n) (β : ℝ) (a : DiagObservable n) :
    gibbsStateMatrix H β (diagMatrix a) = gibbsStateDiag H β a := by
  unfold gibbsStateMatrix gibbsStateDiag diagMatrix
  simp

/-- Internal energy `U = E_β[H]`. -/
noncomputable def internalEnergy (H : DiagObservable n) (β : ℝ) : ℝ :=
  gibbsStateDiag H β H

/-- Shannon entropy of the Gibbs distribution in the diagonal model. -/
noncomputable def gibbsEntropy (H : DiagObservable n) (β : ℝ) : ℝ :=
  -∑ i, gibbsProb H β i * Real.log (gibbsProb H β i)

/-- Gibbs entropy identity: `S = β U + log Z`. -/
lemma gibbsEntropy_eq_beta_internal_plus_logPartition
    (H : DiagObservable n) (β : ℝ) :
    gibbsEntropy H β = β * internalEnergy H β + logPartition H β := by
  have hrewrite :
      ∑ i, gibbsProb H β i * Real.log (gibbsProb H β i)
        = ∑ i, gibbsProb H β i * (-β * H i - logPartition H β) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [log_gibbsProb]
  have hE :
      ∑ i, gibbsProb H β i * (-β * H i)
        = (-β) * internalEnergy H β := by
    unfold internalEnergy gibbsStateDiag
    calc
      ∑ i, gibbsProb H β i * (-β * H i)
          = ∑ i, (-β) * (gibbsProb H β i * H i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (-β) * ∑ i, gibbsProb H β i * H i := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Fin n)))
                (a := -β)
                (f := fun i => gibbsProb H β i * H i)).symm
  have hZ :
      ∑ i, gibbsProb H β i * (-logPartition H β)
        = (-logPartition H β) * (∑ i, gibbsProb H β i) := by
    calc
      ∑ i, gibbsProb H β i * (-logPartition H β)
          = ∑ i, (-logPartition H β) * gibbsProb H β i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (-logPartition H β) * (∑ i, gibbsProb H β i) := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Fin n)))
                (a := -logPartition H β)
                (f := fun i => gibbsProb H β i)).symm
  calc
    gibbsEntropy H β
        = -∑ i, gibbsProb H β i * Real.log (gibbsProb H β i) := by
            rfl
    _ = -∑ i, gibbsProb H β i * (-β * H i - logPartition H β) := by
          rw [hrewrite]
    _ = -(
          ∑ i, (gibbsProb H β i * (-β * H i) + gibbsProb H β i * (-logPartition H β))
        ) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = -(
          (∑ i, gibbsProb H β i * (-β * H i))
            + (∑ i, gibbsProb H β i * (-logPartition H β))
        ) := by
          rw [Finset.sum_add_distrib]
    _ = -(((-β) * internalEnergy H β)
            + ((-logPartition H β) * (∑ i, gibbsProb H β i))) := by
          rw [hE, hZ]
    _ = β * internalEnergy H β + logPartition H β := by
          rw [gibbsProb_sum_one]
          ring

/-- Real-time modular conjugation in diagonal basis:
`(σ_t(A))ᵢⱼ = exp(t (Hⱼ - Hᵢ)) Aᵢⱼ`. -/
noncomputable def modularConj
    (H : DiagObservable n) (t : ℝ) (A : FinMat n) : FinMat n :=
  fun i j => Real.exp (t * (H j - H i)) * A i j

omit [Nonempty (Fin n)] in
/-- On diagonal observables, modular conjugation fixes diagonal entries. -/
lemma modularConj_diag_entry
    (H : DiagObservable n) (t : ℝ) (a : DiagObservable n) (i : Fin n) :
    modularConj H t (diagMatrix a) i i = a i := by
  simp [modularConj, diagMatrix]

/-- Diagonal observable product (commuting subalgebra product). -/
def diagMul (a b : DiagObservable n) : DiagObservable n :=
  fun i => a i * b i

/-- Diagonal modular shift extracted from matrix modular conjugation. -/
noncomputable def modularShiftDiag
    (H : DiagObservable n) (t : ℝ) (a : DiagObservable n) : DiagObservable n :=
  fun i => modularConj H t (diagMatrix a) i i

omit [Nonempty (Fin n)] in
/-- The diagonal modular shift acts trivially on diagonal observables. -/
lemma modularShiftDiag_eq
    (H : DiagObservable n) (t : ℝ) (a : DiagObservable n) :
    modularShiftDiag H t a = a := by
  funext i
  exact modularConj_diag_entry H t a i

omit [Nonempty (Fin n)] in
/-- KMS-like cyclicity on the diagonal (commuting) subalgebra. -/
theorem gibbsState_kmsLike_diag
    (H : DiagObservable n) (β t : ℝ) (a b : DiagObservable n) :
    gibbsStateDiag H β (diagMul a (modularShiftDiag H t b))
      = gibbsStateDiag H β (diagMul b a) := by
  have hshift : modularShiftDiag H t b = b := modularShiftDiag_eq H t b
  unfold gibbsStateDiag diagMul
  rw [hshift]
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

/-- Helmholtz free energy in the finite diagonal model (`β ≠ 0` regime). -/
noncomputable def helmholtzFreeEnergy (H : DiagObservable n) (β : ℝ) : ℝ :=
  -(1 / β) * logPartition H β

end Model

end ThermalDiagonal

end JaynesInfoStatMech
