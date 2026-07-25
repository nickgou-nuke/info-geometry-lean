import Mathlib.Tactic
import InfoGeometry.MaxEnt.Jaynes

/-!
# InfoGeometry.Arithmetic.PrimeLatticeGasVariational

\[
\mathcal C_M := \{\text{finite subsets of prime sites }\le M\},
\qquad
\Xi(M,z)=\sum_{C\in\mathcal C_M} z^{|C|}.
\]

\[
\Xi(M,z) = (1+z)^{\#\{p\le M : p\ \mathrm{prime}\}}.
\]
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeLatticeGasVariational

open scoped BigOperators
open InfoGeometry.MaxEnt

/-! ## 1. Finite prime-supported lattice sites -/

/-- `\{p\in\mathbb N : p\le M\wedge p\ \mathrm{prime}\}`. -/
def primeSiteFinset (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter Nat.Prime

/-- Prime lattice sites as a finite type. -/
abbrev PrimeSites (M : ℕ) : Type :=
  {n : ℕ // n ∈ primeSiteFinset M}

/-- `\#\{p\le M : p\ \mathrm{prime}\}`. -/
def primeSiteCount (M : ℕ) : ℕ :=
  (primeSiteFinset M).card

/-- `p\in\mathrm{PrimeSites}(M) \to p\le M`. -/
theorem PrimeSites.value_le_cutoff
    {M : ℕ}
    (p : PrimeSites M) :
    p.1 ≤ M := by
  have hp_range : p.1 ∈ Finset.range (M + 1) := (Finset.mem_filter.mp p.2).1
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_range)

/-- `p\in\mathrm{PrimeSites}(M) \to p\ \mathrm{prime}`. -/
theorem PrimeSites.value_prime
    {M : ℕ}
    (p : PrimeSites M) :
    Nat.Prime p.1 :=
  (Finset.mem_filter.mp p.2).2

/-- `\#\mathrm{PrimeSites}(M) = \mathrm{primeSiteCount}(M)`. -/
theorem fintype_card_PrimeSites (M : ℕ) :
    Fintype.card (PrimeSites M) = primeSiteCount M := by
  rw [primeSiteCount]
  exact Fintype.card_coe (primeSiteFinset M)

/-! ## 2. Hard-core configurations and grand partition -/

/-- `\mathcal C_M := \mathrm{Finset}(\mathrm{PrimeSites}(M))`. -/
abbrev Configuration (M : ℕ) : Type :=
  Finset (PrimeSites M)

/-- `z := e^{\beta\mu}`. -/
structure Fugacity where
  /-- Fugacity weight `z`. -/
  z : ℝ

/-- `\Xi(M,z)=\sum_{C\in\mathcal C_M} z^{|C|}`. -/
def grandPartition (M : ℕ) (Z : Fugacity) : ℝ :=
  ∑ C : Configuration M, Z.z ^ C.card

/-- `\Xi(M,z)=(1+z)^{\#\mathrm{PrimeSites}(M)}`. -/
def grandPartitionClosed (M : ℕ) (Z : Fugacity) : ℝ :=
  (1 + Z.z) ^ Fintype.card (PrimeSites M)

/-- `\Omega = -(1/\beta)\log\Xi`. -/
def grandPotential (β : ℝ) (M : ℕ) (Z : Fugacity) : ℝ :=
  - (1 / β) * Real.log (grandPartitionClosed M Z)

/--
Each finite subset contributes `z^card`, so summing over all hard-core
configurations gives `(1 + z)^N`.
-/
theorem grandPartition_eq_closed
    (M : ℕ)
    (Z : Fugacity) :
    grandPartition M Z = grandPartitionClosed M Z := by
  classical
  unfold grandPartition grandPartitionClosed
  have h :=
    (Finset.prod_one_add
      (s := (Finset.univ : Finset (PrimeSites M)))
      (f := fun _ : PrimeSites M => Z.z)).symm
  simpa [Finset.card_univ] using h

/-- The same closed form expressed with the concrete prime-site count. -/
theorem grandPartition_eq_one_add_pow_primeSiteCount
    (M : ℕ)
    (Z : Fugacity) :
    grandPartition M Z = (1 + Z.z) ^ primeSiteCount M := by
  rw [grandPartition_eq_closed, grandPartitionClosed, fintype_card_PrimeSites]

/-- `H(q) \le H(\mathrm{gibbs})` on the zero-feature Jaynes feasible set. -/
theorem primeLatticeGas_zeroFeature_entropy_maximizer
    (M : ℕ) :
    let n := Fintype.card (Configuration M)
    ∀ q : Fin n → ℝ,
      q ∈ MaxEntConstraint (n := n) (fun _ : Fin n => (0 : ℝ)) 0 →
        ShannonEntropy q ≤
          ShannonEntropy (gibbs (fun _ : Fin n => (0 : ℝ)) 0) := by
  classical
  dsimp
  intro q hq
  let n := Fintype.card (Configuration M)
  have hpos : 0 < n := by
    dsimp [n]
    exact Fintype.card_pos_iff.mpr (⟨Finset.empty⟩ : Nonempty (Configuration M))
  letI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  have hp :
      gibbs (fun _ : Fin n => (0 : ℝ)) 0 ∈
        MaxEntConstraint (n := n) (fun _ : Fin n => (0 : ℝ)) 0 := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro i
        exact gibbs_nonneg (f := fun _ : Fin n => (0 : ℝ)) (lam := 0) i
      · simpa using
          (gibbs_sum_one (f := fun _ : Fin n => (0 : ℝ)) (lam := 0))
    · simp
  simpa [ShannonEntropy] using
    (gibbs_maximizes_shannon_under_moment
      (n := n)
      (f := fun _ : Fin n => (0 : ℝ))
      (E := 0)
      (lam := 0)
      (p := gibbs (fun _ : Fin n => (0 : ℝ)) 0)
      hp
      (by intro i; rfl)
      q hq)

end InfoGeometry.Arithmetic.PrimeLatticeGasVariational
