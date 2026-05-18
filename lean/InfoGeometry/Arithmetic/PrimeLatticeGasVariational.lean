import Mathlib
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.MaxEnt.Jaynes

/-!
# InfoGeometry.Arithmetic.PrimeLatticeGasVariational

Finite hard-core lattice gas supported on prime sites.

This file formalizes the proof-bearing finite statistical-mechanics layer behind
the Vericat-style prime lattice gas:

* lattice sites are `1, …, M`;
* only prime sites are allowed;
* each allowed site has hard-core occupation;
* the finite grand partition function is `(1 + z)^(# prime sites ≤ M)`.

The variational explicit-formula/RH-facing material is deliberately represented
only by witness sockets. This file does not prove RH, does not assert that a
variational extremum proves RH, and does not replace the Euler-product zeta
owner files.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeLatticeGasVariational

open scoped BigOperators
open InfoGeometry.MaxEnt

/-! ## 1. Finite prime-supported lattice sites -/

/--
The finite set of prime lattice sites in `1, …, M`.

This is a concrete finite set of natural numbers. The `< M + 1` encoding is
equivalent to `≤ M`, and gives a finite carrier immediately.
-/
def primeSiteFinset (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter Nat.Prime

/-- Prime lattice sites as a finite type. -/
abbrev PrimeSites (M : ℕ) : Type :=
  {n : ℕ // n ∈ primeSiteFinset M}

/-- The number of allowed prime sites up to the cutoff. -/
def primeSiteCount (M : ℕ) : ℕ :=
  (primeSiteFinset M).card

/-- A prime site has natural-number value at most `M`. -/
theorem PrimeSites.value_le_cutoff
    {M : ℕ}
    (p : PrimeSites M) :
    p.1 ≤ M := by
  have hp_range : p.1 ∈ Finset.range (M + 1) := (Finset.mem_filter.mp p.2).1
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_range)

/-- A prime site is prime. -/
theorem PrimeSites.value_prime
    {M : ℕ}
    (p : PrimeSites M) :
    Nat.Prime p.1 :=
  (Finset.mem_filter.mp p.2).2

/-- The finite type cardinality agrees with the concrete site count. -/
theorem fintype_card_PrimeSites (M : ℕ) :
    Fintype.card (PrimeSites M) = primeSiteCount M := by
  rw [primeSiteCount]
  exact Fintype.card_coe (primeSiteFinset M)

/-! ## 2. Hard-core configurations and grand partition -/

/-- A hard-core configuration is a finite subset of the allowed prime sites. -/
abbrev Configuration (M : ℕ) : Type :=
  Finset (PrimeSites M)

/-- Fugacity parameter. In physics notation, `z = exp(β μ)`. -/
structure Fugacity where
  /-- The fugacity weight per occupied prime site. -/
  z : ℝ

/--
Finite grand partition function of the prime-supported hard-core lattice gas.

Every allowed prime site is either empty or occupied once.
-/
def grandPartition (M : ℕ) (Z : Fugacity) : ℝ :=
  ∑ C : Configuration M, Z.z ^ C.card

/--
Closed finite grand partition function:

`Ξ(M,z) = (1 + z)^(number of prime sites ≤ M)`.
-/
def grandPartitionClosed (M : ℕ) (Z : Fugacity) : ℝ :=
  (1 + Z.z) ^ Fintype.card (PrimeSites M)

/-- Grand potential for the finite lattice gas: `Ω = -(1 / β) log Ξ`. -/
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

/-! ## 3. Variational explicit-formula witness sockets -/

/--
A witness-gated variational explicit-formula model for the prime-counting term.

This packages a supplied `π(M; σ)`-style approximation and grand-potential
approximation. It is not a proof of RH.
-/
structure PrimeCountingVariationalModel where
  /-- Lattice cutoff. -/
  M : ℕ
  /-- Selected real part / variational parameter. -/
  sigma : ℝ
  /-- Supplied prime-counting approximation. -/
  piApprox : ℝ
  /-- Supplied approximate grand potential. -/
  grandPotentialApprox : ℝ
  /-- Supplied explicit-formula law. -/
  explicitFormulaLaw : Prop
  /-- Certificate for the supplied explicit-formula law. -/
  explicitFormulaCertificate : explicitFormulaLaw
  /-- Supplied variational extremum condition. -/
  extremumCondition : Prop
  /-- Certificate for the supplied extremum condition. -/
  extremumCertificate : extremumCondition
  /-- Guardrail: this packet is not an RH proof. -/
  noRHClaimWitness : Type*

namespace PrimeCountingVariationalModel

/-- Re-export the supplied explicit-formula law. -/
theorem explicitFormula_valid
    (V : PrimeCountingVariationalModel) :
    V.explicitFormulaLaw :=
  V.explicitFormulaCertificate

/-- Re-export the supplied extremum condition. -/
theorem extremum_valid
    (V : PrimeCountingVariationalModel) :
    V.extremumCondition :=
  V.extremumCertificate

end PrimeCountingVariationalModel

/--
Vericat-style critical-line gate.

If a supplied variational model selects `1 / 2`, this structure records that
fact. It is a theorem about the supplied model data, not a theorem about zeta
zeros.
-/
structure VariationalCriticalLineGate where
  /-- Selected variational parameter. -/
  selectedSigma : ℝ
  /-- Supplied certificate that the selected parameter is `1 / 2`. -/
  selectedSigma_eq_half : selectedSigma = 1 / 2
  /-- Guardrail: this gate is not an RH proof. -/
  noRHClaimWitness : Type*

/-- Re-export of the supplied critical-line selection certificate. -/
theorem selectedSigma_eq_half
    (G : VariationalCriticalLineGate) :
    G.selectedSigma = 1 / 2 :=
  G.selectedSigma_eq_half

/--
Optional packet combining the finite exact lattice gas with a supplied
variational model. The finite theorem remains independent of the heuristic gate.
-/
structure PrimeLatticeGasVariationalPacket where
  /-- Finite cutoff. -/
  M : ℕ
  /-- Fugacity data. -/
  fugacity : Fugacity
  /-- Optional supplied explicit-formula/variational model. -/
  variationalModel : Option PrimeCountingVariationalModel
  /-- Optional supplied critical-line selection gate. -/
  criticalLineGate : Option VariationalCriticalLineGate
  /-- Guardrail: no Euler-product zeta bridge is claimed here. -/
  notEulerProductBridgeWitness : Type*

/-- Owner target for the exact finite hard-core prime lattice gas identity. -/
@[owner_target_tag]
def PrimeLatticeGasFiniteOwnerTarget : Prop :=
  ∀ (M : ℕ) (Z : Fugacity),
    grandPartition M Z = (1 + Z.z) ^ primeSiteCount M

/-- The finite owner target is exactly the closed-form grand partition theorem. -/
theorem primeLatticeGasFiniteOwnerTarget :
    PrimeLatticeGasFiniteOwnerTarget := by
  intro M Z
  exact grandPartition_eq_one_add_pow_primeSiteCount M Z

/--
Finite entropy maximizer on the prime lattice configuration space.

This is the honest MaxEnt statement available in the repository: the zero-feature
Gibbs law on the finite configuration carrier maximizes Shannon entropy on the
Jaynes feasible set.  It does not claim anything about zeta zeros.
-/
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
