import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic

/-!
# arXiv:2309.01382 finite symmetry packet

Paper: Pushpa Kalaunia and Prasanta K. Panigrahi,
*A symmetry perspective of the Riemann zeros*, arXiv:2309.01382v1.

This module formalizes the finite algebraic backbone of the paper:

* Witten-index classification by zero-energy boson/fermion counts;
* the paper's scalar `PT` equality
  `ζ(σ+iω)ζ(1-σ-iω)=ζ(σ-iω)ζ(1-σ+iω)` as a predicate over an abstract zeta
  readout;
* the `2 × 2` supersymmetric block Hamiltonian surface;
* the spin-half `su(2)` matrix relations for `J₊`, `J₋`, and `J₀`;
* the spin-half Casimir value `3/4`.

The module records no global zeta analysis, no completeness result for function
spaces, and no operator spectrum theorem for zeta zeros.
-/

namespace InfoGeometry.Arithmetic.Arxiv230901382RiemannZerosSymmetry

open Matrix

/-! ## Witten index classification -/

/-- Integer Witten index from zero-energy bosonic and fermionic counts. -/
def wittenIndex (nBosonZero nFermionZero : ℤ) : ℤ :=
  nBosonZero - nFermionZero

/-- Paper-style Witten classification reduced to finite counts. -/
inductive SusyStatus where
  | unbroken
  | broken
  deriving DecidableEq, Repr

/-- Witten's three finite count cases as a status classifier. -/
def wittenStatus (nBosonZero nFermionZero : ℤ) : SusyStatus :=
  if wittenIndex nBosonZero nFermionZero ≠ 0 then .unbroken
  else if nBosonZero = 0 ∧ nFermionZero = 0 then .broken
  else .unbroken

/-- Nonzero Witten index gives the unbroken branch. -/
theorem wittenStatus_unbroken_of_index_ne_zero
    {nB nF : ℤ} (h : wittenIndex nB nF ≠ 0) :
    wittenStatus nB nF = .unbroken := by
  simp [wittenStatus, h]

/-- If both zero-energy counts vanish, the finite classifier is broken. -/
theorem wittenStatus_broken_zero_zero :
    wittenStatus 0 0 = .broken := by
  rfl

/-- Equal nonzero counts give the third Witten unbroken branch. -/
theorem wittenStatus_unbroken_equal_nonzero :
    wittenStatus 1 1 = .unbroken := by
  rfl

/-- The paper's non-trivial-zero count pattern has vanishing index but unbroken status. -/
theorem nontrivial_zero_count_pattern :
    wittenIndex 1 1 = 0 ∧ wittenStatus 1 1 = .unbroken := by
  exact ⟨rfl, rfl⟩

/-! ## Abstract zeta/PT scalar condition -/

/-- Abstract complex coordinate `s = σ + iω` represented by its two real parts. -/
structure ZetaCoordinate where
  sigma : ℝ
  omega : ℝ

/-- Reflection `s ↦ 1-s` in `(σ,ω)` coordinates. -/
def oneMinus (s : ZetaCoordinate) : ZetaCoordinate where
  sigma := 1 - s.sigma
  omega := -s.omega

/-- Conjugation `σ+iω ↦ σ-iω`. -/
def conjCoord (s : ZetaCoordinate) : ZetaCoordinate where
  sigma := s.sigma
  omega := -s.omega

theorem oneMinus_involutive (s : ZetaCoordinate) :
    oneMinus (oneMinus s) = s := by
  cases s
  simp [oneMinus]

theorem conjCoord_involutive (s : ZetaCoordinate) :
    conjCoord (conjCoord s) = s := by
  cases s
  simp [conjCoord]

/-- Critical-line predicate `σ=1/2`. -/
def OnCriticalLine (s : ZetaCoordinate) : Prop :=
  s.sigma = (1 / 2 : ℝ)

theorem oneMinus_eq_conj_iff_onCriticalLine (s : ZetaCoordinate) :
    oneMinus s = conjCoord s ↔ OnCriticalLine s := by
  cases s
  simp [oneMinus, conjCoord, OnCriticalLine]
  constructor <;> intro h <;> linarith

/-- The paper's finite scalar `PT` equality for an abstract zeta readout. -/
def PTScalarCondition (zeta : ZetaCoordinate → ℂ) (s : ZetaCoordinate) : Prop :=
  zeta s * zeta (oneMinus s) = zeta (conjCoord s) * zeta (oneMinus (conjCoord s))

/-- On the critical line, the `1-s` coordinate equals the conjugate coordinate. -/
theorem oneMinus_eq_conj_on_critical {s : ZetaCoordinate} (h : OnCriticalLine s) :
    oneMinus s = conjCoord s := by
  cases s
  simp [OnCriticalLine, oneMinus, conjCoord] at h ⊢
  linarith

/-- If `1-s = conj(s)`, the scalar PT condition is automatic by commutativity. -/
theorem PTScalarCondition_of_oneMinus_eq_conj
    (zeta : ZetaCoordinate → ℂ) {s : ZetaCoordinate}
    (h : oneMinus s = conjCoord s) :
    PTScalarCondition zeta s := by
  cases s with
  | mk sigma omega =>
      simp [oneMinus, conjCoord] at h
      have hcrit : sigma = (1 / 2 : ℝ) := by linarith
      subst sigma
      simp [PTScalarCondition, oneMinus, conjCoord]
      have hhalf : (1 - (2 : ℝ)⁻¹) = (2 : ℝ)⁻¹ := by norm_num
      rw [hhalf]
      rw [mul_comm]

/-- Critical-line coordinates satisfy the paper's scalar PT equality. -/
theorem PTScalarCondition_on_critical
    (zeta : ZetaCoordinate → ℂ) {s : ZetaCoordinate} (h : OnCriticalLine s) :
    PTScalarCondition zeta s :=
  PTScalarCondition_of_oneMinus_eq_conj zeta (oneMinus_eq_conj_on_critical h)

/-- Real-axis coordinates also satisfy the paper's scalar PT equality. -/
theorem PTScalarCondition_on_real_axis
    (zeta : ZetaCoordinate → ℂ) {s : ZetaCoordinate} (hω : s.omega = 0) :
    PTScalarCondition zeta s := by
  unfold PTScalarCondition oneMinus conjCoord
  cases s
  simp at hω ⊢
  rw [hω]
  simp

/-! ## Supersymmetric block-Hamiltonian bookkeeping -/

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Block Hamiltonian `diag(E₋,E₊)` for the two SUSY partner sectors. -/
def susyHamiltonianBlock (Eminus Eplus : ℂ) : Mat2C :=
  !![Eminus, 0;
     0, Eplus]

/-- If both partner energies agree, the block Hamiltonian is scalar. -/
theorem susyHamiltonianBlock_eq_scalar_of_equal (E : ℂ) :
    susyHamiltonianBlock E E = E • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [susyHamiltonianBlock]

/-- If the common zeta-product energy is zero, the finite block Hamiltonian is zero. -/
theorem susyHamiltonianBlock_zero_of_energy_zero {E : ℂ} (hE : E = 0) :
    susyHamiltonianBlock E E = 0 := by
  rw [hE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [susyHamiltonianBlock]

/-! ## Spin-half `su(2)` matrix relations -/

abbrev Mat2Q := Matrix (Fin 2) (Fin 2) ℚ

/-- Spin-half raising matrix. -/
def Jplus : Mat2Q :=
  !![0, 1;
     0, 0]

/-- Spin-half lowering matrix. -/
def Jminus : Mat2Q :=
  !![0, 0;
     1, 0]

/-- Spin-half diagonal generator. -/
def J0 : Mat2Q :=
  !![(1 / 2 : ℚ), 0;
     0, -(1 / 2 : ℚ)]

/-- Matrix commutator. -/
def commQ (A B : Mat2Q) : Mat2Q :=
  A * B - B * A

/-- First `su(2)` relation `[J₊,J₋]=2J₀`. -/
theorem comm_Jplus_Jminus :
    commQ Jplus Jminus = (2 : ℚ) • J0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [commQ, Jplus, Jminus, J0, Matrix.mul_apply, Fin.sum_univ_two]

/-- Second `su(2)` relation `[J₀,J₊]=J₊`. -/
theorem comm_J0_Jplus :
    commQ J0 Jplus = Jplus := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [commQ, Jplus, J0, Matrix.mul_apply, Fin.sum_univ_two]

/-- Third `su(2)` relation `[J₀,J₋]=-J₋`. -/
theorem comm_J0_Jminus :
    commQ J0 Jminus = -Jminus := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [commQ, Jminus, J0, Matrix.mul_apply, Fin.sum_univ_two]

/-- Spin-half Casimir in raising/lowering coordinates. -/
def spinHalfCasimir : Mat2Q :=
  J0 * J0 + (1 / 2 : ℚ) • (Jplus * Jminus + Jminus * Jplus)

/-- The spin-half Casimir has value `3/4`. -/
theorem spinHalfCasimir_eq_three_quarters :
    spinHalfCasimir = (3 / 4 : ℚ) • (1 : Mat2Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinHalfCasimir, Jplus, Jminus, J0, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Paper-level two-state actions and SUSY operators -/

/-- Spin-up basis state `|1/2,1/2⟩`. -/
def ketUp : Fin 2 → ℚ := ![1, 0]

/-- Spin-down basis state `|1/2,-1/2⟩`. -/
def ketDown : Fin 2 → ℚ := ![0, 1]

/-- Raising kills spin-up. -/
theorem Jplus_ketUp : Jplus.mulVec ketUp = 0 := by
  ext i
  fin_cases i <;> norm_num [Jplus, Matrix.mulVec, Fin.sum_univ_two, ketUp]

/-- Raising maps spin-down to spin-up. -/
theorem Jplus_ketDown : Jplus.mulVec ketDown = ketUp := by
  ext i
  fin_cases i <;> norm_num [Jplus, Matrix.mulVec, Fin.sum_univ_two, ketDown, ketUp]

/-- Lowering maps spin-up to spin-down. -/
theorem Jminus_ketUp : Jminus.mulVec ketUp = ketDown := by
  ext i
  fin_cases i <;> norm_num [Jminus, Matrix.mulVec, Fin.sum_univ_two, ketUp, ketDown]

/-- Lowering kills spin-down. -/
theorem Jminus_ketDown : Jminus.mulVec ketDown = 0 := by
  ext i
  fin_cases i <;> norm_num [Jminus, Matrix.mulVec, Fin.sum_univ_two, ketDown]

/-- `J₀` eigenvalue `+1/2` on spin-up. -/
theorem J0_ketUp : J0.mulVec ketUp = (1 / 2 : ℚ) • ketUp := by
  ext i
  fin_cases i <;> norm_num [J0, Matrix.mulVec, Fin.sum_univ_two, ketUp]

/-- `J₀` eigenvalue `-1/2` on spin-down. -/
theorem J0_ketDown : J0.mulVec ketDown = (-(1 / 2 : ℚ)) • ketDown := by
  ext i
  fin_cases i <;> norm_num [J0, Matrix.mulVec, Fin.sum_univ_two, ketDown]

/-- Finite SUSY supercharge lowering from bosonic to fermionic sector with amplitude `a`. -/
def superchargeA (a : ℂ) : Mat2C :=
  !![0, 0;
     a, 0]

/-- Finite SUSY supercharge raising from fermionic to bosonic sector with amplitude `b`. -/
def superchargeAdag (b : ℂ) : Mat2C :=
  !![0, b;
     0, 0]

/-- Finite partner Hamiltonian `H₋ = A†A`. -/
noncomputable def HminusFinite (a b : ℂ) : Mat2C :=
  superchargeAdag b * superchargeA a

/-- Finite partner Hamiltonian `H₊ = AA†`. -/
noncomputable def HplusFinite (a b : ℂ) : Mat2C :=
  superchargeA a * superchargeAdag b

/-- The finite `H₋` block has eigenvalue product `ba` in the bosonic slot. -/
theorem HminusFinite_eq (a b : ℂ) :
    HminusFinite a b = !![b * a, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HminusFinite, superchargeA, superchargeAdag, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite `H₊` block has eigenvalue product `ab` in the fermionic slot. -/
theorem HplusFinite_eq (a b : ℂ) :
    HplusFinite a b = !![0, 0; 0, a * b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HplusFinite, superchargeA, superchargeAdag, Matrix.mul_apply, Fin.sum_univ_two]

/-- If the zeta-product amplitude vanishes, both finite partner blocks vanish. -/
theorem finite_partner_blocks_zero_of_product_zero {a b : ℂ} (h : a * b = 0) :
    HminusFinite a b = 0 ∧ HplusFinite a b = 0 := by
  constructor
  · rw [HminusFinite_eq]
    have hb : b * a = 0 := by simpa [mul_comm] using h
    rw [hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [HplusFinite_eq]
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Fermion-parity grading used in the Witten trace. -/
def fermionParity : Mat2Q :=
  !![1, 0;
     0, -1]

/-- Finite Witten trace of a zero-mode occupancy diagonal. -/
def finiteWittenTrace (nB nF : ℚ) : ℚ :=
  trace (fermionParity * !![nB, 0; 0, nF])

/-- The finite Witten trace is the boson-minus-fermion count. -/
theorem finiteWittenTrace_eq (nB nF : ℚ) :
    finiteWittenTrace nB nF = nB - nF := by
  simp [finiteWittenTrace, fermionParity, Fin.sum_univ_two, Matrix.trace]
  ring

/-- Finite parity operator for the direct-sum PT shadow. -/
def parityP : Mat2Q :=
  !![0, 1;
     1, 0]

/-- The parity shadow is an involution. -/
theorem parityP_sq : parityP * parityP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [parityP, Matrix.mul_apply, Fin.sum_univ_two]

/-- A diagonal two-level Hamiltonian is parity-invariant exactly when the two diagonal entries agree. -/
theorem parity_conjugates_diagonal (Eleft Eright : ℚ) :
    parityP * !![Eleft, 0; 0, Eright] * parityP = !![Eright, 0; 0, Eleft] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [parityP, Matrix.mul_apply, Fin.sum_univ_two]

/-- Abstract gate saying a chosen zeta product vanishes. -/
def ZetaProductZero (zeta : ZetaCoordinate → ℂ) (s : ZetaCoordinate) : Prop :=
  zeta s * zeta (oneMinus s) = 0

/-- A zeta-product zero makes the scalar SUSY block vanish. -/
theorem susyBlock_zero_of_ZetaProductZero
    {zeta : ZetaCoordinate → ℂ} {s : ZetaCoordinate} (h : ZetaProductZero zeta s) :
    susyHamiltonianBlock (zeta s * zeta (oneMinus s)) (zeta s * zeta (oneMinus s)) = 0 :=
  susyHamiltonianBlock_zero_of_energy_zero h

/-- Consolidated kernel-checked packet for arXiv:2309.01382. -/
theorem arxiv230901382_finite_symmetry_packet :
    wittenIndex 1 1 = 0 ∧
      wittenStatus 1 1 = .unbroken ∧
      wittenStatus 0 0 = .broken ∧
      commQ Jplus Jminus = (2 : ℚ) • J0 ∧
      commQ J0 Jplus = Jplus ∧
      commQ J0 Jminus = -Jminus ∧
      spinHalfCasimir = (3 / 4 : ℚ) • (1 : Mat2Q) ∧
      Jplus.mulVec ketDown = ketUp ∧
      Jminus.mulVec ketUp = ketDown ∧
      finiteWittenTrace 1 1 = 0 ∧
      parityP * parityP = 1 := by
  exact ⟨rfl, rfl, rfl, comm_Jplus_Jminus, comm_J0_Jplus,
    comm_J0_Jminus, spinHalfCasimir_eq_three_quarters, Jplus_ketDown,
    Jminus_ketUp, by norm_num [finiteWittenTrace_eq], parityP_sq⟩

end InfoGeometry.Arithmetic.Arxiv230901382RiemannZerosSymmetry
