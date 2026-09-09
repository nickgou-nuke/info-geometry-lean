import InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator
import InfoGeometry.Arithmetic.PrimeBitFiniteKernelIndexBridge
import InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge
import InfoGeometry.Arithmetic.ChiralPrimonGas
import InfoGeometry.Cocycle.MatrixDetExpTrace
import InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra
import InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional

/-!
# Finite Berry--Keating and prime-register index bridge

This file joins three existing finite readouts on the same square-free prime
register.  A vertex supplies a Berry--Keating Jost root, its arithmetic
square-free integer and Mobius parity, while the whole register supplies the
genuine finite kernel/divisor index.

No equality between a Jost determinant and an index is asserted: the Jost
determinant is a spectral polynomial, whereas the divisor index is a signed
kernel-dimension readout.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.FiniteBerryKeatingPrimeIndexBridge

open InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator
open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.FiniteCantorZetaDirac
open InfoGeometry.Arithmetic.PrimeExteriorRepresentation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeBitFiniteKernelIndexBridge
open InfoGeometry.Arithmetic.IndexTheorem
open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Physics.LorentzChiralCuntzBridge
open InfoGeometry.Arithmetic.PrimeExteriorRepresentation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

abbrev CutoffMode (n : ℕ) :=
  PrimeCantorBerryKeatingOperator.PrimeMode (primeCutoffRegister n)

abbrev CutoffVertex (n : ℕ) :=
  PrimeCantorBerryKeatingOperator.Vertex (primeCutoffRegister n)

theorem primesUpto_succ (n : ℕ) :
    primesUpto (n + 1) =
      if Nat.Prime (n + 1) then insert (n + 1) (primesUpto n)
      else primesUpto n := by
  ext p
  by_cases hp : Nat.Prime (n + 1)
  · rw [if_pos hp]
    simp only [mem_primesUpto_iff, Finset.mem_insert]
    constructor
    · intro h
      by_cases hpn : p = n + 1
      · exact Or.inl hpn
      · exact Or.inr ⟨Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h.1 hpn), h.2⟩
    · rintro (rfl | h)
      · exact ⟨le_rfl, hp⟩
      · exact ⟨h.1.trans (Nat.le_succ n), h.2⟩
  · rw [if_neg hp]
    simp only [mem_primesUpto_iff]
    constructor
    · intro h
      by_cases hpn : p = n + 1
      · exact False.elim (hp (hpn ▸ h.2))
      · exact ⟨Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h.1 hpn), h.2⟩
    · intro h
      exact ⟨h.1.trans (Nat.le_succ n), h.2⟩

theorem cutoffMode_card_succ (n : ℕ) :
    Fintype.card (CutoffMode (n + 1)) =
      if Nat.Prime (n + 1) then
        Fintype.card (CutoffMode n) + 1
      else
        Fintype.card (CutoffMode n) := by
  classical
  change Fintype.card (primesUpto (n + 1) : Type) =
    if Nat.Prime (n + 1) then
      Fintype.card (primesUpto n : Type) + 1
    else
      Fintype.card (primesUpto n : Type)
  simp only [Fintype.card_coe]
  rw [primesUpto_succ]
  by_cases hp : Nat.Prime (n + 1)
  · simp [hp]
  · simp [hp]

def cutoffModeSucc (n : ℕ) : CutoffMode n ↪ CutoffMode (n + 1) where
  toFun p :=
    ⟨p.1, by
      apply (mem_primesUpto_iff.mpr)
      have hp := (mem_primesUpto_iff.mp (show p.1 ∈ primesUpto n from by
        simpa [primeCutoffRegister] using p.2))
      exact ⟨hp.1.trans (Nat.le_succ n), hp.2⟩⟩
  inj' a b h :=
    Subtype.ext (congrArg (fun q : CutoffMode (n + 1) => q.1) h)

def cutoffNewMode (n : ℕ) (hp : Nat.Prime (n + 1)) : CutoffMode (n + 1) :=
  ⟨n + 1, (mem_primesUpto_iff).2 ⟨le_rfl, hp⟩⟩

theorem cutoffModeSucc_ne_new (n : ℕ) (hp : Nat.Prime (n + 1))
    (p : CutoffMode n) :
    cutoffModeSucc n p ≠ cutoffNewMode n hp := by
  intro h
  have hv := congrArg (fun q : CutoffMode (n + 1) => q.1) h
  have hp_le := (mem_primesUpto_iff.mp p.2).1
  dsimp [cutoffModeSucc, cutoffNewMode] at hv
  omega

theorem cutoffMode_succ_cases (n : ℕ) (hp : Nat.Prime (n + 1))
    (q : CutoffMode (n + 1)) :
    (∃ p : CutoffMode n, cutoffModeSucc n p = q) ∨
      q = cutoffNewMode n hp := by
  have hq := mem_primesUpto_iff.mp q.2
  by_cases hqnew : q.1 = n + 1
  · exact Or.inr (Subtype.ext hqnew)
  · left
    have hqn : q.1 ≤ n :=
      Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hq.1 hqnew)
    let p : CutoffMode n :=
      ⟨q.1, (mem_primesUpto_iff).2 ⟨hqn, hq.2⟩⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    rfl

noncomputable def cutoffModeOptionEquiv (n : ℕ) (hp : Nat.Prime (n + 1)) :
    Option (CutoffMode n) ≃ CutoffMode (n + 1) := by
  let f : Option (CutoffMode n) → CutoffMode (n + 1) := fun o =>
    match o with
    | none => cutoffNewMode n hp
    | some p => cutoffModeSucc n p
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some p =>
              exact False.elim
                ((cutoffModeSucc_ne_new n hp p) hab.symm)
      | some p =>
          cases b with
          | none =>
              exact False.elim
                ((cutoffModeSucc_ne_new n hp p) hab)
          | some q =>
              congr
              exact Subtype.ext
                (congrArg (fun r : CutoffMode (n + 1) => r.1) hab)
    · intro q
      rcases cutoffMode_succ_cases n hp q with ⟨p, hpq⟩ | hq
      · exact ⟨some p, hpq⟩
      · exact ⟨none, hq.symm⟩
  exact Equiv.ofBijective f hf

@[simp] theorem cutoffModeOptionEquiv_none (n : ℕ)
    (hp : Nat.Prime (n + 1)) :
    cutoffModeOptionEquiv n hp none = cutoffNewMode n hp := by
  rfl

@[simp] theorem cutoffModeOptionEquiv_some (n : ℕ)
    (hp : Nat.Prime (n + 1)) (p : CutoffMode n) :
    cutoffModeOptionEquiv n hp (some p) = cutoffModeSucc n p := by
  rfl

def optionArrowBoolEquiv (α : Type*) :
    (Option α → Bool) ≃ ((α → Bool) × Bool) where
  toFun f := (fun a => f (some a), f none)
  invFun p := fun o => match o with
    | none => p.2
    | some a => p.1 a
  left_inv := by
    intro f
    funext o
    cases o <;> rfl
  right_inv := by
    intro p
    cases p with
    | mk f b =>
        rfl

def cutoffModeBooleanSuccEquiv (n : ℕ) (hp : Nat.Prime (n + 1)) :
    (CutoffMode (n + 1) → Bool) ≃
      ((CutoffMode n → Bool) × Bool) :=
  (Equiv.arrowCongr (cutoffModeOptionEquiv n hp).symm
      (Equiv.refl Bool)).trans (optionArrowBoolEquiv (CutoffMode n))

def cutoffVertexSuccEquiv (n : ℕ) (hp : Nat.Prime (n + 1)) :
    CutoffVertex (n + 1) ≃ (CutoffVertex n × Bool) :=
  (booleanCoordinatesEquiv (CutoffMode (n + 1))).trans
    ((cutoffModeBooleanSuccEquiv n hp).trans
      (Equiv.prodCongr
        (booleanCoordinatesEquiv (CutoffMode n)).symm
        (Equiv.refl Bool)))

def cutoffVertexSucc (n : ℕ) : CutoffVertex n → CutoffVertex (n + 1) :=
  fun S => S.map (cutoffModeSucc n)

theorem cutoffVertexSuccEquiv_old (n : ℕ) (hp : Nat.Prime (n + 1))
    (S : CutoffVertex n) :
    cutoffVertexSuccEquiv n hp (cutoffVertexSucc n S) = (S, false) := by
  apply Prod.ext
  · apply (booleanCoordinatesEquiv (CutoffMode n)).injective
    funext p
    simp [cutoffVertexSuccEquiv, cutoffModeBooleanSuccEquiv,
      optionArrowBoolEquiv, cutoffVertexSucc,
      booleanCoordinatesEquiv_apply_mem]
  · change booleanCoordinatesEquiv (CutoffMode (n + 1))
      (cutoffVertexSucc n S) (cutoffNewMode n hp) = false
    rw [booleanCoordinatesEquiv_apply_mem]
    simp [cutoffVertexSucc, cutoffModeSucc_ne_new n hp]

def cutoffNewVertex (n : ℕ) (hp : Nat.Prime (n + 1)) :
    CutoffVertex (n + 1) :=
  {cutoffNewMode n hp}

def cutoffVertexAddNew (n : ℕ) (hp : Nat.Prime (n + 1))
    (S : CutoffVertex n) : CutoffVertex (n + 1) :=
  insert (cutoffNewMode n hp) (cutoffVertexSucc n S)

theorem cutoffVertexSuccEquiv_new (n : ℕ) (hp : Nat.Prime (n + 1)) :
    cutoffVertexSuccEquiv n hp (cutoffNewVertex n hp) =
      (∅, true) := by
  apply Prod.ext
  · apply (booleanCoordinatesEquiv (CutoffMode n)).injective
    funext p
    have hneq : cutoffModeSucc n p ≠ cutoffNewMode n hp :=
      cutoffModeSucc_ne_new n hp p
    simp [cutoffNewVertex, cutoffVertexSuccEquiv,
      cutoffModeBooleanSuccEquiv, optionArrowBoolEquiv,
      booleanCoordinatesEquiv_apply_mem, hneq]
  · change booleanCoordinatesEquiv (CutoffMode (n + 1))
      (cutoffNewVertex n hp) (cutoffNewMode n hp) = true
    rw [booleanCoordinatesEquiv_apply_mem]
    simp [cutoffNewVertex]

theorem cutoffVertexSuccEquiv_addNew (n : ℕ) (hp : Nat.Prime (n + 1))
    (S : CutoffVertex n) :
    cutoffVertexSuccEquiv n hp (cutoffVertexAddNew n hp S) =
      (S, true) := by
  apply Prod.ext
  · apply (booleanCoordinatesEquiv (CutoffMode n)).injective
    funext p
    have hneq : cutoffModeSucc n p ≠ cutoffNewMode n hp :=
      cutoffModeSucc_ne_new n hp p
    have hmap : cutoffModeSucc n p ∈ cutoffVertexSucc n S ↔ p ∈ S := by
      rw [cutoffVertexSucc]
      simp
    simp [cutoffVertexAddNew, cutoffVertexSuccEquiv,
      cutoffModeBooleanSuccEquiv, optionArrowBoolEquiv,
      booleanCoordinatesEquiv_apply_mem, hneq, hmap]
  · change booleanCoordinatesEquiv (CutoffMode (n + 1))
      (cutoffVertexAddNew n hp S) (cutoffNewMode n hp) = true
    rw [booleanCoordinatesEquiv_apply_mem]
    simp [cutoffVertexAddNew]

theorem cutoffVertexSucc_card (n : ℕ) (S : CutoffVertex n) :
    (cutoffVertexSucc n S).card = S.card := by
  exact Finset.card_map (cutoffModeSucc n)

/-! The finite prime/Fock carrier has the expected Boolean-cube cardinality.
This is a carrier theorem only: it does not identify the cutoff successor with
the dyadic UHF bonding map. -/
theorem cutoffVertex_card (n : ℕ) :
    Fintype.card (CutoffVertex n) = 2 ^ Fintype.card (CutoffMode n) := by
  exact InfoGeometry.Arithmetic.PrimeExteriorRepresentation.card_squareFreePrimeState
    (CutoffMode n)

/-! The corresponding finite Fock-coordinate equivalence.  Its target is
`Fin (card (CutoffMode n)) → Bool`; this is the exact finite coordinate type
needed for matrix reindexing, without asserting compatibility with a dyadic
stage index. -/
def cutoffVertexBitWordEquiv (n : ℕ) :
    CutoffVertex n ≃ (Fin (Fintype.card (CutoffMode n)) → Bool) :=
  (booleanCoordinatesEquiv (CutoffMode n)).trans
    (Equiv.arrowCongr (Fintype.equivFin (CutoffMode n)) (Equiv.refl Bool))

/-! ## Finite BK matrix and Jost operator representations -/

def bkHamiltonianMatrix {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) :
    Matrix (Vertex P) (Vertex P) ℂ :=
  Matrix.diagonal (fun S => (bkEnergy logPrime S : ℂ))

def bkJostDet {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) (z : ℂ) : ℂ :=
  (z • (1 : Matrix (Vertex P) (Vertex P) ℂ) -
      bkHamiltonianMatrix logPrime).det

theorem bkHamiltonianMatrix_isHermitian {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) :
    (bkHamiltonianMatrix logPrime).IsHermitian := by
  unfold Matrix.IsHermitian bkHamiltonianMatrix
  ext S T
  by_cases hST : S = T
  · subst hST
    simp
  · simp [Matrix.conjTranspose, Matrix.diagonal, hST, Ne.symm hST]

theorem bkJostDet_eq_prod {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) (z : ℂ) :
    bkJostDet logPrime z =
      ∏ S : Vertex P, (z - (bkEnergy logPrime S : ℂ)) := by
  unfold bkJostDet bkHamiltonianMatrix
  have hdiag : z • (1 : Matrix (Vertex P) (Vertex P) ℂ) -
      Matrix.diagonal (fun S => (bkEnergy logPrime S : ℂ)) =
      Matrix.diagonal (fun S => z - (bkEnergy logPrime S : ℂ)) := by
    ext S T
    by_cases hST : S = T
    · subst hST
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hST]
  rw [hdiag]
  exact Matrix.det_diagonal

theorem bkJostDet_zero_of_basisDelta_eigenvalue {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) (S : Vertex P) :
    bkJostDet logPrime (bkEnergy logPrime S : ℂ) = 0 := by
  rw [bkJostDet_eq_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ S) (sub_self _)

theorem bkEnergy_primeEnergy_eq_stateEnergy {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (S : Vertex P) :
    bkEnergy (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P => Real.log (p : ℝ)) S =
      InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.stateEnergy S := by
  unfold bkEnergy InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.stateEnergy
  rfl

theorem bkEnergy_primeEnergy_eq_log_stateNat {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (S : Vertex P) :
    bkEnergy (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P => Real.log (p : ℝ)) S =
      Real.log (InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.stateNat S : ℝ) := by
  have h_ne_zero : ∀ n ∈ natSetOfState S, (n : ℝ) ≠ 0 := by
    intro n hn
    exact_mod_cast (natSetOfState_prime_mem S n hn).ne_zero
  unfold stateNat
  rw [Nat.cast_prod, Real.log_prod h_ne_zero]
  unfold natSetOfState bkEnergy
  rw [Finset.sum_map]
  rfl

theorem bkHamiltonian_isSelfAdjoint {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) :
    IsAdjointPair (P := P) (bkHamiltonian logPrime) (bkHamiltonian logPrime) := by
  intro f g
  unfold pairing bkHamiltonian
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem bkHamiltonian_basisDelta_eigenvector {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) (T : Vertex P) :
    bkHamiltonian logPrime (PrimeCantorZetaDiracOperator.basisDelta T) =
      (bkEnergy logPrime T : ℂ) • PrimeCantorZetaDiracOperator.basisDelta T := by
  funext S
  by_cases hST : S = T
  · subst hST
    simp [bkHamiltonian, PrimeCantorZetaDiracOperator.basisDelta]
  · simp [bkHamiltonian, PrimeCantorZetaDiracOperator.basisDelta, hST]

/-! ## Finite BK stage readout in the native complex UHF tower

The prime-register cutoff has `2 ^ card (CutoffMode n)` vertices.  Reindexing
along this finite equivalence gives an actual matrix in the existing complex
UHF stage.  The stage is then injected into the existing algebraic star
colimit; no successor compatibility is inferred here. -/

noncomputable def cutoffVertexFinEquiv (n : ℕ) :
    CutoffVertex n ≃ Fin (2 ^ Fintype.card (CutoffMode n)) :=
  Fintype.equivFinOfCardEq (cutoffVertex_card n)

noncomputable def bkHamiltonianMatrixStage (n : ℕ)
    (logPrime : CutoffMode n → ℝ) :
    MatrixStage (Fintype.card (CutoffMode n)) :=
  Matrix.reindex (cutoffVertexFinEquiv n) (cutoffVertexFinEquiv n)
    (bkHamiltonianMatrix logPrime)

theorem bkHamiltonianMatrixStage_det (n : ℕ)
    (logPrime : CutoffMode n → ℝ) :
    Matrix.det (bkHamiltonianMatrixStage n logPrime) =
      Matrix.det (bkHamiltonianMatrix logPrime) := by
  unfold bkHamiltonianMatrixStage
  exact Matrix.det_reindex_self (cutoffVertexFinEquiv n)
    (bkHamiltonianMatrix logPrime)

theorem bkHamiltonianMatrixStage_trace (n : ℕ)
    (logPrime : CutoffMode n → ℝ) :
    Matrix.trace (bkHamiltonianMatrixStage n logPrime) =
      Matrix.trace (bkHamiltonianMatrix logPrime) := by
  unfold bkHamiltonianMatrixStage
  change Matrix.trace
      ((Matrix.reindexAlgEquiv ℂ ℂ (cutoffVertexFinEquiv n))
        (bkHamiltonianMatrix logPrime)) = _
  exact trace_reindex (cutoffVertexFinEquiv n)
    (bkHamiltonianMatrix logPrime)

theorem bkHamiltonianMatrixStage_isHermitian (n : ℕ)
    (logPrime : CutoffMode n → ℝ) :
    (bkHamiltonianMatrixStage n logPrime).IsHermitian := by
  unfold Matrix.IsHermitian bkHamiltonianMatrixStage
  ext v w
  by_cases h : v = w
  · subst h
    simp [Matrix.conjTranspose, bkHamiltonianMatrix]
  · simp [Matrix.conjTranspose, bkHamiltonianMatrix, h]

noncomputable def bkHamiltonianColimit (n : ℕ)
    (logPrime : CutoffMode n → ℝ) :
    InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier :=
  stageInjection (Fintype.card (CutoffMode n))
    (bkHamiltonianMatrixStage n logPrime)

theorem bkHamiltonianColimit_isSelfAdjoint (n : ℕ)
    (logPrime : CutoffMode n → ℝ) :
    star (bkHamiltonianColimit n logPrime) =
      bkHamiltonianColimit n logPrime := by
  rw [bkHamiltonianColimit, ← stageInjection_star]
  exact congrArg
    (stageInjection (Fintype.card (CutoffMode n)))
    (bkHamiltonianMatrixStage_isHermitian n logPrime)

theorem bkHamiltonianColimit_trace (n : ℕ)
    (logPrime : CutoffMode n → ℝ) :
    traceFunctional (bkHamiltonianColimit n logPrime) =
      (1 / (2 ^ Fintype.card (CutoffMode n) : ℂ)) *
        Matrix.trace (bkHamiltonianMatrix logPrime) := by
  rw [bkHamiltonianColimit, traceFunctional_stage,
    matrixTraceState_apply, bkHamiltonianMatrixStage_trace]

theorem bkHamiltonianColimit_trace_eq_normalized_energy_sum (n : ℕ)
    (logPrime : CutoffMode n → ℝ) :
    traceFunctional (bkHamiltonianColimit n logPrime) =
      (1 / (2 ^ Fintype.card (CutoffMode n) : ℂ)) *
        (∑ S : CutoffVertex n, (bkEnergy logPrime S : ℂ)) := by
  rw [bkHamiltonianColimit_trace]
  simp [bkHamiltonianMatrix]

theorem cutoff_bkEnergy_succ (n : ℕ) (S : CutoffVertex n) :
    bkEnergy
        (fun p : CutoffMode (n + 1) => Real.log (p : ℝ))
        (cutoffVertexSucc n S) =
      bkEnergy (fun p : CutoffMode n => Real.log (p : ℝ)) S := by
  unfold cutoffVertexSucc bkEnergy
  rw [Finset.sum_map]
  rfl

theorem cutoff_bkEnergy_addNew (n : ℕ) (hp : Nat.Prime (n + 1))
    (S : CutoffVertex n) :
    bkEnergy
        (fun p : CutoffMode (n + 1) => Real.log (p : ℝ))
        (cutoffVertexAddNew n hp S) =
      bkEnergy (fun p : CutoffMode n => Real.log (p : ℝ)) S +
        Real.log (n + 1 : ℝ) := by
  have hnot : cutoffNewMode n hp ∉ cutoffVertexSucc n S := by
    intro h
    rcases Finset.mem_map.mp h with ⟨p, _hpS, heq⟩
    exact cutoffModeSucc_ne_new n hp p heq
  unfold cutoffVertexAddNew
  calc
    bkEnergy
        (fun p : CutoffMode (n + 1) => Real.log (p : ℝ))
        (insert (cutoffNewMode n hp) (cutoffVertexSucc n S)) =
      Real.log (cutoffNewMode n hp : ℝ) +
        bkEnergy
          (fun p : CutoffMode (n + 1) => Real.log (p : ℝ))
          (cutoffVertexSucc n S) := by
      simp [bkEnergy, hnot]
    _ = bkEnergy (fun p : CutoffMode n => Real.log (p : ℝ)) S +
        Real.log (n + 1 : ℝ) := by
      rw [cutoff_bkEnergy_succ]
      dsimp [cutoffNewMode]
      rw [add_comm]
      congr 1
      norm_num

theorem cutoff_bkEnergy_successor_pair (n : ℕ)
    (hp : Nat.Prime (n + 1)) (S : CutoffVertex n) :
    bkEnergy
          (fun p : CutoffMode (n + 1) => Real.log (p : ℝ))
          ((cutoffVertexSuccEquiv n hp).symm (S, false)) +
        bkEnergy
          (fun p : CutoffMode (n + 1) => Real.log (p : ℝ))
          ((cutoffVertexSuccEquiv n hp).symm (S, true)) =
      2 * bkEnergy (fun p : CutoffMode n => Real.log (p : ℝ)) S +
        Real.log (n + 1 : ℝ) := by
  have hfalse :
      (cutoffVertexSuccEquiv n hp).symm (S, false) =
        cutoffVertexSucc n S := by
    apply (cutoffVertexSuccEquiv n hp).injective
    rw [Equiv.apply_symm_apply, cutoffVertexSuccEquiv_old]
  have htrue :
      (cutoffVertexSuccEquiv n hp).symm (S, true) =
        cutoffVertexAddNew n hp S := by
    apply (cutoffVertexSuccEquiv n hp).injective
    rw [Equiv.apply_symm_apply, cutoffVertexSuccEquiv_addNew]
  rw [hfalse, htrue, cutoff_bkEnergy_succ, cutoff_bkEnergy_addNew]
  ring

theorem cutoff_bkEnergy_sum_succ (n : ℕ)
    (hp : Nat.Prime (n + 1)) :
    (∑ T : CutoffVertex (n + 1),
        bkEnergy
          (fun p : CutoffMode (n + 1) => Real.log (p : ℝ)) T) =
      ∑ S : CutoffVertex n,
        (2 * bkEnergy (fun p : CutoffMode n => Real.log (p : ℝ)) S +
          Real.log (n + 1 : ℝ)) := by
  rw [← Equiv.sum_comp (cutoffVertexSuccEquiv n hp).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro S _
  simpa [add_comm] using cutoff_bkEnergy_successor_pair n hp S

theorem cutoff_bkEnergy_normalized_sum_succ (n : ℕ)
    (hp : Nat.Prime (n + 1)) :
    (1 / (2 ^ Fintype.card (CutoffMode (n + 1)) : ℝ)) *
        (∑ T : CutoffVertex (n + 1),
          bkEnergy
            (fun p : CutoffMode (n + 1) => Real.log (p : ℝ)) T) =
      (1 / (2 ^ Fintype.card (CutoffMode n) : ℝ)) *
          (∑ S : CutoffVertex n,
            bkEnergy (fun p : CutoffMode n => Real.log (p : ℝ)) S) +
        (1 / 2 : ℝ) * Real.log (n + 1 : ℝ) := by
  rw [cutoff_bkEnergy_sum_succ n hp, cutoffMode_card_succ n]
  simp only [if_pos hp]
  have hsum :
      (∑ S : CutoffVertex n,
          (2 * bkEnergy (fun p : CutoffMode n => Real.log (p : ℝ)) S +
            Real.log (n + 1 : ℝ))) =
        2 * (∑ S : CutoffVertex n,
          bkEnergy (fun p : CutoffMode n => Real.log (p : ℝ)) S) +
          (2 ^ Fintype.card (CutoffMode n) : ℝ) * Real.log (n + 1 : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hconst :
        (∑ S : CutoffVertex n, Real.log (n + 1 : ℝ)) =
          (Fintype.card (CutoffVertex n) : ℝ) * Real.log (n + 1 : ℝ) := by
      simp
    rw [hconst, cutoffVertex_card]
    simp [mul_comm]
  rw [hsum, pow_succ]
  field_simp [pow_ne_zero (Fintype.card (CutoffMode n))
    (by norm_num : (2 : ℝ) ≠ 0)]

/-! The finite critical-line holonomy is compatible with the register
successor.  This is the phase-level wire needed before any directed-limit
lift; no determinant statement is inferred from it. -/
theorem cutoff_bkStatePhase_succ (n : ℕ) (t : ℝ) (S : CutoffVertex n) :
    bkStatePhase
        (fun p : CutoffMode (n + 1) => Real.log (p : ℝ)) t
        (cutoffVertexSucc n S) =
      bkStatePhase (fun p : CutoffMode n => Real.log (p : ℝ)) t S := by
  unfold bkStatePhase
  rw [cutoff_bkEnergy_succ]

/-! ## Finite chiral/projective realization of the BK phase -/

theorem expDiagSL2_projective_multiplier (η : ℂ) :
    (spinMatrix (expDiagSL2 η)) 0 0 /
        (spinMatrix (expDiagSL2 η)) 1 1 = Complex.exp (2 * η) := by
  change Complex.exp η / (Complex.exp η)⁻¹ = Complex.exp (2 * η)
  rw [div_eq_mul_inv, inv_inv, ← Complex.exp_add]
  congr 1
  ring

theorem bkStatePhase_eq_expDiagSL2_projective_multiplier
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ)
    (t : ℝ) (S : Vertex P) :
    (spinMatrix (expDiagSL2
        (-(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ)) / 2))) 0 0 /
        (spinMatrix (expDiagSL2
          (-(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ)) / 2))) 1 1 =
      bkStatePhase logPrime t S := by
  rw [expDiagSL2_projective_multiplier]
  simp [bkStatePhase]
  congr 1
  ring

theorem bkJostDet_zero_at_stateNat_log
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (S : Vertex P) :
    bkJostDet (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P => Real.log (p : ℝ))
        (Real.log (stateNat S : ℝ) : ℂ) = 0 := by
  rw [← bkEnergy_primeEnergy_eq_log_stateNat S]
  exact bkJostDet_zero_of_basisDelta_eigenvalue
    (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P => Real.log (p : ℝ)) S

theorem bkJostDet_zero_at_stateNat_log_iff_eigenstate
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (S : Vertex P) :
    bkJostDet (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P => Real.log (p : ℝ))
        (Real.log (stateNat S : ℝ) : ℂ) = 0 ∧
      ∃ f : CantorField P, f ≠ 0 ∧
        bkHamiltonian
          (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P => Real.log (p : ℝ)) f =
          (Real.log (stateNat S : ℝ) : ℂ) • f := by
  refine ⟨bkJostDet_zero_at_stateNat_log S, ?_⟩
  refine ⟨PrimeCantorZetaDiracOperator.basisDelta S, ?_, ?_⟩
  · intro hzero
    have hvalue := congrFun hzero S
    simp [PrimeCantorZetaDiracOperator.basisDelta] at hvalue
  · rw [← bkEnergy_primeEnergy_eq_log_stateNat S]
    exact bkHamiltonian_basisDelta_eigenvector
      (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P => Real.log (p : ℝ)) S

theorem stateNat_mobius_eq_prime_register_parity
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (S : Vertex P) :
    ArithmeticFunction.moebius (stateNat S) =
      SquareFreePrimeState.fermionParitySign S :=
  mobius_stateNat_eq_fermionParitySign S

theorem finite_prime_register_kernel_divisor_index
    (P : PrimeBitWittenIndex.PrimeRegister) :
    finiteKernelIndex (primeRegisterParityComplex P) =
      InfoGeometry.Algebra.EulerLaurentDerivation.divisorIndex
        P.primes.powerset primeRegisterParityCharge :=
  finite_kernel_index_prime_register_parity_eq_divisorIndex P

theorem bkHamiltonianMatrix_exp_det_eq_exp_trace
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) :
    Matrix.det (NormedSpace.exp (bkHamiltonianMatrix logPrime)) =
      NormedSpace.exp (Matrix.trace (bkHamiltonianMatrix logPrime)) := by
  exact InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace _

/-- The complete finite packet carried by one square-free prime register. -/
theorem finite_bk_prime_packet
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff} (S : Vertex P) :
    bkJostDet (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P => Real.log (p : ℝ))
        (Real.log (stateNat S : ℝ) : ℂ) = 0 ∧
      ArithmeticFunction.moebius (stateNat S) =
        SquareFreePrimeState.fermionParitySign S ∧
      finiteKernelIndex (primeRegisterParityComplex P) =
        InfoGeometry.Algebra.EulerLaurentDerivation.divisorIndex
          P.primes.powerset primeRegisterParityCharge := by
  refine ⟨bkJostDet_zero_at_stateNat_log S,
    stateNat_mobius_eq_prime_register_parity S,
    finite_prime_register_kernel_divisor_index P⟩

/-! ## Finite spectral/index synthesis on the common prime register -/

theorem finite_bk_operator_index_packet
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeCantorBerryKeatingOperator.PrimeMode P → ℝ) :
    IsAdjointPair (P := P) (bkHamiltonian logPrime) (bkHamiltonian logPrime) ∧
      (bkHamiltonianMatrix logPrime).IsHermitian ∧
      (∀ S : Vertex P,
        bkJostDet
            (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P =>
              Real.log (p : ℝ))
            (Real.log (stateNat S : ℝ) : ℂ) = 0 ∧
          ∃ f : CantorField P, f ≠ 0 ∧
            bkHamiltonian
                (fun p : PrimeCantorBerryKeatingOperator.PrimeMode P =>
                  Real.log (p : ℝ)) f =
              (Real.log (stateNat S : ℝ) : ℂ) • f) ∧
      finiteKernelIndex (primeRegisterParityComplex P) =
        InfoGeometry.Algebra.EulerLaurentDerivation.divisorIndex
          P.primes.powerset primeRegisterParityCharge := by
  refine ⟨bkHamiltonian_isSelfAdjoint logPrime,
    bkHamiltonianMatrix_isHermitian logPrime, ?_,
    finite_prime_register_kernel_divisor_index P⟩
  intro S
  exact bkJostDet_zero_at_stateNat_log_iff_eigenstate S

end InfoGeometry.Arithmetic.FiniteBerryKeatingPrimeIndexBridge
