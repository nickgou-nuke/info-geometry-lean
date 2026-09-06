import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCliffordSourceWickBase
import InfoGeometry.Canonical.SplitCliffordJordanWigner
import InfoGeometry.Canonical.ModularNilpotentAutomorphism
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Topology.FractalCantorFock

noncomputable section

namespace InfoGeometry.Canonical.CantorFockSpace

open Matrix
open InfoGeometry.Canonical.SplitCliffordSourceWickBase
open InfoGeometry.Canonical.ModularNilpotentAutomorphism
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Topology.FractalCantorFock

set_option linter.unusedSectionVars false

/-- Local Wick seed as the nilpotent annihilation coordinate. -/
abbrev localAnnihilation : M2R :=
  a

/-- Local Wick adjoint-like creation coordinate. -/
abbrev localCreation : M2R :=
  aDag

/-- Local local vacuum vector (single-mode column). -/
abbrev localVacuumVector : Matrix (Fin 2) (Fin 1) ℝ :=
  vac

/-- Square-zero of the local annihilation mode: `N^2 = 0`. -/
@[simp] theorem localAnnihilation_sq_zero :
    localAnnihilation * localAnnihilation = (0 : M2R) := by
  change N * N = (0 : M2R)
  exact ModularNilpotentAutomorphism.N_sq_zero

/-- Square-zero of the local creation mode: `a^\u2020² = 0`. -/
@[simp] theorem localCreation_sq_zero :
    localCreation * localCreation = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localCreation, aDag, Matrix.mul_apply, Fin.sum_univ_two]

/-- Local CAR identity from the same Wick atom: `{a, a^\u2020} = 1`. -/
@[simp] theorem localCAR :
    localAnnihilation * localCreation + localCreation * localAnnihilation = (1 : M2R) := by
  simpa [localAnnihilation, localCreation] using local_car_identity

/-- Local vacuum annihilation identity: `a |0\rangle = 0`. -/
theorem localVacuum_annihilation :
    localAnnihilation * localVacuumVector = 0 := by
  simpa [localAnnihilation, localVacuumVector] using vacuum_annihilation

/-- Concrete local Jordan--Wigner parity operator carried by this atom. -/
def localParity : M2R :=
  SplitCliffordJordanWigner.P

@[simp] theorem localParity_sq :
    localParity * localParity = (1 : M2R) := by
  simpa [localParity] using SplitCliffordJordanWigner.parity_sq_eq_one

@[simp] theorem localParity_conj_annihilation :
    localParity * localAnnihilation * localParity = -localAnnihilation := by
  simpa [localParity, localAnnihilation] using
    SplitCliffordJordanWigner.parity_conj_annihilate

@[simp] theorem localParity_conj_creation :
    localParity * localCreation * localParity = -localCreation := by
  simpa [localParity, localCreation] using
    SplitCliffordJordanWigner.parity_conj_create

theorem localParity_mul_annihilation :
    localParity * localAnnihilation =
      -(localAnnihilation * localParity) := by
  calc
    localParity * localAnnihilation =
        localParity * localAnnihilation *
          (localParity * localParity) := by
            rw [localParity_sq]
            simp
    _ = (localParity * localAnnihilation * localParity) * localParity := by
          noncomm_ring
    _ = (-localAnnihilation) * localParity := by
          rw [localParity_conj_annihilation]
    _ = -(localAnnihilation * localParity) := by
          simp

theorem localParity_mul_creation :
    localParity * localCreation =
      -(localCreation * localParity) := by
  calc
    localParity * localCreation =
        localParity * localCreation *
          (localParity * localParity) := by
            rw [localParity_sq]
            simp
    _ = (localParity * localCreation * localParity) * localParity := by
          noncomm_ring
    _ = (-localCreation) * localParity := by
          rw [localParity_conj_creation]
    _ = -(localCreation * localParity) := by
          simp

theorem localParity_vacuum :
    localParity * localVacuumVector = localVacuumVector := by
  simpa [localParity, localVacuumVector] using
    SplitCliffordJordanWigner.parity_vacuum

/-- Finite CAR pair extracted from the local nilpotent seed. -/
def localCARPair : RealCARPair M2R where
  annihilation := localAnnihilation
  creation := localCreation
  nilpotent_annihilation := localAnnihilation_sq_zero
  nilpotent_creation := localCreation_sq_zero
  car := localCAR

/-- The `C*`-free local annihilation readout from the modular seed equals the entropy flux. -/
theorem local_entropyFlux_eq_annihilation :
    entropyFlux = localAnnihilation := by
  simpa [localAnnihilation, entropyFlux] using (ModularNilpotentAutomorphism.entropyFlux_eq_N : entropyFlux = N)

/-- The local modular free-energy operator is zero in this sector. -/
theorem local_informationFreeEnergy_eq_zero :
    informationFreeEnergy = (0 : M2R) := by
  simpa [informationFreeEnergy] using informationFreeEnergy_eq_zero

/-- Canonical vacuum boundary word `0000...`. -/
abbrev vacuumBoundary : (ℕ → Bool) :=
  fun _ : ℕ => false

/-- Finite-cylinder Fock-state readout: a finite prefix is sent to a Hilbert basis vector. -/
def cantorPrefixState
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteHilbertCarrier E) (ξ : (ℕ → Bool)) (n : ℕ) : E :=
  W.orbitBasis (FractalCantorCliffordFockBridge.boundaryPrefix n ξ)

/-- Empty-prefix readout is the Hilbert vacuum basis vector (the empty cylinder). -/
theorem cantorPrefixState_empty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteHilbertCarrier E)
    (ξ : (ℕ → Bool)) :
    cantorPrefixState (W := W) ξ 0 = W.orbitBasis [] := by
  simp [cantorPrefixState]

theorem cantorPrefixState_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteHilbertCarrier E) (ξ : (ℕ → Bool)) (n : ℕ) :
    ‖cantorPrefixState (W := W) ξ n‖ = 1 := by
  exact W.orbit_orthonormal.norm_eq_one _

theorem cantorPrefixState_eq_of_prefix_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteHilbertCarrier E) (ξ η : (ℕ → Bool)) (n : ℕ)
    (h : FractalCantorCliffordFockBridge.boundaryPrefix n ξ =
      FractalCantorCliffordFockBridge.boundaryPrefix n η) :
    cantorPrefixState (W := W) ξ n = cantorPrefixState (W := W) η n := by
  simp [cantorPrefixState, h]

/-- Prefix recursion at one step. -/
theorem cantorPrefixState_succ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteHilbertCarrier E) (ξ : (ℕ → Bool)) (n : ℕ) :
    cantorPrefixState (W := W) ξ (n + 1)
      = W.orbitBasis
          (FractalCantorCliffordFockBridge.boundaryHead ξ ::
            FractalCantorCliffordFockBridge.boundaryPrefix n (FractalCantorCliffordFockBridge.boundaryTail ξ)) := by
  simp [cantorPrefixState, FractalCantorCliffordFockBridge.boundaryPrefix_succ]

/-- Distinct finite prefixes are orthogonal in the Cantor/Fock basis. -/
theorem cantorPrefixState_orthogonal_of_distinct_prefix
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteHilbertCarrier E) (ξ η : (ℕ → Bool))
    (n : ℕ) (h : FractalCantorCliffordFockBridge.boundaryPrefix n ξ ≠
      FractalCantorCliffordFockBridge.boundaryPrefix n η) :
    inner ℂ (cantorPrefixState (W := W) ξ n) (cantorPrefixState (W := W) η n) = 0 := by
  have h' := W.orbit_orthogonal_of_distinct_words (w := FractalCantorCliffordFockBridge.boundaryPrefix n ξ)
    (v := FractalCantorCliffordFockBridge.boundaryPrefix n η) h
  simpa [cantorPrefixState] using h'

/-- Vacuum boundary map along the finite-prefix reconstruction. -/
def cantorVacuumPrefixState
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteHilbertCarrier E) (n : ℕ) : E :=
  cantorPrefixState (W := W) vacuumBoundary n

/-- The vacuum prefix starts at the empty cylinder. -/
theorem cantorVacuumPrefixState_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteHilbertCarrier E) :
    cantorVacuumPrefixState (W := W) 0 = W.orbitBasis [] := by
  simp [cantorVacuumPrefixState, cantorPrefixState]

end InfoGeometry.Canonical.CantorFockSpace
