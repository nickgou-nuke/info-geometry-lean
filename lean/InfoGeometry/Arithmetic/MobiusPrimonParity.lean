import Mathlib
import InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Arithmetic.MobiusPrimonParity

Finite square-free Möbius parity readback for split-Majorana primon modes.

This file connects the split-Majorana chirality layer

`Π_p = 1 - 2N_p`

to the existing finite prime-bit Möbius theorem:

`Γ |S⟩ = (-1)^|S| |S⟩ = μ(∏ p∈S p) |S⟩`

for square-free/exterior prime occupations.

It does not assert an infinite Euler product, analytic continuation, RH, CFT
locality, or a spectral zero-mode theorem.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MobiusPrimonParity

open scoped BigOperators
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.SplitMajoranaPrimon
open InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter

/-! ## 1. Square-free primon occupation states -/

/-- A square-free primon state is a finite occupied subset of a certified prime register. -/
abbrev SquareFreePrimonState (P : PrimeRegister) :=
  {S : Finset ℕ // S ⊆ P.primes}

namespace SquareFreePrimonState

variable {P : PrimeRegister}

/-- The occupied prime subset of a square-free primon state. -/
def support (S : SquareFreePrimonState P) : Finset ℕ :=
  S.1

/-- The support is contained in the ambient prime register. -/
theorem support_subset (S : SquareFreePrimonState P) :
    S.support ⊆ P.primes :=
  S.2

/-- The represented square-free integer `∏ p∈S p`. -/
def representedNat (S : SquareFreePrimonState P) : ℕ :=
  ∏ p ∈ S.support, p

/-- Fermion number of a square-free primon state. -/
def fermionNumber (S : SquareFreePrimonState P) : ℕ :=
  S.support.card

/-- Fermion parity of a square-free primon state. -/
def fermionParity (S : SquareFreePrimonState P) : ℤ :=
  (-1 : ℤ) ^ S.fermionNumber

/-- Split-Majorana chirality readout `Γ_Λ(S) = ∏_p Π_p(S)`. -/
def majoranaChirality (S : SquareFreePrimonState P) : ℤ :=
  globalMajoranaChirality P S.support

/-- Möbius readout of the represented square-free integer. -/
def mobiusReadout (S : SquareFreePrimonState P) : ℤ :=
  ArithmeticFunction.moebius S.representedNat

/-- Majorana chirality is fermion parity on square-free primon states. -/
theorem majoranaChirality_eq_fermionParity
    (S : SquareFreePrimonState P) :
    S.majoranaChirality = S.fermionParity := by
  simp [majoranaChirality, fermionParity, fermionNumber,
    globalMajoranaChirality_eq_neg_one_pow_card P S.support S.support_subset]

/-- Möbius readout is fermion parity on square-free primon states. -/
theorem mobiusReadout_eq_fermionParity
    (S : SquareFreePrimonState P) :
    S.mobiusReadout = S.fermionParity := by
  simpa [mobiusReadout, representedNat, fermionParity, fermionNumber, support]
    using mobius_prime_product_eq_parity S.support
      (fun p hp => P.prime_mem p (S.support_subset hp))

/-- Majorana chirality is the Möbius readout on square-free primon states. -/
theorem majoranaChirality_eq_mobiusReadout
    (S : SquareFreePrimonState P) :
    S.majoranaChirality = S.mobiusReadout := by
  rw [majoranaChirality_eq_fermionParity, mobiusReadout_eq_fermionParity]

end SquareFreePrimonState

/-! ## 2. Finite chirality character readbacks -/

/--
Finite Majorana-chirality thermal character over square-free primon occupations.

This is the same finite sum as the Dirichlet Witten character, but with the
coefficient written as the split-Majorana chirality readout.
-/
def finiteMajoranaChiralityCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.primes.powerset,
    (globalMajoranaChirality P S : ℝ) * ∏ p ∈ S, q p

/-- Majorana-chirality character equals the finite Dirichlet Witten character. -/
theorem finiteMajoranaChiralityCharacter_eq_dirichletWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteMajoranaChiralityCharacter P q =
      dirichletWittenCharacter P q := by
  classical
  unfold finiteMajoranaChiralityCharacter dirichletWittenCharacter
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hSub : S ⊆ P.primes := Finset.mem_powerset.mp hS
  rw [globalMajoranaChirality_eq_neg_one_pow_card P S hSub]
  norm_num

/-- Majorana-chirality character is the finite reciprocal Euler product. -/
theorem finiteMajoranaChiralityCharacter_eq_eulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteMajoranaChiralityCharacter P q =
      finiteEulerProduct P q := by
  rw [finiteMajoranaChiralityCharacter_eq_dirichletWittenCharacter,
    dirichletWittenCharacter_eq_eulerProduct]

/-- Majorana-chirality character equals the Möbius graded thermal character. -/
theorem finiteMajoranaChiralityCharacter_eq_mobiusGradedThermalCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteMajoranaChiralityCharacter P q =
      mobiusGradedThermalCharacter P q := by
  rw [finiteMajoranaChiralityCharacter_eq_dirichletWittenCharacter]
  rfl

/-! ## 3. Guardrail for non-square-free integers -/

/--
Nonsquare-free integers are not represented as exterior square-free primon
states; their Möbius coefficient is zero in the arithmetic layer.
-/
theorem mobius_zero_of_not_squarefree
    {n : ℕ} (hn : ¬ Squarefree n) :
    ArithmeticFunction.moebius n = 0 :=
  PrimeBitWittenIndex.mobius_eq_zero_of_not_squarefree hn

/-! ## 4. Owner target -/

/--
Owner target for the finite square-free Möbius parity layer.

This target intentionally stops at finite square-free chirality and finite
Euler products.
-/
@[owner_target_tag]
def MobiusPrimonParityOwnerTarget : Prop :=
  ∀ (P : PrimeRegister) (q : ℕ → ℝ),
    finiteMajoranaChiralityCharacter P q = finiteEulerProduct P q ∧
    finiteMajoranaChiralityCharacter P q = mobiusGradedThermalCharacter P q

/-- The finite square-free Möbius parity owner target is proved. -/
theorem mobiusPrimonParityOwnerTarget :
    MobiusPrimonParityOwnerTarget := by
  intro P q
  exact ⟨finiteMajoranaChiralityCharacter_eq_eulerProduct P q,
    finiteMajoranaChiralityCharacter_eq_mobiusGradedThermalCharacter P q⟩

end InfoGeometry.Arithmetic.MobiusPrimonParity

