import InfoGeometry.Arithmetic.PrimitiveSouriauZeta
import InfoGeometry.Canonical.SuperSouriauFermionGasBridge

/-!
InfoGeometry/Arithmetic/PrimitiveBinarySuperZetaBridge.lean

Constructive finite bridge between:

* prime-bit binary occupation profiles;
* logarithmic arithmetic energy;
* the primitive Mellin/zeta kernel;
* finite Souriau-zeta partitions.

This file does not prove the primitive-set theorem, an infinite Euler product,
the Riemann hypothesis, or a prime-factorization antichain theorem.  It proves
the finite bit-energy identity and the resulting Gibbs/Mellin kernel identity.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.PrimitiveSouriauZeta

/--
A finite prime-bit lattice.

Each index is a fermionic/binary mode.  The mode label is a prime number, and a
profile `ε : Index → Bool` records occupation.
-/
structure FinitePrimeBitLattice where
  Index : Type*
  fintypeIndex : Fintype Index
  decEqIndex : DecidableEq Index
  prime : Index → ℕ
  prime_isPrime : ∀ i : Index, Nat.Prime (prime i)

attribute [instance] FinitePrimeBitLattice.fintypeIndex
attribute [instance] FinitePrimeBitLattice.decEqIndex

namespace FinitePrimeBitLattice

variable (P : FinitePrimeBitLattice)

/-- Binary occupation profiles on the finite prime lattice. -/
abbrev Profile : Type :=
  P.Index → Bool

/-- Occupied prime factor at a mode. -/
def occupiedFactor (ε : P.Profile) (i : P.Index) : ℕ :=
  if ε i then P.prime i else 1

/-- Real occupied prime factor at a mode. -/
def occupiedFactorReal (ε : P.Profile) (i : P.Index) : ℝ :=
  if ε i then (P.prime i : ℝ) else 1

/-- Integer readout of a binary prime profile. -/
def bitInteger (ε : P.Profile) : ℕ :=
  ∏ i : P.Index, P.occupiedFactor ε i

/-- Logarithmic energy of a binary prime profile. -/
def bitEnergy (ε : P.Profile) : ℝ :=
  ∑ i : P.Index, if ε i then Real.log (P.prime i : ℝ) else 0

/-- Positive real value of every occupied-factor readout. -/
theorem occupiedFactorReal_pos
    (ε : P.Profile) (i : P.Index) :
    0 < P.occupiedFactorReal ε i := by
  unfold occupiedFactorReal
  by_cases h : ε i
  · simp [h, Nat.cast_pos.mpr (P.prime_isPrime i).pos]
  · simp [h]

/-- Cast of the finite product defining `bitInteger`. -/
theorem bitInteger_cast
    (ε : P.Profile) :
    ((P.bitInteger ε : ℕ) : ℝ) =
      ∏ i : P.Index, P.occupiedFactorReal ε i := by
  unfold bitInteger occupiedFactor occupiedFactorReal
  simp

/--
Constructive energy identity:

`Σ εᵢ log pᵢ = log (∏ pᵢ^εᵢ)`.
-/
theorem bitEnergy_eq_log_bitInteger
    (ε : P.Profile) :
    P.bitEnergy ε = Real.log (P.bitInteger ε : ℝ) := by
  unfold bitEnergy
  rw [P.bitInteger_cast ε]
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    unfold occupiedFactorReal
    by_cases h : ε i
    · simp [h]
    · simp [h]
  · intro i hi
    exact (P.occupiedFactorReal_pos ε i).ne'

/--
The bit-profile primitive energy agrees with the logarithmic arithmetic energy
of the integer readout.
-/
theorem primitiveEnergy_bitInteger_eq_bitEnergy
    (ε : P.Profile) :
    primitiveEnergy (P.bitInteger ε) = P.bitEnergy ε := by
  unfold primitiveEnergy
  exact (P.bitEnergy_eq_log_bitInteger ε).symm

/--
For nontrivial bit profiles, the primitive Mellin kernel is exactly the Gibbs
factor for the bit-lattice energy.
-/
theorem primitiveMellinKernel_bitInteger_eq_exp_neg_mul_bitEnergy
    (ε : P.Profile) (β : ℝ)
    (hε : 1 < P.bitInteger ε) :
    primitiveMellinKernel (P.bitInteger ε) β =
      Real.exp (-β * P.bitEnergy ε) := by
  rw [P.bitEnergy_eq_log_bitInteger ε]
  simp [primitiveMellinKernel, hε]

/-- Finite partition over a finite set of binary profiles. -/
def bitFiniteZetaPartition
    (S : Finset P.Profile) (β : ℝ) : ℝ :=
  Finset.sum S (fun ε => primitiveMellinKernel (P.bitInteger ε) β)

/--
On a finite support of nontrivial bit profiles, the bit partition is the Gibbs
sum over bit energies.
-/
theorem bitFiniteZetaPartition_eq_exp_sum
    (S : Finset P.Profile) (β : ℝ)
    (hS : ∀ ε ∈ S, 1 < P.bitInteger ε) :
    P.bitFiniteZetaPartition S β =
      Finset.sum S (fun ε => Real.exp (-β * P.bitEnergy ε)) := by
  unfold bitFiniteZetaPartition
  refine Finset.sum_congr rfl ?_
  intro ε hε
  exact P.primitiveMellinKernel_bitInteger_eq_exp_neg_mul_bitEnergy ε β (hS ε hε)

/-- Image support in arithmetic state space. -/
def arithmeticSupportOfProfiles
    (S : Finset P.Profile) : Finset ℕ :=
  S.image P.bitInteger

/--
If the bit-integer map is injective on a finite support, the arithmetic finite
zeta partition over the image equals the bit-profile partition.
-/
theorem primitiveFiniteZetaPartition_image_eq_bitFiniteZetaPartition
    (S : Finset P.Profile) (β : ℝ)
    (hinj : Set.InjOn P.bitInteger (↑S : Set P.Profile)) :
    primitiveFiniteZetaPartition (P.arithmeticSupportOfProfiles S) β =
      P.bitFiniteZetaPartition S β := by
  unfold arithmeticSupportOfProfiles bitFiniteZetaPartition
  unfold primitiveFiniteZetaPartition
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact hinj ha hb hab

/--
If the profile support is nontrivial and the bit-integer map is injective on it,
the arithmetic Souriau-zeta partition is the Gibbs sum over prime-bit energies.
-/
theorem primitiveFiniteZetaPartition_image_eq_exp_sum
    (S : Finset P.Profile) (β : ℝ)
    (hinj : Set.InjOn P.bitInteger (↑S : Set P.Profile))
    (hS : ∀ ε ∈ S, 1 < P.bitInteger ε) :
    primitiveFiniteZetaPartition (P.arithmeticSupportOfProfiles S) β =
      Finset.sum S (fun ε => Real.exp (-β * P.bitEnergy ε)) := by
  rw [P.primitiveFiniteZetaPartition_image_eq_bitFiniteZetaPartition S β hinj]
  exact P.bitFiniteZetaPartition_eq_exp_sum S β hS

/--
Bit-profile support is primitive in the profile order when no distinct occupied
profile is below another.

This is the binary-lattice antichain predicate.  It is intentionally stated on
profiles; the arithmetic equivalence requires a separate prime-factorization
order-reflection theorem.
-/
def ProfileLe (ε η : P.Profile) : Prop :=
  ∀ i : P.Index, ε i = true → η i = true

/-- Antichain predicate on finite profile supports. -/
def ProfileAntichain (S : Finset P.Profile) : Prop :=
  ∀ ⦃ε η : P.Profile⦄,
    ε ∈ S → η ∈ S → P.ProfileLe ε η → ε = η

/--
Constructive order-free primitive support witness.

This is the correct first replacement for a vague primitive/binary-lattice
claim: the antichain condition is now an explicit finite predicate.
-/
structure PrimitiveBinarySupport where
  support : Finset P.Profile
  antichain : P.ProfileAntichain support
  nontrivial : ∀ ε ∈ support, 1 < P.bitInteger ε

/-- Partition of a primitive binary support. -/
def PrimitiveBinarySupport.partition
    (B : P.PrimitiveBinarySupport) (β : ℝ) : ℝ :=
  P.bitFiniteZetaPartition B.support β

/-- Primitive binary support partition is the Gibbs sum over bit energies. -/
theorem PrimitiveBinarySupport.partition_eq_exp_sum
    (B : P.PrimitiveBinarySupport) (β : ℝ) :
    PrimitiveBinarySupport.partition P B β =
      Finset.sum B.support (fun ε => Real.exp (-β * P.bitEnergy ε)) := by
  unfold PrimitiveBinarySupport.partition
  exact P.bitFiniteZetaPartition_eq_exp_sum B.support β B.nontrivial

end FinitePrimeBitLattice

end InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge
