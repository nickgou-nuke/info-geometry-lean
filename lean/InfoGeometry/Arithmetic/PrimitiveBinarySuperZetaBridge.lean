import Mathlib.Algebra.BigOperators.Associated
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

lemma bitEnergy_nonneg (ε : P.Profile) :
    0 ≤ P.bitEnergy ε := by
  unfold bitEnergy
  exact Finset.sum_nonneg (fun i _hi => by
    by_cases h : ε i
    · simp [h]
      exact Real.log_nonneg (by exact_mod_cast (P.prime_isPrime i).one_le)
    · simp [h])

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

lemma bitFiniteZetaPartition_nonneg
    (S : Finset P.Profile) (β : ℝ)
    (hS : ∀ ε ∈ S, 1 < P.bitInteger ε) :
    0 ≤ P.bitFiniteZetaPartition S β := by
  rw [P.bitFiniteZetaPartition_eq_exp_sum S β hS]
  exact Finset.sum_nonneg (fun ε _hε => le_of_lt (Real.exp_pos _))

lemma bitFiniteZetaPartition_pos_of_mem
    {S : Finset P.Profile} {β : ℝ}
    (hS : ∀ ε ∈ S, 1 < P.bitInteger ε)
    {ε : P.Profile} (hε : ε ∈ S) :
    0 < P.bitFiniteZetaPartition S β := by
  rw [P.bitFiniteZetaPartition_eq_exp_sum S β hS]
  exact Finset.sum_pos'
    (fun η _hη => le_of_lt (Real.exp_pos _))
    ⟨ε, hε, Real.exp_pos _⟩

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

/-- The prime labels are distinct across binary modes. -/
def DistinctPrimeLabels : Prop :=
  Function.Injective P.prime

/-- Profile order implies divisibility of the associated bit-integers. -/
theorem bitInteger_dvd_of_profileLe
    {ε η : P.Profile}
    (hεη : P.ProfileLe ε η) :
    P.bitInteger ε ∣ P.bitInteger η := by
  unfold bitInteger
  refine Finset.prod_dvd_prod_of_dvd _ _ ?_
  intro i _hi
  unfold occupiedFactor
  by_cases hi : ε i
  · have hη : η i = true := hεη i hi
    simp [hi, hη]
  · simp [hi]

/--
Under distinct prime labels, divisibility of bit-integers reflects the profile
order.
-/
theorem profileLe_of_bitInteger_dvd
    (hdistinct : P.DistinctPrimeLabels)
    {ε η : P.Profile}
    (hdiv : P.bitInteger ε ∣ P.bitInteger η) :
    P.ProfileLe ε η := by
  intro i hi
  by_cases hη : η i
  · exact hη
  · exfalso
    have hp_dvd_eps : P.prime i ∣ P.bitInteger ε := by
      unfold bitInteger
      have hmem : i ∈ (Finset.univ : Finset P.Index) := Finset.mem_univ i
      have hfactor :
          P.occupiedFactor ε i ∣
            Finset.prod (Finset.univ : Finset P.Index) (fun j => P.occupiedFactor ε j) :=
        Finset.dvd_prod_of_mem (fun j => P.occupiedFactor ε j) hmem
      simpa [occupiedFactor, hi] using hfactor
    have hp_dvd_eta : P.prime i ∣ P.bitInteger η :=
      dvd_trans hp_dvd_eps hdiv
    have hpPrime : Prime (P.prime i) := (P.prime_isPrime i).prime
    have hprod :
        P.prime i ∣
          Finset.prod (Finset.univ : Finset P.Index) (fun j => P.occupiedFactor η j) := by
      simpa [bitInteger] using hp_dvd_eta
    rcases (hpPrime.dvd_finset_prod_iff (fun j => P.occupiedFactor η j)).mp hprod with
      ⟨j, _hj, hjdvd⟩
    by_cases hηj : η j
    · have hprime_eq : P.prime i = P.prime j := by
        have hji : P.prime j = P.prime i :=
          (P.prime_isPrime j).dvd_iff_eq (P.prime_isPrime i).ne_one |>.mp
            (by simpa [occupiedFactor, hηj] using hjdvd)
        exact hji.symm
      have hij : i = j := hdistinct hprime_eq
      exact hη (by simpa [hij] using hηj)
    · have hp_dvd_one : P.prime i ∣ 1 := by
        simpa [occupiedFactor, hηj] using hjdvd
      exact (P.prime_isPrime i).not_dvd_one hp_dvd_one

/--
For a finite binary lattice with distinct prime labels, divisibility of
bit-integers is exactly profile inclusion.
-/
theorem bitInteger_dvd_iff_profileLe
    (hdistinct : P.DistinctPrimeLabels)
    (ε η : P.Profile) :
    P.bitInteger ε ∣ P.bitInteger η ↔ P.ProfileLe ε η :=
  ⟨P.profileLe_of_bitInteger_dvd hdistinct, P.bitInteger_dvd_of_profileLe⟩

/-- Antichain predicate on finite profile supports. -/
def ProfileAntichain (S : Finset P.Profile) : Prop :=
  ∀ ⦃ε η : P.Profile⦄,
    ε ∈ S → η ∈ S → P.ProfileLe ε η → ε = η

/--
A profile antichain maps to an arithmetic primitive finset under distinct prime
labels.
-/
theorem primitiveFinset_image_of_profileAntichain
    (S : Finset P.Profile)
    (hdistinct : P.DistinctPrimeLabels)
    (hS : P.ProfileAntichain S) :
    PrimitiveFinset (P.arithmeticSupportOfProfiles S) := by
  intro a b ha hb hab
  unfold arithmeticSupportOfProfiles at ha hb
  rcases Finset.mem_image.mp ha with ⟨ε, hεS, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨η, hηS, hbη⟩
  have hle : P.ProfileLe ε η :=
    (P.bitInteger_dvd_iff_profileLe hdistinct ε η).mp (by simpa [hbη] using hab)
  have hεη : ε = η := hS hεS hηS hle
  exact (congrArg P.bitInteger hεη).trans hbη

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
