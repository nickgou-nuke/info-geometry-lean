import InfoGeometry.Arithmetic.PrimeBitFiniteKernelIndexBridge

/-!
# Compatibility names for the canonical finite prime-bit index owner

The canonical construction is `PrimeBitFiniteKernelIndexBridge`.  This file
does not introduce another carrier or another index definition; it only
forwards the shorter compatibility names used by earlier synthesis notes.

No divisor/residue identification is asserted here.  That remains a
separate theorem requiring an explicit finite correspondence.
-/

namespace InfoGeometry.Arithmetic.PrimeBitFiniteIndexBridge

open scoped BigOperators
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.IndexTheorem
open InfoGeometry.Arithmetic.PrimeBitFiniteKernelIndexBridge

theorem primeBit_witten_cancellation
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  finite_witten_index_cancel P hP

theorem primeBit_cancellation_as_finite_kernel_index
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    finiteKernelIndex (primeRegisterParityComplex P) = 0 :=
  finite_kernel_index_prime_register_parity_cancel P hP

end InfoGeometry.Arithmetic.PrimeBitFiniteIndexBridge
