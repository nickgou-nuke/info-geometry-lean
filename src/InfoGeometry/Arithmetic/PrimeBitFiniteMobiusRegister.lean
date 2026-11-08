import InfoGeometry.Canonical.BooleanCubeDictionary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeBitFiniteMobiusRegister

open scoped ArithmeticFunction.Moebius
open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Canonical.BooleanCubeDictionary

noncomputable def arithmeticRegisterEmbedding (P : PrimeRegister) :
    {S : Finset ℕ // S ∈ P.primes.powerset} ↪ ArithmeticRegister P :=
  { toFun := fun S =>
      subsetToArithmeticEquiv P
        ⟨S.1, Finset.mem_powerset.mp S.2⟩
    inj' := by
        intro S T hST
        have hsubset :
            (subsetToArithmeticEquiv P
                ⟨S.1, Finset.mem_powerset.mp S.2⟩).val =
              (subsetToArithmeticEquiv P
                ⟨T.1, Finset.mem_powerset.mp T.2⟩).val := by
          exact congrArg Subtype.val hST
        have hST' :
            (⟨S.1, Finset.mem_powerset.mp S.2⟩ :
              {S : Finset ℕ // S ⊆ P.primes}) =
              ⟨T.1, Finset.mem_powerset.mp T.2⟩ :=
          (subsetToArithmeticEquiv P).injective (Subtype.ext hsubset)
        have hvals : S.1 = T.1 :=
          congrArg
            (fun U : {S : Finset ℕ // S ⊆ P.primes} => U.1) hST'
        exact Subtype.ext hvals }

noncomputable def arithmeticRegisterFinset (P : PrimeRegister) :
    Finset (ArithmeticRegister P) :=
  Finset.map (arithmeticRegisterEmbedding P) P.primes.powerset.attach

theorem powerset_mobius_sum_eq_arithmeticRegisterFinset_sum
    (P : PrimeRegister) :
    (∑ S ∈ P.primes.powerset,
      ArithmeticFunction.moebius (∏ p ∈ S, p)) =
      ∑ n ∈ arithmeticRegisterFinset P,
        ArithmeticFunction.moebius n.1 := by
  classical
  have hsum := Finset.sum_map
    (P.primes.powerset.attach) (arithmeticRegisterEmbedding P)
    (fun n : ArithmeticRegister P => ArithmeticFunction.moebius n.1)
  calc
    (∑ S ∈ P.primes.powerset,
        ArithmeticFunction.moebius (∏ p ∈ S, p)) =
        ∑ S ∈ P.primes.powerset.attach,
          ArithmeticFunction.moebius (∏ p ∈ S.1, p) := by
      simpa using (Finset.sum_attach P.primes.powerset
        (fun S => ArithmeticFunction.moebius (∏ p ∈ S, p))).symm
    _ = ∑ S ∈ P.primes.powerset.attach,
          ArithmeticFunction.moebius (arithmeticRegisterEmbedding P S).1 := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      change ArithmeticFunction.moebius (∏ p ∈ S.1, p) =
        ArithmeticFunction.moebius (∏ p ∈ S.1, p)
      rfl
    _ = ∑ n ∈ Finset.map (arithmeticRegisterEmbedding P)
          P.primes.powerset.attach,
          ArithmeticFunction.moebius n.1 := hsum.symm
    _ = ∑ n ∈ arithmeticRegisterFinset P,
          ArithmeticFunction.moebius n.1 := by
      rfl

theorem powerset_parity_sum_eq_arithmeticRegisterFinset_mobius_sum
    (P : PrimeRegister) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) =
      ∑ n ∈ arithmeticRegisterFinset P,
        ArithmeticFunction.moebius n.1 := by
  calc
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) =
        ∑ S ∈ P.primes.powerset,
          ArithmeticFunction.moebius (∏ p ∈ S, p) := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      exact (PrimeBitWittenIndex.mobius_prime_product_eq_parity S
        (fun p hp => P.prime_mem p (Finset.mem_powerset.mp hS hp))).symm
    _ = ∑ n ∈ arithmeticRegisterFinset P,
          ArithmeticFunction.moebius n.1 :=
      powerset_mobius_sum_eq_arithmeticRegisterFinset_sum P

end InfoGeometry.Arithmetic.PrimeBitFiniteMobiusRegister
